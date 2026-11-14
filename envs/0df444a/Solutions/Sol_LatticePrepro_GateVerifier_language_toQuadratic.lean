-- Prove2me | solution 1 for LatticePrepro.GateVerifier.language_toQuadratic
-- status  : ACCEPTED   (prove)
-- author  : @WizardOfMenlo
-- created : 2026-11-13T09:28:16.878174+00:00
-- url     : https://prove2.me/submissions/af77588e-6328-4ad8-b376-50e16f631345

import Mathlib
import Definitions.Def_LatticePrepro_Verifier_Quadratic
import Definitions.Def_LatticePrepro_Verifier_Gates

namespace LatticePrepro end LatticePrepro
namespace LatticePrepro.GateVerifier end LatticePrepro.GateVerifier

namespace LatticePrepro

section QuadForm

variable {R : Type*} [CommRing R] {m : ℕ}

/-- The quadratic form `∑ i j, T i j * z i * z j` of a coefficient tensor. -/
def quadForm (T : Fin m → Fin m → R) (z : Fin m → R) : R := ∑ i, ∑ j, T i j * (z i * z j)

lemma quadForm_sub (T T' : Fin m → Fin m → R) (z : Fin m → R) :
    quadForm (T - T') z = quadForm T z - quadForm T' z := by
  simp [quadForm, sub_mul, Finset.sum_sub_distrib]

lemma quadForm_deltaTensor (i₀ j₀ : Fin m) (c : R) (z : Fin m → R) :
    quadForm (deltaTensor i₀ j₀ c) z = c * (z i₀ * z j₀) := by
  unfold quadForm deltaTensor
  rw [Finset.sum_eq_single i₀]
  · rw [Finset.sum_eq_single j₀]
    · simp
    · intro j _ hj; simp [hj]
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro i _ hi; simp [hi]
  · intro h; exact absurd (Finset.mem_univ _) h

end QuadForm

namespace GateVerifier

variable (W : GateVerifier)

/-- The interpolation identity `f u v = a + b u + c v + d u v` on Boolean inputs. -/
lemma toNat_eq_interp (f : Bool → Bool → Bool) (u v : Bool) :
    ((f u v).toNat : ℤ) =
      c00 f + c10 f * u.toNat + c01 f * v.toNat + c11 f * (u.toNat * v.toNat) := by
  cases u <;> cases v <;>
    simp only [Bool.toNat_true, Bool.toNat_false, c00, c10, c01, c11, Nat.cast_one,
      Nat.cast_zero] <;> ring

variable (p : ℕ)

lemma gateEq_toQuadratic (b : Fin W.G) (z : Fin (W.S + 1) → ZMod p) :
    (W.toQuadratic p).gateEq b z =
      z 0 * z (W.out b).succ - ((c00 (W.fn b) : ℤ) : ZMod p) * (z 0 * z 0) -
        ((c10 (W.fn b) : ℤ) : ZMod p) * (z 0 * z (W.in1 b).succ) -
        ((c01 (W.fn b) : ℤ) : ZMod p) * (z 0 * z (W.in2 b).succ) -
        ((c11 (W.fn b) : ℤ) : ZMod p) * (z (W.in1 b).succ * z (W.in2 b).succ) := by
  show quadForm _ z = _
  simp only [quadForm_sub, quadForm_deltaTensor, one_mul]

/-- The `𝔽_p`-assignment `(1, z)` of a Boolean wire assignment `z`. -/
def lift (z : Fin W.S → Bool) : Fin (W.S + 1) → ZMod p :=
  Fin.cons 1 fun i => ((z i).toNat : ZMod p)

@[simp] lemma lift_zero (z : Fin W.S → Bool) : W.lift p z 0 = 1 := by
  simp [lift]

@[simp] lemma lift_succ (z : Fin W.S → Bool) (i : Fin W.S) :
    W.lift p z i.succ = ((z i).toNat : ZMod p) := by
  simp [lift]

/-- On lifted assignments, the gate equation evaluates to `z_o - f(z_l, z_{l'})`. -/
lemma gateEq_lift (b : Fin W.G) (z : Fin W.S → Bool) :
    (W.toQuadratic p).gateEq b (W.lift p z) =
      ((((z (W.out b)).toNat : ℤ) - ((W.fn b (z (W.in1 b)) (z (W.in2 b))).toNat : ℤ) : ℤ) :
        ZMod p) := by
  rw [gateEq_toQuadratic, toNat_eq_interp (W.fn b) (z (W.in1 b)) (z (W.in2 b))]
  simp only [lift_zero, lift_succ]
  push_cast
  ring

lemma inputIdx_toQuadratic (i : Fin W.n) :
    (W.toQuadratic p).inputIdx i = (W.inputWire i).succ := rfl

lemma outputIdx_toQuadratic : (W.toQuadratic p).outputIdx = W.outputWire.succ := rfl

variable [Fact p.Prime]

lemma toNat_sub_toNat_cast_eq_zero_iff (u v : Bool) :
    ((((u.toNat : ℤ) - (v.toNat : ℤ) : ℤ) : ZMod p) = 0) ↔ u = v := by
  cases u <;> cases v <;> simp

lemma isValid_lift_iff (z : Fin W.S → Bool) :
    (W.toQuadratic p).IsValid (W.lift p z) ↔ W.IsValid z := by
  unfold QuadraticVerifier.IsValid IsValid
  refine forall_congr' fun b => ?_
  rw [gateEq_lift, toNat_sub_toNat_cast_eq_zero_iff]

lemma toNat_cast_eq_ite_iff (u v : Bool) :
    ((u.toNat : ZMod p) = if v then 1 else 0) ↔ u = v := by
  cases u <;> cases v <;> simp

lemma toNat_cast_eq_one_iff (u : Bool) : ((u.toNat : ZMod p) = 1) ↔ u = true := by
  cases u <;> simp

lemma hasPrefix_lift_iff (x : Fin W.n → Bool) (z : Fin W.S → Bool) :
    (W.toQuadratic p).HasPrefix x (W.lift p z) ↔ W.HasPrefix x z := by
  unfold QuadraticVerifier.HasPrefix HasPrefix
  rw [outputIdx_toQuadratic, lift_succ, toNat_cast_eq_one_iff]
  refine and_congr (forall_congr' fun i => ?_) Iff.rfl
  rw [inputIdx_toQuadratic, lift_succ, toNat_cast_eq_ite_iff]

lemma isBoolean_lift (z : Fin W.S → Bool) :
    (W.toQuadratic p).IsBooleanAssignment (W.lift p z) := by
  refine ⟨W.lift_zero p z, fun i => ?_⟩
  refine Fin.cases ?_ (fun j => ?_) i
  · simp
  · rw [lift_succ]; cases z j <;> simp

/-- The Boolean wire assignment underlying an `𝔽_p`-assignment. -/
def toBits (z' : Fin (W.S + 1) → ZMod p) : Fin W.S → Bool := fun i => decide (z' i.succ = 1)

/-- A Boolean `𝔽_p`-assignment is the lift of its underlying bits. -/
lemma eq_lift_toBits {z' : Fin (W.S + 1) → ZMod p}
    (hz : (W.toQuadratic p).IsBooleanAssignment z') : z' = W.lift p (W.toBits p z') := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rw [lift_zero]; exact hz.1
  · rw [lift_succ]
    unfold toBits
    rcases hz.2 j.succ with h | h
    · rw [h]
      have : (0 : ZMod p) ≠ 1 := zero_ne_one
      simp [this]
    · rw [h]; simp

/-- **Claim 3.15**: the quadratic verifier accepts the same language. -/
private theorem language_toQuadratic : (W.toQuadratic p).Language = W.Language := by
  ext x
  simp only [QuadraticVerifier.Language, Language, Set.mem_ofPred_eq, QuadraticVerifier.IsAccepting]
  constructor
  · rintro ⟨z', hbool, hvalid, hpre⟩
    rw [W.eq_lift_toBits p hbool] at hvalid hpre
    exact ⟨W.toBits p z', (W.isValid_lift_iff p _).mp hvalid, (W.hasPrefix_lift_iff p x _).mp hpre⟩
  · rintro ⟨z, hvalid, hpre⟩
    exact ⟨W.lift p z, W.isBoolean_lift p z, (W.isValid_lift_iff p z).mpr hvalid,
      (W.hasPrefix_lift_iff p x z).mpr hpre⟩

end GateVerifier

end LatticePrepro

open LatticePrepro
open LatticePrepro.GateVerifier
variable (W : GateVerifier)
variable (p : ℕ)
variable [Fact p.Prime]
theorem solution : (W.toQuadratic p).Language = W.Language :=
  @LatticePrepro.GateVerifier.language_toQuadratic W p _
