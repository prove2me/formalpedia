-- Prove2me | solution 1 for LatticePrepro.FixedSystem.recover
-- status  : ACCEPTED   (prove)
-- author  : @WizardOfMenlo
-- created : 2026-11-13T09:28:12.888744+00:00
-- url     : https://prove2.me/submissions/0ef5f485-bf48-484b-9acb-9ef30c08ca6c

import Mathlib
import Definitions.Def_LatticePrepro_Basic_Blocks
import Definitions.Def_LatticePrepro_Reduction_LinearSystem
import Definitions.Def_LatticePrepro_Moments_Basic
import Definitions.Def_LatticePrepro_Moments_Representation
import Definitions.Def_LatticePrepro_Verifier_Quadratic
import Definitions.Def_LatticePrepro_Reduction_FixedSystem

namespace LatticePrepro end LatticePrepro
namespace LatticePrepro.FixedSystem end LatticePrepro.FixedSystem

namespace LatticePrepro

namespace EncodingTuple

variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] {S : ℕ}
  (ε : EncodingTuple p K S)

/-- A vanishing combination `∑ c_i E_i = 0` with `c_0` arbitrary forces `c_i = 0` for `i ≥ 1`. -/
lemma eq_zero_of_sum_smul_eq_zero {c : Fin (S + 1) → ZMod p} (h : ∑ i, c i • ε.E i = 0)
    (i : Fin (S + 1)) (hi : i ≠ 0) : c i = 0 := by
  rw [Fin.sum_univ_succ, ε.E_zero, smul_zero, zero_add] at h
  obtain ⟨j, rfl⟩ : ∃ j : Fin S, i = j.succ := ⟨i.pred hi, (Fin.succ_pred i hi).symm⟩
  exact (Fintype.linearIndependent_iff.mp ε.linearIndependent) (fun j => c j.succ) h j

end EncodingTuple

end LatticePrepro

namespace LatticePrepro

open Finsupp

namespace FixedSystem

variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K]
    {Ω : Type} [Field Ω] [Algebra (ZMod p) Ω] [Algebra K Ω] [IsScalarTower (ZMod p) K Ω]
    (V : QuadraticVerifier p) (R : MomentRepresentation p K Ω) (ε : EncodingTuple p K V.S)

lemma algebraMap_smul_eq (c : ZMod p) (y : K) :
    algebraMap K Ω (c • y) = c • algebraMap K Ω y := by
  rw [Algebra.smul_def, Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply]

/-- A vanishing `𝔽_p`-combination of the images of the `E_i` in `Ω` has zero coefficients
(except possibly at the constant index `0`). -/
lemma coeff_eq_zero_of_sum_smul_algebraMap {c : Fin (V.S + 1) → ZMod p}
    (h : ∑ i, c i • algebraMap K Ω (ε.E i) = 0) (i : Fin (V.S + 1)) (hi : i ≠ 0) : c i = 0 := by
  have h' : ∑ i, c i • ε.E i = 0 := by
    apply (algebraMap K Ω).injective
    rw [map_sum, map_zero, ← h]
    exact Finset.sum_congr rfl fun i _ => algebraMap_smul_eq _ _
  exact ε.eq_zero_of_sum_smul_eq_zero h' i hi

/-- **Lemma 4.7** (pointwise form). Values `Fv i j ∈ 𝔽_p` at a point `α` that are symmetric,
satisfy `Fv i i = Fv i 0`, the encoding identities and the gate identities, with `Fv 0 0 ≠ 0`,
come from a Boolean valid assignment `z` with `enc z = α`. -/
private theorem recover {Fv : Fin (V.S + 1) → Fin (V.S + 1) → ZMod p}
    (hsymm : ∀ i j, Fv i j = Fv j i) (hdiag : ∀ i, Fv i i = Fv i 0) {α : Ω}
    (henc : ∀ j, α * algebraMap (ZMod p) Ω (Fv 0 j) =
      ∑ i, algebraMap K Ω (ε.E i) * algebraMap (ZMod p) Ω (Fv i j))
    (hgate : ∀ b, ∑ i, ∑ j, V.coeff b i j * Fv i j = 0) (hne : Fv 0 0 ≠ 0) :
    ∃ z : Fin (V.S + 1) → ZMod p, V.IsBooleanAssignment z ∧ V.IsValid z ∧
      algebraMap K Ω (ε.enc z) = α := by
  set a := Fv 0 0 with ha
  let z : Fin (V.S + 1) → ZMod p := fun i => Fv i 0 / a
  have hz0 : z 0 = 1 := div_self hne
  have hFi0 : ∀ i, Fv i 0 = a * z i := fun i => by
    simp only [z]
    rw [mul_div_cancel₀ _ hne]
  have ha' : algebraMap (ZMod p) Ω a ≠ 0 := (map_ne_zero _).mpr hne
  -- the point is the encoding of `z`
  have hα : α = algebraMap K Ω (ε.enc z) := by
    have h0 := henc 0
    rw [EncodingTuple.enc, map_sum]
    apply mul_right_cancel₀ ha'
    rw [h0, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hFi0 i, map_mul, algebraMap_smul_eq, Algebra.smul_def]
    ring
  -- product structure
  have hprod : ∀ i j, Fv i j = a * (z i * z j) := by
    intro i j
    by_cases hi : i = 0
    · subst hi
      rw [hsymm 0 j, hFi0 j, hz0, one_mul]
    · have hj := henc j
      rw [hα, hsymm 0 j, hFi0 j] at hj
      have hl : algebraMap K Ω (ε.enc z) * algebraMap (ZMod p) Ω (a * z j) =
          ∑ i, (z i * (a * z j)) • algebraMap K Ω (ε.E i) := by
        rw [EncodingTuple.enc, map_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply]
        ring
      rw [hl] at hj
      have hcomb : ∑ i, (z i * (a * z j) - Fv i j) • algebraMap K Ω (ε.E i) = 0 := by
        rw [Finset.sum_congr rfl fun i _ => sub_smul _ _ _, Finset.sum_sub_distrib, hj,
          sub_eq_zero]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Algebra.smul_def]
        ring
      have := coeff_eq_zero_of_sum_smul_algebraMap V ε hcomb i hi
      rw [sub_eq_zero] at this
      rw [← this]
      ring
  -- Boolean coordinates
  have hbool : ∀ i, z i = 0 ∨ z i = 1 := by
    intro i
    have h1 := hdiag i
    rw [hprod i i, hprod i 0, hz0, mul_one] at h1
    have h2 : z i * z i = z i := mul_left_cancel₀ hne h1
    have h3 : z i * (z i - 1) = 0 := by rw [mul_sub, mul_one, h2, sub_self]
    rcases mul_eq_zero.mp h3 with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.mp h)
  -- validity
  have hvalid : V.IsValid z := by
    intro b
    have h := hgate b
    simp_rw [hprod] at h
    unfold QuadraticVerifier.gateEq
    apply mul_left_cancel₀ hne
    rw [mul_zero, Finset.mul_sum, ← h]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  exact ⟨z, ⟨hz0, hbool⟩, hvalid, hα.symm⟩

end FixedSystem

end LatticePrepro

open LatticePrepro
open Finsupp
open LatticePrepro.FixedSystem
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K]
    {Ω : Type} [Field Ω] [Algebra (ZMod p) Ω] [Algebra K Ω] [IsScalarTower (ZMod p) K Ω]
    (V : QuadraticVerifier p) (R : MomentRepresentation p K Ω) (ε : EncodingTuple p K V.S)
theorem solution {Fv : Fin (V.S + 1) → Fin (V.S + 1) → ZMod p}
    (hsymm : ∀ i j, Fv i j = Fv j i) (hdiag : ∀ i, Fv i i = Fv i 0) {α : Ω}
    (henc : ∀ j, α * algebraMap (ZMod p) Ω (Fv 0 j) =
      ∑ i, algebraMap K Ω (ε.E i) * algebraMap (ZMod p) Ω (Fv i j))
    (hgate : ∀ b, ∑ i, ∑ j, V.coeff b i j * Fv i j = 0) (hne : Fv 0 0 ≠ 0) :
    ∃ z : Fin (V.S + 1) → ZMod p, V.IsBooleanAssignment z ∧ V.IsValid z ∧
      algebraMap K Ω (ε.enc z) = α :=
  @LatticePrepro.FixedSystem.recover p _ K _ _ Ω _ _ _ _ V ε Fv hsymm hdiag α henc hgate hne
