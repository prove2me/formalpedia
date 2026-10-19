-- Prove2me | solution 1 for OAI.BalancedTransport.Effectivity.elementary_loadingVelocity
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T06:18:56.348372+00:00
-- url     : https://prove2.me/submissions/1ef23ca3-4a3d-4205-a8f3-2f71cb6459bd

-- Generated from openai/math@1581d4c lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/ElementaryFields.lean:L160-L179
-- (upload_full_project.md Phase 4): solution for node OAI.BalancedTransport.Effectivity.elementary_loadingVelocity. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_BalancedThreeStack
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_FlatBounds
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EffectiveArithmetic
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_RationalAlgorithms
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EffectiveExp
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_RecorderRules
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_PrefixCoding
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_BoxCoding
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Work
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_TimeRegularity
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_FieldBounds
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_CompactFamilies
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_ResidualRegularity
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_RhoAlgorithms
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EffectiveLog
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericPrograms
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_ComputabilityRules
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_MachineRecursion
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_FiniteSimulator
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_UniversalInput
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericBounds
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericEvaluation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericDifferentiation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericScopes
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericJets
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericAlgebra
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Elementary
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EnergyCurve
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Sobolev
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EnergySlice
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Loading
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Periodic
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Motion
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Parking
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Deformation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_ElementaryMotion
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_ElementaryCalculus
import Theorems.Thm_OAI_BalancedTransport_Effectivity_elementary_movingBoxVelocity
import Theorems.Thm_OAI_BalancedTransport_Effectivity_transition_denom_lower

-- ---- from OAI.MathematicalPhysics.NavierStokes.BalancedTransport.FlatBounds ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section
namespace BalancedTransport.Effectivity
open Polynomial

lemma rhoJet_zero (x : ℝ) : rhoJet 0 x = expNegInvGlue x := by
  simp [rhoJet, rhoPolynomial]

end BalancedTransport.Effectivity
end

end OAI

-- ---- from OAI.MathematicalPhysics.NavierStokes.BalancedTransport.NumericScopes ----
namespace OAI

noncomputable section
namespace BalancedTransport.Effectivity.NumericOp

lemma real_append (d : ℕ) [NeZero d] (o : NumericOp) (x : Fin d → ℝ)
    (s q : List ℝ) (hs : o.Scoped s.length) : o.real d x (s ++ q) = o.real d x s := by
  have he (i : ℕ) (hi : i < s.length) : (s ++ q).getD i 0 = s.getD i 0 := by
    simp [List.getD, List.getElem?_append_left hi]
  rcases o with ⟨j,r,a,b⟩
  fin_cases j <;> simp only [Scoped, real, tag, rat, left, right] at hs ⊢
  all_goals first | rfl | exact he _ hs | simp only [he _ hs] | simp only [he _ hs.1, he _ hs.2]

lemma valid_append (o : NumericOp) (s q : List ℝ) (hs : o.Scoped s.length) :
    o.Valid (s ++ q) ↔ o.Valid s := by
  by_cases ht : o.tag = 5
  · have hh : o.left < s.length := by unfold Scoped at hs; rw [ht] at hs; exact hs
    simp only [Valid, ht, forall_const]
    simp only [List.getD, List.getElem?_append_left hh]
  · simp [Valid, ht]

end BalancedTransport.Effectivity.NumericOp
end

noncomputable section
namespace BalancedTransport.Effectivity.NumericProgram
variable {d : ℕ} [NeZero d]

lemma realFrom_length (p : NumericProgram) (x : Fin d → ℝ) (s : List ℝ) :
    (realFrom p x s).length = p.length + s.length := by
  induction p generalizing s with
  | nil => simp [realFrom]
  | cons o p ih => simpa [realFrom, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (o.real d x s :: s)

lemma realFrom_append (p : NumericProgram) (x : Fin d → ℝ) (s q : List ℝ)
    (hs : p.ScopedFrom s.length) : realFrom p x (s ++ q) = realFrom p x s ++ q := by
  induction p generalizing s with
  | nil => rfl
  | cons o p ih =>
    change realFrom p x (o.real d x (s ++ q) :: (s ++ q)) =
      realFrom p x (o.real d x s :: s) ++ q
    rw [o.real_append d x s q hs.1]
    exact ih (o.real d x s :: s) hs.2

lemma validFrom_append (p : NumericProgram) (x : Fin d → ℝ) (s q : List ℝ)
    (hs : p.ScopedFrom s.length) : ValidFrom x p (s ++ q) ↔ ValidFrom x p s := by
  induction p generalizing s with
  | nil => rfl
  | cons o p ih =>
    change o.Valid (s ++ q) ∧ ValidFrom x p (o.real d x (s ++ q) :: (s ++ q)) ↔
      o.Valid s ∧ ValidFrom x p (o.real d x s :: s)
    rw [o.valid_append s q hs.1, o.real_append d x s q hs.1]
    exact and_congr_right (fun _ => ih (o.real d x s :: s) hs.2)

lemma realFrom_empty_append (p : NumericProgram) (hp : p.Closed) (x : Fin d → ℝ) (s : List ℝ) :
    realFrom p x s = realFrom p x [] ++ s :=
  realFrom_append p x [] s hp

lemma validFrom_of_closed (p : NumericProgram) (hp : p.Closed) (x : Fin d → ℝ) (s : List ℝ) :
    ValidFrom x p s ↔ p.Valid x := p.validFrom_append x [] s hp

lemma realFrom_concat (p q : NumericProgram) (x : Fin d → ℝ) (s : List ℝ) :
    (p ++ q).realFrom x s = q.realFrom x (realFrom p x s) := List.foldl_append

lemma validFrom_concat (p q : NumericProgram) (x : Fin d → ℝ) (s : List ℝ) :
    (p ++ q).ValidFrom x s ↔ ValidFrom x p s ∧ q.ValidFrom x (realFrom p x s) := by
  induction p generalizing s with
  | nil => simp [ValidFrom, realFrom]
  | cons o p ih => simpa only [List.cons_append, ValidFrom, realFrom,
      List.foldl_cons, and_assoc] using and_congr_right (fun _ => ih _)

lemma scopedFrom_mono (p : NumericProgram) {n m : ℕ} (hnm : n ≤ m) :
    p.ScopedFrom n → p.ScopedFrom m := by
  intro h
  induction p generalizing n m with
  | nil => trivial
  | cons o p ih =>
    refine ⟨?_, ih (Nat.add_le_add_right hnm 1) h.2⟩
    rcases o with ⟨j,r,a,b⟩
    have ho := h.1
    fin_cases j <;> dsimp only [NumericOp.Scoped, NumericOp.tag, NumericOp.rat,
      NumericOp.left, NumericOp.right] at ho ⊢
    all_goals first | trivial | exact ho.trans_le hnm | exact ⟨ho.1.trans_le hnm,ho.2.trans_le hnm⟩

lemma scopedFrom_concat (p q : NumericProgram) (n : ℕ) :
    (p ++ q).ScopedFrom n ↔ p.ScopedFrom n ∧ q.ScopedFrom (n+p.length) := by
  induction p generalizing n with
  | nil => simp [ScopedFrom]
  | cons o p ih =>
    simp only [List.cons_append, ScopedFrom, List.length_cons]
    rw [ih]
    simp only [Nat.add_assoc, Nat.add_comm 1, and_assoc]

end BalancedTransport.Effectivity.NumericProgram
end

end OAI

-- ---- from OAI.MathematicalPhysics.NavierStokes.BalancedTransport.NumericAlgebra ----
namespace OAI

noncomputable section
namespace BalancedTransport.Effectivity.NumericOp
variable (d : ℕ) [NeZero d]

end BalancedTransport.Effectivity.NumericOp
end

noncomputable section
namespace BalancedTransport.Effectivity.NumericProgram
variable {d : ℕ} [NeZero d]

lemma literal_closed (q : ℚ) : (literal q).Closed := by trivial

lemma literal_valid (q : ℚ) (x : Fin d → ℝ) : (literal q).Valid x := by
  simp [literal, Valid, ValidFrom, NumericOp.Valid, NumericOp.tag]

omit [NeZero d] in
lemma coordinate_closed (k : Fin d) : (coordinate k).Closed := by trivial

lemma coordinate_valid (k : Fin d) (x : Fin d → ℝ) : (coordinate k).Valid x := by
  simp [coordinate, Valid, ValidFrom, NumericOp.Valid, NumericOp.tag]

lemma coordinate_real (k : Fin d) (x : Fin d → ℝ) : (coordinate k).real x = x k := by
  simp [coordinate, real, realFrom, NumericOp.real, NumericOp.tag, NumericOp.left, Fin.ofNat_eq_cast]

lemma unary_real (j : Fin 9) (n : ℕ) (p : NumericProgram) (x : Fin d → ℝ) :
    (unary j n p).real x = NumericOp.real d (j,0,0,n) x (p.realFrom x []) := by
  simp [unary, real, realFrom, List.foldl_append]

lemma unary_valid (j : Fin 9) (n : ℕ) (p : NumericProgram) (x : Fin d → ℝ)
    (hp : p.Valid x) (hi : j = 5 → ((n+1:ℕ):ℝ)⁻¹ ≤ p.real x) :
    (unary j n p).Valid x := by
  exact (validFrom_concat _ _ _ _).mpr ⟨hp, ⟨hi, trivial⟩⟩

lemma unary_closed (j : Fin 9) (n : ℕ) (p : NumericProgram) (hp : p.Closed)
    (hne : p ≠ []) (hj : j = 4 ∨ j = 5 ∨ j = 7) : (unary j n p).Closed := by
  have hn : 0 < p.length := List.length_pos_iff.mpr hne
  apply (scopedFrom_concat _ _ _).mpr
  refine ⟨hp, ?_⟩
  rcases hj with rfl | rfl | rfl <;> exact ⟨by simpa [NumericOp.Scoped, NumericOp.tag, NumericOp.left] using hn,trivial⟩

lemma realFrom_head {s : List ℝ} (hs : 0 < s.length) (t : List ℝ) :
    (s ++ t).getD 0 0 = s.getD 0 0 := by
  simp only [List.getD, List.getElem?_append_left hs]

lemma binary_real (j : Fin 9) (p q : NumericProgram) (hq : q.Closed) (hne : q ≠ [])
    (x : Fin d → ℝ) :
    (binary j p q).real x =
      NumericOp.real d (j,0,q.length,0) x (q.realFrom x [] ++ p.realFrom x []) := by
  cases q with
  | nil => exact (hne rfl).elim
  | cons head tail =>
    simp only [binary, real, realFrom_concat]
    rw [realFrom_empty_append (head :: tail) hq]
    rfl

lemma binary_register_left (p q : NumericProgram) (x : Fin d → ℝ) :
    (q.realFrom x [] ++ p.realFrom x []).getD q.length 0 = p.real x := by
  have he := q.realFrom_length x []
  simp only [List.length_nil, Nat.add_zero] at he
  rw [← he]
  simp only [List.getD, List.getElem?_append_right (le_refl _), Nat.sub_self]
  rfl

lemma binary_register_right (p q : NumericProgram) (hne : q ≠ []) (x : Fin d → ℝ) :
    (q.realFrom x [] ++ p.realFrom x []).getD 0 0 = q.real x := by
  apply realFrom_head
  simpa only [realFrom_length, List.length_nil, Nat.add_zero] using List.length_pos_iff.mpr hne

lemma binary_valid (j : Fin 9) (p q : NumericProgram) (hq : q.Closed) (hj : j ≠ 5)
    (x : Fin d → ℝ) (hpv : p.Valid x) (hqv : q.Valid x) : (binary j p q).Valid x := by
  apply (validFrom_concat _ _ _ _).mpr
  refine ⟨(validFrom_concat _ _ _ _).mpr ⟨hpv,
    (validFrom_of_closed q hq x _).mpr hqv⟩, ?_⟩
  exact ⟨fun h => (hj h).elim, trivial⟩

lemma binary_closed (j : Fin 9) (p q : NumericProgram) (hp : p.Closed) (hq : q.Closed)
    (hnep : p ≠ []) (hneq : q ≠ []) (hj : j = 2 ∨ j = 3) : (binary j p q).Closed := by
  have hn : 0 < p.length := List.length_pos_iff.mpr hnep
  have hqn : 0 < q.length := List.length_pos_iff.mpr hneq
  apply (scopedFrom_concat _ _ _).mpr
  refine ⟨(scopedFrom_concat _ _ _).mpr ⟨hp, q.scopedFrom_mono (Nat.zero_le _) hq⟩, ?_⟩
  rcases hj with rfl | rfl <;>
    simp only [ScopedFrom, NumericOp.Scoped, NumericOp.tag, NumericOp.left,
      NumericOp.right, List.length_append]
  all_goals exact ⟨⟨by omega, by omega⟩,trivial⟩

lemma binary_add_real (p q : NumericProgram) (hq : q.Closed) (hne : q ≠ []) (x : Fin d → ℝ) :
    (binary 2 p q).real x = p.real x + q.real x := by
  rw [binary_real 2 p q hq hne]
  exact congrArg₂ (· + ·) (binary_register_left p q x) (binary_register_right p q hne x)

lemma binary_mul_real (p q : NumericProgram) (hq : q.Closed) (hne : q ≠ []) (x : Fin d → ℝ) :
    (binary 3 p q).real x = p.real x * q.real x := by
  rw [binary_real 3 p q hq hne]
  exact congrArg₂ (· * ·) (binary_register_left p q x) (binary_register_right p q hne x)

end BalancedTransport.Effectivity.NumericProgram
end

end OAI

-- ---- from OAI.MathematicalPhysics.NavierStokes.BalancedTransport.Elementary ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section
namespace BalancedTransport.Effectivity

end BalancedTransport.Effectivity
end

noncomputable section
namespace BalancedTransport.Effectivity.Elementary
variable {d e : ℕ} [NeZero d] [NeZero e] {f g : (Fin d → ℝ) → ℝ}

lemma literal (q : ℚ) : Elementary (fun _ : Fin d → ℝ => (q : ℝ)) :=
  ⟨NumericProgram.literal q, by simp [NumericProgram.literal],
    NumericProgram.literal_closed q, NumericProgram.literal_valid q, rfl⟩

lemma coordinate (k : Fin d) : Elementary (fun z : Fin d → ℝ => z k) :=
  ⟨NumericProgram.coordinate k, by simp [NumericProgram.coordinate],
    NumericProgram.coordinate_closed k, NumericProgram.coordinate_valid k,
    funext (NumericProgram.coordinate_real k)⟩

lemma add (hf : Elementary f) (hg : Elementary g) : Elementary (fun x => f x + g x) := by
  obtain ⟨p, hpn, hpc, hpv, rfl⟩ := hf
  obtain ⟨q, hqn, hqc, hqv, rfl⟩ := hg
  exact ⟨NumericProgram.binary 2 p q, by simp [NumericProgram.binary],
    NumericProgram.binary_closed 2 p q hpc hqc hpn hqn (Or.inl rfl),
    fun x => NumericProgram.binary_valid 2 p q hqc (by decide) x (hpv x) (hqv x),
    funext (NumericProgram.binary_add_real p q hqc hqn)⟩

lemma mul (hf : Elementary f) (hg : Elementary g) : Elementary (fun x => f x * g x) := by
  obtain ⟨p, hpn, hpc, hpv, rfl⟩ := hf
  obtain ⟨q, hqn, hqc, hqv, rfl⟩ := hg
  exact ⟨NumericProgram.binary 3 p q, by simp [NumericProgram.binary],
    NumericProgram.binary_closed 3 p q hpc hqc hpn hqn (Or.inr rfl),
    fun x => NumericProgram.binary_valid 3 p q hqc (by decide) x (hpv x) (hqv x),
    funext (NumericProgram.binary_mul_real p q hqc hqn)⟩

lemma neg (hf : Elementary f) : Elementary (fun x => -f x) := by
  obtain ⟨p, hn, hc, hv, rfl⟩ := hf
  refine ⟨NumericProgram.unary 4 0 p, by simp [NumericProgram.unary],
    NumericProgram.unary_closed 4 0 p hc hn (Or.inl rfl),
    fun x => NumericProgram.unary_valid 4 0 p x (hv x) (by simp), ?_⟩
  funext x
  rw [NumericProgram.unary_real]
  rfl

lemma sub (hf : Elementary f) (hg : Elementary g) : Elementary (fun x => f x - g x) := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

lemma inv (hf : Elementary f) (n : ℕ) (hn : ∀ x, ((n+1:ℕ):ℝ)⁻¹ ≤ f x) :
    Elementary (fun x => (f x)⁻¹) := by
  obtain ⟨p, hne, hc, hv, rfl⟩ := hf
  refine ⟨NumericProgram.unary 5 n p, by simp [NumericProgram.unary],
    NumericProgram.unary_closed 5 n p hc hne (Or.inr (Or.inl rfl)),
    fun x => NumericProgram.unary_valid 5 n p x (hv x) (fun _ => hn x), ?_⟩
  funext x
  rw [NumericProgram.unary_real]
  rfl

lemma rho (n : ℕ) (hf : Elementary f) : Elementary (fun x => rhoJet n (f x)) := by
  obtain ⟨p, hn, hc, hv, rfl⟩ := hf
  refine ⟨p ++ [(6,0,n,0)], by simp, ?_, ?_, ?_⟩
  · apply (NumericProgram.scopedFrom_concat _ _ _).mpr
    exact ⟨hc, ⟨by simpa [NumericOp.Scoped, NumericOp.tag, NumericOp.right] using List.length_pos_iff.mpr hn, trivial⟩⟩
  · intro x
    exact (NumericProgram.validFrom_concat _ _ _ _).mpr ⟨hv x, ⟨by simp [NumericOp.Valid, NumericOp.tag], trivial⟩⟩
  · funext x
    simp only [NumericProgram.real, NumericProgram.realFrom_concat]
    rfl

end BalancedTransport.Effectivity.Elementary
end

noncomputable section
namespace BalancedTransport.Effectivity.Elementary
variable {d e : ℕ} [NeZero d] [NeZero e]

lemma one : Elementary (fun _ : Fin d → ℝ => (1 : ℝ)) := by simpa using (literal (d := d) 1)

lemma smoothTransition {f : (Fin d → ℝ) → ℝ} (hf : Elementary f) :
    Elementary (fun x => Real.smoothTransition (f x)) := by
  have hρ : Elementary (fun x => expNegInvGlue (f x)) := by
    simpa only [rhoJet_zero] using hf.rho 0
  have hρ' : Elementary (fun x => expNegInvGlue (1 - f x)) := by
    simpa only [rhoJet_zero] using (one.sub hf).rho 0
  have hi := (hρ.add hρ').inv 8 (fun x => by
    simpa using transition_denom_lower (f x))
  simpa only [Real.smoothTransition, div_eq_mul_inv] using hρ.mul hi

end BalancedTransport.Effectivity.Elementary
end

end OAI

-- ---- from OAI.MathematicalPhysics.NavierStokes.BalancedTransport.ElementaryMotion ----
namespace OAI

noncomputable section
namespace BalancedTransport.Effectivity
open BalancedTransport.Geometry Set

end BalancedTransport.Effectivity
end

noncomputable section
namespace BalancedTransport.Effectivity.RationalConstant
open BalancedTransport.Geometry Set

lemma rat (q : ℚ) : RationalConstant (q : ℝ) := ⟨q,rfl⟩

lemma nat (n : ℕ) : RationalConstant (n : ℝ) := ⟨n, by simp⟩

lemma zero : RationalConstant 0 := by simpa using rat 0

lemma elementary {d : ℕ} [NeZero d] {a : ℝ} (ha : RationalConstant a) :
    Elementary (fun _ : Fin d → ℝ => a) := by
  obtain ⟨a,rfl⟩ := ha; exact Elementary.literal a

end BalancedTransport.Effectivity.RationalConstant
end

noncomputable section
namespace BalancedTransport.Effectivity
open BalancedTransport.Geometry Set

end BalancedTransport.Effectivity
end

noncomputable section
namespace BalancedTransport.Effectivity.ElementaryCurve
open BalancedTransport.Geometry Set

end BalancedTransport.Effectivity.ElementaryCurve
end

noncomputable section
namespace BalancedTransport.Effectivity
open BalancedTransport.Geometry Set
variable {ι : Type*} [Fintype ι]

end BalancedTransport.Effectivity
end

noncomputable section
namespace BalancedTransport.Effectivity.ElementaryMotion
open BalancedTransport.Geometry Set
variable {ι : Type*} [Fintype ι]
variable {A B C : BoxLayout ι} {safe : Set ι} {η : ℝ}

end BalancedTransport.Effectivity.ElementaryMotion
end

noncomputable section
namespace BalancedTransport.Effectivity
open BalancedTransport.Geometry Set
variable {ι : Type*} [Fintype ι]

end BalancedTransport.Effectivity
end

end OAI

-- ---- from OAI.MathematicalPhysics.NavierStokes.BalancedTransport.ElementaryFields ----
namespace OAI

noncomputable section
namespace BalancedTransport.Effectivity.ElementaryScalar
open BalancedTransport.Geometry
variable {d : ℕ} {f g : (Fin d → ℝ) → Field ℝ}

lemma literal (q : ℚ) : ElementaryScalar (fun _ : Fin d → ℝ => fun _ _ => (q : ℝ)) := Elementary.literal q

lemma rational {q : ℝ} (hq : RationalConstant q) : ElementaryScalar (fun _ : Fin d → ℝ => fun _ _ => q) := hq.elementary

lemma mul (hf : ElementaryScalar f) (hg : ElementaryScalar g) : ElementaryScalar (fun p t x => f p t x * g p t x) := Elementary.mul hf hg

lemma sub (hf : ElementaryScalar f) (hg : ElementaryScalar g) : ElementaryScalar (fun p t x => f p t x - g p t x) := Elementary.sub hf hg

lemma transition (hf : ElementaryScalar f) : ElementaryScalar (fun p t x => Real.smoothTransition (f p t x)) := Elementary.smoothTransition hf

lemma time : ElementaryScalar (fun _ : Fin d → ℝ => fun t _ => t) := Elementary.coordinate (Fin.castAdd d 0)

lemma parameter (i : Fin d) : ElementaryScalar (fun p : Fin d → ℝ => fun _ _ => p i) := Elementary.coordinate (Fin.natAdd 4 i)

end BalancedTransport.Effectivity.ElementaryScalar
end

noncomputable section
namespace BalancedTransport.Effectivity.ElementaryField
open BalancedTransport.Geometry
variable {d : ℕ} {v w : (Fin d → ℝ) → Velocity}

end BalancedTransport.Effectivity.ElementaryField
end

noncomputable section
namespace BalancedTransport.Effectivity
open BalancedTransport.Geometry

lemma elementary_loadingVelocity {η : ℝ} (hr : RationalConstant η) :
    ElementaryField (fun p : Fin 3 → ℝ => loadingVelocity p η) := by
  have labelRat : ∀ i, RationalConstant (fixedLabel i) := by
    intro i
    fin_cases i
    · exact RationalConstant.nat 4
    · exact RationalConstant.zero
    · exact RationalConstant.zero
  apply elementary_movingBoxVelocity fixedLabel fixedLabel labelRat labelRat
  · intro i
    simpa only [loadingCenter, loadingSwitch, Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
      Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using
      ((((ElementaryScalar.literal 2).mul ElementaryScalar.time).sub
        (ElementaryScalar.literal (1/2))).transition.mul
        ((ElementaryScalar.parameter i).sub (ElementaryScalar.rational (labelRat i))))
  · intro i
    simpa using (ElementaryScalar.literal (d:=3) 1)
  · intro i
    exact ⟨0, by intro p t; norm_num⟩
  · exact hr

end BalancedTransport.Effectivity
end

end OAI

-- ---- platform node ----
open OAI OAI.BalancedTransport OAI.BalancedTransport.Effectivity
open BalancedTransport.Geometry


theorem solution : type_of% @_root_.OAI.BalancedTransport.Effectivity.elementary_loadingVelocity := @_root_.OAI.BalancedTransport.Effectivity.elementary_loadingVelocity
