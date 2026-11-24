-- Prove2me | solution 1 for GlobalTheory.Unipotence.root_of_unity
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:49:52.220083+00:00
-- url     : https://prove2.me/submissions/a6ef8adc-d732-409d-b4a4-cf371f8e84d7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_EqOneOfPowEqOneOfCongrOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IsNilpotentSubOneOfConjPow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open GlobalTheory.Unipotence
open Polynomial
namespace GlobalTheory.Unipotence
theorem _root_.solution {K n : Type} [Field K] [Fintype n] [DecidableEq n]
    (A : Matrix n n K) (hA : IsUnit A) (P : (Matrix n n K)ˣ) (q : ℕ) (hq : 2 ≤ q)
    (h : (P : Matrix n n K) * A = A ^ q * P) (x : K) (hx : x ∈ spectrum K A) :
    ∃ m : ℕ, m ≠ 0 ∧ x ^ m = 1 := by
  have hconj : A ^ q = P * A * (P⁻¹ : (Matrix n n K)ˣ) := by
    rw [h, mul_assoc, Units.mul_inv, mul_one]
  have hstep : ∀ y ∈ spectrum K A, y ^ q ∈ spectrum K A := by
    intro y hy
    have := spectrum.pow_mem_pow A q hy
    rwa [hconj, spectrum.units_conjugate] at this
  have hall : ∀ k : ℕ, x ^ (q ^ k) ∈ spectrum K A := by
    intro k
    induction k with
    | zero => simpa using hx
    | succ k ih => rw [pow_succ, pow_mul]; exact hstep _ ih
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact (spectrum.zero_mem_iff K).mp hx hA
  obtain ⟨i, j, hij, he⟩ := (Matrix.finite_spectrum A).exists_lt_map_eq_of_forall_mem hall
  have hlt : q ^ i < q ^ j := Nat.pow_lt_pow_right (by omega) hij
  refine ⟨q ^ j - q ^ i, by omega, ?_⟩
  apply mul_left_cancel₀ (pow_ne_zero (q ^ i) hx0)
  rw [← pow_add, mul_one, Nat.add_sub_cancel' hlt.le]
  exact he.symm
end GlobalTheory.Unipotence
