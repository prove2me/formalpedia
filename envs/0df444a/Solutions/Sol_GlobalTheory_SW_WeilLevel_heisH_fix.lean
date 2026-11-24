-- Prove2me | solution 1 for GlobalTheory.SW.WeilLevel.heisH_fix
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:03:25.419933+00:00
-- url     : https://prove2.me/submissions/76cd18f9-4e0d-4197-8a13-26f6aba4a50b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_NotAdmissibleHalfLatticeFamily
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_FinsumQuotientOfLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionUnitaryGroupTestFunctions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianHeisenbergOperatorLaws
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_WeilActionLevelSupNormUniformInLattice
import Theorems.Thm_GlobalTheory_SW_WeilLevel_cc_sub
import Theorems.Thm_GlobalTheory_SW_WeilLevel_cc_mul
import Theorems.Thm_GlobalTheory_SW_WeilLevel_cc_nat
import Theorems.Thm_GlobalTheory_SW_WeilLevel_colsIn_smul
import Theorems.Thm_GlobalTheory_SW_Base_herm_one
import Theorems.Thm_GlobalTheory_SW_Model_herm_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.WeilLevel
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n N : ℕ} {Λ : Lt E n}
namespace GlobalTheory.SW.WeilLevel
theorem _root_.solution (hΛ : ∀ x, x ∈ Λ ↔ ∀ y ∈ Λ, IsIntegral ℤ (herm 1 x y)) {R : ℕ}
    {φ : Matrix (Fin n) (Fin N) E → ℂ} (h : LevelL Λ R φ) {d b : Matrix (Fin n) (Fin N) E}
    (hd : ColsIn Λ d) (hb : ColsIn Λ b) :
    heisH (((2 * R : ℕ) : E) • d) (((2 * R : ℕ) : E) • b) φ = φ := by
  funext x
  have e1 : φ (x - ((2 * R : ℕ) : E) • d) = φ x := by
    rw [← h.2 x (-(((2 : ℕ) : E) • d)) fun a => Λ.neg_mem (colsIn_smul 2 hd a)]
    congr 1
    rw [smul_neg, smul_smul, sub_eq_add_neg, Nat.cast_mul, mul_comm]
  rw [heisH, e1]
  by_cases hx : φ x = 0
  · rw [hx, zero_mul]
  set y : Matrix (Fin n) (Fin N) E :=
    ((2 : ℕ) : E) • ((R : E) • x) - ((2 * R * R : ℕ) : E) • d with hy
  have hyΛ : ColsIn Λ y := fun a =>
    Λ.sub_mem (colsIn_smul 2 (h.1 x hx) a) (colsIn_smul _ hd a)
  have hw : IsIntegral ℤ (∑ a, herm 1 (bᵀ a) (yᵀ a)) :=
    IsIntegral.sum _ fun a _ => (hΛ _).1 (hb a) _ (hyΛ a)
  obtain ⟨k, hk⟩ := IsIntegrallyClosed.isIntegral_iff.1
    (Algebra.isIntegral_trace (L := ℚ) (F := E) hw)
  have e2 : ∑ k, ∑ a, (((2 * R : ℕ) : E) • b) k a *
      (2 * cc (x k a) - cc ((((2 * R : ℕ) : E) • d) k a)) =
      (2 : ℚ) • ∑ a, herm 1 (bᵀ a) (yᵀ a) := by
    rw [Finset.sum_comm, Finset.smul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Model.herm_one, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [hy, Matrix.transpose_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul,
      cc_sub, cc_mul, cc_nat, Rat.smul_def]
    push_cast
    ring
  rw [e2, map_smul, ← hk]
  have : (π : ℂ) * I * (((2 : ℚ) • algebraMap ℤ ℚ k : ℚ) : ℂ) = k * (2 * π * I) := by
    simp; ring
  rw [this, Complex.exp_int_mul_two_pi_mul_I, mul_one]
end GlobalTheory.SW.WeilLevel
