-- Prove2me | solution 1 for GlobalTheory.SW.WeilAdm.phase_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:03:24.99441+00:00
-- url     : https://prove2.me/submissions/c96ce557-da7f-41e3-8f53-eb925995dfb4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpaceStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionUnitaryGroupTestFunctionsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionCommPositiveUnitaryGroupStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianHeisenbergOperatorLawsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_WeilActionLevelSupNormUniformInLatticeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_WeilActionLevelSupNormUniformInLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_AdmissibleLatticeFamilyHermitianWeilAction
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
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.WeilAdm
open WeilLevel Base
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n N : ℕ} {Λ Λ' : Lt E n}
namespace GlobalTheory.SW.WeilAdm
theorem _root_.solution (hΛ : ∀ x, x ∈ Λ ↔ ∀ y ∈ Λ, IsIntegral ℤ (herm 1 x y))
    {b y : Matrix (Fin n) (Fin N) E} (hb : ColsIn Λ b) (hy : ColsIn Λ y) :
    cexp (π * I * ((Algebra.trace ℚ E (∑ k, ∑ a, 2 * (b k a * cc (y k a))) : ℚ) : ℂ)) = 1 := by
  have hw : IsIntegral ℤ (∑ a, herm 1 (bᵀ a) (yᵀ a)) :=
    IsIntegral.sum _ fun a _ => (hΛ _).1 (hb a) _ (hy a)
  obtain ⟨k, hk⟩ := IsIntegrallyClosed.isIntegral_iff.1
    (Algebra.isIntegral_trace (L := ℚ) (F := E) hw)
  have e2 : ∑ k, ∑ a, 2 * (b k a * cc (y k a)) = (2 : ℚ) • ∑ a, herm 1 (bᵀ a) (yᵀ a) := by
    rw [Finset.sum_comm, Finset.smul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [herm_one, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [Rat.smul_def]
  rw [e2, map_smul, ← hk]
  have : (π : ℂ) * I * (((2 : ℚ) • algebraMap ℤ ℚ k : ℚ) : ℂ) = k * (2 * π * I) := by
    simp; ring
  rw [this, Complex.exp_int_mul_two_pi_mul_I]
end GlobalTheory.SW.WeilAdm
