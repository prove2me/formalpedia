-- Prove2me | solution 1 for GlobalTheory.SW.WeilAdm.levelL_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:16:01.870611+00:00
-- url     : https://prove2.me/submissions/9f8aa665-7fa4-48ef-a99b-acc7841748a5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpaceStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionUnitaryGroupTestFunctionsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionCommPositiveUnitaryGroupStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianHeisenbergOperatorLawsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_WeilActionLevelSupNormUniformInLatticeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_WeilActionLevelSupNormUniformInLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_AdmissibleLatticeFamilyHermitianWeilAction
import Theorems.Thm_GlobalTheory_SW_WeilAdm_sum_quot_comp
import Theorems.Thm_GlobalTheory_SW_WeilAdm_rho_add
import Theorems.Thm_GlobalTheory_SW_WeilAdm_rho_sum
import Theorems.Thm_GlobalTheory_SW_WeilAdm_rho_congr
import Theorems.Thm_GlobalTheory_SW_WeilLevel_levelL_of_fix


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
    (hΛ' : ∀ x, x ∈ Λ' ↔ ∀ y ∈ Λ', IsIntegral ℤ (herm 1 x y)) {s R : ℕ} [Fintype (Quo Λ' N s)]
    (h2 : ∀ v ∈ Λ', (s : E) • v ∈ Λ) {φ : Matrix (Fin n) (Fin N) E → ℂ} (hφ : LevelL Λ R φ) :
    LevelL Λ' ((NumberField.discr E).natAbs * (2 * R)) (∑ q : Quo Λ' N s, rho R q.out.1 φ) := by
  refine levelL_of_fix hΛ' fun d b hd hb => ?_
  have hY : Matrix.fromCols d b ∈ cols Λ' N := by
    rintro (i | i)
    · exact hd i
    · exact hb i
  change rho R (Matrix.fromCols d b) _ = _
  rw [rho_sum, ← sum_quot_comp _ (fun x : cols Λ' N => rho R x.1 φ) (rho_congr hΛ hΛ' h2 hφ)
    (fun x => ⟨_, hY⟩ + x) fun x y h => by rwa [add_sub_add_left_eq_sub] at h]
  exact Finset.sum_congr rfl fun q _ => (rho_add hΛ' R q.out.2 hY φ).symm
end GlobalTheory.SW.WeilAdm
