-- Prove2me | solution 1 for GlobalTheory.SW.Step.exists_enum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:54:09.71763+00:00
-- url     : https://prove2.me/submissions/b6fde037-0b16-4846-a60e-99c2431caa2e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_RationalSchwartzBruhatAlgebraIntegralLinearStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionSiegelParabolicExplicit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionCommPositiveUnitaryGroupStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_WeilActionLevelSupNormUniformInLatticeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_FiniteClsAndStab
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SiegelWeilDifferenceAutomorphyLinearityStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsGoodSplitPrimeCmFieldStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_NeBotOfNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ClassSumNbStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_TwistAdmissible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_TwistedSiegelWeilDifferenceBoundedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HeckeRelationAdmissibleFamilyPointwiseStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SiegelWeilFormulaDegreeSucc
import Theorems.Thm_GlobalTheory_SW_TransComp_key
import Theorems.Thm_GlobalTheory_SW_neighbours
import Theorems.Thm_P2M_GlobalTheory_SW_Nbr_Int__symm_b5c59deb8a7e


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
open scoped ComplexConjugate ComplexOrder Real Classical
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.Step
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Finset (E →+* ℂ)} {n N : ℕ}
namespace GlobalTheory.SW.Step
theorem _root_.solution {M q : ℕ} {P : Ideal (𝓞 E)} (hM : 0 < M) (hP : GoodPrime M q P) :
    ∃ (B : ℕ) (e : Fin B → Lt E n → Lt E n), ∀ Λ ∈ Vset E n M, (∀ j, e j Λ ∈ Vset E n M) ∧
      ∀ g : Lt E n → ℂ, ∑ᶠ Λ' ∈ Nb M P Λ, g Λ' = ∑ j, g (e j Λ) := by
  have H := (neighbours E n M q P hM hP).2.2
  have hq : 0 < q - 1 := Nat.sub_pos_of_lt hP.1.one_lt
  have key : ∀ Λ : Lt E n, ∃ e : Fin ((q ^ n - 1) / (q - 1)) → Lt E n, Λ ∈ Vset E n M →
      (∀ j, e j ∈ Vset E n M) ∧ ∀ g : Lt E n → ℂ, ∑ᶠ Λ' ∈ Nb M P Λ, g Λ' = ∑ j, g (e j) := by
    intro Λ
    by_cases hΛ : Λ ∈ Vset E n M
    · obtain ⟨hf, hc, -⟩ := H Λ hΛ
      have hc' : hf.toFinset.card = (q ^ n - 1) / (q - 1) := by
        rw [← hc, Nat.mul_div_cancel _ hq, Set.ncard_eq_toFinset_card _ hf]
      let σ := (Finset.equivFinOfCardEq hc').symm
      refine ⟨fun j => (σ j).1, fun _ => ⟨fun j => (hf.mem_toFinset.1 (σ j).2).1, fun g => ?_⟩⟩
      rw [finsum_mem_eq_finite_toFinset_sum _ hf, ← Finset.sum_coe_sort, ← σ.sum_comp]
    · exact ⟨fun _ => Λ, fun h => (hΛ h).elim⟩
  choose e he using key
  exact ⟨_, fun j Λ => e Λ j, he⟩
end GlobalTheory.SW.Step
