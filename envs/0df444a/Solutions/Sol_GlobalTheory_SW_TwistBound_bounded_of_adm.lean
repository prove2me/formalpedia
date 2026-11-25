-- Prove2me | solution 1 for GlobalTheory.SW.TwistBound.bounded_of_adm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:09:38.976137+00:00
-- url     : https://prove2.me/submissions/7c0b76bc-cef4-4697-8027-3d46f48c07e6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SchwartzBruhatInnerProductSelfNonnegBounds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_FiniteClsAndStab
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_TwistAdmissible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionSiegelParabolicExplicitStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SiegelWeilDifferenceAutomorphyLinearityStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SiegelWeilDifferenceInvariantNormBoundedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsRationalMatrixMoveAdmissibleUniformLevelStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_TwistedSiegelWeilDifferenceBounded
import Theorems.Thm_GlobalTheory_SW_TwistBound_isSB_of_adm
import Theorems.Thm_GlobalTheory_IsSiegel_mk
import Theorems.Thm_GlobalTheory_SW_Base_cls_eq_iff
import Theorems.Thm_GlobalTheory_SW_Cusp_isSB_of_adm
import Theorems.Thm_GlobalTheory_SW_finite_cls_and_stab
import Theorems.Thm_GlobalTheory_SW_ip_self_nonneg_and_bounds


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
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.TwistBound
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Finset (E →+* ℂ)} {n N : ℕ}
namespace GlobalTheory.SW.TwistBound
theorem _root_.solution {M R : ℕ} {φ : Fam E n N} (h : admitted M R φ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ Λ ∈ Vset E n M, ∀ x, ‖φ Λ x‖ ≤ B := by
  haveI : Finite (Cls E n M) := (finite_cls_and_stab E n M h.pos.1).1
  have h1 : ∀ c : Cls E n M, ∃ B : ℝ, ∀ x, ‖φ (Quot.out c).1 x‖ ≤ B := fun c => by
    obtain ⟨S, hS, hl⟩ := isSB_of_adm h (Quot.out c).2
    exact (ip_self_nonneg_and_bounds E _ _ S _ hS hl).2.2.2.2.1
  choose b hb using h1
  obtain ⟨B, hB⟩ := (Set.finite_range b).bddAbove
  refine ⟨max B 0, le_max_right _ _, fun Λ hΛ x => ?_⟩
  set c : Cls E n M := Quot.mk _ ⟨Λ, hΛ⟩ with hc
  obtain ⟨g, hg, hm⟩ := (Base.cls_eq_iff ⟨Λ, hΛ⟩ (Quot.out c)).1 (Quot.out_eq c).symm
  rw [← h.equiv g hg Λ hΛ _ (Quot.out c).2 hm x]
  exact ((hb c _).trans (hB ⟨c, rfl⟩)).trans (le_max_left _ _)
end GlobalTheory.SW.TwistBound
