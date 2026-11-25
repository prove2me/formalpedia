-- Prove2me | solution 1 for GlobalTheory.SS.HtForm.gen_field
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:48:54.426476+00:00
-- url     : https://prove2.me/submissions/2f083bad-33e2-4192-8405-69db6d22db83

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ForallGeometricallyIntegralOfSmoothOfGeometrical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsProductFormulaPlacesOfFgFieldStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsLineBundleHeightProperSchemeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsPositiveDefiniteQuadraticFormEndomorphisms
import Theorems.Thm_GlobalTheory_SS_HtForm_res_res
import Theorems.Thm_GlobalTheory_SS_HtForm_res_self
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_res_res


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.HtForm
namespace GlobalTheory.SS.HtForm
theorem _root_.solution {k : Type} [Field k] (M : LB (Sp k)) (hM : M.IsLB) : ∃ e : M.Gen, e.IsGen := by
  have hm : (IsLocalRing.closedPoint k : Sp k) ∈ (⨆ i, M.U i) := by
    rw [hM.cover]; trivial
  obtain ⟨i₀, hi₀⟩ := TopologicalSpace.Opens.mem_iSup.1 hm
  have htop : M.U i₀ = ⊤ := (IsLocalRing.closedPoint_mem_iff _).1 hi₀
  have hle : ∀ i, M.U i ≤ M.U i ⊓ M.U i₀ := fun i => le_inf le_rfl (htop ▸ le_top)
  refine ⟨⟨fun i => res (hle i) (M.g i i₀)⟩, fun i j => ?_⟩
  have h3 : M.U i ⊓ M.U j ≤ M.U i ⊓ M.U j ⊓ M.U i₀ := le_inf le_rfl (htop ▸ le_top)
  have hc := congrArg (res h3) (hM.cocycle i j i₀)
  rw [map_mul, res_res, res_res, res_res, res_self] at hc
  rw [res_res, res_res]
  exact hc.symm
end GlobalTheory.SS.HtForm
