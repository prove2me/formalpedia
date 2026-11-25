-- Prove2me | solution 1 for GlobalTheory.SS.HtForm.gen_reindex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:48:58.749373+00:00
-- url     : https://prove2.me/submissions/6a732bb1-498b-4326-a44a-55da6a1d008f

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
theorem _root_.solution {X Y : Scheme.{0}} (L : LB X) {I J : Type} [Fintype I] [Fintype J] (e : J ≃ I)
    (φ : I → (Y ⟶ X)) (ε : I → ℤ) (h : ∃ t : LB.Gen (LB.LinComb L φ ε), t.IsGen) :
    ∃ t : LB.Gen (LB.LinComb L (fun i => φ (e i)) (fun i => ε (e i))), t.IsGen := by
  obtain ⟨t, ht⟩ := h
  have hle : ∀ j : J → L.ι, LB.wchart L (fun i => φ (e i)) j ≤ LB.wchart L φ (fun i => j (e.symm i)) :=
    fun j y hy => Set.mem_iInter.2 fun i => by
      have := Set.mem_iInter.1 hy (e.symm i)
      simpa using this
  refine ⟨⟨fun j => res (hle j) (t.s _)⟩, fun j j' => ?_⟩
  have h1 := congrArg (res (inf_le_inf (hle j) (hle j'))) (ht (fun i => j (e.symm i)) (fun i => j' (e.symm i)))
  refine ((res_res _ _ _).trans (res_res _ _ _).symm).trans (h1.trans ((map_mul _ _ _).trans ?_))
  refine congrArg₂ (· * ·) ?_ ((res_res _ _ _).trans (res_res _ _ _).symm)
  refine (map_prod (res (inf_le_inf (hle j) (hle j'))) _ _).trans ?_
  simp only [LB.LinComb, map_zpow, res_res]
  refine Fintype.prod_equiv e.symm _ _ fun i => ?_
  obtain ⟨i, rfl⟩ := e.surjective i
  have key : ∀ (i' : J) (hi : i' = i) (a : LB.wchart L (fun i => φ (e i)) j ⊓ LB.wchart L (fun i => φ (e i)) j' ≤ φ (e i) ⁻¹ᵁ (L.U (j i') ⊓ L.U (j' i')))
      (b : LB.wchart L (fun i => φ (e i)) j ⊓ LB.wchart L (fun i => φ (e i)) j' ≤ φ (e i') ⁻¹ᵁ (L.U (j i') ⊓ L.U (j' i'))),
      res a (pullU (φ (e i)) _ (L.g (j i') (j' i'))) ^ ε (e i) = res b (pullU (φ (e i')) _ (L.g (j i') (j' i'))) ^ ε (e i') := by
    rintro _ rfl _ _
    rfl
  exact (congrArg (· ^ ε (e i)) (res_res _ _ _)).trans (key _ (e.symm_apply_apply i) _ _)
end GlobalTheory.SS.HtForm
