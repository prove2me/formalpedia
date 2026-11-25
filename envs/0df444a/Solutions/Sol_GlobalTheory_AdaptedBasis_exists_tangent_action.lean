-- Prove2me | solution 1 for GlobalTheory.AdaptedBasis.exists_tangent_action
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:59:38.851874+00:00
-- url     : https://prove2.me/submissions/95ea4b00-907a-42a7-b847-02ccabd146da

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsGaloisCover
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueSumSingle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_DetCondIffOfFieldExtension
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_IsLocallyConstantRankAtStalkEigenSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsAdaptedLieBasis
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_tvec_inj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_tvec_tmap
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory GlobalTheory.AdaptedBasis
open ReciprocityTheory.ChartRestriction.G.Chart (prodPts scaleD tvec tmap IsUnivChart)
variable {k : Type} [Field k] {G : Over (Sp k)} [GrpObj G] {n : ℕ}
  {x : ∀ m : ℕ, Chart.sp (R₀ := k) (Chart.JetR k (Fin n) m) ⟶ G} (hx : IsUnivChart G n x)
include hx
namespace GlobalTheory.AdaptedBasis
theorem _root_.solution {O : Type} [CommRing O] (act : OAct O G) :
    ∃ r : O →+* Module.End k (Fin n → k), ∀ a c, tvec (x := x) (r a c) = tvec (x := x) c ≫ act.act a := by
  have : ∀ a, IsMonHom (act.act a) := act.hom
  have hadd : ∀ a c, Chart.tmap hx (act.act (a + c)) = Chart.tmap hx (act.act a) + Chart.tmap hx (act.act c) :=
    fun a c => LinearMap.ext fun v => Chart.tvec_inj hx (by
      rw [LinearMap.add_apply, Chart.tvec_add hx, Chart.tvec_tmap, Chart.tvec_tmap, Chart.tvec_tmap, act.add,
        MonObj.comp_mul])
  refine ⟨{ toFun := fun a => Chart.tmap hx (act.act a)
            map_one' := ?_
            map_mul' := fun a c => ?_
            map_zero' := ?_
            map_add' := hadd }, fun a c => Chart.tvec_tmap hx _ c⟩
  · refine LinearMap.ext fun v => Chart.tvec_inj hx ?_
    show tvec (x := x) (Chart.tmap hx (act.act 1) v) = tvec (x := x) v
    rw [Chart.tvec_tmap, act.one, Category.comp_id]
  · refine LinearMap.ext fun v => Chart.tvec_inj hx ?_
    show tvec (x := x) (Chart.tmap hx (act.act (a * c)) v) =
      tvec (x := x) (Chart.tmap hx (act.act a) (Chart.tmap hx (act.act c) v))
    rw [Chart.tvec_tmap, Chart.tvec_tmap, Chart.tvec_tmap, mul_comm a c, act.mul, Category.assoc]
  · have h00 := hadd 0 0
    rw [add_zero] at h00
    show Chart.tmap hx (act.act 0) = 0
    exact add_left_cancel (by rw [add_zero]; exact h00.symm :
      Chart.tmap hx (act.act 0) + Chart.tmap hx (act.act 0) = Chart.tmap hx (act.act 0) + 0)
end GlobalTheory.AdaptedBasis
