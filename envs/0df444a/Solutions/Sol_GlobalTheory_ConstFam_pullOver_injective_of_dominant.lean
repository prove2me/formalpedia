-- Prove2me | solution 1 for GlobalTheory.ConstFam.pullOver_injective_of_dominant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:36:53.48171+00:00
-- url     : https://prove2.me/submissions/962f6ea0-43ab-4077-8e20-065de1ebb024

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ExpandsAtSecIsMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ExpandsAtSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsFETranslateFeTranslate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsSmulMemSpanOfExpandsAt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TopologicalSpace NumberField
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.ConstFam
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.FieldBaseChange
namespace GlobalTheory.ConstFam
theorem _root_.solution {R R' : Type} [CommRing R] [CommRing R'] {X Y Y' : Scheme.{0}}
    {π : Y ⟶ Spec (CommRingCat.of R)} (L : LB X) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} (ε : K → ℤ)
    {π' : Y' ⟶ Spec (CommRingCat.of R')} {g : R →+* R'} {p : Y' ⟶ Y}
    (hp : p ≫ π = π' ≫ Spec.map (CommRingCat.ofHom g)) {φ' : K → (Y' ⟶ X)} (hφ : ∀ k, φ' k = p ≫ φ k)
    [IsSchemeTheoreticallyDominant p] [QuasiCompact p] : Function.Injective (pullOver L ε hp hφ) := by
  intro s t h
  refine SecOver.ext _ _ fun i => p.app_injective _ (fn_ext fun y hy => ?_)
  have e := congrArg (fun q : SecOver π' (LB.LinComb L φ' ε) => gs (𝟙 _) y _ (LB.Sec.f q i)) h
  have hy' : (𝟙 Y' : _ ⟶ _) y ∈ LB.wchart L φ' i := (wchart_eq hφ i).ge hy
  exact (gs_pull _ _ y _ hy _).trans ((gs_pullFn _ _ _ _ y hy').symm.trans (e.trans
    ((gs_pullFn _ _ _ _ y hy').trans (gs_pull _ _ y _ hy _).symm)))
end GlobalTheory.ConstFam
