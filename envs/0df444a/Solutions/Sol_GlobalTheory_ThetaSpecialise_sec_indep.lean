-- Prove2me | solution 1 for GlobalTheory.ThetaSpecialise.sec_indep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:16:41.96247+00:00
-- url     : https://prove2.me/submissions/c2f73db2-b3b1-4b4b-a768-089e74937ca4

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_ThetaMove
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExpansionBijectiveOverFields
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUniqueSecPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExpandsAtTransport
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PowEqOneOfPush
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ThetaGrpActsLinearly
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsMoveMap
import Theorems.Thm_GlobalTheory_ThetaSpecialise_fn_indep
import Theorems.Thm_P2M_GlobalTheory_FieldBaseChange_gs_zero__47fb152d3439
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
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ThetaSpecialise
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.FieldBaseChange
variable {S F : Type} [CommRing S] [CommRing F] {fS : S →+* F} {X Y Y' : Scheme.{0}}
  {π : Y ⟶ Spec (CommRingCat.of S)} {π' : Y' ⟶ Spec (CommRingCat.of F)} {p : Y' ⟶ Y}
  (H : IsPullback p π' π (Spec.map (CommRingCat.ofHom fS))) [Flat π]
namespace GlobalTheory.ThetaSpecialise
theorem _root_.solution {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} (ε : K → ℤ) {φ' : K → (Y' ⟶ X)}
    (hφ : ∀ k, φ' k = p ≫ φ k) {n : ℕ} (c : Fin n → F)
    (hc : ∀ a : Fin n → S, ∑ i, fS (a i) * c i = 0 → ∀ i, a i = 0) (a : Fin n → SecOver π (LB.LinComb L φ ε))
    (h : ∑ i, c i • pullOver L ε H.w hφ (a i) = 0) (i : Fin n) : a i = 0 := by
  refine SecOver.ext _ _ fun (j : K → L.ι) => fn_ext fun y hy => ?_
  obtain ⟨_, ⟨U, hU, rfl⟩, hyU, hle⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open hy (LB.wchart L φ j).isOpen
  have hle : U ≤ LB.wchart L φ j := hle
  have hle' : p ⁻¹ᵁ U ≤ LB.wchart L φ' j := fun z hz => (wchart_eq hφ j).ge (hle hz)
  have e := fn_indep H hU c hc (fun i => resFn π hle (chartLin π (LB.LinComb L φ ε) j (a i))) (by
    have := congrArg (resFn π' hle' ∘ₗ chartLin π' (LB.LinComb L φ' ε) j) h
    rw [map_zero, map_sum] at this
    refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) this
    rw [map_smul]
    refine congrArg (c i • ·) (fn_ext fun z hz => ?_)
    exact ((gs_pullFn H.w _ _ _ z hz).trans (gs_res (𝟙 Y' ≫ p) z hle hz _)).trans
      ((gs_res _ z hle' hz _).trans (gs_pullFn H.w _ _ _ z (hle' hz))).symm) i
  exact ((gs_res (𝟙 Y) y hle hyU _).symm.trans ((congrArg (gs (𝟙 Y) y U) e).trans (gs_zero' _ y U hyU))).trans
    (gs_zero' _ y _ hy).symm
end GlobalTheory.ThetaSpecialise
