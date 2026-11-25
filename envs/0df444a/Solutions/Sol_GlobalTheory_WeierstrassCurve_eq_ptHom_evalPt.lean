-- Prove2me | solution 1 for GlobalTheory.WeierstrassCurve.eq_ptHom_evalPt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:55:53.195121+00:00
-- url     : https://prove2.me/submissions/2e780ecb-3127-4dd6-a0d9-4771def45be1

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjDehomA
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_OpensRangeChartYSupOpensRangeChartZ
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_AwayToSectionFromZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsRegularFnIffOfIsAffineOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsAffineHomOfIsPullbackSpecMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TangentBijectionOfValues
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_SpecMapAwayFnEquivAwayChart
import Theorems.Thm_GlobalTheory_WeierstrassCurve_fromSpec_coordOpen_eq_ptHom
import Theorems.Thm_GlobalTheory_WeierstrassCurve_evalPt_constOn
import Theorems.Thm_GlobalTheory_TangentOrigin_eq_spec_fromSpec
import Theorems.Thm_GlobalTheory_TangentOrigin_evalPt_res
import Theorems.Thm_GlobalTheory_WeierstrassCurve_isAffineOpen_coordOpen


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
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap resG constFn)
open GlobalTheory.ProjFrac GlobalTheory.QCoh.Qcqs GlobalTheory.TangentOrigin
open GlobalTheory
open GlobalTheory.WeierstrassCurve
variable {R : Type} [CommRing R] (W : WeierstrassCurve R)
variable {W} {A : Type} [CommRing A]
namespace GlobalTheory.WeierstrassCurve
theorem _root_.solution {x : Sp A ⟶ scheme W} {ρ : R →+* A} (hx : x ≫ toSpec W = spMap ρ)
    {U : (scheme W).Opens} {i : Fin 3} (hi : U ≤ coordOpen W i) (h : ⊤ ≤ x ⁻¹ᵁ U)
    {P : Fin 3 → A} (hP : ∀ j, evalPt x U h (ratioOn W U i hi j) = P j) :
    ∃ hP, x = ptHom W ρ P hP := by
  have h' : ⊤ ≤ x ⁻¹ᵁ coordOpen W i := h.trans (x.preimage_mono hi)
  have e := eq_spec_fromSpec (isAffineOpen_coordOpen W i) x h'
  rw [fromSpec_coordOpen_eq_ptHom, SpecMap_ptHom] at e
  have e₁ : (evalPt x _ h').comp (constOn W _) = ρ := RingHom.ext (evalPt_constOn hx h')
  have e₂ : evalPt x _ h' ∘ ratio W i = P := funext fun j =>
    (evalPt_res x hi h' h _).symm.trans (hP j)
  subst e₁ e₂
  exact ⟨_, e⟩
end GlobalTheory.WeierstrassCurve
