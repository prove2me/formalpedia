-- Prove2me | solution 1 for GlobalTheory.SecGlue.eq_of_chartHom_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:35:15.711662+00:00
-- url     : https://prove2.me/submissions/e11798da-fd19-474d-a564-d8dcd553a58a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsCombIn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsAffineCombinationInChartUnique

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory GlobalTheory.SecGlue
namespace GlobalTheory.SecGlue
theorem _root_.solution {Y : Scheme.{0}} {V : Y.Opens} (hV : IsAffineOpen V) {S : Type}
    [CommRing S] (c c' : Sp S ⟶ Y) (hc : c ⁻¹ᵁ V = ⊤) (hc' : c' ⁻¹ᵁ V = ⊤)
    (e : ∀ x, chartHom V c hc x = chartHom V c' hc' x) : c = c' := by
  have e₁ : c.appLE V ⊤ hc.ge = c'.appLE V ⊤ hc'.ge := by
    rw [← cancel_mono (Scheme.ΓSpecIso (CommRingCat.of S)).hom]
    exact CommRingCat.hom_ext (RingHom.ext e)
  have a := IsAffineOpen.SpecMap_appLE_fromSpec c hV (isAffineOpen_top (Sp S)) hc.ge
  have a' := IsAffineOpen.SpecMap_appLE_fromSpec c' hV (isAffineOpen_top (Sp S)) hc'.ge
  rw [e₁, a', IsAffineOpen.fromSpec_top] at a
  exact ((cancel_epi _).1 a).symm
end GlobalTheory.SecGlue
