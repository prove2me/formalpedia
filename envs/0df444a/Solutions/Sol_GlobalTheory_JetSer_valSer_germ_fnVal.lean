-- Prove2me | solution 1 for GlobalTheory.JetSer.valSer_germ_fnVal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:34:14.642799+00:00
-- url     : https://prove2.me/submissions/c0626039-eb54-4d05-8da1-06f2e4b4aca7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ValSerGermFnVal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.JetSer
namespace GlobalTheory.JetSer
theorem _root_.solution {A : Type} [CommRing A] {Y : Scheme.{0}} (r : Spec (CommRingCat.of A) ⟶ Y) (U : Y.Opens)
    (h : ⊤ ≤ r ⁻¹ᵁ U) (z : Spec (CommRingCat.of A)) (f : Γ(Y, U)) :
    ((Spec (CommRingCat.of A)).presheaf.germ ⊤ z trivial).hom
      ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom (fnVal r U f)) = gs r z U f := by
  have hz : r z ∈ U := h (show z ∈ (⊤ : (Spec (CommRingCat.of A)).Opens) from trivial)
  rw [gs_eq r z U hz, fnVal, dif_pos h]
  have e : ∀ a, (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom a) = a :=
    fun a => (Scheme.ΓSpecIso (CommRingCat.of A)).hom_inv_id_apply a
  rw [e]
  exact TopCat.Presheaf.germ_res_apply (Spec (CommRingCat.of A)).presheaf (homOfLE h) z trivial _
end GlobalTheory.JetSer
