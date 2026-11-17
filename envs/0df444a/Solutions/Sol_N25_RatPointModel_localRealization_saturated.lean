-- Prove2me | solution 1 for N25.RatPointModel.localRealization_saturated
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:28:53.974738+00:00
-- url     : https://prove2.me/submissions/86bd24b7-ecd7-40ad-9f15-63a455418c49

import Mathlib
import Definitions.Def_N25_RatPointModel
import Definitions.Def_N25_LocalCarrier
import Theorems.Thm_N25_RatPointModel_preimage71_algebraic
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_isFinite_and_flat_schemeNsmul
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_coe_nsmul_eq_comp_schemeNsmul
import Theorems.Thm_AlgebraicGeometry_existsUnique_section_comp_eq_of_isFinite_of_isAlgClosed

set_option autoImplicit false

noncomputable section

namespace N25

/-- The image criterion and algebraicity of division make the local realization
saturated for multiplication by seventy-one. -/
theorem _root_.solution
    (D : RatPointModel) (e : ↥M5 →+ D.Local)
    (himage : ∀ y : D.Local,
      y ∈ e.range ↔ D.localMap y ∈ D.barMap.range) :
    ∀ y : D.Local,
      (71 : ℕ) • y ∈ e.range → y ∈ e.range := by
  intro y hy
  apply (himage y).mpr
  apply D.preimage71_algebraic
  simpa only [map_nsmul] using (himage ((71 : ℕ) • y)).mp hy

end N25
