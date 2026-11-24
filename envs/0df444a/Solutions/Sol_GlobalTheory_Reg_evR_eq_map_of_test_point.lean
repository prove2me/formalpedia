-- Prove2me | solution 1 for GlobalTheory.Reg.evR_eq_map_of_test_point
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:55:17.165686+00:00
-- url     : https://prove2.me/submissions/f1fa1a95-d47d-411a-9e16-685b07724033

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_RegularCharts_Reframe
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_RegularCharts_ModelAt
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_FrameCharts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_SectionEqZeroOfGenericFramedPointValues

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg
open GlobalTheory GlobalTheory.Reg
namespace GlobalTheory.Reg
theorem _root_.solution {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (hL : EvLaws Xo c) {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ}
    {g : Rul Xo c} (hg : g ∈ sec Xo c a n) {S : Type} [CommRing S] [Algebra c.F S] (p : TRing c.F)
    (φ : p.R →ₐ[c.F] S) (y : FrPt Xo c p.R) (w : FrPt Xo c S) (hw : FrMap φ y w) :
    evR Xo c g w = φ (g p y) := by
  have h : FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) w := ⟨p, φ, y, hw⟩
  unfold evR evalAt
  rw [dif_pos h]
  exact hL.wd g hg.1 S _ p _ φ _ y w h.choose_spec.choose_spec.choose_spec hw
end GlobalTheory.Reg
