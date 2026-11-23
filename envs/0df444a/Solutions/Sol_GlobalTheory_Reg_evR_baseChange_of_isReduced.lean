-- Prove2me | solution 1 for GlobalTheory.Reg.evR_baseChange_of_isReduced
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:45:32.768906+00:00
-- url     : https://prove2.me/submissions/b3efb83e-c005-4d5b-93e0-da8c5bdeb5ca

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_RegularCharts_ModelAt
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_FrameCharts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_NaturalRuleValueBaseChangeOfIsReduced
import Theorems.Thm_Formalism_L2_Pj_frMap_trans


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
namespace GlobalTheory.Reg
theorem _root_.solution :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), EvLaws Xo c → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c), f ∈ sec Xo c a n → ∀ (S T : Type) [CommRing S] [IsReduced S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T) (y : FrPt Xo c S) (z : FrPt Xo c T), FrMap φ y z → evR Xo c f z = φ (evR Xo c f y) := by
  intro E _ _ _ H Dw l Xo c hL a n f hf S T _ _ _ _ _ φ y z hm
  have hT1 : FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) y := hL.test S y
  have hT2 : FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) z := by
    obtain ⟨p, ψ, y', hy'⟩ := hT1
    exact ⟨p, φ.comp ψ, y', frMap_trans (Xo := Xo) (c := c) _ _ _ ψ φ y' y z hy' hm⟩
  unfold evR evalAt
  rw [dif_pos hT2, dif_pos hT1]
  exact hL.wd f hf.1 T _ _ _ _ _ _ z hT2.choose_spec.choose_spec.choose_spec
    (frMap_trans (Xo := Xo) (c := c) _ _ _ _ φ _ y z hT1.choose_spec.choose_spec.choose_spec hm)
end GlobalTheory.Reg
