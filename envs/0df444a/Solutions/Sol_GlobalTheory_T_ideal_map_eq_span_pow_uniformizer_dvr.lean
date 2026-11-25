-- Prove2me | solution 1 for GlobalTheory.T.ideal_map_eq_span_pow_uniformizer_dvr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:20:49.623738+00:00
-- url     : https://prove2.me/submissions/34d74c7d-d051-4c4a-b787-0038f0ef7f1b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IdealMapEqSpanPowUniformizerDvr
import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThickTransComp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IdealMapEqSpanPowUniformizerDvrStatement
import Theorems.Thm_GlobalTheory_ideal_map_eq_span_pow_uniformizer


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory IsLocalRing ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (V W : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] (f : V →+* W), Function.Injective f → ∀ (ϖ : V) (w : W) (e a : ℕ) (I : Ideal V), Irreducible ϖ → Irreducible w → Associated (f ϖ) (w ^ e) → I.map f = Ideal.span {w ^ a} → ∃ b : ℕ, e * b = a ∧ I = Ideal.span {ϖ ^ b} := by
  first | exact @GlobalTheory.ideal_map_eq_span_pow_uniformizer | exact GlobalTheory.ideal_map_eq_span_pow_uniformizer | (intros; apply GlobalTheory.ideal_map_eq_span_pow_uniformizer <;> assumption)
end _root_.GlobalTheory.T
