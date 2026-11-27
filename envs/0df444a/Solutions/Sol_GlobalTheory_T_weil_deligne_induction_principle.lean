-- Prove2me | solution 1 for GlobalTheory.T.weil_deligne_induction_principle
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:34:52.42467+00:00
-- url     : https://prove2.me/submissions/5ab54cf2-0f62-467e-ba48-d3e5578eca15

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WeilDeligneInductionPrinciple
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_MonodromyZeroOfWeilDeligneRepClassIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WeilDeligneInductionPrincipleStatement
import Theorems.Thm_GlobalTheory_WeilDeligne_WD_induction_lpSum_twist_finite


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (S : WD h → Prop), (∀ x y, S x → S y → S (x.lpSum y)) → (∀ x y, (∀ σ, x.charPol σ = y.charPol σ) → S x → S y) → (∀ (n : ℕ) (a : WDRep h (Fin n → ℂ)) (μ : Weil h →* ℂˣ) (hμ : IsSmooth μ), (Set.range a.ρ).Finite → S (WD.mk (a.twist μ hμ))) → ∀ x, S x := by
  first | exact @GlobalTheory.WeilDeligne.WD.induction_lpSum_twist_finite | exact GlobalTheory.WeilDeligne.WD.induction_lpSum_twist_finite | (intros; apply GlobalTheory.WeilDeligne.WD.induction_lpSum_twist_finite <;> assumption)
end _root_.GlobalTheory.T
