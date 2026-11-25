-- Prove2me | solution 1 for GlobalTheory.T.weil_deligne_of_finite_image
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:56:43.616291+00:00
-- url     : https://prove2.me/submissions/cc815f08-0595-4f61-bd93-fc360f31f614

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WeilDeligneOfFiniteImage
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_MonodromyZeroOfWeilDeligneRepClassIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WeilDeligneOfFiniteImageStatement
import Theorems.Thm_GlobalTheory_WeilDeligne_exists_wdRep_pull_finite_twist


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
theorem _root_.solution : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (G : Type) [Group G] [Finite G] (π : Weil h →* G), IsOpen {σ : Ine (F := E) A | π (ineIncl h σ) = 1} → ∀ (n : ℕ) (R : Representation ℂ G (Fin n → ℂ)) (μ : Weil h →* ℂˣ), IsSmooth μ → ∃ b : WDRep h (Fin n → ℂ), ∀ σ, b.ρ σ = (μ σ : ℂ) • R (π σ) := by
  first | exact @GlobalTheory.WeilDeligne.exists_wdRep_pull_finite_twist | exact GlobalTheory.WeilDeligne.exists_wdRep_pull_finite_twist | (intros; apply GlobalTheory.WeilDeligne.exists_wdRep_pull_finite_twist <;> assumption)
end _root_.GlobalTheory.T
