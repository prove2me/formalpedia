-- Prove2me | solution 1 for GlobalTheory.T.truncatedWhittaker_weilRep_eventually
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:04:46.438436+00:00
-- url     : https://prove2.me/submissions/c33ef921-8143-4175-a1e8-e2dfc82f1972

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TruncatedWhittakerWeilRepEventually
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TruncatedWhittakerWeilRepEventuallyStatement
import Theorems.Thm_GlobalTheory_JR_WhitX_lam_weil_eventually


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (m : A.Meas ψ) (x : A.Kˣ) (γ : ℂ) W, A.IsWeil ψ x A.etaK (m.μL x) γ W → ∀ φ, IsTest φ → ∀ a : A.K, IsUnit a → (∀ y : A.L, IsUnit y → a = x * A.NL y → ∀ᶠ c in 𝓝[≠] (0 : F), A.abelian₂ m.μK ψ a (fun g => W g φ 0) c = γ * A.orbL m.ν φ y) ∧ ((¬ ∃ y : A.L, IsUnit y ∧ a = x * A.NL y) → ∀ᶠ c in 𝓝[≠] (0 : F), A.abelian₂ m.μK ψ a (fun g => W g φ 0) c = 0) := by
  first | exact @GlobalTheory.JR.WhitX.lam_weil_eventually | exact GlobalTheory.JR.WhitX.lam_weil_eventually | (intros; apply GlobalTheory.JR.WhitX.lam_weil_eventually <;> assumption)
end _root_.GlobalTheory.T
