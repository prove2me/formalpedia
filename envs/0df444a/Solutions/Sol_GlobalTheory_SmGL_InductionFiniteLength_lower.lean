-- Prove2me | solution 1 for GlobalTheory.SmGL.InductionFiniteLength.lower
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:16:08.326017+00:00
-- url     : https://prove2.me/submissions/1024eedb-4a13-4da9-ab01-df9d877d3c63

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsUnitarisableOfCharIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_LeviEmbMemNormalizerLower
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_HasFiniteLengthOfIsIrreducible
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_comp
import Theorems.Thm_GlobalTheory_SmGL_deltaHalf_opp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL
open GlobalTheory
open GlobalTheory.SmGL
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)]
  [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]
  {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
namespace GlobalTheory.SmGL
namespace InductionFiniteLength
theorem _root_.solution (h : InductionFiniteLength k) (e : (Σ a, m a) ≃ n)
    {ρ : Representation ℂ (Levi k m) W} (hρ : IsSmooth ρ) (hl : HasFiniteLength ρ) :
    HasFiniteLength (parIndLower e ρ) := by
  have key : ∀ χ : Levi k m →* ℂˣ, deltaHalf k (fun a : αᵒᵈ => m (OrderDual.ofDual a)) = χ →
      HasFiniteLength (smInd (parabLower k e) ((twist ρ χ).comp (leviProjLower k e))) := by
    rintro _ rfl
    exact h _ _ _ (opp e) W ρ hρ hl
  exact key _ (MonoidHom.ext fun g => deltaHalf_opp (m := m) g)
end InductionFiniteLength
end GlobalTheory.SmGL
