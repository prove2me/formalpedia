-- Prove2me | solution 1 for GlobalTheory.SmGL.InductionContragredient.lower
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:16:07.561068+00:00
-- url     : https://prove2.me/submissions/c294b8b8-0886-4e50-b345-a706c93e758f

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
namespace InductionContragredient
theorem _root_.solution (h : InductionContragredient k) (e : (Σ a, m a) ≃ n)
    [MeasurableSpace (GL n k)] [BorelSpace (GL n k)] (μ : Measure (GL n k)) [μ.IsHaarMeasure]
    {ρ : Representation ℂ (Levi k m) W} (hρ : IsSmooth ρ) :
    ∃ Φ : (parIndLower e (contra ρ)).Equiv (contra (parIndLower e ρ)),
      ∀ (f' : IndSpLower e (contra ρ)) (f : IndSpLower e ρ),
        (Φ f' : Module.Dual ℂ (IndSpLower e ρ)) f =
          ∫ x in (KO k n : Set (GL n k)), (f'.1.1 x : Module.Dual ℂ W) (f.1.1 x) ∂μ := by
  have key : ∀ χ : Levi k m →* ℂˣ, deltaHalf k (fun a : αᵒᵈ => m (OrderDual.ofDual a)) = χ →
      ∃ Φ : (smInd (parabLower k e) ((twist (contra ρ) χ).comp (leviProjLower k e))).Equiv
          (contra (smInd (parabLower k e) ((twist ρ χ).comp (leviProjLower k e)))),
        ∀ f' f, (Φ f').1 f =
          ∫ x in (KO k n : Set (GL n k)), (f'.1.1 x : Module.Dual ℂ W) (f.1.1 x) ∂μ := by
    rintro _ rfl
    exact h _ _ _ (opp e) μ W ρ hρ
  exact key _ (MonoidHom.ext fun g => deltaHalf_opp (m := m) g)
end InductionContragredient
end GlobalTheory.SmGL
