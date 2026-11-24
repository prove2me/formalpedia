-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SelfDualReal.selfDual_transport
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:36:09.443742+00:00
-- url     : https://prove2.me/submissions/58bd0a6a-48e9-4725-a8e9-a3951ef64eb8

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SWXSDefs
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_HermitianForms_BijectiveLinearCombinationOfRankAtStalk

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory HeckeCharacterZeroLocus.SiegelWeilU
open scoped FourierTransform RealInnerProductSpace
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SelfDualReal
namespace GlobalTheory.CompanionTheory.SelfDualReal
theorem _root_.solution {V W : Type} [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V]
    [BorelSpace V] [AddCommGroup W] [TopologicalSpace W] [IsTopologicalAddGroup W]
    [MeasurableSpace W] [BorelSpace W]
    (f : V ≃+ W) (hf : Continuous f) (hf' : Continuous f.symm) (ν : Measure W) (χ : W → W → ℂ)
    (h : SelfDual ν χ) : SelfDual (ν.map f.symm) (fun x y => χ (f x) (f y)) := by
  let g : W ≃ₜ V := { f.symm.toEquiv with continuous_toFun := hf', continuous_invFun := hf }
  haveI : IsTopologicalAddGroup V := g.symm.isInducing.topologicalAddGroup f.toAddMonoidHom
  obtain ⟨hν, hinv⟩ := h
  have hm : MeasurableEmbedding f.symm := g.measurableEmbedding
  refine ⟨AddEquiv.isAddHaarMeasure_map ν f.symm hf' hf, ?_⟩
  intro Φ hΦ hc hi z
  simp only [hm.integral_map, hm.integrable_map_iff, AddEquiv.apply_symm_apply,
    Function.comp_def] at hi ⊢
  have := hinv (Φ ∘ g) (hΦ.comp g.continuous) (hc.comp_homeomorph g) hi (f z)
  simp only [Function.comp_def] at this
  have h2 : g (-f z) = -z := by
    change f.symm (-f z) = -z
    simp
  rw [h2] at this
  exact this
end GlobalTheory.CompanionTheory.SelfDualReal
