-- Prove2me | solution 1 for GlobalTheory.MultilinFubini.integral_multilinear_pi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T06:09:57.777663+00:00
-- url     : https://prove2.me/submissions/dc8c3623-9cb5-4d6b-a47f-bfde59def0f8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntegralContinuousMultilinearMapPiMeasure
import Theorems.Thm_GlobalTheory_MultilinFubini_aestronglyMeasurable_pi_of_forall
import Theorems.Thm_GlobalTheory_MultilinFubini_integral_vecOn

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open GlobalTheory GlobalTheory.MultilinFubini
variable {ι : Type} [Fintype ι] [DecidableEq ι] {X : ι → Type} [∀ i, MeasurableSpace (X i)]
  {E : ι → Type} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℂ (E i)]
  {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F]
namespace GlobalTheory.MultilinFubini
theorem _root_.solution : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (X : ι → Type) [∀ i, MeasurableSpace (X i)] (μ : ∀ i, Measure (X i)) [∀ i, SigmaFinite (μ i)] (E : ι → Type) [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℂ (E i)] [∀ i, CompleteSpace (E i)] (F : Type) [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F] (Φ : ContinuousMultilinearMap ℂ E F) (g : ∀ i, X i → E i), (∀ i, Integrable (g i) (μ i)) → Integrable (fun x : ∀ i, X i => Φ fun i => g i (x i)) (Measure.pi μ) ∧ ∫ x, Φ (fun i => g i (x i)) ∂Measure.pi μ = Φ fun i => ∫ y, g i y ∂μ i := by
  intro ι _ _ X _ μ _ E _ _ _ F _ _ _ Φ g hg
  constructor
  · have hmeas : AEStronglyMeasurable (fun x : ∀ i, X i => fun i => g i (x i)) (Measure.pi μ) :=
      aestronglyMeasurable_pi_of_forall (f := fun i (x : ∀ i, X i) => g i (x i)) fun i =>
        (hg i).1.comp_quasiMeasurePreserving (Measure.quasiMeasurePreserving_eval μ i)
    have hdom : Integrable (fun x : ∀ i, X i => ‖Φ‖ * ∏ i, ‖g i (x i)‖) (Measure.pi μ) :=
      (Integrable.fintype_prod_dep (f := fun i (y : X i) => ‖g i y‖) fun i => (hg i).norm).const_mul _
    exact hdom.mono' (Φ.cont.comp_aestronglyMeasurable hmeas) (ae_of_all _ fun x => Φ.le_opNorm _)
  · let e : (↥(Finset.univ : Finset ι)) ≃ ι := Equiv.subtypeUnivEquiv Finset.mem_univ
    have hmp := measurePreserving_piCongrLeft μ e
    rw [← hmp.integral_comp']
    have hpt : ∀ z : ∀ i : (Finset.univ : Finset ι), X i,
        (fun i => g i (MeasurableEquiv.piCongrLeft X e z i)) = vecOn g Finset.univ 0 z := by
      intro z; funext i
      have h := Equiv.piCongrLeft_apply_apply X e z ⟨i, Finset.mem_univ i⟩
      simp only [vecOn, dif_pos (Finset.mem_univ i)]
      rw [MeasurableEquiv.coe_piCongrLeft]
      exact congrArg (g i) h
    refine ((integral_congr_ae (ae_of_all _ fun z => congrArg Φ (hpt z))).trans
      (integral_vecOn μ Φ g hg Finset.univ 0)).trans ?_
    simp
end GlobalTheory.MultilinFubini
