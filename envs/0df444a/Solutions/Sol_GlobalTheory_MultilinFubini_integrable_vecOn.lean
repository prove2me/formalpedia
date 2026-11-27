-- Prove2me | solution 1 for GlobalTheory.MultilinFubini.integrable_vecOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T06:05:54.536585+00:00
-- url     : https://prove2.me/submissions/24be98ac-dc2f-45a1-9cac-54430994222c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntegralContinuousMultilinearMapPiMeasure
import Theorems.Thm_GlobalTheory_MultilinFubini_aestronglyMeasurable_pi_of_forall

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
theorem _root_.solution (μ : ∀ i, Measure (X i)) [∀ i, SigmaFinite (μ i)]
    (Φ : ContinuousMultilinearMap ℂ E F) (g : ∀ i, X i → E i) (hg : ∀ i, Integrable (g i) (μ i))
    (s : Finset ι) (m : ∀ i, E i) :
    Integrable (fun x => Φ (vecOn g s m x)) (Measure.pi fun i : s => μ i) := by
  have hmeas : AEStronglyMeasurable (fun x => vecOn g s m x) (Measure.pi fun i : s => μ i) := by
    refine aestronglyMeasurable_pi_of_forall (f := fun i x => vecOn g s m x i) fun i => ?_
    by_cases hi : i ∈ s
    · simp only [vecOn, dif_pos hi]
      exact (hg i).1.comp_quasiMeasurePreserving
        (Measure.quasiMeasurePreserving_eval (fun j : s => μ j) ⟨i, hi⟩)
    · simp only [vecOn, dif_neg hi]; exact aestronglyMeasurable_const
  have hdom : Integrable (fun x : ∀ j : s, X j => ‖Φ‖ * ((∏ j : s, ‖g j (x j)‖) * ∏ i ∈ sᶜ, ‖m i‖))
      (Measure.pi fun i : s => μ i) :=
    ((Integrable.fintype_prod_dep (f := fun (j : s) (y : X j) => ‖g j y‖)
      fun j => (hg j).norm).mul_const _).const_mul _
  refine hdom.mono' (Φ.cont.comp_aestronglyMeasurable hmeas) (ae_of_all _ fun x => ?_)
  refine (Φ.le_opNorm _).trans (le_of_eq ?_)
  congr 1
  rw [← Finset.prod_mul_prod_compl s]
  congr 1
  · rw [← Finset.prod_coe_sort s]
    refine Finset.prod_congr rfl fun j _ => ?_
    simp [vecOn, j.2]
  · refine Finset.prod_congr rfl fun i hi => ?_
    simp [vecOn, Finset.mem_compl.1 hi]
end GlobalTheory.MultilinFubini
