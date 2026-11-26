-- Prove2me | solution 1 for Malliavin.measure_coord_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:56:36.147116+00:00
-- url     : https://prove2.me/submissions/bf3adf1c-c527-4d58-ae89-ac5eb51f0a55

import Definitions.Def_Malliavin_Symmetrization
import Definitions.Def_Malliavin_Simplex
import Theorems.Thm_Malliavin_mem_symmetricSubmodule
attribute [local simp] Malliavin.mem_symmetricSubmodule



set_option autoImplicit false
open MeasureTheory Finset Set
open scoped ENNReal
noncomputable section
open Malliavin
variable {T : Type*} {E : Type*}
variable [MeasurableSpace T] [TopologicalSpace T] [LinearOrder T] [OrderClosedTopology T]
  [SecondCountableTopology T] [OpensMeasurableSpace T]
variable {μ : Measure T} [SigmaFinite μ]
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
namespace Malliavin
theorem _root_.solution [NullSingletonClass μ] {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    Measure.pi (fun _ : Fin n => μ) {t : Fin n → T | t i = t j} = 0 := by
  cases n with
  | zero => exact i.elim0
  | succ m =>
    obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq hij.symm
    subst hk
    let e : (Fin (m + 1) → T) ≃ᵐ T × (Fin m → T) :=
      MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => T) i
    have hmp : MeasurePreserving e (Measure.pi fun _ : Fin (m + 1) => μ)
        (μ.prod (Measure.pi fun _ : Fin m => μ)) :=
      measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) => μ) i
    let s : Set (T × (Fin m → T)) := {p | p.1 = p.2 k}
    have hs : MeasurableSet s := by
      have : s = {p : T × (Fin m → T) | p.1 ≤ p.2 k} ∩ {p | p.2 k ≤ p.1} := by
        ext p
        simp only [le_antisymm_iff, mem_ofPred_eq, mem_inter_iff, s]
      rw [this]
      exact (measurableSet_le (by fun_prop) (by fun_prop)).inter
        (measurableSet_le (by fun_prop) (by fun_prop))
    have hpre : {t : Fin (m + 1) → T | t i = t (i.succAbove k)} = e ⁻¹' s := rfl
    have h0 : ∀ x : T, (Measure.pi fun _ : Fin m => μ) (Prod.mk x ⁻¹' s) = 0 := by
      intro x
      have hset : Prod.mk x ⁻¹' s =
          Set.pi Set.univ (Function.update (fun _ : Fin m => (Set.univ : Set T)) k {x}) := by
        ext u
        simp only [s, Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_univ_pi]
        constructor
        · intro h l
          by_cases hl : l = k
          · rw [hl]
            simp only [h, Function.update_self, mem_singleton_iff]
          · simp only [ne_eq, hl, not_false_eq_true, Function.update_of_ne, Set.mem_univ]
        · intro h
          have hk := h k
          simp only [Function.update_self, mem_singleton_iff] at hk
          exact hk.symm
      rw [hset, Measure.pi_pi]
      exact Finset.prod_eq_zero (Finset.mem_univ k)
        (by simp [(Set.subsingleton_singleton).measure_zero μ])
    rw [hpre, ← Measure.map_apply hmp.measurable hs, hmp.map_eq, Measure.prod_apply hs]
    simp only [h0, lintegral_const, zero_mul]
end Malliavin
