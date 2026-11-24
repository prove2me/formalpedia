-- Prove2me | solution 1 for Kyprianou.Ch03.strongMarkovGridPositionLawV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T08:18:10.510806+00:00
-- url     : https://prove2.me/submissions/a71de6b7-0cc4-47cd-98d5-4e0a0e53f074

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_Kyprianou_Ch03_strongMarkovOrderedIncrementLawV1
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

private theorem prefix_eq {A : Type}
    (Z : NNReal → A → ℝ) (t : ℕ → NNReal) (n : ℕ) :
    (fun w : A => fun i : Fin n => Z (t (i.val+1)) w - Z (t 0) w) =
      (fun v : Fin n → ℝ => fun i : Fin n =>
        ∑ k ∈ Finset.range (i.val+1), (if h : k < n then v ⟨k,h⟩ else 0)) ∘
      (fun w : A => fun i : Fin n => Z (t (i.val+1)) w - Z (t i.val) w) := by
  funext w i
  simp only [Function.comp_apply]
  have hsum (m : ℕ) : (∑ k ∈ Finset.range m, (Z (t (k+1)) w - Z (t k) w)) =
      Z (t m) w - Z (t 0) w := by
    induction m with
    | zero => simp
    | succ m ih => rw [Finset.sum_range_succ, ih]; ring
  rw [← hsum]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [dif_pos (lt_of_lt_of_le (Finset.mem_range.mp hk) i.isLt)]

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (X : NNReal → Omega → Real)
    (hAdapt : ∀ t : NNReal, Measurable[F t] (X t))
    (hOne : ∀ (s t : NNReal), s ≤ t → ∀ (A : Set Omega), MeasurableSet[F s] A →
      ∀ (C : Set Real), MeasurableSet C →
      P (A ∩ {w | X t w - X s w ∈ C}) =
        P A * P {w | X t w - X s w ∈ C})
    (hX : IsLevyProcess X P)
    (s : NNReal) (A : Set Omega) (hA : MeasurableSet[F s] A)
    (t : ℕ → NNReal) (ht : Monotone t) (ht0 : t 0 = 0) (n : ℕ) :
    Measure.map (fun w : Omega => fun i : Fin n =>
      X (s+t (i.val+1)) w - X s w) (P.restrict A) =
    P A • Measure.map (fun w : Omega => fun i : Fin n =>
      X (t (i.val+1)) w) P := by
  classical
  let g : (Fin n → ℝ) → (Fin n → ℝ) := fun v i =>
    ∑ k ∈ Finset.range (i.val+1), (if h : k < n then v ⟨k,h⟩ else 0)
  have hg : Measurable g := by
    refine measurable_pi_lambda _ fun i => Finset.measurable_sum _ fun k _ => ?_
    split_ifs <;> first | exact measurable_pi_apply _ | exact measurable_const
  have hm (u : NNReal) : Measurable (X u) := (hAdapt u).mono (F.le u) le_rfl
  let U : Omega → (Fin n → ℝ) := fun w i => X (s+t (i.val+1)) w - X (s+t i.val) w
  let V : Omega → (Fin n → ℝ) := fun w i => X (t (i.val+1)) w - X (t i.val) w
  have hU : Measurable U := measurable_pi_iff.mpr (fun i => (hm _).sub (hm _))
  have hV : Measurable V := measurable_pi_iff.mpr (fun i => (hm _).sub (hm _))
  have keyU : (fun w : Omega => fun i : Fin n => X (s+t (i.val+1)) w - X s w) = g ∘ U := by
    simpa only [ht0, add_zero] using prefix_eq X (fun k => s+t k) n
  have keyV : (fun w : Omega => fun i : Fin n => X (t (i.val+1)) w) = g ∘ V := by
    simpa only [ht0, hX.start_zero, sub_zero] using prefix_eq X t n
  have hInc : Measure.map U (P.restrict A) = P A • Measure.map V P :=
    Kyprianou.Ch03.strongMarkovOrderedIncrementLawV1 P F X hAdapt hOne hX s A hA t ht ht0 n
  rw [keyU, keyV, ← Measure.map_map hg hU, ← Measure.map_map hg hV, hInc, Measure.map_smul]
