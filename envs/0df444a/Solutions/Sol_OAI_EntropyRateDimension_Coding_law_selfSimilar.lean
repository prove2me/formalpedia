-- Prove2me | solution 1 for OAI.EntropyRateDimension.Coding.law_selfSimilar
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T06:35:04.771993+00:00
-- url     : https://prove2.me/submissions/a87001d5-a4cd-4a99-82ed-a6380a0edf34

import Mathlib
import Definitions.Def_SelfSimilar
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Basic
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteEntropy
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteDistribution
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_MeasureEntropy
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_RandomGrid
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Boundary
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_TranslationGain
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FairPairs
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_ProductLaw
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_GridCoupling
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteRefinement
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_SumsetBound
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_WordTypes
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_DigitSumset
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Bernoulli
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Coding

open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.Coding
universe uι
open scoped BigOperators ENNReal
open MeasureTheory
open MeasureTheory Metric Set Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set ProbabilityTheory
open scoped Topology
open Filter Set
open scoped Topology
variable {ι : Type uι} [Fintype ι] [Nonempty ι]
variable [MeasurableSpace ι] [MeasurableSingletonClass ι]
def h41n_cons {κ : Type*} (p : κ × (ℕ → κ)) : ℕ → κ
  | 0 => p.1
  | k+1 => p.2 k

theorem h41n_cons_meas {κ : Type*} [MeasurableSpace κ] :
    Measurable (h41n_cons (κ := κ)) := by
  apply measurable_pi_lambda
  intro n
  cases n with
  | zero => exact measurable_fst
  | succ k => exact (measurable_pi_apply k).comp measurable_snd

theorem h41n_prod_split (s : Finset ℕ) (f : ℕ → ℝ≥0∞) :
    ∏ i ∈ s, f i = (if 0 ∈ s then f 0 else 1) *
      ∏ k ∈ s.preimage Nat.succ (Nat.succ_injective.injOn), f (k+1) := by
  classical
  let g : ℕ → ℝ≥0∞ := fun i => if i = 0 then 1 else f i
  have h1 : ∏ k ∈ s.preimage Nat.succ (Nat.succ_injective.injOn), f (k+1) = ∏ i ∈ s, g i := by
    rw [← Finset.prod_preimage Nat.succ s (Nat.succ_injective.injOn) g]
    · apply Finset.prod_congr rfl
      intro k _
      simp [g]
    · intro x _ hx
      have : x = 0 := by
        by_contra h
        exact hx ⟨x - 1, by simp only [Nat.succ_eq_add_one]; omega⟩
      simp [g, this]
  rw [h1]
  have h2 : ∏ i ∈ s, f i = ∏ i ∈ s, ((if i = 0 then f 0 else 1) * g i) := by
    apply Finset.prod_congr rfl
    intro i _
    by_cases h : i = 0
    · subst h; simp [g]
    · simp [g, h]
  rw [h2, Finset.prod_mul_distrib, Finset.prod_ite_eq']

theorem h41n_addr_eq {κ : Type*} [Fintype κ] [Nonempty κ] [MeasurableSpace κ]
    [MeasurableSingletonClass κ] (S : System κ) :
    ((Coding.symbolMeasure S).prod (Coding.addressMeasure S)).map h41n_cons =
      Coding.addressMeasure S := by
  classical
  unfold Coding.addressMeasure
  apply Measure.eq_infinitePi
  intro s t ht
  rw [Measure.map_apply h41n_cons_meas (MeasurableSet.pi s.countable_toSet (fun i _ => ht i))]
  have hpre : h41n_cons ⁻¹' (Set.pi ↑s t) = (if 0 ∈ s then t 0 else Set.univ) ×ˢ
      Set.pi ↑(s.preimage Nat.succ (Nat.succ_injective.injOn)) (fun k => t (k+1)) := by
    ext ⟨a, ω⟩
    simp only [Set.mem_preimage, Set.mem_pi, Finset.mem_coe, Set.mem_prod, Finset.mem_preimage]
    constructor
    · intro h
      refine ⟨?_, fun k hk => h (k+1) hk⟩
      split_ifs with h0
      · exact h 0 h0
      · trivial
    · rintro ⟨h1, h2⟩ i hi
      cases i with
      | zero => rw [if_pos hi] at h1; exact h1
      | succ k => exact h2 k hi
  rw [hpre, Measure.prod_prod, Measure.infinitePi_pi (fun _ => Coding.symbolMeasure S) (t := fun k => t (k+1)) (fun k _ => ht (k+1)), h41n_prod_split s]
  congr 1
  split_ifs <;> simp

theorem h41n_point_cons {κ : Type*} [Fintype κ] [Nonempty κ] (S : System κ) (p : κ × (ℕ → κ)) :
    Coding.point S (h41n_cons p) = S.affine p.1 (Coding.point S p.2) := by
  unfold Coding.point
  rw [(Coding.term_summable S (h41n_cons p)).tsum_eq_zero_add]
  have h0 : Coding.term S (h41n_cons p) 0 = S.offset p.1 := by
    simp [Coding.term, Coding.slope_zero, h41n_cons]
  have hs : ∀ n, Coding.term S (h41n_cons p) (n+1) = S.ratio p.1 * Coding.term S p.2 n := by
    intro n
    simp only [Coding.term, Coding.slope, Finset.prod_range_succ']
    simp [h41n_cons]
    ring
  simp only [h0, hs, tsum_mul_left, System.affine]
  ring

theorem h41n_prod_apply {κ : Type*} [Fintype κ] [Nonempty κ] [MeasurableSpace κ]
    [MeasurableSingletonClass κ] (S : System κ) {C : Set (κ × (ℕ → κ))} (hC : MeasurableSet C) :
    ((Coding.symbolMeasure S).prod (Coding.addressMeasure S)) C =
      ∑ i, ENNReal.ofReal (S.weight i) * Coding.addressMeasure S (Prod.mk i ⁻¹' C) := by
  rw [Measure.prod_apply hC]
  unfold Coding.symbolMeasure
  rw [lintegral_finset_sum_measure]
  apply Finset.sum_congr rfl
  intro i _
  rw [lintegral_smul_measure, lintegral_dirac, smul_eq_mul]

theorem solution (S : System ι) : S.SelfSimilar (law S) := by
  unfold System.SelfSimilar law
  have hA := h41n_addr_eq S
  have haff : ∀ i, Measurable (S.affine i) := fun i => by unfold System.affine; fun_prop
  ext A hAm
  conv_lhs => rw [← hA]
  rw [Measure.map_map (point_measurable S) h41n_cons_meas,
    Measure.map_apply ((point_measurable S).comp h41n_cons_meas) hAm,
    h41n_prod_apply S (((point_measurable S).comp h41n_cons_meas) hAm),
    Measure.coe_finset_sum, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [Measure.smul_apply, smul_eq_mul, Measure.map_apply (haff i) hAm,
    Measure.map_apply (point_measurable S) ((haff i) hAm)]
  congr 2
  ext ω
  simp [h41n_point_cons]

