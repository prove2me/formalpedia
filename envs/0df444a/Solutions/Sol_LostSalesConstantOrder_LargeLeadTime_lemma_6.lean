-- Prove2me | solution 1 for LostSalesConstantOrder.LargeLeadTime.lemma_6
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T11:38:42.949279+00:00
-- url     : https://prove2.me/submissions/ab02905b-f507-4fbe-bfeb-585ee4f736bd

import Theorems.Thm_LostSalesConstantOrder_LargeLeadTime_lemma_3
import Definitions.Def_LostSalesConstantOrder_LargeLeadTime_RandomWalk

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators

namespace LSCOL6

open CappedBaseStock LostSalesConstantOrder.LargeLeadTime

/-- reversal of the first `k` coordinates -/
def revIdx (k : ℕ) (i : ℕ) : ℕ := if i < k then k - 1 - i else i

lemma revIdx_invol (k : ℕ) (i : ℕ) : revIdx k (revIdx k i) = i := by
  unfold revIdx
  split_ifs with h1 h2 <;> omega

/-- the involution of `ℕ` reversing `0, …, k - 1` -/
def revEquiv (k : ℕ) : ℕ ≃ ℕ where
  toFun := revIdx k
  invFun := revIdx k
  left_inv := revIdx_invol k
  right_inv := revIdx_invol k

def rev (k : ℕ) (d : DemandPath) : DemandPath := fun i => d (revIdx k i)

lemma measurable_rev (k : ℕ) : Measurable (rev k) :=
  measurable_pi_lambda _ (fun i => measurable_pi_apply _)

lemma map_rev (P : DemandLaw) (k : ℕ) : (demandPathLaw P).map (rev k) = demandPathLaw P := by
  unfold demandPathLaw
  refine Measure.eq_infinitePi _ (fun s t ht => ?_)
  rw [Measure.map_apply (measurable_rev k) (MeasurableSet.pi s.countable_toSet
    (fun i _ => ht i))]
  have hset : rev k ⁻¹' (Set.pi (↑s) t) =
      Set.pi (↑(s.map (revEquiv k).toEmbedding)) (fun i => t (revIdx k i)) := by
    ext d
    simp only [Set.mem_preimage, Set.mem_pi, Finset.mem_coe, Finset.mem_map,
      forall_exists_index, and_imp, rev]
    constructor
    · rintro h i j hj rfl
      have := h j hj
      simp only [Equiv.toEmbedding_apply, revEquiv, Equiv.coe_fn_mk]
      rwa [revIdx_invol]
    · intro h j hj
      have := h (revIdx k j) j hj rfl
      rwa [revIdx_invol] at this
  rw [hset, Measure.infinitePi_pi _ (fun i _ => ht _), Finset.prod_map]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  simp only [Equiv.toEmbedding_apply, revEquiv, Equiv.coe_fn_mk, revIdx_invol]

/-- the term of lemma 3's maximum -/
noncomputable def Tm {L : ℕ} (x : Fin L → ℝ≥0) (I : ℝ≥0) (k : ℕ) (d : DemandPath) (j : ℕ) : ℝ :=
  (∑ i ∈ Finset.Icc (k + 1 - j) k, ((slot x (i - 1) : ℝ) - (d (i - 1) : ℝ))) +
    if j = k then (I : ℝ) else 0

lemma sum_rev (k j : ℕ) (hj : j ≤ k) (f : ℕ → ℝ) :
    ∑ i ∈ Finset.Icc (k + 1 - j) k, f (revIdx k (i - 1)) = ∑ i ∈ Finset.Icc 1 j, f (i - 1) := by
  refine Finset.sum_nbij' (fun i => k + 1 - i) (fun i => k + 1 - i) ?_ ?_ ?_ ?_ ?_
  · intro i hi
    simp_all [Finset.mem_Icc]
    omega
  · intro i hi
    simp_all [Finset.mem_Icc]
    omega
  · intro i hi
    simp_all [Finset.mem_Icc]
    omega
  · intro i hi
    simp_all [Finset.mem_Icc]
    omega
  · intro i hi
    simp only [Finset.mem_Icc] at hi
    congr 1
    unfold revIdx
    rw [if_pos (by omega)]
    omega

lemma vTerm_eq {L : ℕ} (x : Fin L → ℝ≥0) (I : ℝ≥0) (k : ℕ) (d : DemandPath) (j : ℕ)
    (hj : j ≤ k) : vTerm x I k d j = Tm x I k (rev k d) j := by
  unfold vTerm Tm
  rw [Finset.sum_sub_distrib]
  congr 2
  exact (sum_rev k j hj (fun i => (d i : ℝ))).symm

lemma Vk_eq {L : ℕ} (x : Fin L → ℝ≥0) (I : ℝ≥0) (k : ℕ) (d : DemandPath) :
    Vk x I k d = (Finset.range (k + 1)).sup' Finset.nonempty_range_add_one
      (Tm x I k (rev k d)) := by
  unfold Vk
  refine Finset.sup'_congr _ rfl (fun j hj => ?_)
  exact vTerm_eq x I k d j (by have := Finset.mem_range.1 hj; omega)

lemma measurable_Tm_sup {L : ℕ} (x : Fin L → ℝ≥0) (I : ℝ≥0) (k : ℕ) :
    Measurable (fun d : DemandPath => (Finset.range (k + 1)).sup' Finset.nonempty_range_add_one
      (Tm x I k d)) := by
  have : ∀ j, Measurable (fun d : DemandPath => Tm x I k d j) := by
    intro j
    unfold Tm
    fun_prop
  exact Finset.measurable_range_sup'' (f := fun j d => Tm x I k d j) (fun j _ => this j)

lemma integral_Vk (P : DemandLaw) {L : ℕ} (x : Fin L → ℝ≥0) (I : ℝ≥0) (k : ℕ) :
    ∫ d, Vk x I k d ∂demandPathLaw P =
      ∫ d, (Finset.range (k + 1)).sup' Finset.nonempty_range_add_one (Tm x I k d)
        ∂demandPathLaw P := by
  simp_rw [Vk_eq]
  have := integral_map (μ := demandPathLaw P) (measurable_rev k).aemeasurable
    (measurable_Tm_sup x I k).aestronglyMeasurable
  rw [map_rev] at this
  exact this.symm

lemma pipe_le (prm : Parameters) (π : AdmissiblePolicy) (ω : Sample) (Q : ℝ≥0)
    (h : ∀ t, order π t ω ≤ Q) (t : ℕ) : ∀ i, (run prm π ω t).2 i ≤ Q := by
  induction t with
  | zero => intro i; simp [run, initialState]
  | succ t ih =>
    intro i
    simp only [run, step]
    split_ifs
    · exact ih _
    · exact h t

theorem main (P : DemandLaw) (prm : Parameters)
    (h3 : FiniteThirdMoment P) (hnd : NonDeterministic P)
    (π : AdmissiblePolicy) (hπ : OrdersBounded P π (Qlevel P prm))
    (x : Fin prm.L → ℝ≥0) (I : ℝ≥0) (hmin : IsWindowMinimizer P prm x I) (t₀ : ℕ) :
    ENNReal.ofReal
        (prm.h * ∑ k ∈ Finset.Icc 1 prm.L, ∫ d, Vk x I k d ∂demandPathLaw P +
          prm.p * ((∫ d, (endInventory prm x I d : ℝ) ∂demandPathLaw P) -
            I + prm.L * mean P - ∑ i, (x i : ℝ))) ≤
      costWindow P prm π t₀ := by
  obtain ⟨h1, h2⟩ := lemma_3 P prm h3 hnd
  simp_rw [integral_Vk]
  have hW := h2 x I
  unfold Tm
  rw [← hW, h1 π t₀]
  calc windowCost P prm x I = ∫⁻ _ω, windowCost P prm x I ∂sampleLaw P := by simp
    _ ≤ _ := by
      apply lintegral_mono_ae
      filter_upwards [hπ] with ω hω
      exact hmin.2 _ _ (pipe_le prm π ω _ hω t₀)

end LSCOL6

open LostSalesConstantOrder.LargeLeadTime in
theorem solution (P : CappedBaseStock.DemandLaw) (prm : CappedBaseStock.Parameters)
    (h3 : FiniteThirdMoment P) (hnd : NonDeterministic P)
    (π : CappedBaseStock.AdmissiblePolicy) (hπ : OrdersBounded P π (Qlevel P prm))
    (x : Fin prm.L → ℝ≥0) (I : ℝ≥0) (hmin : IsWindowMinimizer P prm x I) (t₀ : ℕ) :
    ENNReal.ofReal
        (prm.h * ∑ k ∈ Finset.Icc 1 prm.L, ∫ d, Vk x I k d ∂CappedBaseStock.demandPathLaw P +
          prm.p * ((∫ d, (endInventory prm x I d : ℝ) ∂CappedBaseStock.demandPathLaw P) -
            I + prm.L * CappedBaseStock.mean P - ∑ i, (x i : ℝ))) ≤
      costWindow P prm π t₀ :=
  LSCOL6.main P prm h3 hnd π hπ x I hmin t₀
