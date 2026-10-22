-- Prove2me | solution 1 for LeightonRao.Product.lemma_10
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-21T22:10:29.468797+00:00
-- url     : https://prove2.me/submissions/9684e56d-9bd6-4aa8-86ae-4fff653f06d4

import Mathlib
import Definitions.Def_LeightonRao_Product_Setting

open scoped BigOperators

namespace LeightonRao.Product

variable {V : Type} [Fintype V] [DecidableEq V]

lemma lr_walkLen_nonneg (N : Network V) (d : V → V → ℝ) (hd : IsDistanceFunction d)
    {u v : V} (p : N.graph.Walk u v) : 0 ≤ walkLen N d p := by
  unfold walkLen
  apply List.sum_nonneg
  intro x hx
  obtain ⟨a, _, rfl⟩ := List.mem_map.mp hx
  exact hd.1 _ _

lemma lr_walkLen_concat (N : Network V) (d : V → V → ℝ) {u v w : V}
    (p : N.graph.Walk u v) (h : N.graph.Adj v w) :
    walkLen N d (p.concat h) = walkLen N d p + d v w := by
  unfold walkLen
  simp [SimpleGraph.Walk.darts_concat, List.concat_eq_append]

lemma lr_walkLen_nil (N : Network V) (d : V → V → ℝ) (u : V) :
    walkLen N d (SimpleGraph.Walk.nil : N.graph.Walk u u) = 0 := by
  simp [walkLen]

lemma lr_dist_nonneg (N : Network V) (d : V → V → ℝ) (hd : IsDistanceFunction d) (u v : V) :
    0 ≤ dist N d u v :=
  Real.iInf_nonneg (fun p => lr_walkLen_nonneg N d hd p)

lemma lr_dist_le (N : Network V) (d : V → V → ℝ) (hd : IsDistanceFunction d) {u v : V}
    (p : N.graph.Walk u v) : dist N d u v ≤ walkLen N d p :=
  ciInf_le ⟨0, by rintro _ ⟨q, rfl⟩; exact lr_walkLen_nonneg N d hd q⟩ p

lemma lr_dist_self (N : Network V) (d : V → V → ℝ) (hd : IsDistanceFunction d) (u : V) :
    dist N d u u = 0 :=
  le_antisymm (by simpa [lr_walkLen_nil] using lr_dist_le N d hd (SimpleGraph.Walk.nil : N.graph.Walk u u))
    (lr_dist_nonneg N d hd u u)

lemma lr_dist_adj (N : Network V) (d : V → V → ℝ) (hd : IsDistanceFunction d) (t : V) {u w : V}
    (h : N.graph.Adj u w) : dist N d t w ≤ dist N d t u + d u w := by
  by_cases hE : IsEmpty (N.graph.Walk t u)
  · have hE2 : IsEmpty (N.graph.Walk t w) := ⟨fun q => hE.false (q.concat h.symm)⟩
    have h1 : dist N d t w = 0 := Real.iInf_of_isEmpty _
    have h2 : dist N d t u = 0 := Real.iInf_of_isEmpty _
    rw [h1, h2]; linarith [hd.1 u w]
  · rw [not_isEmpty_iff] at hE
    have : dist N d t w - d u w ≤ dist N d t u := by
      apply le_ciInf
      intro p
      have := lr_dist_le N d hd (p.concat h)
      rw [lr_walkLen_concat] at this
      linarith
    linarith

lemma lr_distFrom_nonneg (N : Network V) (d : V → V → ℝ) (hd : IsDistanceFunction d)
    (T : Finset V) (u : V) : 0 ≤ distFrom N d T u :=
  Real.iInf_nonneg (fun t => lr_dist_nonneg N d hd _ _)

lemma lr_distFrom_le (N : Network V) (d : V → V → ℝ) (hd : IsDistanceFunction d)
    (T : Finset V) (u : V) (t : V) (ht : t ∈ T) : distFrom N d T u ≤ dist N d t u :=
  ciInf_le (f := fun s : T => dist N d s u)
    ⟨0, by rintro _ ⟨q, rfl⟩; exact lr_dist_nonneg N d hd _ _⟩ ⟨t, ht⟩

lemma lr_distFrom_mem (N : Network V) (d : V → V → ℝ) (hd : IsDistanceFunction d)
    (T : Finset V) (t : V) (ht : t ∈ T) : distFrom N d T t = 0 :=
  le_antisymm (by simpa [lr_dist_self N d hd] using lr_distFrom_le N d hd T t t ht)
    (lr_distFrom_nonneg N d hd T t)

lemma lr_distFrom_adj (N : Network V) (d : V → V → ℝ) (hd : IsDistanceFunction d)
    (T : Finset V) (hT : T.Nonempty) {u w : V} (h : N.graph.Adj u w) :
    distFrom N d T w ≤ distFrom N d T u + d u w := by
  have : Nonempty T := ⟨⟨hT.choose, hT.choose_spec⟩⟩
  have : distFrom N d T w - d u w ≤ distFrom N d T u := by
    apply le_ciInf
    intro t
    have h1 := lr_distFrom_le N d hd T w t.1 t.2
    have h2 := lr_dist_adj N d hd t.1 h
    linarith
  linarith

lemma lr_adj_of_pos (N : Network V) {u w : V} (h : 0 < N.C u w) : N.graph.Adj u w := by
  unfold Network.graph
  rw [SimpleGraph.fromRel_adj]
  refine ⟨?_, Or.inl h⟩
  rintro rfl
  rw [N.C_self] at h
  exact lt_irrefl _ h

lemma lr_lip (N : Network V) (d : V → V → ℝ) (hd : IsDistanceFunction d)
    (T : Finset V) (hT : T.Nonempty) (u w : V) :
    N.C u w * |distFrom N d T w - distFrom N d T u| ≤ N.C u w * d u w := by
  rcases (N.C_nonneg u w).lt_or_eq with hC | hC
  · apply mul_le_mul_of_nonneg_left _ hC.le
    have h1 := lr_distFrom_adj N d hd T hT (lr_adj_of_pos N hC)
    have hC' : 0 < N.C w u := by rw [N.C_symm]; exact hC
    have h2 := lr_distFrom_adj N d hd T hT (lr_adj_of_pos N hC')
    rw [hd.2 w u] at h2
    rw [abs_le]; constructor <;> linarith
  · rw [← hC]; simp

lemma lr_integral_step (a b c : ℝ) :
    ∫ r, (Set.Ico a b).indicator (fun _ => c) r = max (b - a) 0 * c := by
  rw [MeasureTheory.integral_indicator_const _ measurableSet_Ico]
  simp [Real.volume_Ico, ENNReal.toReal_ofReal', MeasureTheory.Measure.real]

lemma lr_integrable_step (a b c : ℝ) :
    MeasureTheory.Integrable (fun r => (Set.Ico a b).indicator (fun _ => c) r) := by
  apply MeasureTheory.IntegrableOn.integrable_indicator _ measurableSet_Ico
  exact MeasureTheory.integrableOn_const (by simp [Real.volume_Ico])


lemma lr_piSum_nonneg (π : V → ℝ) (hπ : ∀ u, 0 ≤ π u) (U : Finset V) : 0 ≤ piSum π U :=
  Finset.sum_nonneg fun u _ => hπ u

lemma lemma_10_core (N : Network V) (hconn : IsConnectedNet N)
    (π : V → ℝ) (hπ : IsPMFPWeight π) (hp : 2 ≤ (support π).card) (d : V → V → ℝ)
    (hd : IsDistanceFunction d) (T : Finset V)
    (hT : 2 * ((support π).card : ℝ) ≤ 3 * piSum π T)
    (hsum : 1 / (2 * ((support π).card : ℝ)) ≤ ∑ u ∈ Tᶜ, π u * distFrom N d T u) :
    ∃ U : Finset V, 0 < piSum π U ∧ 0 < piSum π Uᶜ ∧
      weightedRatio N π U ≤ 6 * totalWeight N d := by
  have hπ0 : ∀ u, 0 ≤ π u := hπ.1
  set n : ℝ := ((support π).card : ℝ) with hn_def
  have hn2 : (2:ℝ) ≤ n := by rw [hn_def]; exact_mod_cast hp
  have hTpos : 0 < piSum π T := by linarith
  have hTne : T.Nonempty := by
    rcases T.eq_empty_or_nonempty with h | h
    · rw [h] at hTpos; simp [piSum] at hTpos
    · exact h
  set δ : V → ℝ := fun u => distFrom N d T u with hδ
  have hδnn : ∀ u, 0 ≤ δ u := fun u => lr_distFrom_nonneg N d hd T u
  have hδT : ∀ t ∈ T, δ t = 0 := fun t ht => lr_distFrom_mem N d hd T t ht
  set W := totalWeight N d with hW
  have hWnn : 0 ≤ W := by
    rw [hW, totalWeight]
    apply mul_nonneg (by norm_num)
    exact Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun v _ =>
      mul_nonneg (N.C_nonneg u v) (hd.1 u v)
  -- Claim A
  set A := ∑ u, ∑ v, N.C u v * max (δ v - δ u) 0 with hA
  have hA_le : A ≤ W := by
    have hswap : ∑ u, ∑ v, N.C u v * max (δ u - δ v) 0 = A := by
      rw [hA, Finset.sum_comm]
      refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
      rw [N.C_symm]
    have h2 : A + A ≤ ∑ u, ∑ v, N.C u v * d u v := by
      calc A + A = ∑ u, ∑ v, N.C u v * |δ v - δ u| := by
            conv_lhs => arg 1; rw [← hswap]
            rw [hA, ← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun u _ => ?_
            rw [← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun v _ => ?_
            rw [← mul_add]
            congr 1
            rcases le_total (δ u) (δ v) with h | h
            · rw [abs_of_nonneg (by linarith), max_eq_right (by linarith),
                max_eq_left (by linarith)]; ring
            · rw [abs_of_nonpos (by linarith), max_eq_left (by linarith),
                max_eq_right (by linarith)]; ring
        _ ≤ ∑ u, ∑ v, N.C u v * d u v := by
            apply Finset.sum_le_sum; intro u _
            apply Finset.sum_le_sum; intro v _
            exact lr_lip N d hd T hTne u v
    rw [hW, totalWeight]; linarith
  have hAnn : ∀ u v, 0 ≤ N.C u v * max (δ v - δ u) 0 :=
    fun u v => mul_nonneg (N.C_nonneg u v) (le_max_right _ _)
  -- Claim B
  set B := ∑ u, ∑ v, π u * π v * max (δ v - δ u) 0 with hB
  have hB_ge : 1 / 3 ≤ B := by
    have hS : 1 / (2 * n) ≤ ∑ v, π v * δ v := by
      calc 1 / (2 * n) ≤ ∑ u ∈ Tᶜ, π u * δ u := hsum
        _ ≤ ∑ v, π v * δ v := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun v _ _ => mul_nonneg (hπ0 v) (hδnn v))
    have h1 : piSum π T * ∑ v, π v * δ v ≤ B := by
      calc piSum π T * ∑ v, π v * δ v = ∑ u ∈ T, ∑ v, π u * π v * max (δ v - δ u) 0 := by
            rw [piSum, Finset.sum_mul]
            refine Finset.sum_congr rfl fun u hu => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun v _ => ?_
            rw [hδT u hu, sub_zero, max_eq_left (hδnn v)]; ring
        _ ≤ B := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun u _ _ => Finset.sum_nonneg fun v _ =>
              mul_nonneg (mul_nonneg (hπ0 u) (hπ0 v)) (le_max_right _ _))
    have h3 : (1:ℝ) / 3 ≤ piSum π T * ∑ v, π v * δ v := by
      have hnpos : 0 < n := by linarith
      have : (1:ℝ) / 3 = (2 * n / 3) * (1 / (2 * n)) := by field_simp
      rw [this]
      apply mul_le_mul (by linarith) hS (by positivity) hTpos.le
    linarith
  -- the step function
  let f : ℝ → ℝ := fun r => ∑ u, ∑ v,
    (Set.Ico (δ u) (δ v)).indicator (fun _ => N.C u v - 6 * W * (π u * π v)) r
  have hint : ∫ r, f r = A - 6 * W * B := by
    simp only [f]
    rw [MeasureTheory.integral_finsetSum _ (fun u _ => MeasureTheory.integrable_finsetSum _
      (fun v _ => lr_integrable_step _ _ _))]
    simp_rw [MeasureTheory.integral_finsetSum _ (fun v _ => lr_integrable_step _ _ _),
      lr_integral_step]
    rw [hA, hB, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun v _ => ?_
    ring
  -- f r in terms of a cut
  have hf_eq : ∀ r, f r = cutCap N (Finset.univ.filter (fun u => δ u ≤ r)) -
      6 * W * (piSum π (Finset.univ.filter (fun u => δ u ≤ r)) *
        piSum π (Finset.univ.filter (fun u => δ u ≤ r))ᶜ) := by
    intro r
    set U := Finset.univ.filter (fun u => δ u ≤ r) with hUdef
    have key : cutCap N U - 6 * W * (piSum π U * piSum π Uᶜ) =
        ∑ u ∈ U, ∑ v ∈ Uᶜ, (N.C u v - 6 * W * (π u * π v)) := by
      rw [cutCap, piSum, piSum, Finset.sum_mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    have hc : Uᶜ = Finset.univ.filter (fun u => ¬ δ u ≤ r) := Finset.compl_filter _
    rw [key, hc, hUdef]
    simp only [f, Finset.sum_filter]
    refine Finset.sum_congr rfl fun u _ => ?_
    split_ifs with hu
    · refine Finset.sum_congr rfl fun v _ => ?_
      by_cases hv : δ v ≤ r
      · simp [Set.indicator_apply, Set.mem_Ico, hu, hv, not_lt.mpr hv]
      · simp [Set.indicator_apply, Set.mem_Ico, hu, hv, lt_of_not_ge hv]
    · refine Finset.sum_eq_zero fun v _ => ?_
      simp only [Set.indicator_apply, Set.mem_Ico]
      rw [if_neg]
      tauto
  rcases hWnn.lt_or_eq with hWpos | hW0
  · have hneg : ∫ r, f r < 0 := by
      rw [hint]; nlinarith
    obtain ⟨r, hr⟩ : ∃ r, f r < 0 := by
      by_contra hcon
      push_neg at hcon
      exact absurd (MeasureTheory.integral_nonneg hcon) (not_le.mpr hneg)
    set U := Finset.univ.filter (fun u => δ u ≤ r)
    rw [hf_eq] at hr
    have hcut : 0 ≤ cutCap N U := Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun v _ =>
      N.C_nonneg u v
    have hprod : 0 < piSum π U * piSum π Uᶜ := by
      by_contra hc; push_neg at hc; nlinarith
    have hU0 := lr_piSum_nonneg π hπ0 U
    have hUc0 := lr_piSum_nonneg π hπ0 Uᶜ
    have hU : 0 < piSum π U := by
      rcases hU0.lt_or_eq with h | h
      · exact h
      · rw [← h] at hprod; simp at hprod
    have hUc : 0 < piSum π Uᶜ := by
      rcases hUc0.lt_or_eq with h | h
      · exact h
      · rw [← h] at hprod; simp at hprod
    refine ⟨U, hU, hUc, ?_⟩
    rw [weightedRatio, div_le_iff₀ hprod]; linarith
  · exfalso
    have hA0 : A = 0 := le_antisymm (by linarith)
      (Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun v _ => hAnn u v)
    have hterm : ∀ u v, N.C u v * max (δ v - δ u) 0 = 0 := by
      intro u v
      have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun u _ =>
        Finset.sum_nonneg fun v _ => hAnn u v)).mp hA0 u (Finset.mem_univ _)
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun v _ => hAnn u v)).mp h1 v (Finset.mem_univ _)
    set U := Finset.univ.filter (fun u => δ u ≤ 0) with hUdef
    have hUne : U.Nonempty := by
      obtain ⟨t, ht⟩ := hTne
      exact ⟨t, by simp [hUdef, hδT t ht]⟩
    have hUcne : Uᶜ.Nonempty := by
      by_contra hc
      rw [Finset.not_nonempty_iff_eq_empty] at hc
      have hall : ∀ u, δ u = 0 := by
        intro u
        have : u ∉ Uᶜ := by rw [hc]; simp
        rw [Finset.mem_compl, not_not, hUdef, Finset.mem_filter] at this
        exact le_antisymm this.2 (hδnn u)
      have : ∑ u ∈ Tᶜ, π u * distFrom N d T u = 0 :=
        Finset.sum_eq_zero fun u _ => by
          have := hall u
          simp only [hδ] at this
          rw [this, mul_zero]
      rw [this] at hsum
      have : 0 < 1 / (2 * n) := by positivity
      linarith
    have hcut := hconn U hUne hUcne
    have : cutCap N U = 0 := by
      apply Finset.sum_eq_zero
      intro u hu
      apply Finset.sum_eq_zero
      intro v hv
      rw [hUdef, Finset.mem_filter] at hu
      rw [Finset.mem_compl, hUdef, Finset.mem_filter] at hv
      push_neg at hv
      have hpos : 0 < max (δ v - δ u) 0 := lt_max_of_lt_left (by linarith [hv (Finset.mem_univ _)])
      have := hterm u v
      rcases mul_eq_zero.mp this with h | h
      · exact h
      · linarith
    linarith

end LeightonRao.Product

open LeightonRao.Product


theorem solution {V : Type} [Fintype V] [DecidableEq V] (N : Network V) (hconn : IsConnectedNet N)
    (π : V → ℝ) (hπ : IsPMFPWeight π) (hp : 2 ≤ (support π).card) (d : V → V → ℝ)
    (hd : IsDistanceFunction d) (T : Finset V)
    (hT : 2 * ((support π).card : ℝ) ≤ 3 * piSum π T)
    (hsum : 1 / (2 * ((support π).card : ℝ)) ≤ ∑ u ∈ Tᶜ, π u * distFrom N d T u) :
    ∃ U : Finset V, 0 < piSum π U ∧ 0 < piSum π Uᶜ ∧
      weightedRatio N π U ≤ 6 * totalWeight N d := by
  exact lemma_10_core N hconn π hπ hp d hd T hT hsum
