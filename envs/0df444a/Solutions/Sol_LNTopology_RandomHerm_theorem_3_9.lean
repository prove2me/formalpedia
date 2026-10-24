-- Prove2me | solution 1 for LNTopology.RandomHerm.theorem_3_9
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T02:52:36.951708+00:00
-- url     : https://prove2.me/submissions/5428e5f3-e127-4537-86e4-84ff185bfd05

import Mathlib
import Definitions.Def_LNTopology_Local_Model
import Definitions.Def_LNTopology_Hermetic_Model
import Definitions.Def_LNTopology_RandomHerm_ChannelCost
import Definitions.Def_LNTopology_RandomHerm_Hermetization
import Theorems.Thm_LNTopology_RandomHerm_lemma_B_1

open MeasureTheory

namespace LNRHHelp
open LNTopology.Local LNTopology.Hermetic LNTopology.RandomHerm

lemma c_le {c : ℝ → ℝ} (hc : IsChannelCost c) {x y : ℝ} (hy : 0 ≤ y) (hxy : y ≤ x) :
    c y ≤ c x := by
  rcases hxy.lt_or_eq with h | h
  · exact (hc.mono x y hy h).le
  · rw [h]

lemma c_abs {c : ℝ → ℝ} (hc : IsChannelCost c) (x : ℝ) : c |x| = c x := by
  rcases abs_choice x with h | h <;> rw [h]
  exact hc.symm x

lemma c_pos {c : ℝ → ℝ} (hc : IsChannelCost c) {x : ℝ} (hx : 0 < x) : 0 < c x := by
  have := hc.mono x 0 le_rfl hx
  rwa [hc.zero] at this

lemma c_meas {c : ℝ → ℝ} (hc : IsChannelCost c) : Measurable c := by
  have hmono : Monotone (fun x => c (max x 0)) := fun x y hxy =>
    c_le hc (le_max_right _ _) (max_le_max hxy le_rfl)
  have : c = (fun x => c (max x 0)) ∘ (fun x => |x|) := by
    funext x; simp [max_eq_left (abs_nonneg x), c_abs hc]
  rw [this]; exact hmono.measurable.comp continuous_abs.measurable

end LNRHHelp

open LNTopology.RandomHerm LNRHHelp

theorem solution :
    ∀ a b ε : ℝ, 1 < a → 0 < b → 0 < ε → ∃ k : ℝ, 0 < k ∧
      ∀ (V : Type) [Fintype V] [DecidableEq V] (E : SimpleGraph V) [DecidableRel E.Adj]
        (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (Λ : Ω → V → V → ℝ) (c g : ℝ → ℝ),
        LNTopology.Local.IsChannelCost c → LNTopology.Hermetic.SAPlus c g →
        (∀ ω, LNTopology.Local.IsLN (Λ ω)) →
        (∀ ω i j, Λ ω i j ≠ 0 ↔ E.Adj i j) →
        (∀ i j, Measurable fun ω => Λ ω i j) →
        (∀ i j, E.Adj i j → ∀ x : ℝ, 0 < x →
          P {ω | x < c (Λ ω i j)} < ENNReal.ofReal (b * x ^ (-a))) →
        (∀ i j, E.Adj i j → P {ω | ε < c (Λ ω i j)} = 1) →
        (∃ u v, E.Adj u v) →
        1 - k * ∑ i, (E.degree i : ℝ) * (g (E.degree i)) ^ (-a)
          ≤ (P {ω | IsHermetizableLN c (Λ ω)}).toReal := by
  intro a b ε ha hb hε
  refine ⟨b * (ε / 2) ^ (-a), by positivity, ?_⟩
  intro V _ _ E _ Ω _ P _ Λ c g hc hg hLN hE hmeas htail hfloor hchan
  set U := Finset.univ.filter (fun i => 0 < E.degree i) with hU
  have hgpos : ∀ i, 0 < E.degree i → 0 < g (E.degree i) := by
    intro i hi
    have h0 := hg.2.1 0 le_rfl
    have := hg.1 (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 (Nat.cast_nonneg (E.degree i)))
      (by exact_mod_cast hi : (0:ℝ) < E.degree i)
    linarith
  have hgnn : ∀ i, 0 ≤ g (E.degree i) := fun i => hg.2.1 _ (Nat.cast_nonneg _)
  have hnbrU : ∀ ω i, chanNbrs (Λ ω) U i = E.neighborFinset i := by
    intro ω i; ext j
    simp only [chanNbrs, Finset.mem_filter, SimpleGraph.mem_neighborFinset, hE, hU,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨_, h⟩; exact h
    · intro h; exact ⟨(E.degree_pos_iff_exists_adj j).2 ⟨i, h.symm⟩, h⟩
  have hdegU : ∀ ω i, degOn (Λ ω) U i = E.degree i := by
    intro ω i; simp [degOn, hnbrU, SimpleGraph.card_neighborFinset_eq_degree]
  let F : V → Set Ω := fun i =>
    {ω | g (E.degree i) ≤ 2 * c (maxChanOn (Λ ω) U i) / c (minChanOn (Λ ω) U i)}
  have hcompl : {ω | IsHermetizableLN c (Λ ω)}ᶜ ⊆ ⋃ i ∈ U, F i := by
    intro ω hω
    by_contra hcon
    apply hω
    refine ⟨U, lemma_B_1 c g (Λ ω) U hc hg (hLN ω) ?_ ?_ ?_⟩
    · obtain ⟨u, v, huv⟩ := hchan
      have hu : 0 < E.degree u := (E.degree_pos_iff_exists_adj u).2 ⟨v, huv⟩
      exact ⟨u, by simpa only [hU, Finset.mem_filter, Finset.mem_univ, true_and] using hu⟩
    · intro i hi; rw [hdegU]; simp only [hU, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      exact hi
    · intro i hi
      simp only [Set.mem_iUnion, not_exists] at hcon
      have := hcon i hi
      simp only [F, Set.mem_setOf_eq, not_le] at this
      rw [hdegU]; exact this
  let N : Set Ω := ⋃ i, ⋃ j, {ω | E.Adj i j ∧ c (Λ ω i j) ≤ ε}
  have hN : P N = 0 := by
    apply measure_iUnion_null; intro i; apply measure_iUnion_null; intro j
    by_cases hij : E.Adj i j
    · have hms : MeasurableSet {ω | ε < c (Λ ω i j)} :=
        measurableSet_lt measurable_const ((c_meas hc).comp (hmeas i j))
      have h1 := (prob_compl_eq_zero_iff hms).2 (hfloor i j hij)
      refine measure_mono_null (fun ω hω => ?_) h1
      simp only [Set.mem_setOf_eq, Set.mem_compl_iff, not_lt] at hω ⊢
      exact hω.2
    · simp [hij]
  have hF : ∀ i ∈ U, F i ⊆
      N ∪ ⋃ j ∈ E.neighborFinset i, {ω | ε / 2 * g (E.degree i) < c (Λ ω i j)} := by
    intro i hi ω hω
    by_cases hωN : ω ∈ N
    · exact Or.inl hωN
    right
    have hgood : ∀ j, E.Adj i j → ε < c (Λ ω i j) := by
      intro j hj
      by_contra hle
      push Not at hle
      exact hωN (by simp only [N, Set.mem_iUnion]; exact ⟨i, j, hj, hle⟩)
    have hdpos : 0 < E.degree i := by
      simpa only [hU, Finset.mem_filter, Finset.mem_univ, true_and] using hi
    have hne : (chanNbrs (Λ ω) U i).Nonempty := by
      rw [hnbrU]
      obtain ⟨v, hv⟩ := (E.degree_pos_iff_exists_adj i).1 hdpos
      exact ⟨v, by simpa using hv⟩
    obtain ⟨j0, hj0, h0⟩ := Finset.exists_mem_eq_inf' hne (fun j => |Λ ω i j|)
    obtain ⟨j1, hj1, h1⟩ := Finset.exists_mem_eq_sup' hne (fun j => |Λ ω i j|)
    have hmin : minChanOn (Λ ω) U i = |Λ ω i j0| := by
      simp only [minChanOn, dif_pos hne]; exact h0
    have hmax : maxChanOn (Λ ω) U i = |Λ ω i j1| := by
      simp only [maxChanOn, dif_pos hne]; exact h1
    rw [hnbrU, SimpleGraph.mem_neighborFinset] at hj0 hj1
    have hω' : g (E.degree i) ≤ 2 * c (maxChanOn (Λ ω) U i) / c (minChanOn (Λ ω) U i) := hω
    rw [hmin, hmax, c_abs hc, c_abs hc] at hω'
    have hc0 := hgood j0 hj0
    have hcpos : 0 < c (Λ ω i j0) := hε.trans hc0
    rw [le_div_iff₀ hcpos] at hω'
    have hg0 := hgpos i hdpos
    simp only [Set.mem_iUnion]
    refine ⟨j1, by simpa using hj1, ?_⟩
    show ε / 2 * g _ < c (Λ ω i j1)
    nlinarith
  have hterm_nn : ∀ i, 0 ≤ (E.degree i : ℝ) * (b * (ε / 2 * g (E.degree i)) ^ (-a)) := fun i =>
    mul_nonneg (Nat.cast_nonneg _)
      (mul_nonneg hb.le (Real.rpow_nonneg (mul_nonneg (by positivity) (hgnn i)) _))
  have hPB : P {ω | IsHermetizableLN c (Λ ω)}ᶜ ≤ ENNReal.ofReal
      (∑ i ∈ U, (E.degree i : ℝ) * (b * (ε / 2 * g (E.degree i)) ^ (-a))) := by
    calc P {ω | IsHermetizableLN c (Λ ω)}ᶜ ≤ P (⋃ i ∈ U, F i) := measure_mono hcompl
    _ ≤ ∑ i ∈ U, P (F i) := measure_biUnion_finset_le U F
    _ ≤ ∑ i ∈ U, ENNReal.ofReal
          ((E.degree i : ℝ) * (b * (ε / 2 * g (E.degree i)) ^ (-a))) := by
        apply Finset.sum_le_sum
        intro i hi
        have hdpos : 0 < E.degree i := by
          simpa only [hU, Finset.mem_filter, Finset.mem_univ, true_and] using hi
        have hx : 0 < ε / 2 * g (E.degree i) := mul_pos (by positivity) (hgpos i hdpos)
        calc P (F i) ≤ P (N ∪ ⋃ j ∈ E.neighborFinset i,
              {ω | ε / 2 * g (E.degree i) < c (Λ ω i j)}) := measure_mono (hF i hi)
        _ ≤ P N + P (⋃ j ∈ E.neighborFinset i,
              {ω | ε / 2 * g (E.degree i) < c (Λ ω i j)}) := measure_union_le _ _
        _ = P (⋃ j ∈ E.neighborFinset i,
              {ω | ε / 2 * g (E.degree i) < c (Λ ω i j)}) := by rw [hN, zero_add]
        _ ≤ ∑ j ∈ E.neighborFinset i, P {ω | ε / 2 * g (E.degree i) < c (Λ ω i j)} :=
            measure_biUnion_finset_le _ _
        _ ≤ ∑ j ∈ E.neighborFinset i,
              ENNReal.ofReal (b * (ε / 2 * g (E.degree i)) ^ (-a)) :=
            Finset.sum_le_sum (fun j hj => (htail i j (by simpa using hj) _ hx).le)
        _ = _ := by
            rw [Finset.sum_const, SimpleGraph.card_neighborFinset_eq_degree, nsmul_eq_mul,
              ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    _ = _ := (ENNReal.ofReal_sum_of_nonneg (fun i _ => hterm_nn i)).symm
  have h1 : 1 ≤ (P {ω | IsHermetizableLN c (Λ ω)}).toReal
      + (P {ω | IsHermetizableLN c (Λ ω)}ᶜ).toReal := by
    have hle : (1 : ENNReal) ≤ P {ω | IsHermetizableLN c (Λ ω)}
        + P {ω | IsHermetizableLN c (Λ ω)}ᶜ := by
      rw [← measure_univ (μ := P), ← Set.union_compl_self {ω | IsHermetizableLN c (Λ ω)}]
      exact measure_union_le _ _
    rw [← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
    have := ENNReal.toReal_mono
      (ENNReal.add_ne_top.2 ⟨measure_ne_top _ _, measure_ne_top _ _⟩) hle
    simpa using this
  have h2 : (P {ω | IsHermetizableLN c (Λ ω)}ᶜ).toReal ≤
      ∑ i ∈ U, (E.degree i : ℝ) * (b * (ε / 2 * g (E.degree i)) ^ (-a)) :=
    ENNReal.toReal_le_of_le_ofReal (Finset.sum_nonneg (fun i _ => hterm_nn i)) hPB
  have h3 : ∑ i ∈ U, (E.degree i : ℝ) * (b * (ε / 2 * g (E.degree i)) ^ (-a))
      = b * (ε / 2) ^ (-a) * ∑ i, (E.degree i : ℝ) * (g (E.degree i)) ^ (-a) := by
    rw [Finset.mul_sum, hU, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs with hd
    · rw [Real.mul_rpow (by positivity) (hgnn i)]; ring
    · have : E.degree i = 0 := by omega
      simp [this]
  linarith
