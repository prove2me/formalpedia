-- Prove2me | solution 1 for LearningBasedRO.display_5
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-12T02:20:01.839004+00:00
-- url     : https://prove2.me/submissions/6d03f2c9-8ff2-4d30-b488-d626a11bb14c

import Definitions.Def_LearningBasedRO_Model
import Theorems.Thm_LearningBasedRO_lemma_3
import Theorems.Thm_LearningBasedRO_iStar_valid_iff

open MeasureTheory Filter
open scoped ENNReal

namespace LearningBasedRO

private lemma orderStat_lt_iff_exists_finset {n : ℕ} (y : Fin n → ℝ) (c : ℝ) (r : ℕ)
    (hr1 : 1 ≤ r) (hrn : r ≤ n) :
    orderStat y r < c ↔ ∃ S : Finset (Fin n), r ≤ S.card ∧ ∀ j ∈ S, y j < c := by
  have hr : 1 ≤ r ∧ r ≤ n := ⟨hr1, hrn⟩
  let idx : Fin n := ⟨r - 1, by omega⟩
  let σ : Equiv.Perm (Fin n) := Tuple.sort y
  have hos : orderStat y r = y (σ idx) := dif_pos hr
  rw [hos]
  have hmono : Monotone (y ∘ σ) := Tuple.monotone_sort y
  constructor
  · intro hlt
    refine ⟨Finset.map σ.toEmbedding (Finset.Iic idx), ?_, ?_⟩
    · rw [Finset.card_map, Fin.card_Iic]
      change r ≤ (r - 1) + 1
      omega
    · intro j hj
      rcases Finset.mem_map.mp hj with ⟨m, hm, rfl⟩
      rw [Finset.mem_Iic] at hm
      exact lt_of_le_of_lt (hmono hm) hlt
  · rintro ⟨S, hcardS, hS⟩
    by_contra hnot
    have hge : c ≤ y (σ idx) := le_of_not_gt hnot
    have hsub : Finset.map σ.symm.toEmbedding S ⊆ Finset.Iio idx := by
      intro m hm
      rcases Finset.mem_map.mp hm with ⟨j, hj, rfl⟩
      rw [Finset.mem_Iio]
      by_contra hle_not
      have hle : idx ≤ σ.symm j := le_of_not_gt hle_not
      have hval : y (σ idx) ≤ y (σ (σ.symm j)) := hmono hle
      rw [σ.apply_symm_apply] at hval
      linarith [hS j hj]
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_map, Fin.card_Iio] at hcard
    change S.card ≤ r - 1 at hcard
    omega

private lemma measurable_orderStat_aux (n r : ℕ) :
    Measurable (fun y : Fin n → ℝ => orderStat y r) := by
  by_cases hr : 1 ≤ r ∧ r ≤ n
  · refine measurable_of_Iio fun c => ?_
    have hset :
        (fun y : Fin n → ℝ => orderStat y r) ⁻¹' Set.Iio c =
          ⋃ S ∈ (Finset.univ.filter (fun S : Finset (Fin n) => r ≤ S.card)),
            ⋂ j ∈ S, {y : Fin n → ℝ | y j < c} := by
      ext y
      simp [orderStat_lt_iff_exists_finset y c r hr.1 hr.2]
    rw [hset]
    refine Finset.measurableSet_biUnion _ fun S _ => ?_
    refine Finset.measurableSet_biInter _ fun j _ => ?_
    exact measurableSet_Iio.preimage (measurable_pi_apply j)
  · have hzero : (fun y : Fin n → ℝ => orderStat y r) = fun _ => 0 := by
      ext y
      exact dif_neg hr
    rw [hzero]
    exact measurable_const

private lemma quantile_properties (μ : Measure ℝ) [IsProbabilityMeasure μ] [NullSingletonClass μ]
    (ϵ : ℝ) (hϵ0 : 0 < ϵ) (hϵ1 : ϵ < 1) :
    let S := {y : ℝ | ENNReal.ofReal (1 - ϵ) ≤ μ (Set.Iic y)}
    S.Nonempty ∧ BddBelow S ∧ μ (Set.Iic (sInf S)) = ENNReal.ofReal (1 - ϵ) := by
  intro S
  have hp_pos : 0 < ENNReal.ofReal (1 - ϵ) := ENNReal.ofReal_pos.mpr (by linarith)
  have hp_lt_one : ENNReal.ofReal (1 - ϵ) < 1 := by
    rw [← ENNReal.ofReal_one]
    exact (ENNReal.ofReal_lt_ofReal_iff zero_lt_one).mpr (by linarith)
  have hS_ne : S.Nonempty := by
    have hmono : Monotone (fun m : ℕ => Set.Iic (m : ℝ)) := fun a b hab =>
      Set.Iic_subset_Iic.mpr (Nat.cast_le.mpr hab)
    have hiUnion : (⋃ m : ℕ, Set.Iic (m : ℝ)) = Set.univ := by
      ext x
      simp [exists_nat_ge]
    have htend := tendsto_measure_iUnion_atTop (μ := μ) hmono
    rw [hiUnion, measure_univ] at htend
    have hev : ∀ᶠ m : ℕ in atTop, ENNReal.ofReal (1 - ϵ) < μ (Set.Iic (m : ℝ)) :=
      htend.eventually (Ioi_mem_nhds hp_lt_one)
    rcases hev.exists with ⟨m, hm⟩
    exact ⟨(m : ℝ), le_of_lt hm⟩
  have hS_bdd : BddBelow S := by
    have hanti : Antitone (fun m : ℕ => Set.Iic (-(m : ℝ))) := fun a b hab =>
      Set.Iic_subset_Iic.mpr (neg_le_neg (Nat.cast_le.mpr hab))
    have hiInter : (⋂ m : ℕ, Set.Iic (-(m : ℝ))) = ∅ := by
      ext x
      simp only [Set.mem_iInter, Set.mem_Iic, Set.mem_empty_iff_false, iff_false, not_forall,
        not_le]
      rcases exists_nat_gt (-x) with ⟨m, hm⟩
      exact ⟨m, by linarith⟩
    have htend := tendsto_measure_iInter_atTop (μ := μ)
      (fun _ => measurableSet_Iic.nullMeasurableSet) hanti ⟨0, measure_ne_top μ _⟩
    rw [hiInter, measure_empty] at htend
    have hev : ∀ᶠ m : ℕ in atTop, μ (Set.Iic (-(m : ℝ))) < ENNReal.ofReal (1 - ϵ) :=
      htend.eventually (Iio_mem_nhds hp_pos)
    rcases hev.exists with ⟨m, hm⟩
    refine ⟨-(m : ℝ), fun y hy => ?_⟩
    by_contra hlt
    have hle : μ (Set.Iic y) ≤ μ (Set.Iic (-(m : ℝ))) :=
      measure_mono (Set.Iic_subset_Iic.mpr (le_of_lt (lt_of_not_ge hlt)))
    exact not_lt_of_ge (le_trans hy hle) hm
  refine ⟨hS_ne, hS_bdd, le_antisymm ?_ ?_⟩
  · let q := sInf S
    have hmono : Monotone (fun m : ℕ => Set.Iic (q - 1 / ((m : ℝ) + 1))) := by
      intro a b hab
      refine Set.Iic_subset_Iic.mpr ?_
      have hdiv : 1 / ((b : ℝ) + 1) ≤ 1 / ((a : ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hab 1)
      linarith
    have hiUnion : (⋃ m : ℕ, Set.Iic (q - 1 / ((m : ℝ) + 1))) = Set.Iio q := by
      ext x
      simp only [Set.mem_iUnion, Set.mem_Iic, Set.mem_Iio]
      constructor
      · rintro ⟨m, hm⟩
        have hpos : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
        linarith
      · intro hxq
        have ht0 : Tendsto (fun m : ℕ => q - 1 / ((m : ℝ) + 1)) atTop (nhds q) := by
          simpa using tendsto_const_nhds.sub (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
        rcases (ht0.eventually (Ioi_mem_nhds hxq)).exists with ⟨m, hm⟩
        exact ⟨m, le_of_lt hm⟩
    have htend := tendsto_measure_iUnion_atTop (μ := μ) hmono
    rw [hiUnion] at htend
    have hle_m : ∀ m : ℕ, μ (Set.Iic (q - 1 / ((m : ℝ) + 1))) ≤ ENNReal.ofReal (1 - ϵ) := by
      intro m
      by_contra hnot
      have hmem : q - 1 / ((m : ℝ) + 1) ∈ S := le_of_lt (lt_of_not_ge hnot)
      have hcs : q ≤ q - 1 / ((m : ℝ) + 1) := csInf_le hS_bdd hmem
      have hpos : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
      linarith
    have hIio_le : μ (Set.Iio q) ≤ ENNReal.ofReal (1 - ϵ) :=
      le_of_tendsto' htend hle_m
    have hIic_eq : Set.Iic q = Set.Iio q ∪ {q} := by
      ext x
      simp [le_iff_lt_or_eq]
    rw [show sInf S = q from rfl, hIic_eq,
      measure_union (by simp) (measurableSet_singleton q), measure_singleton, add_zero]
    exact hIio_le
  · let q := sInf S
    have hanti : Antitone (fun m : ℕ => Set.Iic (q + 1 / ((m : ℝ) + 1))) := by
      intro a b hab
      refine Set.Iic_subset_Iic.mpr ?_
      have hdiv : 1 / ((b : ℝ) + 1) ≤ 1 / ((a : ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hab 1)
      linarith
    have hiInter : (⋂ m : ℕ, Set.Iic (q + 1 / ((m : ℝ) + 1))) = Set.Iic q := by
      ext x
      simp only [Set.mem_iInter, Set.mem_Iic]
      constructor
      · intro hx
        have ht0 : Tendsto (fun m : ℕ => q + 1 / ((m : ℝ) + 1)) atTop (nhds q) := by
          simpa using tendsto_const_nhds.add (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
        exact ge_of_tendsto' ht0 hx
      · intro hxq m
        have hpos : (0 : ℝ) ≤ 1 / ((m : ℝ) + 1) := by positivity
        linarith
    have htend := tendsto_measure_iInter_atTop (μ := μ)
      (fun _ => measurableSet_Iic.nullMeasurableSet) hanti ⟨0, measure_ne_top μ _⟩
    rw [hiInter] at htend
    have hge_m : ∀ m : ℕ, ENNReal.ofReal (1 - ϵ) ≤ μ (Set.Iic (q + 1 / ((m : ℝ) + 1))) := by
      intro m
      have hlt : q < q + 1 / ((m : ℝ) + 1) := by
        have hpos : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
        linarith
      rcases exists_lt_of_csInf_lt hS_ne hlt with ⟨y, hyS, hy_lt⟩
      exact le_trans hyS (measure_mono (Set.Iic_subset_Iic.mpr (le_of_lt hy_lt)))
    exact ge_of_tendsto' htend hge_m

end LearningBasedRO

open LearningBasedRO in
theorem solution {E : Type*} [MeasurableSpace E] (P : Measure E) [IsProbabilityMeasure P]
    (n₁ n₂ : ℕ) (ϵ δ : ℝ) (hϵ0 : 0 < ϵ) (hϵ1 : ϵ < 1) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hn₂ : Real.log δ / Real.log (1 - ϵ) ≤ (n₂ : ℝ)) (t : (Fin n₁ → E) → E → ℝ)
    (d₁ : Fin n₁ → E) (ht : Measurable (t d₁)) (hcont : NullSingletonClass (P.map (t d₁))) :
    {d₂ : Fin n₂ → E | IsContentSet P ϵ (uncertaintySet t ϵ δ (d₁, d₂))} =
        {d₂ : Fin n₂ → E |
          sInf {y : ℝ | ENNReal.ofReal (1 - ϵ) ≤ (P.map (t d₁)) (Set.Iic y)} ≤
            orderStat (fun i => t d₁ (d₂ i)) (iStar n₂ ϵ δ)} ∧
      ENNReal.ofReal (1 - δ) ≤
        (Measure.pi fun _ : Fin n₂ => P)
          {d₂ | IsContentSet P ϵ (uncertaintySet t ϵ δ (d₁, d₂))} := by
  let μY : Measure ℝ := P.map (t d₁)
  have hprobY : IsProbabilityMeasure μY := Measure.isProbabilityMeasure_map ht.aemeasurable
  have hnullY : NullSingletonClass μY := hcont
  obtain ⟨_hS_ne, hS_bdd, hq_meas⟩ := quantile_properties μY ϵ hϵ0 hϵ1
  let q : ℝ := sInf {y : ℝ | ENNReal.ofReal (1 - ϵ) ≤ μY (Set.Iic y)}
  have hset :
      {d₂ : Fin n₂ → E | IsContentSet P ϵ (uncertaintySet t ϵ δ (d₁, d₂))} =
        {d₂ : Fin n₂ → E | q ≤ orderStat (fun i => t d₁ (d₂ i)) (iStar n₂ ϵ δ)} := by
    ext d₂
    let s := orderStat (fun i => t d₁ (d₂ i)) (iStar n₂ ϵ δ)
    have hmap_U : P (uncertaintySet t ϵ δ (d₁, d₂)) = μY (Set.Iic s) := by
      change P ((t d₁) ⁻¹' Set.Iic s) = (P.map (t d₁)) (Set.Iic s)
      exact (Measure.map_apply ht measurableSet_Iic).symm
    simp only [Set.mem_ofPred, IsContentSet, hmap_U]
    constructor
    · intro hs
      exact csInf_le hS_bdd hs
    · intro hqs
      calc
        ENNReal.ofReal (1 - ϵ) = μY (Set.Iic q) := hq_meas.symm
        _ ≤ μY (Set.Iic s) := measure_mono (Set.Iic_subset_Iic.mpr hqs)
  refine ⟨hset, ?_⟩
  rw [hset]
  let Φ : (Fin n₂ → E) → (Fin n₂ → ℝ) := fun d₂ i => t d₁ (d₂ i)
  have hΦ : Measurable Φ := measurable_pi_lambda _ fun i => ht.comp (measurable_pi_apply i)
  have hmap_pi : (Measure.pi fun _ : Fin n₂ => P).map Φ = Measure.pi fun _ : Fin n₂ => μY := by
    symm
    refine Measure.pi_eq fun s hs => ?_
    rw [Measure.map_apply hΦ (MeasurableSet.univ_pi hs)]
    have hpre : Φ ⁻¹' Set.univ.pi s = Set.univ.pi (fun i => (t d₁) ⁻¹' s i) := by
      ext d₂
      simp [Φ]
    rw [hpre, Measure.pi_pi]
    exact Finset.prod_congr rfl fun i _ => (Measure.map_apply ht (hs i)).symm
  let B : Set (Fin n₂ → ℝ) := {y | q ≤ orderStat y (iStar n₂ ϵ δ)}
  have hB_meas : MeasurableSet B :=
    measurableSet_le measurable_const (measurable_orderStat_aux n₂ (iStar n₂ ϵ δ))
  have hpreB : {d₂ : Fin n₂ → E | q ≤ orderStat (fun i => t d₁ (d₂ i)) (iStar n₂ ϵ δ)} = Φ ⁻¹' B :=
    rfl
  rw [hpreB, ← Measure.map_apply hΦ hB_meas, hmap_pi]
  have hvalid := iStar_valid_iff n₂ ϵ δ hϵ0 hϵ1 hδ0 hδ1
  have hne : (iStarSet n₂ ϵ δ).Nonempty := hvalid.1.mpr (hvalid.2.mpr hn₂)
  exact (lemma_3 μY n₂ ϵ δ hϵ0 hϵ1 hδ0 hδ1 q hq_meas).1 hne
