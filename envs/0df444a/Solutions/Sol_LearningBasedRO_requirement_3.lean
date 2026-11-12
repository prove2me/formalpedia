-- Prove2me | solution 1 for LearningBasedRO.requirement_3
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-12T02:21:38.536195+00:00
-- url     : https://prove2.me/submissions/1da9156c-fb5a-4839-82ae-540a4f8abbd0

import Definitions.Def_LearningBasedRO_Model
import Theorems.Thm_LearningBasedRO_display_5

open MeasureTheory
open scoped ENNReal

namespace LearningBasedRO

private lemma orderStat_lt_iff_exists_finset' {n : ℕ} (y : Fin n → ℝ) (c : ℝ) (r : ℕ)
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

private lemma measurable_orderStat' (n r : ℕ) :
    Measurable (fun y : Fin n → ℝ => orderStat y r) := by
  by_cases hr : 1 ≤ r ∧ r ≤ n
  · refine measurable_of_Iio fun c => ?_
    have hset :
        (fun y : Fin n → ℝ => orderStat y r) ⁻¹' Set.Iio c =
          ⋃ S ∈ (Finset.univ.filter (fun S : Finset (Fin n) => r ≤ S.card)),
            ⋂ j ∈ S, {y : Fin n → ℝ | y j < c} := by
      ext y
      simp [orderStat_lt_iff_exists_finset' y c r hr.1 hr.2]
    rw [hset]
    refine Finset.measurableSet_biUnion _ fun S _ => ?_
    refine Finset.measurableSet_biInter _ fun j _ => ?_
    exact measurableSet_Iio.preimage (measurable_pi_apply j)
  · have hzero : (fun y : Fin n → ℝ => orderStat y r) = fun _ => 0 := by
      ext y
      exact dif_neg hr
    rw [hzero]
    exact measurable_const

end LearningBasedRO

open LearningBasedRO in
theorem solution {E : Type*} [MeasurableSpace E] (P : Measure E) [IsProbabilityMeasure P]
    (n₁ n₂ : ℕ) (ϵ δ : ℝ) (hϵ0 : 0 < ϵ) (hϵ1 : ϵ < 1) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hn₂ : Real.log δ / Real.log (1 - ϵ) ≤ (n₂ : ℝ)) (t : (Fin n₁ → E) → E → ℝ)
    (ht : Measurable (Function.uncurry t)) (hcont : ∀ d₁, NullSingletonClass (P.map (t d₁))) :
    MeasurableSet {D : (Fin n₁ → E) × (Fin n₂ → E) | IsContentSet P ϵ (uncertaintySet t ϵ δ D)} ∧
      ENNReal.ofReal (1 - δ) ≤
        ∫⁻ d₁, (Measure.pi fun _ : Fin n₂ => P)
            {d₂ | IsContentSet P ϵ (uncertaintySet t ϵ δ (d₁, d₂))}
          ∂(Measure.pi fun _ : Fin n₁ => P) ∧
      splitLaw P n₁ n₂ {D | IsContentSet P ϵ (uncertaintySet t ϵ δ D)} =
        ∫⁻ d₁, (Measure.pi fun _ : Fin n₂ => P)
            {d₂ | IsContentSet P ϵ (uncertaintySet t ϵ δ (d₁, d₂))}
          ∂(Measure.pi fun _ : Fin n₁ => P) ∧
      SatisfiesReq3 (splitLaw P n₁ n₂) P ϵ δ (uncertaintySet t ϵ δ) := by
  let ΩD := (Fin n₁ → E) × (Fin n₂ → E)
  let W : Set (ΩD × E) :=
    {p | t p.1.1 p.2 ≤ orderStat (fun j => t p.1.1 (p.1.2 j)) (iStar n₂ ϵ δ)}
  have hW : MeasurableSet W := by
    have h1 : Measurable (fun p : ΩD × E => t p.1.1 p.2) :=
      ht.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
    have hvec : Measurable (fun (p : ΩD × E) (j : Fin n₂) => t p.1.1 (p.1.2 j)) :=
      measurable_pi_lambda _ fun j =>
        ht.comp ((measurable_fst.comp measurable_fst).prodMk
          ((measurable_pi_apply j).comp (measurable_snd.comp measurable_fst)))
    have h2 : Measurable (fun p : ΩD × E =>
        orderStat (fun j => t p.1.1 (p.1.2 j)) (iStar n₂ ϵ δ)) :=
      (measurable_orderStat' n₂ (iStar n₂ ϵ δ)).comp hvec
    exact measurableSet_le h1 h2
  have hmeas_content : Measurable (fun D : ΩD => P (uncertaintySet t ϵ δ D)) := by
    have hlin : Measurable (fun D : ΩD => ∫⁻ ξ, W.indicator 1 (D, ξ) ∂P) :=
      (measurable_const.indicator hW).lintegral_prod_right'
    have heq : (fun D : ΩD => ∫⁻ ξ, W.indicator 1 (D, ξ) ∂P) =
        fun D : ΩD => P (uncertaintySet t ϵ δ D) := by
      ext D
      have hsec : (fun ξ => W.indicator (1 : ΩD × E → ℝ≥0∞) (D, ξ)) =
          (uncertaintySet t ϵ δ D).indicator 1 := by
        ext ξ
        by_cases hξ : ξ ∈ uncertaintySet t ϵ δ D
        · have hp : (D, ξ) ∈ W := hξ
          simp [hξ, hp]
        · have hp : (D, ξ) ∉ W := hξ
          simp [hξ, hp]
      rw [hsec]
      exact lintegral_indicator_one (hW.preimage measurable_prodMk_left)
    rwa [heq] at hlin
  have hE3 : MeasurableSet {D : ΩD | IsContentSet P ϵ (uncertaintySet t ϵ δ D)} :=
    measurableSet_Ici.preimage hmeas_content
  have hbound :
      ENNReal.ofReal (1 - δ) ≤
        ∫⁻ d₁, (Measure.pi fun _ : Fin n₂ => P)
            {d₂ | IsContentSet P ϵ (uncertaintySet t ϵ δ (d₁, d₂))}
          ∂(Measure.pi fun _ : Fin n₁ => P) := by
    have hpt : ∀ d₁ : Fin n₁ → E,
        ENNReal.ofReal (1 - δ) ≤
          (Measure.pi fun _ : Fin n₂ => P)
            {d₂ | IsContentSet P ϵ (uncertaintySet t ϵ δ (d₁, d₂))} := by
      intro d₁
      have htd₁ : Measurable (t d₁) := ht.comp measurable_prodMk_left
      exact (display_5 P n₁ n₂ ϵ δ hϵ0 hϵ1 hδ0 hδ1 hn₂ t d₁ htd₁ (hcont d₁)).2
    calc
      ENNReal.ofReal (1 - δ)
        = ∫⁻ _d₁, ENNReal.ofReal (1 - δ) ∂(Measure.pi fun _ : Fin n₁ => P) := by
          rw [lintegral_const, measure_univ, mul_one]
      _ ≤ ∫⁻ d₁, (Measure.pi fun _ : Fin n₂ => P)
            {d₂ | IsContentSet P ϵ (uncertaintySet t ϵ δ (d₁, d₂))}
          ∂(Measure.pi fun _ : Fin n₁ => P) := lintegral_mono hpt
  have hprod :
      splitLaw P n₁ n₂ {D | IsContentSet P ϵ (uncertaintySet t ϵ δ D)} =
        ∫⁻ d₁, (Measure.pi fun _ : Fin n₂ => P)
            {d₂ | IsContentSet P ϵ (uncertaintySet t ϵ δ (d₁, d₂))}
          ∂(Measure.pi fun _ : Fin n₁ => P) :=
    Measure.prod_apply hE3
  have hreq : SatisfiesReq3 (splitLaw P n₁ n₂) P ϵ δ (uncertaintySet t ϵ δ) := by
    unfold SatisfiesReq3
    exact hbound.trans_eq hprod.symm
  exact ⟨hE3, hbound, hprod, hreq⟩
