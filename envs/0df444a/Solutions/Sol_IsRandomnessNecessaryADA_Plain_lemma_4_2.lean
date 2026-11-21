-- Prove2me | solution 1 for IsRandomnessNecessaryADA.Plain.lemma_4_2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T16:27:03.639287+00:00
-- url     : https://prove2.me/submissions/22c70aef-ed65-4e47-9244-e0ccf7966435

import Definitions.Def_IsRandomnessNecessaryADA_Plain_Tables

section
set_option autoImplicit false

namespace IsRandomnessNecessaryADA.Plain.Dev.L42

open IsRandomnessNecessaryADA.Plain

open scoped Classical in
theorem card_preimage_le (N M : ℕ) (r : Locations N M) (v : BooleanQuery (Fin N))
    (A : Set (Table N M)) :
    Fintype.card ((completeTable r v ⁻¹' A : Set (Table N M)))
      ≤ 2 ^ N * Fintype.card A := by
  classical
  set c := completeTable r v with hc
  set s : Finset (Table N M) := Finset.univ.filter (fun q => c q ∈ A) with hs
  have h1 : Fintype.card ((c ⁻¹' A : Set (Table N M))) = s.card := by
    rw [Fintype.card_subtype]; rfl
  have h2 : Fintype.card A = A.toFinset.card := by
    rw [Set.toFinset_card]
  have himg : s.image c ⊆ A.toFinset := by
    intro w hw
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hw
    simpa [hs] using hq
  have hfib : ∀ a ∈ s.image c, (s.filter (fun q => c q = a)).card ≤ 2 ^ N := by
    intro a _
    have : (s.filter (fun q => c q = a)).card ≤ (Finset.univ : Finset (Fin N → Bool)).card := by
      refine Finset.card_le_card_of_injOn (fun q => fun i => q (i, r i)) (fun _ _ => Finset.mem_univ _) ?_
      intro q hq q' hq' hqq
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hq hq'
      funext ⟨i, j⟩
      by_cases hj : j = r i
      · subst hj; exact congrFun hqq i
      · have e1 : c q (i, j) = q (i, j) := by simp [hc, completeTable, hj]
        have e2 : c q' (i, j) = q' (i, j) := by simp [hc, completeTable, hj]
        rw [← e1, ← e2, hq.2, hq'.2]
    simpa using this
  rw [h1, h2]
  calc s.card ≤ 2 ^ N * (s.image c).card := Finset.card_le_mul_card_image s _ hfib
    _ ≤ 2 ^ N * A.toFinset.card := Nat.mul_le_mul_left _ (Finset.card_le_card himg)

open scoped Classical in
theorem completion_le (N M : ℕ) (r : Locations N M) (v : BooleanQuery (Fin N))
    (A : Set (Table N M)) :
    (completionLaw r v).toOuterMeasure A ≤ 2 ^ N * (tableLaw N M).toOuterMeasure A := by
  classical
  unfold completionLaw tableLaw
  rw [PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_uniformOfFintype_apply,
    PMF.toOuterMeasure_uniformOfFintype_apply]
  have := card_preimage_le N M r v A
  have h3 : ((Fintype.card ((completeTable r v ⁻¹' A : Set (Table N M))) : ℕ) : ENNReal) ≤
      ((2 ^ N * Fintype.card A : ℕ) : ENNReal) := by exact_mod_cast this
  calc (Fintype.card ((completeTable r v ⁻¹' A : Set (Table N M))) : ENNReal) /
        Fintype.card (Table N M)
      ≤ ((2 ^ N * Fintype.card A : ℕ) : ENNReal) / Fintype.card (Table N M) :=
        ENNReal.div_le_div_right h3 _
    _ = 2 ^ N * (Fintype.card A / Fintype.card (Table N M)) := by
        push_cast; rw [mul_div_assoc]

end IsRandomnessNecessaryADA.Plain.Dev.L42

namespace IsRandomnessNecessaryADA.Plain

theorem chk_lemma_4_2 (N M L : ℕ) (hL : L ≤ N)
    (r : Locations N M) (v : Fin (L + 1) → BooleanQuery (Fin N))
    (joint : PMF ((Fin (L + 1) → Table N M) × Fin (L + 1)))
    (marginals : ∀ j, joint.map (fun w => w.1 j) = completionLaw r (v j))
    (A : Set (Table N M)) :
    probability (joint.map (fun w => w.1 w.2)) A ≤
      (densityFactor N : ℝ) * probability (tableLaw N M) A := by
  classical
  unfold probability
  set T := (tableLaw N M).toOuterMeasure A with hT
  have hTne : T ≠ ⊤ := by
    rw [hT, PMF.toOuterMeasure_apply_fintype]
    exact ENNReal.sum_ne_top.2 (fun x _ =>
      ne_top_of_le_ne_top (PMF.apply_ne_top _ x) (Set.indicator_le_self _ _ x))
  have hE : (joint.map (fun w => w.1 w.2)).toOuterMeasure A ≤
      ((L + 1 : ℕ) : ENNReal) * (2 ^ N * T) := by
    rw [PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_apply_fintype]
    have step : ∀ w : (Fin (L + 1) → Table N M) × Fin (L + 1),
        ((fun w => w.1 w.2) ⁻¹' A).indicator joint w ≤
          ∑ j : Fin (L + 1), {w : (Fin (L + 1) → Table N M) × Fin (L + 1) | w.1 j ∈ A}.indicator joint w := by
      intro w
      by_cases hw : w ∈ (fun w : (Fin (L + 1) → Table N M) × Fin (L + 1) => w.1 w.2) ⁻¹' A
      · rw [Set.indicator_of_mem hw]
        refine le_trans ?_ (Finset.single_le_sum (f := fun j : Fin (L + 1) =>
          {w : (Fin (L + 1) → Table N M) × Fin (L + 1) | w.1 j ∈ A}.indicator joint w)
          (fun _ _ => zero_le) (Finset.mem_univ w.2))
        exact (Set.indicator_of_mem (show w ∈ {w' : (Fin (L + 1) → Table N M) × Fin (L + 1) | w'.1 w.2 ∈ A} from hw) joint).ge
      · rw [Set.indicator_of_notMem hw]; exact zero_le
    refine (Finset.sum_le_sum (fun w _ => step w)).trans ?_
    rw [Finset.sum_comm]
    have hj : ∀ j : Fin (L + 1),
        ∑ w, {w : (Fin (L + 1) → Table N M) × Fin (L + 1) | w.1 j ∈ A}.indicator joint w ≤
          2 ^ N * T := by
      intro j
      rw [← PMF.toOuterMeasure_apply_fintype]
      have : joint.toOuterMeasure {w | w.1 j ∈ A} =
          (completionLaw r (v j)).toOuterMeasure A := by
        rw [← marginals j, PMF.toOuterMeasure_map_apply]; rfl
      rw [this]
      exact Dev.L42.completion_le N M r (v j) A
    calc ∑ j : Fin (L + 1), ∑ w, {w : (Fin (L + 1) → Table N M) × Fin (L + 1) | w.1 j ∈ A}.indicator joint w
        ≤ ∑ j : Fin (L + 1), (2 ^ N * T) := Finset.sum_le_sum (fun j _ => hj j)
      _ = ((L + 1 : ℕ) : ENNReal) * (2 ^ N * T) := by simp
  have hne : ((L + 1 : ℕ) : ENNReal) * (2 ^ N * T) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
      (ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofNat_ne_top) hTne)
  refine (ENNReal.toReal_mono hne hE).trans ?_
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_pow]
  have hdf : (densityFactor N : ℝ) = (N + 1) * 2 ^ N := by
    simp [densityFactor]
  rw [hdf]
  simp only [ENNReal.toReal_natCast, ENNReal.toReal_ofNat]
  have hT0 : 0 ≤ T.toReal := ENNReal.toReal_nonneg
  have hLN : ((L + 1 : ℕ) : ℝ) ≤ (N : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ hL
  have : (0 : ℝ) ≤ 2 ^ N * T.toReal := by positivity
  nlinarith

end IsRandomnessNecessaryADA.Plain
end

theorem solution : type_of% @IsRandomnessNecessaryADA.Plain.chk_lemma_4_2 := @IsRandomnessNecessaryADA.Plain.chk_lemma_4_2
