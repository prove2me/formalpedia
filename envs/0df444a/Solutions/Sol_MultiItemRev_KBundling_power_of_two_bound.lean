-- Prove2me | solution 1 for MultiItemRev.KBundling.power_of_two_bound
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T15:19:25.763641+00:00
-- url     : https://prove2.me/submissions/0ad23fe6-72d3-42ad-ac52-8b5596be219c

import Mathlib
import Definitions.Def_MultiItemRev_Decomp_Model
import Theorems.Thm_MultiItemRev_KBundling_theorem_7
import Theorems.Thm_MultiItemRev_KBundling_proposition_14_ii

open MeasureTheory
open scoped NNReal ENNReal

namespace KBPow2Aux
open MultiItemRev.Decomp

lemma meas_sum {ι : Type*} [Fintype ι] : Measurable (fun x : ι → ℝ≥0 => ∑ i, x i) := by
  fun_prop

/-- Relabeling the goods does not increase the optimal revenue. -/
lemma rev_map_reindex_le {ι ι' : Type*} [Fintype ι] [Fintype ι'] (e : ι ≃ ι')
    (μ : Measure (ι → ℝ≥0)) :
    Rev (μ.map (MeasurableEquiv.piCongrLeft (fun _ : ι' => ℝ≥0) e)) ≤ Rev μ := by
  unfold Rev
  refine iSup₂_le fun M' hM' => ?_
  set g := MeasurableEquiv.piCongrLeft (fun _ : ι' => ℝ≥0) e with hg
  let M : Mechanism ι := ⟨fun x i => M'.q (g x) (e i), fun x => M'.s (g x)⟩
  have hsum : ∀ (x' x : ι → ℝ≥0),
      ∑ i, M.q x' i * (x i : ℝ) = ∑ i', M'.q (g x') i' * (g x i' : ℝ) := by
    intro x' x
    exact Fintype.sum_equiv e _ _ (fun i => by
      simp [M, g, MeasurableEquiv.piCongrLeft_apply_apply])
  obtain ⟨hF, hIC, hIR, hm⟩ := hM'
  have hM : IsAdmissible M := by
    refine ⟨fun x i => hF (g x) (e i), fun x x' => ?_, fun x => ?_, hm.comp g.measurable⟩
    · have := hIC (g x) (g x')
      unfold buyerPayoff at *
      rw [hsum, hsum]
      exact this
    · have := hIR (g x)
      unfold buyerPayoff at *
      rw [hsum]
      exact this
  have hrev : expRevenue (μ.map g) M' = expRevenue μ M := by
    unfold expRevenue
    rw [lintegral_map (f := fun x => ENNReal.ofReal (M'.s x))
        (ENNReal.measurable_ofReal.comp hm) g.measurable,
      lintegral_map (f := fun x => ENNReal.ofReal (-M'.s x))
        (ENNReal.measurable_ofReal.comp hm.neg) g.measurable]
  rw [hrev]
  exact le_iSup₂ (f := fun (M : Mechanism ι) (_ : IsAdmissible M) =>
    (expRevenue μ M).toENNReal) M hM

/-- The law of `X₁+⋯+X_{n+n'}` is the convolution of the laws of the two block sums. -/
lemma map_sum_pi_add (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ] (n n' : ℕ) :
    (Measure.pi (fun _ : Fin (n + n') => ρ)).map (fun x => ∑ i, x i) =
      (((Measure.pi (fun _ : Fin n => ρ)).map (fun x => ∑ i, x i)).prod
        ((Measure.pi (fun _ : Fin n' => ρ)).map (fun x => ∑ i, x i))).map
          (fun p => p.1 + p.2) := by
  have h1 := (measurePreserving_piCongrLeft (fun _ : Fin (n + n') => ρ)
    (finSumFinEquiv (m := n) (n := n'))).map_eq
  have h2 := (measurePreserving_sumPiEquivProdPi_symm
    (X := fun _ : Fin n ⊕ Fin n' => ℝ≥0) (fun _ => ρ)).map_eq
  rw [← h1, ← h2, Measure.map_map (MeasurableEquiv.measurable _) (MeasurableEquiv.measurable _),
    Measure.map_map meas_sum (by fun_prop), Measure.map_prod_map _ _ meas_sum meas_sum,
    Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext p
  simp only [Function.comp_apply, Prod.map_fst, Prod.map_snd]
  rw [← Fintype.sum_equiv (finSumFinEquiv (m := n) (n := n'))
    (fun i => (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin n ⊕ Fin n' => ℝ≥0)).symm p i)]
  · rw [Fintype.sum_sum_type]
    rfl
  · intro i
    simp [MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_apply_apply]

lemma map_sum_pi_one (ρ : Measure ℝ≥0) :
    (Measure.pi (fun _ : Fin 1 => ρ)).map (fun x => ∑ i, x i) = ρ := by
  have : (fun x : Fin 1 → ℝ≥0 => ∑ i, x i) = MeasurableEquiv.funUnique (Fin 1) ℝ≥0 := by
    funext x
    simp [MeasurableEquiv.funUnique]
  rw [this]
  exact (measurePreserving_funUnique ρ (Fin 1)).map_eq

lemma rev_pi_one_le (ν : Measure ℝ≥0) :
    Rev (Measure.pi (fun _ : Fin 1 => ν)) ≤ Rev1 ν := by
  have hpi : Measure.pi (fun _ : Fin 1 => ν) =
      (oneGood ν).map (MeasurableEquiv.piCongrLeft (fun _ : Fin 1 => ℝ≥0)
        (Equiv.ofUnique Unit (Fin 1))) := by
    rw [oneGood, Measure.map_map (MeasurableEquiv.measurable _) (by fun_prop)]
    have h := (measurePreserving_funUnique ν (Fin 1)).symm.map_eq
    refine h.symm.trans ?_
    congr 1
    funext t i
    have hi : i = (Equiv.ofUnique Unit (Fin 1)) () := Subsingleton.elim _ _
    rw [Function.comp_apply, hi, MeasurableEquiv.piCongrLeft_apply_apply]
    rfl
  rw [hpi]
  exact rev_map_reindex_le _ _

lemma srev_pi (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ] (a : ℕ) :
    SRev (Measure.pi (fun _ : Fin a => ρ)) = (a : ℝ≥0∞) * Rev1 ρ := by
  unfold SRev
  have h : ∀ i : Fin a, (Measure.pi (fun _ : Fin a => ρ)).map (fun x => x i) = ρ := by
    intro i
    have := Measure.pi_map_eval (μ := fun _ : Fin a => ρ) i
    simp only [measure_univ, Finset.prod_const_one, one_smul] at this
    exact this
  simp only [h, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

lemma map_sum_pi_blocks (ν : Measure ℝ≥0) [IsProbabilityMeasure ν] (n a : ℕ) :
    (Measure.pi (fun _ : Fin a => (Measure.pi (fun _ : Fin n => ν)).map
      (fun x => ∑ i, x i))).map (fun x => ∑ i, x i) =
      (Measure.pi (fun _ : Fin (a * n) => ν)).map (fun x => ∑ i, x i) := by
  have : IsProbabilityMeasure ((Measure.pi (fun _ : Fin n => ν)).map (fun x => ∑ i, x i)) :=
    Measure.isProbabilityMeasure_map meas_sum.aemeasurable
  induction a with
  | zero =>
    rw [Nat.zero_mul, Measure.pi_of_empty, Measure.pi_of_empty]
  | succ a ih =>
    rw [map_sum_pi_add, ih, map_sum_pi_one, Nat.succ_mul, map_sum_pi_add]

/-- `a · B_n ≤ 4 B_{a n}` (Proposition 14 (ii) applied to `a` i.i.d. copies of `X₁+⋯+X_n`). -/
lemma key (ν : Measure ℝ≥0) [IsProbabilityMeasure ν] (n a : ℕ) (ha : 1 ≤ a) :
    (a : ℝ≥0∞) * BRev (Measure.pi (fun _ : Fin n => ν)) ≤
      4 * BRev (Measure.pi (fun _ : Fin (a * n) => ν)) := by
  set ν' := (Measure.pi (fun _ : Fin n => ν)).map (fun x => ∑ i, x i) with hν'
  have : IsProbabilityMeasure ν' := Measure.isProbabilityMeasure_map meas_sum.aemeasurable
  have h := MultiItemRev.KBundling.proposition_14_ii a ha ν'
  rw [srev_pi] at h
  have hB : BRev (Measure.pi (fun _ : Fin a => ν')) =
      BRev (Measure.pi (fun _ : Fin (a * n) => ν)) := by
    unfold BRev
    rw [hν', map_sum_pi_blocks]
  rw [hB] at h
  have hBn : BRev (Measure.pi (fun _ : Fin n => ν)) = Rev1 ν' := rfl
  rw [hBn]
  calc (a : ℝ≥0∞) * Rev1 ν' = 4 * (ENNReal.ofReal (1 / 4) * ((a : ℝ≥0∞) * Rev1 ν')) := by
        rw [← mul_assoc, show (4 : ℝ≥0∞) * ENNReal.ofReal (1 / 4) = 1 by
          rw [show (4 : ℝ≥0∞) = ENNReal.ofReal 4 by norm_num, ← ENNReal.ofReal_mul (by norm_num)]
          norm_num, one_mul]
    _ ≤ _ := by gcongr

lemma step (ν : Measure ℝ≥0) [IsProbabilityMeasure ν] (n : ℕ) [Nonempty (Fin n)] :
    Rev (Measure.pi (fun _ : Fin (n + n) => ν)) ≤
      2 * Rev (Measure.pi (fun _ : Fin n => ν)) + 2 * BRev (Measure.pi (fun _ : Fin n => ν)) := by
  have h1 := (measurePreserving_piCongrLeft (fun _ : Fin (n + n) => ν)
    (finSumFinEquiv (m := n) (n := n))).map_eq
  have h2 := (measurePreserving_sumPiEquivProdPi_symm
    (X := fun _ : Fin n ⊕ Fin n => ℝ≥0) (fun _ => ν)).map_eq
  have hJ : jointLaw (Measure.pi (fun _ : Fin n => ν)) (Measure.pi (fun _ : Fin n => ν)) =
      Measure.pi (fun _ : Fin n ⊕ Fin n => ν) := h2
  have h7 := (MultiItemRev.KBundling.theorem_7 (Measure.pi (fun _ : Fin n => ν))
    (Measure.pi (fun _ : Fin n => ν))).1
  rw [hJ] at h7
  rw [← h1]
  calc _ ≤ Rev (Measure.pi (fun _ : Fin n ⊕ Fin n => ν)) := rev_map_reindex_le _ _
    _ ≤ _ := h7
    _ = _ := by ring

end KBPow2Aux

open KBPow2Aux in
theorem solution (m : ℕ) (hm : 1 ≤ m)
    (ν : Measure ℝ≥0) [IsProbabilityMeasure ν] :
    MultiItemRev.Decomp.Rev (Measure.pi (fun _ : Fin (2 ^ m) => ν)) ≤
      ENNReal.ofReal (4 * (Real.logb 2 ((2 ^ m : ℕ) : ℝ) + 1)) *
        MultiItemRev.Decomp.BRev (Measure.pi (fun _ : Fin (2 ^ m) => ν)) := by
  set R : ℕ → ℝ≥0∞ := fun i => MultiItemRev.Decomp.Rev (Measure.pi (fun _ : Fin (2 ^ i) => ν))
    with hR
  set B : ℕ → ℝ≥0∞ := fun i => MultiItemRev.Decomp.BRev (Measure.pi (fun _ : Fin (2 ^ i) => ν))
    with hB
  have hrec : ∀ i, R (i + 1) ≤ 2 * R i + 2 * B i := by
    intro i
    have : Nonempty (Fin (2 ^ i)) := ⟨⟨0, by positivity⟩⟩
    simp only [hR, hB]
    rw [show 2 ^ (i + 1) = 2 ^ i + 2 ^ i by ring]
    exact step ν (2 ^ i)
  -- unrolled recursion
  have hunroll : ∀ j, R j ≤ 2 ^ j * B 0 +
      ∑ i ∈ Finset.range j, 2 ^ (j - i) * B i := by
    intro j
    induction j with
    | zero =>
      simp only [pow_zero, one_mul, Finset.range_zero, Finset.sum_empty, add_zero, hR, hB]
      calc _ ≤ MultiItemRev.Decomp.Rev1 ν := rev_pi_one_le ν
        _ = _ := congrArg MultiItemRev.Decomp.Rev1 (map_sum_pi_one ν).symm
    | succ j ih =>
      calc R (j + 1) ≤ 2 * R j + 2 * B j := hrec j
        _ ≤ 2 * (2 ^ j * B 0 + ∑ i ∈ Finset.range j, 2 ^ (j - i) * B i) + 2 * B j := by
          gcongr
        _ = 2 ^ (j + 1) * B 0 + ∑ i ∈ Finset.range (j + 1), 2 ^ (j + 1 - i) * B i := by
          have : ∀ i ∈ Finset.range j, 2 * (2 ^ (j - i) * B i) = 2 ^ (j + 1 - i) * B i := by
            intro i hi
            rw [Finset.mem_range] at hi
            rw [← mul_assoc, ← pow_succ', show j - i + 1 = j + 1 - i by omega]
          rw [Finset.sum_range_succ, mul_add, Finset.mul_sum, Finset.sum_congr rfl this,
            show j + 1 - j = 1 by omega, pow_one, pow_succ]
          ring
  -- each term is at most 4 B m
  have hterm : ∀ i ≤ m, 2 ^ (m - i) * B i ≤ 4 * B m := by
    intro i hi
    have := key ν (2 ^ i) (2 ^ (m - i)) (Nat.one_le_two_pow)
    rw [← pow_add, Nat.sub_add_cancel hi] at this
    simpa [hB] using this
  have hlogb : Real.logb 2 ((2 ^ m : ℕ) : ℝ) = (m : ℝ) := by
    push_cast
    rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one]
  rw [hlogb]
  calc R m ≤ 2 ^ m * B 0 + ∑ i ∈ Finset.range m, 2 ^ (m - i) * B i := hunroll m
    _ ≤ 4 * B m + ∑ i ∈ Finset.range m, 4 * B m := by
        refine add_le_add (by simpa using hterm 0 (Nat.zero_le _))
          (Finset.sum_le_sum fun i hi => hterm i (Finset.mem_range.mp hi).le)
    _ = ((m : ℝ≥0∞) + 1) * (4 * B m) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
    _ = ENNReal.ofReal (4 * ((m : ℝ) + 1)) * B m := by
        rw [ENNReal.ofReal_mul (by norm_num), ← mul_assoc, mul_comm _ (4 : ℝ≥0∞)]
        congr 2
        · norm_num
        · rw [ENNReal.ofReal_add (by positivity) (by norm_num)]; simp
