-- Prove2me | solution 1 for KalaiVempala.Additive.theorem_1_1_a
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-21T18:26:58.404566+00:00
-- url     : https://prove2.me/submissions/b68d0116-efd2-4a60-b9e2-e8235bc8c1a1

import Mathlib
import Definitions.Def_OracleRO_ApproxFPL_FPL
import Definitions.Def_KalaiVempala_Additive_Setting

set_option autoImplicit false

open MeasureTheory OracleRO.ApproxFPL

namespace KV1250

lemma one_sub_sum_le_prod {ι : Type*} (s : Finset ι) (a : ι → ℝ)
    (h0 : ∀ i ∈ s, 0 ≤ a i) (h1 : ∀ i ∈ s, a i ≤ 1) :
    1 - ∑ i ∈ s, a i ≤ ∏ i ∈ s, (1 - a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.prod_insert hj]
    have ih' := ih (fun i hi => h0 i (Finset.mem_insert_of_mem hi))
      (fun i hi => h1 i (Finset.mem_insert_of_mem hi))
    have hs0 : 0 ≤ ∑ i ∈ s, a i :=
      Finset.sum_nonneg (fun i hi => h0 i (Finset.mem_insert_of_mem hi))
    have ha0 := h0 j (Finset.mem_insert_self j s)
    have ha1 := h1 j (Finset.mem_insert_self j s)
    nlinarith [mul_le_mul_of_nonneg_left ih' (sub_nonneg.mpr ha1), mul_nonneg ha0 hs0]

lemma perturb_integral {n : ℕ} (ε : ℝ) (f : (Fin n → ℝ) → ℝ) :
    ∫ p, f p ∂(perturbLaw n ε) =
      (volume (Set.Icc (0 : Fin n → ℝ) (fun _ => ε⁻¹))).toReal⁻¹ *
        ∫ p in Set.Icc (0 : Fin n → ℝ) (fun _ => ε⁻¹), f p := by
  unfold perturbLaw ProbabilityTheory.cond
  rw [integral_smul_measure, ENNReal.toReal_inv, smul_eq_mul]

lemma setIntegral_shift {n : ℕ} (L : ℝ) (f : (Fin n → ℝ) → ℝ) (w : Fin n → ℝ) :
    ∫ p in Set.Icc (0 : Fin n → ℝ) (fun _ => L), f (w + p) =
      ∫ q in Set.Icc w (w + fun _ => L), f q := by
  rw [← integral_indicator measurableSet_Icc, ← integral_indicator measurableSet_Icc]
  rw [← integral_add_left_eq_self (μ := volume)
    (fun q => Set.indicator (Set.Icc w (w + fun _ => L)) f q) w]
  congr 1
  funext p
  have hiff : (w + p ∈ Set.Icc w (w + fun _ => L)) ↔
      p ∈ Set.Icc (0 : Fin n → ℝ) (fun _ => L) := by
    simp only [Set.mem_Icc, le_add_iff_nonneg_right, add_le_add_iff_left]
  by_cases hp : p ∈ Set.Icc (0 : Fin n → ℝ) (fun _ => L)
  · rw [Set.indicator_of_mem hp, Set.indicator_of_mem (hiff.mpr hp)]
  · rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem (fun h => hp (hiff.mp h))]

lemma prob_perturb {n : ℕ} (ε : ℝ) (hε : 0 < ε) : IsProbabilityMeasure (perturbLaw n ε) := by
  have hLpos : 0 < ε⁻¹ := inv_pos.mpr hε
  have hv : (volume (Set.Icc (0 : Fin n → ℝ) (fun _ => ε⁻¹))).toReal ≠ 0 := by
    rw [Real.volume_Icc_pi_toReal (a := (0 : Fin n → ℝ)) (b := fun _ => ε⁻¹)
      (fun i => by simp [hLpos.le])]
    simp only [Pi.zero_apply, sub_zero]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => hLpos.ne')
  have h2 := ENNReal.toReal_ne_zero.mp hv
  unfold perturbLaw
  exact ProbabilityTheory.cond_isProbabilityMeasure_of_finite h2.1 h2.2

lemma abs_integral_le {n : ℕ} (ε : ℝ) (hε : 0 < ε) (f : (Fin n → ℝ) → ℝ) (R : ℝ)
    (hR : ∀ q, |f q| ≤ R) : |∫ p, f p ∂(perturbLaw n ε)| ≤ R := by
  have := prob_perturb (n := n) ε hε
  have := norm_integral_le_of_norm_le_const (μ := perturbLaw n ε) (f := f)
    (Filter.Eventually.of_forall fun q => (by simpa [Real.norm_eq_abs] using hR q))
  simpa [Real.norm_eq_abs] using this

lemma tv_bound {n : ℕ} (ε : ℝ) (hε : 0 < ε) (h : (Fin n → ℝ) → ℝ) (hm : Measurable h)
    (R : ℝ) (hR : ∀ q, |h q| ≤ R) (w : Fin n → ℝ) :
    ∫ p, h p ∂(perturbLaw n ε) - ∫ p, h (w + p) ∂(perturbLaw n ε) ≤
      2 * R * (ε * ∑ i, |w i|) := by
  have hLpos : 0 < ε⁻¹ := inv_pos.mpr hε
  have hR0 : 0 ≤ R := (abs_nonneg _).trans (hR 0)
  by_cases hsmall : ∀ i, |w i| ≤ ε⁻¹
  · set L := ε⁻¹ with hL
    set C : Set (Fin n → ℝ) := Set.Icc 0 (fun _ => L) with hC
    set C' : Set (Fin n → ℝ) := Set.Icc w (w + fun _ => L) with hC'
    have hCvol : (volume C).toReal = L ^ n := by
      rw [hC, Real.volume_Icc_pi_toReal (a := (0 : Fin n → ℝ)) (b := fun _ => L)
        (fun i => by simp [hLpos.le])]
      simp
    have hC'vol : volume.real C' = L ^ n := by
      rw [measureReal_def, hC', Real.volume_Icc_pi_toReal (fun i => by simp [hLpos.le])]
      simp
    have hIvol : volume.real (C ∩ C') = ∏ i, (L - |w i|) := by
      rw [measureReal_def, hC, hC', Set.Icc_inter_Icc]
      have hle : ((0 : Fin n → ℝ) ⊔ w) ≤ ((fun _ => L) ⊓ (w + fun _ => L)) := by
        intro i
        simp only [Pi.sup_apply, Pi.inf_apply, Pi.zero_apply, Pi.add_apply]
        have := hsmall i
        rcases le_total 0 (w i) with hw | hw
        · rw [abs_of_nonneg hw] at this
          rw [max_eq_right hw, min_eq_left (by linarith)]; exact this
        · rw [abs_of_nonpos hw] at this
          rw [max_eq_left hw, min_eq_right (by linarith)]; linarith
      rw [Real.volume_Icc_pi_toReal hle]
      refine Finset.prod_congr rfl (fun i _ => ?_)
      simp only [Pi.sup_apply, Pi.inf_apply, Pi.zero_apply, Pi.add_apply]
      rcases le_total 0 (w i) with hw | hw
      · rw [abs_of_nonneg hw, max_eq_right hw, min_eq_left (by linarith)]
      · rw [abs_of_nonpos hw, max_eq_left hw, min_eq_right (by linarith)]; ring
    have hCfin : volume C < ⊤ := isCompact_Icc.measure_lt_top
    have hC'fin : volume C' < ⊤ := isCompact_Icc.measure_lt_top
    have hbd : ∀ᵐ x ∂(volume : Measure (Fin n → ℝ)), ‖h x‖ ≤ R :=
      Filter.Eventually.of_forall fun q => (by simpa [Real.norm_eq_abs] using hR q)
    have hintC : IntegrableOn h C volume :=
      IntegrableOn.of_bound hCfin hm.aestronglyMeasurable R (ae_restrict_of_ae hbd)
    have hintC' : IntegrableOn h C' volume :=
      IntegrableOn.of_bound hC'fin hm.aestronglyMeasurable R (ae_restrict_of_ae hbd)
    have e1 := integral_inter_add_sdiff (measurableSet_Icc : MeasurableSet C') hintC
    have e2 := integral_inter_add_sdiff (measurableSet_Icc : MeasurableSet C) hintC'
    rw [Set.inter_comm] at e2
    have m1 := measureReal_inter_add_sdiff (μ := volume) (s := C) (t := C')
      measurableSet_Icc hCfin.ne
    have m2 := measureReal_inter_add_sdiff (μ := volume) (s := C') (t := C)
      measurableSet_Icc hC'fin.ne
    rw [Set.inter_comm] at m2
    have hCreal : volume.real C = L ^ n := by rw [measureReal_def]; exact hCvol
    have b1 : |∫ x in C \ C', h x| ≤ R * volume.real (C \ C') := by
      have := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := C \ C') (f := h)
        ((measure_mono Set.sdiff_subset).trans_lt hCfin)
        (fun x _ => by simpa [Real.norm_eq_abs] using hR x)
      simpa [Real.norm_eq_abs] using this
    have b2 : |∫ x in C' \ C, h x| ≤ R * volume.real (C' \ C) := by
      have := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := C' \ C) (f := h)
        ((measure_mono Set.sdiff_subset).trans_lt hC'fin)
        (fun x _ => by simpa [Real.norm_eq_abs] using hR x)
      simpa [Real.norm_eq_abs] using this
    have hD : (∫ x in C, h x) - (∫ x in C', h x) ≤
        2 * R * (L ^ n - ∏ i, (L - |w i|)) := by
      have a1 := le_abs_self (∫ x in C \ C', h x)
      have a2 := neg_abs_le (∫ x in C' \ C, h x)
      rw [hIvol, hCreal] at m1
      rw [hIvol, hC'vol] at m2
      have r1 : volume.real (C \ C') = L ^ n - ∏ i, (L - |w i|) := by linarith
      have r2 : volume.real (C' \ C) = L ^ n - ∏ i, (L - |w i|) := by linarith
      rw [r1] at b1; rw [r2] at b2
      linarith
    have hprod : ∏ i, (L - |w i|) = L ^ n * ∏ i, (1 - ε * |w i|) := by
      have : ∀ i, L - |w i| = L * (1 - ε * |w i|) := by
        intro i
        rw [hL, mul_sub, mul_one, ← mul_assoc, inv_mul_cancel₀ hε.ne', one_mul]
      simp_rw [this]
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have hW := one_sub_sum_le_prod Finset.univ (fun i => ε * |w i|)
      (fun i _ => mul_nonneg hε.le (abs_nonneg _))
      (fun i _ => by
        have := mul_le_mul_of_nonneg_left (hsmall i) hε.le
        rwa [mul_inv_cancel₀ hε.ne'] at this)
    rw [perturb_integral, perturb_integral]
    have hshift := setIntegral_shift L h w
    rw [← hL, hshift, ← hC, ← hC', hCvol]
    have hLn : 0 < L ^ n := pow_pos hLpos n
    rw [← mul_sub]
    rw [hprod] at hD
    have hsum : ε * ∑ i, |w i| = ∑ i, ε * |w i| := Finset.mul_sum _ _ _
    rw [hsum]
    calc (L ^ n)⁻¹ * ((∫ x in C, h x) - ∫ x in C', h x)
        ≤ (L ^ n)⁻¹ * (2 * R * (L ^ n - L ^ n * ∏ i, (1 - ε * |w i|))) :=
          mul_le_mul_of_nonneg_left hD (inv_nonneg.mpr hLn.le)
      _ = 2 * R * (1 - ∏ i, (1 - ε * |w i|)) := by
          field_simp
      _ ≤ 2 * R * ∑ i, ε * |w i| := by
          apply mul_le_mul_of_nonneg_left _ (by linarith)
          linarith
  · push Not at hsmall
    obtain ⟨i, hi⟩ := hsmall
    have h1 := abs_integral_le ε hε h R hR
    have h2 := abs_integral_le ε hε (fun p => h (w + p)) R (fun q => hR _)
    have hsum : 1 ≤ ε * ∑ j, |w j| := by
      have hle : |w i| ≤ ∑ j, |w j| :=
        Finset.single_le_sum (f := fun j => |w j|) (fun j _ => abs_nonneg (w j))
          (Finset.mem_univ i)
      have : 1 < ε * |w i| := by
        calc (1 : ℝ) = ε * ε⁻¹ := (mul_inv_cancel₀ hε.ne').symm
          _ < ε * |w i| := mul_lt_mul_of_pos_left hi hε
      nlinarith
    have a1 := le_abs_self (∫ p, h p ∂(perturbLaw n ε))
    have a2 := neg_abs_le (∫ p, h (w + p) ∂(perturbLaw n ε))
    nlinarith


lemma meas_dot {n : ℕ} (v : Fin n → ℝ) : Measurable (fun x : Fin n → ℝ => v ⬝ᵥ x) := by
  unfold dotProduct
  exact Finset.measurable_sum _ (fun i _ => measurable_const.mul (measurable_pi_apply i))

lemma integrable_shift {n : ℕ} (ε : ℝ) (hε : 0 < ε) (h : (Fin n → ℝ) → ℝ) (hm : Measurable h)
    (R : ℝ) (hR : ∀ q, |h q| ≤ R) (w : Fin n → ℝ) :
    Integrable (fun p => h (w + p)) (perturbLaw n ε) := by
  have := prob_perturb (n := n) ε hε
  exact Integrable.of_bound (hm.comp (measurable_const_add w)).aestronglyMeasurable R
    (Filter.Eventually.of_forall fun q => by simpa [Real.norm_eq_abs] using hR (w + q))

lemma step {n : ℕ} {Dset : Set (Fin n → ℝ)} {M : (Fin n → ℝ) → (Fin n → ℝ)}
    (hM : KalaiVempala.Additive.IsArgminOracle Dset M) (z u : Fin n → ℝ) :
    M (z + u) ⬝ᵥ u ≤ M (z + u) ⬝ᵥ (z + u) - M z ⬝ᵥ z := by
  have h1 := (hM z).2 (M (z + u)) (hM (z + u)).1
  rw [dotProduct_add]
  linarith

lemma per_round {n : ℕ} {Dset : Set (Fin n → ℝ)} {M : (Fin n → ℝ) → (Fin n → ℝ)}
    (hM : KalaiVempala.Additive.IsArgminOracle Dset M) (Y v p : Fin n → ℝ) (k : ℕ)
    (hk : 0 < k) :
    ∑ j ∈ Finset.range k, (1 / (k : ℝ)) * (v ⬝ᵥ M (Y + ((((j : ℝ) + 1) / k) • v + p))) ≤
      M ((Y + v) + p) ⬝ᵥ ((Y + v) + p) - M (Y + p) ⬝ᵥ (Y + p) := by
  set g : ℕ → ℝ := fun j =>
    M (Y + (((j : ℝ) / k) • v + p)) ⬝ᵥ (Y + (((j : ℝ) / k) • v + p)) with hg
  have hk' : (k : ℝ) ≠ 0 := by positivity
  have hterm : ∀ j : ℕ, (1 / (k : ℝ)) * (v ⬝ᵥ M (Y + ((((j : ℝ) + 1) / k) • v + p))) ≤
      g (j + 1) - g j := by
    intro j
    have hz : Y + ((((j : ℝ) + 1) / k) • v + p) =
        (Y + (((j : ℝ) / k) • v + p)) + (1 / (k : ℝ)) • v := by
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    have := step hM (Y + (((j : ℝ) / k) • v + p)) ((1 / (k : ℝ)) • v)
    rw [← hz, dotProduct_smul, smul_eq_mul] at this
    simp only [hg]
    push_cast
    rw [dotProduct_comm v]
    linarith
  have htel : ∀ m, ∑ j ∈ Finset.range m, (g (j + 1) - g j) = g m - g 0 := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [Finset.sum_range_succ, ih]; ring
  calc _ ≤ ∑ j ∈ Finset.range k, (g (j + 1) - g j) := Finset.sum_le_sum (fun j _ => hterm j)
    _ = g k - g 0 := htel k
    _ = _ := by
      simp only [hg]
      have e1 : Y + (((k : ℝ) / k) • v + p) = (Y + v) + p := by
        rw [div_self hk', one_smul, add_assoc]
      have e0 : Y + ((((0 : ℕ) : ℝ) / k) • v + p) = Y + p := by simp
      rw [e1, e0]

lemma tele_Icc (ψ : ℕ → ℝ) (T : ℕ) :
    ∑ t ∈ Finset.Icc 1 T, (ψ t - ψ (t - 1)) = ψ T - ψ 0 := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    simp only [Nat.add_sub_cancel]
    ring

lemma prefixSum_zero' {n : ℕ} (s : ℕ → Fin n → ℝ) : prefixSum s 0 = 0 := by
  simp [prefixSum]

lemma prefixSum_step {n : ℕ} (s : ℕ → Fin n → ℝ) (t : ℕ) (ht : 1 ≤ t) :
    prefixSum s (t - 1) + s t = prefixSum s t := by
  obtain ⟨m, rfl⟩ : ∃ m, t = m + 1 := ⟨t - 1, by omega⟩
  simp only [prefixSum, Nat.add_sub_cancel]
  rw [Finset.sum_Icc_succ_top (by omega)]

lemma sum_range_succ_cast (k : ℕ) :
    ∑ j ∈ Finset.range k, ((j : ℝ) + 1) = k * (k + 1) / 2 := by
  induction k with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

end KV1250

open MeasureTheory OracleRO.ApproxFPL KalaiVempala.Additive in
theorem solution {n : ℕ} (Dset S : Set (Fin n → ℝ))
    (M : (Fin n → ℝ) → (Fin n → ℝ)) (hM : IsArgminOracle Dset M) (hMmeas : Measurable M)
    (Ddiam R A : ℝ) (hD : ∀ d ∈ Dset, ∀ d' ∈ Dset, ∑ i, |d i - d' i| ≤ Ddiam)
    (hR : ∀ d ∈ Dset, ∀ x ∈ S, |d ⬝ᵥ x| ≤ R) (hA : ∀ x ∈ S, ∑ i, |x i| ≤ A)
    (s : ℕ → Fin n → ℝ) (T : ℕ) (hs : ∀ t ∈ Finset.Icc 1 T, s t ∈ S)
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    fplExpectedReward M s ε T ≤
      M (prefixSum s T) ⬝ᵥ prefixSum s T + ε * R * A * T + Ddiam / ε := by
  classical
  set B := M (prefixSum s T) ⬝ᵥ prefixSum s T + Ddiam / ε with hB
  have hprob := KV1250.prob_perturb (n := n) ε hε0
  let h : ℕ → (Fin n → ℝ) → ℝ := fun t q => s t ⬝ᵥ M (prefixSum s (t - 1) + q)
  have hhm : ∀ t, Measurable (h t) := fun t =>
    (KV1250.meas_dot (s t)).comp (hMmeas.comp (measurable_const_add _))
  have hhR : ∀ t ∈ Finset.Icc 1 T, ∀ q, |h t q| ≤ R := by
    intro t ht q
    have := hR _ (hM (prefixSum s (t - 1) + q)).1 (s t) (hs t ht)
    simpa [h, dotProduct_comm] using this
  have key : ∀ k : ℕ, 0 < k →
      fplExpectedReward M s ε T ≤ B + T * (ε * R * A * (1 + 1 / k)) := by
    intro k hk
    have hk' : (0 : ℝ) < k := by exact_mod_cast hk
    let G : (Fin n → ℝ) → ℝ := fun p => ∑ t ∈ Finset.Icc 1 T, ∑ j ∈ Finset.range k,
        (1 / (k : ℝ)) * h t ((((j : ℝ) + 1) / k) • s t + p)
    have hGle : ∀ p ∈ Set.Icc (0 : Fin n → ℝ) (fun _ => ε⁻¹), G p ≤ B := by
      intro p hp
      have h1 : G p ≤ ∑ t ∈ Finset.Icc 1 T,
          (M (prefixSum s t + p) ⬝ᵥ (prefixSum s t + p) -
            M (prefixSum s (t - 1) + p) ⬝ᵥ (prefixSum s (t - 1) + p)) := by
        apply Finset.sum_le_sum
        intro t ht
        have := KV1250.per_round hM (prefixSum s (t - 1)) (s t) p k hk
        rw [KV1250.prefixSum_step s t (Finset.mem_Icc.mp ht).1] at this
        exact this
      have htel := KV1250.tele_Icc (fun t => M (prefixSum s t + p) ⬝ᵥ (prefixSum s t + p)) T
      rw [htel, KV1250.prefixSum_zero', zero_add] at h1
      have h2 : M (prefixSum s T + p) ⬝ᵥ (prefixSum s T + p) ≤
          M (prefixSum s T) ⬝ᵥ (prefixSum s T + p) := (hM _).2 _ (hM _).1
      have h3 : (M (prefixSum s T) - M p) ⬝ᵥ p ≤ Ddiam / ε := by
        have hd := hD _ (hM (prefixSum s T)).1 _ (hM p).1
        rw [div_eq_mul_inv]
        calc (M (prefixSum s T) - M p) ⬝ᵥ p = ∑ i, (M (prefixSum s T) i - M p i) * p i := rfl
          _ ≤ ∑ i, |M (prefixSum s T) i - M p i| * ε⁻¹ := by
            apply Finset.sum_le_sum
            intro i _
            have hp0 : 0 ≤ p i := hp.1 i
            have hp1 : p i ≤ ε⁻¹ := hp.2 i
            calc (M (prefixSum s T) i - M p i) * p i ≤ |M (prefixSum s T) i - M p i| * p i :=
                  mul_le_mul_of_nonneg_right (le_abs_self _) hp0
              _ ≤ _ := mul_le_mul_of_nonneg_left hp1 (abs_nonneg _)
          _ = (∑ i, |M (prefixSum s T) i - M p i|) * ε⁻¹ := by rw [Finset.sum_mul]
          _ ≤ Ddiam * ε⁻¹ := mul_le_mul_of_nonneg_right hd (inv_nonneg.mpr hε0.le)
      rw [dotProduct_add (M (prefixSum s T))] at h2
      rw [sub_dotProduct] at h3
      simp only [hB]
      linarith
    have hint : ∀ t ∈ Finset.Icc 1 T, ∀ j ∈ Finset.range k,
        Integrable (fun p => (1 / (k : ℝ)) * h t ((((j : ℝ) + 1) / k) • s t + p))
          (perturbLaw n ε) := fun t ht j _ =>
      (KV1250.integrable_shift ε hε0 (h t) (hhm t) R (hhR t ht) _).const_mul _
    have hGi : Integrable G (perturbLaw n ε) :=
      integrable_finsetSum _ (fun t ht => integrable_finsetSum _ (fun j hj => hint t ht j hj))
    have hae : ∀ᵐ p ∂(perturbLaw n ε), p ∈ Set.Icc (0 : Fin n → ℝ) (fun _ => ε⁻¹) :=
      ProbabilityTheory.ae_cond_mem measurableSet_Icc
    have hGint : ∫ p, G p ∂(perturbLaw n ε) ≤ B := by
      calc ∫ p, G p ∂(perturbLaw n ε) ≤ ∫ _p, B ∂(perturbLaw n ε) :=
            integral_mono_ae hGi (integrable_const B)
              (by filter_upwards [hae] with p hp using hGle p hp)
        _ = B := by simp
    have hGeq : ∫ p, G p ∂(perturbLaw n ε) = ∑ t ∈ Finset.Icc 1 T, ∑ j ∈ Finset.range k,
        (1 / (k : ℝ)) * ∫ p, h t ((((j : ℝ) + 1) / k) • s t + p) ∂(perturbLaw n ε) := by
      rw [integral_finsetSum _ (fun t ht => integrable_finsetSum _ (fun j hj => hint t ht j hj))]
      refine Finset.sum_congr rfl (fun t ht => ?_)
      rw [integral_finsetSum _ (fun j hj => hint t ht j hj)]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [integral_const_mul]
    have hper : ∀ t ∈ Finset.Icc 1 T, ∫ p, h t p ∂(perturbLaw n ε) ≤
        ∑ j ∈ Finset.range k, (1 / (k : ℝ)) *
          ∫ p, h t ((((j : ℝ) + 1) / k) • s t + p) ∂(perturbLaw n ε)
          + ε * R * A * (1 + 1 / k) := by
      intro t ht
      have hst := hs t ht
      have hR0 : 0 ≤ R := le_trans (abs_nonneg _) (hhR t ht 0)
      have hk1 : 0 ≤ 1 / (k : ℝ) := by positivity
      have hb : ∀ j ∈ Finset.range k, (1 / (k : ℝ)) * ∫ p, h t p ∂(perturbLaw n ε) ≤
          (1 / (k : ℝ)) * ∫ p, h t ((((j : ℝ) + 1) / k) • s t + p) ∂(perturbLaw n ε)
            + (1 / (k : ℝ)) * (2 * R * (ε * ((((j : ℝ) + 1) / k) * A))) := by
        intro j _
        have tv := KV1250.tv_bound ε hε0 (h t) (hhm t) R (hhR t ht)
          ((((j : ℝ) + 1) / k) • s t)
        have hc : 0 ≤ ((j : ℝ) + 1) / k := by positivity
        have hw : ∑ i, |(((((j : ℝ) + 1) / k) • s t) i)| ≤ ((j : ℝ) + 1) / k * A := by
          simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_nonneg hc]
          rw [← Finset.mul_sum]
          exact mul_le_mul_of_nonneg_left (hA _ hst) hc
        have hw2 : 2 * R * (ε * ∑ i, |(((((j : ℝ) + 1) / k) • s t) i)|) ≤
            2 * R * (ε * ((((j : ℝ) + 1) / k) * A)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hw hε0.le) (by linarith)
        rw [← mul_add]
        apply mul_le_mul_of_nonneg_left _ hk1
        linarith
      have hsum := Finset.sum_le_sum hb
      rw [Finset.sum_add_distrib] at hsum
      have e1 : ∑ j ∈ Finset.range k, (1 / (k : ℝ)) * ∫ p, h t p ∂(perturbLaw n ε) =
          ∫ p, h t p ∂(perturbLaw n ε) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        field_simp
      have e2 : ∑ j ∈ Finset.range k, (1 / (k : ℝ)) * (2 * R * (ε * ((((j : ℝ) + 1) / k) * A)))
          = ε * R * A * (1 + 1 / k) := by
        have hj : ∀ j ∈ Finset.range k,
            (1 / (k : ℝ)) * (2 * R * (ε * ((((j : ℝ) + 1) / k) * A))) =
              (2 * R * ε * A / (k : ℝ) ^ 2) * ((j : ℝ) + 1) := by
          intro j _
          field_simp
        rw [Finset.sum_congr rfl hj, ← Finset.mul_sum, KV1250.sum_range_succ_cast]
        field_simp
      rw [e1, e2] at hsum
      exact hsum
    unfold fplExpectedReward
    calc ∑ t ∈ Finset.Icc 1 T, ∫ p, s t ⬝ᵥ M (prefixSum s (t - 1) + p) ∂(perturbLaw n ε)
        ≤ ∑ t ∈ Finset.Icc 1 T, (∑ j ∈ Finset.range k, (1 / (k : ℝ)) *
            ∫ p, h t ((((j : ℝ) + 1) / k) • s t + p) ∂(perturbLaw n ε)
            + ε * R * A * (1 + 1 / k)) := Finset.sum_le_sum (fun t ht => hper t ht)
      _ = ∫ p, G p ∂(perturbLaw n ε) + T * (ε * R * A * (1 + 1 / k)) := by
          rw [Finset.sum_add_distrib, hGeq, Finset.sum_const, Nat.card_Icc]
          simp
      _ ≤ B + T * (ε * R * A * (1 + 1 / k)) := by linarith [hGint]
  by_contra hcon
  push Not at hcon
  set c := ε * R * A * T with hc
  set δ := fplExpectedReward M s ε T - (B + c) with hδdef
  have hδ : 0 < δ := by simp only [hδdef, hB]; linarith
  obtain ⟨k, hk⟩ := exists_nat_gt (|c| / δ)
  have hk' : (0 : ℝ) < k := lt_of_le_of_lt (div_nonneg (abs_nonneg _) hδ.le) hk
  have hkpos : 0 < k := by exact_mod_cast hk'
  have hkey := key k hkpos
  have e : (T : ℝ) * (ε * R * A * (1 + 1 / k)) = c + c / k := by
    simp only [hc]
    field_simp
  rw [e] at hkey
  have h1 : c / k ≤ |c| / k := div_le_div_of_nonneg_right (le_abs_self c) hk'.le
  have h2 : |c| / k < δ := by
    rw [div_lt_iff₀ hk']
    rw [div_lt_iff₀ hδ] at hk
    linarith
  have : fplExpectedReward M s ε T = δ + (B + c) := by simp only [hδdef]; ring
  linarith
