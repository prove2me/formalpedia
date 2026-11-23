-- Prove2me | solution 1 for L1Sparsifiers.Main.lemma_8
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:28:24.367536+00:00
-- url     : https://prove2.me/submissions/eb58ba62-eb5d-4c16-8db5-a1da7de4420f

import Definitions.Def_L1Sparsifiers_Main_UniformCube

open MeasureTheory L1Sparsifiers.Main

namespace AuxLemma8

lemma nonneg_of_deriv_nonneg (f f' : ℝ → ℝ) (hf0 : f 0 = 0)
    (hderiv : ∀ x : ℝ, HasDerivAt f (f' x) x) (hnn : ∀ x : ℝ, 0 ≤ x → 0 ≤ f' x)
    {s : ℝ} (hs : 0 ≤ s) : 0 ≤ f s := by
  have hmono : MonotoneOn f (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · exact fun x _ => (hderiv x).continuousAt.continuousWithinAt
    · exact fun x _ => (hderiv x).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      rw [(hderiv x).deriv]
      exact hnn x (Set.mem_Ioi.mp hx).le
  rw [← hf0]
  exact hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hs) hs

lemma sinh_le_mul_exp_sq_div_six {s : ℝ} (hs : 0 ≤ s) :
    Real.sinh s ≤ s * Real.exp (s ^ 2 / 6) := by
  let ψ2 : ℝ → ℝ := fun x => (1 - Real.cosh x + x * Real.sinh x) / 3
  have hψ2_deriv : ∀ x : ℝ, HasDerivAt ψ2 (x / 3 * Real.cosh x) x := by
    intro x
    have h1 : HasDerivAt (fun t => 1 - Real.cosh t + t * Real.sinh t)
        (0 - Real.sinh x + (1 * Real.sinh x + x * Real.cosh x)) x :=
      ((hasDerivAt_const x (1 : ℝ)).sub (Real.hasDerivAt_cosh x)).add
        ((hasDerivAt_id x).mul (Real.hasDerivAt_sinh x))
    have h2 := h1.div_const 3
    have heq : (0 - Real.sinh x + (1 * Real.sinh x + x * Real.cosh x)) / 3 =
        x / 3 * Real.cosh x := by ring
    rwa [heq] at h2
  have hψ2_nn : ∀ x : ℝ, 0 ≤ x → 0 ≤ ψ2 x := fun x hx =>
    nonneg_of_deriv_nonneg ψ2 _ (by simp [ψ2]) hψ2_deriv
      (fun y hy => mul_nonneg (by linarith) (Real.cosh_pos y).le) hx
  let ψ1 : ℝ → ℝ := fun x => x / 3 - 2 / 3 * Real.sinh x + x / 3 * Real.cosh x
  have hψ1_deriv : ∀ x : ℝ, HasDerivAt ψ1 (ψ2 x) x := by
    intro x
    have h1 : HasDerivAt ψ1
        (1 / 3 - 2 / 3 * Real.cosh x + (1 / 3 * Real.cosh x + x / 3 * Real.sinh x)) x :=
      (((hasDerivAt_id x).div_const 3).sub ((Real.hasDerivAt_sinh x).const_mul (2 / 3))).add
        (((hasDerivAt_id x).div_const 3).mul (Real.hasDerivAt_cosh x))
    have heq : 1 / 3 - 2 / 3 * Real.cosh x + (1 / 3 * Real.cosh x + x / 3 * Real.sinh x) =
        ψ2 x := by simp only [ψ2]; ring
    rwa [heq] at h1
  have hψ1_nn : ∀ x : ℝ, 0 ≤ x → 0 ≤ ψ1 x := fun x hx =>
    nonneg_of_deriv_nonneg ψ1 _ (by simp [ψ1]) hψ1_deriv hψ2_nn hx
  let ψ : ℝ → ℝ := fun x => 1 + x ^ 2 / 6 - Real.cosh x + x / 3 * Real.sinh x
  have hψ_deriv : ∀ x : ℝ, HasDerivAt ψ (ψ1 x) x := by
    intro x
    have hpow : HasDerivAt (fun t : ℝ => t ^ 2 / 6) (2 * x / 6) x := by
      have hp := (hasDerivAt_pow 2 x).div_const 6
      have heq : ((2 : ℕ) : ℝ) * x ^ (2 - 1) / 6 = 2 * x / 6 := by norm_num
      rwa [heq] at hp
    have h1 : HasDerivAt ψ
        (0 + 2 * x / 6 - Real.sinh x + (1 / 3 * Real.sinh x + x / 3 * Real.cosh x)) x :=
      (((hasDerivAt_const x (1 : ℝ)).add hpow).sub (Real.hasDerivAt_cosh x)).add
        (((hasDerivAt_id x).div_const 3).mul (Real.hasDerivAt_sinh x))
    have heq : 0 + 2 * x / 6 - Real.sinh x + (1 / 3 * Real.sinh x + x / 3 * Real.cosh x) =
        ψ1 x := by simp only [ψ1]; ring
    rwa [heq] at h1
  have hψ_nn : ∀ x : ℝ, 0 ≤ x → 0 ≤ ψ x := fun x hx =>
    nonneg_of_deriv_nonneg ψ _ (by simp [ψ]) hψ_deriv hψ1_nn hx
  let φ : ℝ → ℝ := fun x => x - Real.exp (-x ^ 2 / 6) * Real.sinh x
  have hφ_deriv : ∀ x : ℝ, HasDerivAt φ
      (1 - Real.exp (-x ^ 2 / 6) * (Real.cosh x - x / 3 * Real.sinh x)) x := by
    intro x
    have hexp : HasDerivAt (fun t => Real.exp (-t ^ 2 / 6))
        (Real.exp (-x ^ 2 / 6) * (-2 * x / 6)) x := by
      have hq : HasDerivAt (fun t : ℝ => -t ^ 2 / 6) (-2 * x / 6) x := by
        have hp := ((hasDerivAt_pow 2 x).neg).div_const 6
        have heq : -(((2 : ℕ) : ℝ) * x ^ (2 - 1)) / 6 = -2 * x / 6 := by norm_num
        rwa [heq] at hp
      exact hq.exp
    have hmul := hexp.mul (Real.hasDerivAt_sinh x)
    have hsub := (hasDerivAt_id x).sub hmul
    have heq : 1 - (Real.exp (-x ^ 2 / 6) * (-2 * x / 6) * Real.sinh x +
        Real.exp (-x ^ 2 / 6) * Real.cosh x) =
        1 - Real.exp (-x ^ 2 / 6) * (Real.cosh x - x / 3 * Real.sinh x) := by ring
    rwa [heq] at hsub
  have hφ_nn : ∀ x : ℝ, 0 ≤ x →
      0 ≤ 1 - Real.exp (-x ^ 2 / 6) * (Real.cosh x - x / 3 * Real.sinh x) := by
    intro x hx
    have hψx := hψ_nn x hx
    have hle1 : Real.cosh x - x / 3 * Real.sinh x ≤ 1 + x ^ 2 / 6 := by
      simp only [ψ] at hψx; linarith
    have hle2 : 1 + x ^ 2 / 6 ≤ Real.exp (x ^ 2 / 6) := by
      linarith [Real.add_one_le_exp (x ^ 2 / 6)]
    have hprod : Real.exp (-x ^ 2 / 6) * (Real.cosh x - x / 3 * Real.sinh x) ≤
        Real.exp (-x ^ 2 / 6) * Real.exp (x ^ 2 / 6) :=
      mul_le_mul_of_nonneg_left (hle1.trans hle2) (Real.exp_pos _).le
    rw [← Real.exp_add] at hprod
    have hz : -x ^ 2 / 6 + x ^ 2 / 6 = 0 := by ring
    rw [hz, Real.exp_zero] at hprod
    linarith
  have hφs : 0 ≤ φ s := nonneg_of_deriv_nonneg φ _ (by simp [φ]) hφ_deriv hφ_nn hs
  simp only [φ] at hφs
  have h1 : Real.exp (-s ^ 2 / 6) * Real.sinh s ≤ s := by linarith
  calc Real.sinh s
      = Real.exp (s ^ 2 / 6) * (Real.exp (-s ^ 2 / 6) * Real.sinh s) := by
          rw [← mul_assoc, ← Real.exp_add]
          have : s ^ 2 / 6 + -s ^ 2 / 6 = 0 := by ring
          rw [this, Real.exp_zero, one_mul]
    _ ≤ Real.exp (s ^ 2 / 6) * s := mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
    _ = s * Real.exp (s ^ 2 / 6) := mul_comm _ _

lemma integral_exp_Icc_le (s : ℝ) :
    ∫ u in Set.Icc (-1 : ℝ) 1, Real.exp (s * u) ≤ 2 * Real.exp (s ^ 2 / 6) := by
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
  by_cases hs0 : s = 0
  · subst hs0
    norm_num
  · have hderiv : ∀ u ∈ Set.uIcc (-1 : ℝ) 1,
        HasDerivAt (fun t => Real.exp (s * t) / s) (Real.exp (s * u)) u := by
      intro u _
      have h1 : HasDerivAt (fun t => s * t) s u := by
        simpa using (hasDerivAt_id u).const_mul s
      have h2 := h1.exp.div_const s
      have heq : Real.exp (s * u) * s / s = Real.exp (s * u) := mul_div_cancel_right₀ _ hs0
      rwa [heq] at h2
    have hint_s : IntervalIntegrable (fun u => Real.exp (s * u)) volume (-1) 1 :=
      (Real.continuous_exp.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint_s]
    have h_eq : Real.exp (s * 1) / s - Real.exp (s * (-1)) / s = 2 * (Real.sinh |s| / |s|) := by
      rcases lt_or_gt_of_ne hs0 with hlt | hgt
      · rw [abs_of_neg hlt, Real.sinh_eq]
        have : -(-s) = s := neg_neg s
        rw [this]
        field_simp
        ring
      · rw [abs_of_pos hgt, Real.sinh_eq]
        field_simp
    rw [h_eq]
    have habs : 0 < |s| := abs_pos.mpr hs0
    have hsinh := sinh_le_mul_exp_sq_div_six habs.le
    rw [sq_abs] at hsinh
    have hdiv : Real.sinh |s| / |s| ≤ Real.exp (s ^ 2 / 6) :=
      (div_le_iff₀ habs).mpr (by linarith)
    linarith

lemma volume_cube (m : ℕ) : volume (cube m) = (2 : ENNReal) ^ m := by
  have hcube : cube m = Set.pi Set.univ (fun _ : Fin m => Set.Icc (-1 : ℝ) 1) := by
    ext x
    simp [cube, Set.mem_Icc, Pi.le_def]
  rw [hcube, MeasureTheory.volume_pi, Measure.pi_pi]
  simp [Real.volume_Icc, show (1 : ℝ) - -1 = 2 by ring]

lemma integral_prod_exp_cube : ∀ (m : ℕ) (w : Fin m → ℝ),
    ∫ x in cube m, (∏ i : Fin m, Real.exp (w i * x i)) ≤
      (2 : ℝ) ^ m * Real.exp ((∑ i : Fin m, w i ^ 2) / 6)
  | 0, _ => by
    have hcube0 : cube 0 = Set.univ := by
      ext x; simp [cube, Set.mem_Icc]
    have hv0 : (volume (Set.univ : Set (Fin 0 → ℝ))).toReal = 1 := by
      rw [← hcube0, volume_cube 0]
      simp
    rw [hcube0]
    simp [Measure.real, hv0]
  | m + 1, w => by
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0
    have hmp : MeasurePreserving e volume volume :=
      MeasureTheory.volume_preserving_piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0
    have he_set : e ⁻¹' (Set.Icc (-1 : ℝ) 1 ×ˢ cube m) = cube (m + 1) := by
      ext x
      simp only [Set.mem_preimage, e, MeasurableEquiv.piFinSuccAbove_apply, Set.mem_prod,
        cube, Set.mem_Icc, Pi.le_def, Fin.forall_iff_succ]
      constructor
      · rintro ⟨⟨hl0, hu0⟩, hl, hu⟩
        exact ⟨⟨hl0, fun i => hl i⟩, ⟨hu0, fun i => hu i⟩⟩
      · rintro ⟨⟨hl0, hl⟩, ⟨hu0, hu⟩⟩
        exact ⟨⟨hl0, hu0⟩, ⟨fun i => hl i, fun i => hu i⟩⟩
    let g : ℝ × (Fin m → ℝ) → ℝ :=
      fun p => Real.exp (w 0 * p.1) * ∏ i : Fin m, Real.exp (w i.succ * p.2 i)
    have hfun : ∀ x : Fin (m + 1) → ℝ,
        (∏ i : Fin (m + 1), Real.exp (w i * x i)) = g (e x) := by
      intro x
      simp only [g, e, MeasurableEquiv.piFinSuccAbove_apply,
        Fin.prod_univ_succ, Fin.insertNthEquiv_zero, Fin.consEquiv_symm_apply]
      rfl
    simp_rw [hfun, ← he_set]
    rw [hmp.setIntegral_preimage_emb e.measurableEmbedding g (Set.Icc (-1 : ℝ) 1 ×ˢ cube m)]
    have hsplit : ∫ p in Set.Icc (-1 : ℝ) 1 ×ˢ cube m, g p =
        (∫ u in Set.Icc (-1 : ℝ) 1, Real.exp (w 0 * u)) *
          (∫ y in cube m, ∏ i : Fin m, Real.exp (w i.succ * y i)) := by
      simp only [g]
      rw [Measure.volume_eq_prod]
      exact MeasureTheory.setIntegral_prod_mul (μ := (volume : Measure ℝ))
        (ν := (volume : Measure (Fin m → ℝ))) (fun u => Real.exp (w 0 * u))
        (fun y => ∏ i : Fin m, Real.exp (w i.succ * y i)) (Set.Icc (-1 : ℝ) 1) (cube m)
    rw [hsplit]
    have h1 := integral_exp_Icc_le (w 0)
    have h2 := integral_prod_exp_cube m (fun i => w i.succ)
    calc (∫ u in Set.Icc (-1 : ℝ) 1, Real.exp (w 0 * u)) *
            (∫ y in cube m, ∏ i : Fin m, Real.exp (w i.succ * y i))
        ≤ (2 * Real.exp (w 0 ^ 2 / 6)) * ((2 : ℝ) ^ m * Real.exp ((∑ i : Fin m, w i.succ ^ 2) / 6)) :=
            mul_le_mul h1 h2 (setIntegral_nonneg isClosed_Icc.measurableSet
              (fun y _ => Finset.prod_nonneg (fun _ _ => (Real.exp_pos _).le))) (by positivity)
      _ = (2 : ℝ) ^ (m + 1) * (Real.exp (w 0 ^ 2 / 6) * Real.exp ((∑ i : Fin m, w i.succ ^ 2) / 6)) := by
            ring
      _ = (2 : ℝ) ^ (m + 1) * Real.exp ((∑ i : Fin (m + 1), w i ^ 2) / 6) := by
            rw [← Real.exp_add, Fin.sum_univ_succ]
            congr 2
            ring

lemma exp_neg_three_halves_le_two_rpow {lam : ℝ} (hlam : 0 ≤ lam) :
    Real.exp (-3 * lam / 2) ≤ (2 : ℝ) ^ (-2 * lam) := by
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  apply Real.exp_le_exp.mpr
  suffices hlog : Real.log 2 ≤ 3 / 4 by nlinarith
  rw [Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 2)]
  have h1 : (2.71 : ℝ) ≤ Real.exp 1 := by
    linarith [Real.exp_one_gt_d9]
  have h2 : (16 : ℝ) ≤ (Real.exp 1) ^ 3 := by
    have : (16 : ℝ) ≤ (2.71 : ℝ) ^ 3 := by norm_num
    exact this.trans (pow_le_pow_left₀ (by norm_num) h1 3)
  have h3 : (Real.exp (3 / 4)) ^ 4 = (Real.exp 1) ^ 3 := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
    congr 1
    norm_num
  have h4 : (2 : ℝ) ^ 4 ≤ (Real.exp (3 / 4)) ^ 4 := by
    calc (2 : ℝ) ^ 4 = 16 := by norm_num
      _ ≤ (Real.exp 1) ^ 3 := h2
      _ = (Real.exp (3 / 4)) ^ 4 := h3.symm
  exact le_of_pow_le_pow_left₀ (by norm_num : 4 ≠ 0) (Real.exp_pos _).le h4

end AuxLemma8

theorem solution {m : ℕ} (v : Fin m → ℝ) (lam : ℝ) (hlam : 0 ≤ lam) :
    cubeProb m {x | Real.sqrt lam * Real.sqrt (∑ i, v i ^ 2) < ∑ i, v i * x i} ≤
      (2 : ℝ) ^ (-2 * lam) := by
  set E : Set (Fin m → ℝ) := {x | Real.sqrt lam * Real.sqrt (∑ i, v i ^ 2) < ∑ i, v i * x i}
  by_cases hlam0 : lam = 0
  · subst hlam0
    simp only [mul_zero, Real.rpow_zero]
    unfold cubeProb
    have hvol_cube := AuxLemma8.volume_cube m
    have hle : volume (E ∩ cube m) ≤ (2 : ENNReal) ^ m := by
      rw [← hvol_cube]
      exact measure_mono Set.inter_subset_right
    have hfin : ((2 : ENNReal) ^ m) ≠ ⊤ := by finiteness
    have htoReal : (volume (E ∩ cube m)).toReal ≤ ((2 : ENNReal) ^ m).toReal :=
      ENNReal.toReal_mono hfin hle
    simp only [ENNReal.toReal_pow, ENNReal.toReal_ofNat] at htoReal
    exact (div_le_one (by positivity)).mpr htoReal
  have hlam_pos : 0 < lam := lt_of_le_of_ne hlam (Ne.symm hlam0)
  set S2 : ℝ := ∑ i, v i ^ 2
  have hS2_nn : 0 ≤ S2 := Finset.sum_nonneg (fun i _ => sq_nonneg (v i))
  by_cases hS20 : S2 = 0
  · have hv0 : ∀ i, v i = 0 := by
      intro i
      have hsq : v i ^ 2 = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (v j))).mp hS20 i (Finset.mem_univ i)
      exact sq_eq_zero_iff.mp hsq
    have hE_empty : E = ∅ := by
      ext x
      simp [E, hv0]
    rw [hE_empty]
    unfold cubeProb
    simp only [Set.empty_inter, measure_empty, ENNReal.toReal_zero, zero_div]
    positivity
  have hS2_pos : 0 < S2 := lt_of_le_of_ne hS2_nn (Ne.symm hS20)
  set normv : ℝ := Real.sqrt S2
  have hnormv_pos : 0 < normv := Real.sqrt_pos.mpr hS2_pos
  set t : ℝ := 3 * Real.sqrt lam / normv
  have ht_pos : 0 < t := by positivity
  have hE_meas : MeasurableSet (E ∩ cube m) := by
    have hopen : IsOpen E := isOpen_lt continuous_const (continuous_finsetSum _ (fun i _ =>
      continuous_const.mul (continuous_apply i)))
    exact hopen.measurableSet.inter isClosed_Icc.measurableSet
  have hcube_fin : volume (cube m) < ⊤ := by
    rw [AuxLemma8.volume_cube m]
    finiteness
  have hEc_fin : volume (E ∩ cube m) ≠ ⊤ :=
    ((measure_mono Set.inter_subset_right).trans_lt hcube_fin).ne
  have hmarkov : Real.exp (t * (Real.sqrt lam * normv)) * (volume (E ∩ cube m)).toReal ≤
      ∫ x in cube m, Real.exp (∑ i, (t * v i) * x i) := by
    have hcont : ContinuousOn (fun x : Fin m → ℝ => Real.exp (∑ i, (t * v i) * x i)) (cube m) :=
      (Real.continuous_exp.comp (continuous_finsetSum _ (fun i _ =>
        continuous_const.mul (continuous_apply i)))).continuousOn
    have hint : IntegrableOn (fun x : Fin m → ℝ => Real.exp (∑ i, (t * v i) * x i)) (cube m) volume :=
      hcont.integrableOn_compact isCompact_Icc
    calc Real.exp (t * (Real.sqrt lam * normv)) * (volume (E ∩ cube m)).toReal
        = ∫ _ in E ∩ cube m, Real.exp (t * (Real.sqrt lam * normv)) := by
            rw [MeasureTheory.setIntegral_const, smul_eq_mul, mul_comm]
            rfl
      _ ≤ ∫ x in E ∩ cube m, Real.exp (∑ i, (t * v i) * x i) := by
            refine setIntegral_mono_on (integrableOn_const hEc_fin)
              (hint.mono_set Set.inter_subset_right) hE_meas ?_
            intro x hx
            apply Real.exp_le_exp.mpr
            have hlt : Real.sqrt lam * normv < ∑ i, v i * x i := hx.1
            have heq : ∑ i, (t * v i) * x i = t * ∑ i, v i * x i := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl (fun i _ => by ring)
            rw [heq]
            exact mul_le_mul_of_nonneg_left hlt.le ht_pos.le
      _ ≤ ∫ x in cube m, Real.exp (∑ i, (t * v i) * x i) :=
            setIntegral_mono_set hint (Filter.Eventually.of_forall (fun _ => (Real.exp_pos _).le))
              (Filter.Eventually.of_forall (fun _ hx => hx.2))
  have hprod_eq : ∀ x : Fin m → ℝ,
      Real.exp (∑ i, (t * v i) * x i) = ∏ i, Real.exp ((t * v i) * x i) :=
    fun x => Real.exp_sum Finset.univ (fun i => (t * v i) * x i)
  simp_rw [hprod_eq] at hmarkov
  have hbound := hmarkov.trans (AuxLemma8.integral_prod_exp_cube m (fun i => t * v i))
  have hsum_tw : (∑ i : Fin m, (t * v i) ^ 2) / 6 = 3 * lam / 2 := by
    have h1 : ∑ i : Fin m, (t * v i) ^ 2 = t ^ 2 * S2 := by
      simp only [S2, mul_pow, ← Finset.mul_sum]
    rw [h1]
    simp only [t, normv, div_pow, mul_pow, Real.sq_sqrt hlam, Real.sq_sqrt hS2_nn]
    field_simp [hS2_pos.ne']
    ring
  have hexp_lhs : t * (Real.sqrt lam * normv) = 3 * lam := by
    simp only [t]
    field_simp [hnormv_pos.ne']
    rw [Real.sq_sqrt hlam]
  rw [hsum_tw, hexp_lhs] at hbound
  have hvol_le : (volume (E ∩ cube m)).toReal ≤ (2 : ℝ) ^ m * Real.exp (-3 * lam / 2) := by
    have hpos : 0 < Real.exp (3 * lam) := Real.exp_pos _
    rw [← mul_le_mul_iff_right₀ hpos]
    calc Real.exp (3 * lam) * (volume (E ∩ cube m)).toReal
        ≤ (2 : ℝ) ^ m * Real.exp (3 * lam / 2) := hbound
      _ = Real.exp (3 * lam) * ((2 : ℝ) ^ m * Real.exp (-3 * lam / 2)) := by
          have : Real.exp (3 * lam) * ((2 : ℝ) ^ m * Real.exp (-3 * lam / 2)) =
              (2 : ℝ) ^ m * (Real.exp (3 * lam) * Real.exp (-3 * lam / 2)) := by ring
          rw [this, ← Real.exp_add]
          congr 2
          ring
  unfold cubeProb
  calc (volume (E ∩ cube m)).toReal / (2 : ℝ) ^ m
      ≤ ((2 : ℝ) ^ m * Real.exp (-3 * lam / 2)) / (2 : ℝ) ^ m :=
          div_le_div_of_nonneg_right hvol_le (by positivity)
    _ = Real.exp (-3 * lam / 2) := mul_div_cancel_left₀ _ (by positivity)
    _ ≤ (2 : ℝ) ^ (-2 * lam) := AuxLemma8.exp_neg_three_halves_le_two_rpow hlam
