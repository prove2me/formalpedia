-- Prove2me | solution 1 for MertensNumberField.tendsto_log_mul_prod_one_sub_inv_absNorm
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T16:24:32.87486+00:00
-- url     : https://prove2.me/submissions/253161e1-98fd-40e5-8786-bebcea8481f6

import Mathlib
import Theorems.Thm_TauCeti_dedekindZeta_ofReal_eq_exp_tsum_neg_log_one_sub
import Theorems.Thm_TauCeti_tendsto_log_dedekindZeta_re_sub_log_one_div_sub_one
import Theorems.Thm_EulerMascheroni_loglog_integral_asymp
import Theorems.Thm_MertensNumberField_exists_abs_sum_log_absNorm_div_sub_log_le

open Filter Topology NumberField IsDedekindDomain

set_option autoImplicit false

namespace Sol_MertensNumberField_tendsto_log_mul_prod_one_sub_inv_absNorm

variable {F : Type*} [Field F] [NumberField F]

noncomputable def nrm (v : HeightOneSpectrum (𝓞 F)) : ℝ := (Ideal.absNorm v.asIdeal : ℝ)

lemma two_le_nrm (v : HeightOneSpectrum (𝓞 F)) : 2 ≤ nrm v := by
  have := NumberField.HeightOneSpectrum.one_lt_absNorm v
  unfold nrm; exact_mod_cast this

lemma nrm_pos (v : HeightOneSpectrum (𝓞 F)) : 0 < nrm v := by linarith [two_le_nrm v]

lemma finite_nrm_le (x : ℝ) : {v : HeightOneSpectrum (𝓞 F) | nrm v ≤ x}.Finite := by
  have h := Ideal.finite_setOfPred_absNorm_le (S := 𝓞 F) ⌊x⌋₊
  refine (h.preimage (f := fun v : HeightOneSpectrum (𝓞 F) => v.asIdeal) ?_).subset ?_
  · intro v _ w _ hvw; exact HeightOneSpectrum.ext hvw
  · intro v hv
    simp only [Set.mem_ofPred_eq, Set.mem_preimage] at hv ⊢
    have : (Ideal.absNorm v.asIdeal : ℝ) ≤ x := hv
    exact Nat.le_floor this

lemma finite_nrm_lt (x : ℝ) : {v : HeightOneSpectrum (𝓞 F) | nrm v < x}.Finite :=
  (finite_nrm_le x).subset fun _ hv => le_of_lt (show _ < x from hv)

instance countable_hos : Countable (HeightOneSpectrum (𝓞 F)) := by
  have : (Set.univ : Set (HeightOneSpectrum (𝓞 F))) = ⋃ n : ℕ, {v | nrm v ≤ n} := by
    ext v; simp only [Set.mem_univ, Set.mem_iUnion, Set.mem_ofPred_eq, true_iff]
    obtain ⟨n, hn⟩ := exists_nat_ge (nrm v); exact ⟨n, hn⟩
  have hc : (Set.univ : Set (HeightOneSpectrum (𝓞 F))).Countable := by
    rw [this]; exact Set.countable_iUnion fun n => (finite_nrm_le (n : ℝ)).countable
  exact Set.countable_univ_iff.mp hc

/-- `g s v = -log (1 - N(v)^(-s))`. -/
noncomputable def g (s : ℝ) (v : HeightOneSpectrum (𝓞 F)) : ℝ := -Real.log (1 - nrm v ^ (-s))

/-- `a v = -log (1 - N(v)⁻¹)`. -/
noncomputable def a (v : HeightOneSpectrum (𝓞 F)) : ℝ := -Real.log (1 - (nrm v)⁻¹)

lemma rpow_neg_le_inv {s : ℝ} (hs : 1 ≤ s) (v : HeightOneSpectrum (𝓞 F)) :
    nrm v ^ (-s) ≤ (nrm v)⁻¹ := by
  have h2 := two_le_nrm v
  calc nrm v ^ (-s) ≤ nrm v ^ (-1:ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    _ = (nrm v)⁻¹ := Real.rpow_neg_one _

lemma inv_le_half (v : HeightOneSpectrum (𝓞 F)) : (nrm v)⁻¹ ≤ 1 / 2 := by
  rw [one_div]; exact inv_anti₀ (by norm_num) (two_le_nrm v)

lemma self_le_neg_log_one_sub {y : ℝ} (hy1 : y < 1) : y ≤ -Real.log (1 - y) := by
  have := Real.log_le_sub_one_of_pos (show 0 < 1 - y by linarith); linarith

lemma neg_log_one_sub_le {y : ℝ} (_hy0 : 0 ≤ y) (hy : y ≤ 1 / 2) :
    -Real.log (1 - y) ≤ y + 2 * y ^ 2 := by
  have h1 : 0 < 1 - y := by linarith
  have h2 := Real.one_sub_inv_le_log_of_pos h1
  have h3 : (1 - y)⁻¹ ≤ 1 + y + 2 * y ^ 2 := by
    rw [inv_le_iff_one_le_mul₀ h1]; nlinarith
  linarith

lemma g_nonneg {s : ℝ} (hs : 1 ≤ s) (v : HeightOneSpectrum (𝓞 F)) : 0 ≤ g s v :=
  le_trans (Real.rpow_nonneg (nrm_pos v).le _)
    (self_le_neg_log_one_sub (by linarith [rpow_neg_le_inv hs v, inv_le_half v]))

lemma g_anti {s t : ℝ} (hs : 1 ≤ s) (hst : s ≤ t) (v : HeightOneSpectrum (𝓞 F)) :
    g t v ≤ g s v := by
  unfold g
  have h1 : nrm v ^ (-t) ≤ nrm v ^ (-s) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith [two_le_nrm v]) (by linarith)
  have h2 : 0 < 1 - nrm v ^ (-s) := by linarith [rpow_neg_le_inv hs v, inv_le_half v]
  have := Real.log_le_log h2 (by linarith : 1 - nrm v ^ (-s) ≤ 1 - nrm v ^ (-t))
  linarith

lemma summable_g {s : ℝ} (hs : 1 < s) : Summable (g (F := F) s) := by
  by_contra hns
  have key : ∀ t ∈ Set.Ioc 1 s, dedekindZeta F t = 1 := by
    intro t ht
    have hnt : ¬ Summable (g (F := F) t) := fun h =>
      hns (Summable.of_nonneg_of_le (g_nonneg hs.le) (g_anti ht.1.le ht.2) h)
    rw [TauCeti.dedekindZeta_ofReal_eq_exp_tsum_neg_log_one_sub ht.1]
    have : (∑' P : HeightOneSpectrum (𝓞 F),
        -Real.log (1 - (Ideal.absNorm P.asIdeal : ℝ) ^ (-t))) = 0 :=
      tsum_eq_zero_of_not_summable hnt
    rw [this]; simp
  have h1 := tendsto_sub_one_mul_dedekindZeta_nhdsGT F
  have h2 : Tendsto (fun s : ℝ ↦ ((s : ℂ) - 1) * dedekindZeta F s) (𝓝[>] 1) (𝓝 0) := by
    have h3 : Tendsto (fun s : ℝ => ((s : ℂ) - 1)) (𝓝[>] 1) (𝓝 0) := by
      have : Tendsto (fun s : ℝ => ((s : ℂ) - 1)) (𝓝 1) (𝓝 (((1 : ℝ) : ℂ) - 1)) :=
        ((Complex.continuous_ofReal.tendsto 1).sub tendsto_const_nhds)
      simpa using this.mono_left nhdsWithin_le_nhds
    refine h3.congr' ?_
    filter_upwards [Ioc_mem_nhdsGT hs] with t ht
    rw [key t ht, mul_one]
  have := tendsto_nhds_unique h1 h2
  exact dedekindZeta_residue_ne_zero F (by exact_mod_cast this)

lemma summable_rpow {s : ℝ} (hs : 1 < s) :
    Summable (fun v : HeightOneSpectrum (𝓞 F) => nrm v ^ (-s)) :=
  Summable.of_nonneg_of_le (fun v => Real.rpow_nonneg (nrm_pos v).le _)
    (fun v => self_le_neg_log_one_sub (by linarith [rpow_neg_le_inv hs.le v, inv_le_half v]))
    (summable_g hs)

lemma a_eq_g_one (v : HeightOneSpectrum (𝓞 F)) : a v = g 1 v := by
  unfold a g; rw [Real.rpow_neg_one]

lemma inv_le_a (v : HeightOneSpectrum (𝓞 F)) : (nrm v)⁻¹ ≤ a v :=
  self_le_neg_log_one_sub (by linarith [inv_le_half v])

lemma a_le (v : HeightOneSpectrum (𝓞 F)) : a v ≤ (nrm v)⁻¹ + 2 * ((nrm v)⁻¹) ^ 2 :=
  neg_log_one_sub_le (inv_nonneg.mpr (nrm_pos v).le) (inv_le_half v)

lemma g_le {s : ℝ} (hs : 1 ≤ s) (v : HeightOneSpectrum (𝓞 F)) :
    g s v ≤ nrm v ^ (-s) + 2 * (nrm v ^ (-s)) ^ 2 :=
  neg_log_one_sub_le (Real.rpow_nonneg (nrm_pos v).le _)
    (le_trans (rpow_neg_le_inv hs v) (inv_le_half v))

lemma rpow_one_sub (s : ℝ) (v : HeightOneSpectrum (𝓞 F)) :
    nrm v ^ (1 - s) = nrm v * nrm v ^ (-s) := by
  rw [sub_eq_add_neg, Real.rpow_add (nrm_pos v), Real.rpow_one]

lemma inv_sq_eq_rpow (v : HeightOneSpectrum (𝓞 F)) : ((nrm v)⁻¹) ^ 2 = nrm v ^ (-(2 : ℝ)) := by
  rw [Real.rpow_neg (nrm_pos v).le, Real.rpow_two, inv_pow]

lemma summable_inv_sq : Summable (fun v : HeightOneSpectrum (𝓞 F) => ((nrm v)⁻¹) ^ 2) := by
  simp_rw [inv_sq_eq_rpow]; exact summable_rpow (by norm_num)

lemma aU_le {s : ℝ} (_hs : 1 ≤ s) (v : HeightOneSpectrum (𝓞 F)) :
    a v * nrm v ^ (1 - s) ≤ 2 * nrm v ^ (-s) := by
  rw [rpow_one_sub]
  have hN := nrm_pos v
  have hu : (nrm v)⁻¹ * nrm v = 1 := inv_mul_cancel₀ hN.ne'
  have ha : a v ≤ 2 * (nrm v)⁻¹ := by
    have := a_le v; have := inv_le_half v; have := inv_nonneg.mpr hN.le; nlinarith
  have hy := Real.rpow_nonneg hN.le (-s)
  calc a v * (nrm v * nrm v ^ (-s)) ≤ 2 * (nrm v)⁻¹ * (nrm v * nrm v ^ (-s)) :=
        mul_le_mul_of_nonneg_right ha (mul_nonneg hN.le hy)
    _ = 2 * ((nrm v)⁻¹ * nrm v) * nrm v ^ (-s) := by ring
    _ = 2 * nrm v ^ (-s) := by rw [hu, mul_one]

lemma a_nonneg (v : HeightOneSpectrum (𝓞 F)) : 0 ≤ a v :=
  le_trans (inv_nonneg.mpr (nrm_pos v).le) (inv_le_a v)

lemma summable_aU {s : ℝ} (hs : 1 < s) :
    Summable (fun v : HeightOneSpectrum (𝓞 F) => a v * nrm v ^ (1 - s)) :=
  Summable.of_nonneg_of_le (fun v => mul_nonneg (a_nonneg v) (Real.rpow_nonneg (nrm_pos v).le _))
    (fun v => aU_le hs.le v) ((summable_rpow hs).mul_left 2)

lemma abs_diff_le {s : ℝ} (hs : 1 ≤ s) (v : HeightOneSpectrum (𝓞 F)) :
    |g s v - a v * nrm v ^ (1 - s)| ≤ 2 * ((nrm v)⁻¹) ^ 2 := by
  rw [rpow_one_sub]
  have hN := nrm_pos v
  have hu : (nrm v)⁻¹ * nrm v = 1 := inv_mul_cancel₀ hN.ne'
  set y := nrm v ^ (-s) with hy_def
  set u := (nrm v)⁻¹ with hu_def
  have hy0 : 0 ≤ y := Real.rpow_nonneg hN.le _
  have hyu : y ≤ u := rpow_neg_le_inv hs v
  have hu0 : 0 ≤ u := inv_nonneg.mpr hN.le
  have hg1 : y ≤ g s v := self_le_neg_log_one_sub (by linarith [inv_le_half v])
  have hg2 : g s v ≤ y + 2 * y ^ 2 := g_le hs v
  have ha1 : u ≤ a v := inv_le_a v
  have ha2 : a v ≤ u + 2 * u ^ 2 := a_le v
  have hNy : 0 ≤ nrm v * y := mul_nonneg hN.le hy0
  have e1 : u * (nrm v * y) = y := by rw [← mul_assoc, hu, one_mul]
  have e2 : (u + 2 * u ^ 2) * (nrm v * y) = y + 2 * u * y := by
    have : (u + 2 * u ^ 2) * (nrm v * y) = u * (nrm v * y) + 2 * u * (u * (nrm v * y)) := by ring
    rw [this, e1]
  have hb1 : y ≤ a v * (nrm v * y) :=
    calc y = u * (nrm v * y) := e1.symm
      _ ≤ a v * (nrm v * y) := mul_le_mul_of_nonneg_right ha1 hNy
  have hb2 : a v * (nrm v * y) ≤ y + 2 * u * y :=
    calc a v * (nrm v * y) ≤ (u + 2 * u ^ 2) * (nrm v * y) := mul_le_mul_of_nonneg_right ha2 hNy
      _ = y + 2 * u * y := e2
  rw [abs_le]; constructor <;> nlinarith

noncomputable def T (s : ℝ) : ℝ := ∑' v : HeightOneSpectrum (𝓞 F), g s v
noncomputable def U (s : ℝ) : ℝ := ∑' v : HeightOneSpectrum (𝓞 F), a v * nrm v ^ (1 - s)

lemma tendsto_g (v : HeightOneSpectrum (𝓞 F)) :
    Tendsto (fun s : ℝ => g s v - a v * nrm v ^ (1 - s)) (𝓝[>] 1) (𝓝 0) := by
  have hN := nrm_pos v
  have hc1 : ContinuousAt (fun s : ℝ => nrm v ^ (-s)) 1 :=
    continuousAt_const.rpow continuous_neg.continuousAt (Or.inl hN.ne')
  have hne : (1 : ℝ) - nrm v ^ (-(1 : ℝ)) ≠ 0 := by
    rw [Real.rpow_neg_one]; linarith [inv_le_half v]
  have hc2 : ContinuousAt (fun s : ℝ => g s v) 1 := by
    unfold g
    exact ((continuousAt_const.sub hc1).log hne).neg
  have hc3 : ContinuousAt (fun s : ℝ => nrm v ^ (1 - s)) 1 :=
    continuousAt_const.rpow (continuousAt_const.sub continuousAt_id) (Or.inl hN.ne')
  have hc : ContinuousAt (fun s : ℝ => g s v - a v * nrm v ^ (1 - s)) 1 :=
    hc2.sub (continuousAt_const.mul hc3)
  have := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi 1))
  convert this using 2
  rw [← a_eq_g_one, sub_self, Real.rpow_zero, mul_one, sub_self]

lemma tendsto_T_sub_U :
    Tendsto (fun s : ℝ => T (F := F) s - U (F := F) s) (𝓝[>] 1) (𝓝 0) := by
  have h : Tendsto (fun s : ℝ => ∑' v : HeightOneSpectrum (𝓞 F), (g s v - a v * nrm v ^ (1 - s)))
      (𝓝[>] 1) (𝓝 (∑' _ : HeightOneSpectrum (𝓞 F), (0 : ℝ))) := by
    refine tendsto_tsum_of_dominated_convergence (summable_inv_sq.mul_left 2)
      (fun v => tendsto_g v) ?_
    filter_upwards [self_mem_nhdsWithin] with s hs v
    rw [Real.norm_eq_abs]; exact abs_diff_le (le_of_lt hs) v
  rw [tsum_zero] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact (Summable.tsum_sub (summable_g hs) (summable_aU hs))

lemma tendsto_T_add_log :
    Tendsto (fun s : ℝ => T (F := F) s + Real.log (s - 1)) (𝓝[>] 1)
      (𝓝 (Real.log (dedekindZeta_residue F))) := by
  have h := TauCeti.tendsto_log_dedekindZeta_re_sub_log_one_div_sub_one (K := F)
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs' : (1 : ℝ) < s := hs
  rw [TauCeti.dedekindZeta_ofReal_eq_exp_tsum_neg_log_one_sub hs', Complex.ofReal_re,
    Real.log_exp, one_div, Real.log_inv, sub_neg_eq_add]
  rfl

open MeasureTheory in
lemma integrableOn_rpow {s : ℝ} (hs : 1 < s) :
    IntegrableOn (fun t : ℝ => t ^ (-s)) (Set.Ioi 2) :=
  integrableOn_Ioi_rpow_of_lt (by linarith) (by norm_num)

lemma integral_rpow {s : ℝ} (hs : 1 < s) :
    ∫ t in Set.Ioi (2 : ℝ), t ^ (-s) = 2 ^ (1 - s) / (s - 1) := by
  rw [integral_Ioi_rpow_of_lt (by linarith) (by norm_num)]
  have h1 : (-s + 1) = 1 - s := by ring
  rw [h1, neg_div, ← div_neg, neg_sub]

open MeasureTheory in
lemma integrableOn_mul_rpow_of_bdd {E : ℝ → ℝ} {M s : ℝ} (hs : 1 < s) (hEm : Measurable E)
    (hM : ∀ t, 2 < t → |E t| ≤ M) :
    IntegrableOn (fun t : ℝ => E t * t ^ (-s)) (Set.Ioi 2) := by
  refine Integrable.mono' ((integrableOn_rpow hs).const_mul M) ?_ ?_
  · exact (hEm.mul (measurable_id.pow_const _)).aestronglyMeasurable
  · rw [ae_restrict_iff' measurableSet_Ioi]
    refine Filter.Eventually.of_forall fun t ht => ?_
    have ht' : (2 : ℝ) < t := ht
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg (by linarith) _)]
    exact mul_le_mul_of_nonneg_right (hM t ht') (Real.rpow_nonneg (by linarith) _)

open MeasureTheory in
/-- An Abelian lemma: if `E` is bounded on `(2,∞)` and `E t → L`, then
`(s-1) ∫_{2}^{∞} E(t) t^{-s} dt → L` as `s → 1⁺`. -/
lemma tendsto_mellin_of_tendsto {E : ℝ → ℝ} {L M : ℝ} (hEm : Measurable E)
    (hM : ∀ t, 2 < t → |E t| ≤ M) (hL : Tendsto E atTop (𝓝 L)) :
    Tendsto (fun s : ℝ => (s - 1) * ∫ t in Set.Ioi (2 : ℝ), E t * t ^ (-s)) (𝓝[>] 1) (𝓝 L) := by
  -- the error term
  have hmain : Tendsto (fun s : ℝ => (s - 1) * ∫ t in Set.Ioi (2 : ℝ), (E t - L) * t ^ (-s))
      (𝓝[>] 1) (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hε3 : 0 < ε / 3 := by linarith
    obtain ⟨T0, hT0⟩ := Filter.eventually_atTop.mp
      (hL.eventually (Metric.closedBall_mem_nhds L hε3))
    set T := max T0 3 with hT
    have hT3 : 3 ≤ T := le_max_right _ _
    set C := M + |L| with hC
    have hC0 : 0 ≤ C := by
      have := hM 3 (by norm_num); have := abs_nonneg (E 3); have := abs_nonneg L; linarith
    have hpt : ∀ t, 2 < t → |E t - L| ≤ ε / 3 + C * T * t⁻¹ := by
      intro t ht
      have ht0 : 0 < t := by linarith
      by_cases htT : T ≤ t
      · have h1 := hT0 t (le_trans (le_max_left _ _) htT)
        rw [Real.dist_eq] at h1
        have : 0 ≤ C * T * t⁻¹ := by positivity
        linarith
      · push Not at htT
        have h1 : 1 ≤ T * t⁻¹ := by rw [← div_eq_mul_inv, le_div_iff₀ ht0]; linarith
        have h2 : C ≤ C * T * t⁻¹ := by
          rw [mul_assoc]; nlinarith
        have h3 : |E t - L| ≤ C := by
          have := abs_sub (E t) L; have := hM t ht; linarith
        linarith
    have hδ : 0 < ε / 3 / (C * T + 1) := by positivity
    filter_upwards [Ioo_mem_nhdsGT (show (1 : ℝ) < 1 + ε / 3 / (C * T + 1) by linarith)]
      with s hs
    obtain ⟨hs1, hs2⟩ := hs
    have hs0 : 0 < s - 1 := by linarith
    -- the dominating function
    set b : ℝ → ℝ := fun t => ε / 3 * t ^ (-s) + C * T * t ^ (-1 - s) with hb
    have hbint : IntegrableOn b (Set.Ioi 2) :=
      ((integrableOn_rpow hs1).const_mul _).add
        ((integrableOn_Ioi_rpow_of_lt (by linarith) (by norm_num)).const_mul _)
    have hbval : ∫ t in Set.Ioi (2 : ℝ), b t = ε / 3 * (2 ^ (1 - s) / (s - 1)) +
        C * T * (2 ^ (-s) / s) := by
      rw [hb, integral_add ((integrableOn_rpow hs1).const_mul _)
        ((integrableOn_Ioi_rpow_of_lt (by linarith) (by norm_num)).const_mul _),
        integral_const_mul, integral_const_mul, integral_rpow hs1,
        integral_Ioi_rpow_of_lt (by linarith) (by norm_num)]
      congr 2
      rw [show (-1 - s + 1) = -s by ring, neg_div_neg_eq]
    have hle : ‖∫ t in Set.Ioi (2 : ℝ), (E t - L) * t ^ (-s)‖ ≤ ∫ t in Set.Ioi (2 : ℝ), b t := by
      refine norm_integral_le_of_norm_le hbint ?_
      rw [ae_restrict_iff' measurableSet_Ioi]
      refine Filter.Eventually.of_forall fun t ht => ?_
      have ht' : (2 : ℝ) < t := ht
      have ht0 : 0 < t := by linarith
      have hp : 0 ≤ t ^ (-s) := Real.rpow_nonneg ht0.le _
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hp]
      simp only [hb]
      have e1 : t ^ (-1 - s) = t⁻¹ * t ^ (-s) := by
        rw [sub_eq_add_neg, Real.rpow_add ht0, Real.rpow_neg_one]
      rw [e1]
      calc |E t - L| * t ^ (-s) ≤ (ε / 3 + C * T * t⁻¹) * t ^ (-s) :=
            mul_le_mul_of_nonneg_right (hpt t ht') hp
        _ = ε / 3 * t ^ (-s) + C * T * (t⁻¹ * t ^ (-s)) := by ring
    rw [hbval] at hle
    have h21 : (2 : ℝ) ^ (1 - s) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
    have h22 : (2 : ℝ) ^ (-s) / s ≤ 1 := by
      rw [div_le_one (by linarith)]
      have : (2 : ℝ) ^ (-s) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
      linarith
    rw [Real.dist_eq, sub_zero, abs_mul, abs_of_pos hs0]
    have hnn : 0 ≤ ‖∫ t in Set.Ioi (2 : ℝ), (E t - L) * t ^ (-s)‖ := norm_nonneg _
    rw [← Real.norm_eq_abs]
    calc (s - 1) * ‖∫ t in Set.Ioi (2 : ℝ), (E t - L) * t ^ (-s)‖
        ≤ (s - 1) * (ε / 3 * (2 ^ (1 - s) / (s - 1)) + C * T * (2 ^ (-s) / s)) :=
          mul_le_mul_of_nonneg_left hle hs0.le
      _ = ε / 3 * 2 ^ (1 - s) + (s - 1) * (C * T) * (2 ^ (-s) / s) := by
          field_simp
      _ ≤ ε / 3 * 1 + (s - 1) * (C * T) * 1 := by
          gcongr
      _ < ε := by
          have : (s - 1) * (C * T) < ε / 3 := by
            have h3 : s - 1 < ε / 3 / (C * T + 1) := by linarith
            rw [lt_div_iff₀ (by positivity)] at h3
            nlinarith
          linarith
  -- the main term
  have hconst : Tendsto (fun s : ℝ => L * (2 : ℝ) ^ (1 - s)) (𝓝[>] 1) (𝓝 L) := by
    have hc : ContinuousAt (fun s : ℝ => L * (2 : ℝ) ^ (1 - s)) 1 :=
      continuousAt_const.mul (continuousAt_const.rpow (continuousAt_const.sub continuousAt_id)
        (Or.inl (by norm_num)))
    have := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi 1))
    simpa using this
  have hsum := hconst.add hmain
  rw [add_zero] at hsum
  refine hsum.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs1 : (1 : ℝ) < s := hs
  have hint1 := integrableOn_mul_rpow_of_bdd hs1 hEm hM
  have hint2 : IntegrableOn (fun t : ℝ => L * t ^ (-s)) (Set.Ioi 2) :=
    (integrableOn_rpow hs1).const_mul L
  have : (fun t : ℝ => (E t - L) * t ^ (-s)) = fun t => E t * t ^ (-s) - L * t ^ (-s) := by
    funext t; ring
  rw [this, integral_sub hint1 hint2, integral_const_mul, integral_rpow hs1]
  have hs0 : s - 1 ≠ 0 := by linarith
  field_simp
  ring

/-- `S t = ∑_{N(v) < t} -log (1 - N(v)⁻¹)`. -/
noncomputable def S (t : ℝ) : ℝ := ∑ v ∈ (finite_nrm_lt (F := F) t).toFinset, a v

lemma S_mono : Monotone (S (F := F)) := by
  intro t t' htt'
  unfold S
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun v _ _ => a_nonneg v)
  intro v hv
  rw [Set.Finite.mem_toFinset] at hv ⊢
  exact lt_of_lt_of_le hv htt'

lemma tsum_indicator_eq (s t : ℝ) :
    ∑' v : HeightOneSpectrum (𝓞 F), Set.indicator (Set.Ioi (nrm v)) (fun t => a v * t ^ (-s)) t
      = S (F := F) t * t ^ (-s) := by
  rw [tsum_eq_sum (s := (finite_nrm_lt (F := F) t).toFinset)]
  · unfold S; rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun v hv => ?_
    rw [Set.Finite.mem_toFinset] at hv
    exact Set.indicator_of_mem (show t ∈ Set.Ioi (nrm v) from hv) _
  · intro v hv
    rw [Set.Finite.mem_toFinset] at hv
    exact Set.indicator_of_notMem (show t ∉ Set.Ioi (nrm v) from hv) _

open MeasureTheory in
lemma U_eq {s : ℝ} (hs : 1 < s) :
    U (F := F) s = (s - 1) * ∫ t in Set.Ioi (2 : ℝ), S (F := F) t * t ^ (-s) := by
  set Fv : HeightOneSpectrum (𝓞 F) → ℝ → ℝ :=
    fun v => Set.indicator (Set.Ioi (nrm v)) (fun t => a v * t ^ (-s)) with hFv
  have hF_int : ∀ v, Integrable (Fv v) (volume.restrict (Set.Ioi 2)) := fun v =>
    ((integrableOn_rpow hs).const_mul (a v)).indicator measurableSet_Ioi
  have hval : ∀ v, ∫ t in Set.Ioi (2 : ℝ), Fv v t = a v * nrm v ^ (1 - s) / (s - 1) := by
    intro v
    simp only [hFv]
    rw [setIntegral_indicator measurableSet_Ioi, Set.Ioi_inter_Ioi, max_eq_right (two_le_nrm v),
      integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) (nrm_pos v),
      show -s + 1 = 1 - s by ring, neg_div, ← div_neg, neg_sub, mul_div_assoc]
  have hnn : ∀ v t, 0 ≤ Fv v t := by
    intro v t
    simp only [hFv]
    refine Set.indicator_nonneg (fun t ht => ?_) t
    have ht' : nrm v < t := ht
    exact mul_nonneg (a_nonneg v) (Real.rpow_nonneg (by linarith [nrm_pos v]) _)
  have hnorm : ∀ v, ∫ t in Set.Ioi (2 : ℝ), ‖Fv v t‖ = ∫ t in Set.Ioi (2 : ℝ), Fv v t := by
    intro v; congr 1; funext t; exact Real.norm_of_nonneg (hnn v t)
  have hsum : Summable (fun v => ∫ t in Set.Ioi (2 : ℝ), ‖Fv v t‖) := by
    simp_rw [hnorm, hval]; exact (summable_aU hs).div_const _
  have key := integral_tsum_of_summable_integral_norm hF_int hsum
  have hS : (fun t => S (F := F) t * t ^ (-s)) = fun t => ∑' v, Fv v t := by
    funext t; rw [← tsum_indicator_eq]
  rw [hS, ← key]
  simp_rw [hval]
  rw [tsum_div_const]
  unfold U
  have : s - 1 ≠ 0 := by linarith
  field_simp

open MeasureTheory in
lemma integrableOn_loglog {s : ℝ} (hs : 1 < s) :
    IntegrableOn (fun t : ℝ => Real.log (Real.log t) * t ^ (-s)) (Set.Ioi 2) := by
  set ε := (s - 1) / 2 with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  refine Integrable.mono' ((integrableOn_rpow hs).add
    ((integrableOn_Ioi_rpow_of_lt (a := ε - s) (by rw [hε]; linarith) (by norm_num)).const_mul
      (1 / ε))) ?_ ?_
  · exact ((Real.measurable_log.comp Real.measurable_log).mul
      (measurable_id.pow_const _)).aestronglyMeasurable
  · rw [ae_restrict_iff' measurableSet_Ioi]
    refine Filter.Eventually.of_forall fun t ht => ?_
    have ht' : (2 : ℝ) < t := ht
    have ht0 : 0 < t := by linarith
    have hp : 0 ≤ t ^ (-s) := Real.rpow_nonneg ht0.le _
    have hlog2 : (2 : ℝ)⁻¹ < Real.log t := by
      have := Real.log_two_gt_d9
      have := Real.log_lt_log (by norm_num) ht'
      norm_num at *; linarith
    have hlogpos : 0 < Real.log t := by linarith
    have hup : Real.log (Real.log t) ≤ t ^ ε / ε := by
      have h1 := Real.log_le_sub_one_of_pos hlogpos
      have h2 := Real.log_le_rpow_div ht0.le hε0
      linarith
    have hlow : -1 ≤ Real.log (Real.log t) := by
      have h1 := Real.log_le_sub_one_of_pos (inv_pos.mpr hlogpos)
      rw [Real.log_inv] at h1
      have h2 : (Real.log t)⁻¹ ≤ 2 := by
        rw [inv_le_comm₀ hlogpos (by norm_num)]; exact hlog2.le
      linarith
    have hpow : 0 ≤ t ^ ε / ε := div_nonneg (Real.rpow_nonneg ht0.le _) hε0.le
    have habs : |Real.log (Real.log t)| ≤ 1 + t ^ ε / ε := by
      rw [abs_le]; constructor <;> linarith
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hp]
    have e1 : t ^ (ε - s) = t ^ ε * t ^ (-s) := by
      rw [sub_eq_add_neg, Real.rpow_add ht0]
    calc |Real.log (Real.log t)| * t ^ (-s) ≤ (1 + t ^ ε / ε) * t ^ (-s) :=
          mul_le_mul_of_nonneg_right habs hp
      _ = t ^ (-s) + 1 / ε * t ^ (ε - s) := by rw [e1]; ring

lemma key_limit {L : ℝ}
    (hL : Tendsto (fun t => S (F := F) t - Real.log (Real.log t)) atTop (𝓝 L)) :
    L = Real.log (dedekindZeta_residue F) + Real.eulerMascheroniConstant := by
  set E : ℝ → ℝ := fun t => S (F := F) t - Real.log (Real.log t) with hE
  have hEm : Measurable E :=
    (S_mono (F := F)).measurable.sub (Real.measurable_log.comp Real.measurable_log)
  obtain ⟨T0, hT0⟩ := Filter.eventually_atTop.mp
    (hL.eventually (Metric.closedBall_mem_nhds L (show (0 : ℝ) < 1 by norm_num)))
  set T1 := max T0 3 with hT1
  set M := |L| + 1 + S (F := F) T1 + |Real.log (Real.log 2)| + |Real.log (Real.log T1)| with hMdef
  have hS0 : ∀ t, 0 ≤ S (F := F) t := fun t =>
    Finset.sum_nonneg (fun v _ => a_nonneg v)
  have hM : ∀ t, 2 < t → |E t| ≤ M := by
    intro t ht
    by_cases htT : T1 ≤ t
    · have h1 := hT0 t (le_trans (le_max_left _ _) htT)
      rw [Real.dist_eq] at h1
      have := abs_sub_abs_le_abs_sub (E t) L
      have := hS0 T1; have := abs_nonneg (Real.log (Real.log 2))
      have := abs_nonneg (Real.log (Real.log T1))
      simp only [hMdef]; linarith
    · push Not at htT
      have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have hl1 : Real.log 2 ≤ Real.log t := Real.log_le_log (by norm_num) ht.le
      have hl2 : Real.log t ≤ Real.log T1 := Real.log_le_log (by linarith) htT.le
      have hll1 : Real.log (Real.log 2) ≤ Real.log (Real.log t) := Real.log_le_log hlog2 hl1
      have hll2 : Real.log (Real.log t) ≤ Real.log (Real.log T1) :=
        Real.log_le_log (by linarith) hl2
      have hSt : S (F := F) t ≤ S (F := F) T1 := S_mono htT.le
      have := hS0 t
      have h3 : |Real.log (Real.log t)| ≤ |Real.log (Real.log 2)| + |Real.log (Real.log T1)| := by
        rw [abs_le]; constructor
        · have := neg_abs_le (Real.log (Real.log 2)); have := abs_nonneg (Real.log (Real.log T1))
          linarith
        · have := le_abs_self (Real.log (Real.log T1)); have := abs_nonneg (Real.log (Real.log 2))
          linarith
      have h4 : |E t| ≤ S (F := F) t + |Real.log (Real.log t)| := by
        simp only [hE]
        calc |S t - Real.log (Real.log t)| ≤ |S (F := F) t| + |Real.log (Real.log t)| :=
              abs_sub _ _
          _ = S (F := F) t + |Real.log (Real.log t)| := by rw [abs_of_nonneg (hS0 t)]
      have := abs_nonneg L
      simp only [hMdef]; linarith
  have h1 := tendsto_mellin_of_tendsto hEm hM hL
  have h2 := EulerMascheroni.loglog_integral_asymp
  have h3 := tendsto_T_sub_U (F := F)
  have h4 := (h3.add h2).add h1
  have h5 := tendsto_T_add_log (F := F)
  have h6 : Tendsto (fun s : ℝ => T (F := F) s + Real.log (s - 1)) (𝓝[>] 1)
      (𝓝 (0 + -Real.eulerMascheroniConstant + L)) := by
    refine h4.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs1 : (1 : ℝ) < s := hs
    rw [U_eq hs1]
    have hsplit : ∫ t in Set.Ioi (2 : ℝ), S (F := F) t * t ^ (-s) =
        (∫ t in Set.Ioi (2 : ℝ), Real.log (Real.log t) * t ^ (-s)) +
          ∫ t in Set.Ioi (2 : ℝ), E t * t ^ (-s) := by
      rw [← MeasureTheory.integral_add (integrableOn_loglog hs1)
        (integrableOn_mul_rpow_of_bdd hs1 hEm hM)]
      congr 1; funext t; simp only [hE]; ring
    rw [hsplit]; ring
  have := tendsto_nhds_unique h5 h6
  linarith

lemma prod_eq (x : ℝ) :
    ∏ᶠ (v : HeightOneSpectrum (𝓞 F)) (_ : (Ideal.absNorm v.asIdeal : ℝ) < x),
      (1 - ((Ideal.absNorm v.asIdeal : ℝ))⁻¹) = Real.exp (-S (F := F) x) := by
  have h := finprod_mem_eq_finite_toFinset_prod (fun v : HeightOneSpectrum (𝓞 F) =>
    (1 - (nrm v)⁻¹)) (finite_nrm_lt (F := F) x)
  refine h.trans ?_
  have : -S (F := F) x = ∑ v ∈ (finite_nrm_lt (F := F) x).toFinset, Real.log (1 - (nrm v)⁻¹) := by
    unfold S a; rw [← Finset.sum_neg_distrib]; simp only [neg_neg]
  rw [this, Real.exp_sum]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [Real.exp_log (by linarith [inv_le_half v])]

/-! ### Mertens' second theorem from Mertens' first theorem (partial summation) -/

/-- `c v = log N(v) / N(v)`. -/
noncomputable def c (v : HeightOneSpectrum (𝓞 F)) : ℝ := Real.log (nrm v) / nrm v

lemma log_nrm_pos (v : HeightOneSpectrum (𝓞 F)) : 0 < Real.log (nrm v) :=
  Real.log_pos (by linarith [two_le_nrm v])

lemma c_nonneg (v : HeightOneSpectrum (𝓞 F)) : 0 ≤ c v :=
  div_nonneg (log_nrm_pos v).le (nrm_pos v).le

/-- `A x = ∑_{N(v) ≤ x} log N(v) / N(v)`. -/
noncomputable def A (x : ℝ) : ℝ := ∑ v ∈ (finite_nrm_le (F := F) x).toFinset, c v

/-- `Alt x = ∑_{N(v) < x} log N(v) / N(v)`. -/
noncomputable def Alt (x : ℝ) : ℝ := ∑ v ∈ (finite_nrm_lt (F := F) x).toFinset, c v

/-- `Plt x = ∑_{N(v) < x} 1 / N(v)`. -/
noncomputable def Plt (x : ℝ) : ℝ := ∑ v ∈ (finite_nrm_lt (F := F) x).toFinset, (nrm v)⁻¹

/-- The terms `log N(v) / N(v)^k` of the von Mangoldt sum. -/
noncomputable def fvm (p : HeightOneSpectrum (𝓞 F) × ℕ) : ℝ := Real.log (nrm p.1) / nrm p.1 ^ p.2

lemma fvm_nonneg (p : HeightOneSpectrum (𝓞 F) × ℕ) : 0 ≤ fvm p :=
  div_nonneg (log_nrm_pos p.1).le (pow_nonneg (nrm_pos p.1).le _)

lemma pset_bounds {v : HeightOneSpectrum (𝓞 F)} {k : ℕ} {x : ℝ} (hk : 0 < k)
    (hle : nrm v ^ k ≤ x) : nrm v ≤ x ∧ k ≤ ⌊x⌋₊ := by
  have hN := two_le_nrm v
  have h1 : nrm v ≤ nrm v ^ k := le_self_pow₀ (by linarith) hk.ne'
  refine ⟨h1.trans hle, ?_⟩
  apply Nat.le_floor
  have h2 : (k : ℝ) ≤ 2 ^ k := by exact_mod_cast (Nat.lt_two_pow_self).le
  have h3 : (2 : ℝ) ^ k ≤ nrm v ^ k := pow_le_pow_left₀ (by norm_num) hN k
  linarith

lemma finite_pset (x : ℝ) :
    {p : HeightOneSpectrum (𝓞 F) × ℕ | 0 < p.2 ∧ nrm p.1 ^ p.2 ≤ x}.Finite := by
  refine ((finite_nrm_le (F := F) x).prod (Set.finite_Iic ⌊x⌋₊)).subset ?_
  rintro ⟨v, k⟩ ⟨hk, hle⟩
  exact pset_bounds hk hle

lemma summable_log_div_sq :
    Summable (fun v : HeightOneSpectrum (𝓞 F) => Real.log (nrm v) * ((nrm v)⁻¹) ^ 2) := by
  refine Summable.of_nonneg_of_le (fun v => mul_nonneg (log_nrm_pos v).le (sq_nonneg _))
    (fun v => ?_) ((summable_rpow (F := F) (s := 3 / 2) (by norm_num)).mul_left 2)
  have hN := nrm_pos v
  have h1 := Real.log_le_rpow_div hN.le (show (0 : ℝ) < 1 / 2 by norm_num)
  rw [inv_sq_eq_rpow]
  calc Real.log (nrm v) * nrm v ^ (-(2 : ℝ))
      ≤ (nrm v ^ (1 / 2 : ℝ) / (1 / 2)) * nrm v ^ (-(2 : ℝ)) :=
        mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hN.le _)
    _ = 2 * (nrm v ^ (1 / 2 : ℝ) * nrm v ^ (-(2 : ℝ))) := by ring
    _ = 2 * nrm v ^ (-(3 / 2 : ℝ)) := by
        rw [← Real.rpow_add hN]; norm_num

lemma geom_le {r : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ 1 / 2) (K : ℕ) :
    ∑ k ∈ Finset.Icc 2 K, r ^ k ≤ 2 * r ^ 2 := by
  rcases Nat.lt_or_ge K 2 with hK | hK
  · rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]; positivity
  · have hr1 : r - 1 < 0 := by linarith
    have e : Finset.Icc 2 K = Finset.Ico 2 (K + 1) := by
      ext k; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
    rw [e, geom_sum_Ico (by intro h; linarith) (by omega), div_le_iff_of_neg hr1]
    nlinarith [pow_nonneg hr0 (K + 1), mul_nonneg (sq_nonneg r) (by linarith : (0 : ℝ) ≤ 1 - 2 * r)]

lemma exists_bound_A : ∃ C1 : ℝ, ∀ x : ℝ, 1 ≤ x → |A (F := F) x - Real.log x| ≤ C1 := by
  obtain ⟨C, hC⟩ := MertensNumberField.exists_abs_sum_log_absNorm_div_sub_log_le F
  set D := ∑' v : HeightOneSpectrum (𝓞 F), 2 * (Real.log (nrm v) * ((nrm v)⁻¹) ^ 2) with hD
  have hD0 : 0 ≤ D := tsum_nonneg fun v =>
    mul_nonneg (by norm_num) (mul_nonneg (log_nrm_pos v).le (sq_nonneg _))
  refine ⟨C + D, fun x hx => ?_⟩
  have hfin := finite_pset (F := F) x
  have e : (∑ᶠ (p : HeightOneSpectrum (𝓞 F) × ℕ)
          (_ : 0 < p.2 ∧ (Ideal.absNorm p.1.asIdeal : ℝ) ^ p.2 ≤ x),
          Real.log (Ideal.absNorm p.1.asIdeal : ℝ) / (Ideal.absNorm p.1.asIdeal : ℝ) ^ p.2) =
      ∑ p ∈ hfin.toFinset, fvm p := finsum_mem_eq_finite_toFinset_sum (fvm (F := F)) hfin
  have h1 := hC x hx
  rw [e] at h1
  have hsplit := Finset.sum_filter_add_sum_filter_not hfin.toFinset (fun p => p.2 = 1)
    (fvm (F := F))
  have hfirst : ∑ p ∈ hfin.toFinset.filter (fun p => p.2 = 1), fvm p = A (F := F) x := by
    unfold A
    refine Finset.sum_nbij' (fun p => p.1) (fun v => (v, 1)) ?_ ?_ ?_ ?_ ?_
    · intro p hp
      rw [Finset.mem_filter, Set.Finite.mem_toFinset] at hp
      rw [Set.Finite.mem_toFinset]
      obtain ⟨⟨hk, hle⟩, h1⟩ := hp
      exact (pset_bounds hk hle).1
    · intro v hv
      rw [Set.Finite.mem_toFinset] at hv
      rw [Finset.mem_filter, Set.Finite.mem_toFinset]
      refine ⟨⟨Nat.one_pos, ?_⟩, rfl⟩
      show nrm v ^ 1 ≤ x
      rw [pow_one]; exact hv
    · intro p hp
      rw [Finset.mem_filter] at hp
      exact Prod.ext rfl hp.2.symm
    · intro v _; rfl
    · intro p hp
      rw [Finset.mem_filter] at hp
      unfold fvm c; rw [hp.2, pow_one]
  have hrest_nn : 0 ≤ ∑ p ∈ hfin.toFinset.filter (fun p => ¬ p.2 = 1), fvm p :=
    Finset.sum_nonneg fun p _ => fvm_nonneg p
  have hrest_le : ∑ p ∈ hfin.toFinset.filter (fun p => ¬ p.2 = 1), fvm p ≤ D := by
    calc ∑ p ∈ hfin.toFinset.filter (fun p => ¬ p.2 = 1), fvm p
        ≤ ∑ p ∈ (finite_nrm_le (F := F) x).toFinset ×ˢ Finset.Icc 2 ⌊x⌋₊, fvm p := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun p _ _ => fvm_nonneg p)
          intro p hp
          rw [Finset.mem_filter, Set.Finite.mem_toFinset] at hp
          obtain ⟨⟨hk, hle⟩, hne⟩ := hp
          have hb := pset_bounds hk hle
          rw [Finset.mem_product, Set.Finite.mem_toFinset, Finset.mem_Icc]
          exact ⟨hb.1, by omega, hb.2⟩
      _ = ∑ v ∈ (finite_nrm_le (F := F) x).toFinset, ∑ k ∈ Finset.Icc 2 ⌊x⌋₊, fvm (v, k) :=
          Finset.sum_product _ _ _
      _ ≤ ∑ v ∈ (finite_nrm_le (F := F) x).toFinset,
            2 * (Real.log (nrm v) * ((nrm v)⁻¹) ^ 2) := by
          refine Finset.sum_le_sum fun v _ => ?_
          have hfv : ∀ k, fvm (F := F) (v, k) = Real.log (nrm v) * ((nrm v)⁻¹) ^ k := fun k => by
            unfold fvm; rw [div_eq_mul_inv, inv_pow]
          simp_rw [hfv, ← Finset.mul_sum]
          have hg := geom_le (inv_nonneg.mpr (nrm_pos v).le) (inv_le_half v) ⌊x⌋₊
          have hl := (log_nrm_pos v).le
          nlinarith
      _ ≤ D := Summable.sum_le_tsum _ (fun v _ =>
            mul_nonneg (by norm_num) (mul_nonneg (log_nrm_pos v).le (sq_nonneg _)))
            (summable_log_div_sq.mul_left 2)
  rw [hfirst] at hsplit
  rw [abs_le] at h1 ⊢
  constructor <;> linarith [h1.1, h1.2]

lemma Alt_mono : Monotone (Alt (F := F)) := by
  intro t t' htt'
  unfold Alt
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun v _ _ => c_nonneg v)
  intro v hv
  rw [Set.Finite.mem_toFinset] at hv ⊢
  exact lt_of_lt_of_le hv htt'

lemma exists_bound_Alt :
    ∃ C2 : ℝ, 0 ≤ C2 ∧ ∀ t : ℝ, 2 ≤ t → |Alt (F := F) t - Real.log t| ≤ C2 := by
  obtain ⟨C1, hC1⟩ := exists_bound_A (F := F)
  refine ⟨|C1| + Real.log 2, add_nonneg (abs_nonneg _) (Real.log_nonneg (by norm_num)),
    fun t ht => ?_⟩
  have hup : Alt (F := F) t ≤ A (F := F) t := by
    unfold Alt A
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun v _ _ => c_nonneg v)
    intro v hv
    rw [Set.Finite.mem_toFinset] at hv ⊢
    exact le_of_lt (show nrm v < t from hv)
  have hlow : A (F := F) (t - 1) ≤ Alt (F := F) t := by
    unfold Alt A
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun v _ _ => c_nonneg v)
    intro v hv
    rw [Set.Finite.mem_toFinset] at hv ⊢
    have hv' : nrm v ≤ t - 1 := hv
    show nrm v < t
    linarith
  have h1 := hC1 t (by linarith)
  have h2 := hC1 (t - 1) (by linarith)
  have h3 : Real.log t - Real.log 2 ≤ Real.log (t - 1) := by
    rw [← Real.log_div (by linarith) (by norm_num)]
    exact Real.log_le_log (by linarith) (by linarith)
  have h4 : Real.log (t - 1) ≤ Real.log t := Real.log_le_log (by linarith) (by linarith)
  have := le_abs_self C1
  rw [abs_le] at h1 h2 ⊢
  have := Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num)
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

/-- `w t = 1 / (t log² t)`. -/
noncomputable def w (t : ℝ) : ℝ := t⁻¹ / Real.log t ^ 2

lemma hasDerivAt_neg_inv_log {t : ℝ} (ht : 1 < t) :
    HasDerivAt (fun t => -(Real.log t)⁻¹) (w t) t := by
  have h1 : HasDerivAt Real.log t⁻¹ t := Real.hasDerivAt_log (by linarith)
  have h2 := (h1.inv (Real.log_pos ht).ne').neg
  have e : w t = -(-t⁻¹ / Real.log t ^ 2) := by unfold w; ring
  rw [e]; exact h2

lemma hasDerivAt_loglog {t : ℝ} (ht : 1 < t) :
    HasDerivAt (fun t => Real.log (Real.log t)) (t⁻¹ / Real.log t) t :=
  (Real.hasDerivAt_log (by linarith)).log (Real.log_pos ht).ne'

lemma continuousOn_w {a b : ℝ} (ha : 1 < a) : ContinuousOn w (Set.Icc a b) := by
  intro t ht
  have ht1 : 1 < t := lt_of_lt_of_le ha ht.1
  have hl : Real.log t ≠ 0 := (Real.log_pos ht1).ne'
  exact ((continuousAt_inv₀ (by linarith : t ≠ 0)).div
    ((Real.continuousAt_log (by linarith : t ≠ 0)).pow 2) (pow_ne_zero 2 hl)).continuousWithinAt

lemma continuousOn_w1 {a b : ℝ} (ha : 1 < a) :
    ContinuousOn (fun t : ℝ => t⁻¹ / Real.log t) (Set.Icc a b) := by
  intro t ht
  have ht1 : 1 < t := lt_of_lt_of_le ha ht.1
  have hl : Real.log t ≠ 0 := (Real.log_pos ht1).ne'
  exact ((continuousAt_inv₀ (by linarith : t ≠ 0)).div
    (Real.continuousAt_log (by linarith : t ≠ 0)) hl).continuousWithinAt

open MeasureTheory in
lemma integral_w {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    ∫ t in Set.Ioc a b, w t = (Real.log a)⁻¹ - (Real.log b)⁻¹ := by
  rw [← intervalIntegral.integral_of_le hab,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t => -(Real.log t)⁻¹)
      (fun t ht => hasDerivAt_neg_inv_log (lt_of_lt_of_le ha
        (by rw [Set.uIcc_of_le hab] at ht; exact ht.1)))
      (ContinuousOn.intervalIntegrable (by rw [Set.uIcc_of_le hab]; exact continuousOn_w ha))]
  ring

open MeasureTheory in
lemma integral_w1 {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    ∫ t in Set.Ioc a b, t⁻¹ / Real.log t = Real.log (Real.log b) - Real.log (Real.log a) := by
  rw [← intervalIntegral.integral_of_le hab,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t => Real.log (Real.log t))
      (fun t ht => hasDerivAt_loglog (lt_of_lt_of_le ha
        (by rw [Set.uIcc_of_le hab] at ht; exact ht.1)))
      (ContinuousOn.intervalIntegrable (by rw [Set.uIcc_of_le hab]; exact continuousOn_w1 ha))]

open MeasureTheory in
lemma integrableOn_w : IntegrableOn w (Set.Ioi 2) := by
  refine integrableOn_Ioi_deriv_of_nonneg' (g := fun t => -(Real.log t)⁻¹) (l := 0)
    (fun t ht => hasDerivAt_neg_inv_log (lt_of_lt_of_le (by norm_num) ht)) (fun t ht => ?_) ?_
  · have ht' : (2 : ℝ) < t := ht
    unfold w; exact div_nonneg (inv_nonneg.mpr (by linarith)) (sq_nonneg _)
  · have := (tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop).neg
    simpa using this

lemma measurable_w : Measurable w := by
  unfold w; fun_prop

open MeasureTheory in
lemma Plt_identity {x : ℝ} (hx : 2 ≤ x) :
    Plt (F := F) x = Alt (F := F) x / Real.log x + ∫ t in Set.Ioc 2 x, Alt (F := F) t * w t := by
  have hint : ∫ t in Set.Ioc 2 x, Alt (F := F) t * w t =
      ∑ v ∈ (finite_nrm_lt (F := F) x).toFinset,
        c v * ((Real.log (nrm v))⁻¹ - (Real.log x)⁻¹) := by
    have hcongr : Set.EqOn (fun t => Alt (F := F) t * w t)
        (fun t => ∑ v ∈ (finite_nrm_lt (F := F) x).toFinset,
          c v * Set.indicator (Set.Ioi (nrm v)) w t) (Set.Ioc 2 x) := by
      intro t ht
      simp only
      unfold Alt
      rw [Finset.sum_mul]
      simp_rw [Set.indicator_apply, mul_ite, mul_zero]
      rw [← Finset.sum_filter]
      refine Finset.sum_congr ?_ (fun _ _ => rfl)
      ext v
      rw [Finset.mem_filter, Set.Finite.mem_toFinset, Set.Finite.mem_toFinset]
      constructor
      · intro h; exact ⟨lt_of_lt_of_le (show nrm v < t from h) ht.2, h⟩
      · intro h; exact h.2
    rw [setIntegral_congr_fun measurableSet_Ioc hcongr]
    rw [integral_finsetSum _ (fun v _ =>
      ((integrableOn_w.mono_set Set.Ioc_subset_Ioi_self).indicator measurableSet_Ioi).const_mul
        (c v))]
    refine Finset.sum_congr rfl fun v hv => ?_
    rw [Set.Finite.mem_toFinset] at hv
    have hv' : nrm v < x := hv
    rw [integral_const_mul, setIntegral_indicator measurableSet_Ioi, Set.Ioc_inter_Ioi,
      max_eq_right (two_le_nrm v), integral_w (by linarith [two_le_nrm v]) hv'.le]
  rw [hint]
  unfold Plt Alt
  rw [div_eq_mul_inv, Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun v _ => ?_
  have h1 := (log_nrm_pos v).ne'
  have h2 := (nrm_pos v).ne'
  have h3 : Real.log x ≠ 0 := (Real.log_pos (by linarith)).ne'
  unfold c
  field_simp
  ring

open MeasureTheory in
lemma exists_tendsto_Plt :
    ∃ B, Tendsto (fun x => Plt (F := F) x - Real.log (Real.log x)) atTop (𝓝 B) := by
  obtain ⟨C2, hC2, hC2b⟩ := exists_bound_Alt (F := F)
  set R : ℝ → ℝ := fun t => Alt (F := F) t - Real.log t with hR
  have hRm : Measurable R := (Alt_mono (F := F)).measurable.sub Real.measurable_log
  have hRw : IntegrableOn (fun t => R t * w t) (Set.Ioi 2) := by
    refine Integrable.mono' (integrableOn_w.const_mul C2)
      (hRm.mul measurable_w).aestronglyMeasurable ?_
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine Filter.Eventually.of_forall fun t ht => ?_
    have ht' : (2 : ℝ) < t := ht
    have hw : 0 ≤ w t := by
      unfold w; exact div_nonneg (inv_nonneg.mpr (by linarith)) (sq_nonneg _)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hw]
    exact mul_le_mul_of_nonneg_right (hC2b t ht'.le) hw
  refine ⟨1 - Real.log (Real.log 2) + ∫ t in Set.Ioi 2, R t * w t, ?_⟩
  have hlim1 : Tendsto (fun x => Alt (F := F) x / Real.log x) atTop (𝓝 1) := by
    have h0 : Tendsto (fun x => R x / Real.log x) atTop (𝓝 0) := by
      refine squeeze_zero_norm' ?_ ((tendsto_const_nhds (x := C2)).div_atTop Real.tendsto_log_atTop)
      filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
      have hl : 0 < Real.log x := Real.log_pos (by linarith)
      rw [Real.norm_eq_abs, abs_div, abs_of_pos hl]
      exact div_le_div_of_nonneg_right (hC2b x hx) hl.le
    have := h0.const_add 1
    rw [add_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
    have hl : Real.log x ≠ 0 := (Real.log_pos (by linarith)).ne'
    simp only [hR]
    field_simp
    ring
  have hlim2 : Tendsto (fun x => ∫ t in (2 : ℝ)..x, R t * w t) atTop
      (𝓝 (∫ t in Set.Ioi 2, R t * w t)) :=
    intervalIntegral_tendsto_integral_Ioi 2 hRw tendsto_id
  have hlim := (hlim1.sub_const (Real.log (Real.log 2))).add hlim2
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
  rw [intervalIntegral.integral_of_le hx, Plt_identity hx]
  have hsplit : ∫ t in Set.Ioc 2 x, Alt (F := F) t * w t =
      (Real.log (Real.log x) - Real.log (Real.log 2)) + ∫ t in Set.Ioc 2 x, R t * w t := by
    rw [← integral_w1 (by norm_num) hx, ← integral_add
      ((continuousOn_w1 (b := x) (by norm_num : (1 : ℝ) < 2)).integrableOn_Icc.mono_set
        Set.Ioc_subset_Icc_self)
      (hRw.mono_set Set.Ioc_subset_Ioi_self)]
    refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
    have ht' : (2 : ℝ) < t := ht.1
    have hl : Real.log t ≠ 0 := (Real.log_pos (by linarith)).ne'
    have ht0 : t ≠ 0 := by linarith
    simp only [hR]
    unfold w
    field_simp
    ring
  rw [hsplit]
  ring

lemma exists_tendsto_S :
    ∃ L, Tendsto (fun t => S (F := F) t - Real.log (Real.log t)) atTop (𝓝 L) := by
  obtain ⟨B, hPltB⟩ := exists_tendsto_Plt (F := F)
  -- the difference `S - Plt` converges
  have hsum : Summable (fun v : HeightOneSpectrum (𝓞 F) => a v - (nrm v)⁻¹) := by
    refine Summable.of_nonneg_of_le (fun v => by linarith [inv_le_a v]) (fun v => ?_)
      (summable_inv_sq.mul_left 2)
    have := a_le v; linarith
  have hmono : Monotone (fun x : ℝ => (finite_nrm_lt (F := F) x).toFinset) := by
    intro x y hxy v hv
    rw [Set.Finite.mem_toFinset] at hv ⊢
    exact lt_of_lt_of_le hv hxy
  have hT : Tendsto (fun x : ℝ => (finite_nrm_lt (F := F) x).toFinset) atTop atTop :=
    tendsto_atTop_finset_of_monotone hmono fun v => ⟨nrm v + 1, by
      rw [Set.Finite.mem_toFinset]; show nrm v < nrm v + 1; linarith⟩
  have hD : Tendsto (fun x : ℝ => ∑ v ∈ (finite_nrm_lt (F := F) x).toFinset, (a v - (nrm v)⁻¹))
      atTop (𝓝 (∑' v : HeightOneSpectrum (𝓞 F), (a v - (nrm v)⁻¹))) :=
    (show Tendsto (fun s : Finset (HeightOneSpectrum (𝓞 F)) => ∑ v ∈ s, (a v - (nrm v)⁻¹))
      atTop (𝓝 _) from hsum.hasSum).comp hT
  refine ⟨(∑' v : HeightOneSpectrum (𝓞 F), (a v - (nrm v)⁻¹)) + B, ?_⟩
  refine (hD.add hPltB).congr fun x => ?_
  simp only [Finset.sum_sub_distrib]
  unfold S Plt; ring

end Sol_MertensNumberField_tendsto_log_mul_prod_one_sub_inv_absNorm

open Sol_MertensNumberField_tendsto_log_mul_prod_one_sub_inv_absNorm in
theorem solution (F : Type*) [Field F] [NumberField F] :
    Tendsto
      (fun x : ℝ => Real.log x *
        ∏ᶠ (v : HeightOneSpectrum (𝓞 F)) (_ : (Ideal.absNorm v.asIdeal : ℝ) < x),
          (1 - ((Ideal.absNorm v.asIdeal : ℝ))⁻¹))
      atTop (𝓝 (Real.exp (-Real.eulerMascheroniConstant) / dedekindZeta_residue F)) := by
  obtain ⟨L, hL⟩ := exists_tendsto_S (F := F)
  have hLv := key_limit hL
  have hexp : Tendsto (fun x => Real.exp (-(S (F := F) x - Real.log (Real.log x)))) atTop
      (𝓝 (Real.exp (-L))) := (Real.continuous_exp.tendsto _).comp hL.neg
  have hval : Real.exp (-L) = Real.exp (-Real.eulerMascheroniConstant) / dedekindZeta_residue F := by
    rw [hLv, neg_add, Real.exp_add, Real.exp_neg (Real.log _),
      Real.exp_log (dedekindZeta_residue_pos F)]
    ring
  rw [hval] at hexp
  refine hexp.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  rw [Sol_MertensNumberField_tendsto_log_mul_prod_one_sub_inv_absNorm.prod_eq, neg_sub, Real.exp_sub, Real.exp_log (Real.log_pos hx), div_eq_mul_inv,
    ← Real.exp_neg]
