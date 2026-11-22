-- Prove2me | solution 1 for MasulloGRH.finiteLocalZeta_meromorphic_and_residue
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T17:03:30.766062+00:00
-- url     : https://prove2.me/submissions/1b330f34-9053-4541-8211-2dbb736a2f77

import Mathlib
import Definitions.Def_MasulloGRH_SLocalTamagawaMeasures
import Theorems.Thm_MasulloGRH_finiteLocalZeta_integers_of_unramified
import Theorems.Thm_MasulloGRH_finiteLocalMulTamagawa_isHaarMeasure_and_units

open MeasureTheory NumberField IsDedekindDomain

set_option autoImplicit false

namespace Sol_MasulloGRH_finiteLocalZeta_meromorphic_and_residue

open MasulloGRH

variable {F : Type*} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

lemma one_lt_q : (1 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by
  exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v

lemma norm_of_val (x : v.adicCompletion F) (k : ℤ) (h : Valued.v x = WithZero.exp k) :
    ‖x‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ k := by
  rw [NumberField.FinitePlace.norm_def, h,
    WithZeroMulInt.toNNReal_neg_apply _ (WithZero.exp_ne_zero)]
  simp only [NNReal.coe_zpow, NNReal.coe_natCast]
  congr 1

lemma norm_eq_zpow (x : v.adicCompletion F) (hx : x ≠ 0) :
    ∃ k : ℤ, ‖x‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ k := by
  have h0 : Valued.v x ≠ 0 := by simpa using hx
  exact ⟨WithZero.log (Valued.v x), norm_of_val v x _ (WithZero.exp_log h0).symm⟩

lemma norm_le_one_iff (x : v.adicCompletion F) : ‖x‖ ≤ 1 ↔ Valued.v x ≤ 1 := by
  rw [NumberField.FinitePlace.norm_def]
  have := WithZeroMulInt.toNNReal_le_one_iff (m := Valued.v x)
    (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v)
  exact_mod_cast this

lemma norm_eq_one_iff (x : v.adicCompletion F) : ‖x‖ = 1 ↔ Valued.v x = 1 := by
  rw [NumberField.FinitePlace.norm_def]
  have := WithZeroMulInt.toNNReal_eq_one_iff (Valued.v x)
    (NumberField.HeightOneSpectrum.absNorm_ne_zero v)
    (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v).ne'
  exact_mod_cast this

lemma exists_unif : ∃ ϖ : (v.adicCompletion F)ˣ,
    Valued.v (ϖ : v.adicCompletion F) = WithZero.exp (-1 : ℤ) := by
  obtain ⟨x, hx⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective F v (WithZero.exp (-1 : ℤ))
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [map_zero] at hx
    exact WithZero.exp_ne_zero hx.symm
  exact ⟨Units.mk0 x hx0, hx⟩

/-- The shell `{x : ‖x‖ = q^k}` in `F_vˣ`. -/
def shell (k : ℤ) : Set (v.adicCompletion F)ˣ :=
  {x | ‖(x : v.adicCompletion F)‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ k}

lemma measurableSet_shell (k : ℤ) : MeasurableSet (shell v k) := by
  apply IsClosed.measurableSet
  exact isClosed_eq (continuous_norm.comp Units.continuous_val) continuous_const

lemma shell_eq_preimage (ϖ : (v.adicCompletion F)ˣ)
    (hϖ : ‖(ϖ : v.adicCompletion F)‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ (-1 : ℤ)) (k : ℤ) :
    shell v k = (fun y => ϖ ^ k * y) ⁻¹' shell v 0 := by
  have hq : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := zero_lt_one.trans (one_lt_q v)
  ext y
  simp only [shell, Set.mem_preimage, Set.mem_ofPred_eq, Units.val_mul,
    Units.val_zpow_eq_zpow_val, norm_mul, norm_zpow, hϖ, zpow_zero]
  rw [← zpow_mul]
  have hpos : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) ^ ((-1 : ℤ) * k) := zpow_pos hq _
  constructor
  · intro h
    rw [h, ← zpow_add₀ hq.ne']
    simp
  · intro h
    have : ‖(y : v.adicCompletion F)‖ = ((Ideal.absNorm v.asIdeal : ℝ) ^ ((-1 : ℤ) * k))⁻¹ := by
      exact eq_inv_of_mul_eq_one_right h
    rw [this, ← zpow_neg]
    congr 1; ring

lemma measure_shell_lt_top (k : ℤ) : finiteLocalMulTamagawa F v (shell v k) < ⊤ := by
  have hH := finiteLocalMulTamagawa_isHaarMeasure_and_units F v
  have := hH.1
  obtain ⟨ϖ, hϖ⟩ := exists_unif v
  rw [shell_eq_preimage v ϖ (norm_of_val v _ _ hϖ) k, measure_preimage_mul]
  have h0 : shell v 0 = {u : (v.adicCompletion F)ˣ | Valued.v (u : v.adicCompletion F) = 1} := by
    ext u
    simp only [shell, Set.mem_ofPred_eq, zpow_zero]
    exact norm_eq_one_iff v _
  rw [h0, hH.2, ENNReal.inv_lt_top, ENNReal.ofReal_pos]
  apply Real.sqrt_pos.mpr
  exact pow_pos (zero_lt_one.trans (one_lt_q v)) _

lemma cpow_zpow (k : ℤ) (s : ℂ) :
    ((((Ideal.absNorm v.asIdeal : ℝ) ^ k : ℝ)) : ℂ) ^ s =
      Complex.exp (k * (Real.log (Ideal.absNorm v.asIdeal : ℝ) : ℂ) * s) := by
  have hq : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := zero_lt_one.trans (one_lt_q v)
  have hpos : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) ^ k := zpow_pos hq _
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hpos.ne'), ← Complex.ofReal_log hpos.le,
    Real.log_zpow]
  push_cast
  ring_nf

lemma exists_N (f : v.adicCompletion F → ℂ) (hfc : HasCompactSupport f) :
    ∃ N : ℕ, ∀ x, f x ≠ 0 → ‖x‖ ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ N := by
  obtain ⟨R, hR⟩ := hfc.isCompact.exists_bound_of_continuousOn continuous_id.continuousOn
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt R (one_lt_q v)
  refine ⟨N, fun x hx => ?_⟩
  have := hR x (subset_tsupport f (Function.mem_support.mpr hx))
  simp only [id] at this
  linarith

lemma exists_n (f : v.adicCompletion F → ℂ) (hf : IsLocallyConstant f) :
    ∃ n : ℕ, ∀ x, ‖x‖ ≤ ((Ideal.absNorm v.asIdeal : ℝ) ^ n)⁻¹ → f x = f 0 := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp (hf.isOpen_fiber (f 0)) 0 rfl
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε (inv_lt_one_of_one_lt₀ (one_lt_q v))
  refine ⟨n, fun x hx => ?_⟩
  have hx' : x ∈ Metric.ball (0 : v.adicCompletion F) ε := by
    rw [mem_ball_zero_iff]
    rw [inv_pow] at hn
    linarith
  exact hball hx'

/-- The units of valuation `≤ 1`, i.e. `𝒪_vˣ`-orbit of `𝒪_v ∖ {0}`. -/
def ball0 : Set (v.adicCompletion F)ˣ := {x | Valued.v (x : v.adicCompletion F) ≤ 1}

lemma measurableSet_ball0 : MeasurableSet (ball0 v) := by
  have : ball0 v = {x : (v.adicCompletion F)ˣ | ‖(x : v.adicCompletion F)‖ ≤ 1} := by
    ext x
    simp only [ball0, Set.mem_ofPred_eq]
    exact (norm_le_one_iff v _).symm
  rw [this]
  apply IsClosed.measurableSet
  exact isClosed_le (continuous_norm.comp Units.continuous_val) continuous_const

/-- `f - f(0) 1_{𝒪_v}` on `F_vˣ`. -/
noncomputable def hpart (f : v.adicCompletion F → ℂ) (x : (v.adicCompletion F)ˣ) : ℂ :=
  f x - (ball0 v).indicator (fun _ => f 0) x

lemma decomp (f : v.adicCompletion F → ℂ) (n N : ℕ)
    (hN : ∀ x, f x ≠ 0 → ‖x‖ ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ N)
    (hn : ∀ x, ‖x‖ ≤ ((Ideal.absNorm v.asIdeal : ℝ) ^ n)⁻¹ → f x = f 0)
    (s : ℂ) (x : (v.adicCompletion F)ˣ) :
    hpart v f x * ((‖(x : v.adicCompletion F)‖ : ℝ) : ℂ) ^ s =
      ∑ k ∈ Finset.Icc (-(n : ℤ)) N, (shell v k).indicator (fun y => hpart v f y *
        Complex.exp (k * (Real.log (Ideal.absNorm v.asIdeal : ℝ) : ℂ) * s)) x := by
  have hq1 := one_lt_q v
  have hq : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := zero_lt_one.trans hq1
  obtain ⟨k0, hk0⟩ := norm_eq_zpow v (x : v.adicCompletion F) x.ne_zero
  have hmem : ∀ k : ℤ, x ∈ shell v k ↔ k = k0 := by
    intro k
    simp only [shell, Set.mem_ofPred_eq, hk0]
    exact ⟨fun h => (zpow_right_injective₀ hq hq1.ne' h).symm, fun h => h ▸ rfl⟩
  have hind : ∀ k : ℤ, (shell v k).indicator (fun y => hpart v f y *
        Complex.exp (k * (Real.log (Ideal.absNorm v.asIdeal : ℝ) : ℂ) * s)) x =
      if k = k0 then hpart v f x *
        Complex.exp (k * (Real.log (Ideal.absNorm v.asIdeal : ℝ) : ℂ) * s) else 0 := by
    intro k
    by_cases hk : k = k0
    · rw [Set.indicator_of_mem ((hmem k).mpr hk), if_pos hk]
    · rw [Set.indicator_of_notMem (mt (hmem k).mp hk), if_neg hk]
  rw [Finset.sum_congr rfl (fun k _ => hind k), Finset.sum_ite_eq']
  split_ifs with hT
  · rw [hk0, cpow_zpow]
  · have h0 : hpart v f x = 0 := by
      rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hT
      unfold hpart
      rcases hT with hT | hT
      · have hle : ‖(x : v.adicCompletion F)‖ ≤ ((Ideal.absNorm v.asIdeal : ℝ) ^ n)⁻¹ := by
          rw [hk0, ← zpow_natCast, ← zpow_neg]
          exact zpow_le_zpow_right₀ hq1.le hT.le
        have hb : x ∈ ball0 v := by
          show Valued.v (x : v.adicCompletion F) ≤ 1
          rw [← norm_le_one_iff, hk0]
          exact zpow_le_one_of_nonpos₀ hq1.le (by omega)
        rw [Set.indicator_of_mem hb, hn _ hle, sub_self]
      · have hf0 : f x = 0 := by
          by_contra hne
          have h1 := hN _ hne
          rw [hk0, ← zpow_natCast] at h1
          exact absurd h1 (not_le.mpr (zpow_lt_zpow_right₀ hq1 hT))
        have hb : x ∉ ball0 v := by
          show ¬ Valued.v (x : v.adicCompletion F) ≤ 1
          rw [← norm_le_one_iff, hk0, not_le]
          exact one_lt_zpow₀ hq1 (by omega)
        rw [Set.indicator_of_notMem hb, hf0, sub_self]
    rw [h0, zero_mul]

lemma integrableOn_shell (f : v.adicCompletion F → ℂ) (hf : IsLocallyConstant f)
    (hfc : HasCompactSupport f) (k : ℤ) (e : ℂ) :
    IntegrableOn (fun y => hpart v f y * e) (shell v k) (finiteLocalMulTamagawa F v) := by
  obtain ⟨C, hC⟩ := hf.continuous.bounded_above_of_compact_support hfc
  have hmeas : Measurable (fun y : (v.adicCompletion F)ˣ => hpart v f y * e) := by
    unfold hpart
    have h1 : Measurable (fun y : (v.adicCompletion F)ˣ => f (y : v.adicCompletion F)) :=
      (hf.continuous.comp Units.continuous_val).measurable
    have h2 : Measurable ((ball0 v).indicator (fun _ : (v.adicCompletion F)ˣ => f 0)) :=
      measurable_const.indicator (measurableSet_ball0 v)
    exact (h1.sub h2).mul_const e
  refine Measure.integrableOn_of_bounded (measure_shell_lt_top v k).ne
    hmeas.aestronglyMeasurable (M := (C + ‖f 0‖) * ‖e‖) (ae_of_all _ fun y => ?_)
  rw [norm_mul]
  gcongr
  unfold hpart
  calc ‖f (y : v.adicCompletion F) - (ball0 v).indicator (fun _ => f 0) y‖
      ≤ ‖f (y : v.adicCompletion F)‖ + ‖(ball0 v).indicator (fun _ => f 0) y‖ := norm_sub_le _ _
    _ ≤ C + ‖f 0‖ := add_le_add (hC _) (norm_indicator_le_norm_self _ _)

end Sol_MasulloGRH_finiteLocalZeta_meromorphic_and_residue

open Sol_MasulloGRH_finiteLocalZeta_meromorphic_and_residue MasulloGRH

theorem solution
    (F : Type*) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (f : v.adicCompletion F → ℂ) (hf : IsLocallyConstant f) (hfc : HasCompactSupport f) :
    ∃ M : ℂ → ℂ, MeromorphicOn M Set.univ ∧
      (∀ s : ℂ, 0 < s.re →
        Integrable
          (fun x : (v.adicCompletion F)ˣ =>
            f (x : v.adicCompletion F) * ((‖(x : v.adicCompletion F)‖ : ℝ) : ℂ) ^ s)
          (finiteLocalMulTamagawa F v) ∧
        M s = ∫ x : (v.adicCompletion F)ˣ,
          f (x : v.adicCompletion F) * ((‖(x : v.adicCompletion F)‖ : ℝ) : ℂ) ^ s
            ∂(finiteLocalMulTamagawa F v)) ∧
      (∀ s : ℂ, ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s) ≠ 1 → AnalyticAt ℂ M s) ∧
      Filter.Tendsto (fun s : ℂ => s * M s) (nhdsWithin 0 {0}ᶜ)
        (nhds ((((Real.sqrt ((Ideal.absNorm v.asIdeal : ℝ) ^
          multiplicity v.asIdeal (differentIdeal ℤ (𝓞 F))))⁻¹ : ℝ) : ℂ) * f 0 /
            ((Real.log (Ideal.absNorm v.asIdeal : ℝ) : ℝ) : ℂ))) := by
  have hq1 := one_lt_q v
  have hq : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := zero_lt_one.trans hq1
  have hL : 0 < Real.log (Ideal.absNorm v.asIdeal : ℝ) := Real.log_pos hq1
  obtain ⟨N, hN⟩ := exists_N v f hfc
  obtain ⟨n, hn⟩ := exists_n v f hf
  obtain ⟨ϖ, hϖ⟩ := exists_unif v
  have hϖn := norm_of_val v _ _ hϖ
  set L : ℂ := ((Real.log (Ideal.absNorm v.asIdeal : ℝ) : ℝ) : ℂ) with hL_def
  set c0 : ℂ := (((Real.sqrt ((Ideal.absNorm v.asIdeal : ℝ) ^
          multiplicity v.asIdeal (differentIdeal ℤ (𝓞 F))))⁻¹ : ℝ) : ℂ) with hc0_def
  set T : Finset ℤ := Finset.Icc (-(n : ℤ)) N with hT_def
  set μ := finiteLocalMulTamagawa F v with hμ_def
  let b : ℤ → ℂ := fun k => ∫ y in shell v k, hpart v f y ∂μ
  let g : ℂ → ℂ := fun s => 1 - Complex.exp (-(L * s))
  let P : ℂ → ℂ := fun s => ∑ k ∈ T, b k * Complex.exp (k * L * s)
  let M : ℂ → ℂ := fun s => f 0 * (c0 * (g s)⁻¹) + P s
  have hg_diff : Differentiable ℂ g := by fun_prop
  have hP_diff : Differentiable ℂ P := by fun_prop
  have hg_an : ∀ s, AnalyticAt ℂ g s := fun s => hg_diff.analyticAt s
  have hP_an : ∀ s, AnalyticAt ℂ P s := fun s => hP_diff.analyticAt s
  refine ⟨M, ?_, ?_, ?_, ?_⟩
  · intro s _
    exact (analyticAt_const.meromorphicAt.mul
      (analyticAt_const.meromorphicAt.mul (hg_an s).meromorphicAt.inv)).add (hP_an s).meromorphicAt
  · intro s hs
    let c : (v.adicCompletion F)ˣ → ℂ := fun x => ((‖(x : v.adicCompletion F)‖ : ℝ) : ℂ) ^ s
    have hmul : ∀ x y, c (x * y) = c x * c y := by
      intro x y
      simp only [c, Units.val_mul, norm_mul]
      push_cast
      exact Complex.mul_cpow_ofReal_nonneg (norm_nonneg _) (norm_nonneg _) s
    have hunr : ∀ u : (v.adicCompletion F)ˣ, Valued.v (u : v.adicCompletion F) = 1 → c u = 1 := by
      intro u hu
      simp only [c]
      rw [(norm_eq_one_iff v _).mpr hu]
      simp
    have hcϖ : c ϖ = Complex.exp (-(L * s)) := by
      simp only [c]
      rw [hϖn, cpow_zpow]
      congr 1
      simp only [Int.cast_neg, Int.cast_one, L]
      ring
    have hσ : ‖c ϖ‖ < 1 := by
      simp only [c]
      rw [Complex.norm_cpow_eq_rpow_re_of_pos (norm_pos_iff.mpr ϖ.ne_zero), hϖn]
      exact Real.rpow_lt_one (zpow_nonneg hq.le _) (zpow_lt_one_of_neg₀ hq1 (by norm_num)) hs
    obtain ⟨hI, hval⟩ := finiteLocalZeta_integers_of_unramified F v c hmul hunr ϖ hϖ hσ
    have hsplit : (fun x : (v.adicCompletion F)ˣ =>
        f (x : v.adicCompletion F) * ((‖(x : v.adicCompletion F)‖ : ℝ) : ℂ) ^ s) =
        fun x => (ball0 v).indicator (fun y => f 0 * c y) x +
          ∑ k ∈ T, (shell v k).indicator (fun y => hpart v f y *
            Complex.exp (k * L * s)) x := by
      funext x
      rw [← decomp v f n N hN hn s x]
      simp only [hpart, c]
      by_cases hx : x ∈ ball0 v
      · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]; ring
      · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]; ring
    have hint1 : Integrable ((ball0 v).indicator (fun y => f 0 * c y)) μ :=
      (show IntegrableOn (fun y => f 0 * c y) (ball0 v) μ from
        hI.const_mul (f 0)).integrable_indicator (measurableSet_ball0 v)
    have hint2 : ∀ k ∈ T, Integrable ((shell v k).indicator (fun y => hpart v f y *
        Complex.exp (k * L * s))) μ := fun k _ =>
      (integrableOn_shell v f hf hfc k _).integrable_indicator (measurableSet_shell v k)
    rw [hsplit]
    refine ⟨hint1.add (integrable_finsetSum T hint2), ?_⟩
    rw [integral_add hint1 (integrable_finsetSum T hint2), integral_finsetSum T hint2,
      integral_indicator (measurableSet_ball0 v), integral_const_mul]
    have hval' : ∫ x in ball0 v, c x ∂μ = c0 * (1 - c ϖ)⁻¹ := hval
    rw [hval', hcϖ]
    simp only [M, P, g]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    rw [integral_indicator (measurableSet_shell v k), integral_mul_const]
  · intro s hs
    have hne : g s ≠ 0 := by
      simp only [g]
      intro h
      apply hs
      have hq0 : ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ≠ 0 := by
        exact_mod_cast (Nat.cast_pos.mp hq).ne'
      rw [Complex.cpow_def_of_ne_zero hq0, ← Complex.natCast_log]
      have h' := sub_eq_zero.mp h
      rw [show ((Real.log (Ideal.absNorm v.asIdeal : ℝ) : ℝ) : ℂ) * -s = -(L * s) by
        simp only [L]; ring]
      exact h'.symm
    exact (analyticAt_const.mul (analyticAt_const.mul ((hg_an s).inv hne))).add (hP_an s)
  · have hL0 : L ≠ 0 := by
      simp only [L]
      exact_mod_cast hL.ne'
    have hderiv : HasDerivAt g L 0 := by
      have h2 := (((hasDerivAt_id (0 : ℂ)).const_mul L).neg.cexp).const_sub 1
      have h3 : HasDerivAt g (-(Complex.exp (-(L * id 0)) * -(L * 1))) 0 := h2
      refine h3.congr_deriv ?_
      simp
    have h1 : Filter.Tendsto (fun t => t⁻¹ * g t) (nhdsWithin 0 {0}ᶜ) (nhds L) := by
      have := hasDerivAt_iff_tendsto_slope_zero.mp hderiv
      have hg0 : g 0 = 0 := by simp [g]
      refine this.congr (fun t => ?_)
      rw [hg0, sub_zero, zero_add, smul_eq_mul]
    have h2 : Filter.Tendsto (fun t => t * (g t)⁻¹) (nhdsWithin 0 {0}ᶜ) (nhds L⁻¹) := by
      refine (h1.inv₀ hL0).congr (fun t => ?_)
      rw [mul_inv, inv_inv]
    have h3 : Filter.Tendsto (fun t => t * P t) (nhdsWithin 0 {0}ᶜ) (nhds (0 * P 0)) :=
      ((continuous_id.mul hP_diff.continuous).tendsto 0).mono_left nhdsWithin_le_nhds
    have h4 := (h2.const_mul (f 0 * c0)).add h3
    have h5 : (fun s => s * M s) = fun t => f 0 * c0 * (t * (g t)⁻¹) + t * P t := by
      funext t
      simp only [M]
      ring
    have h6 : c0 * f 0 / L = f 0 * c0 * L⁻¹ + 0 * P 0 := by ring
    rw [h5, h6]
    exact h4
