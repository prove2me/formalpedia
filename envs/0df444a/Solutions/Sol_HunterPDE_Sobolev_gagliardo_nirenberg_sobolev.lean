-- Prove2me | solution 1 for HunterPDE.Sobolev.gagliardo_nirenberg_sobolev
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T05:01:47.549987+00:00
-- url     : https://prove2.me/submissions/a7f5ca20-e1fa-4030-944a-dd55afe7c692

import Mathlib
import Definitions.Def_HunterPDE_Sobolev_SobolevConjugate

section GNSAux

open scoped ENNReal NNReal
open Set Function Finset MeasureTheory Measure Filter Topology

namespace GNS


/-- `f b = -∫_{(b,∞)} f'` for a `C¹` function with compact support. -/
lemma integral_Ioi_deriv_eq {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (h2f : HasCompactSupport f) (b : ℝ) :
    ∫ x in Ioi b, deriv f x = - f b := by
  have hder : ∀ x ∈ Ioi b, HasDerivAt f (deriv f x) x := fun x _ =>
    (hf.differentiable one_ne_zero x).hasDerivAt
  have hint : IntegrableOn (deriv f) (Ioi b) :=
    (hf.continuous_deriv le_rfl |>.integrable_of_hasCompactSupport h2f.deriv).integrableOn
  have htop : Tendsto f atTop (𝓝 0) := by
    rw [hasCompactSupport_iff_eventuallyEq, Filter.coclosedCompact_eq_cocompact] at h2f
    exact h2f.filter_mono _root_.atTop_le_cocompact |>.tendsto
  have := integral_Ioi_of_hasDerivAt_of_tendsto hf.continuous.continuousWithinAt hder hint htop
  rw [this]; ring

lemma enorm_le_lintegral_Ioi_deriv {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (h2f : HasCompactSupport f)
    (b : ℝ) : ‖f b‖ₑ ≤ ∫⁻ y in Ioi b, ‖deriv f y‖ₑ := by
  have h := integral_Ioi_deriv_eq hf h2f b
  calc ‖f b‖ₑ = ‖∫ x in Ioi b, deriv f x‖ₑ := by rw [h, enorm_neg]
    _ ≤ ∫⁻ x in Ioi b, ‖deriv f x‖ₑ := enorm_integral_le_lintegral_enorm _

lemma two_mul_enorm_le_lintegral_deriv {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (h2f : HasCompactSupport f) (b : ℝ) : 2 * ‖f b‖ₑ ≤ ∫⁻ y, ‖deriv f y‖ₑ := by
  have h1 := HasCompactSupport.enorm_le_lintegral_Ici_deriv hf h2f b
  have h2 := enorm_le_lintegral_Ioi_deriv hf h2f b
  have h3 : ∫⁻ y, ‖deriv f y‖ₑ = (∫⁻ y in Iic b, ‖deriv f y‖ₑ) + ∫⁻ y in Ioi b, ‖deriv f y‖ₑ := by
    rw [← lintegral_union measurableSet_Ioi (Set.disjoint_left.2 fun x hx hx' =>
      absurd (Set.mem_Iic.1 hx) (not_le.2 (Set.mem_Ioi.1 hx'))), Set.Iic_union_Ioi, Measure.restrict_univ]
  rw [h3, two_mul]
  exact add_le_add h1 h2


local prefix:max "#" => Fintype.card

/-- The Gagliardo grid-lines estimate with the sharp factor `1/2` and an arbitrary dominating
function `F` of the partial derivatives. -/
theorem lintegral_pow_le_half {ι : Type*} [Fintype ι] [DecidableEq ι] {q : ℝ} (hq : Real.HolderConjugate #ι q)
    {u : (ι → ℝ) → ℝ} (hu : ContDiff ℝ 1 u) (h2u : HasCompactSupport u)
    {F : (ι → ℝ) → ℝ≥0∞} (hF : Measurable F)
    (hdF : ∀ x i t, ‖deriv (u ∘ update x i) t‖ₑ ≤ F (update x i t)) :
    ∫⁻ x, ‖u x‖ₑ ^ q ≤ (ENNReal.ofReal (1 / 2) * ∫⁻ x, F x) ^ q := by
  have h1 : (1 : ℝ) ≤ #ι - 1 := by
    have hι : (2 : ℝ) ≤ #ι := by exact_mod_cast hq.lt
    linarith
  set F' : (ι → ℝ) → ℝ≥0∞ := fun x => ENNReal.ofReal (1 / 2) * F x with hF'
  have hF'm : Measurable F' := hF.const_mul _
  have hpt : ∀ x i, ‖u x‖ₑ ≤ ∫⁻ xᵢ, F' (update x i xᵢ) := by
    intro x i
    have hC1 : ContDiff ℝ 1 (u ∘ update x i) := hu.comp (by convert! contDiff_update 1 x i)
    have hcs : HasCompactSupport (u ∘ update x i) :=
      h2u.comp_isClosedEmbedding (isClosedEmbedding_update x i)
    have h2 := two_mul_enorm_le_lintegral_deriv hC1 hcs (x i)
    have h3 : (u ∘ update x i) (x i) = u x := by simp
    rw [h3] at h2
    have h4 : ∫⁻ t, ‖deriv (u ∘ update x i) t‖ₑ ≤ ∫⁻ t, F (update x i t) :=
      lintegral_mono fun t => hdF x i t
    have h5 : ∫⁻ xᵢ, F' (update x i xᵢ) = ENNReal.ofReal (1 / 2) * ∫⁻ t, F (update x i t) := by
      simp only [hF']
      rw [lintegral_const_mul]
      exact hF.comp (measurable_update x)
    rw [h5]
    calc ‖u x‖ₑ = ENNReal.ofReal (1 / 2) * (2 * ‖u x‖ₑ) := by
          rw [← mul_assoc]
          have : ENNReal.ofReal (1 / 2) * 2 = 1 := by
            rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num)]
            norm_num
          rw [this, one_mul]
      _ ≤ ENNReal.ofReal (1 / 2) * ∫⁻ t, F (update x i t) :=
          by gcongr; exact h2.trans h4
  calc ∫⁻ x, ‖u x‖ₑ ^ q
      = ∫⁻ x, (‖u x‖ₑ ^ (1 / (#ι - 1 : ℝ))) ^ (#ι : ℝ) := by
        congr! 2 with x
        rw [← ENNReal.rpow_mul, hq.conjugate_eq]
        field_simp
    _ = ∫⁻ x, ∏ _i : ι, ‖u x‖ₑ ^ (1 / (#ι - 1 : ℝ)) := by
        congr! 2 with x
        simp_rw [prod_const]
        norm_cast
    _ ≤ ∫⁻ x, ∏ i, (∫⁻ xᵢ, F' (update x i xᵢ)) ^ ((1 : ℝ) / (#ι - 1 : ℝ)) := by
        gcongr with x i
        exact hpt x i
    _ ≤ (∫⁻ x, F' x) ^ q := by
        apply lintegral_prod_lintegral_pow_le _ hq
        exact hF'm
    _ = (ENNReal.ofReal (1 / 2) * ∫⁻ x, F x) ^ q := by
        simp only [hF']
        rw [lintegral_const_mul _ hF]


lemma enorm_gradient_eq {n : ℕ} (u : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    ‖gradient u x‖ = ‖fderiv ℝ u x‖ := by
  unfold gradient
  exact LinearIsometryEquiv.norm_map _ _

lemma continuous_gradient {n : ℕ} {u : EuclideanSpace ℝ (Fin n) → ℝ} (hu : ContDiff ℝ 1 u) :
    Continuous (gradient u) := by
  unfold gradient
  exact (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm.continuous.comp
    (hu.continuous_fderiv one_ne_zero)

/-- Gagliardo's inequality with the sharp factor `1/2` on `ℝⁿ = EuclideanSpace ℝ (Fin n)`. -/
theorem lintegral_pow_le_half_euclid {n : ℕ} {q : ℝ} (hq : Real.HolderConjugate n q)
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hu : ContDiff ℝ 1 u) (h2u : HasCompactSupport u) :
    ∫⁻ x, ‖u x‖ₑ ^ q ≤ (ENNReal.ofReal (1 / 2) * ∫⁻ x, ‖gradient u x‖ₑ) ^ q := by
  classical
  have hcard : #(Fin n) = n := Fintype.card_fin n
  have hq' : Real.HolderConjugate #(Fin n) q := by rwa [hcard]
  set v : (Fin n → ℝ) → ℝ := fun y => u (WithLp.toLp 2 y) with hv
  have hvC : ContDiff ℝ 1 v := hu.comp (PiLp.contDiff_toLp (p := 2) (E := fun _ : Fin n => ℝ))
  have hvc : HasCompactSupport v :=
    h2u.comp_homeomorph (PiLp.homeomorph 2 (fun _ : Fin n => ℝ)).symm
  set F : (Fin n → ℝ) → ℝ≥0∞ := fun y => ‖gradient u (WithLp.toLp 2 y)‖ₑ with hF
  have hFm : Measurable F :=
    ((continuous_gradient hu).comp (PiLp.continuous_toLp 2 _)).enorm.measurable
  have hdF : ∀ y i t, ‖deriv (v ∘ update y i) t‖ₑ ≤ F (update y i t) := by
    intro y i t
    have hc : HasDerivAt (fun t : ℝ => (WithLp.toLp 2 (update y i t) : EuclideanSpace ℝ (Fin n)))
        (EuclideanSpace.single i (1 : ℝ)) t := by
      have := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).symm.hasFDerivAt.comp_hasDerivAt
        t (hasDerivAt_update y i t)
      exact this
    have hd := (hu.differentiable one_ne_zero (WithLp.toLp 2 (update y i t))).hasFDerivAt.comp_hasDerivAt t hc
    have hder : deriv (v ∘ update y i) t = fderiv ℝ u (WithLp.toLp 2 (update y i t))
        (EuclideanSpace.single i 1) := by
      exact hd.deriv
    rw [hder]
    simp only [hF]
    rw [enorm_eq_nnnorm, enorm_eq_nnnorm]
    have hle : ‖fderiv ℝ u (WithLp.toLp 2 (update y i t)) (EuclideanSpace.single i (1 : ℝ))‖ ≤
        ‖gradient u (WithLp.toLp 2 (update y i t))‖ := by
      rw [enorm_gradient_eq]
      calc _ ≤ ‖fderiv ℝ u (WithLp.toLp 2 (update y i t))‖ * ‖EuclideanSpace.single i (1 : ℝ)‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ = _ := by rw [PiLp.norm_single]; simp
    exact_mod_cast hle
  have hmain := lintegral_pow_le_half hq' hvC hvc hFm hdF
  have hm1 : ∫⁻ x : EuclideanSpace ℝ (Fin n), ‖u x‖ₑ ^ q = ∫⁻ y : Fin n → ℝ, ‖v y‖ₑ ^ q := by
    have hmeas : Measurable (fun x : EuclideanSpace ℝ (Fin n) => ‖u x‖ₑ ^ q) :=
      (hu.continuous.enorm.measurable).pow_const _
    have := (PiLp.volume_preserving_toLp (Fin n)).lintegral_comp hmeas
    exact this.symm
  have hm2 : ∫⁻ x : EuclideanSpace ℝ (Fin n), ‖gradient u x‖ₑ = ∫⁻ y : Fin n → ℝ, F y := by
    have hmeas : Measurable (fun x : EuclideanSpace ℝ (Fin n) => ‖gradient u x‖ₑ) :=
      (continuous_gradient hu).enorm.measurable
    have := (PiLp.volume_preserving_toLp (Fin n)).lintegral_comp hmeas
    exact this.symm
  rw [hm1, hm2]
  exact hmain



lemma cancel {A K : ℝ≥0∞} {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (hA : A ≠ ⊤)
    (h : A ≤ K * A ^ γ) : A ^ (1 - γ) ≤ K := by
  rcases eq_or_ne A 0 with rfl | h0
  · rw [ENNReal.zero_rpow_of_pos (by linarith)]; exact bot_le
  · have h1 : A ^ γ ≠ 0 := (ENNReal.rpow_pos (pos_iff_ne_zero.2 h0) hA).ne'
    have h2 : A ^ γ ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg hγ0 hA
    have h3 : A ^ (1 - γ) * A ^ γ = A := by
      rw [← ENNReal.rpow_add _ _ h0 hA]; simp
    refine (ENNReal.mul_le_mul_iff_left h1 h2).1 ?_
    calc A ^ (1 - γ) * A ^ γ = A := h3
      _ ≤ K * A ^ γ := h

lemma finite_lintegral {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : Continuous f)
    (hfc : HasCompactSupport f) {r : ℝ} (hr : 0 < r) : ∫⁻ x, ‖f x‖ₑ ^ r ≠ ⊤ := by
  have hmem : MemLp f (ENNReal.ofReal r) volume := hf.memLp_of_hasCompactSupport hfc
  have h1 := hmem.eLpNorm_lt_top
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simpa using hr) ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hr.le] at h1
  intro htop
  rw [htop, ENNReal.top_rpow_of_pos (by positivity)] at h1
  exact lt_irrefl _ h1


/-- `v = |f|^s` is `C¹` with compact support, with the expected gradient bound. -/
lemma rpow_aux {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiff ℝ 1 f)
    (hfc : HasCompactSupport f) {s : ℝ} (hs : 1 < s) :
    ContDiff ℝ 1 (fun x => ‖f x‖ ^ s) ∧ HasCompactSupport (fun x => ‖f x‖ ^ s) ∧
      ∀ x, ‖gradient (fun x => ‖f x‖ ^ s) x‖ₑ ≤
        ENNReal.ofReal s * ‖f x‖ₑ ^ (s - 1) * ‖gradient f x‖ₑ := by
  refine ⟨(contDiff_norm_rpow (E := ℝ) hs).comp hf, ?_, fun x => ?_⟩
  · exact hfc.comp_left (g := fun t : ℝ => ‖t‖ ^ s) (by simp [Real.zero_rpow (by linarith : s ≠ 0)])
  · have h1 := norm_fderiv_norm_rpow_le (E := ℝ) (hf.differentiable one_ne_zero) (x := x) hs
    have e1 : ‖gradient (fun x => ‖f x‖ ^ s) x‖ₑ =
        ENNReal.ofReal ‖fderiv ℝ (fun x => ‖f x‖ ^ s) x‖ := by
      rw [← enorm_gradient_eq]; exact (ofReal_norm _).symm
    have e2 : ‖gradient f x‖ₑ = ENNReal.ofReal ‖fderiv ℝ f x‖ := by
      rw [← enorm_gradient_eq]; exact (ofReal_norm _).symm
    have e3 : ‖f x‖ₑ = ENNReal.ofReal ‖f x‖ := (ofReal_norm _).symm
    rw [e1, e2, e3, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by linarith : (0:ℝ) ≤ s - 1),
      ← ENNReal.ofReal_mul (by linarith), ← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal h1


/-- The case `1 < p < n`. -/
theorem gns_gt {n : ℕ} (hn : 2 ≤ n) {p : ℝ} (hp : 1 < p) (hpn : p < n)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f) :
    eLpNorm f (ENNReal.ofReal ((n : ℝ) * p / ((n : ℝ) - p))) volume ≤
      ENNReal.ofReal (p * ((n : ℝ) - 1) / (2 * ((n : ℝ) - p))) *
        eLpNorm (fun x => ‖gradient f x‖) (ENNReal.ofReal p) volume := by
  have hN2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  set N : ℝ := (n : ℝ) with hN
  have hNp : 0 < N - p := by linarith
  have hN1 : 0 < N - 1 := by linarith
  have hp1 : 0 < p - 1 := by linarith
  have hp0 : 0 < p := by linarith
  have hN0 : 0 < N := by linarith
  set s : ℝ := p * (N - 1) / (N - p) with hs
  have hs1 : 1 < s := by rw [hs, lt_div_iff₀ hNp]; nlinarith
  set q : ℝ := Real.conjExponent N with hqdef
  have hq : Real.HolderConjugate N q := Real.HolderConjugate.conjExponent (by linarith)
  set p' : ℝ := Real.conjExponent p with hp'def
  have hpp : Real.HolderConjugate p' p := (Real.HolderConjugate.conjExponent hp).symm
  have hq' : q = N / (N - 1) := rfl
  have hp'' : p' = p / (p - 1) := rfl
  set ps : ℝ := N * p / (N - p) with hps
  have hps0 : 0 < ps := by positivity
  have e1 : s * q = ps := by rw [hs, hq', hps]; field_simp
  have e2 : (s - 1) * p' = ps := by rw [hs, hp'', hps]; field_simp; ring
  have e3 : 1 - q / p' = 1 / s := by rw [hq', hp'', hs]; field_simp; ring
  have hq0 : 0 < q := hq.symm.pos
  have hp'0 : 0 < p' := hpp.pos
  obtain ⟨hvC, hvc, hgrad⟩ := rpow_aux hf hfc hs1
  set A : ℝ≥0∞ := ∫⁻ x, ‖f x‖ₑ ^ ps with hA
  set B : ℝ≥0∞ := ∫⁻ x, ‖gradient f x‖ₑ ^ p with hB
  have hAfin : A ≠ ⊤ := finite_lintegral hf.continuous hfc hps0
  have hmain := lintegral_pow_le_half_euclid hq hvC hvc
  have hLHS : ∫⁻ x, ‖‖f x‖ ^ s‖ₑ ^ q = A := by
    refine lintegral_congr fun x => ?_
    have h0 : 0 ≤ ‖f x‖ ^ s := Real.rpow_nonneg (norm_nonneg _) _
    rw [Real.enorm_eq_ofReal h0, ← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by linarith),
      ofReal_norm, ← ENNReal.rpow_mul, e1]
  have hm1 : AEMeasurable (fun x => ‖f x‖ₑ ^ (s - 1)) volume :=
    (hf.continuous.enorm.measurable.pow_const _).aemeasurable
  have hm2 : AEMeasurable (fun x => ‖gradient f x‖ₑ) volume :=
    (continuous_gradient hf).enorm.measurable.aemeasurable
  have hgb : ∫⁻ x, ‖gradient (fun x => ‖f x‖ ^ s) x‖ₑ ≤
      ENNReal.ofReal s * (A ^ (1 / p') * B ^ (1 / p)) := by
    calc ∫⁻ x, ‖gradient (fun x => ‖f x‖ ^ s) x‖ₑ
        ≤ ∫⁻ x, ENNReal.ofReal s * (‖f x‖ₑ ^ (s - 1) * ‖gradient f x‖ₑ) := by
          refine lintegral_mono fun x => ?_
          calc _ ≤ _ := hgrad x
            _ = _ := by ring
      _ = ENNReal.ofReal s * ∫⁻ x, ‖f x‖ₑ ^ (s - 1) * ‖gradient f x‖ₑ :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal s * (A ^ (1 / p') * B ^ (1 / p)) := by
          gcongr
          have h := ENNReal.lintegral_mul_le_Lp_mul_Lq volume hpp hm1 hm2
          have hA' : ∫⁻ x, (‖f x‖ₑ ^ (s - 1)) ^ p' = A := by
            refine lintegral_congr fun x => ?_
            rw [← ENNReal.rpow_mul, e2]
          rw [hA'] at h
          exact h
  have hc : ENNReal.ofReal (1 / 2) * ENNReal.ofReal s = ENNReal.ofReal (s / 2) := by
    rw [← ENNReal.ofReal_mul (by norm_num)]; congr 1; ring
  have hchain : A ≤ ENNReal.ofReal (s / 2) ^ q * B ^ (q / p) * A ^ (q / p') := by
    calc A = ∫⁻ x, ‖‖f x‖ ^ s‖ₑ ^ q := hLHS.symm
      _ ≤ (ENNReal.ofReal (1 / 2) * ∫⁻ x, ‖gradient (fun x => ‖f x‖ ^ s) x‖ₑ) ^ q := hmain
      _ ≤ (ENNReal.ofReal (1 / 2) * (ENNReal.ofReal s * (A ^ (1 / p') * B ^ (1 / p)))) ^ q := by
          gcongr
      _ = ENNReal.ofReal (s / 2) ^ q * B ^ (q / p) * A ^ (q / p') := by
          rw [← mul_assoc, hc, ENNReal.mul_rpow_of_nonneg _ _ hq0.le,
            ENNReal.mul_rpow_of_nonneg _ _ hq0.le, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
          have e4 : 1 / p' * q = q / p' := by ring
          have e5 : 1 / p * q = q / p := by ring
          rw [e4, e5]; ring
  have hγ : q / p' = 1 - 1 / s := by linarith [e3]
  have hs_inv0 : 0 < 1 / s := by positivity
  have hs_inv1 : 1 / s < 1 := by rw [div_lt_one (by linarith)]; exact hs1
  have hγ0 : 0 ≤ q / p' := by rw [hγ]; linarith
  have hγ1 : q / p' < 1 := by rw [hγ]; linarith
  have hcan := cancel hγ0 hγ1 hAfin hchain
  rw [e3] at hcan
  have hfin : eLpNorm f (ENNReal.ofReal ps) volume = A ^ (1 / ps) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.2 hps0).ne' ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal hps0.le]
  have hgfin : eLpNorm (fun x => ‖gradient f x‖) (ENNReal.ofReal p) volume = B ^ (1 / p) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.2 hp0).ne' ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal hp0.le]
    simp only [enorm_norm]
    rfl
  have hcc : s / 2 = p * (N - 1) / (2 * (N - p)) := by rw [hs]; field_simp
  rw [hfin, hgfin, ← hcc]
  have h1 : A ^ (1 / ps) = (A ^ (1 / s)) ^ (1 / q) := by
    rw [← ENNReal.rpow_mul]; congr 1; rw [← e1]; field_simp
  calc A ^ (1 / ps) = (A ^ (1 / s)) ^ (1 / q) := h1
    _ ≤ (ENNReal.ofReal (s / 2) ^ q * B ^ (q / p)) ^ (1 / q) := by gcongr
    _ = ENNReal.ofReal (s / 2) * B ^ (1 / p) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
        have e6 : q * (1 / q) = 1 := by field_simp
        have e7 : q / p * (1 / q) = 1 / p := by field_simp
        rw [e6, e7, ENNReal.rpow_one]



/-- The case `p = 1`. -/
theorem gns_one {n : ℕ} (hn : 2 ≤ n) {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiff ℝ 1 f)
    (hfc : HasCompactSupport f) :
    eLpNorm f (ENNReal.ofReal ((n : ℝ) * 1 / ((n : ℝ) - 1))) volume ≤
      ENNReal.ofReal (1 * ((n : ℝ) - 1) / (2 * ((n : ℝ) - 1))) *
        eLpNorm (fun x => ‖gradient f x‖) (ENNReal.ofReal 1) volume := by
  have hN2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  set N : ℝ := (n : ℝ) with hN
  have hN1 : 0 < N - 1 := by linarith
  set q : ℝ := Real.conjExponent N with hqdef
  have hq : Real.HolderConjugate N q := Real.HolderConjugate.conjExponent (by linarith)
  have hq' : q = N * 1 / (N - 1) := by rw [mul_one]; rfl
  have hq0 : 0 < q := hq.symm.pos
  have hmain := lintegral_pow_le_half_euclid hq hf hfc
  have hc : 1 * (N - 1) / (2 * (N - 1)) = 1 / 2 := by field_simp
  rw [← hq', hc, ENNReal.ofReal_one, eLpNorm_one_eq_lintegral_enorm,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.2 hq0).ne' ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hq0.le]
  simp only [enorm_norm]
  calc (∫⁻ x, ‖f x‖ₑ ^ q) ^ (1 / q)
      ≤ ((ENNReal.ofReal (1 / 2) * ∫⁻ x, ‖gradient f x‖ₑ) ^ q) ^ (1 / q) := by gcongr
    _ = ENNReal.ofReal (1 / 2) * ∫⁻ x, ‖gradient f x‖ₑ := by
        rw [← ENNReal.rpow_mul, mul_one_div_cancel hq0.ne', ENNReal.rpow_one]

end GNS

end GNSAux

open MeasureTheory

theorem solution {n : ℕ} (hn : 2 ≤ n) {p : ℝ} (hp : 1 ≤ p) (hpn : p < n)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hfc : HasCompactSupport f) :
    eLpNorm f (ENNReal.ofReal (HunterPDE.Sobolev.sobolevConjugate n p)) volume ≤
      ENNReal.ofReal (p * ((n : ℝ) - 1) / (2 * ((n : ℝ) - p))) *
        eLpNorm (fun x => ‖gradient f x‖) (ENNReal.ofReal p) volume := by
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by exact_mod_cast le_top)
  have hsc : HunterPDE.Sobolev.sobolevConjugate n p = (n : ℝ) * p / ((n : ℝ) - p) := rfl
  rw [hsc]
  rcases hp.eq_or_lt with rfl | hp1
  · exact GNS.gns_one hn hf1 hfc
  · exact GNS.gns_gt hn hp1 hpn hf1 hfc
