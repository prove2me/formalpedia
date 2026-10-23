-- Prove2me | solution 1 for KalaiVempala.Lazy.lemma_1_2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-22T07:59:09.526767+00:00
-- url     : https://prove2.me/submissions/8a3cf8d9-0cfd-4d11-964d-6d6cb97c0a83

import Mathlib
import Definitions.Def_OracleRO_ApproxFPL_FPL
import Definitions.Def_KalaiVempala_Lazy_Setting

set_option autoImplicit false

open MeasureTheory OracleRO.ApproxFPL

namespace KV96B

/-! ## Part 1: the Laplace law and the FLL* step -/

lemma integrable_exp_abs (ε : ℝ) (hε : 0 < ε) :
    Integrable (fun x : ℝ => (ε / 2) * Real.exp (-(ε * |x|))) := by
  refine Integrable.const_mul ?_ _
  rw [← integrableOn_univ, ← Set.Iic_union_Ioi (a := (0 : ℝ))]
  refine IntegrableOn.union ?_ ?_
  · refine (integrableOn_exp_mul_Iic hε 0).congr_fun (fun x hx => ?_) measurableSet_Iic
    simp only [Set.mem_Iic] at hx
    rw [abs_of_nonpos hx]; ring_nf
  · refine (exp_neg_integrableOn_Ioi 0 hε).congr_fun (fun x hx => ?_) measurableSet_Ioi
    simp only [Set.mem_Ioi] at hx
    rw [abs_of_pos hx]; ring_nf

lemma integral_exp_abs (ε : ℝ) (hε : 0 < ε) :
    ∫ x : ℝ, (ε / 2) * Real.exp (-(ε * |x|)) = 1 := by
  rw [integral_const_mul]
  have h1 := integral_comp_abs (f := fun y => Real.exp (-(ε * y)))
  rw [h1]
  have h2 : ∫ x in Set.Ioi (0 : ℝ), Real.exp (-(ε * x)) = 1 / ε := by
    have h3 := integral_exp_mul_Ioi (a := -ε) (by linarith) 0
    simp only [mul_zero, Real.exp_zero] at h3
    have h4 : (fun x : ℝ => Real.exp (-(ε * x))) = fun x => Real.exp (-ε * x) := by
      funext x; ring_nf
    rw [h4, h3]; field_simp
  rw [h2]; field_simp

lemma laplace_univ {n : ℕ} (ε : ℝ) (hε : 0 < ε) :
    KalaiVempala.Multiplicative.laplaceLaw n ε Set.univ = 1 := by
  unfold KalaiVempala.Multiplicative.laplaceLaw
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have hprod : ∀ x : Fin n → ℝ, (ε / 2) ^ n * Real.exp (-(ε * ∑ i, |x i|)) =
      ∏ i, (ε / 2) * Real.exp (-(ε * |x i|)) := by
    intro x
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      ← Real.exp_sum]
    congr 2
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
  simp_rw [hprod]
  have hint : Integrable (fun x : Fin n → ℝ => ∏ i, (ε / 2) * Real.exp (-(ε * |x i|))) := by
    have := Integrable.fintype_prod (f := fun (_ : Fin n) (y : ℝ) => (ε / 2) * Real.exp (-(ε * |y|)))
      (μ := fun _ => (volume : Measure ℝ)) (fun _ => integrable_exp_abs ε hε)
    simpa [volume_pi] using this
  rw [← ofReal_integral_eq_lintegral_ofReal hint]
  · rw [integral_fintype_prod_volume_eq_pow (fun y : ℝ => (ε / 2) * Real.exp (-(ε * |y|))),
      integral_exp_abs ε hε, one_pow, ENNReal.ofReal_one]
  · exact Filter.Eventually.of_forall (fun x => Finset.prod_nonneg
      (fun i _ => mul_nonneg (by linarith) (Real.exp_pos _).le))

lemma accept_meas {n : ℕ} (ε : ℝ) (v : Fin n → ℝ) :
    Measurable (fun p : Fin n → ℝ => KalaiVempala.Lazy.fllStarAccept ε v p) := by
  unfold KalaiVempala.Lazy.fllStarAccept
  fun_prop

lemma kernel_meas {n : ℕ} (ε : ℝ) (v : Fin n → ℝ) :
    Measurable (fun p : Fin n → ℝ =>
      ENNReal.ofReal (KalaiVempala.Lazy.fllStarAccept ε v p) • Measure.dirac (p, p - v)
      + ENNReal.ofReal (1 - KalaiVempala.Lazy.fllStarAccept ε v p) • Measure.dirac (p, -p)) := by
  have ha := accept_meas ε v
  refine Measure.measurable_of_measurable_coe _ (fun S hS => ?_)
  simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ hS]
  refine Measurable.add ?_ ?_
  · exact (ENNReal.measurable_ofReal.comp ha).mul
      ((measurable_one.indicator hS).comp (measurable_id.prodMk (measurable_id.sub_const v)))
  · exact (ENNReal.measurable_ofReal.comp (measurable_const.sub ha)).mul
      ((measurable_one.indicator hS).comp (measurable_id.prodMk measurable_id.neg))

lemma accept_le_one {n : ℕ} (ε : ℝ) (v p : Fin n → ℝ) :
    KalaiVempala.Lazy.fllStarAccept ε v p ≤ 1 := by
  unfold KalaiVempala.Lazy.fllStarAccept; exact min_le_left _ _

lemma accept_nonneg {n : ℕ} (ε : ℝ) (v p : Fin n → ℝ) :
    0 ≤ KalaiVempala.Lazy.fllStarAccept ε v p := by
  unfold KalaiVempala.Lazy.fllStarAccept
  exact le_min zero_le_one (Real.exp_pos _).le

lemma key_real (u w X Y : ℝ) (_hu : 0 ≤ u) (_hw : 0 ≤ w) (hX : 0 < X) (_hY : 0 < Y)
    (hXY : X * Y = 1) (huX : u * X = w) (hwY : w * Y = u) :
    u * min 1 X + w * (1 - min 1 Y) = w := by
  rcases le_total X 1 with h | h
  · have hY1 : 1 ≤ Y := by nlinarith
    rw [min_eq_right h, min_eq_left hY1]; linarith
  · have hY1 : Y ≤ 1 := by nlinarith
    rw [min_eq_left h, min_eq_right hY1]; nlinarith

lemma key_identity {n : ℕ} (ε : ℝ) (hε : 0 < ε) (v q : Fin n → ℝ) :
    ENNReal.ofReal ((ε / 2) ^ n * Real.exp (-(ε * ∑ i, |(q + v) i|))) *
        ENNReal.ofReal (KalaiVempala.Lazy.fllStarAccept ε v (q + v)) +
      ENNReal.ofReal ((ε / 2) ^ n * Real.exp (-(ε * ∑ i, |(-q) i|))) *
        ENNReal.ofReal (1 - KalaiVempala.Lazy.fllStarAccept ε v (-q)) =
      ENNReal.ofReal ((ε / 2) ^ n * Real.exp (-(ε * ∑ i, |q i|))) := by
  have hc : 0 ≤ (ε / 2) ^ n := pow_nonneg (by linarith) n
  set N0 := ∑ i, |q i| with hN0
  set N1 := ∑ i, |q i + v i| with hN1
  have e1 : ∑ i, |(q + v) i| = N1 := by simp [hN1]
  have e2 : ∑ i, |(-q) i| = N0 := by simp [hN0]
  have e3 : ∑ i, |(q + v) i - v i| = N0 := by simp [hN0]
  have e4 : ∑ i, |(-q) i - v i| = N1 := by
    rw [hN1]; refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Pi.neg_apply, show -q i - v i = -(q i + v i) by ring, abs_neg]
  have hA1 : KalaiVempala.Lazy.fllStarAccept ε v (q + v) =
      min 1 (Real.exp (-(ε * (N0 - N1)))) := by
    unfold KalaiVempala.Lazy.fllStarAccept; rw [e3, e1]
  have hA2 : KalaiVempala.Lazy.fllStarAccept ε v (-q) =
      min 1 (Real.exp (-(ε * (N1 - N0)))) := by
    unfold KalaiVempala.Lazy.fllStarAccept; rw [e4, e2]
  rw [e1, e2, hA1, hA2]
  have hm1 : 0 ≤ min 1 (Real.exp (-(ε * (N0 - N1)))) := le_min zero_le_one (Real.exp_pos _).le
  have hm2 : 0 ≤ 1 - min 1 (Real.exp (-(ε * (N1 - N0)))) := by
    have := min_le_left (1 : ℝ) (Real.exp (-(ε * (N1 - N0)))); linarith
  have hu : 0 ≤ (ε / 2) ^ n * Real.exp (-(ε * N1)) := mul_nonneg hc (Real.exp_pos _).le
  have hw : 0 ≤ (ε / 2) ^ n * Real.exp (-(ε * N0)) := mul_nonneg hc (Real.exp_pos _).le
  rw [← ENNReal.ofReal_mul hu, ← ENNReal.ofReal_mul hw,
    ← ENNReal.ofReal_add (mul_nonneg hu hm1) (mul_nonneg hw hm2)]
  congr 1
  apply key_real _ _ _ _ hu hw (Real.exp_pos _) (Real.exp_pos _)
  · rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
  · rw [mul_assoc, ← Real.exp_add]; ring_nf
  · rw [mul_assoc, ← Real.exp_add]; ring_nf

lemma stationary {n : ℕ} (ε : ℝ) (hε : 0 < ε) (v : Fin n → ℝ) :
    (KalaiVempala.Lazy.fllStarJoint ε v (KalaiVempala.Multiplicative.laplaceLaw n ε)).map
      Prod.snd = KalaiVempala.Multiplicative.laplaceLaw n ε := by
  set ρ : (Fin n → ℝ) → ENNReal :=
    fun x => ENNReal.ofReal ((ε / 2) ^ n * Real.exp (-(ε * ∑ i, |x i|))) with hρ
  have hρm : Measurable ρ := by rw [hρ]; fun_prop
  have hμ : KalaiVempala.Multiplicative.laplaceLaw n ε = volume.withDensity ρ := rfl
  set a := fun p : Fin n → ℝ => KalaiVempala.Lazy.fllStarAccept ε v p with ha_def
  have ham : Measurable a := accept_meas ε v
  ext B hB
  have hSB : MeasurableSet (Prod.snd ⁻¹' B : Set ((Fin n → ℝ) × (Fin n → ℝ))) := measurable_snd hB
  rw [Measure.map_apply measurable_snd hB, KalaiVempala.Lazy.fllStarJoint,
    Measure.bind_apply hSB (kernel_meas ε v).aemeasurable]
  have hF : ∀ p : Fin n → ℝ,
      (ENNReal.ofReal (KalaiVempala.Lazy.fllStarAccept ε v p) • Measure.dirac (p, p - v)
        + ENNReal.ofReal (1 - KalaiVempala.Lazy.fllStarAccept ε v p) • Measure.dirac (p, -p))
        (Prod.snd ⁻¹' B) =
      ENNReal.ofReal (a p) * B.indicator 1 (p - v) + ENNReal.ofReal (1 - a p) * B.indicator 1 (-p) := by
    intro p
    simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ hSB, ha_def]
    rfl
  simp_rw [hF]
  rw [hμ, lintegral_withDensity_eq_lintegral_mul _ hρm (by
      exact ((ENNReal.measurable_ofReal.comp ham).mul
        ((measurable_one.indicator hB).comp (measurable_id.sub_const v))).add
        ((ENNReal.measurable_ofReal.comp (measurable_const.sub ham)).mul
        ((measurable_one.indicator hB).comp measurable_neg)))]
  simp only [Pi.mul_apply, mul_add]
  rw [lintegral_add_left (f := fun p => ρ p * (ENNReal.ofReal (a p) * B.indicator 1 (p - v)))
      (by exact hρm.mul ((ENNReal.measurable_ofReal.comp ham).mul
        ((measurable_one.indicator hB).comp (measurable_id.sub_const v))))]
  rw [← lintegral_add_right_eq_self (μ := (volume : Measure (Fin n → ℝ)))
      (fun p => ρ p * (ENNReal.ofReal (a p) * B.indicator 1 (p - v))) v]
  rw [← lintegral_neg_eq_self (μ := (volume : Measure (Fin n → ℝ)))
      (fun p => ρ p * (ENNReal.ofReal (1 - a p) * B.indicator 1 (-p)))]
  simp only [add_sub_cancel_right, neg_neg]
  rw [← lintegral_add_left (f := fun q => ρ (q + v) * (ENNReal.ofReal (a (q + v)) * B.indicator 1 q))
      (by exact (hρm.comp (measurable_id.add_const v)).mul ((ENNReal.measurable_ofReal.comp
        (ham.comp (measurable_id.add_const v))).mul (measurable_one.indicator hB)))]
  rw [withDensity_apply _ hB, ← lintegral_indicator hB]
  refine lintegral_congr (fun q => ?_)
  by_cases hq : q ∈ B
  · simp only [Set.indicator_of_mem hq, Pi.one_apply, mul_one]
    rw [hρ, ha_def]
    exact key_identity ε hε v q
  · simp [Set.indicator_of_notMem hq]

lemma fllStarLaw_eq {n : ℕ} (ε : ℝ) (hε : 0 < ε) (s : ℕ → Fin n → ℝ) :
    ∀ k, KalaiVempala.Lazy.fllStarLaw ε s k = KalaiVempala.Multiplicative.laplaceLaw n ε
  | 0 => rfl
  | 1 => rfl
  | k + 2 => by
    rw [KalaiVempala.Lazy.fllStarLaw, fllStarLaw_eq ε hε s (k + 1)]
    exact stationary ε hε (s (k + 1))

lemma reject_le {n : ℕ} (ε : ℝ) (hε : 0 < ε) (v p : Fin n → ℝ) :
    1 - KalaiVempala.Lazy.fllStarAccept ε v p ≤ ε * ∑ i, |v i| := by
  unfold KalaiVempala.Lazy.fllStarAccept
  set u := ε * (∑ i, |p i - v i| - ∑ i, |p i|)
  have htri : ∑ i, |p i - v i| - ∑ i, |p i| ≤ ∑ i, |v i| := by
    have : ∑ i, |p i - v i| ≤ ∑ i, (|p i| + |v i|) :=
      Finset.sum_le_sum (fun i _ => abs_sub _ _)
    rw [Finset.sum_add_distrib] at this; linarith
  have hu : u ≤ ε * ∑ i, |v i| := mul_le_mul_of_nonneg_left htri hε.le
  have hv0 : 0 ≤ ε * ∑ i, |v i| := mul_nonneg hε.le (Finset.sum_nonneg (fun i _ => abs_nonneg _))
  have hexp := Real.add_one_le_exp (-u)
  have : 1 - ε * ∑ i, |v i| ≤ min 1 (Real.exp (-u)) := le_min (by linarith) (by linarith)
  linarith

lemma reject_mass {n : ℕ} (ε : ℝ) (hε : 0 < ε) (v x y : Fin n → ℝ) (hxy : y = x + v)
    (A : ℝ) (hA : ∑ i, |v i| ≤ A) :
    KalaiVempala.Lazy.fllStarJoint ε v (KalaiVempala.Multiplicative.laplaceLaw n ε)
      {q | y + q.2 ≠ x + q.1} ≤ ENNReal.ofReal (ε * A) := by
  have hS : MeasurableSet {q : (Fin n → ℝ) × (Fin n → ℝ) | y + q.2 ≠ x + q.1} :=
    (measurableSet_eq_fun (by fun_prop) (by fun_prop)).compl
  rw [KalaiVempala.Lazy.fllStarJoint, Measure.bind_apply hS (kernel_meas ε v).aemeasurable]
  calc ∫⁻ p, (ENNReal.ofReal (KalaiVempala.Lazy.fllStarAccept ε v p) • Measure.dirac (p, p - v)
        + ENNReal.ofReal (1 - KalaiVempala.Lazy.fllStarAccept ε v p) • Measure.dirac (p, -p))
        {q | y + q.2 ≠ x + q.1} ∂(KalaiVempala.Multiplicative.laplaceLaw n ε)
      ≤ ∫⁻ _p, ENNReal.ofReal (ε * A) ∂(KalaiVempala.Multiplicative.laplaceLaw n ε) := by
        refine lintegral_mono (fun p => ?_)
        have h0 : (Measure.dirac (p, p - v)) {q : (Fin n → ℝ) × (Fin n → ℝ) | y + q.2 ≠ x + q.1}
            = 0 := by
          rw [Measure.dirac_apply' _ hS, Set.indicator_of_notMem]
          simp only [Set.mem_ofPred_eq, not_not, hxy]
          abel
        simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul, h0, mul_zero, zero_add]
        calc ENNReal.ofReal (1 - KalaiVempala.Lazy.fllStarAccept ε v p) *
              (Measure.dirac (p, -p)) {q : (Fin n → ℝ) × (Fin n → ℝ) | y + q.2 ≠ x + q.1}
            ≤ ENNReal.ofReal (1 - KalaiVempala.Lazy.fllStarAccept ε v p) * 1 :=
              by gcongr; exact prob_le_one
          _ ≤ ENNReal.ofReal (ε * A) := by
              rw [mul_one]
              exact ENNReal.ofReal_le_ofReal ((reject_le ε hε v p).trans
                (mul_le_mul_of_nonneg_left hA hε.le))
    _ = ENNReal.ofReal (ε * A) := by
        rw [lintegral_const, laplace_univ ε hε, mul_one]

end KV96B

namespace KV96U

lemma grid_eq_toIcoMod (ε : ℝ) (hε : 0 < ε) (x p : ℝ) :
    p + (⌈ε * (x - p)⌉ : ℝ) / ε = toIcoMod (inv_pos.mpr hε) x p := by
  symm
  rw [toIcoMod_eq_iff]
  refine ⟨⟨?_, ?_⟩, -⌈ε * (x - p)⌉, ?_⟩
  · have h1 := Int.le_ceil (ε * (x - p))
    have : x - p ≤ (⌈ε * (x - p)⌉ : ℝ) / ε := by rw [le_div_iff₀ hε]; linarith
    linarith
  · have h1 := Int.ceil_lt_add_one (ε * (x - p))
    have : (⌈ε * (x - p)⌉ : ℝ) / ε < x - p + ε⁻¹ := by
      rw [div_lt_iff₀ hε, add_mul, inv_mul_cancel₀ hε.ne']; linarith
    linarith
  · rw [zsmul_eq_mul, div_eq_mul_inv]; push_cast; ring

lemma grid_fun_eq (ε : ℝ) (hε : 0 < ε) (x : ℝ) :
    (fun r : ℝ => r + (⌈ε * (x - r)⌉ : ℝ) / ε) = toIcoMod (inv_pos.mpr hε) x := by
  funext r; exact grid_eq_toIcoMod ε hε x r

lemma grid_meas (ε x : ℝ) : Measurable (fun r : ℝ => r + (⌈ε * (x - r)⌉ : ℝ) / ε) := by
  have h : Measurable (fun r : ℝ => ((⌈ε * (x - r)⌉ : ℤ) : ℝ)) :=
    measurable_from_top.comp (Measurable.ceil (by fun_prop))
  exact measurable_id.add (h.div_const ε)

lemma grid_nd_meas {n : ℕ} (ε : ℝ) (x : Fin n → ℝ) :
    Measurable (KalaiVempala.Lazy.fllGridPoint ε x) :=
  measurable_pi_lambda _ (fun i => (grid_meas ε (x i)).comp (measurable_pi_apply i))

lemma map_toIcoMod (L : ℝ) (hL : 0 < L) (x : ℝ) :
    (volume.restrict (Set.Icc (0 : ℝ) L)).map (toIcoMod hL x) =
      volume.restrict (Set.Icc x (x + L)) := by
  haveI : Fact (0 < L) := ⟨hL⟩
  set f : AddCircle L → ℝ := fun z => ((AddCircle.measurableEquivIco L x z : Set.Ico x (x + L)) : ℝ)
    with hf
  have hfm : Measurable f := measurable_subtype_coe.comp (AddCircle.measurableEquivIco L x).measurable
  have hmk : Measurable (fun r : ℝ => (r : AddCircle L)) := AddCircle.measurable_mk'
  have hcomp : toIcoMod hL x = f ∘ (fun r : ℝ => (r : AddCircle L)) := by
    funext r; rfl
  have h0 : volume.restrict (Set.Icc (0 : ℝ) L) = volume.restrict (Set.Ioc 0 (0 + L)) := by
    rw [zero_add]; exact Measure.restrict_congr_set Ioc_ae_eq_Icc.symm
  have hx : volume.restrict (Set.Icc x (x + L)) = volume.restrict (Set.Ioc x (x + L)) :=
    Measure.restrict_congr_set Ioc_ae_eq_Icc.symm
  have hxo : volume.restrict (Set.Icc x (x + L)) = volume.restrict (Set.Ico x (x + L)) :=
    Measure.restrict_congr_set Ico_ae_eq_Icc.symm
  calc (volume.restrict (Set.Icc (0 : ℝ) L)).map (toIcoMod hL x)
      = ((volume.restrict (Set.Ioc 0 (0 + L))).map (fun r : ℝ => (r : AddCircle L))).map f := by
        rw [h0, hcomp, Measure.map_map hfm hmk]
    _ = ((volume.restrict (Set.Ioc x (x + L))).map (fun r : ℝ => (r : AddCircle L))).map f := by
        rw [(AddCircle.measurePreserving_mk L 0).map_eq, (AddCircle.measurePreserving_mk L x).map_eq]
    _ = (volume.restrict (Set.Ico x (x + L))).map (toIcoMod hL x) := by
        rw [Measure.map_map hfm hmk, ← hcomp, ← hx, hxo]
    _ = (volume.restrict (Set.Ico x (x + L))).map id := by
        refine Measure.map_congr ?_
        exact (ae_restrict_mem measurableSet_Ico).mono
          (fun r hr => (toIcoMod_eq_self (hp := hL) (a := x)).mpr hr)
    _ = volume.restrict (Set.Icc x (x + L)) := by rw [Measure.map_id, hxo]

lemma map_add_restrict (L x : ℝ) :
    (volume.restrict (Set.Icc (0 : ℝ) L)).map (fun p => x + p) =
      volume.restrict (Set.Icc x (x + L)) := by
  have h := ((measurePreserving_add_left (volume : Measure ℝ) x).restrict_preimage
    (measurableSet_Icc (a := x) (b := x + L))).map_eq
  have hpre : (fun p : ℝ => x + p) ⁻¹' Set.Icc x (x + L) = Set.Icc 0 L := by
    ext p; simp
  rw [hpre] at h; exact h

lemma map_grid_1d (ε : ℝ) (hε : 0 < ε) (x : ℝ) :
    (ProbabilityTheory.cond (volume : Measure ℝ) (Set.Icc (0 : ℝ) ε⁻¹)).map (fun r => r + (⌈ε * (x - r)⌉ : ℝ) / ε) =
      (ProbabilityTheory.cond (volume : Measure ℝ) (Set.Icc (0 : ℝ) ε⁻¹)).map (fun r => x + r) := by
  rw [grid_fun_eq ε hε, ProbabilityTheory.cond, Measure.map_smul, Measure.map_smul,
    map_toIcoMod _ _ x, map_add_restrict]

lemma cond_prob (ε : ℝ) (hε : 0 < ε) : IsProbabilityMeasure (ProbabilityTheory.cond (volume : Measure ℝ) (Set.Icc (0 : ℝ) ε⁻¹)) := by
  have hL := inv_pos.mpr hε
  refine ProbabilityTheory.cond_isProbabilityMeasure_of_finite ?_ ?_
  · rw [Real.volume_Icc, sub_zero]; exact ENNReal.ofReal_ne_zero_iff.mpr hL
  · rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top

lemma perturb_pi {n : ℕ} (ε : ℝ) (hε : 0 < ε) :
    perturbLaw n ε = Measure.pi (fun _ : Fin n => ProbabilityTheory.cond (volume : Measure ℝ) (Set.Icc (0 : ℝ) ε⁻¹)) := by
  haveI := KV96U.cond_prob ε hε
  symm
  refine Measure.pi_eq (fun s hs => ?_)
  have hC : Set.Icc (0 : Fin n → ℝ) (fun _ => ε⁻¹) = Set.univ.pi (fun _ => Set.Icc (0 : ℝ) ε⁻¹) := by
    ext y; simp [Set.mem_Icc, Pi.le_def, ]
  rw [perturbLaw, ProbabilityTheory.cond_apply measurableSet_Icc, hC, ← Set.pi_inter_distrib,
    volume_pi_pi, volume_pi_pi]
  simp_rw [ProbabilityTheory.cond_apply measurableSet_Icc]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_const, ENNReal.inv_pow]

lemma map_grid {n : ℕ} (ε : ℝ) (hε : 0 < ε) (x : Fin n → ℝ) :
    (perturbLaw n ε).map (KalaiVempala.Lazy.fllGridPoint ε x) =
      (perturbLaw n ε).map (fun p => x + p) := by
  haveI := KV96U.cond_prob ε hε
  have hm1 : ∀ i, Measurable (fun r : ℝ => r + (⌈ε * (x i - r)⌉ : ℝ) / ε) :=
    fun i => grid_meas ε (x i)
  haveI : ∀ i, IsProbabilityMeasure ((ProbabilityTheory.cond (volume : Measure ℝ) (Set.Icc (0 : ℝ) ε⁻¹)).map
      (fun r : ℝ => r + (⌈ε * (x i - r)⌉ : ℝ) / ε)) :=
    fun i => Measure.isProbabilityMeasure_map (hm1 i).aemeasurable
  haveI : ∀ i, IsProbabilityMeasure ((ProbabilityTheory.cond (volume : Measure ℝ) (Set.Icc (0 : ℝ) ε⁻¹)).map (fun r : ℝ => x i + r)) :=
    fun i => Measure.isProbabilityMeasure_map (measurable_const_add (x i)).aemeasurable
  rw [perturb_pi ε hε]
  have e1 : KalaiVempala.Lazy.fllGridPoint ε x =
      fun p i => (fun r : ℝ => r + (⌈ε * (x i - r)⌉ : ℝ) / ε) (p i) := rfl
  have e2 : (fun p : Fin n → ℝ => x + p) = fun p i => (fun r : ℝ => x i + r) (p i) := rfl
  rw [e1, e2, Measure.pi_map_pi (fun i => (hm1 i).aemeasurable),
    Measure.pi_map_pi (fun i => (measurable_const_add (x i)).aemeasurable)]
  congr 1; funext i; exact map_grid_1d ε hε (x i)

lemma move_1d (ε : ℝ) (hε : 0 < ε) (x x' : ℝ) :
    (ProbabilityTheory.cond (volume : Measure ℝ) (Set.Icc (0 : ℝ) ε⁻¹))
        {r | r + (⌈ε * (x - r)⌉ : ℝ) / ε ≠ r + (⌈ε * (x' - r)⌉ : ℝ) / ε}
      ≤ ENNReal.ofReal (ε * |x' - x|) := by
  have hL := inv_pos.mpr hε
  have hset : {r : ℝ | r + (⌈ε * (x - r)⌉ : ℝ) / ε ≠ r + (⌈ε * (x' - r)⌉ : ℝ) / ε} =
      (toIcoMod hL x) ⁻¹' {y | toIcoMod hL x' y ≠ y} := by
    ext r
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, grid_eq_toIcoMod ε hε, toIcoMod_toIcoMod]
    exact ne_comm
  have htm : Measurable (toIcoMod hL x) := by rw [← grid_fun_eq ε hε]; exact grid_meas ε x
  have hmap : (ProbabilityTheory.cond (volume : Measure ℝ) (Set.Icc (0 : ℝ) ε⁻¹)).map (toIcoMod hL x) =
      (volume (Set.Icc (0 : ℝ) ε⁻¹))⁻¹ • volume.restrict (Set.Icc x (x + ε⁻¹)) := by
    rw [← grid_fun_eq ε hε, map_grid_1d ε hε, ProbabilityTheory.cond, Measure.map_smul,
      map_add_restrict]
  rw [hset]
  refine (Measure.le_map_apply htm.aemeasurable _).trans ?_
  rw [hmap, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply' measurableSet_Icc,
    Real.volume_Icc, sub_zero, ENNReal.ofReal_inv_of_pos hε, inv_inv]
  have hsub : {y | toIcoMod hL x' y ≠ y} ∩ Set.Icc x (x + ε⁻¹) ⊆
      Set.Icc x x' ∪ Set.Icc (x' + ε⁻¹) (x + ε⁻¹) := by
    rintro y ⟨hy1, hy2⟩
    have hy1' : ¬ (y ∈ Set.Ico x' (x' + ε⁻¹)) := fun h => hy1 ((toIcoMod_eq_self (hp := hL)).mpr h)
    simp only [Set.mem_Ico, not_and, not_lt] at hy1'
    by_cases h : y < x'
    · exact Or.inl ⟨hy2.1, h.le⟩
    · exact Or.inr ⟨hy1' (not_lt.mp h), hy2.2⟩
  have hvol : volume ({y | toIcoMod hL x' y ≠ y} ∩ Set.Icc x (x + ε⁻¹)) ≤
      ENNReal.ofReal |x' - x| := by
    calc _ ≤ volume (Set.Icc x x' ∪ Set.Icc (x' + ε⁻¹) (x + ε⁻¹)) := measure_mono hsub
      _ ≤ volume (Set.Icc x x') + volume (Set.Icc (x' + ε⁻¹) (x + ε⁻¹)) := measure_union_le _ _
      _ = ENNReal.ofReal |x' - x| := by
        rw [Real.volume_Icc, Real.volume_Icc]
        rcases le_total x x' with h | h
        · rw [ENNReal.ofReal_of_nonpos (by linarith : x + ε⁻¹ - (x' + ε⁻¹) ≤ 0), add_zero,
            abs_of_nonneg (by linarith)]
        · rw [ENNReal.ofReal_of_nonpos (by linarith : x' - x ≤ 0), zero_add,
            abs_of_nonpos (by linarith)]
          congr 1; ring
  calc ENNReal.ofReal ε * volume ({y | toIcoMod hL x' y ≠ y} ∩ Set.Icc x (x + ε⁻¹))
      ≤ ENNReal.ofReal ε * ENNReal.ofReal |x' - x| := by gcongr
    _ = ENNReal.ofReal (ε * |x' - x|) := (ENNReal.ofReal_mul hε.le).symm

lemma move_nd {n : ℕ} (ε : ℝ) (hε : 0 < ε) (x v : Fin n → ℝ) :
    perturbLaw n ε {p | KalaiVempala.Lazy.fllGridPoint ε x p ≠
        KalaiVempala.Lazy.fllGridPoint ε (x + v) p}
      ≤ ENNReal.ofReal (ε * ∑ i, |v i|) := by
  haveI := KV96U.cond_prob ε hε
  rw [perturb_pi ε hε]
  set E : Fin n → Set ℝ := fun i =>
    {r | r + (⌈ε * (x i - r)⌉ : ℝ) / ε ≠ r + (⌈ε * ((x + v) i - r)⌉ : ℝ) / ε} with hE
  have hsub : {p | KalaiVempala.Lazy.fllGridPoint ε x p ≠
      KalaiVempala.Lazy.fllGridPoint ε (x + v) p} ⊆ ⋃ i, (Function.eval i) ⁻¹' E i := by
    intro p hp
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hp
    exact Set.mem_iUnion.mpr ⟨i, hi⟩
  have hEm : ∀ i, MeasurableSet (E i) := fun i =>
    (measurableSet_eq_fun (grid_meas ε (x i)) (grid_meas ε ((x + v) i))).compl
  calc _ ≤ Measure.pi (fun _ : Fin n => ProbabilityTheory.cond (volume : Measure ℝ) (Set.Icc (0 : ℝ) ε⁻¹))
          (⋃ i, (Function.eval i) ⁻¹' E i) := measure_mono hsub
    _ ≤ ∑ i, Measure.pi (fun _ : Fin n => ProbabilityTheory.cond (volume : Measure ℝ) (Set.Icc (0 : ℝ) ε⁻¹))
          ((Function.eval i) ⁻¹' E i) := measure_iUnion_fintype_le _ _
    _ = ∑ i, ProbabilityTheory.cond (volume : Measure ℝ) (Set.Icc (0 : ℝ) ε⁻¹) (E i) := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        exact (measurePreserving_eval (μ := fun _ : Fin n => ProbabilityTheory.cond (volume : Measure ℝ) (Set.Icc (0 : ℝ) ε⁻¹)) i
          ).measure_preimage (hEm i).nullMeasurableSet
    _ ≤ ∑ i, ENNReal.ofReal (ε * |v i|) := by
        refine Finset.sum_le_sum (fun i _ => ?_)
        have h := move_1d ε hε (x i) ((x + v) i)
        rw [Pi.add_apply, add_sub_cancel_left] at h
        exact h
    _ = ENNReal.ofReal (ε * ∑ i, |v i|) := by
        rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg hε.le (abs_nonneg _)),
          Finset.mul_sum]

lemma meas_dot {n : ℕ} (v : Fin n → ℝ) : Measurable (fun x : Fin n → ℝ => v ⬝ᵥ x) := by
  unfold dotProduct
  exact Finset.measurable_sum _ (fun i _ => measurable_const.mul (measurable_pi_apply i))

lemma prefixSum_step {n : ℕ} (s : ℕ → Fin n → ℝ) (t : ℕ) (ht : 1 ≤ t) :
    prefixSum s (t - 1) + s t = prefixSum s t := by
  obtain ⟨m, rfl⟩ : ∃ m, t = m + 1 := ⟨t - 1, by omega⟩
  simp only [prefixSum, Nat.add_sub_cancel]
  rw [Finset.sum_Icc_succ_top (by omega)]

end KV96U

open MeasureTheory OracleRO.ApproxFPL KalaiVempala.Lazy in
theorem solution {n : ℕ} (Dset S : Set (Fin n → ℝ))
    (M : (Fin n → ℝ) → (Fin n → ℝ)) (hM : KalaiVempala.Additive.IsArgminOracle Dset M) (hMmeas : Measurable M)
    (Ddiam : ℝ) (hD : ∀ d ∈ Dset, ∀ d' ∈ Dset, ∑ i, |d i - d' i| ≤ Ddiam)
    (A : ℝ) (hA : ∀ x ∈ S, ∑ i, |x i| ≤ A)
    (s : ℕ → Fin n → ℝ) (hs : ∀ t, 1 ≤ t → s t ∈ S) (ε : ℝ) (hε : 0 < ε) :
    ∀ t, 1 ≤ t →
      (∫ p, s t ⬝ᵥ M (fllGridPoint ε (prefixSum s (t - 1)) p) ∂(perturbLaw n ε) =
          ∫ p, s t ⬝ᵥ M (prefixSum s (t - 1) + p) ∂(perturbLaw n ε)) ∧
      perturbLaw n ε {p | fllGridPoint ε (prefixSum s (t - 1)) p ≠
          fllGridPoint ε (prefixSum s t) p} ≤ ENNReal.ofReal (ε * A) ∧
      (∫ p, s t ⬝ᵥ M (prefixSum s (t - 1) + p) ∂(fllStarLaw ε s t) =
          ∫ p, s t ⬝ᵥ M (prefixSum s (t - 1) + p) ∂(KalaiVempala.Multiplicative.laplaceLaw n ε)) ∧
      fllStarJoint ε (s t) (fllStarLaw ε s t)
          {q | prefixSum s t + q.2 ≠ prefixSum s (t - 1) + q.1} ≤ ENNReal.ofReal (ε * A) := by
  intro t ht
  have hstep : prefixSum s t = prefixSum s (t - 1) + s t := (KV96U.prefixSum_step s t ht).symm
  have hSt : ∑ i, |s t i| ≤ A := hA _ (hs t ht)
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hh : Measurable (fun y : Fin n → ℝ => s t ⬝ᵥ M y) := (KV96U.meas_dot (s t)).comp hMmeas
    have h1 := integral_map (μ := perturbLaw n ε)
      (KV96U.grid_nd_meas ε (prefixSum s (t - 1))).aemeasurable
      (f := fun y => s t ⬝ᵥ M y) hh.aestronglyMeasurable
    have h2 := integral_map (μ := perturbLaw n ε)
      (measurable_const_add (prefixSum s (t - 1))).aemeasurable
      (f := fun y => s t ⬝ᵥ M y) hh.aestronglyMeasurable
    rw [← h1, ← h2, KV96U.map_grid ε hε]
  · rw [hstep]
    exact (KV96U.move_nd ε hε _ _).trans
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hSt hε.le))
  · rw [KV96B.fllStarLaw_eq ε hε]
  · rw [KV96B.fllStarLaw_eq ε hε]
    exact KV96B.reject_mass ε hε (s t) _ _ hstep A hSt
