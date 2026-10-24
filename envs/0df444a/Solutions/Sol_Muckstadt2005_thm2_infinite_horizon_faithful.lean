-- Prove2me | solution 1 for Muckstadt2005.thm2_infinite_horizon_faithful
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T06:22:48.854027+00:00
-- url     : https://prove2.me/submissions/46188ba3-a65e-43a8-8442-21704ba37a56

import Mathlib
import Definitions.Def_ServiceParts_BaseStock_Model
import Definitions.Def_ServiceParts_BaseStock_Recursion
import Theorems.Thm_ServiceParts_BaseStock_deriv_bounds
import Theorems.Thm_ServiceParts_BaseStock_property_a
import Theorems.Thm_ServiceParts_BaseStock_order_up_to_optimal

open MeasureTheory Set Filter Topology

namespace MU87
open ServiceParts.BaseStock

variable (M : Model)

lemma g_int : IntegrableOn M.g (Ioi 0) :=
  Integrable.of_integral_ne_zero (by rw [M.g_total]; norm_num)

lemma g_nonneg {x : ℝ} (hx : x ∈ Ioi (0:ℝ)) : 0 ≤ M.g x := (M.g_pos x hx).le

lemma b_pos : 0 < M.b := by
  have h1 : 0 ≤ (1 - M.α) / M.α * M.c :=
    mul_nonneg (div_nonneg (by linarith [M.α_lt_one]) M.α_pos.le) M.c_nonneg
  linarith [M.b_gt]

lemma mean_nonneg : 0 ≤ ∫ x in Ioi (0:ℝ), x * M.g x :=
  setIntegral_nonneg measurableSet_Ioi (fun _ hx => mul_nonneg (le_of_lt hx) (g_nonneg M hx))

lemma L_nonneg (y : ℝ) : 0 ≤ M.L y := by
  unfold Model.L
  split_ifs with hy
  · apply add_nonneg
    · apply mul_nonneg M.h_pos.le
      apply setIntegral_nonneg measurableSet_Ioc
      intro x hx
      exact mul_nonneg (by linarith [hx.2]) (g_nonneg M hx.1)
    · apply mul_nonneg (b_pos M).le
      apply setIntegral_nonneg measurableSet_Ioi
      intro x hx
      exact mul_nonneg (by linarith [show y < x from hx]) (g_nonneg M (show (0:ℝ) < x by
        have : y < x := hx; linarith))
  · apply mul_nonneg (b_pos M).le
    apply setIntegral_nonneg measurableSet_Ioi
    intro x hx
    have : (0:ℝ) < x := hx
    exact mul_nonneg (by linarith) (g_nonneg M hx)

lemma lin_int (w : ℝ) : IntegrableOn (fun x => (w - x) * M.g x) (Ioi 0) := by
  have h1 : IntegrableOn (fun x => w * M.g x) (Ioi 0) := (g_int M).const_mul w
  have h2 := h1.sub M.g_mean
  refine h2.congr_fun (fun x _ => ?_) measurableSet_Ioi
  simp only [Pi.sub_apply]; ring

lemma lin_integral (w : ℝ) :
    ∫ x in Ioi (0:ℝ), (w - x) * M.g x = w - ∫ x in Ioi (0:ℝ), x * M.g x := by
  have h1 : IntegrableOn (fun x => w * M.g x) (Ioi 0) := (g_int M).const_mul w
  have : (fun x => (w - x) * M.g x) = fun x => w * M.g x - x * M.g x := by
    funext x; ring
  rw [this, integral_sub h1 M.g_mean, integral_const_mul, M.g_total, mul_one]

lemma L_ge (w : ℝ) : M.h * (w - ∫ x in Ioi (0:ℝ), x * M.g x) ≤ M.L w := by
  have hμ := mean_nonneg M
  by_cases hw : 0 < w
  · have hL : M.L w = M.h * (∫ x in Ioc (0 : ℝ) w, (w - x) * M.g x) +
        M.b * (∫ x in Ioi w, (x - w) * M.g x) := by
      unfold Model.L; rw [if_pos hw]
    have hb : 0 ≤ M.b * (∫ x in Ioi w, (x - w) * M.g x) := by
      apply mul_nonneg (b_pos M).le
      apply setIntegral_nonneg measurableSet_Ioi
      intro x hx
      have : w < x := hx
      exact mul_nonneg (by linarith) (g_nonneg M (show (0:ℝ) < x by linarith))
    have hsplit := setIntegral_union (μ := volume) (f := fun x => (w - x) * M.g x)
      (Ioc_disjoint_Ioi (le_refl w)) measurableSet_Ioi
      ((lin_int M w).mono_set Ioc_subset_Ioi_self)
      ((lin_int M w).mono_set (Ioi_subset_Ioi hw.le))
    rw [Ioc_union_Ioi_eq_Ioi hw.le, lin_integral] at hsplit
    have hneg : ∫ x in Ioi w, (w - x) * M.g x ≤ 0 := by
      apply setIntegral_nonpos measurableSet_Ioi
      intro x hx
      have : w < x := hx
      exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (g_nonneg M (show (0:ℝ) < x by linarith))
    have : w - ∫ x in Ioi (0:ℝ), x * M.g x ≤ ∫ x in Ioc (0 : ℝ) w, (w - x) * M.g x := by
      linarith
    rw [hL]
    have := mul_le_mul_of_nonneg_left this M.h_pos.le
    linarith
  · have h1 : M.h * (w - ∫ x in Ioi (0:ℝ), x * M.g x) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos M.h_pos.le (by linarith)
    linarith [L_nonneg M w]

lemma f_ge_L : ∀ n : ℕ, 1 ≤ n → ∀ y, M.L y ≤ M.f n y
  | 0, h, _ => by omega
  | 1, _, y => le_refl _
  | n + 2, _, y => by
    have ih := f_ge_L (n + 1) (by omega)
    show M.L y ≤ sInf (M.stageCost (M.f (n + 1)) y '' Ici 0)
    apply le_csInf (Set.Nonempty.image _ nonempty_Ici)
    rintro _ ⟨u, hu, rfl⟩
    unfold Model.stageCost
    have h1 : 0 ≤ M.c * u := mul_nonneg M.c_nonneg hu
    have h2 : 0 ≤ M.α * ∫ x in Ioi (0 : ℝ), M.f (n + 1) (y + u - x) * M.g x := by
      apply mul_nonneg M.α_pos.le
      apply setIntegral_nonneg measurableSet_Ioi
      intro x hx
      exact mul_nonneg ((L_nonneg M _).trans (ih _)) (g_nonneg M hx)
    linarith

/-- uniform Lipschitz constant -/
noncomputable def K : ℝ := M.c + M.b + M.h / (1 - M.α)

lemma K_nonneg : 0 ≤ K M := by
  unfold K
  have : 0 ≤ M.h / (1 - M.α) := div_nonneg M.h_pos.le (by linarith [M.α_lt_one])
  linarith [M.c_nonneg, b_pos M]

lemma f_lip (n : ℕ) (hn : 1 ≤ n) (a b : ℝ) : |M.f n a - M.f n b| ≤ K M * |a - b| := by
  obtain ⟨hd, hb⟩ := deriv_bounds M n hn
  have : ‖M.f n a - M.f n b‖ ≤ K M * ‖a - b‖ := by
    apply Convex.norm_image_sub_le_of_norm_deriv_le (fun x _ => hd x) _ convex_univ (mem_univ _)
      (mem_univ _)
    intro x _
    obtain ⟨h1, h2⟩ := hb x
    rw [Real.norm_eq_abs, abs_le]
    unfold K
    have : 0 ≤ M.h / (1 - M.α) := div_nonneg M.h_pos.le (by linarith [M.α_lt_one])
    constructor <;> linarith [M.c_nonneg, b_pos M]
  simpa [Real.norm_eq_abs] using this

lemma f_cont (n : ℕ) (hn : 1 ≤ n) : Continuous (M.f n) :=
  (deriv_bounds M n hn).1.continuous

/-- integrability of `V (z - x) * g x` under a linear growth bound -/
lemma comp_int (V : ℝ → ℝ) (hV : Continuous V) (A : ℝ) (hA : ∀ w, |V w| ≤ A + K M * |w|)
    (z : ℝ) : IntegrableOn (fun x => V (z - x) * M.g x) (Ioi 0) := by
  have hb : IntegrableOn (fun x => (A + K M * |z|) * M.g x + K M * (x * M.g x)) (Ioi 0) :=
    ((g_int M).const_mul _).add (M.g_mean.const_mul _)
  refine hb.mono' ?_ ?_
  · exact ((hV.comp (continuous_const.sub continuous_id)).aestronglyMeasurable).mul
      (M.g_cont.aestronglyMeasurable measurableSet_Ioi)
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun x hx => ?_)
    have hx' : (0:ℝ) < x := hx
    have hg := g_nonneg M hx
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hg]
    have h1 := hA (z - x)
    have h2 : |z - x| ≤ |z| + x := by
      calc |z - x| ≤ |z| + |x| := abs_sub _ _
        _ = |z| + x := by rw [abs_of_pos hx']
    have h3 : |V (z - x)| ≤ A + K M * |z| + K M * x := by
      have := mul_le_mul_of_nonneg_left h2 (K_nonneg M); linarith
    have := mul_le_mul_of_nonneg_right h3 hg
    linarith

lemma f_growth (n : ℕ) (hn : 1 ≤ n) (w : ℝ) : |M.f n w| ≤ |M.f n 0| + K M * |w| := by
  have := f_lip M n hn w 0
  rw [sub_zero] at this
  have := abs_sub_abs_le_abs_sub (M.f n w) (M.f n 0)
  linarith

lemma f_int (n : ℕ) (hn : 1 ≤ n) (z : ℝ) :
    IntegrableOn (fun x => M.f n (z - x) * M.g x) (Ioi 0) :=
  comp_int M _ (f_cont M n hn) _ (f_growth M n hn) z

lemma int_lower (n : ℕ) (hn : 1 ≤ n) (z : ℝ) :
    M.h * (z - 2 * ∫ x in Ioi (0:ℝ), x * M.g x) ≤ ∫ x in Ioi (0:ℝ), M.f n (z - x) * M.g x := by
  set μ := ∫ x in Ioi (0:ℝ), x * M.g x
  have hi : IntegrableOn (fun x => M.h * ((z - μ) - x) * M.g x) (Ioi 0) := by
    have : IntegrableOn (fun x => M.h * (((z - μ) - x) * M.g x)) (Ioi 0) :=
      (lin_int M (z - μ)).const_mul M.h
    refine this.congr_fun (fun x _ => by ring) measurableSet_Ioi
  have hval : ∫ x in Ioi (0:ℝ), M.h * ((z - μ) - x) * M.g x = M.h * (z - 2 * μ) := by
    have : (fun x => M.h * ((z - μ) - x) * M.g x) = fun x => M.h * (((z - μ) - x) * M.g x) := by
      funext x; ring
    rw [this, integral_const_mul, lin_integral]; ring
  rw [← hval]
  apply setIntegral_mono_on hi (f_int M n hn z) measurableSet_Ioi
  intro x hx
  apply mul_le_mul_of_nonneg_right _ (g_nonneg M hx)
  have := L_ge M (z - x)
  have := f_ge_L M n hn (z - x)
  have : M.h * ((z - μ) - x) = M.h * (z - x - μ) := by ring
  linarith

end MU87



namespace MU87
open ServiceParts.BaseStock

variable (M : Model)

lemma dct (f : ℝ → ℝ) (hf : ∀ y : ℝ, Tendsto (fun n : ℕ => M.f n y) atTop (𝓝 (f y)))
    (m : ℕ → ℕ) (hm : Tendsto m atTop atTop) (zs : ℕ → ℝ) (z : ℝ)
    (hz : Tendsto zs atTop (𝓝 z)) :
    Tendsto (fun k => ∫ x in Ioi (0:ℝ), M.f (m k) (zs k - x) * M.g x) atTop
      (𝓝 (∫ x in Ioi (0:ℝ), f (z - x) * M.g x)) := by
  have hm1 : ∀ᶠ k in atTop, 1 ≤ m k := hm.eventually (eventually_ge_atTop 1)
  have hB : ∀ᶠ k in atTop, |M.f (m k) 0| < |f 0| + 1 :=
    (tendsto_order.1 ((hf 0).comp hm).abs).2 _ (lt_add_one _)
  have hZ : ∀ᶠ k in atTop, |zs k| < |z| + 1 :=
    (tendsto_order.1 hz.abs).2 _ (lt_add_one _)
  set B := |f 0| + 1
  set Z := |z| + 1
  have hK := K_nonneg M
  apply tendsto_integral_filter_of_dominated_convergence
    (fun x => (B + K M * Z) * M.g x + K M * (x * M.g x))
  · filter_upwards [hm1] with k hk
    exact ((f_cont M _ hk).comp (continuous_const.sub continuous_id)).aestronglyMeasurable.mul
      (M.g_cont.aestronglyMeasurable measurableSet_Ioi)
  · filter_upwards [hm1, hB, hZ] with k hk hBk hZk
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun x hx => ?_)
    have hx' : (0:ℝ) < x := hx
    have hg := g_nonneg M hx
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hg]
    have h1 := f_growth M _ hk (zs k - x)
    have h2 : |zs k - x| ≤ Z + x := by
      calc |zs k - x| ≤ |zs k| + |x| := abs_sub _ _
        _ ≤ Z + x := by rw [abs_of_pos hx']; linarith
    have h3 : |M.f (m k) (zs k - x)| ≤ B + K M * Z + K M * x := by
      have := mul_le_mul_of_nonneg_left h2 hK; linarith
    have := mul_le_mul_of_nonneg_right h3 hg
    linarith
  · exact ((g_int M).const_mul _).add (M.g_mean.const_mul _)
  · refine Eventually.of_forall fun x => ?_
    apply Tendsto.mul_const
    have h2 : Tendsto (fun k => M.f (m k) (z - x)) atTop (𝓝 (f (z - x))) := (hf (z - x)).comp hm
    have h1 : Tendsto (fun k => M.f (m k) (zs k - x) - M.f (m k) (z - x)) atTop (𝓝 0) := by
      have hc : Tendsto (fun k => K M * |zs k - z|) atTop (𝓝 0) := by
        have := ((hz.sub_const z).abs).const_mul (K M)
        simpa using this
      apply squeeze_zero_norm' _ hc
      filter_upwards [hm1] with k hk
      rw [Real.norm_eq_abs]
      have := f_lip M _ hk (zs k - x) (z - x)
      rwa [show zs k - x - (z - x) = zs k - z by ring] at this
    have := h1.add h2
    simpa using this

end MU87



theorem solution (M : ServiceParts.BaseStock.Model)
    (f : ℝ → ℝ) (hf : ∀ y : ℝ, Tendsto (fun n : ℕ => M.f n y) atTop (𝓝 (f y))) :
    ∃ s : ℝ, ∀ y : ℝ, ∀ u : ℝ, 0 ≤ u →
      M.stageCost f y (max 0 (s - y)) ≤ M.stageCost f y u := by
  obtain ⟨N, hN2, hN⟩ := (ServiceParts.BaseStock.order_up_to_optimal M).2
  choose s hs using hN
  set t : ℕ → ℝ := fun k => s (k + N) (by omega) with ht_def
  have ht : ∀ k, M.IsOrderUpToOptimal (k + N) (t k) := fun k => hs _ _
  set m : ℕ → ℕ := fun k => k + N - 1 with hm_def
  have hm : Tendsto m atTop atTop :=
    tendsto_atTop_atTop.2 fun b => ⟨b + 1, fun a ha => by simp only [hm_def]; omega⟩
  have key : ∀ k y u, 0 ≤ u →
      M.stageCost (M.f (m k)) y (max 0 (t k - y)) ≤ M.stageCost (M.f (m k)) y u :=
    fun k y u hu => (ht k y).2 u hu
  have hm1 : ∀ k, 1 ≤ m k := fun k => by simp only [hm_def]; omega
  have hmono : Monotone t := by
    refine monotone_nat_of_le_succ fun k => ?_
    have h2 := ht (k + 1)
    rw [show k + 1 + N = k + N + 1 by ring] at h2
    exact ServiceParts.BaseStock.property_a M (k + N) (by omega) _ _ (ht k) h2
  -- boundedness
  set μ := ∫ x in Ioi (0:ℝ), x * M.g x
  have hI0 := MU87.dct M f hf m hm (fun _ => 0) 0 tendsto_const_nhds
  set C := ∫ x in Ioi (0:ℝ), f (0 - x) * M.g x
  have hev : ∀ᶠ k in atTop, t k ≤ (C + 1 + 2 * M.h * μ) / M.h := by
    filter_upwards [(tendsto_order.1 hI0).2 _ (lt_add_one C)] with k hk
    set a := max 0 (t k - 0)
    have h1 := key k 0 0 le_rfl
    unfold ServiceParts.BaseStock.Model.stageCost at h1
    have ha : 0 ≤ a := le_max_left _ _
    have hca : 0 ≤ M.c * a := mul_nonneg M.c_nonneg ha
    have hlow := MU87.int_lower M (m k) (hm1 k) (0 + a)
    set P := ∫ x in Ioi (0:ℝ), M.f (m k) (0 + a - x) * M.g x
    set Q := ∫ x in Ioi (0:ℝ), M.f (m k) (0 + 0 - x) * M.g x
    have hQ : Q < C + 1 := by simpa [Q] using hk
    have hPQ : M.α * P ≤ M.α * Q := by linarith
    have hPQ' : P ≤ Q := le_of_mul_le_mul_left hPQ M.α_pos
    have : M.h * a < C + 1 + 2 * M.h * μ := by
      have : M.h * (0 + a - 2 * μ) = M.h * a - 2 * M.h * μ := by ring
      linarith
    have hta : t k ≤ a := by simp [a]
    calc t k ≤ a := hta
      _ ≤ (C + 1 + 2 * M.h * μ) / M.h := by
        rw [le_div_iff₀ M.h_pos]; linarith [mul_comm a M.h]
  have hbdd : BddAbove (range t) := by
    obtain ⟨k0, hk0⟩ := eventually_atTop.1 hev
    refine ⟨(C + 1 + 2 * M.h * μ) / M.h, ?_⟩
    rintro _ ⟨k, rfl⟩
    exact (hmono (le_max_left k k0)).trans (hk0 _ (le_max_right _ _))
  have hconv := tendsto_atTop_ciSup hmono hbdd
  refine ⟨⨆ k, t k, fun y u hu => ?_⟩
  have ha : Tendsto (fun k => max 0 (t k - y)) atTop (𝓝 (max 0 ((⨆ k, t k) - y))) :=
    tendsto_const_nhds.max (hconv.sub_const y)
  have hintL := MU87.dct M f hf m hm (fun k => y + max 0 (t k - y)) _
    (tendsto_const_nhds.add ha)
  have hintR := MU87.dct M f hf m hm (fun _ => y + u) _ tendsto_const_nhds
  have hL : Tendsto (fun k => M.stageCost (M.f (m k)) y (max 0 (t k - y))) atTop
      (𝓝 (M.stageCost f y (max 0 ((⨆ k, t k) - y)))) := by
    unfold ServiceParts.BaseStock.Model.stageCost
    exact ((tendsto_const_nhds.mul ha).add tendsto_const_nhds).add
      (tendsto_const_nhds.mul hintL)
  have hR : Tendsto (fun k => M.stageCost (M.f (m k)) y u) atTop
      (𝓝 (M.stageCost f y u)) := by
    unfold ServiceParts.BaseStock.Model.stageCost
    exact tendsto_const_nhds.add (tendsto_const_nhds.mul hintR)
  exact le_of_tendsto_of_tendsto' hL hR (fun k => key k y u hu)
