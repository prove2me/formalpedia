-- Prove2me | solution 1 for ModernOnlineLearning.SaddlePoint.theorem_15_26
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T14:08:33.262101+00:00
-- url     : https://prove2.me/submissions/c41cf5ee-948b-4897-af68-d5a022bf7968

import Mathlib
import Definitions.Def_ModernOnlineLearning_SaddlePoint_Setting

set_option autoImplicit false

namespace RRAux_SP1526
open Filter Topology Finset

section gen
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma slope_tendsto (f : E → ℝ) (a v : E) (D : E →L[ℝ] ℝ) (hf : HasFDerivAt f D a) :
    Tendsto (fun s : ℝ => s⁻¹ * (f (a + s • v) - f a)) (𝓝[>] 0) (𝓝 (D v)) := by
  have h1 : HasDerivAt (fun s : ℝ => a + s • v) v 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const v).const_add a
  have h3 : HasFDerivAt f D ((fun s : ℝ => a + s • v) 0) := by simpa using hf
  have h2 := (h3.comp_hasDerivAt (0:ℝ) h1).tendsto_slope_zero_right
  simpa [Function.comp_def] using h2

lemma grad_ineq (V : Set E) (φ : E → ℝ) (hc : ConvexOn ℝ V φ) (x w : E) (hx : x ∈ V)
    (hw : w ∈ V) (D : E →L[ℝ] ℝ) (hd : HasFDerivAt φ D x) : φ x + D (w - x) ≤ φ w := by
  have hT := slope_tendsto φ x (w - x) D hd
  have key : D (w - x) ≤ φ w - φ x := by
    refine le_of_tendsto hT ?_
    have hIoo : Set.Ioo (0:ℝ) 1 ∈ 𝓝[>] (0:ℝ) := Ioo_mem_nhdsGT (by norm_num)
    filter_upwards [hIoo] with s hs
    have hs0 : 0 < s := hs.1
    have h := hc.2 hx hw (sub_nonneg.mpr hs.2.le) hs.1.le (by ring)
    have e : (1 - s) • x + s • w = x + s • (w - x) := by
      rw [smul_sub, sub_smul, one_smul]; abel
    rw [e, smul_eq_mul, smul_eq_mul] at h
    rw [inv_mul_le_iff₀ hs0]
    linear_combination h
  linarith

lemma sc_min (V : Set E) (ψ : E → ℝ) (lam : ℝ) (hst : StrongConvexOn V lam ψ)
    (h : E →L[ℝ] ℝ) (z : E) (hz : z ∈ V) (hmin : ∀ w ∈ V, ψ z + h z ≤ ψ w + h w)
    (w : E) (hw : w ∈ V) : ψ z + h z + lam / 2 * ‖w - z‖ ^ 2 ≤ ψ w + h w := by
  have hK : Tendsto (fun s : ℝ => (1 - s) * (lam / 2 * ‖w - z‖ ^ 2)) (𝓝[>] 0)
      (𝓝 (lam / 2 * ‖w - z‖ ^ 2)) := by
    have : Tendsto (fun s : ℝ => (1 - s) * (lam / 2 * ‖w - z‖ ^ 2)) (𝓝 0)
        (𝓝 ((1 - 0) * (lam / 2 * ‖w - z‖ ^ 2))) :=
      ((continuous_const.sub continuous_id).mul continuous_const).tendsto 0
    simpa using this.mono_left nhdsWithin_le_nhds
  have key : lam / 2 * ‖w - z‖ ^ 2 ≤ ψ w + h w - (ψ z + h z) := by
    refine le_of_tendsto hK ?_
    have hIoo : Set.Ioo (0:ℝ) 1 ∈ 𝓝[>] (0:ℝ) := Ioo_mem_nhdsGT (by norm_num)
    filter_upwards [hIoo] with s hs
    have hs0 : 0 < s := hs.1
    have hp : s • w + (1 - s) • z ∈ V := hst.1 hw hz hs.1.le (sub_nonneg.mpr hs.2.le) (by ring)
    have h1 := hst.2 hw hz hs.1.le (sub_nonneg.mpr hs.2.le) (by ring)
    have h2 := hmin _ hp
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul] at h2
    rw [smul_eq_mul, smul_eq_mul] at h1
    have h3 : s * ((1 - s) * (lam / 2 * ‖w - z‖ ^ 2)) ≤ s * (ψ w + h w - (ψ z + h z)) := by
      nlinarith
    exact le_of_mul_le_mul_left h3 hs0
  linarith

lemma young (a d lam : ℝ) (hlam : 0 < lam) :
    a * d - lam / 2 * d ^ 2 ≤ a ^ 2 / lam - lam / 4 * d ^ 2 := by
  have h : a ^ 2 / lam - lam / 4 * d ^ 2 - (a * d - lam / 2 * d ^ 2)
      = (2 * a - lam * d) ^ 2 / (4 * lam) := by
    field_simp; ring
  have : 0 ≤ (2 * a - lam * d) ^ 2 / (4 * lam) := by positivity
  linarith

lemma young' (a d lam : ℝ) (hlam : 0 < lam) :
    a * d - lam / 2 * d ^ 2 ≤ a ^ 2 / lam := by
  have := young a d lam hlam
  have : 0 ≤ lam / 4 * d ^ 2 := by positivity
  linarith

lemma dual (g : E →L[ℝ] ℝ) (v : E) : g v ≤ ‖g‖ * ‖v‖ :=
  (le_abs_self _).trans ((Real.norm_eq_abs _).symm ▸ g.le_opNorm v)

end gen

lemma coef (a b c α lX lY : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hα : 0 < α)
    (hlX : 0 < lX) (hlY : 0 < lY)
    (hX : 2 * Real.sqrt 2 * (a + b * α) ≤ lX) (hY : 2 * Real.sqrt 2 * (c + b / α) ≤ lY) :
    2 * a ^ 2 / lX + 2 * b ^ 2 / lY ≤ lX / 4 := by
  set k := 2 * Real.sqrt 2 with hk
  have hk2 : k ^ 2 = 8 := by
    rw [hk, mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]; norm_num
  have hk0 : 0 < k := by positivity
  -- k b ≤ α lY
  have hb1 : k * b ≤ α * lY := by
    have : k * (b / α) ≤ lY := by
      have : 0 ≤ k * c := by positivity
      nlinarith
    rw [mul_div_assoc'] at this
    rw [div_le_iff₀ hα] at this; linarith
  -- 2 b² / lY ≤ k (b α) / 4
  have hB : 2 * b ^ 2 / lY ≤ k * (b * α) / 4 := by
    rw [div_le_iff₀ hlY]
    have : k * b * b ≤ α * lY * b := mul_le_mul_of_nonneg_right hb1 hb
    -- 2 b² = k² b² / 4 ≤ k b α lY / 4
    nlinarith
  -- 8 a² ≤ lX² - k (bα) lX
  have hA : 2 * a ^ 2 / lX ≤ lX / 4 - k * (b * α) / 4 := by
    rw [div_le_iff₀ hlX]
    have hs : k * (a + b * α) ≤ lX := hX
    have h1 : 0 ≤ lX - k * (b * α) - k * a := by linarith
    have h2 : k * (a + b * α) * (k * a) ≤ lX * (lX - k * (b * α)) := by
      have h3 : k * a ≤ lX - k * (b * α) := by linarith
      have h4 : 0 ≤ k * a := by positivity
      exact mul_le_mul hs h3 h4 hlX.le
    have h5 : k * (a + b * α) * (k * a) = 8 * a ^ 2 + 8 * a * (b * α) := by
      rw [show k * (a + b * α) * (k * a) = k ^ 2 * (a ^ 2 + a * (b * α)) by ring, hk2]; ring
    have h6 : 0 ≤ a * (b * α) := by positivity
    nlinarith
  linarith

lemma per_step (a b c α lX lY p q A B : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hα : 0 < α) (hlX : 0 < lX) (hlY : 0 < lY)
    (hX : 2 * Real.sqrt 2 * (a + b * α) ≤ lX) (hY : 2 * Real.sqrt 2 * (c + b / α) ≤ lY)
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hA0 : 0 ≤ A) (hB0 : 0 ≤ B)
    (hA : A ≤ a * p + b * q) (hB : B ≤ b * p + c * q) :
    A ^ 2 / lX + B ^ 2 / lY ≤ lX / 4 * p ^ 2 + lY / 4 * q ^ 2 := by
  have c1 := coef a b c α lX lY ha hb hc hα hlX hlY hX hY
  have c2 := coef c b a α⁻¹ lY lX hc hb ha (inv_pos.mpr hα) hlY hlX
    (by rw [← div_eq_mul_inv]; exact hY) (by rw [div_inv_eq_mul]; exact hX)
  have hA2 : A ^ 2 ≤ 2 * a ^ 2 * p ^ 2 + 2 * b ^ 2 * q ^ 2 := by
    have : A ^ 2 ≤ (a * p + b * q) ^ 2 := pow_le_pow_left₀ hA0 hA 2
    nlinarith [sq_nonneg (a * p - b * q)]
  have hB2 : B ^ 2 ≤ 2 * b ^ 2 * p ^ 2 + 2 * c ^ 2 * q ^ 2 := by
    have : B ^ 2 ≤ (b * p + c * q) ^ 2 := pow_le_pow_left₀ hB0 hB 2
    nlinarith [sq_nonneg (b * p - c * q)]
  have e1 : A ^ 2 / lX ≤ (2 * a ^ 2 * p ^ 2 + 2 * b ^ 2 * q ^ 2) / lX :=
    div_le_div_of_nonneg_right hA2 hlX.le
  have e2 : B ^ 2 / lY ≤ (2 * b ^ 2 * p ^ 2 + 2 * c ^ 2 * q ^ 2) / lY :=
    div_le_div_of_nonneg_right hB2 hlY.le
  have e3 : (2 * a ^ 2 * p ^ 2 + 2 * b ^ 2 * q ^ 2) / lX + (2 * b ^ 2 * p ^ 2 + 2 * c ^ 2 * q ^ 2) / lY
      = p ^ 2 * (2 * a ^ 2 / lX + 2 * b ^ 2 / lY) + q ^ 2 * (2 * c ^ 2 / lY + 2 * b ^ 2 / lX) := by
    ring
  have e4 : p ^ 2 * (2 * a ^ 2 / lX + 2 * b ^ 2 / lY) ≤ p ^ 2 * (lX / 4) :=
    mul_le_mul_of_nonneg_left c1 (by positivity)
  have e5 : q ^ 2 * (2 * c ^ 2 / lY + 2 * b ^ 2 / lX) ≤ q ^ 2 * (lY / 4) :=
    mul_le_mul_of_nonneg_left c2 (by positivity)
  nlinarith

lemma sum_shift (f : ℕ → ℝ) (k : ℕ) :
    ∑ t ∈ Icc 1 (k + 1), f t = f 1 + ∑ t ∈ Icc 1 k, f (t + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_Icc_succ_top (by omega)]
    ring

section ftrl
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The objective of round `t`. -/
noncomputable def Fo (ψ : E → ℝ) (g : ℕ → E →L[ℝ] ℝ) (t : ℕ) (w : E) : ℝ :=
  ψ w + g (t - 1) w + ∑ i ∈ Ico 1 t, g i w

lemma ftrl (V : Set E) (ψ : E → ℝ) (lam : ℝ) (hlam : 0 < lam) (hst : StrongConvexOn V lam ψ)
    (g : ℕ → E →L[ℝ] ℝ) (z : ℕ → E) (T : ℕ) (hT : 1 ≤ T)
    (hrun : ModernOnlineLearning.SaddlePoint.IsOptFTRLRun V ψ g z T) (u : E) (hu : u ∈ V) :
    ∑ t ∈ Icc 1 T, g t (z t - u) ≤ ψ u - ψ (z 1)
      + ∑ t ∈ Icc 1 T, ‖g t - g (t - 1)‖ ^ 2 / lam
      - lam / 4 * ∑ t ∈ Icc 1 (T - 1), ‖z t - z (t + 1)‖ ^ 2 := by
  obtain ⟨hg0, hstep⟩ := hrun
  have hzV : ∀ t ∈ Icc 1 T, z t ∈ V := fun t ht => (hstep t ht).1
  have hmin : ∀ t ∈ Icc 1 T, ∀ w ∈ V,
      Fo ψ g t (z t) + lam / 2 * ‖w - z t‖ ^ 2 ≤ Fo ψ g t w := by
    intro t ht w hw
    have hm := (hstep t ht)
    have e : ∀ w', Fo ψ g t w' = ψ w' + (g (t - 1) + ∑ i ∈ Ico 1 t, g i) w' := by
      intro w'; unfold Fo
      rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.sum_apply]; ring
    rw [e, e]
    refine sc_min V ψ lam hst _ (z t) hm.1 ?_ w hw
    intro w' hw'
    have := hm.2 w' hw'
    rw [← e, ← e]; exact this
  have hF1 : ∀ w, Fo ψ g 1 w = ψ w := by
    intro w; simp [Fo, hg0]
  have hFs : ∀ t, 1 ≤ t → ∀ w, Fo ψ g (t + 1) w = Fo ψ g t w + 2 * g t w - g (t - 1) w := by
    intro t ht w
    unfold Fo
    rw [Finset.sum_Ico_succ_top ht, Nat.add_sub_cancel]
    ring
  -- potential bound
  have hB : ∀ n, 1 ≤ n → n ≤ T →
      ∑ t ∈ Icc 1 n, g t (z t) - Fo ψ g n (z n) - (g n - g (n - 1)) (z n)
        ≤ -ψ (z 1) + ∑ t ∈ Icc 1 (n - 1), ((g t - g (t - 1)) (z t - z (t + 1))
            - lam / 2 * ‖z t - z (t + 1)‖ ^ 2) := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base =>
      intro _
      simp [hF1, hg0]
    | succ n hn ih =>
      intro hnT
      have ih' := ih (by omega)
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      have hm := hmin (k + 1) (by rw [Finset.mem_Icc]; omega) (z (k + 1 + 1))
        (hzV _ (by rw [Finset.mem_Icc]; omega))
      have hf := hFs (k + 1) (by omega) (z (k + 1 + 1))
      simp only [Nat.add_sub_cancel] at ih' hf ⊢
      rw [Finset.sum_Icc_succ_top (show 1 ≤ k + 1 + 1 by omega) (fun t => g t (z t)),
        Finset.sum_Icc_succ_top (show 1 ≤ k + 1 by omega)
          (fun t => (g t - g (t - 1)) (z t - z (t + 1)) - lam / 2 * ‖z t - z (t + 1)‖ ^ 2)]
      simp only [Nat.add_sub_cancel]
      simp only [ContinuousLinearMap.sub_apply, map_sub] at ih' ⊢
      rw [norm_sub_rev] at hm
      linarith
  -- final
  obtain ⟨k, rfl⟩ : ∃ k, T = k + 1 := ⟨T - 1, by omega⟩
  have hBT := hB (k + 1) (by omega) le_rfl
  have hmT := hmin (k + 1) (by rw [Finset.mem_Icc]; omega) u hu
  simp only [Nat.add_sub_cancel] at hBT hmT ⊢
  have hsumu : ∑ t ∈ Icc 1 (k + 1), g t u = Fo ψ g (k + 1) u - ψ u - g k u + g (k + 1) u := by
    unfold Fo
    rw [Nat.add_sub_cancel, Finset.Ico_add_one_right_eq_Icc, Finset.sum_Icc_succ_top (by omega : 1 ≤ k + 1)]
    ring
  have hsplit : ∑ t ∈ Icc 1 (k + 1), g t (z t - u)
      = ∑ t ∈ Icc 1 (k + 1), g t (z t) - ∑ t ∈ Icc 1 (k + 1), g t u := by
    rw [← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro t _; rw [map_sub]
  rw [hsplit, hsumu]
  -- stage terms
  have hstage : ∑ t ∈ Icc 1 k, ((g t - g (t - 1)) (z t - z (t + 1))
      - lam / 2 * ‖z t - z (t + 1)‖ ^ 2) ≤
      ∑ t ∈ Icc 1 k, (‖g t - g (t - 1)‖ ^ 2 / lam - lam / 4 * ‖z t - z (t + 1)‖ ^ 2) := by
    apply Finset.sum_le_sum; intro t _
    have h1 := dual (g t - g (t - 1)) (z t - z (t + 1))
    have h2 := young ‖g t - g (t - 1)‖ ‖z t - z (t + 1)‖ lam hlam
    linarith
  have hlast : (g (k + 1) - g k) (z (k + 1) - u) - lam / 2 * ‖u - z (k + 1)‖ ^ 2
      ≤ ‖g (k + 1) - g k‖ ^ 2 / lam := by
    have h1 := dual (g (k + 1) - g k) (z (k + 1) - u)
    have h2 := young' ‖g (k + 1) - g k‖ ‖z (k + 1) - u‖ lam hlam
    rw [norm_sub_rev u]
    linarith
  have hR : ∑ t ∈ Icc 1 k, (‖g t - g (t - 1)‖ ^ 2 / lam - lam / 4 * ‖z t - z (t + 1)‖ ^ 2)
      = ∑ t ∈ Icc 1 k, ‖g t - g (t - 1)‖ ^ 2 / lam
        - lam / 4 * ∑ t ∈ Icc 1 k, ‖z t - z (t + 1)‖ ^ 2 := by
    rw [Finset.sum_sub_distrib, Finset.mul_sum]
  rw [hR] at hstage
  rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ k + 1) (fun t => ‖g t - g (t - 1)‖ ^ 2 / lam)]
  try simp only [Nat.add_sub_cancel]
  simp only [ContinuousLinearMap.sub_apply, map_sub] at hlast hBT hstage ⊢
  linarith

end ftrl

end RRAux_SP1526

namespace RRAux_SP1526
open Finset

lemma jensen_avg_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (V : Set E)
    (φ : E → ℝ) (hc : ConvexOn ℝ V φ) (z : ℕ → E) (T : ℕ) (hT : 1 ≤ T)
    (hz : ∀ t ∈ Icc 1 T, z t ∈ V) :
    φ (ModernOnlineLearning.SaddlePoint.avg T z) ≤ (T : ℝ)⁻¹ * ∑ t ∈ Icc 1 T, φ (z t) := by
  unfold ModernOnlineLearning.SaddlePoint.avg
  rw [Finset.smul_sum, Finset.mul_sum]
  have hw : ∑ _t ∈ Icc 1 T, (T : ℝ)⁻¹ = 1 := by
    rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
    have : (T : ℝ) ≠ 0 := by exact_mod_cast (show T ≠ 0 by omega)
    simp [this]
  have := hc.map_sum_le (t := Icc 1 T) (w := fun _ => (T : ℝ)⁻¹) (p := z)
    (fun _ _ => by positivity) hw hz
  simpa [smul_eq_mul] using this

end RRAux_SP1526

open ModernOnlineLearning.SaddlePoint in
-- Theorem 15.26.
theorem solution {EX EY : Type*}
    [NormedAddCommGroup EX] [NormedSpace ℝ EX] [FiniteDimensional ℝ EX]
    [NormedAddCommGroup EY] [NormedSpace ℝ EY] [FiniteDimensional ℝ EY]
    (X : Set EX) (Y : Set EY) (f : EX → EY → ℝ)
    (gx : EX → EY → EX →L[ℝ] ℝ) (gy : EX → EY → EY →L[ℝ] ℝ)
    (ψX : EX → ℝ) (ψY : EY → ℝ) (x : ℕ → EX) (y : ℕ → EY)
    (LXX LXY LYY lamX lamY alpha : ℝ) (T : ℕ)
    (hT : 1 ≤ T) (hXne : X.Nonempty) (hYne : Y.Nonempty)
    (hXclosed : IsClosed X) (hYclosed : IsClosed Y)
    (hX : Convex ℝ X) (hY : Convex ℝ Y)
    (hfx : ∀ v ∈ Y, ConvexOn ℝ X (fun w => f w v))
    (hfy : ∀ u ∈ X, ConcaveOn ℝ Y (f u))
    (hLXX : 0 ≤ LXX) (hLXY : 0 ≤ LXY) (hLYY : 0 ≤ LYY)
    (halpha : 0 < alpha) (hlamX : 0 < lamX) (hlamY : 0 < lamY)
    (hlowerX : 2 * Real.sqrt 2 * (LXX + LXY * alpha) ≤ lamX)
    (hlowerY : 2 * Real.sqrt 2 * (LYY + LXY / alpha) ≤ lamY)
    (hψX : StrongConvexOn X lamX ψX) (hψY : StrongConvexOn Y lamY ψY)
    (hsmooth : IsSmoothSaddleOn X Y f gx gy LXX LXY LYY)
    (hrun : IsOptFTRLSaddleRun X Y ψX ψY gx gy x y T)
    (xm : EX) (ym : EY)
    (hmin : IsMinOn X (fun w => f w (avg T y)) xm)
    (hmax : IsMaxOn Y (f (avg T x)) ym) :
    f (avg T x) ym - f xm (avg T y) ≤
      (ψX xm - ψX (x 1) + ψY ym - ψY (y 1) +
        ‖gx (x 1) (y 1)‖ ^ 2 / lamX +
        ‖gy (x 1) (y 1)‖ ^ 2 / lamY) / T := by
  obtain ⟨U, _, hXYU, hder, hLxx, hLxy1, hLxy2, hLyy⟩ := hsmooth
  obtain ⟨hrX, hrY⟩ := hrun
  have hxX : ∀ t ∈ Finset.Icc 1 T, x t ∈ X := fun t ht => (hrX.2 t ht).1
  have hyY : ∀ t ∈ Finset.Icc 1 T, y t ∈ Y := fun t ht => (hrY.2 t ht).1
  have hxm : xm ∈ X := hmin.1
  have hym : ym ∈ Y := hmax.1
  have RX := RRAux_SP1526.ftrl X ψX lamX hlamX hψX _ x T hT hrX xm hxm
  have RY := RRAux_SP1526.ftrl Y ψY lamY hlamY hψY _ y T hT hrY ym hym
  -- Jensen
  have JX := RRAux_SP1526.jensen_avg_le X (fun w => f w ym) (hfx ym hym) x T hT hxX
  have JY := RRAux_SP1526.jensen_avg_le Y (fun w => -(f xm w)) (hfy xm hxm).neg y T hT hyY
  simp only [Finset.sum_neg_distrib] at JY
  -- per-round gradient inequalities
  have hround : ∀ t ∈ Finset.Icc 1 T, f (x t) ym - f xm (y t) ≤
      (if t = 0 then 0 else gx (x t) (y t)) (x t - xm)
        + (if t = 0 then 0 else -gy (x t) (y t)) (y t - ym) := by
    intro t ht
    have ht0 : t ≠ 0 := by rw [Finset.mem_Icc] at ht; omega
    simp only [ht0, if_false]
    have hp := hder (x t, y t) (hXYU ⟨hxX t ht, hyY t ht⟩)
    have g1 := RRAux_SP1526.grad_ineq X (fun w => f w (y t)) (hfx (y t) (hyY t ht)) (x t) xm
      (hxX t ht) hxm (gx (x t) (y t)) hp.1
    have g2 := RRAux_SP1526.grad_ineq Y (fun w => -(f (x t) w)) (hfy (x t) (hxX t ht)).neg
      (y t) ym (hyY t ht) hym (-gy (x t) (y t)) hp.2.neg
    try simp only at g1 g2
    have e1 : gx (x t) (y t) (xm - x t) = - gx (x t) (y t) (x t - xm) := by
      rw [← map_neg, neg_sub]
    have e2 : (-gy (x t) (y t)) (ym - y t) = - (-gy (x t) (y t)) (y t - ym) := by
      rw [← map_neg, neg_sub]
    linarith
  have hsumr := Finset.sum_le_sum hround
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib] at hsumr
  -- coupling of the stage terms
  obtain ⟨k, rfl⟩ : ∃ k, T = k + 1 := ⟨T - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at RX RY
  rw [RRAux_SP1526.sum_shift (fun t => ‖(if t = 0 then 0 else gx (x t) (y t))
      - (if t - 1 = 0 then 0 else gx (x (t - 1)) (y (t - 1)))‖ ^ 2 / lamX)] at RX
  rw [RRAux_SP1526.sum_shift (fun t => ‖(if t = 0 then 0 else -gy (x t) (y t))
      - (if t - 1 = 0 then 0 else -gy (x (t - 1)) (y (t - 1)))‖ ^ 2 / lamY)] at RY
  have hstep : ∀ t ∈ Finset.Icc 1 k,
      ‖(if t + 1 = 0 then 0 else gx (x (t + 1)) (y (t + 1)))
        - (if t + 1 - 1 = 0 then 0 else gx (x (t + 1 - 1)) (y (t + 1 - 1)))‖ ^ 2 / lamX
      + ‖(if t + 1 = 0 then 0 else -gy (x (t + 1)) (y (t + 1)))
        - (if t + 1 - 1 = 0 then 0 else -gy (x (t + 1 - 1)) (y (t + 1 - 1)))‖ ^ 2 / lamY
      ≤ lamX / 4 * ‖x t - x (t + 1)‖ ^ 2 + lamY / 4 * ‖y t - y (t + 1)‖ ^ 2 := by
    intro t ht
    have ht0 : t ≠ 0 := by rw [Finset.mem_Icc] at ht; omega
    have ht1 : t ∈ Finset.Icc 1 (k + 1) := by rw [Finset.mem_Icc] at ht ⊢; omega
    have ht2 : t + 1 ∈ Finset.Icc 1 (k + 1) := by rw [Finset.mem_Icc] at ht ⊢; omega
    simp only [Nat.add_sub_cancel, ht0, Nat.add_one_ne_zero, if_false]
    have hx1 := hxX t ht1; have hx2 := hxX (t + 1) ht2
    have hy1 := hyY t ht1; have hy2 := hyY (t + 1) ht2
    have hA : ‖gx (x (t + 1)) (y (t + 1)) - gx (x t) (y t)‖ ≤
        LXX * ‖x t - x (t + 1)‖ + LXY * ‖y t - y (t + 1)‖ := by
      have e : gx (x (t + 1)) (y (t + 1)) - gx (x t) (y t)
          = (gx (x (t + 1)) (y (t + 1)) - gx (x t) (y (t + 1)))
            + (gx (x t) (y (t + 1)) - gx (x t) (y t)) := by abel
      rw [e]
      refine (norm_add_le _ _).trans ?_
      have h1 := hLxx (x (t + 1)) hx2 (x t) hx1 (y (t + 1)) hy2
      have h2 := hLxy1 (x t) hx1 (y (t + 1)) hy2 (y t) hy1
      rw [norm_sub_rev (x (t + 1))] at h1
      rw [norm_sub_rev (y (t + 1))] at h2
      linarith
    have hB : ‖-gy (x (t + 1)) (y (t + 1)) - -gy (x t) (y t)‖ ≤
        LXY * ‖x t - x (t + 1)‖ + LYY * ‖y t - y (t + 1)‖ := by
      have e : -gy (x (t + 1)) (y (t + 1)) - -gy (x t) (y t)
          = -((gy (x (t + 1)) (y (t + 1)) - gy (x t) (y (t + 1)))
            + (gy (x t) (y (t + 1)) - gy (x t) (y t))) := by abel
      rw [e, norm_neg]
      refine (norm_add_le _ _).trans ?_
      have h1 := hLxy2 (x (t + 1)) hx2 (x t) hx1 (y (t + 1)) hy2
      have h2 := hLyy (x t) hx1 (y (t + 1)) hy2 (y t) hy1
      rw [norm_sub_rev (x (t + 1))] at h1
      rw [norm_sub_rev (y (t + 1))] at h2
      linarith
    exact RRAux_SP1526.per_step LXX LXY LYY alpha lamX lamY _ _ _ _ hLXX hLXY hLYY halpha
      hlamX hlamY hlowerX hlowerY (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
      (norm_nonneg _) hA hB
  have hcouple := Finset.sum_le_sum hstep
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    at hcouple
  have h1X : ‖(if (1:ℕ) = 0 then 0 else gx (x 1) (y 1))
      - (if (1:ℕ) - 1 = 0 then 0 else gx (x (1 - 1)) (y (1 - 1)))‖ ^ 2 / lamX
      = ‖gx (x 1) (y 1)‖ ^ 2 / lamX := by simp
  have h1Y : ‖(if (1:ℕ) = 0 then 0 else -gy (x 1) (y 1))
      - (if (1:ℕ) - 1 = 0 then 0 else -gy (x (1 - 1)) (y (1 - 1)))‖ ^ 2 / lamY
      = ‖gy (x 1) (y 1)‖ ^ 2 / lamY := by simp
  rw [h1X] at RX
  rw [h1Y] at RY
  have htot : (∑ t ∈ Finset.Icc 1 (k + 1), f (x t) ym - ∑ t ∈ Finset.Icc 1 (k + 1), f xm (y t))
      ≤ ψX xm - ψX (x 1) + ψY ym - ψY (y 1) + ‖gx (x 1) (y 1)‖ ^ 2 / lamX
        + ‖gy (x 1) (y 1)‖ ^ 2 / lamY := by
    linarith
  have hTpos : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
  have hfin : f (avg (k + 1) x) ym - f xm (avg (k + 1) y) ≤
      ((k + 1 : ℕ) : ℝ)⁻¹ * (∑ t ∈ Finset.Icc 1 (k + 1), f (x t) ym
        - ∑ t ∈ Finset.Icc 1 (k + 1), f xm (y t)) := by
    try simp only at JX JY
    rw [mul_sub]; linarith
  rw [div_eq_inv_mul]
  exact hfin.trans (mul_le_mul_of_nonneg_left htot (by positivity))

#print axioms solution
