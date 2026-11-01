-- Prove2me | solution 1 for KellyStochasticNetworks.LossLimits.fluctuation_exp_moment_bound
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T06:09:51.619997+00:00
-- url     : https://prove2.me/submissions/dacfaa42-49df-4a43-968c-d53cbd40d703

import Mathlib
import Definitions.Def_KellyStochasticNetworks_LossLimits_Laws
import Definitions.Def_KellyStochasticNetworks_LossLimits_Gaussian
import Definitions.Def_KellyStochasticNetworks_LossLimits_Optimization
import Definitions.Def_KellyLossNetworks_Primal_Problem
import Theorems.Thm_KellyStochasticNetworks_LossLimits_product_law_normalized
import Theorems.Thm_KellyStochasticNetworks_LossLimits_blocking_mode_limit

open MeasureTheory Filter Topology Complex
open scoped Real

namespace GLL

/-- `φ(w) = e^w - 1 - w`. -/
noncomputable def phi (w : ℂ) : ℂ := cexp w - 1 - w

lemma one_sub_cos_ge {b : ℝ} (hb : |b| ≤ π) : 2 / π ^ 2 * b ^ 2 ≤ 1 - Real.cos b := by
  wlog h0 : 0 ≤ b generalizing b
  · have := this (b := -b) (by rwa [abs_neg]) (by linarith)
    simpa [Real.cos_neg] using this
  rw [abs_of_nonneg h0] at hb
  have hsin : 2 / π * (b / 2) ≤ Real.sin (b / 2) :=
    Real.mul_le_sin (by linarith) (by linarith)
  have hc : Real.cos b = 1 - 2 * Real.sin (b / 2) ^ 2 := by
    rw [← Real.cos_two_mul_eq_one_sub]; congr 1; ring
  rw [hc]
  have h1 : 0 ≤ 2 / π * (b / 2) := by positivity
  have h2 : (2 / π * (b / 2)) ^ 2 ≤ Real.sin (b / 2) ^ 2 := pow_le_pow_left₀ h1 hsin 2
  have : (2 / π * (b / 2)) ^ 2 = b ^ 2 / π ^ 2 := by field_simp
  rw [this] at h2
  have : 2 / π ^ 2 * b ^ 2 = 2 * (b ^ 2 / π ^ 2) := by ring
  rw [this]; linarith

lemma re_phi (a b : ℝ) : (phi (a + b * I)).re = Real.exp a * Real.cos b - 1 - a := by
  simp [phi, Complex.exp_re]

lemma re_phi_le {a b : ℝ} (ha : |a| ≤ 1) :
    (phi (a + b * I)).re ≤ -Real.exp (-1) * (1 - Real.cos b) + a ^ 2 := by
  rw [re_phi]
  have h1 := Real.abs_exp_sub_one_sub_id_le ha
  have h2 : Real.exp (-1) ≤ Real.exp a := Real.exp_le_exp.2 (by linarith [(abs_le.1 ha).1])
  have h3 : 0 ≤ 1 - Real.cos b := by linarith [Real.cos_le_one b]
  have h4 : Real.exp a * Real.cos b - 1 - a =
      -Real.exp a * (1 - Real.cos b) + (Real.exp a - 1 - a) := by ring
  rw [h4]
  have : Real.exp (-1) * (1 - Real.cos b) ≤ Real.exp a * (1 - Real.cos b) :=
    mul_le_mul_of_nonneg_right h2 h3
  linarith [(abs_le.1 h1).2]

lemma phi_sub_sq_le {z : ℂ} (hz : ‖z‖ ≤ 1) : ‖phi z - z ^ 2 / 2‖ ≤ ‖z‖ ^ 3 := by
  have h := Complex.exp_bound hz (n := 3) (by norm_num)
  have he : phi z - z ^ 2 / 2 = cexp z - ∑ m ∈ Finset.range 3, z ^ m / (m.factorial : ℂ) := by
    simp [phi, Finset.sum_range_succ]; ring
  rw [he]
  refine le_trans h ?_
  have : ((Nat.succ 3 : ℕ) : ℝ) * ((Nat.factorial 3 : ℕ) * (3:ℕ) : ℝ)⁻¹ ≤ 1 := by
    norm_num [Nat.factorial]
  calc ‖z‖ ^ 3 * (((Nat.succ 3 : ℕ) : ℝ) * ((Nat.factorial 3 : ℕ) * (3:ℕ) : ℝ)⁻¹)
      ≤ ‖z‖ ^ 3 * 1 := by gcongr
    _ = ‖z‖ ^ 3 := mul_one _

lemma tendsto_inv_sqrt : Tendsto (fun N : ℕ => (Real.sqrt N)⁻¹) atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)

lemma phi_limit (w : ℂ) :
    Tendsto (fun N : ℕ => (N : ℂ) * phi (w / (Real.sqrt N : ℂ))) atTop (𝓝 (w ^ 2 / 2)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hb : Tendsto (fun N : ℕ => ‖w‖ ^ 3 * (Real.sqrt N)⁻¹) atTop (𝓝 0) := by
    simpa using tendsto_inv_sqrt.const_mul (‖w‖ ^ 3)
  refine squeeze_zero' (Eventually.of_forall fun N => norm_nonneg _) ?_ hb
  have hev : ∀ᶠ N : ℕ in atTop, ‖w‖ * (Real.sqrt N)⁻¹ ≤ 1 := by
    have := (tendsto_inv_sqrt.const_mul ‖w‖)
    rw [mul_zero] at this
    exact this.eventually (ge_mem_nhds (by norm_num))
  filter_upwards [hev, eventually_gt_atTop 0] with N hN hN0
  have hs : 0 < Real.sqrt N := Real.sqrt_pos.2 (by exact_mod_cast hN0)
  have hz : ‖w / (Real.sqrt N : ℂ)‖ = ‖w‖ * (Real.sqrt N)⁻¹ := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs, div_eq_mul_inv]
  have key := phi_sub_sq_le (z := w / (Real.sqrt N : ℂ)) (by rw [hz]; exact hN)
  have hNeq : (N : ℂ) = (Real.sqrt N : ℂ) ^ 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]; simp
  have : (N : ℂ) * phi (w / (Real.sqrt N : ℂ)) - w ^ 2 / 2 =
      (N : ℂ) * (phi (w / (Real.sqrt N : ℂ)) - (w / (Real.sqrt N : ℂ)) ^ 2 / 2) := by
    have hs' : (Real.sqrt N : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
    rw [hNeq]; field_simp
  rw [this, norm_mul]
  rw [hz] at key
  have hN' : ‖(N : ℂ)‖ = Real.sqrt N ^ 2 := by
    rw [Complex.norm_natCast, Real.sq_sqrt (Nat.cast_nonneg _)]
  rw [hN']
  calc Real.sqrt N ^ 2 * ‖phi (w / ↑√↑N) - (w / ↑√↑N) ^ 2 / 2‖
      ≤ Real.sqrt N ^ 2 * (‖w‖ * (Real.sqrt N)⁻¹) ^ 3 := by gcongr
    _ = ‖w‖ ^ 3 * (Real.sqrt N)⁻¹ := by field_simp

section compact
variable {d R : ℕ} (K : Fin d → Fin R → ℤ)

/-- `(Kᵀ s)_r`. -/
def KT (s : Fin d → ℝ) (r : Fin R) : ℝ := ∑ i, (K i r : ℝ) * s i

lemma KT_smul (c : ℝ) (s : Fin d → ℝ) (r : Fin R) : KT K (c • s) r = c * KT K s r := by
  simp only [KT, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => by ring)

lemma KT_cont (r : Fin R) : Continuous (fun s : Fin d → ℝ => KT K s r) := by
  unfold KT; fun_prop

lemma KT_add (s t : Fin d → ℝ) (r : Fin R) : KT K (s + t) r = KT K s r + KT K t r := by
  simp only [KT, Pi.add_apply, mul_add, Finset.sum_add_distrib]

/-- Bound `|(Kᵀ s)_r| ≤ Kmax ‖s‖`. -/
noncomputable def Kmax : ℝ := ∑ i, ∑ r, |(K i r : ℝ)|

lemma Kmax_nonneg : 0 ≤ Kmax K := by
  unfold Kmax; positivity

lemma abs_KT_le (s : Fin d → ℝ) (r : Fin R) : |KT K s r| ≤ Kmax K * ‖s‖ := by
  unfold KT Kmax
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum (fun i _ => ?_)
  rw [abs_mul]
  have h1 : |s i| ≤ ‖s‖ := by
    have := norm_le_pi_norm s i
    rwa [Real.norm_eq_abs] at this
  have h2 : |(K i r : ℝ)| ≤ ∑ r', |(K i r' : ℝ)| :=
    Finset.single_le_sum (f := fun r' => |(K i r' : ℝ)|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ r)
  calc |(K i r : ℝ)| * |s i| ≤ (∑ r', |(K i r' : ℝ)|) * ‖s‖ :=
        mul_le_mul h2 h1 (abs_nonneg _) (by positivity)

/-- Coercivity of `s ↦ ∑_r (Kᵀ s)_r²` when `Kᵀ` is injective. -/
lemma exists_coercive (hinj : ∀ s : Fin d → ℝ, (∀ r, KT K s r = 0) → s = 0) :
    ∃ lam : ℝ, 0 < lam ∧ ∀ s : Fin d → ℝ, lam * ‖s‖ ^ 2 ≤ ∑ r, KT K s r ^ 2 := by
  set f : (Fin d → ℝ) → ℝ := fun s => ∑ r, KT K s r ^ 2 with hf
  have hfc : Continuous f := by
    simp only [hf]; exact continuous_finsetSum _ (fun r _ => (KT_cont K r).pow 2)
  have hhom : ∀ (c : ℝ) s, f (c • s) = c ^ 2 * f s := by
    intro c s; simp only [hf, KT_smul, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun r _ => by ring)
  by_cases hne : (Metric.sphere (0 : Fin d → ℝ) 1).Nonempty
  · obtain ⟨s0, hs0, hmin⟩ := (isCompact_sphere (0 : Fin d → ℝ) 1).exists_isMinOn hne
      hfc.continuousOn
    have hs0n : ‖s0‖ = 1 := by simpa using hs0
    have hpos : 0 < f s0 := by
      rcases (Finset.sum_nonneg (fun r _ => sq_nonneg (KT K s0 r)) : 0 ≤ f s0).lt_or_eq with h | h
      · exact h
      · exfalso
        have hz : ∀ r, KT K s0 r = 0 := by
          intro r
          have := (Finset.sum_eq_zero_iff_of_nonneg (fun r _ => sq_nonneg (KT K s0 r))).1 h.symm r
            (Finset.mem_univ r)
          exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
        have := hinj s0 hz
        rw [this, norm_zero] at hs0n; exact zero_ne_one hs0n
    refine ⟨f s0, hpos, fun s => ?_⟩
    rcases eq_or_ne s 0 with rfl | hs
    · simp [hf, KT]
    · have hn : 0 < ‖s‖ := norm_pos_iff.2 hs
      have ht : ‖s‖⁻¹ • s ∈ Metric.sphere (0 : Fin d → ℝ) 1 := by
        simp [norm_smul, hn.ne']
      have h1 := hmin ht
      simp only [Set.mem_setOf_eq] at h1
      have h2 : f s = ‖s‖ ^ 2 * f (‖s‖⁻¹ • s) := by
        rw [hhom, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hn.ne', one_pow, one_mul]
      show f s0 * ‖s‖ ^ 2 ≤ f s
      rw [h2]; nlinarith [sq_nonneg ‖s‖]
  · refine ⟨1, one_pos, fun s => ?_⟩
    have : ‖s‖ = 0 := by
      by_contra h
      apply hne
      have hn : 0 < ‖s‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h)
      exact ⟨‖s‖⁻¹ • s, by simp [norm_smul, hn.ne']⟩
    rw [this]; simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero]
    exact Finset.sum_nonneg (fun r _ => sq_nonneg _)

/-- The torus box `[-π, π]^d`. -/
def Qbox (d : ℕ) : Set (Fin d → ℝ) := Set.pi Set.univ (fun _ => Set.Icc (-π) π)

/-- Away from the origin the phase function is bounded below on the box. -/
lemma exists_far_bound
    (hK : ∀ θ : Fin d → ℝ, (∀ r, ∃ m : ℤ, KT K θ r = 2 * π * m) → ∀ i, ∃ m : ℤ, θ i = 2 * π * m)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ θ ∈ Qbox d, δ ≤ ‖θ‖ → ε ≤ ∑ r, (1 - Real.cos (KT K θ r)) := by
  set T : Set (Fin d → ℝ) := Qbox d ∩ {θ | δ ≤ ‖θ‖} with hT
  have hTc : IsCompact T := by
    apply (isCompact_univ_pi (fun _ => isCompact_Icc)).inter_right
    exact isClosed_le continuous_const continuous_norm
  set F : (Fin d → ℝ) → ℝ := fun θ => ∑ r, (1 - Real.cos (KT K θ r)) with hF
  have hFc : Continuous F := by
    simp only [hF]
    exact continuous_finsetSum _ (fun r _ => continuous_const.sub
      (Real.continuous_cos.comp (KT_cont K r)))
  by_cases hne : T.Nonempty
  · obtain ⟨θ0, hθ0, hmin⟩ := hTc.exists_isMinOn hne hFc.continuousOn
    have hpos : 0 < F θ0 := by
      have hnn : ∀ r ∈ Finset.univ, 0 ≤ 1 - Real.cos (KT K θ0 r) :=
        fun r _ => by linarith [Real.cos_le_one (KT K θ0 r)]
      rcases (Finset.sum_nonneg hnn).lt_or_eq with h | h
      · exact h
      · exfalso
        have hz : ∀ r, ∃ m : ℤ, KT K θ0 r = 2 * π * m := by
          intro r
          have := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 h.symm r (Finset.mem_univ r)
          have hc : Real.cos (KT K θ0 r) = 1 := by linarith
          obtain ⟨n, hn⟩ := (Real.cos_eq_one_iff _).1 hc
          exact ⟨n, by rw [← hn]; ring⟩
        have hθ := hK θ0 hz
        have hzero : θ0 = 0 := by
          funext i
          obtain ⟨m, hm⟩ := hθ i
          have hb := hθ0.1 i (Set.mem_univ i)
          have hb1 : -π ≤ 2 * π * m := hm ▸ hb.1
          have hb2 : 2 * π * m ≤ π := hm ▸ hb.2
          have hm0 : m = 0 := by
            have h1 : (-1 : ℝ) ≤ 2 * m := by
              by_contra hc; push_neg at hc; nlinarith [Real.pi_pos]
            have h2 : (2 : ℝ) * m ≤ 1 := by
              by_contra hc; push_neg at hc; nlinarith [Real.pi_pos]
            have h1' : (-1 : ℤ) ≤ 2 * m := by exact_mod_cast h1
            have h2' : (2 : ℤ) * m ≤ 1 := by exact_mod_cast h2
            omega
          rw [hm, hm0]; simp
        have := hθ0.2
        simp only [Set.mem_setOf_eq, hzero, norm_zero] at this
        linarith
    exact ⟨F θ0, hpos, fun θ hθ hδθ => hmin ⟨hθ, hδθ⟩⟩
  · exact ⟨1, one_pos, fun θ hθ hδθ => absurd ⟨θ, hθ, hδθ⟩ hne⟩

end compact

section main
variable {d R : ℕ} (K : Fin d → Fin R → ℤ)

/-- The exponent `∑_r x_r φ(ζ_r/√N + i (Kᵀθ)_r)`. -/
noncomputable def Phi (x : Fin R → ℝ) (ζ : Fin R → ℂ) (N : ℕ) (θ : Fin d → ℝ) : ℂ :=
  ∑ r, (x r : ℂ) * phi (ζ r / (Real.sqrt N : ℂ) + I * (KT K θ r : ℂ))

/-- The limiting Gaussian integrand. -/
noncomputable def gaussF (xb : Fin R → ℝ) (ζ : Fin R → ℂ) (s : Fin d → ℝ) : ℂ :=
  cexp (∑ r, (xb r : ℂ) * (ζ r + I * (KT K s r : ℂ)) ^ 2 / 2)

noncomputable def gaussInt (xb : Fin R → ℝ) (ζ : Fin R → ℂ) : ℂ :=
  ∫ s, gaussF K xb ζ s

lemma phi_cont : Continuous phi := by unfold phi; fun_prop

lemma Phi_cont (x : Fin R → ℝ) (ζ : Fin R → ℂ) (N : ℕ) : Continuous (Phi K x ζ N) := by
  unfold Phi
  refine continuous_finsetSum _ (fun r _ => continuous_const.mul (phi_cont.comp ?_))
  exact continuous_const.add (continuous_const.mul
    (Complex.continuous_ofReal.comp (KT_cont K r)))

lemma exists_pos_lower (xb : Fin R → ℝ) (hxb : ∀ r, 0 < xb r) :
    ∃ m : ℝ, 0 < m ∧ ∀ r, m ≤ xb r := by
  classical
  let S : Finset ℝ := insert 1 (Finset.univ.image xb)
  have hS : S.Nonempty := ⟨1, Finset.mem_insert_self _ _⟩
  refine ⟨S.min' hS, ?_, fun r => S.min'_le _ (Finset.mem_insert_of_mem
    (Finset.mem_image_of_mem _ (Finset.mem_univ r)))⟩
  have := S.min'_mem hS
  rcases Finset.mem_insert.1 this with h | h
  · rw [h]; exact one_pos
  · obtain ⟨r, -, hr⟩ := Finset.mem_image.1 h
    rw [← hr]; exact hxb r

/-- one-term real-part bound -/
lemma re_term_le (ζr : ℂ) (xr t sN : ℝ) (hsN : 0 < sN) (ha : ‖ζr‖ / sN ≤ 1) (hxr : 0 ≤ xr) :
    ((xr : ℂ) * phi (ζr / (sN : ℂ) + I * (t : ℂ))).re ≤
      xr * (ζr.re / sN) ^ 2 - xr * Real.exp (-1) * (1 - Real.cos (ζr.im / sN + t)) := by
  have heq : ζr / (sN : ℂ) + I * (t : ℂ) = ((ζr.re / sN : ℝ) : ℂ) + ((ζr.im / sN + t : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp [Complex.div_re, Complex.div_im]
  have hre : ((xr : ℂ) * phi (ζr / (sN : ℂ) + I * (t : ℂ))).re =
      xr * (phi (ζr / (sN : ℂ) + I * (t : ℂ))).re := by
    simp [Complex.mul_re]
  rw [hre, heq]
  have habs : |ζr.re / sN| ≤ 1 := by
    rw [abs_div, abs_of_pos hsN]
    exact le_trans (div_le_div_of_nonneg_right (Complex.abs_re_le_norm ζr) hsN.le) ha
  have := re_phi_le (b := ζr.im / sN + t) habs
  nlinarith [mul_le_mul_of_nonneg_left this hxr]

lemma norm_cexp_le_of_re_le {z : ℂ} {c : ℝ} (h : z.re ≤ c) : ‖cexp z‖ ≤ Real.exp c := by
  rw [Complex.norm_exp]; exact Real.exp_le_exp.2 h

lemma Phi_scaled (x : Fin R → ℝ) (ζ : Fin R → ℂ) (N : ℕ) (hN : 0 < N) (s : Fin d → ℝ) :
    Phi K x ζ N ((Real.sqrt N)⁻¹ • s) =
      ∑ r, (x r : ℂ) * phi ((ζ r + I * (KT K s r : ℂ)) / (Real.sqrt N : ℂ)) := by
  unfold Phi
  refine Finset.sum_congr rfl (fun r _ => ?_)
  congr 2
  rw [KT_smul]
  have hs : (Real.sqrt N : ℂ) ≠ 0 := by
    have : 0 < Real.sqrt N := Real.sqrt_pos.2 (by exact_mod_cast hN)
    exact_mod_cast this.ne'
  push_cast
  field_simp

lemma sqrt_pow_exp_decay (d : ℕ) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun N : ℕ => Real.sqrt N ^ d * Real.exp (-c * N)) atTop (𝓝 0) := by
  have h1 := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero d).comp
    ((tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop hc)
  have h2 := h1.const_mul ((c ^ d)⁻¹)
  rw [mul_zero] at h2
  refine squeeze_zero' (Eventually.of_forall fun N => by positivity) ?_ h2
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN' : (1:ℝ) ≤ N := by exact_mod_cast hN
  simp only [Function.comp]
  have hs : Real.sqrt N ≤ N := by
    rw [Real.sqrt_le_left (by linarith)]; nlinarith
  have : Real.sqrt N ^ d ≤ (N:ℝ) ^ d := pow_le_pow_left₀ (Real.sqrt_nonneg _) hs d
  calc Real.sqrt N ^ d * Real.exp (-c * N) ≤ (N:ℝ) ^ d * Real.exp (-c * N) := by gcongr
    _ = (c ^ d)⁻¹ * ((c * N) ^ d * Real.exp (-(c * N))) := by
        rw [mul_pow, neg_mul]; field_simp

lemma near_re_bound (x xb : Fin R → ℝ) (ζ : Fin R → ℂ) (N : ℕ) (hN : 0 < N)
    {m0 lam δ : ℝ} (hm0 : 0 < m0) (hm0le : ∀ r, m0 ≤ xb r) (hlam : 0 ≤ lam)
    (hcoer : ∀ s : Fin d → ℝ, lam * ‖s‖ ^ 2 ≤ ∑ r, KT K s r ^ 2)
    (hxN : ∀ r, xb r * N / 2 ≤ x r ∧ x r ≤ 2 * xb r * N)
    (ha : ∀ r, ‖ζ r‖ / Real.sqrt N ≤ 1) (him : ∀ r, |(ζ r).im| / Real.sqrt N ≤ π / 2)
    (hδ : 0 ≤ δ) (hKδ : Kmax K * δ ≤ π / 2) (s : Fin d → ℝ) (hs : ‖s‖ ≤ δ * Real.sqrt N) :
    (Phi K x ζ N ((Real.sqrt N)⁻¹ • s)).re ≤
      ∑ r, (2 * xb r * (ζ r).re ^ 2 + xb r * (ζ r).im ^ 2)
        - m0 * (Real.exp (-1) / π ^ 2) / 2 * lam * ‖s‖ ^ 2 := by
  set sN := Real.sqrt N with hsNdef
  have hsN : 0 < sN := Real.sqrt_pos.2 (by exact_mod_cast hN)
  have hsN2 : sN ^ 2 = N := Real.sq_sqrt (Nat.cast_nonneg _)
  have hNpos : (0:ℝ) < N := by exact_mod_cast hN
  set κ := Real.exp (-1) / π ^ 2 with hκ
  have hκ0 : 0 < κ := by positivity
  have hκ1 : κ ≤ 1 := by
    rw [hκ, div_le_one (by positivity)]
    have h1 : Real.exp (-1) ≤ 1 := by rw [Real.exp_le_one_iff]; norm_num
    have h2 : (1:ℝ) ≤ π ^ 2 := by nlinarith [Real.pi_gt_three]
    linarith
  set θ := sN⁻¹ • s with hθ
  have hθn : ‖θ‖ ≤ δ := by
    rw [hθ, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hsN]
    rw [inv_mul_le_iff₀ hsN]; linarith
  have hterm : ∀ r, ((x r : ℂ) * phi (ζ r / (sN : ℂ) + I * (KT K θ r : ℂ))).re ≤
      2 * xb r * (ζ r).re ^ 2 + xb r * (ζ r).im ^ 2 - m0 * κ / 2 * KT K s r ^ 2 := by
    intro r
    have hxb0 : 0 ≤ xb r := le_trans hm0.le (hm0le r)
    have hx0 : 0 ≤ x r := le_trans (div_nonneg (mul_nonneg hxb0 (Nat.cast_nonneg _)) two_pos.le) (hxN r).1
    have h1 := re_term_le (ζ r) (x r) (KT K θ r) sN hsN (ha r) hx0
    set b := (ζ r).im / sN + KT K θ r with hb
    have hKTθ : KT K θ r = KT K s r / sN := by
      rw [hθ, KT_smul]; field_simp
    have hbabs : |b| ≤ π := by
      have e1 : |(ζ r).im / sN| ≤ π / 2 := by
        rw [abs_div, abs_of_pos hsN]; exact him r
      have e2 : |KT K θ r| ≤ π / 2 :=
        le_trans (abs_KT_le K θ r) (le_trans
          (mul_le_mul_of_nonneg_left hθn (Kmax_nonneg K)) hKδ)
      calc |b| ≤ |(ζ r).im / sN| + |KT K θ r| := abs_add_le _ _
        _ ≤ π := by linarith
    have hcos := one_sub_cos_ge hbabs
    have hbeq : b ^ 2 = ((ζ r).im + KT K s r) ^ 2 / N := by
      rw [hb, hKTθ, ← hsN2]; field_simp
    have hre2 : x r * ((ζ r).re / sN) ^ 2 ≤ 2 * xb r * (ζ r).re ^ 2 := by
      rw [div_pow, hsN2]
      have := (hxN r).2
      rw [mul_div_assoc']
      rw [div_le_iff₀ hNpos]
      have := mul_le_mul_of_nonneg_right this (sq_nonneg (ζ r).re)
      linear_combination this
    -- lower bound on the cosine term
    have hlow : xb r * κ * ((ζ r).im + KT K s r) ^ 2 ≤
        x r * Real.exp (-1) * (1 - Real.cos b) := by
      have hxl := (hxN r).1
      have hc' : 2 / π ^ 2 * (((ζ r).im + KT K s r) ^ 2 / N) ≤ 1 - Real.cos b := by
        rw [← hbeq]; exact hcos
      have hE : 0 < Real.exp (-1) := Real.exp_pos _
      have hq : 0 ≤ ((ζ r).im + KT K s r) ^ 2 := sq_nonneg _
      calc xb r * κ * ((ζ r).im + KT K s r) ^ 2
          = (xb r * N / 2) * Real.exp (-1) * (2 / π ^ 2 * (((ζ r).im + KT K s r) ^ 2 / N)) := by
            rw [hκ]; field_simp
        _ ≤ x r * Real.exp (-1) * (1 - Real.cos b) := by
            apply mul_le_mul (mul_le_mul_of_nonneg_right hxl hE.le) hc' (by positivity)
              (mul_nonneg hx0 hE.le)
    have hsq : ((ζ r).im + KT K s r) ^ 2 ≥ KT K s r ^ 2 / 2 - (ζ r).im ^ 2 := by
      nlinarith [sq_nonneg ((ζ r).im + KT K s r / 2)]
    have hxbκ : xb r * κ * ((ζ r).im + KT K s r) ^ 2 ≥
        m0 * κ / 2 * KT K s r ^ 2 - xb r * (ζ r).im ^ 2 := by
      have hxb0 : 0 ≤ xb r := le_trans hm0.le (hm0le r)
      have e1 : xb r * κ * ((ζ r).im + KT K s r) ^ 2 ≥
          xb r * κ * (KT K s r ^ 2 / 2 - (ζ r).im ^ 2) :=
        mul_le_mul_of_nonneg_left hsq (by positivity)
      have e2 : xb r * κ * (KT K s r ^ 2 / 2) ≥ m0 * κ / 2 * KT K s r ^ 2 := by
        have := mul_le_mul_of_nonneg_right (hm0le r) (by positivity : (0:ℝ) ≤ κ / 2 * KT K s r ^ 2)
        linear_combination this
      have e3 : xb r * κ * (ζ r).im ^ 2 ≤ xb r * (ζ r).im ^ 2 := by
        have := mul_le_mul_of_nonneg_right hκ1 (by positivity : (0:ℝ) ≤ xb r * (ζ r).im ^ 2)
        linear_combination this
      linear_combination e1 + e2 + e3
    linarith
  have hsum : (Phi K x ζ N θ).re ≤
      ∑ r, (2 * xb r * (ζ r).re ^ 2 + xb r * (ζ r).im ^ 2 - m0 * κ / 2 * KT K s r ^ 2) := by
    unfold Phi
    rw [Complex.re_sum]
    exact Finset.sum_le_sum (fun r _ => hterm r)
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum] at hsum
  have := hcoer s
  have hpos : 0 ≤ m0 * κ / 2 := by positivity
  have h2 := mul_le_mul_of_nonneg_left this hpos
  linear_combination hsum + h2

lemma far_re_bound (x xb : Fin R → ℝ) (ζ : Fin R → ℂ) (N : ℕ) (hN : 0 < N)
    {m0 ε : ℝ} (hm0 : 0 < m0) (hm0le : ∀ r, m0 ≤ xb r)
    (hxN : ∀ r, xb r * N / 2 ≤ x r ∧ x r ≤ 2 * xb r * N)
    (ha : ∀ r, ‖ζ r‖ / Real.sqrt N ≤ 1)
    (him : ∑ r, |(ζ r).im| / Real.sqrt N ≤ ε / 2)
    (θ : Fin d → ℝ) (hθ : ε ≤ ∑ r, (1 - Real.cos (KT K θ r))) :
    (Phi K x ζ N θ).re ≤ ∑ r, 2 * xb r * (ζ r).re ^ 2 - Real.exp (-1) * m0 * ε / 4 * N := by
  set sN := Real.sqrt N with hsNdef
  have hsN : 0 < sN := Real.sqrt_pos.2 (by exact_mod_cast hN)
  have hsN2 : sN ^ 2 = N := Real.sq_sqrt (Nat.cast_nonneg _)
  have hNpos : (0:ℝ) < N := by exact_mod_cast hN
  have hterm : ∀ r, ((x r : ℂ) * phi (ζ r / (sN : ℂ) + I * (KT K θ r : ℂ))).re ≤
      2 * xb r * (ζ r).re ^ 2 -
        Real.exp (-1) * (m0 * N / 2) * (1 - Real.cos ((ζ r).im / sN + KT K θ r)) := by
    intro r
    have hxb0 : 0 ≤ xb r := le_trans hm0.le (hm0le r)
    have hx0 : 0 ≤ x r := le_trans (div_nonneg (mul_nonneg hxb0 (Nat.cast_nonneg _)) two_pos.le) (hxN r).1
    have h1 := re_term_le (ζ r) (x r) (KT K θ r) sN hsN (ha r) hx0
    have hre2 : x r * ((ζ r).re / sN) ^ 2 ≤ 2 * xb r * (ζ r).re ^ 2 := by
      rw [div_pow, hsN2]
      have := (hxN r).2
      rw [mul_div_assoc']
      rw [div_le_iff₀ hNpos]
      have := mul_le_mul_of_nonneg_right this (sq_nonneg (ζ r).re)
      linear_combination this
    have hc0 : 0 ≤ 1 - Real.cos ((ζ r).im / sN + KT K θ r) := by
      linarith [Real.cos_le_one ((ζ r).im / sN + KT K θ r)]
    have hxl : m0 * N / 2 ≤ x r := le_trans (by
      have := hm0le r
      have : m0 * N ≤ xb r * N := mul_le_mul_of_nonneg_right this hNpos.le
      linarith) (hxN r).1
    have : Real.exp (-1) * (m0 * N / 2) * (1 - Real.cos ((ζ r).im / sN + KT K θ r)) ≤
        x r * Real.exp (-1) * (1 - Real.cos ((ζ r).im / sN + KT K θ r)) := by
      have := mul_le_mul_of_nonneg_right hxl
        (mul_nonneg (Real.exp_pos (-1)).le hc0)
      linear_combination this
    linarith
  have hcos : ε / 2 ≤ ∑ r, (1 - Real.cos ((ζ r).im / sN + KT K θ r)) := by
    have : ∀ r, (1 - Real.cos (KT K θ r)) - |(ζ r).im| / sN ≤
        1 - Real.cos ((ζ r).im / sN + KT K θ r) := by
      intro r
      have h := Real.abs_cos_sub_cos_le ((ζ r).im / sN + KT K θ r) (KT K θ r)
      have : |(ζ r).im / sN + KT K θ r - KT K θ r| = |(ζ r).im| / sN := by
        rw [add_sub_cancel_right, abs_div, abs_of_pos hsN]
      rw [this] at h
      linarith [(abs_le.1 h).1, (abs_le.1 h).2]
    have := Finset.sum_le_sum (fun r (_ : r ∈ Finset.univ) => this r)
    rw [Finset.sum_sub_distrib] at this
    linarith
  unfold Phi
  rw [Complex.re_sum]
  refine le_trans (Finset.sum_le_sum (fun r _ => hterm r)) ?_
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  have hE : 0 ≤ Real.exp (-1) * (m0 * N / 2) := by positivity
  have := mul_le_mul_of_nonneg_left hcos hE
  linear_combination this

lemma inj_of_dual (hK : ∀ θ : Fin d → ℝ, (∀ r, ∃ m : ℤ, KT K θ r = 2 * π * m) →
      ∀ i, ∃ m : ℤ, θ i = 2 * π * m) :
    ∀ s : Fin d → ℝ, (∀ r, KT K s r = 0) → s = 0 := by
  intro s hs
  funext i
  by_contra hne
  have h := hK ((π / s i) • s) (fun r => ⟨0, by rw [KT_smul, hs r]; simp⟩) i
  obtain ⟨m, hm⟩ := h
  simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hm hne
  rw [div_mul_cancel₀ _ hne] at hm
  have h2 : (1:ℝ) = 2 * m := by
    have hπ := Real.pi_pos
    field_simp at hm
    nlinarith
  have h3 : (1:ℤ) = 2 * m := by exact_mod_cast h2
  omega

lemma gauss_bound_integrable (d : ℕ) (C c : ℝ) (hc : 0 < c) :
    Integrable (fun s : Fin d → ℝ => Real.exp C * ∏ i, Real.exp (-c * s i ^ 2)) := by
  refine Integrable.const_mul ?_ _
  rw [volume_pi]
  exact Integrable.fintype_prod (fun i => integrable_exp_neg_mul_sq hc)

lemma exp_neg_norm_sq_le (d : ℕ) {c : ℝ} (hc : 0 ≤ c) (s : Fin d → ℝ) :
    Real.exp (-c * ‖s‖ ^ 2) ≤ ∏ i, Real.exp (-(c / (d + 1)) * s i ^ 2) := by
  rw [← Real.exp_sum]
  apply Real.exp_le_exp.2
  have h1 : ∀ i, s i ^ 2 ≤ ‖s‖ ^ 2 := by
    intro i
    have := norm_le_pi_norm s i
    rw [Real.norm_eq_abs] at this
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) this 2
  have h2 : ∑ i, s i ^ 2 ≤ (d + 1) * ‖s‖ ^ 2 := by
    calc ∑ i, s i ^ 2 ≤ ∑ _i : Fin d, ‖s‖ ^ 2 := Finset.sum_le_sum (fun i _ => h1 i)
      _ = d * ‖s‖ ^ 2 := by simp
      _ ≤ (d + 1) * ‖s‖ ^ 2 := by nlinarith [sq_nonneg ‖s‖]
  have : ∑ i, -(c / (d + 1)) * s i ^ 2 = -(c / (d + 1)) * ∑ i, s i ^ 2 := by
    rw [Finset.mul_sum]
  rw [this]
  have hd : (0:ℝ) < d + 1 := by positivity
  have := mul_le_mul_of_nonneg_left h2 (div_nonneg hc hd.le)
  rw [← mul_assoc, div_mul_cancel₀ _ hd.ne'] at this
  linarith

/-- **Laplace asymptotics of the torus integral (single peak).** -/
theorem laplace_main
    (hK : ∀ θ : Fin d → ℝ, (∀ r, ∃ m : ℤ, KT K θ r = 2 * π * m) →
      ∀ i, ∃ m : ℤ, θ i = 2 * π * m)
    (x : ℕ → Fin R → ℝ) (xb : Fin R → ℝ) (hxb : ∀ r, 0 < xb r)
    (hx : ∀ r, Tendsto (fun N : ℕ => x N r / N) atTop (𝓝 (xb r)))
    (ψ : ℕ → (Fin d → ℝ) → ℂ) (hψc : ∀ N, Continuous (ψ N)) (Cψ : ℝ)
    (hψb : ∀ N θ, ‖ψ N θ‖ ≤ Cψ) (hψl : ∀ N θ, ‖ψ N θ - ψ N 0‖ ≤ Cψ * ‖θ‖)
    (ζ : Fin R → ℂ) :
    Tendsto (fun N : ℕ => ((Real.sqrt N ^ d : ℝ) : ℂ) *
        (∫ θ in Qbox d, ψ N θ * cexp (Phi K (x N) ζ N θ)) - ψ N 0 * gaussInt K xb ζ)
      atTop (𝓝 0) := by
  have hCψ : 0 ≤ Cψ := le_trans (norm_nonneg _) (hψb 0 0)
  obtain ⟨lam, hlam, hcoer⟩ := exists_coercive K (inj_of_dual K hK)
  set Km := Kmax K with hKm
  have hKm0 : 0 ≤ Km := Kmax_nonneg K
  set δ := π / (2 * (Km + 1)) with hδdef
  have hδ : 0 < δ := by positivity
  have hKδ : Km * δ ≤ π / 2 := by
    rw [hδdef, mul_div_assoc']
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [Real.pi_pos]
  have hδπ : δ ≤ π := by
    rw [hδdef, div_le_iff₀ (by positivity)]
    nlinarith [Real.pi_pos]
  obtain ⟨ε, hε, hfar⟩ := exists_far_bound K hK hδ
  obtain ⟨m0, hm0, hm0le⟩ := exists_pos_lower xb hxb
  -- eventual conditions
  have hev1 : ∀ᶠ N : ℕ in atTop, ∀ r, xb r * N / 2 ≤ x N r ∧ x N r ≤ 2 * xb r * N := by
    rw [eventually_all]
    intro r
    have h1 : ∀ᶠ N : ℕ in atTop, xb r / 2 < x N r / N :=
      (hx r).eventually (lt_mem_nhds (by linarith [hxb r]))
    have h2 : ∀ᶠ N : ℕ in atTop, x N r / N < 2 * xb r :=
      (hx r).eventually (gt_mem_nhds (by linarith [hxb r]))
    filter_upwards [h1, h2, eventually_gt_atTop 0] with N h1 h2 hN
    have hNp : (0:ℝ) < N := by exact_mod_cast hN
    rw [lt_div_iff₀ hNp] at h1
    rw [div_lt_iff₀ hNp] at h2
    constructor <;> nlinarith
  have hinv := tendsto_inv_sqrt
  have hev2 : ∀ᶠ N : ℕ in atTop, ∀ r, ‖ζ r‖ / Real.sqrt N ≤ 1 := by
    rw [eventually_all]; intro r
    have := hinv.const_mul ‖ζ r‖
    rw [mul_zero] at this
    filter_upwards [this.eventually (ge_mem_nhds one_pos)] with N hN
    rwa [div_eq_mul_inv]
  have hev3 : ∀ᶠ N : ℕ in atTop, ∀ r, |(ζ r).im| / Real.sqrt N ≤ π / 2 := by
    rw [eventually_all]; intro r
    have := hinv.const_mul |(ζ r).im|
    rw [mul_zero] at this
    filter_upwards [this.eventually (ge_mem_nhds (by positivity : (0:ℝ) < π / 2))] with N hN
    rwa [div_eq_mul_inv]
  have hev4 : ∀ᶠ N : ℕ in atTop, ∑ r, |(ζ r).im| / Real.sqrt N ≤ ε / 2 := by
    have := hinv.const_mul (∑ r, |(ζ r).im|)
    rw [mul_zero] at this
    filter_upwards [this.eventually (ge_mem_nhds (by positivity : (0:ℝ) < ε / 2))] with N hN
    rwa [← Finset.sum_div, div_eq_mul_inv]
  -- constants
  set C2 := ∑ r, (2 * xb r * (ζ r).re ^ 2 + xb r * (ζ r).im ^ 2) with hC2
  set c1 := m0 * (Real.exp (-1) / π ^ 2) / 2 * lam with hc1def
  have hc1 : 0 < c1 := by positivity
  set cd := c1 / (d + 1) with hcd
  have hcd : 0 < cd := by positivity
  set g : (Fin d → ℝ) → ℝ := fun s => Real.exp C2 * ∏ i, Real.exp (-cd * s i ^ 2) with hg
  have hgi : Integrable g := gauss_bound_integrable d C2 cd hcd
  have hg0 : ∀ s, 0 ≤ g s := fun s => by positivity
  set C2' := ∑ r, 2 * xb r * (ζ r).re ^ 2 with hC2'
  set c3 := Real.exp (-1) * m0 * ε / 4 with hc3def
  have hc3 : 0 < c3 := by positivity
  set Bδ : Set (Fin d → ℝ) := Metric.closedBall 0 δ with hBδ
  have hBm : MeasurableSet Bδ := measurableSet_closedBall
  -- near domination
  have hnear : ∀ᶠ N : ℕ in atTop, ∀ s : Fin d → ℝ, (Real.sqrt N)⁻¹ • s ∈ Bδ →
      ‖cexp (Phi K (x N) ζ N ((Real.sqrt N)⁻¹ • s))‖ ≤ g s := by
    filter_upwards [hev1, hev2, hev3, eventually_gt_atTop 0] with N h1 h2 h3 hN
    intro s hs
    have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 (by exact_mod_cast hN)
    have hs' : ‖s‖ ≤ δ * Real.sqrt N := by
      rw [hBδ, Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_inv,
        abs_of_pos hsN, inv_mul_le_iff₀ hsN] at hs
      linarith
    have hb := near_re_bound K (x N) xb ζ N hN hm0 hm0le hlam.le hcoer h1 h2 h3 hδ.le hKδ s hs'
    refine le_trans (norm_cexp_le_of_re_le hb) ?_
    rw [hg]
    have : C2 - c1 * ‖s‖ ^ 2 = C2 + (-c1 * ‖s‖ ^ 2) := by ring
    rw [this, Real.exp_add]
    exact mul_le_mul_of_nonneg_left (exp_neg_norm_sq_le d hc1.le s) (Real.exp_pos _).le
  -- far domination
  have hfarb : ∀ᶠ N : ℕ in atTop, ∀ θ ∈ Qbox d, θ ∉ Bδ →
      ‖ψ N θ * cexp (Phi K (x N) ζ N θ)‖ ≤ Cψ * Real.exp (C2' - c3 * N) := by
    filter_upwards [hev1, hev2, hev4, eventually_gt_atTop 0] with N h1 h2 h4 hN
    intro θ hθQ hθB
    have hθn : δ ≤ ‖θ‖ := by
      rw [hBδ, Metric.mem_closedBall, dist_zero_right, not_le] at hθB; exact hθB.le
    have hb := far_re_bound K (x N) xb ζ N hN hm0 hm0le h1 h2 h4 θ (hfar θ hθQ hθn)
    rw [norm_mul]
    refine mul_le_mul (hψb N θ) (norm_cexp_le_of_re_le ?_) (norm_nonneg _) hCψ
    rw [hC2', hc3def]; linarith
  -- integrand and its continuity
  set F : ℕ → (Fin d → ℝ) → ℂ := fun N θ => ψ N θ * cexp (Phi K (x N) ζ N θ) with hF
  have hFc : ∀ N, Continuous (F N) := fun N =>
    (hψc N).mul (Complex.continuous_exp.comp (Phi_cont K (x N) ζ N))
  have hQc : IsCompact (Qbox d) := isCompact_univ_pi (fun _ => isCompact_Icc)
  have hQm : MeasurableSet (Qbox d) := hQc.isClosed.measurableSet
  have hBQ : Bδ ⊆ Qbox d := by
    intro θ hθ i _
    rw [hBδ, Metric.mem_closedBall, dist_zero_right] at hθ
    have := le_trans (norm_le_pi_norm θ i) hθ
    rw [Real.norm_eq_abs] at this
    exact ⟨by linarith [(abs_le.1 (le_trans this hδπ)).1], (abs_le.1 (le_trans this hδπ)).2⟩
  have hsplit : ∀ N, ∫ θ in Qbox d, F N θ =
      (∫ θ, Bδ.indicator (F N) θ) + ∫ θ in Qbox d, Bδᶜ.indicator (F N) θ := by
    intro N
    have hint : IntegrableOn (F N) (Qbox d) := (hFc N).continuousOn.integrableOn_compact hQc
    have e1 : ∫ θ in Qbox d, F N θ =
        ∫ θ in Qbox d, (Bδ.indicator (F N) θ + Bδᶜ.indicator (F N) θ) := by
      congr 1; funext θ; rw [Set.indicator_self_add_compl_apply]
    rw [e1, integral_add (hint.indicator hBm) (hint.indicator hBm.compl)]
    congr 1
    rw [setIntegral_indicator hBm, Set.inter_eq_right.2 hBQ, integral_indicator hBm]
  -- change of variables
  have hcov : ∀ N : ℕ, 0 < N → ((Real.sqrt N ^ d : ℝ) : ℂ) * ∫ θ, Bδ.indicator (F N) θ =
      ∫ s, Bδ.indicator (F N) ((Real.sqrt N)⁻¹ • s) := by
    intro N hN
    have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 (by exact_mod_cast hN)
    rw [MeasureTheory.Measure.integral_comp_smul, Module.finrank_pi, Fintype.card_fin,
      Complex.real_smul]
    congr 1
    rw [inv_pow, inv_inv, abs_of_pos (by positivity)]
  -- the two scaled sequences
  set An : ℕ → (Fin d → ℝ) → ℂ := fun N s => Bδ.indicator
    (fun θ => (ψ N θ - ψ N 0) * cexp (Phi K (x N) ζ N θ)) ((Real.sqrt N)⁻¹ • s) with hAn
  set Bn : ℕ → (Fin d → ℝ) → ℂ := fun N s => Bδ.indicator
    (fun θ => cexp (Phi K (x N) ζ N θ)) ((Real.sqrt N)⁻¹ • s) with hBn
  have hAB : ∀ N s, Bδ.indicator (F N) ((Real.sqrt N)⁻¹ • s) = An N s + ψ N 0 * Bn N s := by
    intro N s
    simp only [hAn, hBn, hF, Set.indicator]
    split_ifs <;> ring
  have hAm : ∀ N, AEStronglyMeasurable (An N) := by
    intro N
    have hc : Continuous (fun θ => (ψ N θ - ψ N 0) * cexp (Phi K (x N) ζ N θ)) :=
      ((hψc N).sub continuous_const).mul (Complex.continuous_exp.comp (Phi_cont K (x N) ζ N))
    exact ((hc.measurable.indicator hBm).comp (measurable_const_smul _)).aestronglyMeasurable
  have hBm' : ∀ N, AEStronglyMeasurable (Bn N) := by
    intro N
    have hc : Continuous (fun θ => cexp (Phi K (x N) ζ N θ)) :=
      Complex.continuous_exp.comp (Phi_cont K (x N) ζ N)
    exact ((hc.measurable.indicator hBm).comp (measurable_const_smul _)).aestronglyMeasurable
  have hBb : ∀ᶠ N : ℕ in atTop, ∀ s, ‖Bn N s‖ ≤ g s := by
    filter_upwards [hnear] with N hN s
    simp only [hBn, Set.indicator]
    split_ifs with h
    · exact hN s h
    · simpa using hg0 s
  have hAb : ∀ᶠ N : ℕ in atTop, ∀ s, ‖An N s‖ ≤ 2 * Cψ * g s := by
    filter_upwards [hnear] with N hN s
    simp only [hAn, Set.indicator]
    split_ifs with h
    · rw [norm_mul]
      have e1 : ‖ψ N ((Real.sqrt N)⁻¹ • s) - ψ N 0‖ ≤ 2 * Cψ :=
        le_trans (norm_sub_le _ _) (by linarith [hψb N ((Real.sqrt N)⁻¹ • s), hψb N 0])
      exact mul_le_mul e1 (hN s h) (norm_nonneg _) (by positivity)
    · simpa using mul_nonneg (mul_nonneg two_pos.le hCψ) (hg0 s)
  -- eventually inside the near ball
  have hin : ∀ s : Fin d → ℝ, ∀ᶠ N : ℕ in atTop, (Real.sqrt N)⁻¹ • s ∈ Bδ := by
    intro s
    have := hinv.mul_const ‖s‖
    rw [zero_mul] at this
    filter_upwards [this.eventually (ge_mem_nhds hδ)] with N hN
    rw [hBδ, Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_inv, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact hN
  have hBlim : ∀ s, Tendsto (fun N => Bn N s) atTop (𝓝 (gaussF K xb ζ s)) := by
    intro s
    have hlim : Tendsto (fun N : ℕ => cexp (∑ r, ((x N r / N : ℝ) : ℂ) *
        ((N : ℂ) * phi ((ζ r + I * (KT K s r : ℂ)) / (Real.sqrt N : ℂ))))) atTop
        (𝓝 (gaussF K xb ζ s)) := by
      unfold gaussF
      refine (Complex.continuous_exp.tendsto _).comp ?_
      refine tendsto_finsetSum _ (fun r _ => ?_)
      have := ((Complex.continuous_ofReal.tendsto _).comp (hx r)).mul
        (phi_limit (ζ r + I * (KT K s r : ℂ)))
      rw [show (xb r : ℂ) * (ζ r + I * (KT K s r : ℂ)) ^ 2 / 2 =
        (xb r : ℂ) * ((ζ r + I * (KT K s r : ℂ)) ^ 2 / 2) by ring]
      exact this
    refine hlim.congr' ?_
    filter_upwards [hin s, eventually_gt_atTop 0] with N hN hN0
    simp only [hBn, Set.indicator_of_mem hN]
    rw [Phi_scaled K (x N) ζ N hN0 s]
    congr 1
    refine Finset.sum_congr rfl (fun r _ => ?_)
    have : (N : ℂ) ≠ 0 := by exact_mod_cast hN0.ne'
    push_cast
    field_simp
  have hAlim : ∀ s, Tendsto (fun N => An N s) atTop (𝓝 0) := by
    intro s
    have hb : Tendsto (fun N : ℕ => Cψ * ((Real.sqrt N)⁻¹ * ‖s‖) * g s) atTop (𝓝 0) := by
      have := ((hinv.mul_const ‖s‖).const_mul Cψ).mul_const (g s)
      simpa using this
    refine squeeze_zero_norm' ?_ hb
    filter_upwards [hin s, hnear] with N hN hN'
    simp only [hAn, Set.indicator_of_mem hN]
    rw [norm_mul]
    refine mul_le_mul ?_ (hN' s hN) (norm_nonneg _) (by positivity)
    refine le_trans (hψl N _) ?_
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (Real.sqrt_nonneg _)]
  have hBint : Tendsto (fun N => ∫ s, Bn N s) atTop (𝓝 (gaussInt K xb ζ)) :=
    tendsto_integral_filter_of_dominated_convergence g (Eventually.of_forall hBm')
      (hBb.mono fun N hN => Eventually.of_forall (hN)) hgi (Eventually.of_forall hBlim)
  have hAint : Tendsto (fun N => ∫ s, An N s) atTop (𝓝 0) := by
    have := tendsto_integral_filter_of_dominated_convergence (fun s => 2 * Cψ * g s)
      (Eventually.of_forall hAm) (hAb.mono fun N hN => Eventually.of_forall (hN))
      (hgi.const_mul (2 * Cψ)) (Eventually.of_forall hAlim)
    simpa using this
  -- far term
  set volQ := (volume (Qbox d)).toReal with hvolQ
  have hfarT : Tendsto (fun N : ℕ => ((Real.sqrt N ^ d : ℝ) : ℂ) *
      ∫ θ in Qbox d, Bδᶜ.indicator (F N) θ) atTop (𝓝 0) := by
    have hdec := (sqrt_pow_exp_decay d hc3).const_mul (Cψ * Real.exp C2' * volQ)
    rw [mul_zero] at hdec
    refine squeeze_zero_norm' ?_ hdec
    filter_upwards [hfarb] with N hN
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hb : ‖∫ θ in Qbox d, Bδᶜ.indicator (F N) θ‖ ≤
        (Cψ * Real.exp (C2' - c3 * N)) * volQ := by
      have := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Qbox d)
        (f := Bδᶜ.indicator (F N)) (C := Cψ * Real.exp (C2' - c3 * N)) hQc.measure_lt_top
        (fun θ hθ => by
          by_cases hθB : θ ∈ Bδ
          · rw [Set.indicator_of_notMem (by simpa using hθB)]
            simpa using mul_nonneg hCψ (Real.exp_pos _).le
          · rw [Set.indicator_of_mem (by simpa using hθB)]
            exact hN θ hθ hθB)
      simpa [measureReal_def, hvolQ] using this
    calc Real.sqrt N ^ d * ‖∫ θ in Qbox d, Bδᶜ.indicator (F N) θ‖
        ≤ Real.sqrt N ^ d * ((Cψ * Real.exp (C2' - c3 * N)) * volQ) := by gcongr
      _ = Cψ * Real.exp C2' * volQ * (Real.sqrt N ^ d * Real.exp (-c3 * N)) := by
        rw [sub_eq_add_neg, Real.exp_add]; ring_nf
  -- assembly
  have hmain : Tendsto (fun N : ℕ => (∫ s, An N s) + ψ N 0 * ((∫ s, Bn N s) - gaussInt K xb ζ)
      + ((Real.sqrt N ^ d : ℝ) : ℂ) * ∫ θ in Qbox d, Bδᶜ.indicator (F N) θ) atTop (𝓝 0) := by
    have h2 : Tendsto (fun N => ψ N 0 * ((∫ s, Bn N s) - gaussInt K xb ζ)) atTop (𝓝 0) := by
      have hsub : Tendsto (fun N => (∫ s, Bn N s) - gaussInt K xb ζ) atTop (𝓝 0) := by
        simpa using hBint.sub_const (gaussInt K xb ζ)
      have := hsub.norm.const_mul Cψ
      rw [norm_zero, mul_zero] at this
      refine squeeze_zero_norm (fun N => ?_) this
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hψb N 0) (norm_nonneg _)
    simpa using (hAint.add h2).add hfarT
  refine hmain.congr' ?_
  filter_upwards [hAb, hBb, eventually_gt_atTop 0] with N hA hB hN0
  have hAi : Integrable (An N) := Integrable.mono' (hgi.const_mul (2 * Cψ)) (hAm N)
    (Eventually.of_forall hA)
  have hBi : Integrable (Bn N) := Integrable.mono' hgi (hBm' N) (Eventually.of_forall hB)
  rw [hsplit N, mul_add, hcov N hN0]
  simp_rw [hAB N]
  rw [integral_add hAi (hBi.const_mul _), integral_const_mul]
  ring


end main

end GLL


open MeasureTheory Filter Topology Complex ProbabilityTheory
open scoped Real NNReal

namespace GLL

/-- complex moment generating function of the Poisson law -/
lemma poisson_cmgf (r : ℝ≥0) (w : ℂ) :
    Integrable (fun k : ℕ => cexp (w * k)) (poissonMeasure r) ∧
    ∫ k, cexp (w * k) ∂(poissonMeasure r) = cexp (r * (cexp w - 1)) := by
  constructor
  · rw [integrable_poissonMeasure_iff]
    have : (fun n : ℕ => Real.exp (-r) * r ^ n / (n.factorial) * ‖cexp (w * n)‖) =
        fun n => Real.exp (-r) * ((r * Real.exp w.re) ^ n / n.factorial) := by
      funext n
      rw [Complex.norm_exp]
      have : (w * n).re = w.re * n := by simp
      rw [this, mul_pow, ← Real.exp_nat_mul]
      ring_nf
    rw [this]
    exact (Real.summable_pow_div_factorial _).mul_left _
  · rw [integral_poissonMeasure r]
    calc ∑' a : ℕ, (Real.exp (-r) * r ^ a / a.factorial : ℝ) • cexp (w * a)
      _ = ∑' a : ℕ, (Real.exp (-r) : ℂ) * ((r * cexp w) ^ a / a.factorial) := by
          congr with a
          rw [Complex.real_smul]
          push_cast
          rw [mul_pow, ← Complex.exp_nat_mul]
          ring_nf
      _ = (Real.exp (-r) : ℂ) * ∑' a : ℕ, ((r * cexp w) ^ a / a.factorial) := tsum_mul_left
      _ = (Real.exp (-r) : ℂ) * cexp (r * cexp w) := by
          rw [(NormedSpace.expSeries_div_hasSum_exp (r * cexp w)).tsum_eq, Complex.exp_eq_exp_ℂ]
      _ = cexp (r * (cexp w - 1)) := by
          rw [Complex.ofReal_exp, ← Complex.exp_add]
          push_cast
          ring_nf

/-- centred version -/
lemma poisson_cmgf_centred (x : ℝ) (hx : 0 ≤ x) (w : ℂ) :
    Integrable (fun k : ℕ => cexp (w * ((k : ℝ) - x : ℝ))) (poissonMeasure x.toNNReal) ∧
    ∫ k, cexp (w * ((k : ℝ) - x : ℝ)) ∂(poissonMeasure x.toNNReal) = cexp (x * phi w) := by
  have h := poisson_cmgf x.toNNReal w
  have hfun : (fun k : ℕ => cexp (w * ((k : ℝ) - x : ℝ))) =
      fun k : ℕ => cexp (-(w * x)) * cexp (w * k) := by
    funext k; rw [← Complex.exp_add]; push_cast; ring_nf
  rw [hfun]
  refine ⟨h.1.const_mul _, ?_⟩
  rw [integral_const_mul, h.2, ← Complex.exp_add]
  congr 1
  rw [Real.coe_toNNReal _ hx]
  simp only [phi]; ring

/-- orthogonality of characters on `[-π, π]` -/
lemma integral_char_1d (v : ℤ) :
    ∫ t in Set.Icc (-π) π, cexp (I * (t * v : ℝ)) = if v = 0 then (2 * π : ℂ) else 0 := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]
  split_ifs with hv
  · subst hv; simp; ring
  · have hc : (I * v) ≠ 0 := by
      simp [Complex.I_ne_zero, hv]
    have : (fun t : ℝ => cexp (I * (t * v : ℝ))) = fun t : ℝ => cexp ((I * v) * t) := by
      funext t; push_cast; ring_nf
    rw [this, integral_exp_mul_complex hc]
    have h1 : cexp (I * v * π) = cexp (I * v * (-π)) := by
      rw [Complex.exp_eq_exp_iff_exists_int]
      refine ⟨v, ?_⟩
      push_cast; ring
    push_cast
    rw [h1]; simp

lemma integral_char {d : ℕ} (v : Fin d → ℤ) :
    ∫ θ in Qbox d, cexp (I * ∑ i, (θ i * v i : ℝ)) =
      if v = 0 then ((2 * π) ^ d : ℂ) else 0 := by
  have hQ : (volume.restrict (Qbox d) : Measure (Fin d → ℝ)) =
      Measure.pi (fun _ => volume.restrict (Set.Icc (-π) π)) := by
    rw [Qbox, volume_pi, Measure.restrict_pi_pi]
  rw [hQ]
  have : (fun θ : Fin d → ℝ => cexp (I * ∑ i, (θ i * v i : ℝ))) =
      fun θ => ∏ i, cexp (I * (θ i * v i : ℝ)) := by
    funext θ; rw [← Complex.exp_sum]; congr 1; push_cast; rw [Finset.mul_sum]
  rw [this, integral_fintype_prod_eq_prod (f := fun i t => cexp (I * (t * v i : ℝ)))]
  simp_rw [integral_char_1d]
  split_ifs with hv
  · subst hv; simp
  · obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
      by_contra h; push_neg at h; exact hv (funext h)
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

section repr
variable {d R : ℕ} (K : Fin d → Fin R → ℤ)

/-- `(K n)_i` for an occupancy vector `n`. -/
def Kn (n : Fin R → ℕ) : Fin d → ℤ := fun i => ∑ r, K i r * (n r : ℤ)

/-- `(K x)_i` for a real vector. -/
noncomputable def Kx (x : Fin R → ℝ) : Fin d → ℝ := fun i => ∑ r, (K i r : ℝ) * x r

/-- The Fourier series of the weight, phase-centred at `K x`. -/
noncomputable def psiHat (x : Fin R → ℝ) (ψ : (Fin d → ℤ) → ℝ) (θ : Fin d → ℝ) : ℂ :=
  ∑' k, (ψ k : ℂ) * cexp (-(I * (∑ i, θ i * ((k i : ℝ) - Kx K x i) : ℝ)))

/-- Product of Poisson laws. -/
noncomputable def poisPi (x : Fin R → ℝ) : Measure (Fin R → ℕ) :=
  Measure.pi fun r => poissonMeasure (x r).toNNReal

instance (x : Fin R → ℝ) : IsProbabilityMeasure (poisPi x) := by
  unfold poisPi; infer_instance

lemma norm_cexp_I_mul (t : ℝ) : ‖cexp (I * (t : ℂ))‖ = 1 := by
  rw [Complex.norm_exp]; simp

lemma psiHat_term_norm (x : Fin R → ℝ) (ψ : (Fin d → ℤ) → ℝ) (hψ0 : ∀ k, 0 ≤ ψ k)
    (θ : Fin d → ℝ) (k : Fin d → ℤ) :
    ‖(ψ k : ℂ) * cexp (-(I * (∑ i, θ i * ((k i : ℝ) - Kx K x i) : ℝ)))‖ = ψ k := by
  rw [norm_mul, Complex.norm_exp]
  simp [abs_of_nonneg (hψ0 k)]

lemma psiHat_cont (x : Fin R → ℝ) (ψ : (Fin d → ℤ) → ℝ) (hψ0 : ∀ k, 0 ≤ ψ k)
    (hψs : Summable ψ) : Continuous (psiHat K x ψ) := by
  unfold psiHat
  refine continuous_tsum (fun k => ?_) hψs (fun k θ => le_of_eq (psiHat_term_norm K x ψ hψ0 θ k))
  fun_prop

lemma psiHat_norm_le (x : Fin R → ℝ) (ψ : (Fin d → ℤ) → ℝ) (hψ0 : ∀ k, 0 ≤ ψ k)
    (hψs : Summable ψ) (θ : Fin d → ℝ) : ‖psiHat K x ψ θ‖ ≤ ∑' k, ψ k := by
  unfold psiHat
  refine le_trans (norm_tsum_le_tsum_norm ?_) (le_of_eq ?_)
  · exact hψs.congr (fun k => (psiHat_term_norm K x ψ hψ0 θ k).symm)
  · exact tsum_congr (fun k => psiHat_term_norm K x ψ hψ0 θ k)

lemma Qbox_lt_top : volume (Qbox d) < ⊤ :=
  (isCompact_univ_pi (fun _ => isCompact_Icc)).measure_lt_top

lemma Qbox_meas : MeasurableSet (Qbox d) :=
  (isCompact_univ_pi (fun _ => isCompact_Icc)).isClosed.measurableSet

/-- Fourier inversion for the weight at an integer point. -/
lemma inversion (x : Fin R → ℝ) (ψ : (Fin d → ℤ) → ℝ) (hψ0 : ∀ k, 0 ≤ ψ k)
    (hψs : Summable ψ) (v : Fin d → ℤ) :
    ((2 * π) ^ d : ℂ) * (ψ v : ℂ) = ∫ θ in Qbox d,
      psiHat K x ψ θ * cexp (I * (∑ i, θ i * ((v i : ℝ) - Kx K x i) : ℝ)) := by
  have hpt : ∀ θ : Fin d → ℝ, psiHat K x ψ θ * cexp (I * (∑ i, θ i * ((v i : ℝ) - Kx K x i) : ℝ))
      = ∑' k, (ψ k : ℂ) * cexp (I * ((∑ i, θ i * (((v - k) i : ℤ) : ℝ) : ℝ) : ℂ)) := by
    intro θ
    unfold psiHat
    rw [← tsum_mul_right]
    refine tsum_congr (fun k => ?_)
    rw [mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    rw [← mul_neg, ← mul_add]
    congr 1
    rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [Pi.sub_apply, Int.cast_sub]; ring
  simp_rw [hpt]
  have hfin : IsFiniteMeasure (volume.restrict (Qbox d)) :=
    isFiniteMeasure_restrict.2 (Qbox_lt_top).ne
  have hint : ∀ k : Fin d → ℤ, Integrable (fun θ : Fin d → ℝ =>
      (ψ k : ℂ) * cexp (I * ((∑ i, θ i * (((v - k) i : ℤ) : ℝ) : ℝ) : ℂ))) (volume.restrict (Qbox d)) := by
    intro k
    refine Integrable.of_bound (C := ψ k) (Continuous.aestronglyMeasurable (by fun_prop)) ?_
    refine Eventually.of_forall (fun θ => ?_)
    rw [norm_mul, norm_cexp_I_mul]; simp [abs_of_nonneg (hψ0 k)]
  rw [← integral_tsum_of_summable_integral_norm hint]
  · have : ∀ k : Fin d → ℤ, ∫ θ in Qbox d, (ψ k : ℂ) * cexp (I * ((∑ i, θ i * (((v - k) i : ℤ) : ℝ) : ℝ) : ℂ))
        = if k = v then (ψ v : ℂ) * ((2 * π) ^ d : ℂ) else 0 := by
      intro k
      rw [integral_const_mul, integral_char (v - k)]
      by_cases hk : k = v
      · subst hk; simp
      · have : v - k ≠ 0 := sub_ne_zero.2 (Ne.symm hk)
        simp [this, hk]
    simp_rw [this]
    rw [tsum_ite_eq]; ring
  · have : ∀ k : Fin d → ℤ, ∫ θ in Qbox d, ‖(ψ k : ℂ) * cexp (I * ((∑ i, θ i * (((v - k) i : ℤ) : ℝ) : ℝ) : ℂ))‖
        = ψ k * (volume (Qbox d)).toReal := by
      intro k
      have : ∀ θ : Fin d → ℝ, ‖(ψ k : ℂ) * cexp (I * ((∑ i, θ i * (((v - k) i : ℤ) : ℝ) : ℝ) : ℂ))‖ = ψ k := by
        intro θ; rw [norm_mul, norm_cexp_I_mul]; simp [abs_of_nonneg (hψ0 k)]
      simp_rw [this]
      rw [integral_const, smul_eq_mul, measureReal_restrict_apply_univ, mul_comm]
      rfl
    simp_rw [this]
    exact hψs.mul_right _

/-- the centred tilt `exp(ζ·u)` as a product of one-dimensional factors -/
lemma tilt_integrable (x : Fin R → ℝ) (hx : ∀ r, 0 ≤ x r) (w : Fin R → ℂ) :
    Integrable (fun n : Fin R → ℕ => ∏ r, cexp (w r * ((n r : ℝ) - x r : ℝ))) (poisPi x) := by
  unfold poisPi
  exact Integrable.fintype_prod (f := fun r (k : ℕ) => cexp (w r * ((k : ℝ) - x r : ℝ)))
    (fun r => (poisson_cmgf_centred (x r) (hx r) (w r)).1)

lemma tilt_integral (x : Fin R → ℝ) (hx : ∀ r, 0 ≤ x r) (w : Fin R → ℂ) :
    ∫ n, ∏ r, cexp (w r * ((n r : ℝ) - x r : ℝ)) ∂(poisPi x) =
      cexp (∑ r, (x r : ℂ) * phi (w r)) := by
  unfold poisPi
  rw [integral_fintype_prod_eq_prod (f := fun r (k : ℕ) => cexp (w r * ((k : ℝ) - x r : ℝ)))]
  rw [Complex.exp_sum]
  exact Finset.prod_congr rfl (fun r _ => (poisson_cmgf_centred (x r) (hx r) (w r)).2)

/-- the phase identity -/
lemma phase_eq (x : Fin R → ℝ) (ζ : Fin R → ℂ) (N : ℕ) (θ : Fin d → ℝ) (n : Fin R → ℕ) :
    cexp (∑ r, ζ r * ((((n r : ℝ) - x r) / Real.sqrt N : ℝ) : ℂ)) *
      cexp (I * ((∑ i, θ i * (((Kn K n i : ℤ) : ℝ) - Kx K x i) : ℝ) : ℂ)) =
    ∏ r, cexp ((ζ r / (Real.sqrt N : ℂ) + I * (KT K θ r : ℂ)) * ((n r : ℝ) - x r : ℝ)) := by
  rw [← Complex.exp_add, ← Complex.exp_sum]
  congr 1
  have h2 : (∑ i, θ i * (((Kn K n i : ℤ) : ℝ) - Kx K x i)) =
      ∑ r, KT K θ r * ((n r : ℝ) - x r) := by
    simp only [Kn, Kx, KT]
    push_cast
    simp_rw [← Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun r _ => Finset.sum_congr rfl (fun i _ => ?_))
    ring
  rw [h2]
  push_cast
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  rw [div_eq_mul_inv, div_eq_mul_inv]
  ring

/-- **Fourier representation of the tilted Poisson sum.** -/
theorem fourier_repr (x : Fin R → ℝ) (hx : ∀ r, 0 ≤ x r) (ψ : (Fin d → ℤ) → ℝ)
    (hψ0 : ∀ k, 0 ≤ ψ k) (hψs : Summable ψ) (ζ : Fin R → ℂ) (N : ℕ) :
    ∫ n, (ψ (Kn K n) : ℂ) * cexp (∑ r, ζ r * ((((n r : ℝ) - x r) / Real.sqrt N : ℝ) : ℂ))
      ∂(poisPi x) =
    ((2 * π) ^ d : ℂ)⁻¹ * ∫ θ in Qbox d, psiHat K x ψ θ * cexp (Phi K x ζ N θ) := by
  set f : (Fin R → ℕ) → ℂ := fun n => cexp (∑ r, ζ r * ((((n r : ℝ) - x r) / Real.sqrt N : ℝ) : ℂ))
    with hf
  set w : Fin d → ℝ → Fin R → ℂ := fun _ _ r => 0 with hw
  have h2π : ((2 * π) ^ d : ℂ) ≠ 0 := by
    have : (2 * π : ℂ) ≠ 0 := by
      have := Real.pi_pos; exact_mod_cast (by positivity : (2 * π : ℝ) ≠ 0)
    exact pow_ne_zero _ this
  -- pointwise inversion
  have hpt : ∀ n, (ψ (Kn K n) : ℂ) * f n = ((2 * π) ^ d : ℂ)⁻¹ * ∫ θ in Qbox d,
      psiHat K x ψ θ * (f n * cexp (I * ((∑ i, θ i * (((Kn K n i : ℤ) : ℝ) - Kx K x i) : ℝ) : ℂ))) := by
    intro n
    have := inversion K x ψ hψ0 hψs (Kn K n)
    have e : ∀ θ : Fin d → ℝ, psiHat K x ψ θ *
        (f n * cexp (I * ((∑ i, θ i * (((Kn K n i : ℤ) : ℝ) - Kx K x i) : ℝ) : ℂ))) =
        f n * (psiHat K x ψ θ * cexp (I * ((∑ i, θ i * (((Kn K n i : ℤ) : ℝ) - Kx K x i) : ℝ) : ℂ))) := by
      intro θ; ring
    simp_rw [e]
    rw [integral_const_mul, ← this]
    field_simp
  refine (integral_congr_ae (Eventually.of_forall hpt)).trans ?_
  rw [integral_const_mul]
  congr 1
  -- Fubini
  have hfin : IsFiniteMeasure (volume.restrict (Qbox d)) :=
    isFiniteMeasure_restrict.2 (Qbox_lt_top).ne
  have hfint : Integrable f (poisPi x) := by
    have := tilt_integrable x hx (fun r => ζ r / (Real.sqrt N : ℂ))
    refine this.congr (Eventually.of_forall fun n => ?_)
    simp only [hf]
    rw [← Complex.exp_sum]
    congr 1
    refine Finset.sum_congr rfl (fun r _ => ?_)
    push_cast; ring
  have hcontθ : ∀ n, Continuous (fun θ : Fin d → ℝ => psiHat K x ψ θ *
      (f n * cexp (I * ((∑ i, θ i * (((Kn K n i : ℤ) : ℝ) - Kx K x i) : ℝ) : ℂ)))) := by
    intro n
    exact (psiHat_cont K x ψ hψ0 hψs).mul (continuous_const.mul (by fun_prop))
  have hint : Integrable (Function.uncurry fun (n : Fin R → ℕ) (θ : Fin d → ℝ) =>
      psiHat K x ψ θ * (f n * cexp (I * ((∑ i, θ i * (((Kn K n i : ℤ) : ℝ) - Kx K x i) : ℝ) : ℂ))))
      ((poisPi x).prod (volume.restrict (Qbox d))) := by
    have hb : Integrable (fun p : (Fin R → ℕ) × (Fin d → ℝ) => ‖f p.1‖ * (∑' k, ψ k))
        ((poisPi x).prod (volume.restrict (Qbox d))) :=
      hfint.norm.mul_prod (integrable_const _)
    refine Integrable.mono' hb ?_ (Eventually.of_forall fun p => ?_)
    · refine Measurable.aestronglyMeasurable ?_
      exact measurable_from_prod_countable_right (fun n => (hcontθ n).measurable)
    · simp only [Function.uncurry]
      rw [norm_mul, norm_mul, norm_cexp_I_mul, mul_one, mul_comm]
      exact mul_le_mul_of_nonneg_left (psiHat_norm_le K x ψ hψ0 hψs p.2) (norm_nonneg _)
  rw [integral_integral_swap hint]
  congr 1
  funext θ
  rw [integral_const_mul]
  congr 1
  simp only [hf]
  simp_rw [phase_eq K x ζ N θ]
  rw [tilt_integral x hx]
  rfl


end repr

end GLL


open MeasureTheory Filter Topology Complex
open scoped Real Matrix

namespace GLL

/-- Lattice reparametrisation: the subgroup `H ℤ^R ⊆ ℤ^b` has a basis `P`, and in these
coordinates `H = P K` with `K` surjective onto `ℤ^b`. -/
theorem lattice_basis {b R : ℕ} (H : Fin b → Fin R → ℕ)
    (hH : LinearIndependent ℝ (fun j : Fin b => fun r => (H j r : ℝ))) :
    ∃ (K : Fin b → Fin R → ℤ) (P : Matrix (Fin b) (Fin b) ℤ),
      (∀ j r, (H j r : ℤ) = ∑ i, P j i * K i r) ∧
      (∀ θ : Fin b → ℝ, (∀ r, ∃ m : ℤ, KT K θ r = 2 * π * m) → ∀ i, ∃ m : ℤ, θ i = 2 * π * m) ∧
      P.det ≠ 0 := by
  classical
  set col : Fin R → (Fin b → ℤ) := fun r j => (H j r : ℤ) with hcol
  set L : Submodule ℤ (Fin b → ℤ) := Submodule.span ℤ (Set.range col) with hL
  obtain ⟨n, β⟩ := Submodule.basisOfPid (Pi.basisFun ℤ (Fin b)) L
  have hmem : ∀ r, col r ∈ L := fun r => Submodule.subset_span ⟨r, rfl⟩
  set K' : Fin n → Fin R → ℤ := fun i r => β.repr ⟨col r, hmem r⟩ i with hK'
  set P' : Fin b → Fin n → ℤ := fun j i => (β i : Fin b → ℤ) j with hP'
  have hHPK : ∀ j r, (H j r : ℤ) = ∑ i, P' j i * K' i r := by
    intro j r
    have h := β.sum_repr ⟨col r, hmem r⟩
    have h2 := congrArg (fun y : L => (y : Fin b → ℤ) j) h
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul] at h2
    calc (H j r : ℤ) = col r j := rfl
      _ = _ := h2.symm
      _ = ∑ i, P' j i * K' i r := Finset.sum_congr rfl (fun i _ => mul_comm _ _)
  -- the dual surjectivity
  have hdual : ∀ θ : Fin n → ℝ, (∀ r, ∃ m : ℤ, KT K' θ r = 2 * π * m) →
      ∀ i, ∃ m : ℤ, θ i = 2 * π * m := by
    intro θ hθ i
    have hbi : (β i : Fin b → ℤ) ∈ Submodule.span ℤ (Set.range col) := (β i).2
    obtain ⟨w, hw⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hbi
    -- apply the coordinate map
    have hrep : ∀ i', (if i' = i then (1 : ℤ) else 0) = ∑ r, w r * K' i' r := by
      intro i'
      have h1 : β.repr (β i) i' = if i' = i then 1 else 0 := by
        rw [β.repr_self, Finsupp.single_apply]; simp [eq_comm]
      have h2 : (β i) = ∑ r, w r • (⟨col r, hmem r⟩ : L) := by
        apply Subtype.ext
        simp only [Submodule.coe_sum, Submodule.coe_smul]
        exact hw.symm
      rw [← h1, h2, map_sum]
      simp only [map_smul, Finsupp.coe_finset_sum, Finsupp.coe_smul, Finset.sum_apply,
        Pi.smul_apply, smul_eq_mul, hK']
    choose m hm using hθ
    refine ⟨∑ r, w r * m r, ?_⟩
    have : θ i = ∑ r, (w r : ℝ) * KT K' θ r := by
      simp only [KT, Finset.mul_sum]
      rw [Finset.sum_comm]
      have : θ i = ∑ i', θ i' * ((if i' = i then (1 : ℤ) else 0 : ℤ) : ℝ) := by
        simp
      rw [this]
      refine Finset.sum_congr rfl (fun i' _ => ?_)
      rw [hrep i']
      push_cast
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun r _ => by ring)
    rw [this]
    simp_rw [hm]
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun r _ => by ring)
  -- dimension count
  have hn_le : n ≤ b := by
    have h1 := Submodule.finrank_le L
    rw [Module.finrank_eq_card_basis β, Module.finrank_pi, Fintype.card_fin, Fintype.card_fin] at h1
    exact h1
  -- real matrices
  set Hr : Matrix (Fin b) (Fin R) ℝ := Matrix.of fun j r => (H j r : ℝ) with hHr
  set Pr : Matrix (Fin b) (Fin n) ℝ := Matrix.of fun j i => (P' j i : ℝ) with hPr
  set Kr : Matrix (Fin n) (Fin R) ℝ := Matrix.of fun i r => (K' i r : ℝ) with hKr
  have hmul : Hr = Pr * Kr := by
    ext j r
    simp only [hHr, hPr, hKr, Matrix.of_apply, Matrix.mul_apply]
    have := congrArg (fun z : ℤ => (z : ℝ)) (hHPK j r)
    simp only [Int.cast_natCast, Int.cast_sum, Int.cast_mul] at this
    exact this
  have hrankH : Hr.rank = b := by
    rw [Matrix.rank_eq_finrank_span_row, finrank_span_eq_card]
    · simp
    · exact hH
  have hb_le : b ≤ n := by
    have h1 : Hr.rank ≤ Pr.rank := by rw [hmul]; exact Matrix.rank_mul_le_left _ _
    have h2 : Pr.rank ≤ n := Matrix.rank_le_width Pr
    omega
  obtain rfl : n = b := le_antisymm hn_le hb_le
  refine ⟨K', Matrix.of P', fun j r => by simpa using hHPK j r, hdual, ?_⟩
  -- invertibility
  have hsurjH : Function.Surjective Hr.mulVecLin := by
    rw [← LinearMap.range_eq_top]
    apply Submodule.eq_top_of_finrank_eq
    rw [Module.finrank_pi, Fintype.card_fin]
    exact hrankH
  have hinjP : ∀ v : Fin n → ℝ, Pr *ᵥ v = 0 → v = 0 := by
    have hsurjP : Function.Surjective Pr.mulVecLin := by
      intro y
      obtain ⟨v, hv⟩ := hsurjH y
      refine ⟨Kr *ᵥ v, ?_⟩
      simp only [Matrix.mulVecLin_apply] at hv ⊢
      rw [Matrix.mulVec_mulVec, ← hmul]; exact hv
    have hinj := (LinearMap.injective_iff_surjective (f := Pr.mulVecLin)).2 hsurjP
    intro v hv
    exact hinj (by simpa using hv)
  have hdetR : Pr.det ≠ 0 := by
    intro h0
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    exact hv0 (hinjP v hv)
  intro hdet
  apply hdetR
  have : Pr = (Matrix.of P').map (Int.castRingHom ℝ) := by
    ext j i; simp [hPr]
  have h2 := (Int.castRingHom ℝ).map_det (Matrix.of P')
  rw [RingHom.mapMatrix_apply] at h2
  rw [this, ← h2, hdet, map_zero]

end GLL


open MeasureTheory Filter Topology Complex ProbabilityTheory
open scoped Real NNReal Matrix

namespace GLL

/-- Summability of product weights on `ℕ^b`. -/
lemma summable_pi_prod : ∀ (b : ℕ) (f : Fin b → ℕ → ℝ), (∀ j k, 0 ≤ f j k) →
    (∀ j, Summable (f j)) → Summable (fun m : Fin b → ℕ => ∏ j, f j (m j))
  | 0, f, _, _ => Summable.of_finite
  | b + 1, f, h0, hs => by
    have ih := summable_pi_prod b (fun j => f j.succ) (fun j k => h0 j.succ k)
      (fun j => hs j.succ)
    have hprod := (hs 0).mul_of_nonneg ih (fun k => h0 0 k)
      (fun m => Finset.prod_nonneg (fun j _ => h0 j.succ (m j)))
    rw [← (Fin.consEquiv (fun _ : Fin (b + 1) => ℕ)).summable_iff]
    refine hprod.congr (fun p => ?_)
    simp only [Function.comp, Fin.consEquiv_apply, Fin.prod_univ_succ, Fin.cons_zero,
      Fin.cons_succ]

lemma summable_geom_pi (b : ℕ) {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ < 1) :
    Summable (fun m : Fin b → ℕ => ∏ j, ρ ^ (m j)) :=
  summable_pi_prod b (fun _ k => ρ ^ k) (fun _ _ => pow_nonneg h0 _)
    (fun _ => summable_geometric_of_lt_one h0 h1)

lemma summable_geom_pi_mul (b : ℕ) {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ < 1) :
    Summable (fun m : Fin b → ℕ => ((∑ j, m j : ℕ) : ℝ) * ∏ j, ρ ^ (m j)) := by
  have : (fun m : Fin b → ℕ => ((∑ j, m j : ℕ) : ℝ) * ∏ j, ρ ^ (m j)) =
      fun m => ∑ j0, ∏ j, (if j = j0 then (m j : ℝ) * ρ ^ (m j) else ρ ^ (m j)) := by
    funext m
    push_cast
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun j0 _ => ?_)
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j0)]
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j0)]
    rw [if_pos rfl, mul_assoc]
    congr 2
    refine Finset.prod_congr rfl (fun j hj => ?_)
    rw [if_neg (Finset.ne_of_mem_erase hj)]
  rw [this]
  refine summable_sum (fun j0 _ => ?_)
  refine summable_pi_prod b (fun j k => if j = j0 then (k : ℝ) * ρ ^ k else ρ ^ k)
    (fun j k => by split_ifs <;> positivity) (fun j => ?_)
  split_ifs
  · exact summable_pow_mul_geometric_of_norm_lt_one 1 (by rwa [Real.norm_eq_abs, abs_of_nonneg h0])
      |>.congr (fun k => by simp)
  · exact summable_geometric_of_lt_one h0 h1

section weights
variable {b : ℕ}

/-- geometric weight on `ℤ^b`, supported on `ℕ^b` -/
noncomputable def geomW (q : Fin b → ℝ) (m : Fin b → ℤ) : ℝ :=
  if ∀ j, 0 ≤ m j then ∏ j, q j ^ (m j).toNat else 0

lemma geomW_nonneg {q : Fin b → ℝ} (hq : ∀ j, 0 ≤ q j) (m : Fin b → ℤ) : 0 ≤ geomW q m := by
  unfold geomW; split_ifs
  · exact Finset.prod_nonneg (fun j _ => pow_nonneg (hq j) _)
  · exact le_rfl

lemma geomW_le {q : Fin b → ℝ} {ρ : ℝ} (hq : ∀ j, 0 ≤ q j) (hqρ : ∀ j, q j ≤ ρ)
    (m : Fin b → ℤ) : geomW q m ≤ geomW (fun _ => ρ) m := by
  unfold geomW; split_ifs
  · exact Finset.prod_le_prod (fun j _ => pow_nonneg (hq j) _)
      (fun j _ => pow_le_pow_left₀ (hq j) (hqρ j) _)
  · exact le_rfl

lemma natCast_pi_injective : Function.Injective (fun m : Fin b → ℕ => fun j => (m j : ℤ)) := by
  intro m m' h
  funext j
  have := congrFun h j
  simpa using this

lemma geomW_support {q : Fin b → ℝ} (m : Fin b → ℤ) (hm : m ∉ Set.range
    (fun m : Fin b → ℕ => fun j => (m j : ℤ))) : geomW q m = 0 := by
  unfold geomW
  rw [if_neg]
  intro h
  apply hm
  exact ⟨fun j => (m j).toNat, funext fun j => Int.toNat_of_nonneg (h j)⟩

lemma geomW_comp (q : Fin b → ℝ) (m : Fin b → ℕ) :
    geomW q (fun j => (m j : ℤ)) = ∏ j, q j ^ (m j) := by
  unfold geomW
  rw [if_pos (fun j => Int.natCast_nonneg _)]
  simp

lemma summable_geomW {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ < 1) :
    Summable (geomW (b := b) (fun _ => ρ)) := by
  rw [← natCast_pi_injective.summable_iff (fun m hm => geomW_support m hm)]
  refine (summable_geom_pi b h0 h1).congr (fun m => ?_)
  simp only [Function.comp, geomW_comp]

/-- the `ℓ¹` size of an integer vector -/
noncomputable def l1 (m : Fin b → ℤ) : ℝ := ∑ j, |(m j : ℝ)|

lemma summable_geomW_l1 {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ < 1) :
    Summable (fun m : Fin b → ℤ => l1 m * geomW (fun _ => ρ) m) := by
  rw [← natCast_pi_injective.summable_iff (fun m hm => by simp [geomW_support m hm])]
  refine (summable_geom_pi_mul b h0 h1).congr (fun m => ?_)
  simp only [Function.comp, geomW_comp, l1]
  congr 1
  push_cast
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [abs_of_nonneg (by positivity)]

/-- the weight in the `K` coordinates -/
noncomputable def psiW (P : Matrix (Fin b) (Fin b) ℤ) (q : Fin b → ℝ) (c : Fin b → ℤ)
    (k : Fin b → ℤ) : ℝ := geomW q (c - P *ᵥ k)

lemma mulVec_injective {P : Matrix (Fin b) (Fin b) ℤ} (hP : P.det ≠ 0) :
    Function.Injective (fun k : Fin b → ℤ => P *ᵥ k) := by
  intro k k' h
  by_contra hne
  apply hP
  apply Matrix.exists_mulVec_eq_zero_iff.1
  refine ⟨k - k', sub_ne_zero.2 hne, ?_⟩
  rw [Matrix.mulVec_sub]
  exact sub_eq_zero.2 h

lemma sub_mulVec_injective {P : Matrix (Fin b) (Fin b) ℤ} (hP : P.det ≠ 0) (c : Fin b → ℤ) :
    Function.Injective (fun k : Fin b → ℤ => c - P *ᵥ k) := by
  intro k k' h
  exact mulVec_injective hP (sub_right_injective h)

lemma summable_geomW_of_le {q : Fin b → ℝ} {ρ : ℝ}
    (hq : ∀ j, 0 ≤ q j) (hqρ : ∀ j, q j ≤ ρ) (hρ0 : 0 ≤ ρ) (hρ : ρ < 1) :
    Summable (geomW q) :=
  Summable.of_nonneg_of_le (geomW_nonneg hq) (geomW_le hq hqρ) (summable_geomW hρ0 hρ)

lemma summable_psiW {P : Matrix (Fin b) (Fin b) ℤ} (hP : P.det ≠ 0) {q : Fin b → ℝ} {ρ : ℝ}
    (hq : ∀ j, 0 ≤ q j) (hqρ : ∀ j, q j ≤ ρ) (hρ0 : 0 ≤ ρ) (hρ : ρ < 1) (c : Fin b → ℤ) :
    Summable (psiW P q c) :=
  (summable_geomW_of_le hq hqρ hρ0 hρ).comp_injective (sub_mulVec_injective hP c)

lemma psiW_nonneg (P : Matrix (Fin b) (Fin b) ℤ) {q : Fin b → ℝ} (hq : ∀ j, 0 ≤ q j)
    (c : Fin b → ℤ) (k : Fin b → ℤ) : 0 ≤ psiW P q c k := geomW_nonneg hq _

lemma tsum_psiW_le {P : Matrix (Fin b) (Fin b) ℤ} (hP : P.det ≠ 0) {q : Fin b → ℝ} {ρ : ℝ}
    (hq : ∀ j, 0 ≤ q j) (hqρ : ∀ j, q j ≤ ρ) (hρ0 : 0 ≤ ρ) (hρ : ρ < 1) (c : Fin b → ℤ) :
    ∑' k, psiW P q c k ≤ ∑' m, geomW (b := b) (fun _ => ρ) m := by
  calc ∑' k, psiW P q c k ≤ ∑' m, geomW q m :=
        tsum_comp_le_tsum_of_inj (summable_geomW_of_le hq hqρ hρ0 hρ) (geomW_nonneg hq)
          (sub_mulVec_injective hP c)
    _ ≤ _ := (summable_geomW_of_le hq hqρ hρ0 hρ).tsum_le_tsum (geomW_le hq hqρ)
        (summable_geomW hρ0 hρ)

lemma sum_sq_le_sq_sum (a : Fin b → ℝ) : ∑ j, a j ^ 2 ≤ (∑ j, |a j|) ^ 2 := by
  have hS : ∀ j, |a j| ≤ ∑ j, |a j| := fun j =>
    Finset.single_le_sum (f := fun j => |a j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
  calc ∑ j, a j ^ 2 = ∑ j, |a j| * |a j| := by
        refine Finset.sum_congr rfl (fun j _ => ?_); rw [← sq, sq_abs]
    _ ≤ ∑ j, |a j| * ∑ j, |a j| :=
        Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hS j) (abs_nonneg _))
    _ = (∑ j, |a j|) ^ 2 := by rw [← Finset.sum_mul, sq]

lemma real_det_ne_zero {P : Matrix (Fin b) (Fin b) ℤ} (hP : P.det ≠ 0) :
    (P.map (Int.castRingHom ℝ)).det ≠ 0 := by
  have h2 := (Int.castRingHom ℝ).map_det P
  rw [RingHom.mapMatrix_apply] at h2
  rw [← h2]
  simpa using hP

/-- quantitative injectivity of `P` on real vectors -/
lemma P_coercive {P : Matrix (Fin b) (Fin b) ℤ} (hP : P.det ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : Fin b → ℝ,
      ∑ i, |v i| ≤ C * ∑ j, |∑ i, (P j i : ℝ) * v i| := by
  set K : Fin b → Fin b → ℤ := fun i j => P j i with hK
  have hKT : ∀ v j, KT K v j = ∑ i, (P j i : ℝ) * v i := fun v j => rfl
  have hinj : ∀ v : Fin b → ℝ, (∀ r, KT K v r = 0) → v = 0 := by
    intro v hv
    by_contra hne
    apply real_det_ne_zero hP
    apply Matrix.exists_mulVec_eq_zero_iff.1
    refine ⟨v, hne, funext fun j => ?_⟩
    have := hv j
    rw [hKT] at this
    simpa [Matrix.mulVec, dotProduct] using this
  obtain ⟨lam, hlam, hco⟩ := exists_coercive K hinj
  refine ⟨b / Real.sqrt lam, by positivity, fun v => ?_⟩
  set S := ∑ j, |∑ i, (P j i : ℝ) * v i| with hS
  have h1 : lam * ‖v‖ ^ 2 ≤ S ^ 2 := by
    refine le_trans (hco v) ?_
    simp_rw [hKT]
    exact sum_sq_le_sq_sum _
  have h2 : Real.sqrt lam * ‖v‖ ≤ S := by
    have hS0 : 0 ≤ S := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
    have : (Real.sqrt lam * ‖v‖) ^ 2 ≤ S ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hlam.le]; exact h1
    exact (pow_le_pow_iff_left₀ (by positivity) hS0 (by norm_num : (2:ℕ) ≠ 0)).1 this
  have h3 : ∑ i, |v i| ≤ b * ‖v‖ := by
    calc ∑ i, |v i| ≤ ∑ _i : Fin b, ‖v‖ := Finset.sum_le_sum (fun i _ => by
          have := norm_le_pi_norm v i; rwa [Real.norm_eq_abs] at this)
      _ = b * ‖v‖ := by simp
  have hsl : 0 < Real.sqrt lam := Real.sqrt_pos.2 hlam
  calc ∑ i, |v i| ≤ b * ‖v‖ := h3
    _ = b / Real.sqrt lam * (Real.sqrt lam * ‖v‖) := by field_simp
    _ ≤ b / Real.sqrt lam * S := by gcongr


lemma psiHat_zero {R : ℕ} (K : Fin b → Fin R → ℤ) (x : Fin R → ℝ) (ψ : (Fin b → ℤ) → ℝ) :
    psiHat K x ψ 0 = ((∑' k, ψ k : ℝ) : ℂ) := by
  unfold psiHat
  rw [Complex.ofReal_tsum]
  refine tsum_congr (fun k => ?_)
  simp

lemma psiHat_lip {R : ℕ} (K : Fin b → Fin R → ℤ) (x : Fin R → ℝ)
    {P : Matrix (Fin b) (Fin b) ℤ} (hP : P.det ≠ 0) {q : Fin b → ℝ} {ρ : ℝ}
    (hq : ∀ j, 0 ≤ q j) (hqρ : ∀ j, q j ≤ ρ) (hρ0 : 0 ≤ ρ) (hρ : ρ < 1) (c : Fin b → ℤ)
    (hc : ∀ j, (c j : ℝ) = ∑ i, (P j i : ℝ) * Kx K x i)
    {CP : ℝ} (hCP0 : 0 ≤ CP)
    (hCP : ∀ v : Fin b → ℝ, ∑ i, |v i| ≤ CP * ∑ j, |∑ i, (P j i : ℝ) * v i|)
    (θ : Fin b → ℝ) :
    ‖psiHat K x (psiW P q c) θ - psiHat K x (psiW P q c) 0‖ ≤
      (CP * ∑' m, l1 m * geomW (b := b) (fun _ => ρ) m) * ‖θ‖ := by
  set ψ := psiW P q c with hψ
  set y := Kx K x with hy
  set T : (Fin b → ℤ) → (Fin b → ℝ) → ℂ := fun k θ =>
    (ψ k : ℂ) * cexp (-(I * ((∑ i, θ i * ((k i : ℝ) - y i) : ℝ) : ℂ))) with hT
  have hψ0 : ∀ k, 0 ≤ ψ k := psiW_nonneg P hq c
  have hψs : Summable ψ := summable_psiW hP hq hqρ hρ0 hρ c
  have hTn : ∀ k θ, ‖T k θ‖ = ψ k := by
    intro k θ
    simp only [hT]
    rw [norm_mul, Complex.norm_exp]
    simp [abs_of_nonneg (hψ0 k)]
  have hTs : ∀ θ, Summable (fun k => T k θ) := fun θ =>
    Summable.of_norm (hψs.congr (fun k => (hTn k θ).symm))
  have hsub : psiHat K x ψ θ - psiHat K x ψ 0 = ∑' k, (T k θ - T k 0) := by
    rw [Summable.tsum_sub (hTs θ) (hTs 0)]
    rfl
  rw [hsub]
  -- the majorant
  set g : (Fin b → ℤ) → ℝ := fun k => ‖θ‖ * CP * (l1 (c - P *ᵥ k) *
    geomW (fun _ => ρ) (c - P *ᵥ k)) with hg
  have hgs : Summable g := by
    have := (summable_geomW_l1 (b := b) hρ0 hρ).comp_injective (sub_mulVec_injective hP c)
    exact this.mul_left (‖θ‖ * CP)
  have hbound : ∀ k, ‖T k θ - T k 0‖ ≤ g k := by
    intro k
    have h0 : T k 0 = ψ k := by simp [hT]
    rw [h0]
    have e : T k θ - (ψ k : ℂ) = (ψ k : ℂ) *
        (cexp (I * ((-(∑ i, θ i * ((k i : ℝ) - y i)) : ℝ) : ℂ)) - 1) := by
      simp only [hT]; push_cast; ring_nf
    rw [e, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hψ0 k)]
    have h1 := Real.norm_exp_I_mul_ofReal_sub_one_le (x := -(∑ i, θ i * ((k i : ℝ) - y i)))
    rw [Real.norm_eq_abs, abs_neg] at h1
    have h2 : |∑ i, θ i * ((k i : ℝ) - y i)| ≤ ‖θ‖ * ∑ i, |(k i : ℝ) - y i| := by
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum (fun i _ => ?_)
      rw [abs_mul]
      have := norm_le_pi_norm θ i
      rw [Real.norm_eq_abs] at this
      exact mul_le_mul_of_nonneg_right this (abs_nonneg _)
    have h3 : ∑ i, |(k i : ℝ) - y i| ≤ CP * l1 (c - P *ᵥ k) := by
      have := hCP (fun i => (k i : ℝ) - y i)
      refine le_trans this (le_of_eq ?_)
      congr 1
      unfold l1
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [← abs_neg]
      congr 1
      simp only [Pi.sub_apply, Matrix.mulVec, dotProduct, Int.cast_sub, Int.cast_sum,
        Int.cast_mul, hc j, mul_sub, Finset.sum_sub_distrib]
      ring
    have h4 : ψ k ≤ geomW (fun _ => ρ) (c - P *ᵥ k) := geomW_le hq hqρ _
    have hl0 : 0 ≤ l1 (c - P *ᵥ k) := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
    calc ψ k * ‖cexp (I * ((-(∑ i, θ i * ((k i : ℝ) - y i)) : ℝ) : ℂ)) - 1‖
        ≤ ψ k * (‖θ‖ * (CP * l1 (c - P *ᵥ k))) := by
          refine mul_le_mul_of_nonneg_left (le_trans h1 (le_trans h2 ?_)) (hψ0 k)
          exact mul_le_mul_of_nonneg_left h3 (norm_nonneg _)
      _ ≤ geomW (fun _ => ρ) (c - P *ᵥ k) * (‖θ‖ * (CP * l1 (c - P *ᵥ k))) :=
          mul_le_mul_of_nonneg_right h4 (by positivity)
      _ = g k := by simp only [hg]; ring
  have hns : Summable (fun k => ‖T k θ - T k 0‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hbound hgs
  calc ‖∑' k, (T k θ - T k 0)‖ ≤ ∑' k, ‖T k θ - T k 0‖ := norm_tsum_le_tsum_norm hns
    _ ≤ ∑' k, g k := hns.tsum_le_tsum hbound hgs
    _ = ‖θ‖ * CP * ∑' k, l1 (c - P *ᵥ k) * geomW (fun _ => ρ) (c - P *ᵥ k) := by
        rw [hg, tsum_mul_left]
    _ ≤ ‖θ‖ * CP * ∑' m, l1 m * geomW (b := b) (fun _ => ρ) m := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact tsum_comp_le_tsum_of_inj (f := fun m => l1 m * geomW (b := b) (fun _ => ρ) m)
          (summable_geomW_l1 hρ0 hρ)
          (fun m => mul_nonneg (Finset.sum_nonneg (fun _ _ => abs_nonneg _))
            (geomW_nonneg (fun _ => hρ0) m)) (sub_mulVec_injective hP c)
    _ = _ := by ring


/-- every residue class contains a small nonnegative representative -/
lemma exists_small_rep {P : Matrix (Fin b) (Fin b) ℤ} (hP : P.det ≠ 0) (c : Fin b → ℤ) :
    ∃ k : Fin b → ℤ, ∀ j, 0 ≤ (c - P *ᵥ k) j ∧ (c - P *ᵥ k) j ≤ P.det.natAbs := by
  set D : ℤ := (P.det.natAbs : ℤ) with hD
  have hDpos : 0 < D := by rw [hD]; exact_mod_cast Int.natAbs_pos.2 hP
  set w : Fin b → ℤ := fun j => c j / D with hw
  refine ⟨P.det.sign • (P.adjugate *ᵥ w), fun j => ?_⟩
  have hPk : P *ᵥ (P.det.sign • (P.adjugate *ᵥ w)) = D • w := by
    rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.mul_adjugate, Matrix.smul_mulVec,
      Matrix.one_mulVec, smul_smul]
    congr 1
    rw [hD]; exact Int.sign_mul_self _
  rw [hPk]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hw]
  rw [← Int.emod_def]
  have h2 := Int.emod_nonneg (c j) hDpos.ne'
  have h3 := Int.emod_lt_of_pos (c j) hDpos
  constructor <;> omega

lemma tsum_psiW_ge {P : Matrix (Fin b) (Fin b) ℤ} (hP : P.det ≠ 0) {q : Fin b → ℝ} {ρ : ℝ}
    (hq : ∀ j, 0 ≤ q j) (hq1 : ∀ j, q j ≤ 1) (hqρ : ∀ j, q j ≤ ρ) (hρ0 : 0 ≤ ρ) (hρ : ρ < 1)
    (c : Fin b → ℤ) :
    ∏ j, q j ^ P.det.natAbs ≤ ∑' k, psiW P q c k := by
  obtain ⟨k, hk⟩ := exists_small_rep hP c
  refine le_trans ?_ (Summable.le_tsum (summable_psiW hP hq hqρ hρ0 hρ c) k
    (fun k' _ => psiW_nonneg P hq c k'))
  unfold psiW geomW
  rw [if_pos (fun j => (hk j).1)]
  refine Finset.prod_le_prod (fun j _ => pow_nonneg (hq j) _) (fun j _ => ?_)
  apply pow_le_pow_of_le_one (hq j) (hq1 j)
  have := (hk j).2
  omega


end weights

lemma exists_upper {b : ℕ} (qb : Fin b → ℝ) (h : ∀ j, qb j < 1) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧ ∀ j, qb j < ρ := by
  classical
  let S : Finset ℝ := insert 0 (Finset.univ.image qb)
  have hS : S.Nonempty := ⟨0, Finset.mem_insert_self _ _⟩
  set M := S.max' hS
  have hM1 : M < 1 := by
    have := S.max'_mem hS
    rcases Finset.mem_insert.1 this with h' | h'
    · rw [show M = 0 from h']; norm_num
    · obtain ⟨j, -, hj⟩ := Finset.mem_image.1 h'
      rw [show M = qb j from hj.symm]; exact h j
  have hM0 : 0 ≤ M := S.le_max' _ (Finset.mem_insert_self _ _)
  refine ⟨(M + 1) / 2, by linarith, by linarith, fun j => ?_⟩
  have : qb j ≤ M := S.le_max' _ (Finset.mem_insert_of_mem
    (Finset.mem_image_of_mem _ (Finset.mem_univ j)))
  linarith

/-- ratio of two sequences with a common bounded-below amplitude -/
lemma ratio_tendsto {X Y : ℕ → ℂ} {a : ℕ → ℝ} {GX GY : ℂ} {δ C : ℝ} (hδ : 0 < δ)
    (ha : ∀ᶠ N in atTop, δ ≤ a N ∧ a N ≤ C) (hGY : GY ≠ 0)
    (hX : Tendsto (fun N => X N - (a N : ℂ) * GX) atTop (𝓝 0))
    (hY : Tendsto (fun N => Y N - (a N : ℂ) * GY) atTop (𝓝 0)) :
    Tendsto (fun N => X N / Y N) atTop (𝓝 (GX / GY)) := by
  have hGYn : 0 < ‖GY‖ := norm_pos_iff.2 hGY
  have hnum : Tendsto (fun N => (X N - (a N : ℂ) * GX) * GY - (Y N - (a N : ℂ) * GY) * GX)
      atTop (𝓝 0) := by
    simpa using (hX.mul_const GY).sub (hY.mul_const GX)
  have hYlow : ∀ᶠ N in atTop, δ * ‖GY‖ / 2 ≤ ‖Y N‖ := by
    have h := hY.norm
    rw [norm_zero] at h
    filter_upwards [ha, h.eventually (gt_mem_nhds (by positivity : (0:ℝ) < δ * ‖GY‖ / 2))]
      with N hN h2
    have e1 : ‖(a N : ℂ) * GY‖ = a N * ‖GY‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (lt_of_lt_of_le hδ hN.1)]
    have e2 : ‖(a N : ℂ) * GY‖ ≤ ‖Y N‖ + ‖Y N - (a N : ℂ) * GY‖ := by
      have := norm_sub_le (Y N) (Y N - (a N : ℂ) * GY)
      simpa using this
    have e3 : δ * ‖GY‖ ≤ a N * ‖GY‖ := mul_le_mul_of_nonneg_right hN.1 (norm_nonneg _)
    linarith
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hb : Tendsto (fun N => ‖(X N - (a N : ℂ) * GX) * GY - (Y N - (a N : ℂ) * GY) * GX‖ /
      (δ * ‖GY‖ / 2 * ‖GY‖)) atTop (𝓝 0) := by
    simpa using hnum.norm.div_const (δ * ‖GY‖ / 2 * ‖GY‖)
  refine squeeze_zero' (Eventually.of_forall fun N => norm_nonneg _) ?_ hb
  filter_upwards [hYlow] with N hN
  have hY0 : Y N ≠ 0 := by
    intro h; rw [h, norm_zero] at hN
    have : 0 < δ * ‖GY‖ / 2 := by positivity
    linarith
  have : X N / Y N - GX / GY =
      ((X N - (a N : ℂ) * GX) * GY - (Y N - (a N : ℂ) * GY) * GX) / (Y N * GY) := by
    field_simp; ring
  rw [this, norm_div, norm_mul]
  apply div_le_div_of_nonneg_left (norm_nonneg _) (by positivity)
  exact mul_le_mul_of_nonneg_right hN (norm_nonneg _)

section relaxed
variable {b R : ℕ}

/-- **Relaxed local asymptotics**: Fourier representation plus Laplace asymptotics. -/
theorem relaxed_asymp (H : Fin b → Fin R → ℕ) (K : Fin b → Fin R → ℤ)
    (P : Matrix (Fin b) (Fin b) ℤ) (hHPK : ∀ j r, (H j r : ℤ) = ∑ i, P j i * K i r)
    (hK : ∀ θ : Fin b → ℝ, (∀ r, ∃ m : ℤ, KT K θ r = 2 * π * m) → ∀ i, ∃ m : ℤ, θ i = 2 * π * m)
    (hP : P.det ≠ 0)
    (x : ℕ → Fin R → ℝ) (xb : Fin R → ℝ) (hxb : ∀ r, 0 < xb r)
    (hx : ∀ r, Tendsto (fun N : ℕ => x N r / N) atTop (𝓝 (xb r)))
    (q : ℕ → Fin b → ℝ) (qb : Fin b → ℝ) (hqb0 : ∀ j, 0 < qb j) (hqb1 : ∀ j, qb j < 1)
    (hq : ∀ j, Tendsto (fun N => q N j) atTop (𝓝 (qb j)))
    (c : ℕ → Fin b → ℤ) (hc : ∀ᶠ N in atTop, ∀ j, (c N j : ℝ) = ∑ r, (H j r : ℝ) * x N r)
    (ζ : Fin R → ℂ) :
    Tendsto (fun N : ℕ => ((Real.sqrt N ^ b : ℝ) : ℂ) * ((2 * π) ^ b : ℂ) *
        (∫ n, (psiW P (q N) (c N) (Kn K n) : ℂ) *
          cexp (∑ r, ζ r * ((((n r : ℝ) - x N r) / Real.sqrt N : ℝ) : ℂ)) ∂(poisPi (x N)))
        - ((∑' k, psiW P (q N) (c N) k : ℝ) : ℂ) * gaussInt K xb ζ) atTop (𝓝 0) := by
  classical
  obtain ⟨ρ, hρ0, hρ1, hqbρ⟩ := exists_upper qb hqb1
  obtain ⟨CP, hCP0, hCP⟩ := P_coercive hP
  -- good indices
  set good : ℕ → Prop := fun N => (∀ j, 0 ≤ q N j ∧ q N j ≤ ρ) ∧ (∀ r, 0 ≤ x N r) ∧
    (∀ j, (c N j : ℝ) = ∑ r, (H j r : ℝ) * x N r) with hgood
  have hgoodev : ∀ᶠ N in atTop, good N := by
    have h1 : ∀ᶠ N in atTop, ∀ j, 0 ≤ q N j ∧ q N j ≤ ρ := by
      rw [eventually_all]; intro j
      filter_upwards [(hq j).eventually (lt_mem_nhds (hqb0 j)),
        (hq j).eventually (gt_mem_nhds (hqbρ j))] with N h1 h2
      exact ⟨h1.le, h2.le⟩
    have h2 : ∀ᶠ N : ℕ in atTop, ∀ r, 0 ≤ x N r := by
      rw [eventually_all]; intro r
      filter_upwards [(hx r).eventually (lt_mem_nhds (hxb r)), eventually_gt_atTop 0]
        with N h hN
      have hNp : (0:ℝ) < N := by exact_mod_cast hN
      exact (div_pos_iff_of_pos_right hNp).1 h |>.le
    filter_upwards [h1, h2, hc] with N a1 a2 a3
    exact ⟨a1, a2, a3⟩
  have hcK : ∀ N, good N → ∀ j, (c N j : ℝ) = ∑ i, (P j i : ℝ) * Kx K (x N) i := by
    intro N hN j
    rw [hN.2.2 j]
    simp only [Kx, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    have := congrArg (fun z : ℤ => (z : ℝ)) (hHPK j r)
    simp only [Int.cast_natCast, Int.cast_sum, Int.cast_mul] at this
    rw [this, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun i _ => by ring)
  set S0 := ∑' m, geomW (b := b) (fun _ => ρ) m with hS0
  set S1 := ∑' m, l1 m * geomW (b := b) (fun _ => ρ) m with hS1
  set Cψ := max S0 (CP * S1) with hCψ
  set Ψ : ℕ → (Fin b → ℝ) → ℂ := fun N θ =>
    if good N then psiHat K (x N) (psiW P (q N) (c N)) θ else 0 with hΨ
  have hΨc : ∀ N, Continuous (Ψ N) := by
    intro N
    simp only [hΨ]
    split_ifs with hN
    · exact psiHat_cont K (x N) _ (psiW_nonneg P (fun j => (hN.1 j).1) _)
        (summable_psiW hP (fun j => (hN.1 j).1) (fun j => (hN.1 j).2) hρ0.le hρ1 _)
    · exact continuous_const
  have hΨb : ∀ N θ, ‖Ψ N θ‖ ≤ Cψ := by
    intro N θ
    simp only [hΨ]
    split_ifs with hN
    · have hq0 := fun j => (hN.1 j).1
      have hqρ := fun j => (hN.1 j).2
      refine le_trans (psiHat_norm_le K (x N) _ (psiW_nonneg P hq0 _)
        (summable_psiW hP hq0 hqρ hρ0.le hρ1 _) θ) ?_
      exact le_trans (tsum_psiW_le hP hq0 hqρ hρ0.le hρ1 _) (le_max_left _ _)
    · simp only [norm_zero]
      exact le_trans (tsum_nonneg (geomW_nonneg (fun _ => hρ0.le))) (le_max_left _ _)
  have hΨl : ∀ N θ, ‖Ψ N θ - Ψ N 0‖ ≤ Cψ * ‖θ‖ := by
    intro N θ
    simp only [hΨ]
    split_ifs with hN
    · have hq0 := fun j => (hN.1 j).1
      have hqρ := fun j => (hN.1 j).2
      refine le_trans (psiHat_lip K (x N) hP hq0 hqρ hρ0.le hρ1 (c N) (hcK N hN) hCP0 hCP θ) ?_
      exact mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)
    · simp only [sub_zero, norm_zero]
      have : 0 ≤ Cψ := le_trans (tsum_nonneg (geomW_nonneg (fun _ => hρ0.le))) (le_max_left _ _)
      positivity
  have hL := laplace_main K hK x xb hxb hx Ψ hΨc Cψ hΨb hΨl ζ
  refine hL.congr' ?_
  filter_upwards [hgoodev] with N hN
  have hq0 := fun j => (hN.1 j).1
  have hqρ := fun j => (hN.1 j).2
  simp only [hΨ, if_pos hN]
  rw [fourier_repr K (x N) hN.2.1 (psiW P (q N) (c N)) (psiW_nonneg P hq0 _)
    (summable_psiW hP hq0 hqρ hρ0.le hρ1 _) ζ N, psiHat_zero]
  have h2π : ((2 * π) ^ b : ℂ) ≠ 0 := by
    have : (2 * π : ℂ) ≠ 0 := by
      have := Real.pi_pos; exact_mod_cast (by positivity : (2 * π : ℝ) ≠ 0)
    exact pow_ne_zero _ this
  field_simp

end relaxed

section gauss
variable {b R : ℕ} (K : Fin b → Fin R → ℤ)

lemma gaussF_zero (xb : Fin R → ℝ) (s : Fin b → ℝ) :
    gaussF K xb 0 s = ((Real.exp (-(∑ r, xb r * KT K s r ^ 2) / 2) : ℝ) : ℂ) := by
  unfold gaussF
  rw [Complex.ofReal_exp]
  congr 1
  push_cast
  rw [neg_div, Finset.sum_div, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  simp only [Pi.zero_apply, zero_add]
  rw [mul_pow, Complex.I_sq]; ring

lemma gauss_real_integrable (hK : ∀ s : Fin b → ℝ, (∀ r, KT K s r = 0) → s = 0)
    (xb : Fin R → ℝ) (hxb : ∀ r, 0 < xb r) :
    Integrable (fun s : Fin b → ℝ => Real.exp (-(∑ r, xb r * KT K s r ^ 2) / 2)) := by
  obtain ⟨lam, hlam, hco⟩ := exists_coercive K hK
  obtain ⟨m0, hm0, hm0le⟩ := exists_pos_lower xb hxb
  set c := m0 * lam / 2 with hc
  have hc0 : 0 < c := by positivity
  have hb := gauss_bound_integrable b 0 (c / (b + 1)) (by positivity)
  refine Integrable.mono' hb (Continuous.aestronglyMeasurable (by
    have := fun r => KT_cont K r
    fun_prop)) (Eventually.of_forall fun s => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_zero, one_mul]
  refine le_trans ?_ (exp_neg_norm_sq_le b hc0.le s)
  apply Real.exp_le_exp.2
  have h1 : m0 * ∑ r, KT K s r ^ 2 ≤ ∑ r, xb r * KT K s r ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun r _ => mul_le_mul_of_nonneg_right (hm0le r) (sq_nonneg _))
  have h2 := mul_le_mul_of_nonneg_left (hco s) hm0.le
  rw [hc]
  nlinarith

lemma gaussInt_zero_re_pos (hK : ∀ s : Fin b → ℝ, (∀ r, KT K s r = 0) → s = 0)
    (xb : Fin R → ℝ) (hxb : ∀ r, 0 < xb r) :
    ∃ g : ℝ, 0 < g ∧ gaussInt K xb 0 = (g : ℂ) := by
  refine ⟨∫ s, Real.exp (-(∑ r, xb r * KT K s r ^ 2) / 2), ?_, ?_⟩
  · rw [integral_pos_iff_support_of_nonneg (fun s => (Real.exp_pos _).le)
      (gauss_real_integrable K hK xb hxb)]
    have : Function.support (fun s : Fin b → ℝ => Real.exp (-(∑ r, xb r * KT K s r ^ 2) / 2))
        = Set.univ := by
      ext s; simp [(Real.exp_pos _).ne']
    rw [this, Measure.measure_univ_pos]
    exact NeZero.ne volume
  · unfold gaussInt
    simp_rw [gaussF_zero]
    exact integral_ofReal

/-- The conditioned-Gaussian identity for the limiting integral. -/
lemma gaussInt_I (H : Fin b → Fin R → ℕ) (P : Matrix (Fin b) (Fin b) ℤ)
    (hHPK : ∀ j r, (H j r : ℤ) = ∑ i, P j i * K i r) (hP : P.det ≠ 0)
    (xb : Fin R → ℝ) (ξ v : Fin R → ℝ) (t : Fin b → ℝ)
    (hv1 : ∀ r, v r = ξ r + ∑ j, (H j r : ℝ) * t j)
    (hv2 : ∀ j, ∑ r, (H j r : ℝ) * xb r * v r = 0) :
    gaussInt K xb (fun r => I * ξ r) =
      cexp (-((∑ r, xb r * v r ^ 2 : ℝ) : ℂ) / 2) * gaussInt K xb 0 := by
  -- shift vector
  set t' : Fin b → ℝ := fun i => ∑ j, (P j i : ℝ) * t j with ht'
  have hHt : ∀ r, ∑ j, (H j r : ℝ) * t j = KT K t' r := by
    intro r
    simp only [KT, ht', Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    have := congrArg (fun z : ℤ => (z : ℝ)) (hHPK j r)
    simp only [Int.cast_natCast, Int.cast_sum, Int.cast_mul] at this
    rw [this, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun i _ => by ring)
  -- orthogonality in K coordinates
  have hz : ∀ i, ∑ r, (K i r : ℝ) * xb r * v r = 0 := by
    set z : Fin b → ℝ := fun i => ∑ r, (K i r : ℝ) * xb r * v r with hzdef
    have hPz : (P.map (Int.castRingHom ℝ)) *ᵥ z = 0 := by
      funext j
      simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Int.coe_castRingHom, hzdef,
        Pi.zero_apply, Finset.mul_sum]
      rw [Finset.sum_comm, ← hv2 j]
      refine Finset.sum_congr rfl (fun r _ => ?_)
      have := congrArg (fun z : ℤ => (z : ℝ)) (hHPK j r)
      simp only [Int.cast_natCast, Int.cast_sum, Int.cast_mul] at this
      rw [this, Finset.sum_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun i _ => by ring)
    intro i
    by_contra hne
    apply real_det_ne_zero hP
    exact Matrix.exists_mulVec_eq_zero_iff.1 ⟨z, fun h => hne (congrFun h i), hPz⟩
  have hpt : ∀ s : Fin b → ℝ, gaussF K xb (fun r => I * ξ r) s =
      cexp (-((∑ r, xb r * v r ^ 2 : ℝ) : ℂ) / 2) * gaussF K xb 0 (s - t') := by
    intro s
    have hsplit : ∀ r, ξ r + KT K s r = v r + KT K (s - t') r := by
      intro r
      rw [hv1 r, hHt r]
      simp only [KT, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
      ring
    have hcross : ∑ r, xb r * v r * KT K (s - t') r = 0 := by
      simp only [KT, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero (fun i _ => ?_)
      have := hz i
      rw [← mul_zero ((s - t') i), ← this, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun r _ => by ring)
    rw [gaussF_zero]
    unfold gaussF
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    have e1 : ∀ r, (xb r : ℂ) * (I * ξ r + I * (KT K s r : ℂ)) ^ 2 / 2 =
        -((xb r * (v r + KT K (s - t') r) ^ 2 : ℝ) : ℂ) / 2 := by
      intro r
      rw [← hsplit r]
      push_cast
      rw [← mul_add, mul_pow, Complex.I_sq]; ring
    simp_rw [e1]
    have e2 : ∑ r, xb r * (v r + KT K (s - t') r) ^ 2 =
        ∑ r, xb r * v r ^ 2 + 2 * ∑ r, xb r * v r * KT K (s - t') r +
          ∑ r, xb r * KT K (s - t') r ^ 2 := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun r _ => by ring)
    rw [← Finset.sum_div, ← Finset.sum_neg_distrib]
    have : ∑ r, (-((xb r * (v r + KT K (s - t') r) ^ 2 : ℝ) : ℂ)) =
        -((∑ r, xb r * (v r + KT K (s - t') r) ^ 2 : ℝ) : ℂ) := by
      push_cast; rw [Finset.sum_neg_distrib]
    rw [this, e2, hcross]
    push_cast
    rw [Finset.sum_neg_distrib]
    ring
  unfold gaussInt
  simp_rw [hpt]
  rw [integral_const_mul]
  congr 1
  exact integral_sub_right_eq_self (fun s => gaussF K xb 0 s) t'

end gauss

section ratio
variable {b R : ℕ}

/-- Relaxed ratio limit. -/
theorem relaxed_ratio (H : Fin b → Fin R → ℕ) (K : Fin b → Fin R → ℤ)
    (P : Matrix (Fin b) (Fin b) ℤ) (hHPK : ∀ j r, (H j r : ℤ) = ∑ i, P j i * K i r)
    (hK : ∀ θ : Fin b → ℝ, (∀ r, ∃ m : ℤ, KT K θ r = 2 * π * m) → ∀ i, ∃ m : ℤ, θ i = 2 * π * m)
    (hP : P.det ≠ 0)
    (x : ℕ → Fin R → ℝ) (xb : Fin R → ℝ) (hxb : ∀ r, 0 < xb r)
    (hx : ∀ r, Tendsto (fun N : ℕ => x N r / N) atTop (𝓝 (xb r)))
    (q : ℕ → Fin b → ℝ) (qb : Fin b → ℝ) (hqb0 : ∀ j, 0 < qb j) (hqb1 : ∀ j, qb j < 1)
    (hq : ∀ j, Tendsto (fun N => q N j) atTop (𝓝 (qb j)))
    (c : ℕ → Fin b → ℤ) (hc : ∀ᶠ N in atTop, ∀ j, (c N j : ℝ) = ∑ r, (H j r : ℝ) * x N r)
    (ζ : Fin R → ℂ) :
    Tendsto (fun N : ℕ =>
        (∫ n, (psiW P (q N) (c N) (Kn K n) : ℂ) *
          cexp (∑ r, ζ r * ((((n r : ℝ) - x N r) / Real.sqrt N : ℝ) : ℂ)) ∂(poisPi (x N))) /
        (∫ n, (psiW P (q N) (c N) (Kn K n) : ℂ) *
          cexp (∑ r, (0 : Fin R → ℂ) r * ((((n r : ℝ) - x N r) / Real.sqrt N : ℝ) : ℂ))
            ∂(poisPi (x N))))
      atTop (𝓝 (gaussInt K xb ζ / gaussInt K xb 0)) := by
  obtain ⟨ρ, hρ0, hρ1, hqbρ⟩ := exists_upper qb hqb1
  obtain ⟨g0, hg0, hG0⟩ := gaussInt_zero_re_pos K (inj_of_dual K hK) xb hxb
  have hGY : gaussInt K xb 0 ≠ 0 := by rw [hG0]; exact_mod_cast hg0.ne'
  set D := P.det.natAbs
  set δ0 := ∏ j, (qb j / 2) ^ D with hδ0
  have hδ0pos : 0 < δ0 := Finset.prod_pos (fun j _ => pow_pos (by linarith [hqb0 j]) _)
  have ha : ∀ᶠ N in atTop, δ0 ≤ ∑' k, psiW P (q N) (c N) k ∧
      ∑' k, psiW P (q N) (c N) k ≤ ∑' m, geomW (b := b) (fun _ => ρ) m := by
    have h1 : ∀ᶠ N in atTop, ∀ j, qb j / 2 ≤ q N j ∧ q N j ≤ ρ := by
      rw [eventually_all]; intro j
      filter_upwards [(hq j).eventually (lt_mem_nhds (by linarith [hqb0 j] : qb j / 2 < qb j)),
        (hq j).eventually (gt_mem_nhds (hqbρ j))] with N h1 h2
      exact ⟨h1.le, h2.le⟩
    filter_upwards [h1] with N hN
    have hq0 : ∀ j, 0 ≤ q N j := fun j => le_trans (by linarith [hqb0 j]) (hN j).1
    have hqρ : ∀ j, q N j ≤ ρ := fun j => (hN j).2
    refine ⟨le_trans ?_ (tsum_psiW_ge hP hq0 (fun j => le_trans (hqρ j) hρ1.le) hqρ hρ0.le hρ1 _),
      tsum_psiW_le hP hq0 hqρ hρ0.le hρ1 _⟩
    exact Finset.prod_le_prod (fun j _ => pow_nonneg (by linarith [hqb0 j]) _)
      (fun j _ => pow_le_pow_left₀ (by linarith [hqb0 j]) (hN j).1 _)
  have hX := relaxed_asymp H K P hHPK hK hP x xb hxb hx q qb hqb0 hqb1 hq c hc ζ
  have hY := relaxed_asymp H K P hHPK hK hP x xb hxb hx q qb hqb0 hqb1 hq c hc 0
  have hr := ratio_tendsto hδ0pos ha hGY hX hY
  refine hr.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with N hN
  have hs : ((Real.sqrt N ^ b : ℝ) : ℂ) * ((2 * π) ^ b : ℂ) ≠ 0 := by
    have h1 : (0:ℝ) < Real.sqrt N ^ b := pow_pos (Real.sqrt_pos.2 (by exact_mod_cast hN)) _
    have h2 : (2 * π : ℂ) ≠ 0 := by
      have := Real.pi_pos; exact_mod_cast (by positivity : (2 * π : ℝ) ≠ 0)
    exact mul_ne_zero (by exact_mod_cast h1.ne') (pow_ne_zero _ h2)
  rw [mul_div_mul_left _ _ hs]


end ratio

section final
variable {b R : ℕ}

lemma psiW_Kn (H : Fin b → Fin R → ℕ) (K : Fin b → Fin R → ℤ)
    (P : Matrix (Fin b) (Fin b) ℤ) (hHPK : ∀ j r, (H j r : ℤ) = ∑ i, P j i * K i r)
    (q : Fin b → ℝ) (c : Fin b → ℕ) (n : Fin R → ℕ) :
    psiW P q (fun j => (c j : ℤ)) (Kn K n) =
      if (∀ j, ∑ r, H j r * n r ≤ c j) then ∏ j, q j ^ (c j - ∑ r, H j r * n r) else 0 := by
  have hPK : ∀ j, (P *ᵥ Kn K n) j = ((∑ r, H j r * n r : ℕ) : ℤ) := by
    intro j
    simp only [Matrix.mulVec, dotProduct, Kn, Finset.mul_sum]
    rw [Finset.sum_comm]
    push_cast
    refine Finset.sum_congr rfl (fun r _ => ?_)
    rw [hHPK j r, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun i _ => by ring)
  unfold psiW geomW
  simp only [Pi.sub_apply, hPK]
  by_cases h : ∀ j, ∑ r, H j r * n r ≤ c j
  · rw [if_pos (fun j => by have := h j; omega), if_pos h]
    refine Finset.prod_congr rfl (fun j _ => ?_)
    rw [Int.toNat_sub]
  · rw [if_neg (fun h' => h (fun j => by have := h' j; omega)), if_neg h]

lemma psiW_le_one (P : Matrix (Fin b) (Fin b) ℤ) {q : Fin b → ℝ} (hq0 : ∀ j, 0 ≤ q j)
    (hq1 : ∀ j, q j ≤ 1) (c : Fin b → ℤ) (k : Fin b → ℤ) : psiW P q c k ≤ 1 := by
  unfold psiW geomW
  split_ifs
  · exact Finset.prod_le_one (fun j _ => pow_nonneg (hq0 j) _) (fun j _ => pow_le_one₀ (hq0 j) (hq1 j))
  · exact zero_le_one

lemma poisPi_zero_pos (x : Fin R → ℝ) : 0 < (poisPi x).real {0} := by
  have : ({0} : Set (Fin R → ℕ)) = Set.pi Set.univ (fun _ => {0}) := by
    ext n; simp [funext_iff]
  rw [measureReal_def, this, poisPi, Measure.pi_pi, ENNReal.toReal_prod]
  refine Finset.prod_pos (fun r _ => ?_)
  rw [← measureReal_def]
  rw [poissonMeasure_real_singleton]
  positivity

/-- the exact (truncated) weight of the core statement -/
noncomputable def coreW {κ : Type*} (H : Fin b → Fin R → ℕ) (G : κ → Fin R → ℕ)
    (q : ℕ → Fin b → ℝ) (c : ℕ → Fin b → ℕ) (cap : ℕ → κ → ℕ) (N : ℕ) (n : Fin R → ℕ) : ℝ := by
  classical
  exact if (∀ j, ∑ r, H j r * n r ≤ c N j) ∧ (∀ k, ∑ r, G k r * n r ≤ cap N k) then
    ∏ j, q N j ^ (c N j - ∑ r, H j r * n r) else 0

/-- the centred, scaled occupancy -/
noncomputable def uN (x : ℕ → Fin R → ℝ) (N : ℕ) (n : Fin R → ℕ) (r : Fin R) : ℝ :=
  ((n r : ℝ) - x N r) / Real.sqrt N

lemma integrable_of_le_one_mul_tilt {f : (Fin R → ℕ) → ℝ} (hf0 : ∀ n, 0 ≤ f n)
    (hf1 : ∀ n, f n ≤ 1) (x : Fin R → ℝ) (hx : ∀ r, 0 ≤ x r) (ζ : Fin R → ℂ) (N : ℕ) :
    Integrable (fun n => (f n : ℂ) * cexp (∑ r, ζ r * ((((n r : ℝ) - x r) / Real.sqrt N : ℝ) : ℂ)))
      (poisPi x) := by
  have hT := tilt_integrable x hx (fun r => ζ r / (Real.sqrt N : ℂ))
  have heq : (fun n : Fin R → ℕ => ∏ r, cexp (ζ r / (Real.sqrt N : ℂ) * ((n r : ℝ) - x r : ℝ))) =
      fun n => cexp (∑ r, ζ r * ((((n r : ℝ) - x r) / Real.sqrt N : ℝ) : ℂ)) := by
    funext n
    rw [← Complex.exp_sum]
    congr 1
    refine Finset.sum_congr rfl (fun r _ => ?_)
    push_cast; ring
  rw [heq] at hT
  refine Integrable.mono' hT.norm (measurable_of_countable _).aestronglyMeasurable
    (Eventually.of_forall fun n => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hf0 n)]
  exact mul_le_of_le_one_left (norm_nonneg _) (hf1 n)


/-- **Core local limit theorem** for the truncated, tilted multivariate Poisson law. -/
theorem core_final (H : Fin b → Fin R → ℕ)
    (hH : LinearIndependent ℝ (fun j : Fin b => fun r => (H j r : ℝ)))
    {κ : Type*} [Fintype κ] (G : κ → Fin R → ℕ)
    (x : ℕ → Fin R → ℝ) (xb : Fin R → ℝ) (hxb : ∀ r, 0 < xb r)
    (hx : ∀ r, Tendsto (fun N : ℕ => x N r / N) atTop (𝓝 (xb r)))
    (q : ℕ → Fin b → ℝ) (qb : Fin b → ℝ) (hqb0 : ∀ j, 0 < qb j) (hqb1 : ∀ j, qb j < 1)
    (hq : ∀ j, Tendsto (fun N => q N j) atTop (𝓝 (qb j)))
    (c : ℕ → Fin b → ℕ) (hc : ∀ᶠ N in atTop, ∀ j, (c N j : ℝ) = ∑ r, (H j r : ℝ) * x N r)
    (cap : ℕ → κ → ℕ) (ε : ℝ) (hε : 0 < ε)
    (hcap : ∀ᶠ N in atTop, ∀ k, ∑ r, (G k r : ℝ) * x N r + ε * N ≤ cap N k) :
    ∃ L : (Fin R → ℂ) → ℂ,
      (∀ ζ : Fin R → ℂ, Tendsto (fun N : ℕ =>
        (∫ n, (coreW H G q c cap N n : ℂ) * cexp (∑ r, ζ r * (uN x N n r : ℂ)) ∂(poisPi (x N))) /
        (∫ n, (coreW H G q c cap N n : ℂ) ∂(poisPi (x N)))) atTop (𝓝 (L ζ))) ∧
      (∀ ξ v : Fin R → ℝ, ∀ t : Fin b → ℝ, (∀ r, v r = ξ r + ∑ j, (H j r : ℝ) * t j) →
        (∀ j, ∑ r, (H j r : ℝ) * xb r * v r = 0) →
        L (fun r => I * ξ r) = cexp (-((∑ r, xb r * v r ^ 2 : ℝ) : ℂ) / 2)) := by
  classical
  obtain ⟨K, P, hHPK, hK, hP⟩ := lattice_basis H hH
  set cZ : ℕ → Fin b → ℤ := fun N j => (c N j : ℤ) with hcZ
  have hcZ' : ∀ᶠ N in atTop, ∀ j, (cZ N j : ℝ) = ∑ r, (H j r : ℝ) * x N r := by
    filter_upwards [hc] with N hN j
    simp only [hcZ, Int.cast_natCast]; exact hN j
  refine ⟨fun ζ => gaussInt K xb ζ / gaussInt K xb 0, ?_, ?_⟩
  swap
  · intro ξ v t hv1 hv2
    obtain ⟨g0, hg0, hG0⟩ := gaussInt_zero_re_pos K (inj_of_dual K hK) xb hxb
    have hGY : gaussInt K xb 0 ≠ 0 := by rw [hG0]; exact_mod_cast hg0.ne'
    simp only
    rw [gaussInt_I K H P hHPK hP xb ξ v t hv1 hv2, mul_div_assoc, div_self hGY, mul_one]
  intro ζ
  set ψ' : ℕ → (Fin R → ℕ) → ℝ := fun N n => psiW P (q N) (cZ N) (Kn K n) with hψ'
  set T : ℕ → (Fin R → ℂ) → (Fin R → ℕ) → ℂ := fun N ζ n =>
    cexp (∑ r, ζ r * ((((n r : ℝ) - x N r) / Real.sqrt N : ℝ) : ℂ)) with hT
  set Ii : ℕ → (Fin R → ℂ) → ℂ := fun N ζ => ∫ n, (ψ' N n : ℂ) * T N ζ n ∂(poisPi (x N))
    with hIi
  set Ji : ℕ → (Fin R → ℂ) → ℂ := fun N ζ =>
    ∫ n, (coreW H G q c cap N n : ℂ) * T N ζ n ∂(poisPi (x N)) with hJi
  have hrel : ∀ ζ, Tendsto (fun N => Ii N ζ / Ii N 0) atTop
      (𝓝 (gaussInt K xb ζ / gaussInt K xb 0)) := fun ζ =>
    relaxed_ratio H K P hHPK hK hP x xb hxb hx q qb hqb0 hqb1 hq cZ hcZ' ζ
  -- good indices
  set good : ℕ → Prop := fun N => 0 < N ∧ (∀ j, 0 < q N j ∧ q N j ≤ 1) ∧ (∀ r, 0 ≤ x N r) ∧
    (∀ k, ∑ r, (G k r : ℝ) * x N r + ε * N ≤ cap N k) with hgood
  have hgoodev : ∀ᶠ N in atTop, good N := by
    have h1 : ∀ᶠ N in atTop, ∀ j, 0 < q N j ∧ q N j ≤ 1 := by
      rw [eventually_all]; intro j
      filter_upwards [(hq j).eventually (lt_mem_nhds (hqb0 j)),
        (hq j).eventually (gt_mem_nhds (hqb1 j))] with N h1 h2
      exact ⟨h1, h2.le⟩
    have h2 : ∀ᶠ N : ℕ in atTop, ∀ r, 0 ≤ x N r := by
      rw [eventually_all]; intro r
      filter_upwards [(hx r).eventually (lt_mem_nhds (hxb r)), eventually_gt_atTop 0]
        with N h hN
      have hNp : (0:ℝ) < N := by exact_mod_cast hN
      exact (div_pos_iff_of_pos_right hNp).1 h |>.le
    filter_upwards [eventually_gt_atTop 0, h1, h2, hcap] with N a0 a1 a2 a3
    exact ⟨a0, a1, a2, a3⟩
  -- the decomposition of the exact weight
  have hW : ∀ N n, coreW H G q c cap N n =
      ψ' N n * (if ∀ k, ∑ r, G k r * n r ≤ cap N k then 1 else 0) := by
    intro N n
    simp only [hψ', hcZ]
    rw [psiW_Kn H K P hHPK (q N) (c N) n]
    unfold coreW
    by_cases h1 : ∀ j, ∑ r, H j r * n r ≤ c N j <;>
      by_cases h2 : ∀ k, ∑ r, G k r * n r ≤ cap N k <;> simp [h1, h2]
  have hψ'01 : ∀ N, good N → ∀ n, 0 ≤ ψ' N n ∧ ψ' N n ≤ 1 := by
    intro N hN n
    exact ⟨psiW_nonneg P (fun j => (hN.2.1 j).1.le) _ _,
      psiW_le_one P (fun j => (hN.2.1 j).1.le) (fun j => (hN.2.1 j).2) _ _⟩
  have hW01 : ∀ N, good N → ∀ n, 0 ≤ coreW H G q c cap N n ∧ coreW H G q c cap N n ≤ 1 := by
    intro N hN n
    rw [hW]
    have := hψ'01 N hN n
    split_ifs
    · simpa using this
    · simp
  have hIint : ∀ N, good N → ∀ ζ, Integrable (fun n => (ψ' N n : ℂ) * T N ζ n) (poisPi (x N)) :=
    fun N hN ζ => integrable_of_le_one_mul_tilt (fun n => (hψ'01 N hN n).1)
      (fun n => (hψ'01 N hN n).2) (x N) hN.2.2.1 ζ N
  have hJint : ∀ N, good N → ∀ ζ, Integrable (fun n => (coreW H G q c cap N n : ℂ) * T N ζ n)
      (poisPi (x N)) :=
    fun N hN ζ => integrable_of_le_one_mul_tilt (fun n => (hW01 N hN n).1)
      (fun n => (hW01 N hN n).2) (x N) hN.2.2.1 ζ N
  -- real tilts
  set ηk : (Fin R → ℂ) → κ → Fin R → ℂ := fun ζ' k r => (((ζ' r).re + G k r : ℝ) : ℂ) with hηk
  have hIreal : ∀ N, good N → ∀ η : Fin R → ℝ, Ii N (fun r => (η r : ℂ)) =
      ((∫ n, ψ' N n * Real.exp (∑ r, η r * uN x N n r) ∂(poisPi (x N)) : ℝ) : ℂ) := by
    intro N hN η
    simp only [hIi, hT]
    refine (integral_congr_ae (Eventually.of_forall fun n => ?_)).trans integral_ofReal
    simp only [uN]
    push_cast
    change _ = (ψ' N n : ℂ) * Complex.ofReal (Real.exp _)
    rw [Complex.ofReal_exp]
    push_cast
    rfl
  -- error term
  have hE : ∀ N, good N → ∀ ζ : Fin R → ℂ, ‖Ii N ζ - Ji N ζ‖ ≤
      Real.exp (-(ε * Real.sqrt N)) * ∑ k, ‖Ii N (ηk ζ k)‖ := by
    intro N hN ζ
    have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 (by exact_mod_cast hN.1)
    rw [← integral_sub (hIint N hN ζ) (hJint N hN ζ)]
    refine le_trans (norm_integral_le_integral_norm _) ?_
    have hpt : ∀ n, ‖(ψ' N n : ℂ) * T N ζ n - (coreW H G q c cap N n : ℂ) * T N ζ n‖ ≤
        ∑ k, Real.exp (-(ε * Real.sqrt N)) * ‖(ψ' N n : ℂ) * T N (ηk ζ k) n‖ := by
      intro n
      rw [hW N n]
      have hψn := hψ'01 N hN n
      split_ifs with hgoodn
      · simp only [mul_one, sub_self, norm_zero]
        exact Finset.sum_nonneg (fun k _ => by positivity)
      · push_neg at hgoodn
        obtain ⟨k0, hk0⟩ := hgoodn
        simp only [mul_zero, Complex.ofReal_zero, zero_mul, sub_zero]
        have hTn : ∀ ζ', ‖T N ζ' n‖ = Real.exp (∑ r, (ζ' r).re * uN x N n r) := by
          intro ζ'
          simp only [hT, uN]
          rw [Complex.norm_exp, Complex.re_sum]
          congr 1
          refine Finset.sum_congr rfl (fun r _ => ?_)
          simp [Complex.mul_re]
        have hk0' : ε * Real.sqrt N ≤ ∑ r, (G k0 r : ℝ) * uN x N n r := by
          have h1 : (cap N k0 : ℝ) < ∑ r, (G k0 r : ℝ) * (n r : ℝ) := by exact_mod_cast hk0
          have h2 := hN.2.2.2 k0
          have h3 : ∑ r, (G k0 r : ℝ) * uN x N n r =
              (∑ r, (G k0 r : ℝ) * (n r : ℝ) - ∑ r, (G k0 r : ℝ) * x N r) / Real.sqrt N := by
            simp only [uN, ← Finset.sum_sub_distrib, Finset.sum_div]
            refine Finset.sum_congr rfl (fun r _ => by ring)
          rw [h3, le_div_iff₀ hsN]
          have : ε * Real.sqrt N * Real.sqrt N = ε * N := by
            rw [mul_assoc, Real.mul_self_sqrt (Nat.cast_nonneg _)]
          linarith
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hψn.1]
        refine le_trans ?_ (Finset.single_le_sum (f := fun k => Real.exp (-(ε * Real.sqrt N)) *
          ‖(ψ' N n : ℂ) * T N (ηk ζ k) n‖) (fun k _ => by positivity) (Finset.mem_univ k0))
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hψn.1, hTn, hTn]
        have e1 : ∑ r, (ηk ζ k0 r).re * uN x N n r =
            ∑ r, (ζ r).re * uN x N n r + ∑ r, (G k0 r : ℝ) * uN x N n r := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl (fun r _ => ?_)
          simp only [hηk, Complex.ofReal_re]; ring
        rw [e1, Real.exp_add]
        have : Real.exp (-(ε * Real.sqrt N)) * Real.exp (∑ r, (G k0 r : ℝ) * uN x N n r) ≥ 1 := by
          rw [← Real.exp_add]; exact Real.one_le_exp (by linarith)
        have hE0 : 0 ≤ ψ' N n * Real.exp (∑ r, (ζ r).re * uN x N n r) :=
          mul_nonneg hψn.1 (Real.exp_pos _).le
        have := mul_le_mul_of_nonneg_left this hE0
        linear_combination this
    refine le_trans (integral_mono_of_nonneg (Eventually.of_forall fun n => norm_nonneg _) ?_
      (Eventually.of_forall hpt)) (le_of_eq ?_)
    · exact integrable_finsetSum _ (fun k _ => ((hIint N hN (ηk ζ k)).norm.const_mul _))
    · rw [integral_finsetSum _ (fun k _ => ((hIint N hN (ηk ζ k)).norm.const_mul _)),
        Finset.mul_sum]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [integral_const_mul]
      congr 1
      -- the integrand is a nonnegative real
      have hk : ηk ζ k = fun r => (((ζ r).re + G k r : ℝ) : ℂ) := rfl
      rw [hk, hIreal N hN, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (integral_nonneg
        (fun n => mul_nonneg (hψ'01 N hN n).1 (Real.exp_pos _).le))]
      refine integral_congr_ae (Eventually.of_forall fun n => ?_)
      simp only [hT, uN]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hψ'01 N hN n).1,
        Complex.norm_exp, Complex.re_sum]
      congr 2
      refine Finset.sum_congr rfl (fun r _ => ?_)
      simp [Complex.mul_re]
  -- nonvanishing of the relaxed normaliser
  have hI0 : ∀ N, good N → Ii N 0 ≠ 0 := by
    intro N hN
    have h0 : (0 : Fin R → ℂ) = fun r => ((0 : ℝ) : ℂ) := by funext r; simp
    rw [h0, hIreal N hN]
    simp only [zero_mul, Finset.sum_const_zero, Real.exp_zero, mul_one]
    have hψ0 : 0 < ψ' N 0 := by
      simp only [hψ', hcZ]
      rw [psiW_Kn H K P hHPK (q N) (c N) 0]
      rw [if_pos (fun j => by simp)]
      exact Finset.prod_pos (fun j _ => pow_pos (hN.2.1 j).1 _)
    have hint : Integrable (ψ' N) (poisPi (x N)) :=
      Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable 1
        (Eventually.of_forall fun n => by
          rw [Real.norm_eq_abs, abs_of_nonneg (hψ'01 N hN n).1]; exact (hψ'01 N hN n).2)
    have hpos : 0 < ∫ n, ψ' N n ∂(poisPi (x N)) := by
      refine lt_of_lt_of_le ?_ (setIntegral_le_integral (s := {0}) hint
        (Eventually.of_forall fun n => (hψ'01 N hN n).1))
      rw [integral_singleton, smul_eq_mul]
      exact mul_pos (poisPi_zero_pos (x N)) hψ0
    exact_mod_cast hpos.ne'
  -- error ratios vanish
  have hdec : Tendsto (fun N : ℕ => Real.exp (-(ε * Real.sqrt N))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp
      ((Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop hε)
  have hEr : ∀ ζ' : Fin R → ℂ, Tendsto (fun N => (Ii N ζ' - Ji N ζ') / Ii N 0) atTop (𝓝 0) := by
    intro ζ'
    have hsum : Tendsto (fun N => ∑ k, ‖Ii N (ηk ζ' k) / Ii N 0‖) atTop
        (𝓝 (∑ k, ‖gaussInt K xb (ηk ζ' k) / gaussInt K xb 0‖)) :=
      tendsto_finsetSum _ (fun k _ => (hrel (ηk ζ' k)).norm)
    have hb := hdec.mul hsum
    rw [zero_mul] at hb
    refine squeeze_zero_norm' ?_ hb
    filter_upwards [hgoodev] with N hN
    rw [norm_div]
    have h1 := hE N hN ζ'
    have hI0n : 0 < ‖Ii N 0‖ := norm_pos_iff.2 (hI0 N hN)
    rw [div_le_iff₀ hI0n]
    refine le_trans h1 (le_of_eq ?_)
    rw [mul_assoc, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [norm_div, div_mul_cancel₀ _ hI0n.ne']
  -- conclusion
  have hlim := ((hrel ζ).sub (hEr ζ)).div ((tendsto_const_nhds (x := (1 : ℂ))).sub (hEr 0))
    (by simp)
  rw [sub_zero, sub_zero, div_one] at hlim
  refine hlim.congr' ?_
  filter_upwards [hgoodev] with N hN
  have hJ0 : (∫ n, (coreW H G q c cap N n : ℂ) ∂(poisPi (x N))) = Ji N 0 := by
    simp only [hJi, hT]
    refine integral_congr_ae (Eventually.of_forall fun n => ?_)
    simp
  have hJζ : (∫ n, (coreW H G q c cap N n : ℂ) * cexp (∑ r, ζ r * (uN x N n r : ℂ))
      ∂(poisPi (x N))) = Ji N ζ := rfl
  rw [hJ0, hJζ]
  have hI0' := hI0 N hN
  simp only [Pi.div_apply, Pi.sub_apply]
  have e1 : Ii N ζ / Ii N 0 - (Ii N ζ - Ji N ζ) / Ii N 0 = Ji N ζ / Ii N 0 := by
    rw [← sub_div]; ring_nf
  have e2 : (1 : ℂ) - (Ii N 0 - Ji N 0) / Ii N 0 = Ji N 0 / Ii N 0 := by
    field_simp; ring
  rw [e1, e2, div_div_div_cancel_right₀ hI0']

end final

end GLL


namespace X5LL
open KellyLossNetworks.Primal KellyStochasticNetworks KellyStochasticNetworks.LossLimits

variable {J R : ℕ} (A : Fin J → Fin R → ℕ) (ν : Fin R → ℝ) (C : Fin J → ℝ)

/-- Route "price" `(Aᵀ y)_r`. -/
noncomputable def ar (y : Fin J → ℝ) (r : Fin R) : ℝ := ∑ j, y j * (A j r : ℝ)

/-- Karush–Kuhn–Tucker conditions for the dual variable `y`. -/
def KKT (y : Fin J → ℝ) : Prop :=
  (∀ j, 0 ≤ y j) ∧ (∀ j, (∑ r, (A j r : ℝ) * primalPoint A ν y r) ≤ C j) ∧
    (∀ j, 0 < y j → (∑ r, (A j r : ℝ) * primalPoint A ν y r) = C j)

lemma pp_eq (y : Fin J → ℝ) (r : Fin R) : primalPoint A ν y r = ν r * Real.exp (-ar A y r) := rfl

lemma pp_pos (hν : ∀ r, 0 < ν r) (y : Fin J → ℝ) (r : Fin R) : 0 < primalPoint A ν y r :=
  mul_pos (hν r) (Real.exp_pos _)

/-- Per-route bound: `u (log ν - a) - u log u + u ≤ ν e^{-a}` with equality iff `u = ν e^{-a}`. -/
lemma psi_le {v a u : ℝ} (hv : 0 < v) (hu : 0 ≤ u) :
    u * Real.log v - u * Real.log u + u - u * a ≤ v * Real.exp (-a) := by
  rcases hu.lt_or_eq with hu | hu
  · set m := v * Real.exp (-a)
    have hm : 0 < m := mul_pos hv (Real.exp_pos _)
    have hlog : Real.log m = Real.log v - a := by
      simp only [m]; rw [Real.log_mul hv.ne' (Real.exp_pos _).ne', Real.log_exp]; ring
    have h := Real.log_le_sub_one_of_pos (div_pos hm hu)
    rw [Real.log_div hm.ne' hu.ne', hlog] at h
    have : u * (Real.log v - a - Real.log u) ≤ u * (m / u - 1) := mul_le_mul_of_nonneg_left h hu.le
    have e : u * (m / u - 1) = m - u := by field_simp
    linarith
  · subst hu; simp; exact (mul_pos hv (Real.exp_pos _)).le

lemma psi_eq {v a u : ℝ} (hv : 0 < v) (hu : 0 ≤ u)
    (h : v * Real.exp (-a) ≤ u * Real.log v - u * Real.log u + u - u * a) :
    u = v * Real.exp (-a) := by
  set m := v * Real.exp (-a)
  have hm : 0 < m := mul_pos hv (Real.exp_pos _)
  rcases hu.lt_or_eq with hu | hu
  · by_contra hne
    have hlog : Real.log m = Real.log v - a := by
      simp only [m]; rw [Real.log_mul hv.ne' (Real.exp_pos _).ne', Real.log_exp]; ring
    have h1 : m / u ≠ 1 := by
      intro h1; apply hne; field_simp at h1; linarith
    have h2 := Real.log_lt_sub_one_of_pos (div_pos hm hu) h1
    rw [Real.log_div hm.ne' hu.ne', hlog] at h2
    have : u * (Real.log v - a - Real.log u) < u * (m / u - 1) := mul_lt_mul_of_pos_left h2 hu
    have e : u * (m / u - 1) = m - u := by field_simp
    linarith
  · subst hu; simp at h; linarith

lemma primal_le_dual (hν : ∀ r, 0 < ν r) {y : Fin J → ℝ} (hy : ∀ j, 0 ≤ y j)
    {x : Fin R → ℝ} (hx : x ∈ feasibleReal A C) :
    primalObjective ν x ≤ dualReal A ν C y := by
  obtain ⟨hx0, hxC⟩ := hx
  have h1 : 0 ≤ ∑ j, y j * (C j - ∑ r, (A j r : ℝ) * x r) :=
    Finset.sum_nonneg (fun j _ => mul_nonneg (hy j) (by linarith [hxC j]))
  have h2 : primalObjective ν x + ∑ j, y j * (C j - ∑ r, (A j r : ℝ) * x r) =
      ∑ r, (x r * Real.log (ν r) - x r * Real.log (x r) + x r - x r * ar A y r) +
        ∑ j, y j * C j := by
    unfold primalObjective ar
    simp only [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_add_distrib]
    rw [Finset.sum_comm (f := fun j r => y j * ((A j r : ℝ) * x r))]
    have : ∀ r, ∑ j, x r * (y j * (A j r : ℝ)) = ∑ j, y j * ((A j r : ℝ) * x r) :=
      fun r => Finset.sum_congr rfl (fun j _ => by ring)
    simp only [this]; ring
  have h3 : ∑ r, (x r * Real.log (ν r) - x r * Real.log (x r) + x r - x r * ar A y r) ≤
      ∑ r, ν r * Real.exp (-ar A y r) :=
    Finset.sum_le_sum (fun r _ => psi_le (hν r) (hx0 r))
  unfold dualReal
  have : ∑ r, ν r * Real.exp (-∑ j, y j * (A j r : ℝ)) = ∑ r, ν r * Real.exp (-ar A y r) := rfl
  linarith

lemma kkt_feasible {y : Fin J → ℝ} (hν : ∀ r, 0 < ν r) (hy : KKT A ν C y) :
    primalPoint A ν y ∈ feasibleReal A C :=
  ⟨fun r => (pp_pos A ν hν y r).le, hy.2.1⟩

lemma kkt_value {y : Fin J → ℝ} (hν : ∀ r, 0 < ν r) (hy : KKT A ν C y) :
    primalObjective ν (primalPoint A ν y) = dualReal A ν C y := by
  have hcs : ∀ j, y j * (C j - ∑ r, (A j r : ℝ) * primalPoint A ν y r) = 0 := by
    intro j
    rcases (hy.1 j).lt_or_eq with h | h
    · rw [hy.2.2 j h]; ring
    · rw [← h]; ring
  have hlog : ∀ r, Real.log (primalPoint A ν y r) = Real.log (ν r) - ar A y r := by
    intro r; rw [pp_eq, Real.log_mul (hν r).ne' (Real.exp_pos _).ne', Real.log_exp]; ring
  have h2 : ∑ j, y j * C j = ∑ r, primalPoint A ν y r * ar A y r := by
    have : ∑ j, y j * C j = ∑ j, y j * ∑ r, (A j r : ℝ) * primalPoint A ν y r :=
      Finset.sum_congr rfl (fun j _ => by linarith [hcs j])
    rw [this]; unfold ar
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun r _ => Finset.sum_congr rfl (fun j _ => by ring))
  unfold primalObjective dualReal
  simp only [hlog]
  rw [h2, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  rw [pp_eq]; unfold ar; ring

lemma kkt_isMax {y : Fin J → ℝ} (hν : ∀ r, 0 < ν r) (hy : KKT A ν C y) :
    IsMaxOn (primalObjective ν) (feasibleReal A C) (primalPoint A ν y) := by
  intro x hx
  rw [Set.mem_setOf_eq, kkt_value A ν C hν hy]
  exact primal_le_dual A ν C hν hy.1 hx

lemma kkt_unique {y : Fin J → ℝ} (hν : ∀ r, 0 < ν r) (hy : KKT A ν C y)
    {x : Fin R → ℝ} (hx : x ∈ feasibleReal A C)
    (hge : dualReal A ν C y ≤ primalObjective ν x) : x = primalPoint A ν y := by
  obtain ⟨hx0, hxC⟩ := hx
  have h1 : 0 ≤ ∑ j, y j * (C j - ∑ r, (A j r : ℝ) * x r) :=
    Finset.sum_nonneg (fun j _ => mul_nonneg (hy.1 j) (by linarith [hxC j]))
  have h2 : primalObjective ν x + ∑ j, y j * (C j - ∑ r, (A j r : ℝ) * x r) =
      ∑ r, (x r * Real.log (ν r) - x r * Real.log (x r) + x r - x r * ar A y r) +
        ∑ j, y j * C j := by
    unfold primalObjective ar
    simp only [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_add_distrib]
    rw [Finset.sum_comm (f := fun j r => y j * ((A j r : ℝ) * x r))]
    have : ∀ r, ∑ j, x r * (y j * (A j r : ℝ)) = ∑ j, y j * ((A j r : ℝ) * x r) :=
      fun r => Finset.sum_congr rfl (fun j _ => by ring)
    simp only [this]; ring
  have hD : dualReal A ν C y = ∑ r, ν r * Real.exp (-ar A y r) + ∑ j, y j * C j := rfl
  set f := fun r => x r * Real.log (ν r) - x r * Real.log (x r) + x r - x r * ar A y r
  set g := fun r => ν r * Real.exp (-ar A y r)
  have hfg : ∀ r ∈ Finset.univ, f r ≤ g r := fun r _ => psi_le (hν r) (hx0 r)
  have hsum : ∑ r, g r ≤ ∑ r, f r := by linarith
  have heq : ∀ r ∈ Finset.univ, f r = g r := by
    by_contra hne
    push_neg at hne
    obtain ⟨r, hr, hne⟩ := hne
    have hlt : ∑ r, f r < ∑ r, g r :=
      Finset.sum_lt_sum hfg ⟨r, hr, lt_of_le_of_ne (hfg r hr) hne⟩
    linarith
  funext r
  exact psi_eq (hν r) (hx0 r) (le_of_eq (heq r (Finset.mem_univ r)).symm)

end X5LL


namespace X5LL
open KellyLossNetworks.Primal KellyStochasticNetworks KellyStochasticNetworks.LossLimits Filter Topology

variable {J R : ℕ} (A : Fin J → Fin R → ℕ) (ν : Fin R → ℝ) (C : Fin J → ℝ)

lemma dual_eq (y : Fin J → ℝ) :
    dualReal A ν C y = ∑ r, ν r * Real.exp (-ar A y r) + ∑ j, y j * C j := rfl

/-- KKT points minimize the dual over the nonnegative orthant. -/
lemma kkt_dualOpt {y : Fin J → ℝ} (hν : ∀ r, 0 < ν r) (hy : KKT A ν C y) :
    dualOptReal A ν C y := by
  refine ⟨hy.1, fun z hz => ?_⟩
  set x := primalPoint A ν y
  have hexp : ∀ r, ν r * Real.exp (-ar A y r) * (ar A y r - ar A z r + 1) ≤
      ν r * Real.exp (-ar A z r) := by
    intro r
    have h := Real.add_one_le_exp (ar A y r - ar A z r)
    have : Real.exp (-ar A z r) = Real.exp (-ar A y r) * Real.exp (ar A y r - ar A z r) := by
      rw [← Real.exp_add]; ring_nf
    rw [this, ← mul_assoc]
    exact mul_le_mul_of_nonneg_left h (mul_pos (hν r) (Real.exp_pos _)).le
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun r _ => hexp r)
  have hlin : ∑ r, ν r * Real.exp (-ar A y r) * (ar A y r - ar A z r + 1) =
      ∑ r, ν r * Real.exp (-ar A y r) +
        ∑ j, (y j - z j) * ∑ r, (A j r : ℝ) * x r := by
    simp only [x, pp_eq, mul_add, mul_one, Finset.sum_add_distrib, ar, mul_sub,
      Finset.sum_sub_distrib, Finset.mul_sum, sub_mul, Finset.sum_mul]
    rw [Finset.sum_comm (f := fun j r => y j * ((A j r : ℝ) * (ν r * Real.exp (-∑ j, y j * (A j r : ℝ)))))]
    rw [Finset.sum_comm (f := fun j r => z j * ((A j r : ℝ) * (ν r * Real.exp (-∑ j, y j * (A j r : ℝ)))))]
    have e1 : ∀ r j, ν r * Real.exp (-∑ j, y j * (A j r : ℝ)) * (y j * (A j r : ℝ)) =
        y j * ((A j r : ℝ) * (ν r * Real.exp (-∑ j, y j * (A j r : ℝ)))) := fun r j => by ring
    have e2 : ∀ r j, ν r * Real.exp (-∑ j, y j * (A j r : ℝ)) * (z j * (A j r : ℝ)) =
        z j * ((A j r : ℝ) * (ν r * Real.exp (-∑ j, y j * (A j r : ℝ)))) := fun r j => by ring
    simp only [e1, e2]; ring
  have hcs : ∀ j, 0 ≤ (z j - y j) * (C j - ∑ r, (A j r : ℝ) * x r) := by
    intro j
    rcases (hy.1 j).lt_or_eq with h | h
    · rw [hy.2.2 j h]; simp
    · rw [← h, sub_zero]; exact mul_nonneg (hz j) (by linarith [hy.2.1 j])
  have hcs' := Finset.sum_nonneg (s := Finset.univ) (fun j _ => hcs j)
  rw [dual_eq, dual_eq]
  have : ∑ j, (z j - y j) * (C j - ∑ r, (A j r : ℝ) * x r) =
      ∑ j, z j * C j - ∑ j, y j * C j + ∑ j, (y j - z j) * ∑ r, (A j r : ℝ) * x r := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  linarith

/-- The one-dimensional dual section in direction `e_j`. -/
lemma dual_dir (y : Fin J → ℝ) (j : Fin J) (t : ℝ) :
    dualReal A ν C (y + t • Pi.single j 1) =
      (∑ r, ν r * Real.exp (-ar A y r) * Real.exp (-(t * (A j r : ℝ))) + t * C j) +
        ∑ i, y i * C i := by
  have har : ∀ r, ar A (y + t • Pi.single j 1) r = ar A y r + t * (A j r : ℝ) := by
    intro r; unfold ar
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb; simp [Pi.single_apply, hb]
    · simp
  rw [dual_eq]
  simp only [har, neg_add, Real.exp_add, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul,
    Finset.sum_add_distrib, mul_assoc]
  have hs : ∑ x, t * ((Pi.single j (1:ℝ) : Fin J → ℝ) x * C x) = t * C j := by
    rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb; simp [Pi.single_apply, hb]
    · simp
  rw [hs]; ring

lemma dual_dir_deriv (y : Fin J → ℝ) (j : Fin J) :
    HasDerivAt (fun t => ∑ r, ν r * Real.exp (-ar A y r) * Real.exp (-(t * (A j r : ℝ))) +
      t * C j) (C j - ∑ r, (A j r : ℝ) * primalPoint A ν y r) 0 := by
  have h : ∀ r, HasDerivAt (fun t => ν r * Real.exp (-ar A y r) * Real.exp (-(t * (A j r : ℝ))))
      (ν r * Real.exp (-ar A y r) * (Real.exp (-((0:ℝ) * (A j r : ℝ))) * (-(A j r : ℝ)))) 0 := by
    intro r
    apply HasDerivAt.const_mul
    have := ((hasDerivAt_id (0:ℝ)).mul_const (A j r : ℝ)).neg.exp
    simpa using this
  have hs := HasDerivAt.fun_sum (u := Finset.univ) (fun r _ => h r)
  have hc := hasDerivAt_mul_const (x := (0:ℝ)) (C j)
  refine (hs.add hc).congr_deriv ?_
  rw [sub_eq_add_neg, add_comm (C j), ← Finset.sum_neg_distrib]
  congr 1
  exact Finset.sum_congr rfl (fun r _ => by simp only [pp_eq, ar, zero_mul, neg_zero, Real.exp_zero]; ring)

/-- Dual optimality implies the KKT conditions. -/
lemma dualOpt_kkt {y : Fin J → ℝ} (hy : dualOptReal A ν C y) : KKT A ν C y := by
  obtain ⟨hy0, hmin⟩ := hy
  have key : ∀ j, ∀ t, 0 ≤ y j + t →
      (∑ r, ν r * Real.exp (-ar A y r) * Real.exp (-((0:ℝ) * (A j r : ℝ))) + 0 * C j) ≤
      ∑ r, ν r * Real.exp (-ar A y r) * Real.exp (-(t * (A j r : ℝ))) + t * C j := by
    intro j t ht
    have hz : ∀ i, 0 ≤ ((y + t • Pi.single j (1:ℝ)) : Fin J → ℝ) i := by
      intro i
      by_cases hi : i = j
      · subst hi; simp; linarith
      · simp [Pi.single_apply, hi, hy0 i]
    have h1 := hmin _ hz
    have h0 := dual_dir A ν C y j 0
    simp only [zero_smul, add_zero] at h0
    rw [dual_dir, h0] at h1
    linarith
  have hge : ∀ j, 0 ≤ C j - ∑ r, (A j r : ℝ) * primalPoint A ν y r := by
    intro j
    have hd := (dual_dir_deriv A ν C y j).tendsto_slope_zero_right
    apply ge_of_tendsto hd
    filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    have := key j t (by linarith [hy0 j])
    simp only [zero_add, smul_eq_mul]
    exact mul_nonneg (inv_nonneg.2 ht.le) (by linarith)
  refine ⟨hy0, fun j => by linarith [hge j], fun j hj => ?_⟩
  have hd := (dual_dir_deriv A ν C y j).tendsto_slope_zero_left
  have hle : C j - ∑ r, (A j r : ℝ) * primalPoint A ν y r ≤ 0 := by
    apply le_of_tendsto hd
    have : Set.Ioo (-y j) 0 ∈ 𝓝[<] (0:ℝ) := Ioo_mem_nhdsLT (by linarith)
    filter_upwards [this] with t ht
    have := key j t (by linarith [ht.1])
    simp only [zero_add, smul_eq_mul]
    exact mul_nonpos_of_nonpos_of_nonneg (inv_nonpos.2 ht.2.le) (by linarith)
  linarith [hge j]

/-- Existence of a dual optimum (coercivity on the orthant). -/
lemma exists_dualOpt (hν : ∀ r, 0 < ν r) (hC : ∀ j, 0 < C j) : ∃ y, dualOptReal A ν C y := by
  set M := dualReal A ν C 0
  set K : Set (Fin J → ℝ) := Set.pi Set.univ (fun j => Set.Icc 0 (max M 0 / C j))
  have hK : IsCompact K := isCompact_univ_pi (fun _ => isCompact_Icc)
  have h0K : (0 : Fin J → ℝ) ∈ K := fun j _ => ⟨le_rfl, div_nonneg (le_max_right _ _) (hC j).le⟩
  have hcont : Continuous (dualReal A ν C) := by
    unfold dualReal; fun_prop
  obtain ⟨y, hyK, hymin⟩ := hK.exists_isMinOn ⟨0, h0K⟩ hcont.continuousOn
  have hy0 : ∀ j, 0 ≤ y j := fun j => (hyK j (Set.mem_univ j)).1
  refine ⟨y, hy0, fun z hz => ?_⟩
  by_cases hzK : z ∈ K
  · exact hymin hzK
  · have hyM : dualReal A ν C y ≤ M := hymin h0K
    simp only [K, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc, not_forall] at hzK
    obtain ⟨j, hj⟩ := hzK
    have hzj : max M 0 / C j < z j := by
      by_contra h; push_neg at h; exact hj ⟨hz j, h⟩
    have h1 : z j * C j ≤ ∑ i, z i * C i :=
      Finset.single_le_sum (f := fun i => z i * C i)
        (fun i _ => mul_nonneg (hz i) (hC i).le) (Finset.mem_univ j)
    have h2 : max M 0 < z j * C j := by rwa [div_lt_iff₀ (hC j)] at hzj
    have h3 : 0 ≤ ∑ r, ν r * Real.exp (-ar A z r) :=
      Finset.sum_nonneg (fun r _ => (mul_pos (hν r) (Real.exp_pos _)).le)
    have := le_max_left M 0
    have := dual_eq A ν C z
    linarith

end X5LL


namespace X5LL
open KellyLossNetworks.Primal KellyStochasticNetworks KellyStochasticNetworks.LossLimits
open Filter Topology

variable {J R : ℕ} (A : Fin J → Fin R → ℕ)

lemma prod_eq (y : Fin J → ℝ) (r : Fin R) :
    ∏ i, (1 - blockingFromDual y i) ^ (A i r) = Real.exp (-ar A y r) := by
  unfold blockingFromDual ar
  simp only [sub_sub_cancel, ← Real.exp_nat_mul, ← Real.exp_sum]
  congr 1
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl (fun i _ => by ring)

lemma carried_eq (ν : Fin R → ℝ) (y : Fin J → ℝ) :
    carried A ν (blockingFromDual y) = primalPoint A ν y := by
  funext r; unfold carried; rw [prod_eq, pp_eq]

lemma bfd_inv {B : Fin J → ℝ} (hB : ∀ j, B j < 1) :
    blockingFromDual (dualFromBlocking B) = B := by
  funext j
  have h1 : 0 < 1 - B j := by linarith [hB j]
  unfold blockingFromDual dualFromBlocking
  rw [neg_neg, Real.exp_log h1]; ring

lemma kkt_bc (ν : Fin R → ℝ) (C : Fin J → ℝ) {y : Fin J → ℝ} (hy : KKT A ν C y) :
    blockingConditions A ν C (blockingFromDual y) := by
  rw [blockingConditions, carried_eq]
  refine ⟨fun j => ⟨?_, ?_⟩, hy.2.1, fun j hB => hy.2.2 j ?_⟩
  · unfold blockingFromDual
    have : Real.exp (-y j) ≤ 1 := Real.exp_le_one_iff.2 (by linarith [hy.1 j])
    linarith
  · unfold blockingFromDual; linarith [Real.exp_pos (-y j)]
  · rcases (hy.1 j).lt_or_eq with h | h
    · exact h
    · exfalso; unfold blockingFromDual at hB; rw [← h] at hB; simp at hB

lemma bc_kkt (ν : Fin R → ℝ) (C : Fin J → ℝ) {B : Fin J → ℝ} (hB : blockingConditions A ν C B) :
    KKT A ν C (dualFromBlocking B) := by
  have hinv := bfd_inv (fun j => (hB.1 j).2)
  have hc : carried A ν B = primalPoint A ν (dualFromBlocking B) := by
    rw [← carried_eq, hinv]
  refine ⟨fun j => ?_, fun j => ?_, fun j hj => ?_⟩
  · unfold dualFromBlocking
    have h1 : 0 < 1 - B j := by linarith [(hB.1 j).2]
    have h2 : 1 - B j ≤ 1 := by linarith [(hB.1 j).1]
    linarith [Real.log_nonpos h1.le h2]
  · rw [← hc]; exact hB.2.1 j
  · rw [← hc]
    apply hB.2.2 j
    rcases (hB.1 j).1.lt_or_eq with h | h
    · exact h
    · exfalso; unfold dualFromBlocking at hj; rw [← h] at hj; simp at hj

lemma bc_exists {ν : Fin R → ℝ} {C : Fin J → ℝ} (hν : ∀ r, 0 < ν r) (hC : ∀ j, 0 < C j) :
    ∃ B, blockingConditions A ν C B := by
  obtain ⟨y, hy⟩ := exists_dualOpt A ν C hν hC
  exact ⟨_, kkt_bc A ν C (dualOpt_kkt A ν C hy)⟩

lemma blocking_spec {ν : Fin R → ℝ} {C : Fin J → ℝ} (hν : ∀ r, 0 < ν r) (hC : ∀ j, 0 < C j) :
    blockingConditions A ν C (blocking A ν C) := by
  have h := bc_exists A hν hC
  unfold blocking
  rw [dif_pos h]
  exact Classical.choose_spec h

lemma ar_inj (hrank : (Matrix.of fun j r => (A j r : ℝ)).rank = J) {y z : Fin J → ℝ}
    (h : ∀ r, ar A y r = ar A z r) : y = z := by
  set M : Matrix (Fin J) (Fin R) ℝ := Matrix.of fun j r => (A j r : ℝ)
  have hT : M.transpose.rank = J := by rw [Matrix.rank_transpose]; exact hrank
  have hker : LinearMap.ker M.transpose.mulVecLin = ⊥ := by
    have h1 := LinearMap.finrank_range_add_finrank_ker M.transpose.mulVecLin
    rw [← Matrix.rank, hT, Module.finrank_fin_fun] at h1
    exact Submodule.finrank_eq_zero.1 (by omega)
  have hmem : y - z ∈ LinearMap.ker M.transpose.mulVecLin := by
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]
    funext r
    have := h r
    unfold ar at this
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, M, Matrix.of_apply, Pi.sub_apply,
      Pi.zero_apply, mul_sub, Finset.sum_sub_distrib]
    have e1 : ∑ x, (A x r : ℝ) * y x = ∑ j, y j * (A j r : ℝ) :=
      Finset.sum_congr rfl (fun j _ => by ring)
    have e2 : ∑ x, (A x r : ℝ) * z x = ∑ j, z j * (A j r : ℝ) :=
      Finset.sum_congr rfl (fun j _ => by ring)
    rw [e1, e2, this, sub_self]
  rw [hker, Submodule.mem_bot, sub_eq_zero] at hmem
  exact hmem

lemma bc_unique {ν : Fin R → ℝ} {C : Fin J → ℝ} (hν : ∀ r, 0 < ν r)
    (hrank : (Matrix.of fun j r => (A j r : ℝ)).rank = J) {B B' : Fin J → ℝ}
    (hB : blockingConditions A ν C B) (hB' : blockingConditions A ν C B') : B = B' := by
  have hk := bc_kkt A ν C hB
  have hk' := bc_kkt A ν C hB'
  have hx : primalPoint A ν (dualFromBlocking B) = primalPoint A ν (dualFromBlocking B') := by
    apply kkt_unique A ν C hν hk' (kkt_feasible A ν C hν hk)
    rw [← kkt_value A ν C hν hk']
    exact kkt_isMax A ν C hν hk (kkt_feasible A ν C hν hk')
  have har : ∀ r, ar A (dualFromBlocking B) r = ar A (dualFromBlocking B') r := by
    intro r
    have := congrFun hx r
    rw [pp_eq, pp_eq] at this
    have h2 := mul_left_cancel₀ (hν r).ne' this
    have := Real.exp_injective h2
    linarith
  have := ar_inj A hrank har
  rw [← bfd_inv (fun j => (hB.1 j).2), this, bfd_inv (fun j => (hB'.1 j).2)]

/-- (3.6) is invariant under scaling of rates and capacities. -/
lemma bc_scale {ν : Fin R → ℝ} {C : Fin J → ℝ} {B : Fin J → ℝ} {N : ℝ} (hN : 0 < N)
    (hB : blockingConditions A ν C B) :
    blockingConditions A (fun r => ν r / N) (fun j => C j / N) B := by
  have hc : ∀ r, carried A (fun r => ν r / N) B r = carried A ν B r / N := by
    intro r; unfold carried; ring
  have hs : ∀ j, ∑ r, (A j r : ℝ) * carried A (fun r => ν r / N) B r =
      (∑ r, (A j r : ℝ) * carried A ν B r) / N := by
    intro j; simp only [hc, Finset.sum_div]
    exact Finset.sum_congr rfl (fun r _ => by ring)
  refine ⟨hB.1, fun j => ?_, fun j hj => ?_⟩
  · rw [hs]; exact div_le_div_of_nonneg_right (hB.2.1 j) hN.le
  · rw [hs, hB.2.2 j hj]

end X5LL


namespace X5LL
open KellyLossNetworks.Primal KellyStochasticNetworks KellyStochasticNetworks.LossLimits
open Filter Topology

variable {J R : ℕ} (A : Fin J → Fin R → ℕ)

lemma blocking_mem (ν : Fin R → ℝ) (C : Fin J → ℝ) (j : Fin J) :
    0 ≤ blocking A ν C j ∧ blocking A ν C j ≤ 1 := by
  unfold blocking
  split_ifs with h
  · have := (Classical.choose_spec h).1 j
    exact ⟨this.1, this.2.le⟩
  · simp

lemma carried_tendsto {ι : Type*} {l : Filter ι} {νs : ι → Fin R → ℝ} {Bs : ι → Fin J → ℝ}
    {ν : Fin R → ℝ} {B : Fin J → ℝ} (hν : ∀ r, Tendsto (fun n => νs n r) l (𝓝 (ν r)))
    (hB : ∀ j, Tendsto (fun n => Bs n j) l (𝓝 (B j))) (r : Fin R) :
    Tendsto (fun n => carried A (νs n) (Bs n) r) l (𝓝 (carried A ν B r)) := by
  unfold carried
  refine (hν r).mul (tendsto_finset_prod _ (fun j _ => ?_))
  exact ((tendsto_const_nhds.sub (hB j)).pow _)

lemma flow_tendsto {ι : Type*} {l : Filter ι} {νs : ι → Fin R → ℝ} {Bs : ι → Fin J → ℝ}
    {ν : Fin R → ℝ} {B : Fin J → ℝ} (hν : ∀ r, Tendsto (fun n => νs n r) l (𝓝 (ν r)))
    (hB : ∀ j, Tendsto (fun n => Bs n j) l (𝓝 (B j))) (j : Fin J) :
    Tendsto (fun n => ∑ r, (A j r : ℝ) * carried A (νs n) (Bs n) r) l
      (𝓝 (∑ r, (A j r : ℝ) * carried A ν B r)) :=
  tendsto_finset_sum _ (fun r _ => (carried_tendsto A hν hB r).const_mul _)

lemma flow_zero_of_one {ν : Fin R → ℝ} {B : Fin J → ℝ} {j : Fin J} (hj : B j = 1) :
    ∑ r, (A j r : ℝ) * carried A ν B r = 0 := by
  refine Finset.sum_eq_zero (fun r _ => ?_)
  rcases Nat.eq_zero_or_pos (A j r) with h | h
  · simp [h]
  · unfold carried
    rw [Finset.prod_eq_zero (Finset.mem_univ j) (by rw [hj, sub_self]; exact zero_pow h.ne')]
    ring

end X5LL


open MeasureTheory Filter Topology Complex ProbabilityTheory
open scoped Real NNReal Matrix

namespace GLG
open KellyStochasticNetworks KellyStochasticNetworks.LossLimits

section setup
variable {J R : ℕ} (A : Fin J → Fin R → ℕ) (νN : ℕ → Fin R → ℝ) (CN : ℕ → Fin J → ℕ)
  (ν : Fin R → ℝ) (C : Fin J → ℝ)

/-- finite-`N` blocking vector -/
noncomputable def BN (N : ℕ) : Fin J → ℝ := blocking A (νN N) (fun j => (CN N j : ℝ))

/-- finite-`N` mode -/
noncomputable def xN (N : ℕ) : Fin R → ℝ := mode A (νN N) (fun j => (CN N j : ℝ))

lemma xN_eq (N : ℕ) : xN A νN CN N = carried A (νN N) (BN A νN CN N) := rfl

lemma spec_N (hscale : Scaling A νN CN ν C) {N : ℕ} (hN : 0 < N) :
    blockingConditions A (νN N) (fun j => (CN N j : ℝ)) (BN A νN CN N) :=
  X5LL.blocking_spec A (hscale.rates_pos N hN)
    (fun j => by exact_mod_cast hscale.capacities_pos N hN j)

lemma spec_lim (hscale : Scaling A νN CN ν C) :
    blockingConditions A ν C (blocking A ν C) :=
  X5LL.blocking_spec A hscale.limit_rates_pos hscale.limit_capacities_pos

lemma carried_pos {ν' : Fin R → ℝ} (hν : ∀ r, 0 < ν' r) {B : Fin J → ℝ}
    (hB : ∀ j, B j < 1) (r : Fin R) : 0 < carried A ν' B r := by
  unfold carried
  exact mul_pos (hν r) (Finset.prod_pos (fun j _ => pow_pos (by linarith [hB j]) _))

lemma xb_pos (hscale : Scaling A νN CN ν C) (r : Fin R) : 0 < mode A ν C r :=
  carried_pos A hscale.limit_rates_pos (fun j => ((spec_lim A νN CN ν C hscale).1 j).2) r

lemma xN_pos (hscale : Scaling A νN CN ν C) {N : ℕ} (hN : 0 < N) (r : Fin R) :
    0 < xN A νN CN N r :=
  carried_pos A (hscale.rates_pos N hN) (fun j => ((spec_N A νN CN ν C hscale hN).1 j).2) r

lemma B_lim (hscale : Scaling A νN CN ν C) (hslack : strictSlack A ν C) (j : Fin J) :
    Tendsto (fun N => BN A νN CN N j) atTop (𝓝 (blocking A ν C j)) :=
  tendsto_pi_nhds.1 (blocking_mode_limit A νN CN ν C hscale hslack).1 j

lemma x_lim (hscale : Scaling A νN CN ν C) (hslack : strictSlack A ν C) (r : Fin R) :
    Tendsto (fun N : ℕ => xN A νN CN N r / N) atTop (𝓝 (mode A ν C r)) :=
  tendsto_pi_nhds.1 (blocking_mode_limit A νN CN ν C hscale hslack).2 r

lemma load_lim (hscale : Scaling A νN CN ν C) (hslack : strictSlack A ν C) (j : Fin J) :
    Tendsto (fun N : ℕ => (∑ r, (A j r : ℝ) * xN A νN CN N r) / N) atTop
      (𝓝 (∑ r, (A j r : ℝ) * mode A ν C r)) := by
  simp_rw [Finset.sum_div]
  refine tendsto_finsetSum _ (fun r _ => ?_)
  have := (x_lim A νN CN ν C hscale hslack r).const_mul (A j r : ℝ)
  refine this.congr (fun N => ?_)
  ring

lemma active_eq (hscale : Scaling A νN CN ν C) (hslack : strictSlack A ν C) (j : Fin J)
    (hj : 0 < blocking A ν C j) :
    ∀ᶠ N in atTop, ∑ r, (A j r : ℝ) * xN A νN CN N r = CN N j := by
  filter_upwards [(B_lim A νN CN ν C hscale hslack j).eventually (lt_mem_nhds hj),
    eventually_gt_atTop 0] with N hN hN0
  exact (spec_N A νN CN ν C hscale hN0).2.2 j hN

lemma inactive_zero (hscale : Scaling A νN CN ν C) (hslack : strictSlack A ν C) (j : Fin J)
    (hj : ¬ 0 < blocking A ν C j) : ∀ᶠ N in atTop, BN A νN CN N j = 0 := by
  have hB0 : blocking A ν C j = 0 :=
    le_antisymm (not_lt.1 hj) ((spec_lim A νN CN ν C hscale).1 j).1
  have hsl := hslack j hB0
  by_contra hne
  rw [Filter.not_eventually] at hne
  have hfreq : ∃ᶠ N in atTop, (∑ r, (A j r : ℝ) * xN A νN CN N r) / N = (CN N j : ℝ) / N := by
    refine (hne.and_eventually (eventually_gt_atTop 0)).mono (fun N hN => ?_)
    have hpos : 0 < BN A νN CN N j :=
      lt_of_le_of_ne ((spec_N A νN CN ν C hscale hN.2).1 j).1 (Ne.symm hN.1)
    rw [xN_eq, (spec_N A νN CN ν C hscale hN.2).2.2 j hpos]
  have := tendsto_nhds_unique_of_frequently_eq (load_lim A νN CN ν C hscale hslack j)
    (hscale.capacities_limit j) hfreq
  linarith

lemma slack_eps (hscale : Scaling A νN CN ν C) (hslack : strictSlack A ν C) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ N in atTop, ∀ j, ¬ 0 < blocking A ν C j →
      ∑ r, (A j r : ℝ) * xN A νN CN N r + ε * N ≤ CN N j := by
  classical
  set δ : Fin J → ℝ := fun j => if 0 < blocking A ν C j then 1 else
    C j - ∑ r, (A j r : ℝ) * mode A ν C r with hδ
  have hδpos : ∀ j, 0 < δ j := by
    intro j
    simp only [hδ]
    split_ifs with hj
    · exact one_pos
    · have hB0 : blocking A ν C j = 0 :=
        le_antisymm (not_lt.1 hj) ((spec_lim A νN CN ν C hscale).1 j).1
      have := hslack j hB0
      linarith
  obtain ⟨m, hm, hmle⟩ := GLL.exists_pos_lower δ hδpos
  refine ⟨m / 2, by positivity, ?_⟩
  rw [eventually_all]
  intro j
  by_cases hj : 0 < blocking A ν C j
  · exact Eventually.of_forall (fun N h => absurd hj h)
  · have hlim := (hscale.capacities_limit j).sub (load_lim A νN CN ν C hscale hslack j)
    have hδj : δ j = C j - ∑ r, (A j r : ℝ) * mode A ν C r := by simp [hδ, hj]
    have hgt : m / 2 < C j - ∑ r, (A j r : ℝ) * mode A ν C r := by
      have := hmle j; rw [hδj] at this; linarith
    filter_upwards [hlim.eventually (lt_mem_nhds hgt), eventually_gt_atTop 0] with N hN hN0 _
    have hNp : (0:ℝ) < N := by exact_mod_cast hN0
    rw [← sub_div, lt_div_iff₀ hNp] at hN
    linarith

end setup

section weights
variable {J R : ℕ} (A : Fin J → Fin R → ℕ) (νN : ℕ → Fin R → ℝ) (CN : ℕ → Fin J → ℕ)
  (ν : Fin R → ℝ) (C : Fin J → ℝ)

/-- active links -/
abbrev Act : Type := Active (blocking A ν C)
/-- inactive links -/
abbrev Inact : Type := {j : Fin J // ¬ 0 < blocking A ν C j}

noncomputable instance : Fintype (Inact A ν C) := by classical exact Subtype.fintype _

noncomputable def bA : ℕ := Fintype.card (Act A ν C)
noncomputable def eA : Fin (bA A ν C) ≃ Act A ν C := (Fintype.equivFin _).symm

noncomputable def Hm (i : Fin (bA A ν C)) (r : Fin R) : ℕ := A (eA A ν C i).val r
def Gm (k : Inact A ν C) (r : Fin R) : ℕ := A k.1 r
noncomputable def qN (N : ℕ) (i : Fin (bA A ν C)) : ℝ := 1 - BN A νN CN N (eA A ν C i).val
noncomputable def cN (N : ℕ) (i : Fin (bA A ν C)) : ℕ := CN N (eA A ν C i).val
def capN (N : ℕ) (k : Inact A ν C) : ℕ := CN N k.1

/-- the exact weight in core form -/
noncomputable def Wc (N : ℕ) (n : Fin R → ℕ) : ℝ :=
  GLL.coreW (Hm A ν C) (Gm A ν C) (qN A νN CN ν C) (cN A CN ν C) (capN A CN ν C) N n

lemma prod_split (f : Fin J → ℝ) :
    ∏ j, f j = (∏ i, f (eA A ν C i).val) * ∏ k : Inact A ν C, f k.1 := by
  classical
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun j => 0 < blocking A ν C j) f]
  congr 1
  exact Fintype.prod_equiv (eA A ν C).symm _ _ (fun a => by simp)

lemma mem_states_iff (N : ℕ) (n : Fin R → ℕ) :
    ((∀ i, ∑ r, Hm A ν C i r * n r ≤ cN A CN ν C N i) ∧
      (∀ k, ∑ r, Gm A ν C k r * n r ≤ capN A CN ν C N k)) ↔ n ∈ lossStates A (CN N) := by
  constructor
  · rintro ⟨h1, h2⟩ j
    by_cases hj : 0 < blocking A ν C j
    · obtain ⟨i, hi⟩ := (eA A ν C).surjective ⟨j, hj⟩
      have hv : (eA A ν C i).val = j := congrArg (fun a : Act A ν C => a.val) hi
      have := h1 i
      simp only [Hm, cN, hv] at this
      exact this
    · exact h2 ⟨j, hj⟩
  · intro h
    exact ⟨fun i => h _, fun k => h _⟩

open Classical in
lemma Wc_eq (N : ℕ) (n : Fin R → ℕ) :
    Wc A νN CN ν C N n = if n ∈ lossStates A (CN N) then
      ∏ i, qN A νN CN ν C N i ^ (cN A CN ν C N i - ∑ r, Hm A ν C i r * n r) else 0 := by
  unfold Wc GLL.coreW
  simp only [mem_states_iff]

lemma poisPi_real_singleton {x : Fin R → ℝ} (hx : ∀ r, 0 ≤ x r) (n : Fin R → ℕ) :
    (GLL.poisPi x).real {n} = ∏ r, Real.exp (-x r) * x r ^ n r / (n r).factorial := by
  have : ({n} : Set (Fin R → ℕ)) = Set.pi Set.univ (fun r => {n r}) := by
    ext m; simp [funext_iff]
  rw [measureReal_def, this, GLL.poisPi, Measure.pi_pi, ENNReal.toReal_prod]
  refine Finset.prod_congr rfl (fun r _ => ?_)
  rw [← measureReal_def, poissonMeasure_real_singleton, Real.coe_toNNReal _ (hx r)]

/-- the weight identity -/
lemma weight_identity (hscale : Scaling A νN CN ν C) {N : ℕ} (hN : 0 < N)
    (hzero : ∀ k : Inact A ν C, BN A νN CN N k.1 = 0) (n : Fin R → ℕ) :
    (lossStates A (CN N)).indicator (lossWeight (νN N)) n *
      ∏ i, qN A νN CN ν C N i ^ (cN A CN ν C N i) =
    Real.exp (∑ r, xN A νN CN N r) * (GLL.poisPi (xN A νN CN N)).real {n} * Wc A νN CN ν C N n := by
  set x := xN A νN CN N with hx
  set q := qN A νN CN ν C N with hq
  have hspec := spec_N A νN CN ν C hscale hN
  have hq0 : ∀ i, 0 < q i := fun i => by
    simp only [hq, qN]; linarith [(hspec.1 (eA A ν C i).val).2]
  -- route identity x_r = ν_r ∏ q^{H}
  have hxr : ∀ r, x r = νN N r * ∏ i, q i ^ (Hm A ν C i r) := by
    intro r
    rw [hx, xN_eq]
    unfold carried
    rw [prod_split A ν C (fun j => (1 - BN A νN CN N j) ^ A j r)]
    have : ∏ k : Inact A ν C, (1 - BN A νN CN N k.1) ^ A k.1 r = 1 :=
      Finset.prod_eq_one (fun k _ => by rw [hzero k]; simp)
    rw [this, mul_one]
    rfl
  have hx0 : ∀ r, 0 ≤ x r := fun r => (xN_pos A νN CN ν C hscale hN r).le
  rw [poisPi_real_singleton hx0, Wc_eq]
  by_cases hn : n ∈ lossStates A (CN N)
  · rw [Set.indicator_of_mem hn, if_pos hn]
    have hle : ∀ i, ∑ r, Hm A ν C i r * n r ≤ cN A CN ν C N i :=
      ((mem_states_iff A CN ν C N n).2 hn).1
    -- left side
    have hL : lossWeight (νN N) n * ∏ i, q i ^ (cN A CN ν C N i) =
        (∏ r, νN N r ^ n r / (n r).factorial) * (∏ i, q i ^ (∑ r, Hm A ν C i r * n r)) *
          ∏ i, q i ^ (cN A CN ν C N i - ∑ r, Hm A ν C i r * n r) := by
      unfold lossWeight
      rw [mul_assoc, ← Finset.prod_mul_distrib]
      congr 1
      refine Finset.prod_congr rfl (fun i _ => ?_)
      rw [← pow_add, Nat.add_sub_cancel' (hle i)]
    -- right side
    have hR : Real.exp (∑ r, x r) * ∏ r, Real.exp (-x r) * x r ^ n r / (n r).factorial =
        (∏ r, νN N r ^ n r / (n r).factorial) * (∏ i, q i ^ (∑ r, Hm A ν C i r * n r)) := by
      rw [Real.exp_sum, ← Finset.prod_mul_distrib]
      have e1 : ∀ r, Real.exp (x r) * (Real.exp (-x r) * x r ^ n r / (n r).factorial) =
          x r ^ n r / (n r).factorial := by
        intro r
        rw [← mul_div_assoc, ← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero,
          one_mul]
      simp_rw [e1, hxr, mul_pow, ← Finset.prod_pow]
      have e2 : ∏ r, (νN N r ^ n r * ∏ i, (q i ^ Hm A ν C i r) ^ n r) / (n r).factorial =
          (∏ r, νN N r ^ n r / (n r).factorial) * ∏ r, ∏ i, (q i ^ Hm A ν C i r) ^ n r := by
        rw [← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl (fun r _ => by ring)
      rw [e2]
      congr 1
      rw [Finset.prod_comm]
      refine Finset.prod_congr rfl (fun i _ => ?_)
      rw [← Finset.prod_pow_eq_pow_sum]
      refine Finset.prod_congr rfl (fun r _ => ?_)
      rw [← pow_mul]
    rw [hL, ← hR]
  · rw [Set.indicator_of_notMem hn, if_neg hn]; simp

lemma lossWeight_nonneg {ν' : Fin R → ℝ} (hν : ∀ r, 0 < ν' r) (n : Fin R → ℕ) :
    0 ≤ lossWeight ν' n := by
  unfold lossWeight
  exact Finset.prod_nonneg (fun r _ => div_nonneg (pow_nonneg (hν r).le _) (Nat.cast_nonneg _))

lemma integral_poisPi_eq_tsum (x : Fin R → ℝ) (f : (Fin R → ℕ) → ℂ) :
    ∫ n, f n ∂(GLL.poisPi x) = ∑' n, ((GLL.poisPi x).real {n} : ℂ) * f n := by
  conv_lhs => rw [← Measure.sum_smul_dirac (GLL.poisPi x)]
  rw [integral_sum_dirac (fun n => measure_ne_top _ _)]
  refine tsum_congr (fun n => ?_)
  rw [Complex.real_smul, measureReal_def]

/-- integrals against the exact occupancy law as ratios of Poisson integrals -/
lemma occ_integral (hscale : Scaling A νN CN ν C) {N : ℕ} (hN : 0 < N)
    (hzero : ∀ k : Inact A ν C, BN A νN CN N k.1 = 0) (g : (Fin R → ℕ) → ℂ) :
    ∫ n, g n ∂(occupancyLaw A (νN N) (CN N)) =
      (∫ n, (Wc A νN CN ν C N n : ℂ) * g n ∂(GLL.poisPi (xN A νN CN N))) /
        (∫ n, (Wc A νN CN ν C N n : ℂ) ∂(GLL.poisPi (xN A νN CN N))) := by
  have hpl := product_law_normalized A (νN N) (CN N) (hscale.rates_pos N hN)
  set Z := partition A (νN N) (CN N) with hZ
  have hZ0 : 0 < Z := hpl.1
  set S := lossStates A (CN N) with hS
  set q := qN A νN CN ν C N with hq
  have hspec := spec_N A νN CN ν C hscale hN
  have hq0 : ∀ i, 0 < q i := fun i => by
    simp only [hq, qN]; linarith [(hspec.1 (eA A ν C i).val).2]
  set Q := ∏ i, q i ^ (cN A CN ν C N i) with hQ
  have hQ0 : 0 < Q := Finset.prod_pos (fun i _ => pow_pos (hq0 i) _)
  set x := xN A νN CN N with hx
  set κ : ℝ := Real.exp (∑ r, x r) / (Z * Q) with hκ
  have key : ∀ g : (Fin R → ℕ) → ℂ, ∫ n, g n ∂(occupancyLaw A (νN N) (CN N)) =
      (κ : ℂ) * ∫ n, (Wc A νN CN ν C N n : ℂ) * g n ∂(GLL.poisPi x) := by
    intro g
    unfold occupancyLaw
    rw [← hZ]
    rw [integral_sum_dirac (fun _ => ENNReal.ofReal_ne_top), integral_poisPi_eq_tsum,
      ← tsum_mul_left]
    have hsub : ∀ s : S, (ENNReal.ofReal (lossWeight (νN N) (s : Fin R → ℕ) / Z)).toReal •
        g s = ((lossWeight (νN N) s / Z : ℝ) : ℂ) * g s := by
      intro s
      rw [Complex.real_smul, ENNReal.toReal_ofReal
        (div_nonneg (lossWeight_nonneg (hscale.rates_pos N hN) _) hZ0.le)]
    simp_rw [hsub]
    rw [tsum_subtype S (fun n => ((lossWeight (νN N) n / Z : ℝ) : ℂ) * g n)]
    refine tsum_congr (fun n => ?_)
    have hw := weight_identity A νN CN ν C hscale hN hzero n
    rw [← hx] at hw
    have e1 : S.indicator (fun n => ((lossWeight (νN N) n / Z : ℝ) : ℂ) * g n) n =
        ((S.indicator (lossWeight (νN N)) n / Z : ℝ) : ℂ) * g n := by
      by_cases hn : n ∈ S
      · rw [Set.indicator_of_mem hn, Set.indicator_of_mem hn]
      · rw [Set.indicator_of_notMem hn, Set.indicator_of_notMem hn]; simp
    rw [e1]
    have e2 : S.indicator (lossWeight (νN N)) n / Z =
        κ * ((GLL.poisPi x).real {n} * Wc A νN CN ν C N n) := by
      rw [hκ]
      field_simp
      rw [hw]
    rw [e2]
    push_cast
    ring
  have h1 := key (fun _ => 1)
  simp only [integral_const, mul_one] at h1
  have hprob : IsProbabilityMeasure (occupancyLaw A (νN N) (CN N)) := hpl.2.2.2.1
  rw [probReal_univ, one_smul] at h1
  have hne : (∫ n, (Wc A νN CN ν C N n : ℂ) ∂(GLL.poisPi x)) ≠ 0 := by
    intro h; rw [h, mul_zero] at h1; exact one_ne_zero h1
  rw [key g]
  field_simp
  linear_combination -(∫ n, (Wc A νN CN ν C N n : ℂ) * g n ∂(GLL.poisPi x)) * h1

end weights

section gauss
variable {J R : ℕ} (A : Fin J → Fin R → ℕ) (νN : ℕ → Fin R → ℝ) (CN : ℕ → Fin J → ℕ)
  (ν : Fin R → ℝ) (C : Fin J → ℝ)

lemma rows_indep (hscale : Scaling A νN CN ν C) :
    LinearIndependent ℝ (fun j : Fin J => fun r => (A j r : ℝ)) := by
  have h := hscale.rank_full
  rw [Matrix.rank_eq_finrank_span_row] at h
  rw [linearIndependent_iff_card_eq_finrank_span, Fintype.card_fin]
  exact h.symm

lemma Hm_indep (hscale : Scaling A νN CN ν C) :
    LinearIndependent ℝ (fun i : Fin (bA A ν C) => fun r => (Hm A ν C i r : ℝ)) := by
  have h := (rows_indep A νN CN ν C hscale).comp (fun i => (eA A ν C i).val)
    (Subtype.val_injective.comp (eA A ν C).injective)
  exact h

lemma sum_rev4 {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (f : α → β → γ → δ → ℝ) :
    ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ d, ∑ c, ∑ b, ∑ a, f a b c d := by
  calc ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ a, ∑ b, ∑ d, ∑ c, f a b c d :=
        Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_comm))
    _ = ∑ a, ∑ d, ∑ b, ∑ c, f a b c d :=
        Finset.sum_congr rfl (fun a _ => Finset.sum_comm)
    _ = ∑ d, ∑ a, ∑ b, ∑ c, f a b c d := Finset.sum_comm
    _ = ∑ d, ∑ a, ∑ c, ∑ b, f a b c d :=
        Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun a _ => Finset.sum_comm))
    _ = ∑ d, ∑ c, ∑ a, ∑ b, f a b c d :=
        Finset.sum_congr rfl (fun d _ => Finset.sum_comm)
    _ = ∑ d, ∑ c, ∑ b, ∑ a, f a b c d :=
        Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun c _ => Finset.sum_comm))

open Classical in
/-- the weighted active Gram matrix is invertible -/
lemma gram_det_ne (hscale : Scaling A νN CN ν C) {x : Fin R → ℝ} (hx : ∀ r, 0 < x r) :
    (activeGram A (blocking A ν C) x).det ≠ 0 := by
  classical
  intro h0
  obtain ⟨y, hy0, hy⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  apply hy0
  set a : Fin R → ℝ := fun r => ∑ j : Act A ν C, (A j.val r : ℝ) * y j with ha
  have hq : ∑ r, x r * a r ^ 2 = 0 := by
    have h1 : ∑ j : Act A ν C, y j * (activeGram A (blocking A ν C) x *ᵥ y) j = 0 := by
      rw [hy]; simp
    rw [← h1]
    have h2 : ∀ j : Act A ν C, (activeGram A (blocking A ν C) x *ᵥ y) j =
        ∑ r, (A j.val r : ℝ) * x r * a r := by
      intro j
      simp only [Matrix.mulVec, dotProduct, activeGram, ha, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl (fun r _ => Finset.sum_congr rfl (fun k _ => by ring))
    simp_rw [h2, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    simp only [ha, sq, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun _ _ => by ring))
  have hz : ∀ r, a r = 0 := by
    intro r
    have hnn : ∀ r ∈ Finset.univ, 0 ≤ x r * a r ^ 2 :=
      fun r _ => mul_nonneg (hx r).le (sq_nonneg _)
    have := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hq r (Finset.mem_univ r)
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h (hx r).ne'
    · exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h
  have hli := (rows_indep A νN CN ν C hscale).comp (fun j : Act A ν C => j.val)
    Subtype.val_injective
  have := (Fintype.linearIndependent_iff.1 hli) y (by
    funext r
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Function.comp, Pi.zero_apply]
    refine (Finset.sum_congr rfl (fun j _ => by ring)).trans (hz r))
  funext j; exact this j

/-- the dual vector of the residual map -/
noncomputable def resT (x : Fin R → ℝ) (ξ : Fin R → ℝ) (k : Act A ν C) : ℝ := by
  classical
  exact ∑ j : Act A ν C, (∑ r, ξ r * x r * (A j.val r : ℝ)) *
    (activeGram A (blocking A ν C) x)⁻¹ j k

noncomputable def resV (x : Fin R → ℝ) (ξ : Fin R → ℝ) (s : Fin R) : ℝ :=
  ξ s - ∑ k : Act A ν C, (A k.val s : ℝ) * resT A ν C x ξ k

lemma residual_pair (x : Fin R → ℝ) (ξ z : Fin R → ℝ) :
    ∑ r, ξ r * gaussianResidual A (blocking A ν C) x z r = ∑ s, resV A ν C x ξ s * z s := by
  classical
  set Mi := (activeGram A (blocking A ν C) x)⁻¹ with hMi
  have hL : ∑ r, ξ r * gaussianResidual A (blocking A ν C) x z r =
      ∑ r, ξ r * z r - ∑ r, ∑ j : Act A ν C, ∑ k : Act A ν C, ∑ s,
        ξ r * x r * (A j.val r : ℝ) * Mi j k * (A k.val s : ℝ) * z s := by
    unfold gaussianResidual
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    rw [mul_sub]
    congr 1
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun k _ =>
      Finset.sum_congr rfl (fun s _ => ?_)))
    rw [hMi]; ring
  have hR : ∑ s, resV A ν C x ξ s * z s =
      ∑ r, ξ r * z r - ∑ s, ∑ k : Act A ν C, ∑ j : Act A ν C, ∑ r,
        ξ r * x r * (A j.val r : ℝ) * Mi j k * (A k.val s : ℝ) * z s := by
    unfold resV resT
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    rw [sub_mul]
    congr 1
    simp only [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun j _ =>
      Finset.sum_congr rfl (fun r _ => ?_)))
    rw [hMi]; ring
  rw [hL, hR, sum_rev4 (fun r (j : Act A ν C) (k : Act A ν C) s =>
    ξ r * x r * (A j.val r : ℝ) * Mi j k * (A k.val s : ℝ) * z s)]

lemma gauss_charFun (hscale : Scaling A νN CN ν C) (ξ : Fin R → ℝ) :
    ∫ u, cexp (I * ∑ r, (ξ r : ℂ) * (u r : ℂ))
        ∂(conditionedGaussian A (blocking A ν C) (mode A ν C)) =
      cexp (-((∑ r, mode A ν C r * resV A ν C (mode A ν C) ξ r ^ 2 : ℝ) : ℂ) / 2) := by
  set xb := mode A ν C with hxb
  set v := resV A ν C xb ξ with hv
  have hxb0 : ∀ r, 0 < xb r := xb_pos A νN CN ν C hscale
  unfold conditionedGaussian
  have hmeas : Measurable (gaussianResidual A (blocking A ν C) xb) := by
    have : Continuous (gaussianResidual A (blocking A ν C) xb) := by
      unfold gaussianResidual; fun_prop
    exact this.measurable
  rw [integral_map hmeas.aemeasurable (Continuous.aestronglyMeasurable (by fun_prop))]
  have hpt : ∀ z : Fin R → ℝ, cexp (I * ∑ r, (ξ r : ℂ) *
      (gaussianResidual A (blocking A ν C) xb z r : ℂ)) = ∏ s, cexp ((I * v s) * (z s : ℂ)) := by
    intro z
    rw [← Complex.exp_sum]
    congr 1
    have := residual_pair A ν C xb ξ z
    have hc := congrArg (fun t : ℝ => (t : ℂ)) this
    push_cast at hc
    rw [hc, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun s _ => by ring)
  simp_rw [hpt]
  rw [integral_fintype_prod_eq_prod (f := fun s (t : ℝ) => cexp ((I * v s) * (t : ℂ)))]
  have h1 : ∀ s, ∫ t, cexp ((I * v s) * (t : ℂ)) ∂(gaussianReal 0 (xb s).toNNReal) =
      cexp (-((xb s * v s ^ 2 : ℝ) : ℂ) / 2) := by
    intro s
    have := complexMGF_id_gaussianReal (μ := 0) (v := (xb s).toNNReal) (I * v s)
    unfold complexMGF at this
    simp only [id] at this
    rw [this, Real.coe_toNNReal _ (hxb0 s).le]
    congr 1
    push_cast
    rw [mul_pow, Complex.I_sq]; ring
  simp_rw [h1]
  rw [← Complex.exp_sum]
  congr 1
  push_cast
  rw [neg_div, Finset.sum_div, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun s _ => by ring)

lemma resV_cond1 (ξ : Fin R → ℝ) (r : Fin R) :
    resV A ν C (mode A ν C) ξ r = ξ r + ∑ i, (Hm A ν C i r : ℝ) *
      (-(resT A ν C (mode A ν C) ξ (eA A ν C i))) := by
  unfold resV
  rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  refine Fintype.sum_equiv (eA A ν C).symm _ _ (fun k => ?_)
  simp [Hm]

open Classical in
lemma resV_cond2 (hscale : Scaling A νN CN ν C) (ξ : Fin R → ℝ) (i : Fin (bA A ν C)) :
    ∑ r, (Hm A ν C i r : ℝ) * mode A ν C r * resV A ν C (mode A ν C) ξ r = 0 := by
  set xb := mode A ν C with hxb
  set M := activeGram A (blocking A ν C) xb with hM
  have hdet : IsUnit M.det := isUnit_iff_ne_zero.2
    (gram_det_ne A νN CN ν C hscale (xb_pos A νN CN ν C hscale))
  have hinv : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul M hdet
  set j := eA A ν C i with hj
  set w : Act A ν C → ℝ := fun l => ∑ r, ξ r * xb r * (A l.val r : ℝ) with hw
  have hT : ∀ k, resT A ν C xb ξ k = ∑ l, w l * M⁻¹ l k := by
    intro k; unfold resT; rfl
  have hMs : ∀ k l : Act A ν C, M k l = ∑ r, (A l.val r : ℝ) * xb r * (A k.val r : ℝ) := by
    intro k l; simp only [hM, activeGram]
    exact Finset.sum_congr rfl (fun r _ => by ring)
  unfold resV
  simp only [Hm, ← hj]
  have e1 : ∑ r, (A j.val r : ℝ) * xb r * (ξ r - ∑ k, (A k.val r : ℝ) * resT A ν C xb ξ k) =
      w j - ∑ k, M j k * resT A ν C xb ξ k := by
    rw [hw]
    simp only [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
    congr 1
    · exact Finset.sum_congr rfl (fun r _ => by ring)
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [hM]; unfold activeGram
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl (fun r _ => by ring)
  rw [e1]
  have e2 : ∑ k, M j k * resT A ν C xb ξ k = w j := by
    simp_rw [hT, Finset.mul_sum]
    rw [Finset.sum_comm]
    have : ∀ l, ∑ k, M j k * (w l * M⁻¹ l k) = w l * (M⁻¹ * M) l j := by
      intro l
      rw [Matrix.mul_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [hMs j k, hMs k j]
      have : ∑ r, (A k.val r : ℝ) * xb r * (A j.val r : ℝ) =
          ∑ r, (A j.val r : ℝ) * xb r * (A k.val r : ℝ) :=
        Finset.sum_congr rfl (fun r _ => by ring)
      rw [this]; ring
    simp_rw [this, hinv, Matrix.one_apply]
    simp
  rw [e2, sub_self]

end gauss

section main
variable {J R : ℕ} (A : Fin J → Fin R → ℕ) (νN : ℕ → Fin R → ℝ) (CN : ℕ → Fin J → ℕ)
  (ν : Fin R → ℝ) (C : Fin J → ℝ)

/-- complex exponential moments of the fluctuation law converge; the limit is the
characteristic function of the conditioned Gaussian on the imaginary axis -/
theorem glue_main (hscale : Scaling A νN CN ν C) (hslack : strictSlack A ν C) :
    ∃ L : (Fin R → ℂ) → ℂ,
      (∀ ζ : Fin R → ℂ, Tendsto (fun N => ∫ u, cexp (∑ r, ζ r * (u r : ℂ))
        ∂(fluctuationLaw A νN CN N)) atTop (𝓝 (L ζ))) ∧
      (∀ ξ : Fin R → ℝ, L (fun r => I * ξ r) = ∫ u, cexp (I * ∑ r, (ξ r : ℂ) * (u r : ℂ))
        ∂(conditionedGaussian A (blocking A ν C) (mode A ν C))) := by
  classical
  have hlimspec := spec_lim A νN CN ν C hscale
  obtain ⟨ε, hε, hslackε⟩ := slack_eps A νN CN ν C hscale hslack
  have hc : ∀ᶠ N in atTop, ∀ i, (cN A CN ν C N i : ℝ) =
      ∑ r, (Hm A ν C i r : ℝ) * xN A νN CN N r := by
    rw [eventually_all]
    intro i
    filter_upwards [active_eq A νN CN ν C hscale hslack (eA A ν C i).val (eA A ν C i).2]
      with N hN
    simp only [cN, Hm]; exact hN.symm
  have hcap : ∀ᶠ N in atTop, ∀ k, ∑ r, (Gm A ν C k r : ℝ) * xN A νN CN N r + ε * N ≤
      capN A CN ν C N k := by
    filter_upwards [hslackε] with N hN k
    exact hN k.1 k.2
  have hq : ∀ i, Tendsto (fun N => qN A νN CN ν C N i) atTop
      (𝓝 (1 - blocking A ν C (eA A ν C i).val)) := fun i =>
    (B_lim A νN CN ν C hscale hslack (eA A ν C i).val).const_sub 1
  obtain ⟨L, hL1, hL2⟩ := GLL.core_final (Hm A ν C) (Hm_indep A νN CN ν C hscale) (Gm A ν C)
    (xN A νN CN) (mode A ν C) (xb_pos A νN CN ν C hscale) (x_lim A νN CN ν C hscale hslack)
    (qN A νN CN ν C) (fun i => 1 - blocking A ν C (eA A ν C i).val)
    (fun i => by linarith [(hlimspec.1 (eA A ν C i).val).2])
    (fun i => by linarith [(eA A ν C i).2])
    hq (cN A CN ν C) hc (capN A CN ν C) ε hε hcap
  refine ⟨L, fun ζ => ?_, fun ξ => ?_⟩
  · refine (hL1 ζ).congr' ?_
    have hzero : ∀ᶠ N in atTop, ∀ k : Inact A ν C, BN A νN CN N k.1 = 0 := by
      rw [eventually_all]
      intro k
      exact inactive_zero A νN CN ν C hscale hslack k.1 k.2
    filter_upwards [hzero, eventually_gt_atTop 0] with N hN hN0
    have hφ : Measurable (fun n : Fin R → ℕ => fun r =>
        ((n r : ℝ) - mode A (νN N) (fun j => (CN N j : ℝ)) r) / Real.sqrt N) :=
      measurable_of_countable _
    unfold fluctuationLaw
    rw [integral_map hφ.aemeasurable (Continuous.aestronglyMeasurable (by fun_prop))]
    rw [occ_integral A νN CN ν C hscale hN0 hN]
    rfl
  · rw [hL2 ξ (resV A ν C (mode A ν C) ξ) (fun i => -(resT A ν C (mode A ν C) ξ (eA A ν C i)))
      (resV_cond1 A ν C ξ) (resV_cond2 A νN CN ν C hscale ξ), gauss_charFun A νN CN ν C hscale ξ]

end main

section children
variable {J R : ℕ} (A : Fin J → Fin R → ℕ) (νN : ℕ → Fin R → ℝ) (CN : ℕ → Fin J → ℕ)
  (ν : Fin R → ℝ) (C : Fin J → ℝ)

theorem childB (hscale : Scaling A νN CN ν C) (hslack : strictSlack A ν C) (ξ : Fin R → ℝ) :
    Tendsto (fun N => ∫ u, Complex.exp (Complex.I * ∑ r, (ξ r : ℂ) * (u r : ℂ))
        ∂(fluctuationLaw A νN CN N)) atTop
      (𝓝 (∫ u, Complex.exp (Complex.I * ∑ r, (ξ r : ℂ) * (u r : ℂ))
        ∂(conditionedGaussian A (blocking A ν C) (mode A ν C)))) := by
  obtain ⟨L, hL1, hL2⟩ := glue_main A νN CN ν C hscale hslack
  rw [← hL2 ξ]
  refine (hL1 (fun r => I * ξ r)).congr (fun N => ?_)
  congr 1; funext u
  congr 1
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun r _ => by ring)

lemma exp_integrable_N (hscale : Scaling A νN CN ν C) (η : Fin R → ℝ) {N : ℕ} (hN : 0 < N) :
    Integrable (fun u : Fin R → ℝ => Real.exp (∑ r, η r * u r)) (fluctuationLaw A νN CN N) := by
  set x := mode A (νN N) (fun j => (CN N j : ℝ)) with hx
  set φ : (Fin R → ℕ) → (Fin R → ℝ) := fun n r => ((n r : ℝ) - x r) / Real.sqrt N with hφ
  have hpl := product_law_normalized A (νN N) (CN N) (hscale.rates_pos N hN)
  set Z := partition A (νN N) (CN N) with hZ
  have hZ0 : 0 < Z := hpl.1
  unfold fluctuationLaw
  rw [integrable_map_measure (Continuous.aestronglyMeasurable (by fun_prop))
    (measurable_of_countable _).aemeasurable]
  unfold occupancyLaw
  rw [← hZ, integrable_sum_dirac_iff (fun _ => ENNReal.ofReal_ne_top)]
  -- summable majorant over all occupancy vectors
  set f : Fin R → ℕ → ℝ := fun r k =>
    νN N r ^ k / (k.factorial : ℝ) * Real.exp (η r * (((k : ℝ) - x r) / Real.sqrt N)) with hf
  have hf0 : ∀ r k, 0 ≤ f r k := fun r k => by
    simp only [hf]
    exact mul_nonneg (div_nonneg (pow_nonneg (hscale.rates_pos N hN r).le _)
      (Nat.cast_nonneg _)) (Real.exp_pos _).le
  have hfs : ∀ r, Summable (f r) := by
    intro r
    have : f r = fun k => Real.exp (-(η r * x r / Real.sqrt N)) *
        ((νN N r * Real.exp (η r / Real.sqrt N)) ^ k / (k.factorial : ℝ)) := by
      funext k
      simp only [hf]
      rw [mul_pow, ← Real.exp_nat_mul, mul_div_assoc, mul_div_right_comm _ _ ((k.factorial : ℝ))]
      rw [show Real.exp (η r * (((k : ℝ) - x r) / Real.sqrt N)) =
          Real.exp (-(η r * x r / Real.sqrt N)) * Real.exp (k * (η r / Real.sqrt N)) by
        rw [← Real.exp_add]; congr 1; ring]
      ring
    rw [this]
    exact (Real.summable_pow_div_factorial _).mul_left _
  have hall := GLL.summable_pi_prod R f hf0 hfs
  have hsub := (hall.div_const Z).subtype (lossStates A (CN N))
  refine hsub.congr (fun s => ?_)
  simp only [Function.comp, Real.norm_eq_abs]
  rw [ENNReal.toReal_ofReal (div_nonneg (lossWeight_nonneg (hscale.rates_pos N hN) _) hZ0.le),
    abs_of_pos (Real.exp_pos _)]
  simp only [hf, lossWeight, hφ]
  rw [Real.exp_sum, div_mul_eq_mul_div, ← Finset.prod_mul_distrib]

theorem childA (hscale : Scaling A νN CN ν C) (hslack : strictSlack A ν C) (η : Fin R → ℝ) :
    (∀ N, 0 < N → Integrable (fun u : Fin R → ℝ => Real.exp (∑ r, η r * u r))
      (fluctuationLaw A νN CN N)) ∧
    ∃ M : ℝ, ∀ᶠ N in atTop,
      ∫ u, Real.exp (∑ r, η r * u r) ∂(fluctuationLaw A νN CN N) ≤ M := by
  refine ⟨fun N hN => exp_integrable_N A νN CN ν C hscale η hN, ?_⟩
  obtain ⟨L, hL1, -⟩ := glue_main A νN CN ν C hscale hslack
  have h := hL1 (fun r => (η r : ℂ))
  have hre : Tendsto (fun N => ∫ u, Real.exp (∑ r, η r * u r) ∂(fluctuationLaw A νN CN N))
      atTop (𝓝 (L (fun r => (η r : ℂ))).re) := by
    have := (Complex.continuous_re.tendsto _).comp h
    refine this.congr (fun N => ?_)
    simp only [Function.comp]
    have : (fun u : Fin R → ℝ => cexp (∑ r, (η r : ℂ) * (u r : ℂ))) =
        fun u => ((Real.exp (∑ r, η r * u r) : ℝ) : ℂ) := by
      funext u; rw [Complex.ofReal_exp]; push_cast; rfl
    rw [this, integral_complex_ofReal, Complex.ofReal_re]
  refine ⟨(L (fun r => (η r : ℂ))).re + 1, ?_⟩
  exact hre.eventually (ge_mem_nhds (by linarith))

end children

end GLG


open MeasureTheory Filter Topology KellyStochasticNetworks.LossLimits in
theorem solution {J R : ℕ} (A : Fin J → Fin R → ℕ)
    (νN : ℕ → Fin R → ℝ) (CN : ℕ → Fin J → ℕ)
    (ν : Fin R → ℝ) (C : Fin J → ℝ)
    (hscale : Scaling A νN CN ν C) (hslack : strictSlack A ν C) (η : Fin R → ℝ) :
    (∀ N, 0 < N → Integrable (fun u : Fin R → ℝ => Real.exp (∑ r, η r * u r))
      (fluctuationLaw A νN CN N)) ∧
    ∃ M : ℝ, ∀ᶠ N in atTop,
      ∫ u, Real.exp (∑ r, η r * u r) ∂(fluctuationLaw A νN CN N) ≤ M :=
  GLG.childA A νN CN ν C hscale hslack η
