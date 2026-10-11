-- Prove2me | solution 1 for GravityNonRenorm.ads_entropy_not_cft
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-10-10T13:03:55.356339+00:00
-- url     : https://prove2.me/submissions/22586f3d-10b4-4f6a-baf2-815f7e114a48

import Definitions.Def_GravityNonRenorm_Defs
import Mathlib

open GravityNonRenorm Filter Asymptotics

namespace GravityNonRenorm

theorem anc_sphereArea_pos (k : ℕ) : 0 < sphereArea k := by
  unfold sphereArea
  have : 0 < Real.Gamma (((k : ℝ) + 1) / 2) := Real.Gamma_pos_of_pos (by positivity)
  positivity

/-- For `r > 0`, `f(r) = 0` iff `r^n + r^(n+2)/R² = c`. -/
theorem anc_iff (n : ℕ) (R c r : ℝ) (hR : 0 < R) (hr : 0 < r) :
    1 - c / r ^ n + r ^ 2 / R ^ 2 = 0 ↔ r ^ n + r ^ (n + 2) / R ^ 2 = c := by
  have hrn : 0 < r ^ n := pow_pos hr n
  have h : 1 - c / r ^ n + r ^ 2 / R ^ 2 = (r ^ n + r ^ (n + 2) / R ^ 2 - c) / r ^ n := by
    field_simp
    ring
  rw [h, div_eq_zero_iff, sub_eq_zero]
  simp [hrn.ne']

/-- The positive-root set of the AdS metric function is a singleton `{r0}`, with
`R² c ≤ 2 r0^(n+2) ≤ 2 R² c`, as soon as `c ≥ 2` and `c ≥ 2 R^n`. -/
theorem anc_key (n : ℕ) (R c : ℝ) (hR : 0 < R) (hc2 : 2 ≤ c) (hcR : 2 * R ^ n ≤ c) :
    ∃ r0 : ℝ, 0 < r0 ∧
      {r : ℝ | 0 < r ∧ 1 - c / r ^ n + r ^ 2 / R ^ 2 = 0} = {r0} ∧
      R ^ 2 * c ≤ 2 * r0 ^ (n + 2) ∧ r0 ^ (n + 2) ≤ R ^ 2 * c := by
  set g : ℝ → ℝ := fun r => r ^ n + r ^ (n + 2) / R ^ 2 with hg
  have hR2 : 0 < R ^ 2 := by positivity
  -- existence via IVT on `[0, b]`
  set b : ℝ := max 1 (R ^ 2 * c) with hb
  have hb1 : 1 ≤ b := le_max_left _ _
  have hb0 : (0 : ℝ) ≤ b := by linarith
  have hg0 : g 0 ≤ c := by
    have : (0 : ℝ) ^ n ≤ 1 := pow_le_one₀ le_rfl zero_le_one
    simp only [hg]
    have : (0 : ℝ) ^ (n + 2) = 0 := by simp
    rw [this]; simp; linarith
  have hgb : c ≤ g b := by
    have h1 : b ≤ b ^ (n + 2) := le_self_pow₀ hb1 (by omega)
    have h2 : R ^ 2 * c ≤ b := le_max_right _ _
    have h3 : c ≤ b ^ (n + 2) / R ^ 2 := by
      rw [le_div_iff₀ hR2]; nlinarith
    have : 0 ≤ b ^ n := by positivity
    simp only [hg]; linarith
  have hcont : ContinuousOn g (Set.Icc 0 b) := by
    simp only [hg]; fun_prop
  obtain ⟨r0, ⟨hr0a, _⟩, hr0g⟩ := intermediate_value_Icc hb0 hcont ⟨hg0, hgb⟩
  have hr0pos : 0 < r0 := by
    rcases hr0a.lt_or_eq with h | h
    · exact h
    · exfalso
      subst h
      have : (0 : ℝ) ^ n ≤ 1 := pow_le_one₀ le_rfl zero_le_one
      have h2 : (0 : ℝ) ^ (n + 2) = 0 := by simp
      simp only [hg, h2] at hr0g
      simp at hr0g
      linarith
  -- strict monotonicity of `g` on `(0, ∞)`
  have hmono : ∀ r s : ℝ, 0 < r → r < s → g r < g s := by
    intro r s hr hrs
    have h1 : r ^ n ≤ s ^ n := pow_le_pow_left₀ hr.le hrs.le n
    have h2 : r ^ (n + 2) < s ^ (n + 2) := pow_lt_pow_left₀ hrs hr.le (by omega)
    have h3 : r ^ (n + 2) / R ^ 2 < s ^ (n + 2) / R ^ 2 := div_lt_div_of_pos_right h2 hR2
    simp only [hg]; linarith
  have hset : {r : ℝ | 0 < r ∧ 1 - c / r ^ n + r ^ 2 / R ^ 2 = 0} = {r0} := by
    ext r
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hr, hf⟩
      have hgr : g r = c := (anc_iff n R c r hR hr).1 hf
      rcases lt_trichotomy r r0 with h | h | h
      · have := hmono r r0 hr h; linarith
      · exact h
      · have := hmono r0 r hr0pos h; linarith
    · rintro rfl
      exact ⟨hr0pos, (anc_iff n R c r hR hr0pos).2 hr0g⟩
  have heq : R ^ 2 * r0 ^ n + r0 ^ (n + 2) = R ^ 2 * c := by
    rw [← hr0g]; simp only [hg]; field_simp
  have hrn0 : 0 ≤ r0 ^ n := by positivity
  refine ⟨r0, hr0pos, hset, ?_, by nlinarith⟩
  have hRr : R ≤ r0 := by
    by_contra hlt
    push Not at hlt
    have h1 : r0 ^ n ≤ R ^ n := pow_le_pow_left₀ hr0pos.le hlt.le n
    have h2 : r0 ^ (n + 2) < R ^ (n + 2) := pow_lt_pow_left₀ hlt hr0pos.le (by omega)
    have h3 : R ^ (n + 2) = R ^ 2 * R ^ n := by ring
    nlinarith
  have h4 : R ^ 2 ≤ r0 ^ 2 := pow_le_pow_left₀ hR.le hRr 2
  have h5 : R ^ 2 * r0 ^ n ≤ r0 ^ 2 * r0 ^ n := mul_le_mul_of_nonneg_right h4 hrn0
  have h6 : r0 ^ (n + 2) = r0 ^ 2 * r0 ^ n := by ring
  nlinarith

theorem anc_main' (d : ℕ) (hd : 3 ≤ d) (G RAdS : ℝ) (hG : 0 < G) (hRAdS : 0 < RAdS) :
    (fun M : ℝ => adsBHEntropy d G M RAdS) =Θ[atTop]
      (fun M : ℝ => M ^ (((d : ℝ) - 2) / ((d : ℝ) - 1))) := by
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 3 := ⟨d - 3, by omega⟩
  have e2 : n + 3 - 2 = n + 1 := by omega
  have e3 : n + 3 - 3 = n := by omega
  have hexp : (((n + 3 : ℕ) : ℝ) - 2) / (((n + 3 : ℕ) : ℝ) - 1) = ((n : ℝ) + 1) / ((n : ℝ) + 2) := by
    push_cast; congr 1 <;> ring
  rw [hexp]
  set p : ℝ := ((n : ℝ) + 1) / ((n : ℝ) + 2) with hp
  have hp0 : 0 ≤ p := by positivity
  have hω : 0 < omega (n + 1) := by
    unfold omega
    have := anc_sphereArea_pos (n + 1)
    have : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    positivity
  set α : ℝ := omega (n + 1) * G with hα
  have hα0 : 0 < α := by positivity
  set K : ℝ := sphereArea (n + 1) / (4 * G) with hK
  have hK0 : 0 < K := by have := anc_sphereArea_pos (n + 1); positivity
  set R := RAdS
  have hR2 : 0 < R ^ 2 := by positivity
  set B1 : ℝ := (R ^ 2 * α) ^ p with hB1
  set B2 : ℝ := (R ^ 2 * α / 2) ^ p with hB2
  have hB2pos : 0 < B2 := by positivity
  -- `r^(n+1) = (r^(n+2))^p`
  have hpow : ∀ r : ℝ, 0 ≤ r → r ^ (n + 1) = (r ^ (n + 2)) ^ p := by
    intro r hr
    rw [← Real.rpow_natCast r (n + 2), ← Real.rpow_mul hr, ← Real.rpow_natCast r (n + 1)]
    congr 1
    rw [hp]; push_cast; field_simp
  have htend : Tendsto (fun M : ℝ => α * M) atTop atTop :=
    Tendsto.const_mul_atTop hα0 tendsto_id
  -- two-sided bounds, eventually
  have hbounds : ∀ᶠ M : ℝ in atTop, 0 < M ∧
      K * B2 * M ^ p ≤ adsBHEntropy (n + 3) G M R ∧
      adsBHEntropy (n + 3) G M R ≤ K * B1 * M ^ p := by
    filter_upwards [eventually_gt_atTop 0, htend.eventually_ge_atTop 2,
      htend.eventually_ge_atTop (2 * R ^ n)] with M hM h2 hRn
    obtain ⟨r0, hr0, hset, hlo, hhi⟩ := anc_key n R (α * M) hRAdS h2 hRn
    have hS : adsBHEntropy (n + 3) G M R = K * r0 ^ (n + 1) := by
      have hset' : {r : ℝ | 0 < r ∧ adsSchwarzschildF (n + 3) G M R r = 0} = {r0} := by
        rw [← hset]
        simp only [adsSchwarzschildF, e2, e3, hα]
      simp only [adsBHEntropy, adsHorizonRadius, bekensteinHawkingEntropy, e2, hset',
        csSup_singleton, hK]
      ring
    have hMp : 0 ≤ M ^ p := by positivity
    have hr0p := hpow r0 hr0.le
    refine ⟨hM, ?_, ?_⟩
    · rw [hS, hr0p, mul_assoc]
      apply mul_le_mul_of_nonneg_left _ hK0.le
      rw [hB2, ← Real.mul_rpow (by positivity) hM.le]
      apply Real.rpow_le_rpow (by positivity) _ hp0
      nlinarith
    · rw [hS, hr0p, mul_assoc]
      apply mul_le_mul_of_nonneg_left _ hK0.le
      rw [hB1, ← Real.mul_rpow (by positivity) hM.le]
      apply Real.rpow_le_rpow (by positivity) _ hp0
      nlinarith
  refine ⟨IsBigO.of_bound (K * B1) ?_, IsBigO.of_bound (K * B2)⁻¹ ?_⟩
  · filter_upwards [hbounds] with M ⟨hM, hlo, hhi⟩
    have hMp : 0 ≤ M ^ p := by positivity
    have hS0 : 0 ≤ adsBHEntropy (n + 3) G M R := le_trans (by positivity) hlo
    rw [Real.norm_of_nonneg hS0, Real.norm_of_nonneg hMp]
    exact hhi
  · filter_upwards [hbounds] with M ⟨hM, hlo, hhi⟩
    have hMp : 0 ≤ M ^ p := by positivity
    have hS0 : 0 ≤ adsBHEntropy (n + 3) G M R := le_trans (by positivity) hlo
    rw [Real.norm_of_nonneg hS0, Real.norm_of_nonneg hMp, inv_mul_eq_div,
      le_div_iff₀ (by positivity)]
    linarith [mul_comm (K * B2) (M ^ p)]

theorem anc_cft (d : ℕ) (hd : 2 ≤ d) (a b R : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hR : 0 < R) :
    (fun E : ℝ => cftEntropyOfEnergy d a b R E) =Θ[atTop]
      (fun E : ℝ => E ^ (((d : ℝ) - 1) / d)) := by
  set c : ℝ := b * R ^ (d - 1) with hc_def
  have hc : 0 < c := by positivity
  set x : ℝ := ((d : ℝ) - 1) / d with hx_def
  set K : ℝ := a * R ^ (d - 1) / c ^ x with hK_def
  have hK : K ≠ 0 := by
    have : 0 < c ^ x := Real.rpow_pos_of_pos hc x
    positivity
  have hexp : (1 / (d : ℝ)) * ((d - 1 : ℕ) : ℝ) = x := by
    rw [hx_def, Nat.cast_sub (by omega : 1 ≤ d)]
    push_cast
    ring
  have heq : (fun E : ℝ => cftEntropyOfEnergy d a b R E) =ᶠ[atTop]
      (fun E : ℝ => K * E ^ x) := by
    filter_upwards [eventually_gt_atTop 0] with E hE
    unfold cftEntropyOfEnergy
    rw [← hc_def, mul_pow, ← Real.rpow_mul_natCast (div_nonneg hE.le hc.le), hexp,
      Real.div_rpow hE.le hc.le, hK_def]
    field_simp
  exact heq.trans_isTheta ((isTheta_const_mul_left hK).2 (isTheta_refl _ _))

theorem anc_exp_lt (d : ℕ) (hd : 3 ≤ d) :
    ((d : ℝ) - 2) / ((d : ℝ) - 1) < ((d : ℝ) - 1) / d := by
  have h3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
  rw [div_lt_div_iff₀ (by linarith) (by linarith)]
  nlinarith

theorem anc_main (d : ℕ) (hd : 3 ≤ d) (G RAdS a b R : ℝ) (hG : 0 < G)
    (hRAdS : 0 < RAdS) (ha : 0 < a) (hb : 0 < b) (hR : 0 < R) :
    ¬ (fun M : ℝ => adsBHEntropy d G M RAdS) =Θ[atTop]
      (fun E : ℝ => cftEntropyOfEnergy d a b R E) := by
  intro h
  have h1 := anc_main' d hd G RAdS hG hRAdS
  have h2 := anc_cft d (by omega) a b R ha hb hR
  have h3 := (h1.symm.trans h).trans h2
  have hlt := anc_exp_lt d hd
  set p : ℝ := ((d : ℝ) - 2) / ((d : ℝ) - 1)
  set q : ℝ := ((d : ℝ) - 1) / d
  obtain ⟨C, hC⟩ := h3.2.bound
  have hT : Tendsto (fun x : ℝ => x ^ (q - p)) atTop atTop :=
    tendsto_rpow_atTop (sub_pos.2 hlt)
  obtain ⟨x, ⟨hx0, hxC⟩, hxb⟩ := (((eventually_gt_atTop 0).and
    (hT.eventually_gt_atTop C)).and hC).exists
  have hxp : 0 < x ^ p := Real.rpow_pos_of_pos hx0 _
  have hxq : 0 < x ^ q := Real.rpow_pos_of_pos hx0 _
  rw [Real.norm_of_nonneg hxq.le, Real.norm_of_nonneg hxp.le] at hxb
  have hsplit : x ^ q = x ^ (q - p) * x ^ p := by
    rw [← Real.rpow_add hx0]; ring_nf
  rw [hsplit] at hxb
  have : x ^ (q - p) ≤ C := le_of_mul_le_mul_right hxb hxp
  linarith

end GravityNonRenorm

theorem solution (d : ℕ) (hd : 3 ≤ d) (G RAdS a b R : ℝ) (hG : 0 < G)
    (hRAdS : 0 < RAdS) (ha : 0 < a) (hb : 0 < b) (hR : 0 < R) :
    ¬ (fun M : ℝ => GravityNonRenorm.adsBHEntropy d G M RAdS) =Θ[atTop]
      (fun E : ℝ => GravityNonRenorm.cftEntropyOfEnergy d a b R E) :=
  GravityNonRenorm.anc_main d hd G RAdS a b R hG hRAdS ha hb hR
