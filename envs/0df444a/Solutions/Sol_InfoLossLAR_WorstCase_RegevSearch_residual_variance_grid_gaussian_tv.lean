-- Prove2me | solution 1 for InfoLossLAR.WorstCase.RegevSearch.residual_variance_grid_gaussian_tv
-- status  : ACCEPTED   (prove)
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-21T02:26:44.087179+00:00
-- url     : https://prove2.me/submissions/822d3e2f-3999-4159-899a-b4328f958b42

import Definitions.Def_InfoLossLAR_NativeSparsePrefix_01
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation

set_option autoImplicit false
open scoped BigOperators
namespace InfoLossLAR.WorstCase.RegevSearch
open AFT.GaussianSource

private theorem grid_weight_mono {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (z : ℤ) :
    weight a z ≤ weight b z := by
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonneg_right (neg_le_neg
    (div_le_div_of_nonneg_left Real.pi_pos.le (sq_pos_of_pos ha)
      ((sq_le_sq₀ ha.le (ha.trans_le hab).le).mpr hab))) (sq_nonneg _)

private theorem grid_theta_reciprocal (a : ℝ) (ha : 0 < a) :
    realNormalizer a = a * realNormalizer a⁻¹ := by
  have hp := Real.tsum_exp_neg_mul_int_sq (sq_pos_of_pos ha)
  rw [← Real.sqrt_eq_rpow, Real.sqrt_sq ha.le] at hp
  have hw (z : ℤ) : weight a⁻¹ z = Real.exp (-Real.pi * a ^ 2 * (z:ℝ)^2) := by
    unfold weight
    congr 1
    rw [inv_pow, div_inv_eq_mul]
    ring
  have he (z : ℤ) : weight a z = Real.exp (-Real.pi / a ^ 2 * (z:ℝ)^2) := by
    unfold weight
    rw [neg_div]
  unfold realNormalizer
  simp_rw [hw, he]
  rw [hp]
  field_simp

private theorem grid_tv_bound {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∑' z : ℤ, |weight a z / realNormalizer a - weight b z / realNormalizer b|)/2 ≤
      (b^2-a^2)/a^2 := by
  let Z := realNormalizer
  have hb := ha.trans_le hab
  have haZ : 0 < Z a := zero_lt_one.trans_le (realNormalizer_ge_one a ha)
  have hbZ : 0 < Z b := zero_lt_one.trans_le (realNormalizer_ge_one b hb)
  have hmono : Z a ≤ Z b := (summable_weight a ha).tsum_le_tsum
    (grid_weight_mono ha hab) (summable_weight b hb)
  have hdual : Z b⁻¹ ≤ Z a⁻¹ := (summable_weight b⁻¹ (inv_pos.mpr hb)).tsum_le_tsum
    (grid_weight_mono (inv_pos.mpr hb) (inv_anti₀ ha hab)) (summable_weight a⁻¹ (inv_pos.mpr ha))
  have hratio : Z b / Z a ≤ b / a := by
    apply (div_le_div_iff₀ haZ ha).mpr
    calc
      Z b * a = (b * Z b⁻¹) * a := by rw [show Z b = b * Z b⁻¹ from grid_theta_reciprocal b hb]
      _ ≤ (b * Z a⁻¹) * a := by gcongr
      _ = b * Z a := by rw [show Z a = a * Z a⁻¹ from grid_theta_reciprocal a ha]; ring
  let p := fun z => weight a z / Z a
  let t := fun z => weight b z / Z b
  let L := Z b / Z a
  have hL : 1 ≤ L := (one_le_div haZ).mpr hmono
  have hsump : Summable p := (summable_weight a ha).div_const _
  have hsumt : Summable t := (summable_weight b hb).div_const _
  have hmassp : ∑' z, p z = 1 := by rw [show (∑' z, p z) = Z a / Z a from tsum_div_const, div_self haZ.ne']
  have hmasst : ∑' z, t z = 1 := by rw [show (∑' z, t z) = Z b / Z b from tsum_div_const, div_self hbZ.ne']
  have hdom (z : ℤ) : p z ≤ L * t z := by
    calc
      p z ≤ weight b z / Z a := div_le_div_of_nonneg_right (grid_weight_mono ha hab z) haZ.le
      _ = L * t z := by dsimp [L,t]; field_simp
  have hpt (z : ℤ) : |p z - t z| ≤ (L-1) * t z + (L*t z-p z) := by
    have hpos : 0 ≤ t z := div_nonneg (weight_pos _ _).le hbZ.le
    exact abs_le.mpr ⟨by nlinarith [mul_nonneg (sub_nonneg.mpr hL) hpos], by linarith [hdom z]⟩
  have hadd := (hsumt.mul_left (L-1)).add ((hsumt.mul_left L).sub hsump)
  have hsum := (hsump.sub hsumt).norm.tsum_le_tsum (fun z => by simpa only [Real.norm_eq_abs] using hpt z) hadd
  simp only [Real.norm_eq_abs] at hsum
  rw [(hsumt.mul_left (L-1)).tsum_add ((hsumt.mul_left L).sub hsump),
    (hsumt.mul_left L).tsum_sub hsump, tsum_mul_left, tsum_mul_left, hmassp, hmasst] at hsum
  calc
    _ ≤ L-1 := by change (∑' z, |p z-t z|)/2 ≤ _; linarith
    _ ≤ b/a-1 := sub_le_sub_right hratio 1
    _ ≤ _ := by
      rw [div_sub_one ha.ne']
      rw [div_le_div_iff₀ ha (sq_pos_of_pos ha)]
      nlinarith [mul_nonneg (mul_nonneg ha.le (sub_nonneg.mpr hab)) hb.le]
end InfoLossLAR.WorstCase.RegevSearch

open InfoLossLAR.WorstCase.RegevSearch AFT.GaussianSource

theorem solution
    (s q M : ℕ) (hs : 2 ≤ s) (hq : 2 ≤ q) (hM : 0 < M)
    (E : ℝ) (hE : 0 ≤ E) (hcap : E ≤ (s : ℝ)^2 / 2) :
    ∃ i : Fin (M + 1), ∀ j : ℕ,
      let den : ℚ := (q : ℚ)^(2*j)
      let v : ℚ := (s : ℚ)^2 - ((s : ℚ)^2/2) * (i.val : ℚ) / M / den
      let total := E / (den : ℝ) + (v : ℝ)
      let mass := fun (width : ℝ) (z : ℤ) => AFT.GaussianSource.weight width z /
        AFT.GaussianSource.realNormalizer width
      (s : ℚ)^2/2 ≤ v ∧ v ≤ (s : ℚ)^2 ∧
      0 ≤ (s : ℝ)^2 - total ∧
      (s : ℝ)^2 - total ≤ (s : ℝ)^2 / (2 * M * (den : ℝ)) ∧
      (∑' z : ℤ, |mass (Real.sqrt total) z - mass (s : ℝ) z|)/2 ≤
        1 / ((M : ℝ) * (den : ℝ)) := by
  let H := (s:ℝ)^2/2
  have hsR : 0 < (s:ℝ) := by exact_mod_cast (show 0<s by omega)
  have hH : 0 < H := by dsimp [H]; positivity
  have hm : 0 < (M:ℝ) := by exact_mod_cast hM
  let a := E * M / H
  have ha : 0 ≤ a := div_nonneg (mul_nonneg hE hm.le) hH.le
  have haM : a ≤ M := by
    apply (div_le_iff₀ hH).mpr
    simpa [mul_comm] using mul_le_mul_of_nonneg_right hcap hm.le
  let i : Fin (M+1) := ⟨⌈a⌉₊, Nat.lt_succ_iff.mpr ((Nat.ceil_le).mpr haM)⟩
  have hi₁ : a ≤ (i.val:ℝ) := Nat.le_ceil _
  have hi₂ : (i.val:ℝ) < a+1 := Nat.ceil_lt_add_one ha
  let g := H * i.val / M
  have hEg : E ≤ g := by
    apply (le_div_iff₀ hm).mpr
    have := (div_le_iff₀ hH).mp hi₁
    linarith only [this]
  have hgap : g - E ≤ H/M := by
    apply (le_div_iff₀ hm).mpr
    have haux := mul_lt_mul_of_pos_right hi₂ hH
    dsimp only [a] at haux
    rw [add_mul,div_mul_cancel₀ _ hH.ne',one_mul] at haux
    dsimp only [g]
    rw [sub_mul,div_mul_cancel₀ _ hm.ne']
    linarith only [haux]
  have hiM : (i.val:ℝ) ≤ M := by exact_mod_cast (show i.val ≤ M by omega)
  have hgpos : 0 ≤ g := by dsimp [g]; positivity
  have hgcap : g ≤ H := by
    apply (div_le_iff₀ hm).mpr
    exact mul_le_mul_of_nonneg_left hiM hH.le
  refine ⟨i,fun j => ?_⟩
  dsimp only
  let d := (q:ℝ)^(2*j)
  have hqR : 1 ≤ (q:ℝ) := by exact_mod_cast (show 1≤q by omega)
  have hd : 1 ≤ d := one_le_pow₀ hqR
  have hdpos := zero_lt_one.trans_le hd
  let v := (s:ℝ)^2 - g/d
  let total := E/d + v
  have hsmall : g/d ≤ H := (div_le_self hgpos hd).trans hgcap
  have hvlo : H ≤ v := by dsimp only [v]; dsimp [H] at hsmall ⊢; linarith
  have hvhi : v ≤ (s:ℝ)^2 := sub_le_self _ (div_nonneg hgpos hdpos.le)
  have htotal : H ≤ total := hvlo.trans (le_add_of_nonneg_left (div_nonneg hE hdpos.le))
  have htotalpos := hH.trans_le htotal
  have hdiff : (s:ℝ)^2-total = (g-E)/d := by dsimp only [total,v]; ring
  have hdiffpos : 0 ≤ (s:ℝ)^2-total := by rw [hdiff]; positivity
  have hdiffle : (s:ℝ)^2-total ≤ H/(M*d) := by
    rw [hdiff,← div_div]; exact div_le_div_of_nonneg_right hgap hdpos.le
  have hroot := Real.sq_sqrt htotalpos.le
  have hroots : Real.sqrt total ≤ s := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) hsR.le).mp
    linarith only [hroot,hdiffpos]
  have htv := grid_tv_bound (Real.sqrt_pos.mpr htotalpos) hroots
  rw [hroot] at htv
  have hrel : ((s:ℝ)^2-total)/total ≤ 1/((M:ℝ)*d) := by
    apply (div_le_iff₀ htotalpos).mpr
    calc
      _ ≤ H/((M:ℝ)*d) := hdiffle
      _ ≤ total/((M:ℝ)*d) := div_le_div_of_nonneg_right htotal (mul_pos hm hdpos).le
      _ = _ := by ring
  have hc : (((s:ℚ)^2-((s:ℚ)^2/2)*(i.val:ℚ)/M/(q:ℚ)^(2*j):ℚ):ℝ) = v := by
    push_cast
    rfl
  have hcden : (((q:ℚ)^(2*j):ℚ):ℝ) = d := by push_cast; rfl
  rw [hcden,hc]
  constructor
  · apply (Rat.cast_le (K := ℝ)).mp
    push_cast
    exact hvlo
  constructor
  · apply (Rat.cast_le (K := ℝ)).mp
    push_cast
    exact hvhi
  refine ⟨hdiffpos,?_,htv.trans hrel⟩
  change (s:ℝ)^2-total ≤ _
  calc
    _ ≤ H/((M:ℝ)*d) := hdiffle
    _ = _ := by dsimp [H]; ring
