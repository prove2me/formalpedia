-- Prove2me | solution 1 for MasulloRH.rational_mesh_completes_unit_height_em_balls
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-27T02:56:38.858676+00:00
-- url     : https://prove2.me/submissions/24e00232-e2eb-4ea0-a9bc-7be346915af7

import Definitions.Def_MasulloRH_UnitHeightMeshes
import Theorems.Thm_MasulloRH_unit_height_zeta_right_rectangle_deriv_bound
import Theorems.Thm_MasulloRH_unit_height_em_enclosure
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.Convex
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

open Set MasulloRH.UnitHeightMeshes

private noncomputable def interp (a b : ℝ) (m i : ℕ) := a + (b-a)*((i:ℝ)/m)

private lemma coordinates (n k m i j : ℕ) :
    (rationalCenter (node n k m i j)).re = interp (1/2+margin k) 1 m i ∧
    (rationalCenter (node n k m i j)).im = interp (100000+n+margin k) (100000+n+1) m j := by
  simp only [rationalCenter, node, margin, interp, Rat.cast_add, Rat.cast_sub, Rat.cast_mul,
    Rat.cast_div, Rat.cast_one, Rat.cast_natCast, Rat.cast_ofNat]
  constructor <;> ring

private lemma margin_range (k : ℕ) : 0 < margin k ∧ margin k < 1/2 := by
  unfold margin
  constructor
  · positivity
  · rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
    linarith [Nat.cast_nonneg (α:=ℝ) k]

private lemma interp_mem {a b : ℝ} (h : a ≤ b) {m i : ℕ} (hm : 0 < m) (hi : i ≤ m) :
    interp a b m i ∈ Icc a b := by
  have pos : 0 < (m:ℝ) := by exact_mod_cast hm
  have lo : 0 ≤ (i:ℝ)/m := by positivity
  have hi' : (i:ℝ)/m ≤ 1 := (div_le_one pos).2 (by exact_mod_cast hi)
  unfold interp
  exact ⟨by linarith [mul_nonneg (sub_nonneg.mpr h) lo],
    by nlinarith [mul_nonneg (sub_nonneg.mpr h) (sub_nonneg.mpr hi')]⟩

private lemma node_mem (n k m i j : ℕ) (hm : 0 < m) (hi : i ≤ m) (hj : j ≤ m) :
    rationalCenter (node n k m i j) ∈ rect n k := by
  obtain ⟨h0,h1⟩ := margin_range k
  obtain ⟨hx,hy⟩ := coordinates n k m i j
  change (rationalCenter _).re ∈ Icc _ _ ∧ (rationalCenter _).im ∈ Icc _ _
  rw [hx, hy]
  exact ⟨interp_mem (by linarith) hm hi, interp_mem (by linarith) hm hj⟩

private lemma lower_nearest {a b x : ℝ} (hab : a < b) (hx : x ∈ Icc a b)
    {m : ℕ} (hm : 0 < m) : ∃ i ≤ m, interp a b m i ≤ x ∧
      |x - interp a b m i| ≤ (b-a)/m := by
  let u := (x-a)/(b-a)
  have hd := sub_pos.mpr hab
  have hpos : 0 < (m:ℝ) := by exact_mod_cast hm
  have ulo : 0 ≤ u := div_nonneg (sub_nonneg.mpr hx.1) hd.le
  have uhi : u ≤ 1 := (div_le_one hd).2 (by linarith [hx.2])
  have ex : x-a = (b-a)*u := by dsimp [u]; field_simp
  let i := ⌊u*(m:ℝ)⌋₊
  have lo : (i:ℝ) ≤ u*m := Nat.floor_le (mul_nonneg ulo hpos.le)
  have hi : u*m < (i:ℝ)+1 := Nat.lt_floor_add_one _
  have im : i ≤ m := by exact_mod_cast lo.trans (by nlinarith : u*m ≤ (m:ℝ))
  have low : (i:ℝ)/m ≤ u := (div_le_iff₀ hpos).2 lo
  have high : u - (i:ℝ)/m ≤ 1/m := by
    apply (le_div_iff₀ hpos).2
    rw [sub_mul,div_mul_cancel₀ _ hpos.ne']
    linarith
  have xp : x - interp a b m i = (b-a)*(u - (i:ℝ)/m) := by unfold interp; linarith [ex, mul_sub (b-a) u ((i:ℝ)/m)]
  have xl : 0 ≤ x - interp a b m i := xp ▸ mul_nonneg hd.le (sub_nonneg.mpr low)
  refine ⟨i,im,sub_nonneg.mp xl,?_⟩
  rw [abs_of_nonneg xl,xp]
  simpa only [one_div,div_eq_mul_inv,one_mul] using mul_le_mul_of_nonneg_left high hd.le

private lemma nearest (n k m : ℕ) (hm : 0 < m) (s : ℂ) (hs : s ∈ rect n k) :
    ∃ i ≤ m, ∃ j ≤ m, (rationalCenter (node n k m i j)).re ≤ s.re ∧
      dist s (rationalCenter (node n k m i j)) < (rad m:ℝ) := by
  obtain ⟨h0,h1⟩ := margin_range k
  obtain ⟨i,hi,hl,dx⟩ := lower_nearest (by linarith : 1/2+margin k < 1) hs.1 hm
  obtain ⟨j,hj,_,dy⟩ := lower_nearest (by linarith : (100000:ℝ)+n+margin k < 100000+n+1) hs.2 hm
  obtain ⟨ex,ey⟩ := coordinates n k m i j
  refine ⟨i,hi,j,hj,ex.trans_le hl,?_⟩
  rw [dist_eq_norm]
  apply (Complex.norm_le_abs_re_add_abs_im _).trans_lt
  simp only [Complex.sub_re,Complex.sub_im,ex,ey]
  refine (add_le_add dx dy).trans_lt ?_
  rw [← add_div]
  simp only [rad,Rat.cast_div,Rat.cast_ofNat,Rat.cast_natCast]
  apply div_lt_div_of_pos_right _ (by exact_mod_cast hm)
  linarith

private lemma variation (n k : ℕ) (s c : ℂ) (hs : s ∈ rect n k) (hc : c ∈ rect n k) :
    ‖riemannZeta s - riemannZeta c‖ ≤ (derivBudget n:ℝ)*dist s c := by
  have cv : Convex ℝ (rect n k) :=
    ((convex_Icc _ _).linear_preimage Complex.reLm).inter ((convex_Icc _ _).linear_preimage Complex.imLm)
  have diff (z : ℂ) (hz : z ∈ rect n k) : DifferentiableAt ℂ riemannZeta z := by
    apply differentiableAt_riemannZeta
    intro e
    have qq := hz.2.1
    rw [e, Complex.one_im] at qq
    linarith [(margin_range k).1, Nat.cast_nonneg (α:=ℝ) n]
  have der (z : ℂ) (hz : z ∈ rect n k) : ‖deriv riemannZeta z‖ ≤ (derivBudget n:ℝ) := by
    simpa [derivBudget] using MasulloRH.unit_height_zeta_right_rectangle_deriv_bound n k z hz
  simpa only [dist_eq_norm] using cv.norm_image_sub_le_of_norm_deriv_le diff der hc hs

private lemma sound (n k : ℕ) (s : ℂ) (hs : s ∈ rect n k) (h : covered n k s) : riemannZeta s ≠ 0 := by
  obtain ⟨p,r,⟨hc,K,N,hK,hN,strict⟩,near⟩ := h
  have err := MasulloRH.unit_height_em_enclosure n k K N hK hN (rationalCenter p) hc
  change ‖riemannZeta (rationalCenter p) - _‖ ≤ (emError n K N:ℝ) at err
  have var := variation n k s (rationalCenter p) hs hc
  have sl : 0 ≤ (derivBudget n:ℝ) := by simp [derivBudget]; positivity
  have bound := mul_le_mul_of_nonneg_left near.le sl
  intro zero
  rw [zero,zero_sub,norm_neg] at var
  have main := norm_add_le (ZetaReflection.EMHigh.emFinite K (rationalCenter p) N - riemannZeta (rationalCenter p)) (riemannZeta (rationalCenter p))
  rw [sub_add_cancel,norm_sub_rev] at main
  push_cast at strict
  linarith

theorem solution :
    (∀ n k m i j : ℕ, 0 < m → i ≤ m → j ≤ m → rationalCenter (node n k m i j) ∈ rect n k) ∧
    (∀ n k m : ℕ, 0 < m → ∀ s ∈ rect n k, ∃ i ≤ m, ∃ j ≤ m,
      (rationalCenter (node n k m i j)).re ≤ s.re ∧ dist s (rationalCenter (node n k m i j)) < (rad m:ℝ)) ∧
    (∀ n k : ℕ, ∀ s ∈ rect n k, ∀ c ∈ rect n k,
      ‖riemannZeta s-riemannZeta c‖ ≤ (derivBudget n:ℝ)*dist s c) ∧
    (∀ n k : ℕ, ∀ s ∈ rect n k, covered n k s → riemannZeta s ≠ 0) := by
  exact ⟨node_mem,nearest,fun n k s hs c hc => variation n k s c hs hc,sound⟩
