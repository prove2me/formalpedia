-- Prove2me | solution 1 for MasulloRH.unit_height_signed_critical_band_certificates
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @GeorgeCoote
-- created : 2026-11-21T18:13:29.281001+00:00
-- url     : https://prove2.me/submissions/9f5d1c02-3359-4a01-8771-e379192b301d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_MasulloRH_RegularizedTrace
import Theorems.Thm_MasulloRH_unit_height_zeta_right_rectangle_mesh_certificates
import Theorems.Thm_riemannZeta_conj
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.Convex
import Mathlib.Data.Set.Card
import Mathlib.NumberTheory.LSeries.ZetaZeros
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open MasulloRH
open scoped ComplexConjugate

set_option autoImplicit false

private theorem exists_subdivision_point {a b x : ℝ} {m : ℕ}
    (hm : 0 < m) (hab : a < b) (hwidth : b - a ≤ 1) (hx : x ∈ Set.Icc a b) :
    ∃ i : Fin (m + 1),
      let y := a + (b - a) * ((i.val : ℝ) / m)
      y ∈ Set.Icc a b ∧ |x - y| ≤ 1 / (m : ℝ) := by
  have hm' : 0 < (m : ℝ) := by exact_mod_cast hm
  have hw : 0 < b - a := sub_pos.mpr hab
  let t := (x - a) * (m : ℝ) / (b - a)
  have ht : 0 ≤ t := div_nonneg (mul_nonneg (sub_nonneg.mpr hx.1) hm'.le) hw.le
  have htm : t ≤ (m : ℝ) := (div_le_iff₀ hw).mpr (by
    rw [mul_comm (m : ℝ)]
    exact mul_le_mul_of_nonneg_right (sub_le_sub_right hx.2 a) hm'.le)
  let i := ⌊t⌋₊
  have hit : (i : ℝ) ≤ t := Nat.floor_le ht
  have hti : t ≤ (i : ℝ) + 1 := (Nat.lt_floor_add_one t).le
  have him : i ≤ m := by exact_mod_cast hit.trans htm
  refine ⟨⟨i, Nat.lt_succ_of_le him⟩, ?_⟩
  let y := a + (b - a) * ((i : ℝ) / m)
  have hstep : x - y = (b - a) * (t - (i : ℝ)) / m := by
    dsimp [y, t]
    field_simp [hw.ne', hm'.ne']
    ring
  have hyx : 0 ≤ x - y := by
    rw [hstep]
    exact div_nonneg (mul_nonneg hw.le (sub_nonneg.mpr hit)) hm'.le
  change y ∈ Set.Icc a b ∧ |x - y| ≤ _
  refine ⟨⟨le_add_of_nonneg_right (mul_nonneg hw.le (div_nonneg (Nat.cast_nonneg i) hm'.le)),
    (sub_nonneg.mp hyx).trans hx.2⟩, ?_⟩
  rw [abs_of_nonneg hyx, hstep]
  have hunit : t - (i : ℝ) ≤ 1 := by linarith only [hti]
  exact div_le_div_of_nonneg_right
    (by simpa using mul_le_mul hwidth hunit (sub_nonneg.mpr hit) zero_le_one) hm'.le

private theorem no_zero_right_of_line (n : ℕ) (s : ℂ)
    (hs : 1 / 2 < s.re) (hs₁ : s.re ≤ 1)
    (hL : (100000 : ℝ) + n < s.im) (hH : s.im ≤ (100000 : ℝ) + n + 1) :
    riemannZeta s ≠ 0 := by
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt
    (lt_min (sub_pos.mpr hs) (sub_pos.mpr hL) :
      0 < min (s.re - 1 / 2) (s.im - ((100000 : ℝ) + n)))
  let margin : ℝ := 1 / ((k : ℝ) + 3)
  let left : ℝ := 1 / 2 + margin
  let bottom : ℝ := (100000 : ℝ) + n + margin
  let top : ℝ := (100000 : ℝ) + n + 1
  have hmargin : 0 < margin := by dsimp [margin]; positivity
  have hsmall : margin ≤ 1 / 3 := by
    dsimp [margin]
    exact one_div_le_one_div_of_le (by norm_num) (le_add_of_nonneg_left (Nat.cast_nonneg k))
  have hclose : margin ≤ 1 / ((k : ℝ) + 1) := by
    dsimp [margin]
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  have hleft : left < 1 := by dsimp [left]; linarith
  have hbottom : bottom < top := by dsimp [bottom, top]; linarith
  have hwre : 1 - left ≤ 1 := by dsimp [left]; linarith
  have hwim : top - bottom ≤ 1 := by dsimp [top, bottom]; linarith
  have hsre : s.re ∈ Set.Icc left 1 :=
    ⟨by dsimp [left]; linarith [(hclose.trans_lt hk).trans_le (min_le_left _ _)], hs₁⟩
  have hsim : s.im ∈ Set.Icc bottom top :=
    ⟨by dsimp [bottom]; linarith [(hclose.trans_lt hk).trans_le (min_le_right _ _)], hH⟩
  obtain ⟨m, M, hm, hM, hderiv, hsamples⟩ := unit_height_zeta_right_rectangle_mesh_certificates n k
  obtain ⟨i, hi, hdist_re⟩ := exists_subdivision_point hm hleft hwre hsre
  obtain ⟨j, hj, hdist_im⟩ := exists_subdivision_point hm hbottom hwim hsim
  let q : ℂ := ⟨left + (1 - left) * ((i.val : ℝ) / m),
    bottom + (top - bottom) * ((j.val : ℝ) / m)⟩
  let R := Complex.reProdIm (Set.Icc left 1) (Set.Icc bottom top)
  have hsR : s ∈ R := Complex.mem_reProdIm.mpr ⟨hsre, hsim⟩
  have hqR : q ∈ R := Complex.mem_reProdIm.mpr ⟨hi, hj⟩
  have hconvex : Convex ℝ R := by
    change Convex ℝ ((Complex.reLm ⁻¹' Set.Icc left 1) ∩
      (Complex.imLm ⁻¹' Set.Icc bottom top))
    have hre : Convex ℝ (Set.Icc left 1) := convex_Icc _ _
    have him : Convex ℝ (Set.Icc bottom top) := convex_Icc _ _
    exact (hre.linear_preimage Complex.reLm).inter (him.linear_preimage Complex.imLm)
  have hdiff (z : ℂ) (hz : z ∈ R) : DifferentiableAt ℂ riemannZeta z := by
    apply differentiableAt_riemannZeta
    intro hz₁
    have hpos : 0 < bottom := by dsimp [bottom]; positivity
    have him := (Complex.mem_reProdIm.mp hz).2.1
    rw [hz₁, Complex.one_im] at him
    exact (not_le_of_gt hpos) him
  have hdist : ‖q - s‖ ≤ 2 / (m : ℝ) := by
    calc
      ‖q - s‖ ≤ |q.re - s.re| + |q.im - s.im| := Complex.norm_le_abs_re_add_abs_im _
      _ = |s.re - q.re| + |s.im - q.im| := by rw [abs_sub_comm q.re, abs_sub_comm q.im]
      _ ≤ 1 / (m : ℝ) + 1 / (m : ℝ) := add_le_add hdist_re hdist_im
      _ = 2 / (m : ℝ) := by ring
  intro hz
  have hval := hconvex.norm_image_sub_le_of_norm_deriv_le hdiff hderiv hsR hqR
  rw [hz, sub_zero] at hval
  have hM' : 0 ≤ (M : ℝ) := by exact_mod_cast hM
  have hbound := hval.trans (mul_le_mul_of_nonneg_left hdist hM')
  have hsample : 2 * (M : ℝ) / (m : ℝ) < ‖riemannZeta q‖ := hsamples i j
  rw [← mul_div_assoc, mul_comm (M : ℝ)] at hbound
  exact (not_lt_of_ge hbound) hsample

private theorem zero_on_line_in_band (n : ℕ) (z : ZetaZerosInTraceStrip (1 / 2))
    (hz : (100000 : ℝ) + n < z.val.im ∧ z.val.im ≤ (100000 : ℝ) + n + 1) :
    z.val.re = 1 / 2 := by
  apply le_antisymm
  · exact le_of_not_gt fun h =>
      no_zero_right_of_line n z.val h z.prop.2.2.1.le hz.1 hz.2 z.prop.1
  · apply le_of_not_gt
    intro h
    let w : ℂ := 1 - conj z.val
    have hwre : w.re = 1 - z.val.re := by simp [w]
    have hwim : w.im = z.val.im := by simp [w]
    have hnontrivial (j : ℕ) : conj z.val ≠ -(j : ℂ) := by
      intro hj
      have hr := congrArg Complex.re hj
      simp only [Complex.conj_re, Complex.neg_re, Complex.natCast_re] at hr
      linarith only [hr, z.prop.2.1, Nat.cast_nonneg (α := ℝ) j]
    have hpole : conj z.val ≠ 1 := by
      intro h₁
      have hr := congrArg Complex.re h₁
      simp only [Complex.conj_re, Complex.one_re] at hr
      linarith only [hr, z.prop.2.2.1]
    have hzero : riemannZeta w = 0 := by
      dsimp [w]
      rw [riemannZeta_one_sub hnontrivial hpole, riemannZeta_conj, z.prop.1, map_zero, mul_zero]
    exact no_zero_right_of_line n w (by linarith only [hwre, h])
      (by linarith only [hwre, z.prop.2.1]) (hwim.symm ▸ hz.1) (hwim.symm ▸ hz.2) hzero

private theorem finite_zeros_in_band (L H : ℝ) :
    {z : ZetaZerosInTraceStrip (1 / 2) | L < z.val.im ∧ z.val.im ≤ H}.Finite := by
  let R := Complex.reProdIm (Set.Icc (0 : ℝ) 1) (Set.Icc L H)
  have hR : IsCompact R := isCompact_Icc.reProdIm isCompact_Icc
  refine (hR.inter_riemannZetaZeros_finite.preimage Subtype.val_injective.injOn).subset ?_
  intro z hz
  exact ⟨Complex.mem_reProdIm.mpr ⟨⟨z.prop.2.1.le, z.prop.2.2.1.le⟩, ⟨hz.1.le, hz.2⟩⟩,
    mem_riemannZetaZeros.mpr z.prop.1⟩

theorem solution (n : ℕ) :
    ∃ (E : Finset (ZetaZerosInTraceStrip (1/2))) (B : Finset (ℚ×ℚ)),
      (∀ z ∈ E, (100000:ℝ)+n < z.val.im ∧ z.val.im ≤ (100000:ℝ)+n+1 ∧ z.val.re=1/2) ∧
      (∀ i ∈ B, (100000:ℝ)+n ≤ (i.1:ℝ) ∧ i.1 < i.2 ∧ (i.2:ℝ) ≤ (100000:ℝ)+n+1 ∧
        (completedRiemannZeta (1/2+(i.1:ℂ)*Complex.I)).re *
        (completedRiemannZeta (1/2+(i.2:ℂ)*Complex.I)).re < 0) ∧
      (∀ i ∈ B, ∀ j ∈ B, i ≠ j → Disjoint (Set.Ioo (i.1:ℝ) (i.2:ℝ)) (Set.Ioo (j.1:ℝ) (j.2:ℝ))) ∧
      (∀ z ∈ E, ∀ i ∈ B, z.val.im ∉ Set.Ioo (i.1:ℝ) (i.2:ℝ)) ∧
      Set.encard {z : ZetaZerosInTraceStrip (1/2) |
        (100000:ℝ)+n<z.val.im ∧ z.val.im ≤ (100000:ℝ)+n+1} ≤
          ((E.card+B.card+1:ℕ):ℕ∞) := by
  classical
  let Z : Set (ZetaZerosInTraceStrip (1 / 2)) :=
    {z | (100000 : ℝ) + n < z.val.im ∧ z.val.im ≤ (100000 : ℝ) + n + 1}
  have hfinite : Z.Finite := finite_zeros_in_band _ _
  let E := hfinite.toFinset
  refine ⟨E, ∅, ?_, by simp, by simp, by simp, ?_⟩
  · intro z hz
    have hzZ : z ∈ Z := hfinite.mem_toFinset.mp hz
    exact ⟨hzZ.1, hzZ.2, zero_on_line_in_band n z hzZ⟩
  · rw [hfinite.encard_eq_coe_toFinset_card]
    simp only [Finset.card_empty, Nat.add_zero]
    exact_mod_cast Nat.le_succ E.card
