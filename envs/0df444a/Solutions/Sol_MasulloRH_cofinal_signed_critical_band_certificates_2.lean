-- Prove2me | solution 2 for MasulloRH.cofinal_signed_critical_band_certificates
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:34:12.104864+00:00
-- url     : https://prove2.me/submissions/6c9efc1c-225d-4326-9469-d669bbd92ab2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_mathlib_riemannHypothesis
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Definitions.Def_MasulloRH_RegularizedTrace
import Theorems.Thm_riemannZeta_conj
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.Convex
import Mathlib.Data.Set.Card
import Mathlib.NumberTheory.LSeries.ZetaZeros
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Theorems.Thm_MasulloRH_critical_zero_band_of_signed_brackets
import Theorems.Thm_MasulloRH_weighted_zero_summability

-- Step 1: `mathlib_riemannHypothesis` implies `MasulloRH.zero_free_right` (accepted reduction of `MasulloRH.zero_free_right`).
section

theorem MasulloRH.zero_free_right (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hs_one : s ≠ 1) :
    riemannZeta s ≠ 0 := by
  intro hz
  have htriv : ¬∃ n : ℕ, s = -2 * ((n : ℂ) + 1) := by
    rintro ⟨n, hn⟩
    have hre := congrArg Complex.re hn
    simp at hre
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hhalf := mathlib_riemannHypothesis s hz htriv hs_one
  linarith

end

-- Step 2: `MasulloRH.zero_free_right` implies `MasulloRH.unit_height_zeta_right_rectangle_mesh_certificates` (accepted reduction of `MasulloRH.unit_height_zeta_right_rectangle_mesh_certificates`).
section

set_option autoImplicit false

private theorem meshCoordinate_mem_Icc {a b : ℝ} (hab : a ≤ b) {m : ℕ}
    (hm : 0 < m) (i : Fin (m + 1)) :
    a + (b - a) * ((i.val : ℝ) / m) ∈ Set.Icc a b := by
  have hmReal : 0 < (m : ℝ) := by exact_mod_cast hm
  have hi : (i.val : ℝ) ≤ m := by exact_mod_cast Nat.lt_succ_iff.mp i.isLt
  have hfrac : (i.val : ℝ) / m ≤ 1 := (div_le_one hmReal).2 hi
  have hwidth : 0 ≤ b - a := sub_nonneg.mpr hab
  have hstep₀ := mul_nonneg hwidth (div_nonneg (Nat.cast_nonneg i.val) hmReal.le)
  have hstep₁ := mul_le_of_le_one_right hwidth hfrac
  exact ⟨by linarith only [hstep₀], by linarith only [hstep₁]⟩

theorem MasulloRH.unit_height_zeta_right_rectangle_mesh_certificates (n k : ℕ) :
    let margin : ℝ := 1 / ((k : ℝ) + 3)
    let left : ℝ := 1 / 2 + margin
    let bottom : ℝ := (100000 : ℝ) + n + margin
    let top : ℝ := (100000 : ℝ) + n + 1
    ∃ (m : ℕ) (M : ℚ), 0 < m ∧ 0 ≤ M ∧
      (∀ s ∈ Complex.reProdIm (Set.Icc left 1) (Set.Icc bottom top),
        ‖deriv riemannZeta s‖ ≤ (M : ℝ)) ∧
      ∀ i j : Fin (m + 1),
        let s : ℂ :=
          ⟨left + (1 - left) * ((i.val : ℝ) / m),
            bottom + (top - bottom) * ((j.val : ℝ) / m)⟩
        2 * (M : ℝ) / m < ‖riemannZeta s‖ := by
  intro margin left bottom top
  let R := Complex.reProdIm (Set.Icc left 1) (Set.Icc bottom top)
  have hmargin : 0 < margin := by dsimp [margin]; positivity
  have hmargin_le : margin ≤ 1 / 3 := by
    dsimp [margin]
    exact one_div_le_one_div_of_le (by norm_num) (le_add_of_nonneg_left (Nat.cast_nonneg k))
  have hleft : left ≤ 1 := by dsimp [left]; linarith only [hmargin_le]
  have hbottom : bottom ≤ top := by dsimp [bottom, top]; linarith only [hmargin_le]
  have hbottom_pos : 0 < bottom := by dsimp [bottom, margin]; positivity
  have hcompact : IsCompact R := isCompact_Icc.reProdIm isCompact_Icc
  have hnonempty : R.Nonempty :=
    ⟨⟨left, bottom⟩, Complex.mem_reProdIm.mpr ⟨⟨le_rfl, hleft⟩, ⟨le_rfl, hbottom⟩⟩⟩

  -- Both the zeta function and its derivative are continuous on the rectangle.
  have hpole {s : ℂ} (hs : s ∈ R) : s ≠ 1 := by
    intro h
    have him : bottom ≤ s.im := (Complex.mem_reProdIm.mp hs).2.1
    rw [h, Complex.one_im] at him
    exact (not_le_of_gt hbottom_pos) him
  have hanalytic : AnalyticOnNhd ℂ riemannZeta R :=
    analyticOn_riemannZeta.mono fun _ hs => hpole hs
  obtain ⟨smax, _, hmax⟩ := hcompact.exists_isMaxOn hnonempty
    hanalytic.deriv.continuousOn.norm
  obtain ⟨M, hM⟩ := exists_rat_gt ‖deriv riemannZeta smax‖
  have hMreal : 0 ≤ (M : ℝ) := (norm_nonneg _).trans hM.le
  have hMnonneg : 0 ≤ M := by exact_mod_cast hMreal

  -- The imported zero-free theorem gives a strictly positive compact minimum.
  obtain ⟨smin, hsmin, hmin⟩ := hcompact.exists_isMinOn hnonempty
    hanalytic.continuousOn.norm
  let δ := ‖riemannZeta smin‖
  have hδ : 0 < δ := by
    have hl : left ≤ smin.re := (Complex.mem_reProdIm.mp hsmin).1.1
    dsimp [left] at hl
    have hr : 1 / 2 < smin.re := by linarith only [hmargin, hl]
    exact norm_pos_iff.mpr (MasulloRH.zero_free_right smin hr (hpole hsmin))

  obtain ⟨m, hm⟩ := exists_nat_gt (max 0 (2 * (M : ℝ) / δ))
  have hmReal : 0 < (m : ℝ) := (le_max_left _ _).trans_lt hm
  have hmPos : 0 < m := by exact_mod_cast hmReal
  have hmesh : 2 * (M : ℝ) / m < δ := by
    have h := (div_lt_iff₀ hδ).1 ((le_max_right _ _).trans_lt hm)
    exact (div_lt_iff₀ hmReal).2 (by simpa only [mul_comm δ (m : ℝ)] using h)
  refine ⟨m, M, hmPos, hMnonneg, fun s hs => (hmax hs).trans hM.le, ?_⟩
  intro i j s
  have hs : s ∈ R := Complex.mem_reProdIm.mpr
    ⟨meshCoordinate_mem_Icc hleft hmPos i, meshCoordinate_mem_Icc hbottom hmPos j⟩
  exact hmesh.trans_le (hmin hs)

end

-- Step 3: `MasulloRH.unit_height_zeta_right_rectangle_mesh_certificates` implies `MasulloRH.unit_height_signed_critical_band_certificates` (accepted reduction of `MasulloRH.unit_height_signed_critical_band_certificates`).
section

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

theorem MasulloRH.unit_height_signed_critical_band_certificates (n : ℕ) :
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

end

-- Step 4: `MasulloRH.unit_height_signed_critical_band_certificates` implies `MasulloRH.cofinal_signed_critical_band_certificates` (accepted reduction of `MasulloRH.cofinal_signed_critical_band_certificates`).
section

open MasulloRH Set Finset Filter Topology

private theorem multiplicity_pos (ρ : ZetaZerosInTraceStrip (1/2)) :
    0 < analyticOrderNatAt riemannZeta ρ.val := by
  have h1 : ρ.val ≠ 1 := fun h => by
    have hr := congrArg Complex.re h
    simp only [Complex.one_re] at hr
    linarith [ρ.prop.2.2.1]
  have hA := analyticOn_riemannZeta
  have htwo : analyticOrderAt riemannZeta 2 = 0 :=
    analyticOrderAt_eq_zero.mpr (Or.inr (riemannZeta_ne_zero_of_one_lt_re (by norm_num)))
  have hfin := hA.analyticOrderAt_ne_top_of_isPreconnected
    (isConnected_compl_singleton_of_one_lt_rank (by simp) (1:ℂ)).isPreconnected
    (show (2:ℂ) ∈ ({1}:Set ℂ)ᶜ by norm_num) h1 (htwo ▸ ENat.zero_ne_top)
  apply Nat.pos_of_ne_zero
  unfold analyticOrderNatAt
  exact fun h => (ENat.toNat_eq_zero.mp h).elim
    ((hA _ h1).analyticOrderAt_ne_zero.mpr ρ.prop.1) hfin

private theorem finite_zeros_to_height (H : ℝ) (hH : 0 ≤ H) :
    {z : ZetaZerosInTraceStrip (1/2) | |z.val.im| ≤ H}.Finite := by
  let w := zeroDecayWeight (1/2)
  have hlim : Tendsto w cofinite (𝓝 0) := (weighted_zero_summability (1/2) (by norm_num)).tendsto_cofinite_zero
  have he := hlim.eventually (gt_mem_nhds (show (0:ℝ) < 1/(1+H^2) by positivity))
  have hbad : {z | ¬ w z < 1/(1+H^2)}.Finite := by
    simpa only [eventually_cofinite] using he
  apply hbad.subset
  intro z hz
  change |z.val.im| ≤ H at hz
  change ¬w z < 1/(1+H^2)
  apply not_lt.mpr
  have hysq : z.val.im^2 ≤ H^2 := by nlinarith [sq_abs z.val.im,mul_self_le_mul_self (abs_nonneg _) hz]
  have hm : (1:ℝ) ≤ analyticOrderNatAt riemannZeta z.val := by exact_mod_cast multiplicity_pos z
  exact (one_div_le_one_div_of_le (by positivity) (by linarith only [hysq])).trans
    (div_le_div_of_nonneg_right hm (by positivity))

private theorem positive_band_zero_on_line (z : ZetaZerosInTraceStrip (1/2))
    (hz : 100000 < z.val.im) : z.val.re = 1/2 := by
  let d : ℝ := z.val.im-100000
  have hd : 0 < d := by dsimp [d]; linarith
  let n : ℕ := Nat.ceil d - 1
  have hn : 1 ≤ Nat.ceil d := Nat.one_le_ceil_iff.mpr hd
  have hnlower : (n:ℝ) < d := Nat.add_one_le_ceil_iff.mp (by dsimp [n]; omega)
  have hncast : (n:ℝ)+1 = (Nat.ceil d : ℝ) := by
    exact_mod_cast (Nat.sub_add_cancel hn : (Nat.ceil d-1)+1=Nat.ceil d)
  have hnupper : d ≤ (n:ℝ)+1 := by rw [hncast]; exact Nat.le_ceil d
  obtain ⟨E,B,hE,hB,hD,hED,hcount⟩ := unit_height_signed_critical_band_certificates n
  have h := critical_zero_band_of_signed_brackets ((100000:ℝ)+n) ((100000:ℝ)+n+1)
    E B hE hB hD hED hcount
  apply h z
  · rw [abs_of_pos (by linarith : 0 < z.val.im)]
    dsimp [d] at hnlower
    linarith
  · rw [abs_of_pos (by linarith : 0 < z.val.im)]
    dsimp [d] at hnupper
    linarith

open Set Finset

theorem solution (T : ℕ) :
    ∃ H : ℕ, T ≤ H ∧ ∃ (E : Finset (ZetaZerosInTraceStrip (1/2))) (B : Finset (ℚ×ℚ)),
      (∀ z ∈ E, 100000 < z.val.im ∧ z.val.im ≤ (H:ℝ) ∧ z.val.re=1/2) ∧
      (∀ i ∈ B, 100000 ≤ (i.1:ℝ) ∧ i.1 < i.2 ∧ (i.2:ℝ) ≤ H ∧
        (completedRiemannZeta (1/2+(i.1:ℂ)*Complex.I)).re * (completedRiemannZeta (1/2+(i.2:ℂ)*Complex.I)).re < 0) ∧
      (∀ i ∈ B, ∀ j ∈ B, i ≠ j → Disjoint (Set.Ioo (i.1:ℝ) (i.2:ℝ)) (Set.Ioo (j.1:ℝ) (j.2:ℝ))) ∧
      (∀ z ∈ E, ∀ i ∈ B, z.val.im ∉ Set.Ioo (i.1:ℝ) (i.2:ℝ)) ∧
      Set.encard {z : ZetaZerosInTraceStrip (1/2) | 100000<z.val.im ∧ z.val.im ≤ H} ≤ ((E.card+B.card+1:ℕ):ℕ∞)  := by
  classical
  let H : ℕ := max T 100000
  let Z : Set (ZetaZerosInTraceStrip (1/2)) :=
    {z | 100000 < z.val.im ∧ z.val.im ≤ (H:ℝ)}
  have hfin : Z.Finite := (finite_zeros_to_height (H:ℝ) (Nat.cast_nonneg H)).subset (by
    intro z hz
    change 100000 < z.val.im ∧ z.val.im ≤ (H:ℝ) at hz
    change |z.val.im| ≤ (H:ℝ)
    rw [abs_of_pos (by linarith [hz.1] : 0 < z.val.im)]
    exact hz.2)
  let E := hfin.toFinset
  refine ⟨H, le_max_left _ _, E, ∅, ?_, by simp, by simp, by simp, ?_⟩
  · intro z hz
    have h : z ∈ Z := (hfin.mem_toFinset).mp hz
    exact ⟨h.1, h.2, positive_band_zero_on_line z h.1⟩
  · change Set.encard Z ≤ ((E.card + (∅ : Finset (ℚ×ℚ)).card + 1 : ℕ):ℕ∞)
    rw [hfin.encard_eq_coe_toFinset_card]
    simp only [Finset.card_empty, Nat.add_zero]
    exact_mod_cast (Nat.le_succ E.card)

end
