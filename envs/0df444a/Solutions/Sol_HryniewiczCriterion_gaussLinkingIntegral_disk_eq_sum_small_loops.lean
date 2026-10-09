-- Prove2me | solution 1 for HryniewiczCriterion.gaussLinkingIntegral_disk_eq_sum_small_loops
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-09T10:05:48.251852+00:00
-- url     : https://prove2.me/submissions/dbf71960-114b-4dcb-bf79-e97ef8091e6e

import Definitions.Def_HryniewiczCriterion_GlobalSection
import Definitions.Def_HryniewiczCriterion_SelfLinking
import Theorems.Thm_HryniewiczCriterion_exists_strip_center
import Theorems.Thm_HryniewiczCriterion_gaussLinkingIntegral_planar_homotopy
import Theorems.Thm_HryniewiczCriterion_gaussLinkingIntegral_strip_bump_jump
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

open HryniewiczCriterion
open Set Filter Topology

/-!
# Reduction of `gaussLinkingIntegral_disk_eq_sum_small_loops` (residue formula)

Strip coordinates `Ψ(μ, s) = c + μ (∂(s) - c)` from a centre `c` that sees the punctures on
distinct rays; graph loops `s ↦ Ψ(h(s), s)` with `h = η + (1 - η) Σ_{w ∈ S} β_w` built from disjoint
periodic bumps; raising the graph over one puncture at a time adds one small loop (bump-jump child).
-/


noncomputable section

namespace HryniewiczCriterion

/-! ### A periodic bump -/

/-- `= 1` at `s₀ + ℤ`, `= 0` unless `s` is within `δ` of `s₀ + ℤ`. -/
def res_bump (s₀ δ s : ℝ) : ℝ :=
  Real.smoothTransition ((Real.cos (2 * Real.pi * (s - s₀)) - Real.cos (2 * Real.pi * δ)) /
    (1 - Real.cos (2 * Real.pi * δ)))

lemma res_bump_contDiff (s₀ δ : ℝ) : ContDiff ℝ 2 (res_bump s₀ δ) := by
  unfold res_bump
  exact Real.smoothTransition.contDiff.comp (by fun_prop)

lemma res_bump_int (s₀ δ s : ℝ) (n : ℤ) : res_bump s₀ δ (s + n) = res_bump s₀ δ s := by
  simp only [res_bump]
  rw [show 2 * Real.pi * (s + n - s₀) = 2 * Real.pi * (s - s₀) + n * (2 * Real.pi) by ring,
    Real.cos_add_int_mul_two_pi]

lemma res_bump_periodic (s₀ δ s : ℝ) : res_bump s₀ δ (s + 1) = res_bump s₀ δ s := by
  have := res_bump_int s₀ δ s 1
  simpa using this

lemma res_bump_mem (s₀ δ s : ℝ) : 0 ≤ res_bump s₀ δ s ∧ res_bump s₀ δ s ≤ 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

lemma res_cos_lt_one {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 1 / 4) : Real.cos (2 * Real.pi * δ) < 1 := by
  have hp := Real.pi_pos
  have := Real.cos_lt_cos_of_nonneg_of_le_pi (x := 0) (y := 2 * Real.pi * δ) le_rfl
    (by nlinarith) (by positivity)
  simpa using this

lemma res_bump_center {s₀ δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 1 / 4) (n : ℤ) :
    res_bump s₀ δ (s₀ + n) = 1 := by
  rw [res_bump_int]
  apply Real.smoothTransition.one_of_one_le
  have h1 : (1 : ℝ) - Real.cos (2 * Real.pi * δ) ≠ 0 := by
    have := res_cos_lt_one hδ hδ'; linarith
  simp [h1]

lemma res_bump_supp {s₀ δ s : ℝ} (hδ : 0 < δ) (hδ' : δ < 1 / 4) (h : res_bump s₀ δ s ≠ 0) :
    ∃ n : ℤ, |s - s₀ - n| < δ := by
  by_contra hcon
  push_neg at hcon
  apply h
  have hp := Real.pi_pos
  set n := round (s - s₀)
  have hy := abs_sub_round (s - s₀)
  have hyδ : δ ≤ |s - s₀ - n| := hcon n
  apply Real.smoothTransition.zero_of_nonpos
  apply div_nonpos_of_nonpos_of_nonneg _ (by have := res_cos_lt_one hδ hδ'; linarith)
  have hc : Real.cos (2 * Real.pi * (s - s₀)) = Real.cos (2 * Real.pi * |s - s₀ - n|) := by
    rw [show 2 * Real.pi * (s - s₀) = 2 * Real.pi * (s - s₀ - n) + n * (2 * Real.pi) by ring,
      Real.cos_add_int_mul_two_pi]
    rcases le_total 0 (s - s₀ - n) with h0 | h0
    · rw [abs_of_nonneg h0]
    · rw [abs_of_nonpos h0, mul_neg, Real.cos_neg]
  rw [hc]
  have := Real.cos_le_cos_of_nonneg_of_le_pi (x := 2 * Real.pi * δ) (y := 2 * Real.pi * |s - s₀ - n|)
    (by positivity) (by nlinarith) (by nlinarith)
  linarith

/-! ### The circle and the disk -/

lemma res_cp_contDiff : ContDiff ℝ 2 circlePoint := by
  rw [contDiff_pi]
  intro i
  fin_cases i <;> simp [circlePoint] <;> fun_prop

lemma res_cp_periodic (s : ℝ) : circlePoint (s + 1) = circlePoint s := by
  ext i
  fin_cases i <;> simp [circlePoint, mul_add, Real.cos_add_two_pi, Real.sin_add_two_pi]

lemma res_cp_sq (s : ℝ) : circlePoint s 0 ^ 2 + circlePoint s 1 ^ 2 = 1 := by
  simp [circlePoint, Real.cos_sq_add_sin_sq]

lemma res_cp_norm_le (s : ℝ) : ‖circlePoint s‖ ≤ 1 := by
  refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_
  fin_cases i <;> simp [circlePoint, Real.abs_cos_le_one, Real.abs_sin_le_one]

lemma res_cp_ne_zero (s : ℝ) : circlePoint s ≠ 0 := by
  intro h
  have := res_cp_sq s
  rw [h] at this
  simp at this

lemma res_mem_disk {c : Plane} (hc : c ∈ openUnitDisk) {μ : ℝ} (h0 : 0 ≤ μ) (h1 : μ ≤ 1) (s : ℝ) :
    c + μ • (circlePoint s - c) ∈ closedUnitDisk := by
  have hc' : c 0 ^ 2 + c 1 ^ 2 < 1 := hc
  have hp := res_cp_sq s
  show (c + μ • (circlePoint s - c)) 0 ^ 2 + (c + μ • (circlePoint s - c)) 1 ^ 2 ≤ 1
  simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  set p0 := circlePoint s 0
  set p1 := circlePoint s 1
  have hm : 0 ≤ μ * (1 - μ) := mul_nonneg h0 (by linarith)
  have hm2 : 0 ≤ (1 - μ) ^ 2 := sq_nonneg _
  nlinarith [mul_nonneg hm (add_nonneg (sq_nonneg (c 0 - p0)) (sq_nonneg (c 1 - p1))),
    mul_nonneg hm2 (by linarith : (0 : ℝ) ≤ 1 - (c 0 ^ 2 + c 1 ^ 2)),
    mul_nonneg hm (by linarith : (0 : ℝ) ≤ 1 - (c 0 ^ 2 + c 1 ^ 2))]

lemma res_convex {r r' R τ : ℝ} (hr : 0 < r) (hr' : r < R) (hr2 : 0 < r') (hr2' : r' < R)
    (h0 : 0 ≤ τ) (h1 : τ ≤ 1) : 0 < (1 - τ) * r + τ * r' ∧ (1 - τ) * r + τ * r' < R := by
  rcases le_total r r' with h | h
  · constructor <;> nlinarith [mul_nonneg h0 (sub_nonneg.2 h), mul_le_mul_of_nonneg_right h1 (sub_nonneg.2 h)]
  · constructor <;> nlinarith [mul_nonneg h0 (sub_nonneg.2 h), mul_le_mul_of_nonneg_right h1 (sub_nonneg.2 h)]

/-! ### Graph heights -/

/-- `h_S = η + (1 - η) Σ_{w ∈ S} β_w`. -/
def res_h (η : ℝ) (β : Plane → ℝ → ℝ) (S : Finset Plane) (s : ℝ) : ℝ :=
  η + (1 - η) * ∑ w ∈ S, β w s

lemma res_gauss_const (N c : R4) (γ : ℝ → R4) : gaussLinkingIntegral N (fun _ => c) γ = 0 := by
  have h0 : ∀ b c' : R4, volumeIn N 0 b c' = 0 := fun b c' =>
    Matrix.det_eq_zero_of_row_eq_zero 1 (fun j => by simp)
  simp [gaussLinkingIntegral, h0]

theorem gaussLinkingIntegral_disk_eq_sum_small_loops' (E : Plane → R4) (U : Set Plane)
    (hU : IsOpen U) (hDU : closedUnitDisk ⊆ U)
    (hE : ContDiffOn ℝ 2 E U) (hEunit : ∀ v ∈ closedUnitDisk, euclidNorm (E v) = 1)
    (γ : ℝ → R4) (hγ : ContDiff ℝ 2 γ) (hγper : ∀ t, γ (t + 1) = γ t)
    (hγunit : ∀ t, euclidNorm (γ t) = 1)
    (Z : Finset Plane) (hZ : ∀ z ∈ Z, z ∈ openUnitDisk)
    (hmiss : ∀ v ∈ closedUnitDisk, v ∉ Z → ∀ t, E v ≠ γ t)
    (N : R4) (hN : euclidNorm N = 1) (hNγ : ∀ t, γ t ≠ N)
    (hNE : ∀ v ∈ closedUnitDisk, E v ≠ N) :
    ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ ρ : ℝ, 0 < ρ → ρ < ρ₀ →
      gaussLinkingIntegral N (fun s => E (circlePoint s)) γ =
        ∑ z ∈ Z, gaussLinkingIntegral N (fun s => E (z + ρ • circlePoint s)) γ := by
  classical
  obtain ⟨c, hc, lam, sp, hcz⟩ := exists_strip_center Z hZ
  set K : Set Plane := {v | v ∈ closedUnitDisk ∧ v ∉ Z} with hK
  have hHom : ∀ L : ℝ → ℝ → Plane, ContDiff ℝ 2 (Function.uncurry L) →
      (∀ τ s, L τ (s + 1) = L τ s) → (∀ τ ∈ Icc (0 : ℝ) 1, ∀ s, L τ s ∈ K) →
      gaussLinkingIntegral N (fun s => E (L 0 s)) γ =
        gaussLinkingIntegral N (fun s => E (L 1 s)) γ :=
    fun L hL hLper hLK => gaussLinkingIntegral_planar_homotopy E U hU K (fun v hv => hDU hv.1) hE
      (fun v hv => hEunit v hv.1) γ hγ hγper hγunit (fun v hv => hmiss v hv.1 hv.2) N hN hNγ
      (fun v hv => hNE v hv.1) L hL hLper hLK
  -- the base height `η`
  obtain ⟨η, ⟨hη0, hη1⟩, hηlam⟩ : ∃ η : ℝ, η ∈ Ioo 0 1 ∧ ∀ z ∈ Z, η ∈ Ioo 0 (lam z) :=
    (Filter.Eventually.and (Ioo_mem_nhdsGT one_pos)
      ((eventually_all_finset Z).2 fun z hz => Ioo_mem_nhdsGT (hcz z hz).1)).exists
  -- the bump width `δ`
  have hdpos : ∀ z ∈ Z, ∀ w ∈ Z, w ≠ z → 0 < |sp w - sp z - round (sp w - sp z)| := by
    intro z hz w hw hwz
    refine abs_pos.2 (sub_ne_zero.2 fun h => (hcz z hz).2.2.2.2 w hw hwz (round (sp w - sp z)) ?_)
    linarith
  obtain ⟨δ, ⟨hδ0, hδ1⟩, hδsep⟩ : ∃ δ : ℝ, δ ∈ Ioo 0 (1 / 4) ∧ ∀ z ∈ Z, ∀ w ∈ Z,
      w ≠ z → 2 * δ < |sp w - sp z - round (sp w - sp z)| := by
    refine (Filter.Eventually.and (Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 4))
      ((eventually_all_finset Z).2 fun z hz => (eventually_all_finset Z).2 fun w hw => ?_)).exists
    by_cases hwz : w = z
    · exact Filter.Eventually.of_forall fun _ h => absurd hwz h
    · filter_upwards [Ioo_mem_nhdsGT (half_pos (hdpos z hz w hw hwz))] with δ hδ _
      linarith [hδ.2]
  have hsep : ∀ z ∈ Z, ∀ w ∈ Z, w ≠ z → ∀ n : ℤ, 2 * δ < |sp w - sp z - n| :=
    fun z hz w hw hwz n => (hδsep z hz w hw hwz).trans_le (round_le _ n)
  set β : Plane → ℝ → ℝ := fun z => res_bump (sp z) δ with hβ
  have hβmem : ∀ z s, 0 ≤ β z s ∧ β z s ≤ 1 := fun z s => res_bump_mem _ _ _
  have hβdisj : ∀ z ∈ Z, ∀ w ∈ Z, w ≠ z → ∀ s, β z s ≠ 0 → β w s = 0 := by
    intro z hz w hw hwz s hzs
    by_contra hws
    obtain ⟨n, hn⟩ := res_bump_supp hδ0 hδ1 hzs
    obtain ⟨m, hm⟩ := res_bump_supp hδ0 hδ1 hws
    have := hsep z hz w hw hwz (n - m)
    push_cast at this
    have : |sp w - sp z - (n - m)| < 2 * δ := by
      calc |sp w - sp z - (n - m)| = |(s - sp z - n) - (s - sp w - m)| := by ring_nf
        _ ≤ |s - sp z - n| + |s - sp w - m| := abs_sub _ _
        _ < 2 * δ := by linarith
    linarith
  have hsum_mem : ∀ S ⊆ Z, ∀ s, 0 ≤ ∑ w ∈ S, β w s ∧ ∑ w ∈ S, β w s ≤ 1 := by
    intro S hS s
    refine ⟨Finset.sum_nonneg fun w _ => (hβmem w s).1, ?_⟩
    by_cases h : ∃ w ∈ S, β w s ≠ 0
    · obtain ⟨w, hwS, hw⟩ := h
      rw [Finset.sum_eq_single_of_mem w hwS fun b hb hbw =>
        hβdisj w (hS hwS) b (hS hb) hbw s hw]
      exact (hβmem w s).2
    · push_neg at h
      rw [Finset.sum_eq_zero h]
      norm_num
  have hβat : ∀ z ∈ Z, ∀ w ∈ Z, ∀ n : ℤ, β w (sp z + n) = if w = z then 1 else 0 := by
    intro z hz w hw n
    split_ifs with hwz
    · subst hwz; exact res_bump_center hδ0 hδ1 n
    · by_contra hne
      obtain ⟨m, hm⟩ := res_bump_supp hδ0 hδ1 hne
      have := hsep w hw z hz (Ne.symm hwz) (m - n)
      push_cast at this
      rw [show sp z - sp w - (m - n) = sp z + n - sp w - m by ring] at this
      linarith
  have hsum_at : ∀ S ⊆ Z, ∀ z ∈ Z, ∀ n : ℤ,
      ∑ w ∈ S, β w (sp z + n) = if z ∈ S then 1 else 0 := by
    intro S hS z hz n
    split_ifs with hzS
    · rw [Finset.sum_eq_single_of_mem z hzS fun b hb hbz => by rw [hβat z hz b (hS hb) n, if_neg hbz]]
      rw [hβat z hz z hz n, if_pos rfl]
    · exact Finset.sum_eq_zero fun b hb => by
        rw [hβat z hz b (hS hb) n, if_neg fun h => hzS (by rw [← h]; exact hb)]
  have hh_mem : ∀ S ⊆ Z, ∀ s, 0 ≤ res_h η β S s ∧ res_h η β S s ≤ 1 := by
    intro S hS s
    obtain ⟨h0, h1⟩ := hsum_mem S hS s
    have : 0 ≤ (1 - η) * ∑ w ∈ S, β w s := mul_nonneg (by linarith) h0
    have : (1 - η) * ∑ w ∈ S, β w s ≤ 1 - η := by nlinarith
    exact ⟨by unfold res_h; linarith, by unfold res_h; linarith⟩
  have hh_at : ∀ S ⊆ Z, ∀ z ∈ Z, ∀ n : ℤ, res_h η β S (sp z + n) = if z ∈ S then 1 else η := by
    intro S hS z hz n
    unfold res_h
    rw [hsum_at S hS z hz n]
    split_ifs <;> ring
  have hh_avoid : ∀ S ⊆ Z, ∀ s, c + res_h η β S s • (circlePoint s - c) ∉ Z := by
    intro S hS s hmem
    generalize hzv : c + res_h η β S s • (circlePoint s - c) = z at hmem
    obtain ⟨hl, n, hn⟩ := (hcz z hmem).2.2.2.1 _ s (hh_mem S hS s).1 hzv
    subst hn
    rw [hh_at S hS _ hmem n] at hl
    have h1 := (hcz _ hmem).2.1
    have h2 := (hηlam _ hmem).2
    split_ifs at hl <;> linarith
  have hh_contDiff : ∀ S : Finset Plane, ContDiff ℝ 2 (res_h η β S) := fun S =>
    contDiff_const.add (contDiff_const.mul (ContDiff.sum fun w _ => res_bump_contDiff _ _))
  have hh_per : ∀ S s, res_h η β S (s + 1) = res_h η β S s := by
    intro S s
    simp only [res_h, hβ, res_bump_periodic]
  have hstripK : ∀ μ s : ℝ, 0 ≤ μ → μ ≤ 1 → c + μ • (circlePoint s - c) ∉ Z →
      c + μ • (circlePoint s - c) ∈ K := fun μ s h0 h1 hZ' => show _ ∧ _ from ⟨res_mem_disk hc h0 h1 s, hZ'⟩
  have hLcontDiff : ∀ m : ℝ → ℝ → ℝ, ContDiff ℝ 2 (Function.uncurry m) →
      ContDiff ℝ 2 (Function.uncurry fun τ s => c + m τ s • (circlePoint s - c)) := by
    intro m hm
    exact contDiff_const.add (hm.smul ((res_cp_contDiff.comp contDiff_snd).sub contDiff_const))
  -- small radii
  have hrad_ev : ∀ z ∈ Z, ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ∀ v, v ≠ z → dist v z < ρ → v ∈ K := by
    intro z hz
    have hopen : IsOpen (openUnitDisk ∩ ((Z.erase z : Finset Plane) : Set Plane)ᶜ) :=
      (isOpen_lt (by fun_prop) continuous_const : IsOpen openUnitDisk).inter
        (Z.erase z).finite_toSet.isClosed.isOpen_compl
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hopen z ⟨hZ z hz, by simp⟩
    filter_upwards [Ioo_mem_nhdsGT hr] with ρ hρ v hvz hv
    have hvb := hball (Metric.mem_ball.2 (hv.trans hρ.2))
    refine ⟨show v 0 ^ 2 + v 1 ^ 2 ≤ 1 from le_of_lt hvb.1, fun hvZ => hvb.2 ?_⟩
    exact Finset.mem_coe.2 (Finset.mem_erase.2 ⟨hvz, hvZ⟩)
  obtain ⟨ρ₀, hρ₀, hρ₀K⟩ : ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ z ∈ Z, ∀ v, v ≠ z → dist v z < ρ₀ → v ∈ K := by
    obtain ⟨ρ, hρ, h⟩ := (Filter.Eventually.and (Ioo_mem_nhdsGT one_pos)
      ((eventually_all_finset Z).2 hrad_ev)).exists
    exact ⟨ρ, hρ.1, h⟩
  have hsmall : ∀ z ∈ Z, ∀ r, 0 < r → r < ρ₀ → ∀ s, z + r • circlePoint s ∈ K := by
    intro z hz r hr hr' s
    refine hρ₀K z hz _ ?_ ?_
    · intro h
      have : r • circlePoint s = 0 := by simpa using congrArg (· - z) h
      exact (smul_ne_zero hr.ne' (res_cp_ne_zero s)) this
    · rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hr.le]
      calc r * ‖circlePoint s‖ ≤ r * 1 := mul_le_mul_of_nonneg_left (res_cp_norm_le s) hr.le
        _ < ρ₀ := by linarith
  have hrad : ∀ z ∈ Z, ∀ r r', 0 < r → r < ρ₀ → 0 < r' → r' < ρ₀ →
      gaussLinkingIntegral N (fun s => E (z + r • circlePoint s)) γ =
        gaussLinkingIntegral N (fun s => E (z + r' • circlePoint s)) γ := by
    intro z hz r r' hr hr' hr2 hr2'
    have h := hHom (fun τ s => z + ((1 - τ) * r + τ * r') • circlePoint s)
      (contDiff_const.add ((by fun_prop : ContDiff ℝ 2 fun p : ℝ × ℝ => (1 - p.1) * r + p.1 * r').smul
        (res_cp_contDiff.comp contDiff_snd)))
      (fun τ s => by simp only [res_cp_periodic])
      (fun τ hτ s => hsmall z hz _ (res_convex hr hr' hr2 hr2' hτ.1 hτ.2).1
        (res_convex hr hr' hr2 hr2' hτ.1 hτ.2).2 s)
    simpa using h
  -- base: `h_∅ = η` is homotopic to the constant loop
  have hbase : gaussLinkingIntegral N (fun s => E (c + res_h η β ∅ s • (circlePoint s - c))) γ = 0 := by
    have h := hHom (fun τ s => c + (τ * η) • (circlePoint s - c))
      (hLcontDiff (fun τ _ => τ * η) (by fun_prop))
      (fun τ s => by simp only [res_cp_periodic])
      (fun τ hτ s => hstripK _ s (mul_nonneg hτ.1 hη0.le) (by nlinarith [hτ.1, hτ.2]) fun hmem => by
        have hl := ((hcz _ hmem).2.2.2.1 _ s (mul_nonneg hτ.1 hη0.le) rfl).1
        have := (hηlam _ hmem).2
        nlinarith [hτ.1, hτ.2])
    have hz0 : (fun s => E (c + ((0 : ℝ) * η) • (circlePoint s - c))) = fun _ => E c := by
      funext s; simp
    simp only [hz0, res_gauss_const] at h
    have he : (fun s => E (c + res_h η β ∅ s • (circlePoint s - c))) =
        fun s => E (c + ((1 : ℝ) * η) • (circlePoint s - c)) := by
      funext s; simp [res_h]
    rw [he, ← h]
  -- top: `h_Z` is homotopic to `h = 1`, the boundary loop
  have htop : gaussLinkingIntegral N (fun s => E (circlePoint s)) γ =
      gaussLinkingIntegral N (fun s => E (c + res_h η β Z s • (circlePoint s - c))) γ := by
    have h := hHom (fun τ s => c + ((1 - τ) * res_h η β Z s + τ) • (circlePoint s - c))
      (hLcontDiff (fun τ s => (1 - τ) * res_h η β Z s + τ)
        (((contDiff_const.sub contDiff_fst).mul ((hh_contDiff Z).comp contDiff_snd)).add contDiff_fst))
      (fun τ s => by simp only [hh_per, res_cp_periodic])
      (fun τ hτ s => by
        have hm := hh_mem Z subset_rfl s
        refine hstripK _ s (by nlinarith [hτ.1, hτ.2]) (by nlinarith [hτ.1, hτ.2]) fun hmem => ?_
        generalize hzv : c + ((1 - τ) * res_h η β Z s + τ) • (circlePoint s - c) = z at hmem
        obtain ⟨hl, n, hn⟩ := (hcz z hmem).2.2.2.1 _ s (by nlinarith [hτ.1, hτ.2]) hzv
        subst hn
        rw [hh_at Z subset_rfl _ hmem n, if_pos hmem] at hl
        have := (hcz _ hmem).2.1
        nlinarith)
    have h0 : (fun s => E (c + ((1 - (0 : ℝ)) * res_h η β Z s + 0) • (circlePoint s - c))) =
        fun s => E (c + res_h η β Z s • (circlePoint s - c)) := by
      funext s; simp
    have h1 : (fun s => E (c + ((1 - (1 : ℝ)) * res_h η β Z s + 1) • (circlePoint s - c))) =
        fun s => E (circlePoint s) := by
      funext s; simp
    simp only [h0, h1] at h
    exact h.symm
  -- telescoping over the punctures
  refine ⟨ρ₀, hρ₀, fun ρ hρ hρ' => ?_⟩
  have htel : ∀ S ⊆ Z,
      gaussLinkingIntegral N (fun s => E (c + res_h η β S s • (circlePoint s - c))) γ =
        ∑ z ∈ S, gaussLinkingIntegral N (fun s => E (z + ρ • circlePoint s)) γ := by
    intro S
    induction S using Finset.induction_on with
    | empty => intro _; rw [hbase, Finset.sum_empty]
    | insert a S haS ih =>
      intro hiZ
      have haZ : a ∈ Z := hiZ (Finset.mem_insert_self a S)
      have hSZ : S ⊆ Z := (Finset.insert_subset_iff.1 hiZ).2
      have hins : ∀ t, res_h η β (insert a S) t = res_h η β S t + (1 - η) * β a t := by
        intro t; simp only [res_h, Finset.sum_insert haS]; ring
      have ha0 := hh_at S hSZ a haZ 0
      have ha1 := hh_at (insert a S) hiZ a haZ 0
      rw [if_neg haS] at ha0
      rw [if_pos (Finset.mem_insert_self a S)] at ha1
      simp only [Int.cast_zero, add_zero] at ha0 ha1
      have hβa : β a (sp a) = 1 := by simpa using res_bump_center (s₀ := sp a) hδ0 hδ1 0
      obtain ⟨ρ₁, hρ₁, hJ⟩ := gaussLinkingIntegral_strip_bump_jump E U hU hDU hE hEunit γ hγ hγper
        hγunit Z hmiss N hN hNγ hNE c hc a (lam a) (sp a) δ (hcz a haZ).2.2.1 hδ0 hδ1
        (res_h η β S) (fun t => (1 - η) * β a t) (hh_contDiff S)
        (contDiff_const.mul (res_bump_contDiff _ _)) (hh_per S)
        (fun t => by simp only [hβ, res_bump_periodic])
        (fun t => ⟨(hh_mem S hSZ t).1, mul_nonneg (by linarith) (hβmem a t).1,
          by rw [← hins]; exact (hh_mem _ hiZ t).2⟩)
        (fun t ht => res_bump_supp hδ0 hδ1 fun h0 => ht (by simp only [hβ] at h0 ⊢; rw [h0, mul_zero]))
        (by rw [ha0]; exact (hηlam a haZ).2)
        (by rw [ha0, hβa]; have := (hcz a haZ).2.1; linarith)
        (fun t μ ht hμ0 hμ1 hmem => by
          generalize hzv : c + μ • (circlePoint t - c) = w at hmem ⊢
          obtain ⟨-, n, hn⟩ := (hcz w hmem).2.2.2.1 μ t hμ0 hzv
          by_contra hwa
          have := hsep a haZ w hmem hwa (-n)
          rw [hn] at ht
          push_cast at this
          rw [show sp w - sp a - -(n : ℝ) = sp w + n - sp a by ring] at this
          linarith)
        (hh_avoid S hSZ) (fun t => by rw [← hins]; exact hh_avoid _ hiZ t)
      have hm0 : 0 < min ρ ρ₁ / 2 := by positivity
      have hm1 : min ρ ρ₁ / 2 < ρ₁ := by linarith [min_le_right ρ ρ₁]
      have hm2 : min ρ ρ₁ / 2 < ρ₀ := by linarith [min_le_left ρ ρ₁]
      have hJ' := hJ _ hm0 hm1
      rw [hrad a haZ _ ρ hm0 hm2 hρ hρ'] at hJ'
      have he : (fun s => E (c + res_h η β (insert a S) s • (circlePoint s - c))) =
          fun s => E (c + (res_h η β S s + (1 - η) * β a s) • (circlePoint s - c)) := by
        funext s; rw [hins]
      rw [he, hJ', ih hSZ, Finset.sum_insert haS, add_comm]
  rw [htop, htel Z subset_rfl]

end HryniewiczCriterion

open HryniewiczCriterion

theorem solution (E : Plane → R4) (U : Set Plane) (hU : IsOpen U) (hDU : closedUnitDisk ⊆ U)
    (hE : ContDiffOn ℝ 2 E U) (hEunit : ∀ v ∈ closedUnitDisk, euclidNorm (E v) = 1)
    (γ : ℝ → R4) (hγ : ContDiff ℝ 2 γ) (hγper : ∀ t, γ (t + 1) = γ t)
    (hγunit : ∀ t, euclidNorm (γ t) = 1)
    (Z : Finset Plane) (hZ : ∀ z ∈ Z, z ∈ openUnitDisk)
    (hmiss : ∀ v ∈ closedUnitDisk, v ∉ Z → ∀ t, E v ≠ γ t)
    (N : R4) (hN : euclidNorm N = 1) (hNγ : ∀ t, γ t ≠ N)
    (hNE : ∀ v ∈ closedUnitDisk, E v ≠ N) :
    ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ ρ : ℝ, 0 < ρ → ρ < ρ₀ →
      gaussLinkingIntegral N (fun s => E (circlePoint s)) γ =
        ∑ z ∈ Z, gaussLinkingIntegral N (fun s => E (z + ρ • circlePoint s)) γ :=
  HryniewiczCriterion.gaussLinkingIntegral_disk_eq_sum_small_loops' E U hU hDU hE hEunit γ hγ hγper hγunit Z hZ hmiss N hN hNγ hNE
