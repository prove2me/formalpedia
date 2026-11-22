-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.exp_of_semigroup_bounded
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T23:04:29.0062+00:00
-- url     : https://prove2.me/submissions/5d7be797-6c3c-4f9f-8a5f-c0b9d1710bc0

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

lemma exp_semigroup_bounded_core_2a006b93
    (f : ℝ → ℝ)
    (hsemi : ∀ x y : ℝ, 0 < x → 0 < y → f (x + y) = f x * f y)
    (hpos : ∀ x : ℝ, 0 < x → 0 < f x)
    (hbdd : ∃ B : ℝ, ∀ x : ℝ, 1 ≤ x → x ≤ 2 → f x ≤ B) :
    ∀ a : ℝ, 0 < a → f a = Real.exp (-a * (-Real.log (f 1))) := by
  rcases hbdd with ⟨B, hB⟩
  let G : ℝ → ℝ := fun x => if 0 < x then Real.log (f x) else if x < 0 then -Real.log (f (-x)) else 0
  have hGp {x : ℝ} (hx : 0 < x) : G x = Real.log (f x) := by simp [G, hx, not_lt_of_ge (le_of_lt hx)]
  have hGn {x : ℝ} (hx : x < 0) : G x = -Real.log (f (-x)) := by have hn : ¬ 0 < x := not_lt_of_ge (le_of_lt hx); simp [G, hn, hx]
  have hG0 : G 0 = 0 := by simp [G]
  have haddpp {x y : ℝ} (hx : 0 < x) (hy : 0 < y) : G (x + y) = G x + G y := by
    rw [hGp (add_pos hx hy), hGp hx, hGp hy, hsemi x y hx hy]; exact Real.log_mul (ne_of_gt (hpos x hx)) (ne_of_gt (hpos y hy))
  have hpn {x y : ℝ} (hx : 0 < x) (hy : y < 0) : G (x + y) = G x + G y := by
    have hny : 0 < -y := neg_pos.mpr hy
    rcases lt_trichotomy (x + y) 0 with hneg | hzero | hposxy
    · have hz : 0 < -(x + y) := neg_pos.mpr hneg; have h := haddpp hx hz
      rw [show x + (-(x + y)) = -y by ring, hGp hny, hGp hz, hGp hx] at h; rw [hGn hneg, hGp hx, hGn hy]; linarith
    · rw [hzero, hG0, hGp hx, hGn hy]
      have hEq : -y = x := by linarith
      rw [hEq]
      ring
    · have h := haddpp hposxy hny
      rw [show (x + y) + (-y) = x by ring, hGp hposxy, hGp hny, hGp hx] at h; rw [hGp hposxy, hGp hx, hGn hy]; linarith
  have hnn {x y : ℝ} (hx : x < 0) (hy : y < 0) : G (x + y) = G x + G y := by
    have hpx : 0 < -x := neg_pos.mpr hx; have hpy : 0 < -y := neg_pos.mpr hy
    have hxy : x + y < 0 := by linarith
    have hz : 0 < -(x + y) := neg_pos.mpr hxy
    have h := haddpp hpx hpy
    rw [show -x + -y = -(x + y) by ring, hGp hpx, hGp hpy, hGp hz] at h; rw [hGn hxy, hGn hx, hGn hy]; linarith
  have hGadd (x y : ℝ) : G (x + y) = G x + G y := by
    rcases lt_trichotomy x 0 with hxneg | hxzero | hxpos
    · rcases lt_trichotomy y 0 with hyneg | hyzero | hypos
      · exact hnn hxneg hyneg
      · rw [hyzero, add_zero, hG0, add_zero]
      · calc
          G (x + y) = G (y + x) := by rw [add_comm]
          _ = G y + G x := hpn hypos hxneg
          _ = G x + G y := by rw [add_comm]
    · rw [hxzero, zero_add, hG0, zero_add]
    · rcases lt_trichotomy y 0 with hyneg | hyzero | hypos
      · exact hpn hxpos hyneg
      · rw [hyzero, add_zero, hG0, add_zero]
      · exact haddpp hxpos hypos
  let H : ℝ →+ ℝ := { toFun := G, map_zero' := hG0, map_add' := hGadd }
  let C : ℝ := |Real.log B| + |Real.log (f 1)| + |Real.log (f 2)| + 1
  have hC : 0 ≤ C := by dsimp [C]; linarith [abs_nonneg (Real.log B), abs_nonneg (Real.log (f 1)), abs_nonneg (Real.log (f 2))]
  have hu {t : ℝ} (h1 : 1 ≤ t) (h2 : t ≤ 2) : Real.log (f t) ≤ Real.log B := Real.log_le_log (hpos t (lt_of_lt_of_le zero_lt_one h1)) (hB t h1 h2)
  have hbp {x : ℝ} (hx : 0 < x) (hx1 : x < 1) : |G x| ≤ C := by
    have hx1p : 0 < x + 1 := by linarith
    have hux1 : G (x + 1) ≤ Real.log B := by rw [hGp hx1p]; exact hu (by linarith) (by linarith)
    have ha1 := hGadd x 1; rw [hGp zero_lt_one] at ha1
    have hup : G x ≤ Real.log B - Real.log (f 1) := by linarith
    have h2p : 0 < 2 - x := by linarith
    have hux2 : Real.log (f (2 - x)) ≤ Real.log B := hu (by linarith) (by linarith)
    have ha2 := hGadd x (2 - x)
    rw [show x + (2 - x) = 2 by ring, hGp (by norm_num : (0 : ℝ) < 2), hGp h2p] at ha2
    have hlo : Real.log (f 2) - Real.log B ≤ G x := by linarith
    have hnegC : -C ≤ Real.log (f 2) - Real.log B := by dsimp [C]; linarith [neg_le_abs (Real.log (f 2)), le_abs_self (Real.log B), abs_nonneg (Real.log (f 1))]
    have hCup : Real.log B - Real.log (f 1) ≤ C := by dsimp [C]; linarith [le_abs_self (Real.log B), neg_le_abs (Real.log (f 1)), abs_nonneg (Real.log (f 2))]
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hbn {x : ℝ} (hl : -1 < x) (hx : x < 0) : |G x| ≤ C := by
    have hb := hbp (neg_pos.mpr hx) (by linarith)
    rw [hGp (neg_pos.mpr hx)] at hb
    rw [hGn hx]
    simpa [abs_neg] using hb
  have hnbd : Set.Ioo (-1 : ℝ) 1 ∈ nhds (0 : ℝ) := isOpen_Ioo.mem_nhds (by constructor <;> norm_num)
  have hbddG : Bornology.IsBounded (H '' Set.Ioo (-1 : ℝ) 1) := by
    rw [isBounded_iff_forall_norm_le]; refine ⟨C, ?_⟩
    rintro z ⟨x, hx, rfl⟩; change ‖G x‖ ≤ C; rw [Real.norm_eq_abs]
    rcases lt_trichotomy x 0 with hxneg | hxzero | hxpos
    · exact hbn hx.1 hxneg
    · rw [hxzero, hG0]; simpa using hC
    · exact hbp hxpos hx.2
  have hcontH : Continuous (H : ℝ → ℝ) := AddMonoidHom.continuous_of_isBounded_nhds_zero H hnbd hbddG
  let L : ℝ →L[ℝ] ℝ := H.toRealLinearMap hcontH
  have hL : ∀ x : ℝ, L x = G x := by intro x; simp [L, H]
  have hLlin : ∀ x : ℝ, L x = x * L 1 := by intro x; simpa [smul_eq_mul] using (L.map_smul x (1 : ℝ))
  have hGlin : ∀ x : ℝ, G x = x * Real.log (f 1) := by
    intro x; rw [← hL x]
    calc
      L x = x * L 1 := hLlin x
      _ = x * Real.log (f 1) := by rw [hL 1, hGp zero_lt_one]
  intro a ha
  have hlog : Real.log (f a) = a * Real.log (f 1) := by rw [← hGp ha]; exact hGlin a
  rw [← Real.exp_log (hpos a ha)]; congr 1; rw [hlog]; ring

theorem solution
    (f : ℝ → ℝ)
    (hsemi : ∀ x y : ℝ, 0 < x → 0 < y → f (x + y) = f x * f y)
    (hpos : ∀ x : ℝ, 0 < x → 0 < f x)
    (hbdd : ∃ B : ℝ, ∀ x : ℝ, 1 ≤ x → x ≤ 2 → f x ≤ B) :
    ∀ a : ℝ, 0 < a → f a = Real.exp (-a * (-Real.log (f 1))) := by
  exact exp_semigroup_bounded_core_2a006b93 f hsemi hpos hbdd
