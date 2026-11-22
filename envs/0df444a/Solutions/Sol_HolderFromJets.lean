-- Prove2me | solution 1 for HolderFromJets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:12:30.277969+00:00
-- url     : https://prove2.me/submissions/7d2cbd4c-a4d8-4204-a926-a12a79264077

import Definitions.Def_PHigherOrder_JetBounds
import Definitions.Def_PHigherOrder_PolyInverseEstimate
import Definitions.Def_PHigherOrder_TaylorPolyDeriv
import Definitions.Def_PHigherOrder_HolderFromJets
import Theorems.Thm_JetBounds
import Theorems.Thm_PolyInverseEstimate
import Theorems.Thm_TaylorPolyDeriv


set_option autoImplicit false

theorem _root_.solution (p : ℝ) (hp : 1 < p) (hp2 : p < 2)
    (hLR : LewisRigidityInput p) (F : FirstOrderEstimateInput p) (hIM : IMRegularityInput p)
    (hsm : SmoothAwayFromCriticalInput p) (hS : DivFormSchauderInput)
    (hLB : LocalBoundednessInput p)
    (k : ℕ) (hk : 2 ≤ k) (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (hks : (k : ℝ) + β < SOpt p) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (u : Plane → ℝ) (g : Plane → Plane), IsPHarm p (Metric.ball 0 1) u g →
        MeasureTheory.MemLp u (ENNReal.ofReal p)
          (MeasureTheory.volume.restrict (Metric.ball (0 : Plane) 1)) →
        ∀ x ∈ Metric.ball (0 : Plane) (1 / 2), ∀ y ∈ Metric.ball (0 : Plane) (1 / 2),
          ∀ w : Plane,
            |iteratedFDeriv ℝ k u x (fun _ => w) - iteratedFDeriv ℝ k u y (fun _ => w)|
              ≤ C * (MeasureTheory.eLpNorm u (ENNReal.ofReal p)
                    (MeasureTheory.volume.restrict (Metric.ball (0 : Plane) 1))).toReal
                * ‖x - y‖ ^ β * ‖w‖ ^ k := by
  -- Step 0: the constants, fixed before `u`
  obtain ⟨CJ, hCJ0, hJB⟩ := JetBounds p hp hp2 hLR F hIM hsm hS hLB k hk β hβ0 hβ1 hks
  obtain ⟨Ck, hCk0, hPIE⟩ := PolyInverseEstimate k
  have hσ0 : (0 : ℝ) < (k : ℝ) + β := by
    have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  have h16 : (0 : ℝ) < (16 : ℝ) ^ β := Real.rpow_pos_of_pos (by norm_num) _
  have h16ne : ((16 : ℝ) ^ β) ≠ 0 := ne_of_gt h16
  have h2s : (0 : ℝ) < (2 : ℝ) ^ ((k : ℝ) + β) := Real.rpow_pos_of_pos (by norm_num) _
  have hE1 : (0 : ℝ) < 2 * (16 : ℝ) ^ β * CJ := mul_pos (mul_pos two_pos h16) hCJ0
  have hE2 : (0 : ℝ) < Ck * (1 + (2 : ℝ) ^ ((k : ℝ) + β)) * CJ :=
    mul_pos (mul_pos hCk0 (by linarith)) hCJ0
  obtain ⟨C, hCdef⟩ : ∃ t : ℝ, t = max (2 * (16 : ℝ) ^ β * CJ)
      (Ck * (1 + (2 : ℝ) ^ ((k : ℝ) + β)) * CJ) := ⟨_, rfl⟩
  have hC1 : 2 * (16 : ℝ) ^ β * CJ ≤ C := by rw [hCdef]; exact le_max_left _ _
  have hC2 : Ck * (1 + (2 : ℝ) ^ ((k : ℝ) + β)) * CJ ≤ C := by rw [hCdef]; exact le_max_right _ _
  refine ⟨C, lt_of_lt_of_le hE1 hC1, ?_⟩
  intro u g hu hLp x hx y hy w
  obtain ⟨hjx, hex⟩ := hJB u g hu hLp x hx
  obtain ⟨hjy, hey⟩ := hJB u g hu hLp y hy
  set N := (MeasureTheory.eLpNorm u (ENNReal.ofReal p)
    (MeasureTheory.volume.restrict (Metric.ball (0 : Plane) 1))).toReal with hNdef
  have hN0 : 0 ≤ N := by rw [hNdef]; exact ENNReal.toReal_nonneg
  obtain ⟨d, hddef⟩ : ∃ t : ℝ, t = ‖x - y‖ := ⟨_, rfl⟩
  have hd0 : 0 ≤ d := by rw [hddef]; exact norm_nonneg _
  have hwk : (0 : ℝ) ≤ ‖w‖ ^ k := by positivity
  rw [← hddef]
  rcases eq_or_lt_of_le hd0 with hd | hd
  · -- Step 1: the case `d = 0`
    have hxy : x = y := by
      have h0 : ‖x - y‖ = 0 := by rw [← hddef, ← hd]
      exact sub_eq_zero.mp (norm_eq_zero.mp h0)
    rw [hxy, sub_self, abs_zero, ← hd, Real.zero_rpow (ne_of_gt hβ0)]
    simp
  rcases le_or_gt (1 / 16 : ℝ) d with hd16 | hd16
  · -- Step 2: the case `d ≥ 1/16`
    have hbx := hjx k (by omega) (le_refl k) w
    have hby := hjy k (by omega) (le_refl k) w
    have htri : |iteratedFDeriv ℝ k u x (fun _ => w) - iteratedFDeriv ℝ k u y (fun _ => w)|
        ≤ 2 * CJ * N * ‖w‖ ^ k := by
      calc |iteratedFDeriv ℝ k u x (fun _ => w) - iteratedFDeriv ℝ k u y (fun _ => w)|
          ≤ |iteratedFDeriv ℝ k u x (fun _ => w)| + |iteratedFDeriv ℝ k u y (fun _ => w)| :=
            abs_sub _ _
        _ ≤ CJ * N * ‖w‖ ^ k + CJ * N * ‖w‖ ^ k := add_le_add hbx hby
        _ = 2 * CJ * N * ‖w‖ ^ k := by ring
    refine le_trans htri ?_
    have hlow : ((16 : ℝ) ^ β)⁻¹ ≤ d ^ β := by
      rw [← Real.inv_rpow (by norm_num : (0 : ℝ) ≤ 16)]
      refine Real.rpow_le_rpow (by norm_num) ?_ (le_of_lt hβ0)
      rw [show ((16 : ℝ)⁻¹) = 1 / 16 by norm_num]
      exact hd16
    have hpos : (0 : ℝ) ≤ 2 * (16 : ℝ) ^ β * CJ * N := mul_nonneg (le_of_lt hE1) hN0
    have hfac : 2 * CJ * N * ‖w‖ ^ k
        = 2 * (16 : ℝ) ^ β * CJ * N * ((16 : ℝ) ^ β)⁻¹ * ‖w‖ ^ k := by
      field_simp
    rw [hfac]
    calc 2 * (16 : ℝ) ^ β * CJ * N * ((16 : ℝ) ^ β)⁻¹ * ‖w‖ ^ k
        ≤ 2 * (16 : ℝ) ^ β * CJ * N * d ^ β * ‖w‖ ^ k :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlow hpos) hwk
      _ ≤ C * N * d ^ β * ‖w‖ ^ k :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hC1 hN0) (Real.rpow_nonneg hd0 _)) hwk
  · -- Step 3: the case `0 < d < 1/16`
    -- (3a) two inclusions
    have hd4 : d < 1 / 4 := by linarith
    have hincl1 : ∀ z ∈ Metric.ball x d, z ∈ Metric.ball x (1 / 4) :=
      fun z hz => Metric.ball_subset_ball (le_of_lt hd4) hz
    have hincl2 : ∀ z ∈ Metric.ball x d, z ∈ Metric.ball y (1 / 4) := by
      intro z hz
      have h1 : ‖z - x‖ < d := by rw [← dist_eq_norm]; exact Metric.mem_ball.mp hz
      rw [Metric.mem_ball, dist_eq_norm]
      calc ‖z - y‖ = ‖z - x + (x - y)‖ := by rw [sub_add_sub_cancel]
        _ ≤ ‖z - x‖ + ‖x - y‖ := norm_add_le _ _
        _ < 1 / 4 := by rw [← hddef]; linarith
    -- (3b) the two Taylor polynomials are close on `ball x d`
    obtain ⟨A, hAdef⟩ : ∃ t : ℝ,
        t = (1 + (2 : ℝ) ^ ((k : ℝ) + β)) * CJ * N * d ^ ((k : ℝ) + β) := ⟨_, rfl⟩
    have hdσ0 : (0 : ℝ) ≤ d ^ ((k : ℝ) + β) := Real.rpow_nonneg hd0 _
    have hA0 : 0 ≤ A := by
      rw [hAdef]
      exact mul_nonneg (mul_nonneg (mul_nonneg (by linarith) (le_of_lt hCJ0)) hN0) hdσ0
    have hclose : ∀ z ∈ Metric.ball x d,
        |TaylorPoly k u x z - TaylorPoly k u y z| ≤ A := by
      intro z hz
      have hzx : ‖z - x‖ < d := by rw [← dist_eq_norm]; exact Metric.mem_ball.mp hz
      have h1 := hex z (hincl1 z hz)
      have h2 := hey z (hincl2 z hz)
      have hCN : (0 : ℝ) ≤ CJ * N := mul_nonneg (le_of_lt hCJ0) hN0
      have hb1 : CJ * N * ‖z - x‖ ^ ((k : ℝ) + β) ≤ CJ * N * d ^ ((k : ℝ) + β) :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (norm_nonneg _) (le_of_lt hzx) (le_of_lt hσ0)) hCN
      have hzy : ‖z - y‖ ≤ 2 * d := by
        calc ‖z - y‖ = ‖z - x + (x - y)‖ := by rw [sub_add_sub_cancel]
          _ ≤ ‖z - x‖ + ‖x - y‖ := norm_add_le _ _
          _ ≤ 2 * d := by rw [← hddef]; linarith
      have hb2 : CJ * N * ‖z - y‖ ^ ((k : ℝ) + β)
          ≤ CJ * N * ((2 : ℝ) ^ ((k : ℝ) + β) * d ^ ((k : ℝ) + β)) := by
        refine mul_le_mul_of_nonneg_left ?_ hCN
        rw [← Real.mul_rpow (by norm_num) hd0]
        exact Real.rpow_le_rpow (norm_nonneg _) hzy (le_of_lt hσ0)
      have heq : TaylorPoly k u x z - TaylorPoly k u y z
          = u z - TaylorPoly k u y z - (u z - TaylorPoly k u x z) := by ring
      rw [heq, hAdef]
      calc |u z - TaylorPoly k u y z - (u z - TaylorPoly k u x z)|
          ≤ |u z - TaylorPoly k u y z| + |u z - TaylorPoly k u x z| := abs_sub _ _
        _ ≤ CJ * N * ((2 : ℝ) ^ ((k : ℝ) + β) * d ^ ((k : ℝ) + β))
              + CJ * N * d ^ ((k : ℝ) + β) :=
            add_le_add (le_trans h2 hb2) (le_trans h1 hb1)
        _ = (1 + (2 : ℝ) ^ ((k : ℝ) + β)) * CJ * N * d ^ ((k : ℝ) + β) := by ring
    -- (3c) the inverse estimate applied to the difference
    obtain ⟨hPcd, hPtop, hPdiag, hPjet, hPval⟩ := TaylorPolyDeriv k u x
    obtain ⟨hQcd, hQtop, hQdiag, hQjet, hQval⟩ := TaylorPolyDeriv k u y
    obtain ⟨S, hSdef⟩ : ∃ f : Plane → ℝ, f = TaylorPoly k u x - TaylorPoly k u y := ⟨_, rfl⟩
    have hSval : ∀ z : Plane, S z = TaylorPoly k u x z - TaylorPoly k u y z := by
      intro z; rw [hSdef]; rfl
    have hScd : ContDiff ℝ (⊤ : ℕ∞) S := by rw [hSdef]; exact hPcd.sub hQcd
    have hSjet : ∀ (n : ℕ) (ζ : Plane), iteratedFDeriv ℝ n S ζ
        = iteratedFDeriv ℝ n (TaylorPoly k u x) ζ
          - iteratedFDeriv ℝ n (TaylorPoly k u y) ζ := by
      intro n ζ
      rw [hSdef]
      exact iteratedFDeriv_sub_apply (hPcd.contDiffAt.of_le (by exact_mod_cast le_top))
        (hQcd.contDiffAt.of_le (by exact_mod_cast le_top))
    have hStop : ∀ ζ : Plane, iteratedFDeriv ℝ (k + 1) S ζ = 0 := by
      intro ζ
      rw [hSjet (k + 1) ζ, hPtop ζ, hQtop ζ, sub_zero]
    have hpie := hPIE S hScd hStop x d A hd hA0
      (fun z hz => by rw [hSval z]; exact hclose z hz)
    -- (3d) passing to the diagonal and identifying the two jets
    have hdiag : |iteratedFDeriv ℝ k S x (fun _ => w)|
        ≤ ‖iteratedFDeriv ℝ k S x‖ * ‖w‖ ^ k := by
      have hnw : ‖(fun _ : Fin k => w)‖ ≤ ‖w‖ :=
        (pi_norm_le_iff_of_nonneg (norm_nonneg w)).mpr fun _ => le_refl _
      have h := ContinuousMultilinearMap.le_opNorm_mul_pow_of_le (iteratedFDeriv ℝ k S x) hnw
      rwa [Real.norm_eq_abs] at h
    have hjetid : iteratedFDeriv ℝ k S x (fun _ => w)
        = iteratedFDeriv ℝ k u x (fun _ => w) - iteratedFDeriv ℝ k u y (fun _ => w) := by
      rw [hSjet k x, sub_apply, hPdiag x w, hQdiag x w]
    rw [← hjetid]
    refine le_trans hdiag ?_
    refine le_trans (mul_le_mul_of_nonneg_right hpie hwk) ?_
    -- (3e) the exponent
    have hdk0 : (0 : ℝ) < d ^ k := by positivity
    have hexp : d ^ ((k : ℝ) + β) / d ^ k = d ^ β := by
      rw [Real.rpow_add hd, Real.rpow_natCast]
      field_simp
    have harith : Ck * A / d ^ k
        = Ck * (1 + (2 : ℝ) ^ ((k : ℝ) + β)) * CJ * N * d ^ β := by
      rw [hAdef, ← hexp]
      field_simp
    rw [harith]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hC2 hN0) (Real.rpow_nonneg hd0 _)) hwk
