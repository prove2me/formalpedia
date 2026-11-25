-- Prove2me | solution 1 for GlobalTheory.PlaneTheta.zero_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:13:35.799616+00:00
-- url     : https://prove2.me/submissions/a3ca0cd5-fa1a-424a-8fdc-230cbca9d160

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_NonemptyRayDataOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_SummableLatticeExpNegPiMulNormSqDiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LatticeThetaAsymptotics
import Theorems.Thm_GlobalTheory_PlaneTheta_exists_pos_le_of_summable
import Theorems.Thm_GlobalTheory_PlaneTheta_abs_tsum_le
import Theorems.Thm_GlobalTheory_poisson_gaussian_lattice_cos
import Theorems.Thm_GlobalTheory_summable_lattice_exp_neg_mul_norm_sq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Asymptotics
open scoped RealInnerProductSpace
open GlobalTheory GlobalTheory.PlaneTheta
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
namespace GlobalTheory.PlaneTheta
theorem _root_.solution (hE : Module.finrank ℝ E = 2) (u : E) :
    ∃ c : ℝ, 0 < c ∧ (fun t : ℝ => (∑' x : L, Real.exp (-Real.pi * t * ‖(x : E) + u‖ ^ 2))
      - 1 / (t * ZLattice.covolume L))
      =O[nhdsWithin 0 (Set.Ioi 0)] (fun t => Real.exp (-c / t)) := by
  classical
  have h : Summable fun y : dualLattice L => Real.exp (-(Real.pi * ‖(y : E)‖ ^ 2)) := by
    simpa only [neg_mul] using summable_lattice_exp_neg_mul_norm_sq (dualLattice L) Real.pi_pos
  obtain ⟨δ, hδ, hq⟩ := exists_pos_le_of_summable h
  have hV := ZLattice.covolume_pos L MeasureTheory.volume
  set C := Real.exp δ * ∑' y : dualLattice L, Real.exp (-(Real.pi * ‖(y : E)‖ ^ 2)) with hC
  have hC0 : 0 ≤ C := mul_nonneg (Real.exp_pos _).le (tsum_nonneg fun _ => (Real.exp_pos _).le)
  refine ⟨δ / 2, by positivity, IsBigO.of_bound ((ZLattice.covolume L)⁻¹ * (2 / δ) * C) ?_⟩
  have h4 : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), t < 1 :=
    nhdsWithin_le_nhds (gt_mem_nhds one_pos)
  filter_upwards [h4, self_mem_nhdsWithin] with t ht1 ht
  have ht : 0 < t := ht
  obtain ⟨h1, h2⟩ := poisson_gaussian_lattice_cos L ht u
  rw [h2, h1.tsum_eq_add_tsum_ite 0, hE]
  have hs : 1 ≤ t⁻¹ := (one_le_inv₀ ht).2 ht1.le
  have h5 := abs_tsum_le (δ := δ) (f := fun y : dualLattice L => if y = 0 then 0 else
      Real.exp (-Real.pi * ‖(y : E)‖ ^ 2 / t) * Real.cos (2 * Real.pi * ⟪(y : E), u⟫)) hs h
      (fun y => ?_) (fun y hy => hq y ?_)
  · generalize (∑' y : dualLattice L, if y = 0 then 0 else
      Real.exp (-Real.pi * ‖(y : E)‖ ^ 2 / t) * Real.cos (2 * Real.pi * ⟪(y : E), u⟫)) = S at h5 ⊢
    rw [← hC] at h5
    have h6 : t ^ (-(((2 : ℕ) : ℝ) / 2)) = t⁻¹ := by
      rw [← Real.rpow_neg_one]; norm_num
    rw [h6]
    have h7 : (ZLattice.covolume L)⁻¹ * t⁻¹ * (Real.exp (-Real.pi * ‖((0 : dualLattice L) : E)‖ ^ 2 / t) *
        Real.cos (2 * Real.pi * ⟪((0 : dualLattice L) : E), u⟫) + S) - 1 / (t * ZLattice.covolume L)
        = (ZLattice.covolume L)⁻¹ * t⁻¹ * S := by
      simp only [ZeroMemClass.coe_zero, norm_zero, inner_zero_left]
      simp
      ring
    rw [h7, Real.norm_of_nonneg (Real.exp_pos _).le, Real.norm_eq_abs, abs_mul,
      abs_of_pos (by positivity)]
    have h8 : t⁻¹ ≤ 2 / δ * Real.exp (δ / 2 * t⁻¹) := by
      have := Real.add_one_le_exp (δ / 2 * t⁻¹)
      rw [div_mul_eq_mul_div, le_div_iff₀ hδ]
      nlinarith
    calc (ZLattice.covolume L)⁻¹ * t⁻¹ * |S|
        ≤ (ZLattice.covolume L)⁻¹ * (2 / δ * Real.exp (δ / 2 * t⁻¹)) * (C * Real.exp (-δ * t⁻¹)) := by
          gcongr
      _ = (ZLattice.covolume L)⁻¹ * (2 / δ) * C * (Real.exp (δ / 2 * t⁻¹) * Real.exp (-δ * t⁻¹)) := by
          ring
      _ = (ZLattice.covolume L)⁻¹ * (2 / δ) * C * Real.exp (-(δ / 2) / t) := by
          rw [← Real.exp_add]; congr 2; ring
  · split_ifs
    · rw [abs_zero]; positivity
    · rw [abs_mul, abs_of_pos (Real.exp_pos _)]
      refine (mul_le_of_le_one_right (Real.exp_pos _).le (Real.abs_cos_le_one _)).trans ?_
      apply le_of_eq; congr 1; ring
  · have hy0 : y ≠ 0 := fun h0 => hy (if_pos h0)
    have : 0 < ‖(y : E)‖ := norm_pos_iff.2 (by simpa using hy0)
    have := Real.pi_pos
    positivity
end GlobalTheory.PlaneTheta
