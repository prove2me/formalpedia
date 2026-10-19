-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff.cutoff16
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T17:08:25.788178+00:00
-- url     : https://prove2.me/submissions/041cb17d-4498-4111-9e4f-8981efa8d3fc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Basic
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_ComplexTransfer
import Definitions.Def_HlawkaSchatten_GapComparison
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff_real_bound16
import Theorems.Thm_HlawkaSchatten_DiagonalConstruction_cyclicConstant_le_of_complex_constant
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa

Circle projection argument adapted from the accepted proof of
HlawkaSchatten.DiagonalConstruction.complex_hlawka_bound,
submission 89624825-1568-41a6-84a2-ddf8c4593b90.
The transfer below is generalized to every positive exponent and real constant.
-/

open MeasureTheory HlawkaSchatten HlawkaSchatten.DiagonalConstruction

namespace HlawkaTransferO18

open MeasureTheory

instance circleMeasure_isProbability : IsProbabilityMeasure circleMeasure :=
  ⟨by simpa only [TopologicalSpace.PositiveCompacts.coe_top] using
    (Measure.haarMeasure_self (K₀ := (⊤ : TopologicalSpace.PositiveCompacts Circle)))⟩

theorem continuous_circle_projection_power {p : ℝ} (hp : 0 < p) (z : ℂ) :
    Continuous (fun u : Circle ↦ |((u : ℂ) * z).re| ^ p) := by
  exact ((Complex.continuous_re.comp (continuous_subtype_val.mul continuous_const)).abs).rpow_const
    (fun _ ↦ Or.inr hp.le)

theorem circleMoment_pos {p : ℝ} (hp : 0 < p) : 0 < circleMoment p := by
  have hc : Continuous (fun u : Circle ↦ |(u : ℂ).re| ^ p) := by
    simpa only [mul_one] using continuous_circle_projection_power hp 1
  exact integral_pos_of_integrable_nonneg_nonzero hc
    (hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (fun u ↦ Real.rpow_nonneg (abs_nonneg _) _) (x := (1 : Circle)) (by simp)

theorem integral_circle_projection_power {p : ℝ} (hp : 0 < p) (z : ℂ) :
    (∫ u : Circle, |((u : ℂ) * z).re| ^ p ∂circleMeasure) = circleMoment p * ‖z‖ ^ p := by
  by_cases hz : z = 0
  · simp [hz, hp.ne']
  have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  let v : Circle := ⟨z / (‖z‖ : ℂ), mem_sphere_zero_iff_norm.mpr (by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg z), div_self hn])⟩
  have hv : (v : ℂ) * (‖z‖ : ℂ) = z := div_mul_cancel₀ _ (Complex.ofReal_ne_zero.mpr hn)
  have hre (u : Circle) : ((u : ℂ) * z).re = ‖z‖ * ((v * u : Circle) : ℂ).re := by
    calc
      _ = (((v : ℂ) * (u : ℂ)) * (‖z‖ : ℂ)).re := by
        congr 1
        conv_lhs => rw [← hv]
        ring
      _ = _ := by simp only [Circle.coe_mul, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, mul_zero, sub_zero]; ring
  simp_rw [hre, abs_mul, abs_of_nonneg (norm_nonneg z),
    Real.mul_rpow (norm_nonneg z) (abs_nonneg _)]
  rw [integral_const_mul]
  have hrot : (∫ a : Circle, |((v * a : Circle) : ℂ).re| ^ p ∂circleMeasure) = circleMoment p :=
    integral_mul_left_eq_self (μ := circleMeasure) (fun a : Circle ↦ |(a : ℂ).re| ^ p) v
  change ‖z‖ ^ p * (∫ a : Circle, |((v * a : Circle) : ℂ).re| ^ p ∂circleMeasure) = _
  rw [hrot]
  exact mul_comm _ _

variable {ι : Type} [Fintype ι]

theorem continuous_projectionPower {p : ℝ} (hp : 0 < p) (z : ι → ℂ) :
    Continuous (projectionPower p z) :=
  continuous_finsetSum _ fun i _ ↦ continuous_circle_projection_power hp (z i)

theorem integral_projectionPower {p : ℝ} (hp : 0 < p) (z : ι → ℂ) :
    (∫ u : Circle, projectionPower p z u ∂circleMeasure) = circleMoment p * ∑ i, ‖z i‖ ^ p := by
  unfold projectionPower
  rw [integral_finsetSum Finset.univ (fun i _ ↦
    (continuous_circle_projection_power hp (z i)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))]
  simp only [integral_circle_projection_power hp, Finset.mul_sum]

variable {κ : Type*} [Fintype κ]

omit [Fintype ι] [Fintype κ] in
theorem finiteProjection_add (p : ℝ) (w : κ → ℝ) (u : κ → Circle) (z v : ι → ℂ) :
    finiteProjection p w u (z + v) = finiteProjection p w u z + finiteProjection p w u v := by
  ext k
  simp [finiteProjection, mul_add, Complex.add_re]

theorem lpNorm_finiteProjection {p : ℝ} (hp : 0 < p) (w : κ → ℝ) (u : κ → Circle)
    (hw : ∀ k, 0 ≤ w k) (z : ι → ℂ) :
    HlawkaSchatten.DiagonalConstruction.lpNorm p (finiteProjection p w u z) = (∑ k, w k * projectionPower p z (u k)) ^ (1 / p) := by
  unfold HlawkaSchatten.DiagonalConstruction.lpNorm
  congr 1
  simp only [finiteProjection, Fintype.sum_prod_type, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (Real.rpow_nonneg (hw _) _)]
  simp_rw [Real.mul_rpow (Real.rpow_nonneg (hw _) _) (abs_nonneg _),
    ← Real.rpow_mul (hw _), one_div_mul_cancel hp.ne', Real.rpow_one]
  simp only [projectionPower, Finset.mul_sum]

theorem continuous_powerDeficit {p : ℝ} (hp : 0 < p) (K : ℝ) : Continuous (powerDeficit p K) := by
  have hc (i : Fin 7) : Continuous (fun a : Fin 7 → ℝ ↦ (a i) ^ (1 / p)) :=
    (continuous_apply i).rpow_const (fun _ ↦ Or.inr (one_div_nonneg.mpr hp.le))
  exact ((continuous_const.mul (((hc 0).add (hc 1)).add (hc 2))).add (hc 6)).sub
    (continuous_const.mul (((hc 3).add (hc 4)).add (hc 5)))

theorem continuous_sevenProjections {p : ℝ} (hp : 0 < p) (x y z : ι → ℂ) :
    Continuous (sevenProjections p x y z) :=
  continuous_pi fun k ↦ continuous_projectionPower hp (sevenVectors x y z k)

theorem powerDeficit_nonneg_on_projection_hull {p K : ℝ} (hp0 : 0 < p)
    (hreal : ∀ (ν : Type) [Fintype ν], HasHlawkaConstant (HlawkaSchatten.DiagonalConstruction.lpNorm p : (ν → ℝ) → ℝ) K)
    (x y z : ι → ℂ) :
    convexHull ℝ (Set.range (sevenProjections p x y z)) ⊆
      {a | 0 ≤ powerDeficit p K a} := by
  classical
  intro a ha
  obtain ⟨κ, _, w, points, hw, _, hpoints, hsum⟩ := mem_convexHull_iff_exists_fintype.mp ha
  choose u hu using hpoints
  have hsum' : ∑ k, w k • sevenProjections p x y z (u k) = a := by
    simpa only [hu] using hsum
  let R : (ι → ℂ) → κ × ι → ℝ := finiteProjection p w u
  have hadd (v v' : ι → ℂ) : R (v + v') = R v + R v' := finiteProjection_add p w u v v'
  have hn (k : Fin 7) : HlawkaSchatten.DiagonalConstruction.lpNorm p (R (sevenVectors x y z k)) = (a k) ^ (1 / p) := by
    rw [lpNorm_finiteProjection hp0 w u hw]
    congr 1
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, sevenProjections] using
      congrFun hsum' k
  have h0 := hn 0
  have h1 := hn 1
  have h2 := hn 2
  have h3 := hn 3
  have h4 := hn 4
  have h5 := hn 5
  have h6 := hn 6
  change HlawkaSchatten.DiagonalConstruction.lpNorm p (R x) = (a 0) ^ (1 / p) at h0
  change HlawkaSchatten.DiagonalConstruction.lpNorm p (R y) = (a 1) ^ (1 / p) at h1
  change HlawkaSchatten.DiagonalConstruction.lpNorm p (R z) = (a 2) ^ (1 / p) at h2
  change HlawkaSchatten.DiagonalConstruction.lpNorm p (R (x + y)) = (a 3) ^ (1 / p) at h3
  change HlawkaSchatten.DiagonalConstruction.lpNorm p (R (x + z)) = (a 4) ^ (1 / p) at h4
  change HlawkaSchatten.DiagonalConstruction.lpNorm p (R (y + z)) = (a 5) ^ (1 / p) at h5
  change HlawkaSchatten.DiagonalConstruction.lpNorm p (R (x + y + z)) = (a 6) ^ (1 / p) at h6
  have h := hreal (κ × ι) (R x) (R y) (R z)
  simp only [tripleGap, pairGapSum, pairGap, ← hadd] at h
  change 0 ≤ powerDeficit p K a
  unfold powerDeficit
  rw [← h0, ← h1, ← h2, ← h3, ← h4, ← h5, ← h6]
  nlinarith

theorem complex_of_real {p K : ℝ} (hp0 : 0 < p)
    (hreal : ∀ (ν : Type) [Fintype ν], HasHlawkaConstant (HlawkaSchatten.DiagonalConstruction.lpNorm p : (ν → ℝ) → ℝ) K) :
    HasHlawkaConstant (HlawkaSchatten.DiagonalConstruction.lpNorm p : (ι → ℂ) → ℝ) K := by
  intro x y z
  let F := sevenProjections p x y z
  let m : Fin 7 → ℝ := ∫ u : Circle, F u ∂circleMeasure
  have hcont : Continuous F := continuous_sevenProjections hp0 x y z
  have hfi : Integrable F circleMeasure :=
    hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hm : m ∈ closure (convexHull ℝ (Set.range F)) := by
    apply (convex_convexHull ℝ (Set.range F)).closure.integral_mem isClosed_closure _ hfi
    exact Filter.Eventually.of_forall fun u ↦
      subset_closure (subset_convexHull ℝ (Set.range F) (Set.mem_range_self u))
  have hclosed : IsClosed {a | 0 ≤ powerDeficit p K a} :=
    isClosed_le continuous_const (continuous_powerDeficit hp0 _)
  have hnon : 0 ≤ powerDeficit p K m :=
    (closure_minimal (powerDeficit_nonneg_on_projection_hull hp0 hreal x y z) hclosed) hm
  have hcoord (k : Fin 7) : m k = circleMoment p * ∑ i, ‖sevenVectors x y z k i‖ ^ p := by
    calc
      _ = ∫ u : Circle, F u k ∂circleMeasure :=
        ((ContinuousLinearMap.proj k : (Fin 7 → ℝ) →L[ℝ] ℝ).integral_comp_comm hfi).symm
      _ = _ := integral_projectionPower hp0 (sevenVectors x y z k)
  let c := circleMoment p ^ (1 / p)
  have hc : 0 < c := Real.rpow_pos_of_pos (circleMoment_pos hp0) _
  have hroot (k : Fin 7) : (m k) ^ (1 / p) = c * HlawkaSchatten.DiagonalConstruction.lpNorm p (sevenVectors x y z k) := by
    rw [hcoord, Real.mul_rpow (circleMoment_pos hp0).le
      (Finset.sum_nonneg fun i _ ↦ Real.rpow_nonneg (norm_nonneg _) _)]
    rfl
  simp only [powerDeficit, hroot] at hnon
  change 0 ≤ (2 * K - 1) *
      (c * HlawkaSchatten.DiagonalConstruction.lpNorm p x + c * HlawkaSchatten.DiagonalConstruction.lpNorm p y + c * HlawkaSchatten.DiagonalConstruction.lpNorm p z) + c * HlawkaSchatten.DiagonalConstruction.lpNorm p (x + y + z) -
    K * (c * HlawkaSchatten.DiagonalConstruction.lpNorm p (x + y) + c * HlawkaSchatten.DiagonalConstruction.lpNorm p (x + z) + c * HlawkaSchatten.DiagonalConstruction.lpNorm p (y + z)) at hnon
  have hscaled : 0 ≤ c * (K * pairGapSum (HlawkaSchatten.DiagonalConstruction.lpNorm p) x y z -
      tripleGap (HlawkaSchatten.DiagonalConstruction.lpNorm p) x y z) := by
    convert hnon using 1
    unfold pairGapSum pairGap tripleGap
    ring
  exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left hc).mp hscaled)

end HlawkaTransferO18

private theorem real_all_fintypes {p K : ℝ}
    (h : ∀ n : ℕ, HasHlawkaConstant (HlawkaSchatten.DiagonalConstruction.lpNorm p : (Fin n → ℝ) → ℝ) K)
    (ν : Type) [Fintype ν] : HasHlawkaConstant (HlawkaSchatten.DiagonalConstruction.lpNorm p : (ν → ℝ) → ℝ) K := by
  let e := Fintype.equivFin ν
  have hn (v : ν → ℝ) : HlawkaSchatten.DiagonalConstruction.lpNorm p (v ∘ e.symm) = HlawkaSchatten.DiagonalConstruction.lpNorm p v := by
    unfold HlawkaSchatten.DiagonalConstruction.lpNorm
    congr 1
    exact e.symm.sum_comp (fun i => ‖v i‖ ^ p)
  intro x y z
  have hh := h (Fintype.card ν) (x ∘ e.symm) (y ∘ e.symm) (z ∘ e.symm)
  have hadd (v w : ν → ℝ) : v ∘ e.symm + w ∘ e.symm = (v + w) ∘ e.symm := rfl
  simpa only [tripleGap, pairGapSum, pairGap, hadd, hn] using hh

theorem solution :
    ∀ p : ℝ, 16 ≤ p →
      IsLeast {C : ℝ | ∀ n : ℕ,
        HasHlawkaConstant (HlawkaSchatten.DiagonalConstruction.lpNorm p : (Fin n → ℂ) → ℝ) C}
        (cyclicConstant p) := by
  intro p hp
  constructor
  · intro n
    exact HlawkaTransferO18.complex_of_real (by linarith)
      (real_all_fintypes (HlawkaSchatten.DiagonalCutoff.real_bound16 p hp))
  · intro C hC
    exact cyclicConstant_le_of_complex_constant (by linarith) (by norm_num : 3 ≤ 3) (hC 3)
