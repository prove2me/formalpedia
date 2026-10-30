-- Prove2me | solution 1 for OAI.Falconer.Regularization.nonendpoint_one_scale_gain
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T21:55:33.951103+00:00
-- url     : https://prove2.me/submissions/940367a2-b865-4f36-8ba0-5559ff0d5f8e

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ088F002
import Theorems.Thm_OAI_Falconer_Regularization_nonendpoint_source_class_middle_pruning

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_InversePowerSum
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite dyadic inverse-power sums at the critical ambient exponent -/

namespace Falconer

theorem inverse_power_dyadic {r s : ℝ} (hr : 0 < r) (hs : 0 ≤ s) (g k : ℕ)
    (hmin : 1/(2:ℝ)^(g+k) ≤ r) :
    (1/r)^s ≤ ((2:ℝ)^g)^s + ∑ j ∈ Finset.range k,
      if r < 1/(2:ℝ)^(g+j) then ((2:ℝ)^(g+j+1))^s else 0 := by
  induction k with
  | zero =>
    simp only [Finset.range_zero,Finset.sum_empty,add_zero] at *
    apply Real.rpow_le_rpow (by positivity) _ hs
    apply (div_le_iff₀ hr).mpr
    have hh := (div_le_iff₀ (by positivity : 0 < (2:ℝ)^g)).mp hmin
    nlinarith
  | succ k ih =>
    rw [Finset.sum_range_succ]
    by_cases hc : 1/(2:ℝ)^(g+k) ≤ r
    · have hh := ih hc
      have hn : 0 ≤ (if r < 1/(2:ℝ)^(g+k) then ((2:ℝ)^(g+k+1))^s else 0) := by
        split_ifs <;> positivity
      linarith
    · rw [ite_eq_left (lt_of_not_ge hc)]
      have hinv : 1/r ≤ (2:ℝ)^(g+k+1) := by
        apply (div_le_iff₀ hr).mpr
        have hh := (div_le_iff₀ (by positivity : 0 < (2:ℝ)^(g+(k+1)))).mp hmin
        simpa only [Nat.add_assoc,mul_comm] using hh
      have hp := Real.rpow_le_rpow (by positivity : 0 ≤ 1/r) hinv hs
      have hsum : 0 ≤ ∑ j ∈ Finset.range k,
          if r < 1/(2:ℝ)^(g+j) then ((2:ℝ)^(g+j+1))^s else 0 := by
        apply Finset.sum_nonneg
        intro j _
        split_ifs <;> positivity
      have hz : 0 ≤ ((2:ℝ)^g)^s := by positivity
      linarith

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_Potential
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Finset

theorem finiteMin_le {ι : Type*} {s : Finset ι} (f : ι → ℝ)
    {i : ι} (hi : i ∈ s) : finiteMin s f ≤ f i := by
  rw [finiteMin, dite_eq_left ⟨i, hi⟩]
  exact Finset.inf'_le f hi

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_Ledger
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Finset

theorem intervalMin_attained (A : ℕ → ℝ) {a t : ℕ} (hat : a ≤ t) :
    ∃ i, a ≤ i ∧ i ≤ t ∧ intervalMin A a t = A i := by
  have hn : (Finset.Icc a t).Nonempty := ⟨a, Finset.mem_Icc.mpr ⟨le_rfl,hat⟩⟩
  obtain ⟨i,hi,he⟩ := Finset.exists_mem_eq_inf' hn A
  exact ⟨i,(Finset.mem_Icc.mp hi).1,(Finset.mem_Icc.mp hi).2,
    by simpa only [intervalMin, finiteMin, dite_eq_left hn] using he⟩

theorem intervalMin_le (A : ℕ → ℝ) {a t i : ℕ} (hai : a ≤ i) (hit : i ≤ t) :
    intervalMin A a t ≤ A i := finiteMin_le A (Finset.mem_Icc.mpr ⟨hai,hit⟩)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Graphs_GraphNormalization
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Dimension-dependent normalization and branch ledger

The critical slope is `d / 2`. Both copies of a profile are needed for
the cancellation of the spatial normalization. The last-potential bound
uses the last interval with a defined two-depth potential, even when the
final interval itself is shorter.
-/

namespace Falconer
open scoped BigOperators

theorem dyadic_rpow_change_base {N : ℕ} (hN : 0 < N) (x : ℝ) :
    ((2 : ℝ)^N) ^ (x / (N : ℝ)) = (2 : ℝ)^x := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  congr 1
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_AllDimensionalAngularProfileSum
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Critical-dimensional cancellation in the parallel-test average

Here `s` will be d/2. The interval minimum is over the original integer
depths, and the retained profile is evaluated at those exact depths.
-/

namespace Falconer

theorem dyadic_power_rpow_as_R {N : ℕ} (hN : 0 < N) (n : ℕ) (s : ℝ) :
    ((2:ℝ)^n)^s = ((2:ℝ)^N)^(s*(n:ℝ)/N) := by
  rw [dyadic_rpow_change_base hN,← Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 2)]
  congr 1
  ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Graphs_AllDimensionalGraphGeometry
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Geometry of the retained graph in arbitrary dimension

The graph tests use orthogonal distance to a line and one scalar longitudinal
constraint. Each longitudinal constraint is in the unknown endpoint's own
cap direction. In particular these bounds do not divide by the angle between
the two endpoint directions.
-/

namespace Falconer

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem perpendicularPart_sub (w u v : E) :
    perpendicularPart w (u-v) = perpendicularPart w u - perpendicularPart w v := by
  simp only [perpendicularPart, inner_sub_right, sub_smul]
  abel

/-- Orthogonal projection is a contraction. -/
theorem norm_perpendicularPart_le {w : E} (hw : ‖w‖ = 1) (v : E) :
    ‖perpendicularPart w v‖ ≤ ‖v‖ := by
  have hn := norm_sub_sq_real v (inner ℝ w v • w)
  rw [real_inner_smul_right, real_inner_comm v w, norm_smul, hw,
    mul_one, Real.norm_eq_abs, sq_abs] at hn
  change ‖v - inner ℝ w v • w‖ ≤ ‖v‖
  rw [real_inner_comm v w]
  nlinarith [norm_nonneg (v - inner ℝ v w • w), norm_nonneg v, sq_nonneg (inner ℝ v w)]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_GridCount
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Candidate grid counts in any ambient dimension

The remaining unknown cell in a retained graph edge is confined to a small
ball. Its integer coordinate labels therefore lie in a product of short
integer intervals. This gives the dimension-dependent degree factor.
-/

namespace Falconer

/-- Euclidean distance bounds every integer coordinate difference. -/
theorem grid_coordinate_bound {d L : ℕ} {s r : ℝ} (hs : 0 < s)
    (hL : r * s ≤ L) {z w : Fin d → ℤ}
    (hz : ‖scaledGridPoint s z - scaledGridPoint s w‖ ≤ r) (i : Fin d) :
    |z i - w i| ≤ (L : ℤ) := by
  have hi := (PiLp.norm_apply_le (scaledGridPoint s z - scaledGridPoint s w) i).trans hz
  change |(z i : ℝ) / s - (w i : ℝ) / s| ≤ r at hi
  rw [← sub_div, abs_div, abs_of_pos hs] at hi
  have hb : |(z i : ℝ) - (w i : ℝ)| ≤ (L : ℝ) :=
    ((div_le_iff₀ hs).mp hi).trans hL
  exact_mod_cast hb

/-- A finite family in a coordinate box has at most `(2L+1)^d` labels. -/
theorem grid_box_card {d L : ℕ} (S : Finset (Fin d → ℤ)) (w : Fin d → ℤ)
    (hS : ∀ z ∈ S, ∀ i, |z i - w i| ≤ (L : ℤ)) :
    S.card ≤ (2 * L + 1)^d := by
  classical
  let shift : (Fin d → ℤ) → (Fin d → ℤ) := fun z i => z i - w i
  have hi : Function.Injective shift := by
    intro u v huv
    funext i
    have hi := congrFun huv i
    dsimp [shift] at hi
    omega
  have hsub : S.image shift ⊆
      Fintype.piFinset (fun _ : Fin d => Finset.Icc (-(L : ℤ)) (L : ℤ)) := by
    intro z hz
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hz
    apply Fintype.mem_piFinset.mpr
    intro i
    exact Finset.mem_Icc.mpr (abs_le.mp (hS u hu i))
  have hcard : (Finset.Icc (-(L : ℤ)) (L : ℤ)).card = 2 * L + 1 := by
    rw [Int.card_Icc]
    omega
  calc
    S.card = (S.image shift).card := (Finset.card_image_of_injective S hi).symm
    _ ≤ (Fintype.piFinset (fun _ : Fin d => Finset.Icc (-(L : ℤ)) (L : ℤ))).card :=
      Finset.card_le_card hsub
    _ = (2 * L + 1)^d := by simp [Fintype.card_piFinset, hcard]

/-- Ball count at a chosen grid center, with explicit integer radius. -/
theorem grid_ball_card {d L : ℕ} {s r : ℝ} (hs : 0 < s) (hL : r * s ≤ L)
    (S : Finset (Fin d → ℤ)) (w : Fin d → ℤ)
    (hS : ∀ z ∈ S, ‖scaledGridPoint s z - scaledGridPoint s w‖ ≤ r) :
    S.card ≤ (2 * L + 1)^d :=
  grid_box_card S w (fun z hz i => grid_coordinate_bound hs hL (hS z hz) i)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_AngularTubes
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# A perpendicular tube test occupies two small direction caps

The centers are the two directions of the actual tested displacement.
This gives the angular measure bound used in the parallel-test average.
-/

namespace Falconer
open MeasureTheory Set Metric
open scoped ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem perpendicularPart_smul (w v : E) (a : ℝ) :
    perpendicularPart w (a • v) = a • perpendicularPart w v := by
  simp only [perpendicularPart,inner_smul_right,smul_sub,smul_smul]

theorem norm_perpendicularPart_sq {w : E} (hw : ‖w‖ = 1) (v : E) :
    ‖perpendicularPart w v‖^2 = ‖v‖^2-(inner ℝ w v)^2 := by
  have h := norm_sub_sq_real v (inner ℝ w v • w)
  rw [real_inner_smul_right,real_inner_comm v w,norm_smul,hw,
    mul_one,Real.norm_eq_abs,sq_abs] at h
  dsimp only [perpendicularPart]
  rw [real_inner_comm v w]
  nlinarith

theorem unit_close_of_perpendicular {w u : E} (hw : ‖w‖ = 1) (hu : ‖u‖ = 1)
    (hinner : 0 ≤ inner ℝ w u) :
    ‖w-u‖ ≤ 2*‖perpendicularPart w u‖ := by
  have hsq := norm_sub_sq_real w u
  have hp := norm_perpendicularPart_sq hw u
  have ha : inner ℝ w u ≤ 1 := by
    have h := (le_abs_self (inner ℝ w u)).trans (abs_real_inner_le_norm w u)
    simpa only [hw,hu,mul_one] using h
  rw [hw,hu] at hsq
  rw [hu] at hp
  have hprod := mul_nonneg (sub_nonneg.mpr ha) (show 0 ≤ 4*inner ℝ w u+2 by linarith)
  nlinarith [norm_nonneg (w-u),norm_nonneg (perpendicularPart w u)]

theorem perpendicular_direction_two_caps {w v : E} (hw : ‖w‖ = 1)
    (hv : v ≠ 0) {W : ℝ} (htube : ‖perpendicularPart w v‖ ≤ W) :
    ‖w-‖v‖⁻¹ • v‖ ≤ 2*W/‖v‖ ∨ ‖w-(-‖v‖⁻¹ • v)‖ ≤ 2*W/‖v‖ := by
  have hvp : 0 < ‖v‖ := norm_pos_iff.mpr hv
  let u := ‖v‖⁻¹ • v
  have hu : ‖u‖ = 1 := by
    dsimp [u]
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hvp),inv_mul_cancel₀ hvp.ne']
  have hpu : ‖perpendicularPart w u‖ ≤ W/‖v‖ := by
    dsimp [u]
    rw [perpendicularPart_smul,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hvp)]
    simpa only [div_eq_mul_inv,mul_comm] using mul_le_mul_of_nonneg_left htube (inv_nonneg.mpr hvp.le)
  have hscale : 2*‖perpendicularPart w u‖ ≤ 2*W/‖v‖ := by
    calc
      _ ≤ 2*(W/‖v‖) := mul_le_mul_of_nonneg_left hpu (by norm_num)
      _ = _ := by ring
  rcases le_total 0 (inner ℝ w u) with hi | hi
  · exact Or.inl ((unit_close_of_perpendicular hw hu hi).trans hscale)
  · have hneg : perpendicularPart w (-u) = -perpendicularPart w u := by
      simp only [perpendicularPart,inner_neg_right,neg_smul]
      abel
    have hh := unit_close_of_perpendicular hw (by simpa only [norm_neg] using hu)
      (show 0 ≤ inner ℝ w (-u) by rw [inner_neg_right]; linarith)
    rw [hneg,norm_neg] at hh
    right
    simpa only [u,neg_smul] using hh.trans hscale

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_BlockRegularization
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

theorem blockDepth_gap (N B i : ℕ) : blockDepth N B i - blockDepth N B (i+1) ≤ B := by
  dsimp only [blockDepth]
  rw [Nat.add_mul, one_mul]
  omega

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_RegularizationScales
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

theorem division_blocks_control {H N : ℕ} (hH : 0 < H) (hN : H ≤ N) :
    0 < N/H ∧ N/(N/H)+1 ≤ 2*H := by
  have hB : 0 < N/H := Nat.div_pos hN hH
  have hrem : N < (N/H+1)*H := by simpa [Nat.mul_comm] using Nat.lt_mul_div_succ N hH
  have hmul : (N/H+1)*H ≤ (2*(N/H))*H := Nat.mul_le_mul_right H (by omega)
  have hlt : N < (2*H)*(N/H) := by
    calc
      N < (N/H+1)*H := hrem
      _ ≤ (2*(N/H))*H := hmul
      _ = (2*H)*(N/H) := by ac_rfl
  have hdiv : N/(N/H) < 2*H := (Nat.div_lt_iff_lt_mul hB).mpr hlt
  exact ⟨hB,by omega⟩

theorem division_block_width {H N : ℕ} {lam : ℝ} (hlam : 0 ≤ lam)
    (hH : 1 ≤ lam*(H:ℝ)) : ((N/H:ℕ):ℝ) ≤ lam*(N:ℝ) := by
  have hn : (((N/H)*H:ℕ):ℝ) ≤ (N:ℝ) := by exact_mod_cast Nat.div_mul_le_self N H
  have h0 : 0 ≤ ((N/H:ℕ):ℝ) := Nat.cast_nonneg _
  have hh := mul_le_mul_of_nonneg_left hH h0
  have hl := mul_le_mul_of_nonneg_left hn hlam
  simp only [Nat.cast_mul, mul_one] at hh hl
  nlinarith

theorem exists_regularization_block_control {lam : ℝ} (hlam : 0 < lam) :
    ∃ H N₀ : ℕ, 0 < H ∧ ∀ N ≥ N₀,
      0 < N ∧ 0 < N/H ∧ N/(N/H)+1 ≤ 2*H ∧
      ((N/H:ℕ):ℝ) ≤ lam*(N:ℝ) ∧
      (2:ℝ)^(N/(N/H)+2) ≤ ((2:ℝ)^N)^lam := by
  obtain ⟨H,hH⟩ := exists_nat_gt (1/lam)
  have hHp : 0 < H := by
    have hp : 0 < (H:ℝ) := (one_div_pos.mpr hlam).trans hH
    exact_mod_cast hp
  have hHl : 1 ≤ lam*(H:ℝ) := by
    have := (div_lt_iff₀ hlam).mp hH
    nlinarith
  obtain ⟨M,hM⟩ := exists_nat_gt (((2*H+1:ℕ):ℝ)/lam)
  refine ⟨H,max H M,hHp,?_⟩
  intro N hN
  have hHN : H ≤ N := (le_max_left _ _).trans hN
  have hMN : M ≤ N := (le_max_right _ _).trans hN
  have hc := division_blocks_control hHp hHN
  refine ⟨lt_of_lt_of_le hHp hHN,hc.1,hc.2,division_block_width hlam.le hHl,?_⟩
  have hreal : ((2*H+1:ℕ):ℝ) ≤ (N:ℝ)*lam := by
    have hm := (div_lt_iff₀ hlam).mp hM
    have hn : (M:ℝ) ≤ N := by exact_mod_cast hMN
    nlinarith
  have hcount : ((N/(N/H)+2:ℕ):ℝ) ≤ (N:ℝ)*lam := by
    have hh : N/(N/H)+2 ≤ 2*H+1 := by omega
    have hhR : ((N/(N/H)+2:ℕ):ℝ) ≤ ((2*H+1:ℕ):ℝ) := by exact_mod_cast hh
    exact hhR.trans hreal
  rw [← Real.rpow_natCast (2:ℝ) (N/(N/H)+2), ← Real.rpow_natCast (2:ℝ) N,
    ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hcount

theorem blockDepth_brackets {N n B : ℕ} (hn : n ≤ N) (hB : 0 < B) :
    let i := (N-n)/B
    i < N/B+1 ∧ blockDepth N B (i+1) ≤ n ∧ n ≤ blockDepth N B i ∧
      blockDepth N B i-n ≤ B ∧ n-blockDepth N B (i+1) ≤ B := by
  dsimp only
  have hlo := Nat.div_mul_le_self (N-n) B
  have hhi := Nat.lt_mul_div_succ (N-n) hB
  have hi : (N-n)/B ≤ N/B := Nat.div_le_div_right (Nat.sub_le _ _)
  simp only [blockDepth]
  rw [Nat.mul_comm B] at hhi
  have hgap := blockDepth_gap N B ((N-n)/B)
  dsimp only [blockDepth] at hgap
  omega

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Frostman_FrostmanProfileCells
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory Set Metric
open scoped ENNReal

theorem fixed_constant_absorbed {lam : ℝ} (hlam : 0 < lam) (C : ℝ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, C ≤ ((2:ℝ)^N)^lam := by
  have hb : 1 < (2:ℝ)^lam := Real.one_lt_rpow (by norm_num) hlam
  obtain ⟨N₀,hN₀⟩ := pow_unbounded_of_one_lt C hb
  refine ⟨N₀,fun N hN => ?_⟩
  have hh := hN₀.le.trans (pow_le_pow_right₀ hb.le hN)
  rw [← Real.rpow_mul_natCast (by norm_num : (0:ℝ) ≤ 2),mul_comm,
    Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 2)] at hh
  exact hh

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_AngularUniformAbsorption
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

theorem fixed_linear_subpower (C : ℝ) (hC : 0 ≤ C) {e : ℝ} (he : 0 < e) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, C*(1+2*(N:ℝ)) ≤ ((2:ℝ)^N)^e := by
  obtain ⟨N₁,hN₁⟩ := fixed_constant_absorbed (half_pos he) C
  obtain ⟨N₂,hN₂⟩ := fixed_polynomial_subpower 1 (half_pos he)
  refine ⟨max N₁ N₂,?_⟩
  intro N hN
  have hc := hN₁ N ((le_max_left _ _).trans hN)
  have hp := hN₂ N ((le_max_right _ _).trans hN)
  simp only [pow_one] at hp
  have hlin : 1+2*(N:ℝ) ≤ ((2:ℝ)^N)^(e/2) := by
    have hn : 0 ≤ (N:ℝ) := Nat.cast_nonneg N
    linarith
  calc
    _ ≤ C*((2:ℝ)^N)^(e/2) := mul_le_mul_of_nonneg_left hlin hC
    _ ≤ ((2:ℝ)^N)^(e/2)*((2:ℝ)^N)^(e/2) :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    _ = _ := by rw [← Real.rpow_add (by positivity)]; congr 1; ring

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_DyadicCube
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Dyadic cubes in the ambient dimension of the manuscript

Half-open cubes partition without boundary overlaps. Their centers and
Euclidean diameter bounds use the same original ambient coordinates as the
distance measure.
-/

namespace Falconer
open Set MeasureTheory

theorem DyadicCube.measurable {d : ℕ} (Q : DyadicCube d) : MeasurableSet Q.carrier := by
  simp only [carrier, ofPred_forall]
  apply MeasurableSet.iInter
  intro i
  exact (measurableSet_le measurable_const (EuclideanSpace.proj i).continuous.measurable).inter
    (measurableSet_lt (EuclideanSpace.proj i).continuous.measurable measurable_const)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_DyadicTree
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite dyadic trees in the original ambient dimension

All descendants use half-open carriers. Equal-depth cells are disjoint and
partition the parent, so restriction to them is an exact measure splitting.
-/

namespace Falconer
open Set MeasureTheory
attribute [local instance] Classical.propDecidable

theorem card_cubePaths (d n : ℕ) : (cubePaths d n).card = 2^(d*n) := by
  induction n with
  | zero => simp [cubePaths]
  | succ n ih =>
    rw [cubePaths, Finset.card_biUnion]
    · have hc (b : Fin d → Bool) : Function.Injective (List.cons b) :=
        fun _ _ h => (List.cons.inj h).2
      simp only [Finset.card_image_of_injective _ (hc _), ih,
        Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
        Fintype.card_fin, smul_eq_mul]
      rw [Nat.mul_succ, pow_add]
      exact Nat.mul_comm _ _
    · intro b _ c _ hbc
      apply Finset.disjoint_left.mpr
      intro p hp hq
      obtain ⟨p', _, hp'⟩ := Finset.mem_image.mp hp
      obtain ⟨q', _, hq'⟩ := Finset.mem_image.mp hq
      exact hbc (List.cons.inj (hp'.trans hq'.symm)).1

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_AllDimensionalRegularizationLabels
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Upward regularization labels in arbitrary dimension

The label-preservation argument applies to all-dimensional dyadic paths.
Each extension retains or removes a whole previous child group.
-/

namespace Falconer.Regularization

variable {d : ℕ}

theorem labeledChildren_eq {L : Finset (CellPath d)} {f : CellPath d → List ℕ}
    {a b : ℕ} {p q : CellPath d} (ha : p.take a = q.take a) (hf : f p = f q) :
    labeledChildren L f a b p = labeledChildren L f a b q := by
  classical
  simp only [labeledChildren, ha, hf]

theorem labeledChildren_nonempty {L : Finset (CellPath d)} (f : CellPath d → List ℕ)
    (a b : ℕ) {p : CellPath d} (hp : p ∈ L) :
    (labeledChildren L f a b p).Nonempty := by
  classical
  exact Finset.image_nonempty.mpr ⟨p, by simp [hp]⟩

theorem extendLabel_old {L : Finset (CellPath d)} {f : CellPath d → List ℕ}
    {a b : ℕ} {p q : CellPath d} (h : extendLabel L a b f p = extendLabel L a b f q) :
    f p = f q := (List.cons.inj h).2

theorem extendLabel_local {L : Finset (CellPath d)} {f : CellPath d → List ℕ}
    {a b : ℕ} {p q : CellPath d} (ha : p.take a = q.take a) :
    extendLabel L a b f p = extendLabel L a b f q ↔ f p = f q := by
  constructor
  · exact extendLabel_old
  · intro hf
    simp only [extendLabel, labeledChildren_eq ha hf, hf]

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_AllDimensionalRegularizationCardinality
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Dimension-dependent counts for regularization labels

A selected-depth gap of length b-a has at most 2^(d*(b-a))
children, so its logarithmic count bin has d*(b-a)+1 possibilities.
The number of final labels is polynomial in terminal depth when the
number of selected blocks is fixed.
-/

namespace Falconer.Regularization
variable {d : ℕ}

theorem labeledChildren_subset_extensions {N a b : ℕ} (hab : a ≤ b) (hbN : b ≤ N)
    {L : Finset (CellPath d)} (hL : L ⊆ cubePaths d N) (f : CellPath d → List ℕ)
    (p : CellPath d) :
    labeledChildren L f a b p ⊆ (cubePaths d (b-a)).image (fun q => p.take a ++ q) := by
  classical
  intro c hc
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hc
  obtain ⟨hq,ha,_⟩ := Finset.mem_filter.mp hq
  have hlen : q.length = N := (mem_cubePaths d N q).mp (hL hq)
  refine Finset.mem_image.mpr ⟨(q.take b).drop a, ?_, ?_⟩
  · simp only [mem_cubePaths, List.length_drop, List.length_take, hlen,
      Nat.min_eq_left hbN]
  · have he := List.take_append_drop a (q.take b)
    simpa only [List.take_take, Nat.min_eq_left hab, ha] using he

theorem labeledChildren_card_le {N a b : ℕ} (hab : a ≤ b) (hbN : b ≤ N)
    {L : Finset (CellPath d)} (hL : L ⊆ cubePaths d N) (f : CellPath d → List ℕ)
    (p : CellPath d) : (labeledChildren L f a b p).card ≤ 2 ^ (d*(b-a)) :=
  (Finset.card_le_card (labeledChildren_subset_extensions hab hbN hL f p)).trans
    (Finset.card_image_le.trans_eq (card_cubePaths d (b-a)))

theorem child_bin_le {N a b : ℕ} (hab : a ≤ b) (hbN : b ≤ N)
    {L : Finset (CellPath d)} (hL : L ⊆ cubePaths d N) (f : CellPath d → List ℕ)
    (p : CellPath d) : Nat.log 2 (labeledChildren L f a b p).card ≤ d*(b-a) := by
  have hc := labeledChildren_card_le hab hbN hL f p
  have := Nat.log_mono_right (b := 2) hc
  simpa only [Nat.log_pow (by decide : 1 < 2)] using this

theorem extendLabel_card_le {N a b : ℕ} (hab : a ≤ b) (hbN : b ≤ N)
    {L : Finset (CellPath d)} (hL : L ⊆ cubePaths d N) (f : CellPath d → List ℕ) :
    (L.image (extendLabel L a b f)).card ≤ (d*(b-a)+1) * (L.image f).card := by
  classical
  let S := (Finset.range (d*(b-a)+1)).product (L.image f)
  have hs : L.image (extendLabel L a b f) ⊆ S.image (fun z => z.1 :: z.2) := by
    intro T hT
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hT
    exact Finset.mem_image.mpr ⟨(Nat.log 2 (labeledChildren L f a b p).card, f p),
      Finset.mem_product.mpr ⟨Finset.mem_range.mpr
        (Nat.lt_succ_of_le (child_bin_le hab hbN hL f p)),
        Finset.mem_image.mpr ⟨p,hp,rfl⟩⟩,rfl⟩
  calc
    _ ≤ (S.image (fun z => z.1 :: z.2)).card := Finset.card_le_card hs
    _ ≤ S.card := Finset.card_image_le
    _ = _ := by simp [S]

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_RegularizationClasses
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Regularization classes on the original all-dimensional dyadic tree

Classes are literal disjoint unions of half-open leaves. The measure
identities and the discarded mass bounds hold for the original law.
-/

namespace Falconer.Regularization
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem leafUnion_measurable (Q : DyadicCube d) (L : Finset (CellPath d)) :
    MeasurableSet (leafUnion Q L) :=
  Finset.measurableSet_biUnion _ (fun p _ => (Q.descendant p).measurable)

theorem leafUnion_subset (Q : DyadicCube d) (_hQ : 0 < Q.side)
    (L : Finset (CellPath d)) : leafUnion Q L ⊆ Q.carrier := by
  intro z hz
  obtain ⟨p,_,hp⟩ := mem_iUnion₂.mp hz
  exact Q.descendant_subset p hp

theorem leafUnion_disjoint (Q : DyadicCube d) (_hQ : 0 < Q.side) {N : ℕ}
    {L T : Finset (CellPath d)} (hL : L ⊆ cubePaths d N)
    (hT : T ⊆ cubePaths d N) (h : Disjoint L T) :
    Disjoint (leafUnion Q L) (leafUnion Q T) := by
  apply Set.disjoint_left.mpr
  intro z hz hz'
  obtain ⟨p,hp,hzp⟩ := mem_iUnion₂.mp hz
  obtain ⟨q,hq,hzq⟩ := mem_iUnion₂.mp hz'
  have hne : p ≠ q := by
    intro he; subst q; exact Finset.disjoint_left.mp h hp hq
  exact Set.disjoint_left.mp (Q.descendants_disjoint
    ((mem_cubePaths _ _ _).mp (hL hp) |>.trans ((mem_cubePaths _ _ _).mp (hT hq)).symm)
    hne) hzp hzq

theorem measure_leafUnion (Q : DyadicCube d) (_hQ : 0 < Q.side) (μ : Measure (Space d))
    {N : ℕ} {L : Finset (CellPath d)} (hL : L ⊆ cubePaths d N) :
    μ (leafUnion Q L) = ∑ p ∈ L, μ (Q.descendant p).carrier := by
  apply measure_biUnion_finset
  · intro p hp q hq hne
    exact Q.descendants_disjoint
      (((mem_cubePaths _ _ _).mp (hL hp)).trans ((mem_cubePaths _ _ _).mp (hL hq)).symm)
      hne
  · intro p _; exact (Q.descendant p).measurable

theorem discarded_leaves_mass (Q : DyadicCube d) (hQ : 0 < Q.side)
    (μ : Measure (Space d)) (N : ℕ) (t : ℝ≥0∞) :
    μ (leafUnion Q (cubePaths d N \ retainedLeaves Q μ N t)) ≤ (2 : ℝ≥0∞)^(d*N) * t := by
  classical
  rw [measure_leafUnion Q hQ μ Finset.sdiff_subset]
  calc
    _ ≤ ∑ _p ∈ cubePaths d N \ retainedLeaves Q μ N t, t := by
      apply Finset.sum_le_sum
      intro p hp
      have hp' := Finset.mem_sdiff.mp hp
      have : ¬ t ≤ μ (Q.descendant p).carrier := by
        intro ht
        exact hp'.2 (Finset.mem_filter.mpr ⟨hp'.1,ht⟩)
      exact (lt_of_not_ge this).le
    _ ≤ (2 : ℝ≥0∞)^(d*N) * t := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      apply mul_le_mul_left
      exact_mod_cast (Finset.card_le_card Finset.sdiff_subset).trans (le_of_eq (card_cubePaths d N))

theorem classLeaves_disjoint (L : Finset (CellPath d))
    (f : CellPath d → List ℕ) {T U : List ℕ} (h : T ≠ U) :
    Disjoint (classLeaves L f T) (classLeaves L f U) := by
  classical
  apply Finset.disjoint_left.mpr
  intro p hp hq
  exact h ((Finset.mem_filter.mp hp).2.symm.trans (Finset.mem_filter.mp hq).2)

theorem discarded_classes_mass (Q : DyadicCube d) (μ : Measure (Space d))
    (L : Finset (CellPath d)) (f : CellPath d → List ℕ)
    (t : ℝ≥0∞) :
    μ (⋃ T ∈ (L.image f).filter (fun T => classMeasure Q μ L f T univ < t),
      leafUnion Q (classLeaves L f T)) ≤ ((L.image f).card : ℝ≥0∞) * t := by
  classical
  calc
    _ ≤ ∑ T ∈ (L.image f).filter (fun T => classMeasure Q μ L f T univ < t),
        μ (leafUnion Q (classLeaves L f T)) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _T ∈ (L.image f).filter (fun T => classMeasure Q μ L f T univ < t), t := by
      apply Finset.sum_le_sum
      intro T hT
      simpa only [classMeasure, Measure.restrict_apply_univ] using (Finset.mem_filter.mp hT).2.le
    _ ≤ _ := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      apply mul_le_mul_left
      exact_mod_cast (Finset.card_filter_le (s := L.image f)
        (fun T => classMeasure Q μ L f T univ < t))

theorem normalizedClass_probability (Q : DyadicCube d) (μ : Measure (Space d))
    [IsFiniteMeasure μ] (L : Finset (CellPath d))
    (f : CellPath d → List ℕ) (T : List ℕ)
    (h : classMeasure Q μ L f T univ ≠ 0) :
    IsProbabilityMeasure (normalizedClass Q μ L f T) := by
  constructor
  simp only [normalizedClass, Measure.smul_apply, smul_eq_mul]
  apply ENNReal.inv_mul_cancel h
  simp only [classMeasure, Measure.restrict_apply_univ]
  exact measure_ne_top _ _

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_LeafMassBins
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Original leaf mass bins with the dimension-dependent cutoff -/

namespace Falconer.Regularization
open MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem massBinCandidates_nonempty {N : ℕ} {w : ℝ}
    (hw : 1 ≤ (2:ℝ)^((d+2)*N)*w) : (massBinCandidates d N w).Nonempty := by
  classical
  exact ⟨0,by simp [massBinCandidates,hw]⟩

theorem leafMassBin_le (N : ℕ) (w : ℝ) : leafMassBin d N w ≤ (d+2)*N := by
  classical
  unfold leafMassBin
  split_ifs with h
  · exact Nat.le_of_lt_succ (Finset.mem_range.mp
      (Finset.mem_filter.mp ((massBinCandidates d N w).max'_mem h)).1)
  · omega

theorem leafMassBin_lower {N : ℕ} {w : ℝ} (hw : 1 ≤ (2:ℝ)^((d+2)*N)*w) :
    (2:ℝ)^(leafMassBin d N w) ≤ (2:ℝ)^((d+2)*N)*w := by
  classical
  unfold leafMassBin
  rw [dite_eq_left (massBinCandidates_nonempty hw)]
  exact (Finset.mem_filter.mp ((massBinCandidates d N w).max'_mem (massBinCandidates_nonempty hw))).2

theorem leafMassBin_upper {N : ℕ} {w : ℝ} (hw : w ≤ 1) :
    (2:ℝ)^((d+2)*N)*w < (2:ℝ)^(leafMassBin d N w+1) := by
  classical
  by_cases hk : leafMassBin d N w < (d+2)*N
  · by_contra h
    have hm : leafMassBin d N w+1 ∈ massBinCandidates d N w := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),not_lt.mp h⟩
    have hh : leafMassBin d N w+1 ≤ leafMassBin d N w := by
      conv_rhs => rw [leafMassBin, dite_eq_left ⟨_,hm⟩]
      exact Finset.le_max' _ _ hm
    omega
  · have he : leafMassBin d N w = (d+2)*N := by have := leafMassBin_le (d := d) N w; omega
    rw [he, pow_succ]
    have hp : 0 < (2:ℝ)^((d+2)*N) := by positivity
    nlinarith

theorem leafBinEndpoint_pos (N k : ℕ) : 0 < leafBinEndpoint d N k := by
  unfold leafBinEndpoint; positivity

theorem leaf_mass_bin_bounds {N : ℕ} {w : ℝ}
    (hlo : 1 ≤ (2:ℝ)^((d+2)*N)*w) (hhi : w ≤ 1) :
    leafBinEndpoint d N (leafMassBin d N w) ≤ w ∧
      w < 2 * leafBinEndpoint d N (leafMassBin d N w) := by
  have hp : 0 < (2:ℝ)^((d+2)*N) := by positivity
  constructor
  · exact (div_le_iff₀ hp).mpr (by simpa [mul_comm] using leafMassBin_lower hlo)
  · have hu := leafMassBin_upper (d := d) (N := N) hhi
    rw [pow_succ] at hu
    unfold leafBinEndpoint
    rw [← mul_div_assoc]
    exact (lt_div_iff₀ hp).mpr (by simpa only [mul_comm] using hu)

theorem sourceLeafLabel_card_le (Q : DyadicCube d) (μ : Measure (Space d)) (N : ℕ)
    (L : Finset (CellPath d)) : (L.image (sourceLeafLabel Q μ N)).card ≤ (d+2)*N+1 := by
  classical
  have hs : L.image (sourceLeafLabel Q μ N) ⊆
      (Finset.range ((d+2)*N+1)).image (fun k => [k]) := by
    intro T hT
    obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp hT
    exact Finset.mem_image.mpr ⟨leafMassBin d N (μ (Q.descendant p).carrier).toReal,
      Finset.mem_range.mpr (by have := leafMassBin_le (d := d) N (μ (Q.descendant p).carrier).toReal; omega),rfl⟩
  exact (Finset.card_le_card hs).trans (Finset.card_image_le.trans (by simp))

theorem retained_leaf_mass_bin_bounds (Q : DyadicCube d) (μ : Measure (Space d))
    [IsProbabilityMeasure μ] (N : ℕ) {p : CellPath d}
    (hp : p ∈ retainedLeaves Q μ N ((2:ℝ≥0∞)^((d+2)*N))⁻¹) :
    let w := (μ (Q.descendant p).carrier).toReal
    leafBinEndpoint d N (leafMassBin d N w) ≤ w ∧ w < 2*leafBinEndpoint d N (leafMassBin d N w) := by
  have hm := (Finset.mem_filter.mp hp).2
  have ht := ENNReal.toReal_mono (measure_ne_top μ _) hm
  simp only [ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_ofNat] at ht
  have hp : 0 < (2:ℝ)^((d+2)*N) := by positivity
  apply leaf_mass_bin_bounds
  · exact (inv_le_iff_one_le_mul₀' hp).mp ht
  · have hh : μ (Q.descendant p).carrier ≤ 1 := prob_le_one
    exact (ENNReal.toReal_le_toReal (measure_ne_top μ _) ENNReal.one_ne_top).mpr hh

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_BlockRegularization
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# All-dimensional block regularization

The upward labels preserve complete child groups at every selected depth.
Count bins cost d*N+1 possibilities and leaf mass bins cost (d+2)*N+1.
-/

namespace Falconer.Regularization
variable {d : ℕ}

theorem blockDepth_antitone (N B : ℕ) : Antitone (blockDepth N B) := by
  intro i j hij
  exact Nat.sub_le_sub_left (Nat.mul_le_mul_right B hij) N

theorem blockDepth_terminal (N : ℕ) {B : ℕ} (hB : 0 < B) :
    blockDepth N B (N/B+1) = 0 := by
  have h := Nat.lt_mul_div_succ N hB
  simp only [blockDepth]
  rw [Nat.mul_comm] at h
  omega

theorem blockLabel_old (L : Finset (CellPath d)) (N B : ℕ) (f : CellPath d → List ℕ)
    {i j : ℕ} (hij : i ≤ j) {p q : CellPath d}
    (he : blockLabel L N B f j p = blockLabel L N B f j q) :
    blockLabel L N B f i p = blockLabel L N B f i q := by
  induction j with
  | zero =>
    have : i = 0 := by omega
    subst i
    exact he
  | succ j ih =>
    by_cases heq : i = j+1
    · simpa only [heq] using he
    · exact ih (by omega) (extendLabel_old he)

theorem blockLabel_local (L : Finset (CellPath d)) (N B : ℕ) (f : CellPath d → List ℕ)
    {i j a : ℕ} (hij : i ≤ j) (ha : blockDepth N B i ≤ a)
    {p q : CellPath d} (hpq : p.take a = q.take a) :
    blockLabel L N B f j p = blockLabel L N B f j q ↔
      blockLabel L N B f i p = blockLabel L N B f i q := by
  induction j with
  | zero =>
    have : i = 0 := by omega
    subst i
    rfl
  | succ j ih =>
    by_cases heq : i = j+1
    · subst i; rfl
    · have hji : i ≤ j := by omega
      rw [blockLabel, extendLabel_local (take_eq_of_take_eq
        ((blockDepth_antitone N B (by omega : i ≤ j+1)).trans ha) hpq)]
      exact ih hji

theorem block_final_children (L : Finset (CellPath d)) (N B : ℕ) (f : CellPath d → List ℕ)
    {i K : ℕ} (hi : i < K) (p : CellPath d) :
    labeledChildren L (blockLabel L N B f K)
      (blockDepth N B (i+1)) (blockDepth N B i) p =
    labeledChildren L (blockLabel L N B f i)
      (blockDepth N B (i+1)) (blockDepth N B i) p := by
  classical
  apply congrArg (Finset.image (List.take (blockDepth N B i)))
  apply Finset.filter_congr
  intro q _
  constructor
  · rintro ⟨ha,hf⟩
    exact ⟨ha,blockLabel_old L N B f (by omega) hf⟩
  · rintro ⟨ha,hf⟩
    refine ⟨ha,(blockLabel_local L N B f (by omega : i+1 ≤ K) le_rfl ha).mpr ?_⟩
    exact (extendLabel_local ha).mpr hf

theorem block_final_bin_eq (L : Finset (CellPath d)) (N B : ℕ) (f : CellPath d → List ℕ)
    {i K : ℕ} (hi : i < K) {p q : CellPath d}
    (hclass : blockLabel L N B f K p = blockLabel L N B f K q) :
    Nat.log 2 (labeledChildren L (blockLabel L N B f K)
      (blockDepth N B (i+1)) (blockDepth N B i) p).card =
    Nat.log 2 (labeledChildren L (blockLabel L N B f K)
      (blockDepth N B (i+1)) (blockDepth N B i) q).card := by
  rw [block_final_children L N B f hi,block_final_children L N B f hi]
  exact (List.cons.inj (blockLabel_old L N B f (by omega : i+1 ≤ K) hclass)).1

theorem blockLabel_card_le {L : Finset (CellPath d)} {N : ℕ} (hL : L ⊆ cubePaths d N)
    (B : ℕ) (f : CellPath d → List ℕ) (K : ℕ) :
    (L.image (blockLabel L N B f K)).card ≤ (d*N+1)^K * (L.image f).card := by
  classical
  induction K with
  | zero => simp [blockLabel]
  | succ K ih =>
    have hs := extendLabel_card_le (blockDepth_antitone N B (Nat.le_succ K))
      (Nat.sub_le N (K*B)) hL (blockLabel L N B f K)
    have hb : d*(blockDepth N B K-blockDepth N B (K+1))+1 ≤ d*N+1 :=
      Nat.add_le_add_right (Nat.mul_le_mul_left d ((Nat.sub_le _ _).trans (Nat.sub_le N (K*B)))) 1
    calc
      _ ≤ (d*N+1) * (L.image (blockLabel L N B f K)).card :=
        hs.trans (Nat.mul_le_mul_right _ hb)
      _ ≤ (d*N+1)*((d*N+1)^K*(L.image f).card) := Nat.mul_le_mul_left _ ih
      _ = _ := by rw [pow_succ]; ac_rfl

theorem regularization_label_count (Q : DyadicCube d) (μ : MeasureTheory.Measure (Space d))
    (N B : ℕ) :
    ((regularizationLeaves Q μ N).image (regularizationLabel Q μ N B)).card ≤
      (d*N+1)^(N/B+1) * ((d+2)*N+1) := by
  classical
  exact (blockLabel_card_le (Finset.filter_subset _ _) B (sourceLeafLabel Q μ N) _).trans
    (Nat.mul_le_mul_left _ (sourceLeafLabel_card_le Q μ N _))

theorem regularization_label_mass_bin (Q : DyadicCube d) (μ : MeasureTheory.Measure (Space d))
    (N B : ℕ) {p q : CellPath d}
    (h : regularizationLabel Q μ N B p = regularizationLabel Q μ N B q) :
    leafMassBin d N (μ (Q.descendant p).carrier).toReal =
      leafMassBin d N (μ (Q.descendant q).carrier).toReal := by
  have := blockLabel_old (regularizationLeaves Q μ N) N B (sourceLeafLabel Q μ N)
    (Nat.zero_le (N/B+1)) h
  exact List.singleton_inj.mp this

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_RegularizationSelection
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Selecting the regular classes with their original masses

Classes are disjoint unions of original leaves. Discarding small leaves
costs 2^(-2N), and discarding small classes costs their number times the
class threshold. No lower density of the original law is required.
-/

namespace Falconer.Regularization
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem regularizationSet_measurable (Q : DyadicCube d) (μ : Measure (Space d))
    (N B : ℕ) (T : List ℕ) : MeasurableSet (regularizationSet Q μ N B T) :=
  leafUnion_measurable Q _

theorem regularizationSet_disjoint (Q : DyadicCube d) (hQ : 0 < Q.side)
    (μ : Measure (Space d)) (N B : ℕ) {T U : List ℕ} (h : T ≠ U) :
    Disjoint (regularizationSet Q μ N B T) (regularizationSet Q μ N B U) :=
  leafUnion_disjoint Q hQ
    (fun _ hp => (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1)
    (fun _ hp => (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1)
    (classLeaves_disjoint _ _ h)

theorem regularizationSet_mass (Q : DyadicCube d) (μ : Measure (Space d))
    (N B : ℕ) (t : ℝ≥0∞) {T : List ℕ} (hT : T ∈ regularizationIndex Q μ N B t) :
    t ≤ μ (regularizationSet Q μ N B T) := by
  simpa only [regularizationSet,classMeasure,Measure.restrict_apply_univ] using (Finset.mem_filter.mp hT).2

theorem regularization_small_leaves_mass (Q : DyadicCube d) (hQ : 0 < Q.side)
    (μ : Measure (Space d)) (N : ℕ) :
    μ (leafUnion Q (cubePaths d N \ regularizationLeaves Q μ N)) ≤ ((2 : ℝ≥0∞)^(2*N))⁻¹ := by
  apply (discarded_leaves_mass Q hQ μ N ((2 : ℝ≥0∞)^((d+2)*N))⁻¹).trans_eq
  rw [Nat.add_mul,pow_add,ENNReal.mul_inv (by simp) (by simp),← mul_assoc,
    ENNReal.mul_inv_cancel (by simp) (by simp),one_mul]

theorem regularization_discarded_mass (Q : DyadicCube d) (hQ : 0 < Q.side)
    (μ : Measure (Space d)) (N B : ℕ) (t : ℝ≥0∞) :
    μ (Q.carrier \ ⋃ T ∈ regularizationIndex Q μ N B t, regularizationSet Q μ N B T) ≤
      ((2 : ℝ≥0∞)^(2*N))⁻¹ + ((d*N+1)^(N/B+1)*((d+2)*N+1) : ℕ)*t := by
  let L := regularizationLeaves Q μ N
  let f := regularizationLabel Q μ N B
  let bad := (L.image f).filter (fun T => classMeasure Q μ L f T univ < t)
  have hsub : (Q.carrier \ ⋃ T ∈ regularizationIndex Q μ N B t, regularizationSet Q μ N B T) ⊆
      leafUnion Q (cubePaths d N \ L) ∪ ⋃ T ∈ bad, leafUnion Q (classLeaves L f T) := by
    intro x hx
    obtain ⟨p,hp,hxp⟩ := Q.mem_descendant_at_depth N hx.1
    by_cases hpL : p ∈ L
    · have hf : f p ∈ L.image f := Finset.mem_image.mpr ⟨p,hpL,rfl⟩
      by_cases hb : classMeasure Q μ L f (f p) univ < t
      · exact Or.inr (mem_iUnion₂.mpr ⟨f p,Finset.mem_filter.mpr ⟨hf,hb⟩,
          mem_iUnion₂.mpr ⟨p,Finset.mem_filter.mpr ⟨hpL,rfl⟩,hxp⟩⟩)
      · have hi : f p ∈ regularizationIndex Q μ N B t :=
          Finset.mem_filter.mpr ⟨hf,le_of_not_gt hb⟩
        exact (hx.2 (mem_iUnion₂.mpr ⟨f p,hi,
          mem_iUnion₂.mpr ⟨p,Finset.mem_filter.mpr ⟨hpL,rfl⟩,hxp⟩⟩)).elim
    · exact Or.inl (mem_iUnion₂.mpr ⟨p,Finset.mem_sdiff.mpr ⟨hp,hpL⟩,hxp⟩)
  apply (measure_mono hsub).trans (measure_union_le _ _ |>.trans ?_)
  apply add_le_add (regularization_small_leaves_mass Q hQ μ N)
  dsimp only [bad]
  apply (discarded_classes_mass Q μ L f t).trans
  exact mul_le_mul' (by exact_mod_cast regularization_label_count Q μ N B) le_rfl

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_RegularizationCount
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial class count and discarded mass in every dimension -/

namespace Falconer.Regularization
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem regularization_discarded_global (Q : DyadicCube d) (hQ : 0 < Q.side)
    (μ : Measure (Space d)) (hcarry : μ Q.carrierᶜ = 0)
    {N H : ℕ} (hH : 0 < H) (hNH : H ≤ N) (hdN : d+3 ≤ N) (t : ℝ≥0∞) :
    μ (⋃ T ∈ regularizationIndex Q μ N (N/H) t, regularizationSet Q μ N (N/H) T)ᶜ ≤
      ((2:ℝ≥0∞)^(2*N))⁻¹ + (N^(4*H+2):ℕ)*t := by
  let U := ⋃ T ∈ regularizationIndex Q μ N (N/H) t, regularizationSet Q μ N (N/H) T
  have hsub : Uᶜ ⊆ (Q.carrier \ U) ∪ Q.carrierᶜ := by
    intro x hx
    by_cases h : x ∈ Q.carrier
    · exact Or.inl ⟨h,hx⟩
    · exact Or.inr h
  have hc : (d*N+1)^(N/(N/H)+1)*((d+2)*N+1) ≤ N^(4*H+2) := by
    have hN : 1 ≤ N := by omega
    have h₁ : d*N+1 ≤ N^2 := by nlinarith
    have h₂ : (d+2)*N+1 ≤ N^2 := by nlinarith
    have hb := (PlanarFalconer.division_blocks_control hH hNH).2
    calc
      _ ≤ (N^2)^(2*H)*N^2 := Nat.mul_le_mul
        ((Nat.pow_le_pow_left h₁ _).trans (Nat.pow_le_pow_right (by positivity) hb)) h₂
      _ = _ := by rw [← pow_mul,← pow_add]; congr 1; omega
  calc
    _ ≤ μ (Q.carrier \ U) + μ Q.carrierᶜ := (measure_mono hsub).trans (measure_union_le _ _)
    _ = μ (Q.carrier \ U) := by rw [hcarry,add_zero]
    _ ≤ ((2:ℝ≥0∞)^(2*N))⁻¹ + ((d*N+1)^(N/(N/H)+1)*((d+2)*N+1):ℕ)*t :=
      regularization_discarded_mass Q hQ μ N (N/H) t
    _ ≤ _ := add_le_add le_rfl (mul_le_mul' (by exact_mod_cast hc) le_rfl)

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_CellwisePairDeletion
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Recombining local pair deletions with their original source-cell masses -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal BigOperators
variable {X Y ι : Type*} [MeasurableSpace X] [MeasurableSpace Y]

theorem conditional_pair_mass_reconstruct (μ : Measure X) (ν : Measure Y)
    [IsFiniteMeasure μ] [SFinite ν] (Q : Set X) (hQ : μ Q ≠ 0) (E : Set (X × Y)) :
    μ Q*((ProbabilityTheory.cond μ Q).prod ν) E = ((μ.restrict Q).prod ν) E := by
  rw [ProbabilityTheory.cond,Measure.prod_smul_left,Measure.smul_apply,smul_eq_mul,
    ← mul_assoc,ENNReal.mul_inv_cancel hQ (measure_ne_top μ Q),one_mul]

theorem cellwise_pair_deletion_bound (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν]
    (I : Finset ι) (Q : ι → Set X) (E : ι → Set (X × Y))
    (hQ : ∀ i ∈ I, MeasurableSet (Q i)) (hE : ∀ i ∈ I, MeasurableSet (E i))
    (hdisj : (I : Set ι).PairwiseDisjoint Q) (t : ℝ≥0∞)
    (hlocal : ∀ i ∈ I, ((μ.restrict (Q i)).prod ν) (E i) ≤ t*μ (Q i)) :
    (μ.prod ν) (⋃ i ∈ I, E i ∩ (Q i ×ˢ univ)) ≤ t*μ univ := by
  calc
    _ ≤ ∑ i ∈ I, (μ.prod ν) (E i ∩ (Q i ×ˢ univ)) := measure_biUnion_finset_le _ _
    _ = ∑ i ∈ I, ((μ.restrict (Q i)).prod ν) (E i) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Measure.restrict_prod_eq_prod_univ,Measure.restrict_apply (hE i hi)]
    _ ≤ ∑ i ∈ I, t*μ (Q i) := Finset.sum_le_sum hlocal
    _ = t*(∑ i ∈ I, μ (Q i)) := (Finset.mul_sum _ _ _).symm
    _ = t*μ (⋃ i ∈ I, Q i) := by rw [measure_biUnion_finset hdisj hQ]
    _ ≤ _ := mul_le_mul' le_rfl (measure_mono (subset_univ _))

theorem conditional_cellwise_pair_deletion (μ : Measure X) (ν : Measure Y)
    [IsFiniteMeasure μ] [SFinite ν] (I : Finset ι) (Q : ι → Set X) (E : ι → Set (X × Y))
    (hQ : ∀ i ∈ I, MeasurableSet (Q i)) (hE : ∀ i ∈ I, MeasurableSet (E i))
    (hpos : ∀ i ∈ I, μ (Q i) ≠ 0) (hdisj : (I : Set ι).PairwiseDisjoint Q) (t : ℝ≥0∞)
    (hlocal : ∀ i ∈ I, ((ProbabilityTheory.cond μ (Q i)).prod ν) (E i) ≤ t) :
    (μ.prod ν) (⋃ i ∈ I, E i ∩ (Q i ×ˢ univ)) ≤ t*μ univ := by
  apply cellwise_pair_deletion_bound μ ν I Q E hQ hE hdisj t
  intro i hi
  rw [← conditional_pair_mass_reconstruct μ ν (Q i) (hpos i hi) (E i),mul_comm t]
  exact mul_le_mul' le_rfl (hlocal i hi)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_RegularizedPotential
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite-scale inverse-distance potentials for the slicing kernels -/

namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal
variable {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]

theorem regularized_potential_dyadic (μ : Measure X)
    (x : X) {s : ℝ} (hs : 0 ≤ s) (g k : ℕ) :
    (∫⁻ y in ball x (1/(2:ℝ)^g),
      ENNReal.ofReal ((1/(dist x y+1/(2:ℝ)^(g+k)))^s) ∂μ) ≤
    ENNReal.ofReal (((2:ℝ)^g)^s)*μ (ball x (1/(2:ℝ)^g))+
      ∑ j ∈ Finset.range k, ENNReal.ofReal (((2:ℝ)^(g+j+1))^s)*
        μ (ball x (1/(2:ℝ)^(g+j))) := by
  let B := ball x (1/(2:ℝ)^g)
  let f : X → ℝ≥0∞ := fun y =>
    ENNReal.ofReal ((1/(dist x y+1/(2:ℝ)^(g+k)))^s)
  let F : X → ℝ≥0∞ := fun y =>
    B.indicator (fun _ => ENNReal.ofReal (((2:ℝ)^g)^s)) y+
      ∑ j ∈ Finset.range k,
        (ball x (1/(2:ℝ)^(g+j))).indicator
          (fun _ => ENNReal.ofReal (((2:ℝ)^(g+j+1))^s)) y
  have hpoint : B.indicator f ≤ F := by
    intro y
    change B.indicator f y ≤ B.indicator (fun _ => ENNReal.ofReal (((2:ℝ)^g)^s)) y+
      ∑ j ∈ Finset.range k, (ball x (1/(2:ℝ)^(g+j))).indicator
        (fun _ => ENNReal.ofReal (((2:ℝ)^(g+j+1))^s)) y
    by_cases hy : y ∈ B
    · rw [indicator_of_mem hy,show B.indicator (fun _ => ENNReal.ofReal (((2:ℝ)^g)^s)) y =
        ENNReal.ofReal (((2:ℝ)^g)^s) from indicator_of_mem hy _]
      have hi := inverse_power_dyadic (s := s)
        (by positivity : 0 < dist x y+1/(2:ℝ)^(g+k)) hs g k
        (by linarith [dist_nonneg (x := x) (y := y)])
      have hh := ENNReal.ofReal_le_ofReal hi
      rw [ENNReal.ofReal_add (by positivity) (Finset.sum_nonneg (fun j _ => by split_ifs <;> positivity)),
        ENNReal.ofReal_sum_of_nonneg (fun j _ => by split_ifs <;> positivity)] at hh
      apply hh.trans
      apply add_le_add le_rfl
      apply Finset.sum_le_sum
      intro j hj
      by_cases hdist : dist x y+1/(2:ℝ)^(g+k) < 1/(2:ℝ)^(g+j)
      · rw [ite_eq_left hdist]
        have hyj : y ∈ ball x (1/(2:ℝ)^(g+j)) := by
          rw [mem_ball,dist_comm]
          linarith [show (0:ℝ) < 1/(2:ℝ)^(g+k) by positivity]
        rw [indicator_of_mem hyj]
      · rw [ite_eq_right hdist,ENNReal.ofReal_zero]
        exact bot_le
    · rw [indicator_of_notMem hy]
      exact bot_le
  rw [← lintegral_indicator measurableSet_ball]
  apply (lintegral_mono hpoint).trans_eq
  change (∫⁻ y, B.indicator (fun _ => ENNReal.ofReal (((2:ℝ)^g)^s)) y+
      ∑ j ∈ Finset.range k, (ball x (1/(2:ℝ)^(g+j))).indicator
        (fun _ => ENNReal.ofReal (((2:ℝ)^(g+j+1))^s)) y ∂μ) = _
  rw [lintegral_add_left (measurable_const.indicator measurableSet_ball),
    lintegral_indicator_const measurableSet_ball,
    lintegral_finsetSum _ (fun j _ => measurable_const.indicator measurableSet_ball)]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  exact lintegral_indicator_const measurableSet_ball _

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_PotentialScale
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Geometric summation above the inverse-kernel exponent -/

namespace Falconer

theorem dyadic_potential_weight (n : ℕ) (s q : ℝ) :
    (((2:ℝ)^(n+1))^s)*(1/(2:ℝ)^n)^q =
      (2:ℝ)^s*(((2:ℝ)^n)^(s-q)) := by
  rw [pow_succ,Real.mul_rpow (by positivity) (by norm_num : (0:ℝ) ≤ 2),
    one_div,Real.inv_rpow (by positivity),Real.rpow_sub (by positivity)]
  ring

theorem dyadic_potential_start (n : ℕ) (s q : ℝ) :
    (((2:ℝ)^n)^s)*(1/(2:ℝ)^n)^q = (((2:ℝ)^n)^(s-q)) := by
  rw [one_div,Real.inv_rpow (by positivity),Real.rpow_sub (by positivity)]
  ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_PrefixCounting
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # All-dimensional prefix counts for regularized original measures -/

namespace Falconer.Regularization
variable {d : ℕ}


theorem prefixFiber_zero (C : Finset (CellPath d)) : prefixFiber C 0 [] = C := by
  classical
  simp [prefixFiber]

theorem prefixFiber_leaf {N : ℕ} {C : Finset (CellPath d)} (hC : C ⊆ cubePaths d N)
    {p : CellPath d} (hp : p ∈ C) : prefixFiber C N p = {p} := by
  classical
  ext q
  have hlen {path : CellPath d} (hpath : path ∈ C) : path.length = N :=
    (mem_cubePaths d N path).mp (hC hpath)
  simp only [prefixFiber, Finset.mem_filter, Finset.mem_singleton]
  constructor
  · rintro ⟨hq,he⟩
    simpa only [← hlen hq, List.take_length] using he
  · intro he; subst q
    exact ⟨hp,by rw [← hlen hp,List.take_length]⟩

theorem prefixFiber_card_sum {C : Finset (CellPath d)} {a b : ℕ} (hab : a ≤ b)
    (P : CellPath d) :
    (prefixFiber C a P).card =
      ∑ c ∈ prefixChildren C a b P, (prefixFiber C b c).card := by
  classical
  rw [Finset.card_eq_sum_card_image (List.take b) (prefixFiber C a P)]
  apply Finset.sum_congr rfl
  intro c hc
  rw [prefixFiber_parent_filter hab hc]

theorem prefixFiber_count_bounds {C : Finset (CellPath d)} {a b lo hi B : ℕ}
    (hab : a ≤ b) (P : CellPath d)
    (hbranch : B ≤ (prefixChildren C a b P).card ∧ (prefixChildren C a b P).card ≤ 2*B)
    (hchild : ∀ c ∈ prefixChildren C a b P,
      lo ≤ (prefixFiber C b c).card ∧ (prefixFiber C b c).card ≤ hi) :
    B*lo ≤ (prefixFiber C a P).card ∧ (prefixFiber C a P).card ≤ 2*B*hi := by
  classical
  rw [prefixFiber_card_sum hab]
  constructor
  · calc
      B*lo ≤ (prefixChildren C a b P).card*lo := Nat.mul_le_mul_right _ hbranch.1
      _ = ∑ _c ∈ prefixChildren C a b P, lo := by simp
      _ ≤ _ := Finset.sum_le_sum (fun c hc => (hchild c hc).1)
  · calc
      _ ≤ ∑ _c ∈ prefixChildren C a b P, hi := Finset.sum_le_sum (fun c hc => (hchild c hc).2)
      _ = (prefixChildren C a b P).card*hi := by simp
      _ ≤ 2*B*hi := Nat.mul_le_mul_right _ hbranch.2

theorem prefixChildren_class_eq (L : Finset (CellPath d)) (F : CellPath d → List ℕ)
    (a b : ℕ) {T : List ℕ} {p : CellPath d} (hp : p ∈ classLeaves L F T) :
    prefixChildren (classLeaves L F T) a b (p.take a) = labeledChildren L F a b p := by
  classical
  have hFp := (Finset.mem_filter.mp hp).2
  apply congrArg (Finset.image (List.take b))
  ext q
  simp only [prefixFiber, classLeaves, Finset.mem_filter, hFp]
  tauto

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_BlockLeafCounts
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # All-dimensional block-leaf counts for regularized original measures -/

namespace Falconer.Regularization
variable {d : ℕ}


theorem blockBin_pos (L : Finset (CellPath d)) (F : CellPath d → List ℕ)
    (N B i : ℕ) (p : CellPath d) : 0 < blockBin L F N B i p := by
  unfold blockBin; positivity

theorem blockProduct_pos (L : Finset (CellPath d)) (F : CellPath d → List ℕ)
    (N B i : ℕ) (p : CellPath d) : 0 < blockProduct L F N B i p := by
  exact Finset.prod_pos (fun j _ => blockBin_pos L F N B j p)

theorem blockClass_child_bounds (L : Finset (CellPath d)) (N B : ℕ) (f : CellPath d → List ℕ)
    {K i : ℕ} (hi : i < K) (p : CellPath d)
    {P : CellPath d}
    (hP : P ∈ (classLeaves L (blockLabel L N B f K) (blockLabel L N B f K p)).image
      (List.take (blockDepth N B (i+1)))) :
    let F := blockLabel L N B f K
    let C := classLeaves L F (F p)
    blockBin L F N B i p ≤ (prefixChildren C (blockDepth N B (i+1)) (blockDepth N B i) P).card ∧
      (prefixChildren C (blockDepth N B (i+1)) (blockDepth N B i) P).card ≤ 2*blockBin L F N B i p := by
  classical
  dsimp only
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hP
  rw [prefixChildren_class_eq L _ _ _ hq]
  have hqL := (Finset.mem_filter.mp hq).1
  have hclass := (Finset.mem_filter.mp hq).2
  unfold blockBin
  rw [block_final_bin_eq L N B f hi hclass.symm]
  have hpos := Finset.card_pos.mpr (labeledChildren_nonempty
    (blockLabel L N B f K) (blockDepth N B (i+1)) (blockDepth N B i) hqL)
  refine ⟨Nat.pow_log_le_self 2 (Nat.ne_of_gt hpos), ?_⟩
  have hu := Nat.lt_pow_succ_log_self (by decide : 1 < 2)
    (labeledChildren L (blockLabel L N B f K) (blockDepth N B (i+1)) (blockDepth N B i) q).card
  simpa only [pow_succ, Nat.mul_comm] using hu.le

theorem blockClass_leaf_count {N : ℕ} {L : Finset (CellPath d)} (hL : L ⊆ cubePaths d N)
    (B : ℕ) (f : CellPath d → List ℕ) (K : ℕ) (p : CellPath d)
    {i : ℕ} (hi : i ≤ K) {P : CellPath d}
    (hP : P ∈ (classLeaves L (blockLabel L N B f K) (blockLabel L N B f K p)).image
      (List.take (blockDepth N B i))) :
    let F := blockLabel L N B f K
    let C := classLeaves L F (F p)
    blockProduct L F N B i p ≤ (prefixFiber C (blockDepth N B i) P).card ∧
      (prefixFiber C (blockDepth N B i) P).card ≤ 2^i * blockProduct L F N B i p := by
  classical
  let F := blockLabel L N B f K
  let C := classLeaves L F (F p)
  have hC : C ⊆ cubePaths d N := fun q hq => hL (Finset.mem_filter.mp hq).1
  change blockProduct L F N B i p ≤ (prefixFiber C (blockDepth N B i) P).card ∧
    (prefixFiber C (blockDepth N B i) P).card ≤ 2^i * blockProduct L F N B i p
  change P ∈ C.image (List.take (blockDepth N B i)) at hP
  induction i generalizing P with
  | zero =>
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hP
    have hlen : q.length = N := (mem_cubePaths _ _ _).mp (hC hq)
    simp only [blockDepth, Nat.zero_mul, Nat.sub_zero, ← hlen, List.take_length]
    rw [show q.length = N from hlen, prefixFiber_leaf hC hq]
    simp [blockProduct]
  | succ i ih =>
    have hb := blockClass_child_bounds L N B f (by omega : i < K) p hP
    have hc := prefixFiber_count_bounds (blockDepth_antitone N B (Nat.le_succ i)) P hb
      (fun c hc => ih (by omega) (prefixChildren_mem_image hc))
    dsimp only [blockProduct] at hc ⊢
    rw [Finset.prod_range_succ]
    constructor
    · simpa only [Nat.mul_comm] using hc.1
    · have hh := hc.2
      convert hh using 1
      all_goals try with_reducible_and_instances rfl
      ring

theorem blockClass_root_count {N : ℕ} {L : Finset (CellPath d)} (hL : L ⊆ cubePaths d N)
    {B : ℕ} (hB : 0 < B) (f : CellPath d → List ℕ) {p : CellPath d} (hp : p ∈ L) :
    let K := N/B+1
    let F := blockLabel L N B f K
    let C := classLeaves L F (F p)
    blockProduct L F N B K p ≤ C.card ∧ C.card ≤ 2^K * blockProduct L F N B K p := by
  classical
  have hpC : p ∈ classLeaves L (blockLabel L N B f (N/B+1)) (blockLabel L N B f (N/B+1) p) := by
    simp [classLeaves,hp]
  have hc := blockClass_leaf_count hL B f (N/B+1) p (le_refl (N/B+1))
    (P := []) (by rw [blockDepth_terminal N hB]; exact Finset.mem_image.mpr ⟨p,hpC,rfl⟩)
  simpa only [blockDepth_terminal N hB, prefixFiber_zero] using hc

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Measures_PrefixMass
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # All-dimensional PrefixMass for regularized original measures -/

namespace Falconer.Regularization
variable {d : ℕ}

open Set MeasureTheory
open scoped ENNReal

theorem descendant_subset_take (Q : DyadicCube d) (_hQ : 0 < Q.side)
    (p : CellPath d) (a : ℕ) : (Q.descendant p).carrier ⊆ (Q.descendant (p.take a)).carrier := by
  have he := Q.descendant_append (p.take a) (p.drop a)
  rw [List.take_append_drop] at he
  rw [he]
  exact (Q.descendant (p.take a)).descendant_subset _

theorem leafUnion_inter_prefix (Q : DyadicCube d) (hQ : 0 < Q.side)
    {N a : ℕ} (ha : a ≤ N) {C : Finset (CellPath d)} (hC : C ⊆ cubePaths d N)
    {P : CellPath d} (hP : P.length = a) :
    (Q.descendant P).carrier ∩ leafUnion Q C = leafUnion Q (prefixFiber C a P) := by
  classical
  ext z
  constructor
  · rintro ⟨hzP,hzC⟩
    obtain ⟨q,hq,hzq⟩ := mem_iUnion₂.mp hzC
    have hqN := (mem_cubePaths _ _ _).mp (hC hq)
    have hlen : (q.take a).length = P.length := by simp [List.length_take,hqN,ha,hP]
    have he : q.take a = P := by
      by_contra hne
      exact Set.disjoint_left.mp (Q.descendants_disjoint hlen hne)
        (descendant_subset_take Q hQ q a hzq) hzP
    exact mem_iUnion₂.mpr ⟨q,by simp [prefixFiber,hq,he],hzq⟩
  · intro hz
    obtain ⟨q,hq,hzq⟩ := mem_iUnion₂.mp hz
    obtain ⟨hq,he⟩ := Finset.mem_filter.mp hq
    refine ⟨?_,mem_iUnion₂.mpr ⟨q,hq,hzq⟩⟩
    rw [← he]
    exact descendant_subset_take Q hQ q a hzq

theorem restriction_prefix_mass (Q : DyadicCube d) (hQ : 0 < Q.side) (μ : Measure (Space d))
    {N a : ℕ} (ha : a ≤ N) {C : Finset (CellPath d)} (hC : C ⊆ cubePaths d N)
    {P : CellPath d} (hP : P.length = a) :
    (μ.restrict (leafUnion Q C)) (Q.descendant P).carrier =
      ∑ q ∈ prefixFiber C a P, μ (Q.descendant q).carrier := by
  rw [Measure.restrict_apply (Q.descendant P).measurable,
    leafUnion_inter_prefix Q hQ ha hC hP]
  exact measure_leafUnion Q hQ μ (fun q hq => hC (Finset.mem_filter.mp hq).1)

theorem restriction_prefix_mass_real (Q : DyadicCube d) (hQ : 0 < Q.side)
    (μ : Measure (Space d)) [IsFiniteMeasure μ]
    {N a : ℕ} (ha : a ≤ N) {C : Finset (CellPath d)} (hC : C ⊆ cubePaths d N)
    {P : CellPath d} (hP : P.length = a) :
    ((μ.restrict (leafUnion Q C)) (Q.descendant P).carrier).toReal =
      ∑ q ∈ prefixFiber C a P, (μ (Q.descendant q).carrier).toReal := by
  rw [restriction_prefix_mass Q hQ μ ha hC hP, ENNReal.toReal_sum]
  intro q _
  exact measure_ne_top _ _

theorem restriction_prefix_mass_bounds (Q : DyadicCube d) (hQ : 0 < Q.side)
    (μ : Measure (Space d)) [IsFiniteMeasure μ]
    {N a : ℕ} (ha : a ≤ N) {C : Finset (CellPath d)} (hC : C ⊆ cubePaths d N)
    {P : CellPath d} (hP : P.length = a) {s : ℝ}
    (hm : ∀ q ∈ C, s ≤ (μ (Q.descendant q).carrier).toReal ∧
      (μ (Q.descendant q).carrier).toReal ≤ 2*s) :
    (prefixFiber C a P).card * s ≤
      ((μ.restrict (leafUnion Q C)) (Q.descendant P).carrier).toReal ∧
    ((μ.restrict (leafUnion Q C)) (Q.descendant P).carrier).toReal ≤
      (prefixFiber C a P).card * (2*s) := by
  rw [restriction_prefix_mass_real Q hQ μ ha hC hP]
  constructor
  · calc
      _ = ∑ _q ∈ prefixFiber C a P, s := by simp
      _ ≤ _ := Finset.sum_le_sum fun q hq => (hm q (Finset.mem_filter.mp hq).1).1
  · calc
      _ ≤ ∑ _q ∈ prefixFiber C a P, 2*s :=
        Finset.sum_le_sum fun q hq => (hm q (Finset.mem_filter.mp hq).1).2
      _ = _ := by simp

theorem restriction_total_mass_real (Q : DyadicCube d) (hQ : 0 < Q.side)
    (μ : Measure (Space d)) [IsFiniteMeasure μ]
    {N : ℕ} {C : Finset (CellPath d)} (hC : C ⊆ cubePaths d N) :
    (μ (leafUnion Q C)).toReal = ∑ q ∈ C, (μ (Q.descendant q).carrier).toReal := by
  rw [measure_leafUnion Q hQ μ hC, ENNReal.toReal_sum]
  intro q _; exact measure_ne_top _ _

theorem restriction_total_mass_bounds (Q : DyadicCube d) (hQ : 0 < Q.side)
    (μ : Measure (Space d)) [IsFiniteMeasure μ]
    {N : ℕ} {C : Finset (CellPath d)} (hC : C ⊆ cubePaths d N) {s : ℝ}
    (hm : ∀ q ∈ C, s ≤ (μ (Q.descendant q).carrier).toReal ∧
      (μ (Q.descendant q).carrier).toReal ≤ 2*s) :
    C.card*s ≤ (μ (leafUnion Q C)).toReal ∧
      (μ (leafUnion Q C)).toReal ≤ C.card*(2*s) := by
  rw [restriction_total_mass_real Q hQ μ hC]
  constructor
  · calc
      _ = ∑ _q ∈ C, s := by simp
      _ ≤ _ := Finset.sum_le_sum fun q hq => (hm q hq).1
  · calc
      _ ≤ ∑ _q ∈ C, 2*s := Finset.sum_le_sum fun q hq => (hm q hq).2
      _ = _ := by simp

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Measures_RegularizedMass
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # All-dimensional RegularizedMass for regularized original measures -/

namespace Falconer.Regularization
variable {d : ℕ}

open MeasureTheory Set
open scoped ENNReal

theorem regularization_class_leaf_bounds (Q : DyadicCube d) (μ : Measure (Space d))
    [IsProbabilityMeasure μ] (N B : ℕ) {p : CellPath d}
    (_hp : p ∈ regularizationLeaves Q μ N) :
    let L := regularizationLeaves Q μ N
    let F := regularizationLabel Q μ N B
    let s := leafBinEndpoint d N (leafMassBin d N (μ (Q.descendant p).carrier).toReal)
    0 < s ∧ ∀ q ∈ classLeaves L F (F p),
      s ≤ (μ (Q.descendant q).carrier).toReal ∧ (μ (Q.descendant q).carrier).toReal ≤ 2*s := by
  refine ⟨leafBinEndpoint_pos _ _,?_⟩
  intro q hq
  obtain ⟨hq,hF⟩ := Finset.mem_filter.mp hq
  have hb := retained_leaf_mass_bin_bounds Q μ N hq
  have he := regularization_label_mass_bin Q μ N B hF
  dsimp only at hb ⊢
  rw [he] at hb
  exact ⟨hb.1,hb.2.le⟩

theorem ratio_bounds_of_mass_bounds {x t s u v C : ℝ}
    (hs : 0 < s) (hu : 0 < u) (hv : 0 < v) (hC : 0 < C)
    (hx : u*s ≤ x ∧ x ≤ C*u*s) (ht : v*s ≤ t ∧ t ≤ C*v*s) :
    (u/v)/C ≤ x/t ∧ x/t ≤ C*(u/v) := by
  have htpos : 0 < t := (mul_pos hv hs).trans_le ht.1
  have hxn : 0 ≤ x := (mul_pos hu hs).le.trans hx.1
  constructor
  · have hh : (u*s)/(C*v*s) ≤ x/t := div_le_div₀ hxn hx.1 htpos ht.2
    rw [mul_div_mul_right _ _ hs.ne'] at hh
    simpa only [div_div, mul_comm C v] using hh
  · have hh : x/t ≤ (C*u*s)/(v*s) := div_le_div₀ (by positivity) hx.2 (mul_pos hv hs) ht.1
    simpa only [mul_div_mul_right _ _ hs.ne', mul_div_assoc] using hh

theorem regularization_grid_mass_bounds (Q : DyadicCube d) (hQ : 0 < Q.side)
    (μ : Measure (Space d)) [IsProbabilityMeasure μ] (N : ℕ) {B : ℕ} (hB : 0 < B)
    {p : CellPath d} (hp : p ∈ regularizationLeaves Q μ N)
    {i : ℕ} (hi : i ≤ N/B+1) {P : CellPath d}
    (hP : P ∈ (classLeaves (regularizationLeaves Q μ N) (regularizationLabel Q μ N B)
      (regularizationLabel Q μ N B p)).image (List.take (blockDepth N B i))) :
    let L := regularizationLeaves Q μ N
    let F := regularizationLabel Q μ N B
    let K := N/B+1
    let M := (blockProduct L F N B i p : ℝ) / (blockProduct L F N B K p : ℝ)
    let ρ := normalizedClass Q μ L F (F p)
    M/(2:ℝ)^(K+1) ≤ (ρ (Q.descendant P).carrier).toReal ∧
      (ρ (Q.descendant P).carrier).toReal ≤ (2:ℝ)^(K+1)*M := by
  classical
  let L := regularizationLeaves Q μ N
  let F := regularizationLabel Q μ N B
  let K := N/B+1
  let C := classLeaves L F (F p)
  let s := leafBinEndpoint d N (leafMassBin d N (μ (Q.descendant p).carrier).toReal)
  have hL : L ⊆ cubePaths d N := Finset.filter_subset _ _
  have hC : C ⊆ cubePaths d N := fun q hq => hL (Finset.mem_filter.mp hq).1
  have hleaf := regularization_class_leaf_bounds Q μ N B hp
  have hs : 0 < s := hleaf.1
  have hm : ∀ q ∈ C, s ≤ (μ (Q.descendant q).carrier).toReal ∧
      (μ (Q.descendant q).carrier).toReal ≤ 2*s := hleaf.2
  have hlen : P.length = blockDepth N B i := by
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hP
    have hqN := (mem_cubePaths _ _ _).mp (hC hq)
    simp [List.length_take,hqN]
  have hc := blockClass_leaf_count hL B (sourceLeafLabel Q μ N) K p hi hP
  have hr := blockClass_root_count hL hB (sourceLeafLabel Q μ N) hp
  change blockProduct L F N B i p ≤ (prefixFiber C (blockDepth N B i) P).card ∧
    (prefixFiber C (blockDepth N B i) P).card ≤ 2^i*blockProduct L F N B i p at hc
  change blockProduct L F N B K p ≤ C.card ∧ C.card ≤ 2^K*blockProduct L F N B K p at hr
  have hmass := restriction_prefix_mass_bounds Q hQ μ (Nat.sub_le _ _) hC hlen hm
  have htotal := restriction_total_mass_bounds Q hQ μ hC hm
  have hpow : (2:ℝ)^i ≤ (2:ℝ)^K := by exact_mod_cast Nat.pow_le_pow_right (by omega : 0 < 2) hi
  have hu : 0 < (blockProduct L F N B i p : ℝ) := by exact_mod_cast blockProduct_pos L F N B i p
  have hv : 0 < (blockProduct L F N B K p : ℝ) := by exact_mod_cast blockProduct_pos L F N B K p
  have hci : (blockProduct L F N B i p : ℝ) ≤ (prefixFiber C (blockDepth N B i) P).card ∧
    (prefixFiber C (blockDepth N B i) P).card ≤ (2:ℝ)^i*(blockProduct L F N B i p : ℝ) := by
    exact_mod_cast hc
  have hcr : (blockProduct L F N B K p : ℝ) ≤ C.card ∧
    (C.card : ℝ) ≤ (2:ℝ)^K*(blockProduct L F N B K p : ℝ) := by exact_mod_cast hr
  have hx : (blockProduct L F N B i p : ℝ)*s ≤
      ((μ.restrict (leafUnion Q C)) (Q.descendant P).carrier).toReal ∧
      ((μ.restrict (leafUnion Q C)) (Q.descendant P).carrier).toReal ≤
        (2:ℝ)^(K+1)*(blockProduct L F N B i p : ℝ)*s := by
    constructor
    · exact (mul_le_mul_of_nonneg_right hci.1 hs.le).trans hmass.1
    · have hc' := hci.2.trans (mul_le_mul_of_nonneg_right hpow hu.le)
      have hh := hmass.2.trans (mul_le_mul_of_nonneg_right hc' (by positivity : 0 ≤ 2*s))
      simpa only [pow_succ, mul_assoc, mul_left_comm, mul_comm] using hh
  have ht : (blockProduct L F N B K p : ℝ)*s ≤ (μ (leafUnion Q C)).toReal ∧
      (μ (leafUnion Q C)).toReal ≤ (2:ℝ)^(K+1)*(blockProduct L F N B K p : ℝ)*s := by
    constructor
    · exact (mul_le_mul_of_nonneg_right hcr.1 hs.le).trans htotal.1
    · have hh := htotal.2.trans (mul_le_mul_of_nonneg_right hcr.2 (by positivity : 0 ≤ 2*s))
      simpa only [pow_succ, mul_assoc, mul_left_comm, mul_comm] using hh
  have hh := ratio_bounds_of_mass_bounds hs hu hv (by positivity) hx ht
  dsimp only
  simpa only [normalizedClass, classMeasure, Measure.smul_apply, smul_eq_mul,
    Measure.restrict_apply_univ, ENNReal.toReal_mul, ENNReal.toReal_inv, div_eq_mul_inv,
    mul_comm] using hh

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_AllDimensionalOccupiedClasses
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Positivity and occupied original prefixes of a normalized class -/

namespace Falconer.Regularization
variable {d : ℕ}
open MeasureTheory Set
open scoped ENNReal

theorem normalizedClass_real (Q : DyadicCube d) (μ : Measure (Space d))
    (L : Finset (CellPath d)) (F : CellPath d → List ℕ) (T : List ℕ) (S : Set (Space d)) :
    (normalizedClass Q μ L F T S).toReal =
      ((μ.restrict (leafUnion Q (classLeaves L F T))) S).toReal /
        (μ (leafUnion Q (classLeaves L F T))).toReal := by
  simp only [normalizedClass,classMeasure,Measure.smul_apply,smul_eq_mul,
    Measure.restrict_apply_univ,ENNReal.toReal_mul,ENNReal.toReal_inv,div_eq_mul_inv,mul_comm]

theorem normalizedClass_occupied_prefix (Q : DyadicCube d) (hQ : 0 < Q.side)
    (μ : Measure (Space d)) {N n : ℕ} (hn : n ≤ N) {L : Finset (CellPath d)}
    (hL : L ⊆ cubePaths d N) (F : CellPath d → List ℕ) (T : List ℕ)
    {P : CellPath d} (hP : P.length = n)
    (hp : 0 < (normalizedClass Q μ L F T (Q.descendant P).carrier).toReal) :
    P ∈ (classLeaves L F T).image (List.take n) := by
  classical
  have hC : classLeaves L F T ⊆ cubePaths d N := fun q hq => hL (Finset.mem_filter.mp hq).1
  have hne : (prefixFiber (classLeaves L F T) n P).Nonempty := by
    by_contra he
    have hz : prefixFiber (classLeaves L F T) n P = ∅ := Finset.not_nonempty_iff_eq_empty.mp he
    rw [normalizedClass_real,restriction_prefix_mass Q hQ μ hn hC hP,hz] at hp
    simp at hp
  obtain ⟨q,hq⟩ := hne
  obtain ⟨hq,he⟩ := Finset.mem_filter.mp hq
  exact Finset.mem_image.mpr ⟨q,hq,he⟩

theorem regularization_class_positive (Q : DyadicCube d) (hQ : 0 < Q.side)
    (μ : Measure (Space d)) [IsProbabilityMeasure μ] (N B : ℕ) {p : CellPath d}
    (hp : p ∈ regularizationLeaves Q μ N) :
    0 < (classMeasure Q μ (regularizationLeaves Q μ N) (regularizationLabel Q μ N B)
      (regularizationLabel Q μ N B p) univ).toReal := by
  classical
  let L := regularizationLeaves Q μ N
  let F := regularizationLabel Q μ N B
  let C := classLeaves L F (F p)
  have hm := regularization_class_leaf_bounds Q μ N B hp
  have hpC : p ∈ C := Finset.mem_filter.mpr ⟨hp, rfl⟩
  have hC : C ⊆ cubePaths d N := fun q hq =>
    (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1
  have hcount : 0 < (C.card:ℝ) := by exact_mod_cast Finset.card_pos.mpr ⟨p,hpC⟩
  have hh := restriction_total_mass_bounds Q hQ μ hC hm.2
  simpa only [classMeasure, Measure.restrict_apply_univ] using (mul_pos hcount hm.1).trans_le hh.1

theorem regularization_class_probability (Q : DyadicCube d) (hQ : 0 < Q.side)
    (μ : Measure (Space d)) [IsProbabilityMeasure μ] (N B : ℕ) {p : CellPath d}
    (hp : p ∈ regularizationLeaves Q μ N) :
    IsProbabilityMeasure (normalizedClass Q μ (regularizationLeaves Q μ N)
      (regularizationLabel Q μ N B) (regularizationLabel Q μ N B p)) := by
  apply normalizedClass_probability
  intro he
  have hh := regularization_class_positive Q hQ μ N B hp
  rw [he,ENNReal.toReal_zero] at hh
  exact (lt_irrefl 0) hh

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_ProfileInterpolation
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Profiles with the correct all-dimensional slope

The logarithmic child counts are linearly interpolated. Their exact slope
bound is d/N; after rescaling the depth interval to [0,1] it is d.
-/

namespace Falconer.Regularization
variable {d : ℕ}

theorem intervalRamp_increment {a b u v : ℝ} (hab : a ≤ b) (huv : u ≤ v) :
    0 ≤ intervalRamp a b v - intervalRamp a b u ∧
      intervalRamp a b v - intervalRamp a b u ≤ v-u := by
  unfold intervalRamp
  simp only [min_def]
  split_ifs <;> constructor <;> linarith

theorem finiteRampProfile_continuous (d c : ℕ → ℝ) (K : ℕ) :
    Continuous (finiteRampProfile d c K) := by
  apply continuous_finsetSum
  intro i _
  exact continuous_const.mul ((continuous_id.min continuous_const).sub
    (continuous_id.min continuous_const))

theorem intervalRamp_sum (d : ℕ → ℝ) (K : ℕ) (u : ℝ) :
    (∑ i ∈ Finset.range K, intervalRamp (d (i+1)) (d i) u) = min u (d 0)-min u (d K) := by
  induction K with
  | zero => simp
  | succ K ih => rw [Finset.sum_range_succ,ih]; unfold intervalRamp; ring

theorem finiteRampProfile_zero (d c : ℕ → ℝ) (K : ℕ) (hd : ∀ i, 0 ≤ d i) :
    finiteRampProfile d c K 0 = 0 := by
  simp [finiteRampProfile,intervalRamp, min_eq_left (hd _)]

theorem finiteRampProfile_increment (d c : ℕ → ℝ) (K : ℕ) {N C u v : ℝ}
    (hd : Antitone d) (h0 : d 0 = N) (hK : d K = 0)
    (hc : ∀ i < K, 0 ≤ c i ∧ c i ≤ C)
    (hu : 0 ≤ u) (huv : u ≤ v) (hv : v ≤ N) :
    0 ≤ finiteRampProfile d c K v - finiteRampProfile d c K u ∧
      finiteRampProfile d c K v - finiteRampProfile d c K u ≤ C*(v-u) := by
  have he : finiteRampProfile d c K v - finiteRampProfile d c K u =
      ∑ i ∈ Finset.range K, c i * (intervalRamp (d (i+1)) (d i) v -
        intervalRamp (d (i+1)) (d i) u) := by
    simp only [finiteRampProfile, ← Finset.sum_sub_distrib, mul_sub]
  rw [he]
  have hr (i : ℕ) := intervalRamp_increment (hd (Nat.le_succ i)) huv
  constructor
  · exact Finset.sum_nonneg fun i hi => mul_nonneg (hc i (Finset.mem_range.mp hi)).1 (hr i).1
  · calc
      _ ≤ ∑ i ∈ Finset.range K, C * (intervalRamp (d (i+1)) (d i) v -
          intervalRamp (d (i+1)) (d i) u) :=
        Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_right
          (hc i (Finset.mem_range.mp hi)).2 (hr i).1
      _ = C*(v-u) := by
        rw [← Finset.mul_sum,Finset.sum_sub_distrib,intervalRamp_sum,intervalRamp_sum,h0,hK]
        rw [min_eq_left hv,min_eq_right (hu.trans huv),min_eq_left (huv.trans hv),min_eq_right hu]
        ring

theorem blockSlope_bounds {N : ℕ} (hN : 0 < N) {L : Finset (CellPath d)}
    (hL : L ⊆ cubePaths d N) (F : CellPath d → List ℕ) (B i : ℕ) (p : CellPath d) :
    0 ≤ blockSlope L F N B i p ∧ blockSlope L F N B i p ≤ (d:ℝ)/(N:ℝ) := by
  have hN' : 0 < (N:ℝ) := by exact_mod_cast hN
  have hd := blockDepth_antitone N B (Nat.le_succ i)
  have hd' : (blockDepth N B (i+1):ℝ) ≤ (blockDepth N B i:ℝ) := by exact_mod_cast hd
  have hb := child_bin_le hd (Nat.sub_le _ _) hL F p
  have hb' : (Nat.log 2 (labeledChildren L F (blockDepth N B (i+1))
      (blockDepth N B i) p).card:ℝ) ≤ (d:ℝ)*((blockDepth N B i:ℝ)-(blockDepth N B (i+1):ℝ)) := by
    have hbR : (Nat.log 2 (labeledChildren L F (blockDepth N B (i+1))
        (blockDepth N B i) p).card:ℝ) ≤ ((d*(blockDepth N B i-blockDepth N B (i+1)):ℕ):ℝ) := by
      exact_mod_cast hb
    simpa only [Nat.cast_mul,Nat.cast_ofNat,Nat.cast_sub hd] using hbR
  unfold blockSlope
  constructor
  · positivity
  · by_cases he : (blockDepth N B i:ℝ)-(blockDepth N B (i+1):ℝ) = 0
    · rw [he,div_zero]; positivity
    · have hp : 0 < (blockDepth N B i:ℝ)-(blockDepth N B (i+1):ℝ) := lt_of_le_of_ne (sub_nonneg.mpr hd') (Ne.symm he)
      apply (div_le_iff₀ hp).mpr
      apply (div_le_iff₀ hN').mpr
      have heq : (d:ℝ)/(N:ℝ)*((blockDepth N B i:ℝ)-(blockDepth N B (i+1):ℝ))*(N:ℝ) =
          (d:ℝ)*((blockDepth N B i:ℝ)-(blockDepth N B (i+1):ℝ)) := by
        field_simp [hN'.ne']
      rw [heq]
      exact hb'

theorem regularizedProfile_continuous (L : Finset (CellPath d)) (F : CellPath d → List ℕ)
    (N B K : ℕ) (p : CellPath d) : Continuous (regularizedProfile L F N B K p) :=
  finiteRampProfile_continuous _ _ _

theorem regularizedProfile_zero (L : Finset (CellPath d)) (F : CellPath d → List ℕ)
    (N B K : ℕ) (p : CellPath d) : regularizedProfile L F N B K p 0 = 0 :=
  finiteRampProfile_zero _ _ _ (fun _ => Nat.cast_nonneg _)

theorem regularizedProfile_increment {N : ℕ} (hN : 0 < N) {L : Finset (CellPath d)}
    (hL : L ⊆ cubePaths d N) (F : CellPath d → List ℕ) {B : ℕ} (hB : 0 < B)
    (p : CellPath d) {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (hv : v ≤ N) :
    0 ≤ regularizedProfile L F N B (N/B+1) p v - regularizedProfile L F N B (N/B+1) p u ∧
      regularizedProfile L F N B (N/B+1) p v - regularizedProfile L F N B (N/B+1) p u ≤
        (d:ℝ)*(v-u)/(N:ℝ) := by
  have hh := finiteRampProfile_increment (fun i => (blockDepth N B i:ℝ))
    (fun i => blockSlope L F N B i p) (N/B+1)
    (fun _ _ h => Nat.cast_le.mpr (blockDepth_antitone N B h)) (by simp [blockDepth])
    (by simp [blockDepth_terminal N hB]) (fun i _ => blockSlope_bounds hN hL F B i p) hu huv hv
  simpa only [regularizedProfile, div_mul_eq_mul_div] using hh

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_ProfileGrid
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact logarithmic profile values at selected depths -/

namespace Falconer.Regularization
variable {d : ℕ}

theorem intervalRamp_at_upper {a b : ℝ} (hab : a ≤ b) : intervalRamp a b b = b-a := by
  simp [intervalRamp,min_eq_right hab]

theorem intervalRamp_at_lower {a b : ℝ} (hab : a ≤ b) : intervalRamp a b a = 0 := by
  simp [intervalRamp,min_eq_left hab]

theorem intervalRamp_of_le {a b u : ℝ} (hab : a ≤ b) (hu : u ≤ a) : intervalRamp a b u = 0 := by
  simp [intervalRamp,min_eq_left hu,min_eq_left (hu.trans hab)]

theorem intervalRamp_of_ge {a b u : ℝ} (hab : a ≤ b) (hu : b ≤ u) : intervalRamp a b u = b-a := by
  simp [intervalRamp,min_eq_right hu,min_eq_right (hab.trans hu)]

theorem finiteRampProfile_block_difference (d c : ℕ → ℝ) (hd : Antitone d)
    {K i : ℕ} (hi : i < K) :
    finiteRampProfile d c K (d i) - finiteRampProfile d c K (d (i+1)) =
      c i*(d i-d (i+1)) := by
  classical
  simp only [finiteRampProfile, ← Finset.sum_sub_distrib]
  rw [Finset.sum_eq_single i]
  · rw [intervalRamp_at_upper (hd (Nat.le_succ i)), intervalRamp_at_lower (hd (Nat.le_succ i))]
    ring
  · intro j _ hji
    rcases lt_or_gt_of_ne hji with h | h
    · rw [intervalRamp_of_le (hd (Nat.le_succ j)) (hd (by omega : j+1 ≤ i)),
        intervalRamp_of_le (hd (Nat.le_succ j)) (hd (by omega : j+1 ≤ i+1))]
      ring
    · rw [intervalRamp_of_ge (hd (Nat.le_succ j)) (hd (by omega : i ≤ j)),
        intervalRamp_of_ge (hd (Nat.le_succ j)) (hd (by omega : i+1 ≤ j))]
      ring
  · intro h; exact (h (Finset.mem_range.mpr hi)).elim

theorem finiteRampProfile_knots_telescope (d c : ℕ → ℝ) (hd : Antitone d)
    {K i : ℕ} (hi : i ≤ K) :
    (∑ j ∈ Finset.range i, c j*(d j-d (j+1))) =
      finiteRampProfile d c K (d 0) - finiteRampProfile d c K (d i) := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Finset.sum_range_succ,ih (by omega)]
    rw [← finiteRampProfile_block_difference d c hd (by omega : i < K)]
    ring

theorem blockSlope_mul_gap_grid {N : ℕ} {L : Finset (CellPath d)} (hL : L ⊆ cubePaths d N)
    (F : CellPath d → List ℕ) (B i : ℕ) (p : CellPath d) :
    blockSlope L F N B i p * ((blockDepth N B i:ℝ)-(blockDepth N B (i+1):ℝ)) =
      (Nat.log 2 (labeledChildren L F (blockDepth N B (i+1)) (blockDepth N B i) p).card:ℝ)/(N:ℝ) := by
  have hd := blockDepth_antitone N B (Nat.le_succ i)
  have hb := child_bin_le hd (Nat.sub_le _ _) hL F p
  by_cases he : (blockDepth N B i:ℝ)-(blockDepth N B (i+1):ℝ) = 0
  · have he' : blockDepth N B i = blockDepth N B (i+1) := by exact_mod_cast sub_eq_zero.mp he
    have hk : Nat.log 2 (labeledChildren L F (blockDepth N B (i+1)) (blockDepth N B i) p).card = 0 := by
      exact Nat.eq_zero_of_le_zero (hb.trans_eq (by rw [he',Nat.sub_self,Nat.mul_zero]))
    simp [blockSlope,hk]
  · unfold blockSlope
    exact div_mul_cancel₀ _ he

theorem blockProduct_eq_pow (L : Finset (CellPath d)) (F : CellPath d → List ℕ)
    (N B i : ℕ) (p : CellPath d) : blockProduct L F N B i p = 2 ^ blockLogProduct L F N B i p := by
  unfold blockProduct blockBin blockLogProduct
  rw [← Finset.prod_pow_eq_pow_sum]

theorem regularizedProfile_grid {N : ℕ} {L : Finset (CellPath d)} (hL : L ⊆ cubePaths d N)
    (F : CellPath d → List ℕ) {B : ℕ} (hB : 0 < B) (p : CellPath d)
    {i : ℕ} (hi : i ≤ N/B+1) :
    regularizedProfile L F N B (N/B+1) p (blockDepth N B i) =
      ((blockLogProduct L F N B (N/B+1) p:ℝ)-(blockLogProduct L F N B i p:ℝ))/(N:ℝ) := by
  let d := fun i => (blockDepth N B i:ℝ)
  let c := fun i => blockSlope L F N B i p
  have hd : Antitone d := fun _ _ h => Nat.cast_le.mpr (blockDepth_antitone N B h)
  have htel (j : ℕ) (hj : j ≤ N/B+1) := finiteRampProfile_knots_telescope d c hd hj
  have hsum (j : ℕ) : (∑ k ∈ Finset.range j, c k*(d k-d (k+1))) =
      (blockLogProduct L F N B j p:ℝ)/(N:ℝ) := by
    unfold c d
    simp only [blockSlope_mul_gap_grid hL F B _ p, ← Finset.sum_div, blockLogProduct, Nat.cast_sum]
  have hi' := htel i hi
  have hK := htel (N/B+1) le_rfl
  rw [hsum] at hi' hK
  have hz : finiteRampProfile d c (N/B+1) (d (N/B+1)) = 0 := by
    change regularizedProfile L F N B (N/B+1) p _ = 0
    rw [show d (N/B+1) = 0 by simp [d,blockDepth_terminal N hB], regularizedProfile_zero]
  rw [hz] at hK
  change finiteRampProfile d c (N/B+1) (d i) = _
  rw [sub_div]
  linarith

theorem regularizedProfile_reference_grid {N : ℕ} (hN : 0 < N)
    {L : Finset (CellPath d)} (hL : L ⊆ cubePaths d N)
    (F : CellPath d → List ℕ) {B : ℕ} (hB : 0 < B) (p : CellPath d)
    {i : ℕ} (hi : i ≤ N/B+1) :
    ((2:ℝ)^N) ^ (-regularizedProfile L F N B (N/B+1) p (blockDepth N B i)) =
      (blockProduct L F N B i p:ℝ)/(blockProduct L F N B (N/B+1) p:ℝ) := by
  rw [regularizedProfile_grid hL F hB p hi, blockProduct_eq_pow,blockProduct_eq_pow]
  simp only [Nat.cast_pow,Nat.cast_ofNat]
  rw [← Real.rpow_natCast (2:ℝ) N, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
  have hN' : (N:ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have he : (N:ℝ) * -(((blockLogProduct L F N B (N/B+1) p:ℝ)-(blockLogProduct L F N B i p:ℝ))/(N:ℝ)) =
      (blockLogProduct L F N B i p:ℝ)-(blockLogProduct L F N B (N/B+1) p:ℝ) := by field_simp; ring
  rw [he,Real.rpow_sub (by norm_num : (0:ℝ) < 2),Real.rpow_natCast,Real.rpow_natCast]

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_IntermediateProfiles
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Mass-profile comparison at every depth in arbitrary dimension

The interpolation loss is (d+1)*lambda. The block depths satisfy the
same numerical bracketing as in the planar case.
-/

namespace Falconer.Regularization
variable {d : ℕ}
open MeasureTheory
open scoped ENNReal

theorem sourceClass_grid_comparison (Q : DyadicCube d) (hQ : 0 < Q.side)
    (μ : Measure (Space d)) [IsProbabilityMeasure μ] {N B : ℕ} (hN : 0 < N) (hB : 0 < B)
    {p : CellPath d} (hp : p ∈ regularizationLeaves Q μ N)
    {i : ℕ} (hi : i ≤ N/B+1) {P : CellPath d}
    (hP : P ∈ (classLeaves (regularizationLeaves Q μ N) (regularizationLabel Q μ N B)
      (regularizationLabel Q μ N B p)).image (List.take (blockDepth N B i))) :
    (((2:ℝ)^N)^(-sourceProfile Q μ N B p (blockDepth N B i)))/(2:ℝ)^(N/B+2) ≤
      (sourceClass Q μ N B p (Q.descendant P).carrier).toReal ∧
    (sourceClass Q μ N B p (Q.descendant P).carrier).toReal ≤
      (2:ℝ)^(N/B+2)*(((2:ℝ)^N)^(-sourceProfile Q μ N B p (blockDepth N B i))) := by
  classical
  rw [sourceProfile,regularizedProfile_reference_grid hN (show regularizationLeaves Q μ N ⊆ cubePaths d N from Finset.filter_subset _ _)
    (regularizationLabel Q μ N B) hB p hi]
  exact regularization_grid_mass_bounds Q hQ μ N hB hp hi hP

theorem profile_bracket_mass_bound {R C lam m₀ mₙ m₁ x₀ xₙ x₁ : ℝ}
    (hR : 1 ≤ R) (hC : 0 < C) (hCL : C ≤ R^lam)
    (hml : m₁-mₙ ≤ (d:ℝ)*lam) (hmu : mₙ-m₀ ≤ (d:ℝ)*lam)
    (hlo : R^(-m₁)/C ≤ x₁) (hhi : x₀ ≤ C*R^(-m₀))
    (hxl : x₁ ≤ xₙ) (hxu : xₙ ≤ x₀) :
    R^(-((d:ℝ)+1)*lam)*R^(-mₙ) ≤ xₙ ∧ xₙ ≤ R^(((d:ℝ)+1)*lam)*R^(-mₙ) := by
  have hRp : 0 < R := lt_of_lt_of_le zero_lt_one hR
  constructor
  · apply le_trans ?_ (hlo.trans hxl)
    apply (le_div_iff₀ hC).mpr
    calc
      R^(-((d:ℝ)+1)*lam)*R^(-mₙ)*C ≤ R^(-((d:ℝ)+1)*lam)*R^(-mₙ)*R^lam :=
        mul_le_mul_of_nonneg_left hCL (by positivity)
      _ = R^(-(d:ℝ)*lam-mₙ) := by rw [← Real.rpow_add hRp,← Real.rpow_add hRp]; congr 1; ring
      _ ≤ R^(-m₁) := Real.rpow_le_rpow_of_exponent_le hR (by linarith)
  · apply le_trans (hxu.trans hhi)
    calc
      C*R^(-m₀) ≤ R^lam*R^(-m₀) := mul_le_mul_of_nonneg_right hCL (by positivity)
      _ = R^(lam-m₀) := by rw [← Real.rpow_add hRp]; rfl
      _ ≤ R^(((d:ℝ)+1)*lam-mₙ) := Real.rpow_le_rpow_of_exponent_le hR (by linarith)
      _ = R^(((d:ℝ)+1)*lam)*R^(-mₙ) := Real.rpow_add hRp _ _

theorem sourceProfile_short_increment (Q : DyadicCube d) (μ : Measure (Space d))
    {N B : ℕ} (hN : 0 < N) (hB : 0 < B) (p : CellPath d) {lam u v : ℝ}
    (hwidth : (B:ℝ) ≤ lam*(N:ℝ)) (hu : 0 ≤ u) (huv : u ≤ v) (hv : v ≤ N)
    (hshort : v-u ≤ B) :
    sourceProfile Q μ N B p v-sourceProfile Q μ N B p u ≤ (d:ℝ)*lam := by
  classical
  have hh := regularizedProfile_increment hN (show regularizationLeaves Q μ N ⊆ cubePaths d N from Finset.filter_subset _ _)
    (regularizationLabel Q μ N B) hB p hu huv hv
  apply hh.2.trans
  apply (div_le_iff₀ (by exact_mod_cast hN : 0 < (N:ℝ))).mpr
  have hmul₁ := mul_le_mul_of_nonneg_left hwidth (Nat.cast_nonneg d)
  have hmul₂ := mul_le_mul_of_nonneg_left hshort (Nat.cast_nonneg d)
  nlinarith

theorem sourceClass_all_depth_comparison (Q : DyadicCube d) (hQ : 0 < Q.side)
    (μ : Measure (Space d)) [IsProbabilityMeasure μ] {N B : ℕ} (hN : 0 < N) (hB : 0 < B)
    {lam : ℝ} (hwidth : (B:ℝ) ≤ lam*(N:ℝ))
    (hlarge : (2:ℝ)^(N/B+2) ≤ ((2:ℝ)^N)^lam)
    {p : CellPath d} (hp : p ∈ regularizationLeaves Q μ N)
    {n : ℕ} (hn : n ≤ N) {P : CellPath d}
    (hP : P ∈ (classLeaves (regularizationLeaves Q μ N) (regularizationLabel Q μ N B)
      (regularizationLabel Q μ N B p)).image (List.take n)) :
    ((2:ℝ)^N)^(-((d:ℝ)+1)*lam)*((2:ℝ)^N)^(-sourceProfile Q μ N B p n) ≤
      (sourceClass Q μ N B p (Q.descendant P).carrier).toReal ∧
    (sourceClass Q μ N B p (Q.descendant P).carrier).toReal ≤
      ((2:ℝ)^N)^(((d:ℝ)+1)*lam)*((2:ℝ)^N)^(-sourceProfile Q μ N B p n) := by
  classical
  let i := (N-n)/B
  have hb := PlanarFalconer.blockDepth_brackets hn hB
  change i < N/B+1 ∧ blockDepth N B (i+1) ≤ n ∧ n ≤ blockDepth N B i ∧
    blockDepth N B i-n ≤ B ∧ n-blockDepth N B (i+1) ≤ B at hb
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hP
  let ρ := sourceClass Q μ N B p
  have : IsProbabilityMeasure ρ := regularization_class_probability Q hQ μ N B hp
  have hgp := sourceClass_grid_comparison Q hQ μ hN hB hp (Nat.le_of_lt hb.1)
    (Finset.mem_image.mpr ⟨q,hq,rfl⟩)
  have hgm := sourceClass_grid_comparison Q hQ μ hN hB hp (by omega : i+1 ≤ N/B+1)
    (Finset.mem_image.mpr ⟨q,hq,rfl⟩)
  have hmono₁ : ρ (Q.descendant (q.take (blockDepth N B i))).carrier ≤
      ρ (Q.descendant (q.take n)).carrier := by
    apply measure_mono
    have hh := descendant_subset_take Q hQ (q.take (blockDepth N B i)) n
    simpa only [List.take_take,Nat.min_eq_left hb.2.2.1] using hh
  have hmono₀ : ρ (Q.descendant (q.take n)).carrier ≤
      ρ (Q.descendant (q.take (blockDepth N B (i+1)))).carrier := by
    apply measure_mono
    have hh := descendant_subset_take Q hQ (q.take n) (blockDepth N B (i+1))
    simpa only [List.take_take,Nat.min_eq_left hb.2.1] using hh
  have hml := sourceProfile_short_increment Q μ hN hB p hwidth
    (Nat.cast_nonneg n) (Nat.cast_le.mpr hb.2.2.1)
    (Nat.cast_le.mpr (Nat.sub_le N (i*B))) (by
      simpa only [Nat.cast_sub hb.2.2.1] using
        (show (((blockDepth N B i-n):ℕ):ℝ) ≤ (B:ℝ) by exact_mod_cast hb.2.2.2.1))
  have hmu := sourceProfile_short_increment Q μ hN hB p hwidth
    (Nat.cast_nonneg (blockDepth N B (i+1))) (Nat.cast_le.mpr hb.2.1) (Nat.cast_le.mpr hn) (by
      simpa only [Nat.cast_sub hb.2.1] using
        (show (((n-blockDepth N B (i+1)):ℕ):ℝ) ≤ (B:ℝ) by exact_mod_cast hb.2.2.2.2))
  exact profile_bracket_mass_bound (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2))
    (by positivity) hlarge hml hmu hgp.1 hgm.2
    (ENNReal.toReal_mono (measure_ne_top ρ _) hmono₁)
    (ENNReal.toReal_mono (measure_ne_top ρ _) hmono₀)

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_ProfileEnvelopes
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Profile lower bounds from the original mass law

An original s-ball estimate yields the lower profile bound after paying
for class normalization and the dimension-dependent interpolation loss.
-/

namespace Falconer.Regularization
open MeasureTheory Set
open scoped ENNReal
variable {d : ℕ}

theorem sourceClass_occupied_comparison (Q : DyadicCube d) (hQ : 0 < Q.side)
    (μ : Measure (Space d)) [IsProbabilityMeasure μ] {N B : ℕ} (hN : 0 < N) (hB : 0 < B)
    {lam : ℝ} (hwidth : (B:ℝ) ≤ lam*(N:ℝ))
    (hlarge : (2:ℝ)^(N/B+2) ≤ ((2:ℝ)^N)^lam)
    {p : CellPath d} (hp : p ∈ regularizationLeaves Q μ N)
    {n : ℕ} (hn : n ≤ N) {P : CellPath d} (hP : P.length = n)
    (hpos : 0 < sourceClass Q μ N B p (Q.descendant P).carrier) :
    ((2:ℝ)^N)^(-((d:ℝ)+1)*lam)*((2:ℝ)^N)^(-sourceProfile Q μ N B p n) ≤
      (sourceClass Q μ N B p (Q.descendant P).carrier).toReal ∧
    (sourceClass Q μ N B p (Q.descendant P).carrier).toReal ≤
      ((2:ℝ)^N)^(((d:ℝ)+1)*lam)*((2:ℝ)^N)^(-sourceProfile Q μ N B p n) := by
  classical
  have : IsProbabilityMeasure (sourceClass Q μ N B p) := regularization_class_probability Q hQ μ N B hp
  apply sourceClass_all_depth_comparison Q hQ μ hN hB hwidth hlarge hp hn
  apply normalizedClass_occupied_prefix Q hQ μ hn
    (show regularizationLeaves Q μ N ⊆ cubePaths d N from Finset.filter_subset _ _)
    (regularizationLabel Q μ N B) (regularizationLabel Q μ N B p) hP
  exact ENNReal.toReal_pos hpos.ne' (measure_ne_top (sourceClass Q μ N B p) _)

theorem normalizedClass_real_le (Q : DyadicCube d) (μ : Measure (Space d)) [IsFiniteMeasure μ]
    (L : Finset (CellPath d)) (F : CellPath d → List ℕ) (T : List ℕ) {t : ℝ} (ht : 0 < t)
    (hmass : t ≤ (classMeasure Q μ L F T univ).toReal) (S : Set (Space d)) :
    (normalizedClass Q μ L F T S).toReal ≤ (μ S).toReal/t := by
  rw [normalizedClass_real]
  have hr : ((μ.restrict (leafUnion Q (classLeaves L F T))) S).toReal ≤ (μ S).toReal :=
    ENNReal.toReal_mono (measure_ne_top _ _) (Measure.restrict_apply_le _ _)
  have hm : t ≤ (μ (leafUnion Q (classLeaves L F T))).toReal := by
    simpa only [classMeasure,Measure.restrict_apply_univ] using hmass
  exact div_le_div₀ ENNReal.toReal_nonneg hr ht hm

theorem sourceProfile_frostman_lower (Q : DyadicCube d) (hQ : 0 < Q.side)
    (μ : Measure (Space d)) [IsProbabilityMeasure μ] {N B : ℕ} (hN : 0 < N) (hB : 0 < B)
    {lam s : ℝ} (hwidth : (B:ℝ) ≤ lam*(N:ℝ))
    (hlarge : (2:ℝ)^(N/B+2) ≤ ((2:ℝ)^N)^lam)
    {p : CellPath d} (hp : p ∈ regularizationLeaves Q μ N)
    (hmass : ((2:ℝ)^N)^(-lam) ≤
      (classMeasure Q μ (regularizationLeaves Q μ N) (regularizationLabel Q μ N B)
        (regularizationLabel Q μ N B p) Set.univ).toReal)
    (hcell : ∀ n ≤ N, ∀ P : CellPath d, P.length = n →
      (μ (Q.descendant P).carrier).toReal ≤
        ((2:ℝ)^N)^lam * ((2:ℝ)^N)^(-s*(n:ℝ)/(N:ℝ)))
    {n : ℕ} (hn : n ≤ N) :
    s*(n:ℝ)/(N:ℝ)-((d:ℝ)+3)*lam ≤ sourceProfile Q μ N B p n := by
  classical
  let R : ℝ := (2:ℝ)^N
  have hR : 1 < R := one_lt_pow₀ (by norm_num : (1:ℝ) < 2) hN.ne'
  have hRp : 0 < R := (zero_lt_one.trans hR)
  have hpN : p.length = N := (mem_cubePaths _ _ _).mp (Finset.mem_filter.mp hp).1
  have hPn : (p.take n).length = n := by simp [List.length_take,hpN,hn]
  have hpC : p ∈ classLeaves (regularizationLeaves Q μ N) (regularizationLabel Q μ N B)
      (regularizationLabel Q μ N B p) := Finset.mem_filter.mpr ⟨hp, rfl⟩
  have hcomp := sourceClass_all_depth_comparison Q hQ μ hN hB hwidth hlarge hp hn
    (Finset.mem_image.mpr ⟨p,hpC,rfl⟩)
  have hnorm := normalizedClass_real_le Q μ (regularizationLeaves Q μ N)
    (regularizationLabel Q μ N B) (regularizationLabel Q μ N B p)
    (Real.rpow_pos_of_pos hRp (-lam)) hmass (Q.descendant (p.take n)).carrier
  have hu := hnorm.trans (div_le_div_of_nonneg_right (hcell n hn (p.take n) hPn) (by positivity))
  have hpow : R^(-((d:ℝ)+1)*lam-sourceProfile Q μ N B p n) ≤ R^(2*lam-s*(n:ℝ)/(N:ℝ)) := by
    have hh := hcomp.1.trans hu
    change R^(-((d:ℝ)+1)*lam)*R^(-sourceProfile Q μ N B p n) ≤
      (R^lam*R^(-s*(n:ℝ)/(N:ℝ)))/R^(-lam) at hh
    rw [← Real.rpow_add hRp,← Real.rpow_add hRp,← Real.rpow_sub hRp] at hh
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    ring
  have he := (Real.rpow_le_rpow_left_iff hR).mp hpow
  nlinarith

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_FrostmanProfiles
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Frostman lower envelopes for the constructed all-dimensional profiles

The enclosing-ball constant is 2*sqrt d, and the numerical choice of block
length is independent of dimension.
-/

namespace Falconer.Regularization
open Set MeasureTheory Metric
open scoped ENNReal
variable {d : ℕ}

theorem dyadic_rpow_scale {N : ℕ} (hN : 0 < N) (j : ℕ) (s : ℝ) :
    ((2:ℝ)^N)^(-s*(j:ℝ)/(N:ℝ)) = (((2:ℝ)^j)^s)⁻¹ := by
  rw [← Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 2)]
  have hN' : (N:ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have he : (N:ℝ)*(-s*(j:ℝ)/(N:ℝ)) = -((j:ℝ)*s) := by field_simp
  rw [he,Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 2)]

theorem dyadic_cell_frostman_bound (hd : 0 < d) (Q : DyadicCube d) (hQ : 0 < Q.side)
    (μ : Measure (Space d)) {s C : ℝ}
    (hball : ∀ x : Space d, ∀ r > 0, μ (ball x r) ≤ ENNReal.ofReal (C*r^s))
    (p : CellPath d) :
    μ (Q.descendant p).carrier ≤ ENNReal.ofReal (C*(2*Real.sqrt d*(Q.descendant p).side)^s) := by
  have hside := Q.descendant_side_pos hQ p
  have hsqrt : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hd)
  apply (measure_mono (show (Q.descendant p).carrier ⊆
      ball (Q.descendant p).center (2*Real.sqrt d*(Q.descendant p).side) from ?_)).trans
    (hball _ _ (by positivity))
  intro x hx
  have hh := (Q.descendant p).dist_le hside.le hx ((Q.descendant p).center_mem hside)
  exact mem_ball.mpr (by nlinarith [mul_pos hsqrt hside])

theorem dyadic_cell_frostman_profile_bound (hd : 0 < d) (Q : DyadicCube d) (hQ : 0 < Q.side)
    (μ : Measure (Space d)) [IsFiniteMeasure μ] {s C : ℝ} (hC : 0 ≤ C)
    (hball : ∀ x : Space d, ∀ r > 0, μ (ball x r) ≤ ENNReal.ofReal (C*r^s))
    {N : ℕ} (hN : 0 < N) (p : CellPath d) :
    (μ (Q.descendant p).carrier).toReal ≤
      (C*(2*Real.sqrt d*Q.side)^s)*((2:ℝ)^N)^(-s*(p.length:ℝ)/(N:ℝ)) := by
  have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top (dyadic_cell_frostman_bound hd Q hQ μ hball p)
  have hside := Q.descendant_side_pos hQ p
  rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ C*(2*Real.sqrt d*(Q.descendant p).side)^s)] at hh
  apply hh.trans_eq
  rw [Q.descendant_side,dyadic_rpow_scale hN]
  rw [show 2*Real.sqrt d*(Q.side/(2:ℝ)^p.length) =
    (2*Real.sqrt d*Q.side)/(2:ℝ)^p.length by ring,
    Real.div_rpow (by positivity) (by positivity)]
  ring

theorem retained_label_real_mass_lower (Q : DyadicCube d) (μ : Measure (Space d))
    [IsFiniteMeasure μ] {N B : ℕ} {p : CellPath d} {lam : ℝ}
    (hp : regularizationLabel Q μ N B p ∈ regularizationIndex Q μ N B
      (ENNReal.ofReal (((2:ℝ)^N)^(-lam)))) :
    ((2:ℝ)^N)^(-lam) ≤ (classMeasure Q μ (regularizationLeaves Q μ N)
      (regularizationLabel Q μ N B) (regularizationLabel Q μ N B p) univ).toReal := by
  have hm := regularizationSet_mass Q μ N B _ hp
  have hh := ENNReal.toReal_mono (measure_ne_top μ _) hm
  simpa only [classMeasure,Measure.restrict_apply_univ,regularizationSet,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ ((2:ℝ)^N)^(-lam))] using hh

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_UnitProfiles
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The constructed d-Lipschitz profiles on the unit interval

This is the paper's normalization of the finite-tree profile. Its slope
bound is the ambient dimension d, and its values lie between zero and d.
-/

namespace Falconer.Regularization
open Set
variable {d : ℕ}

theorem unitProfile_continuous (L : Finset (CellPath d)) (F : CellPath d → List ℕ)
    (N B : ℕ) (p : CellPath d) : Continuous (unitProfile L F N B p) :=
  (regularizedProfile_continuous L F N B (N/B+1) p).comp (continuous_const.mul continuous_id)

theorem unitProfile_zero (L : Finset (CellPath d)) (F : CellPath d → List ℕ)
    (N B : ℕ) (p : CellPath d) : unitProfile L F N B p 0 = 0 := by
  simp only [unitProfile,mul_zero,regularizedProfile_zero]

theorem unitProfile_increment {N B : ℕ} (hN : 0 < N) (hB : 0 < B)
    {L : Finset (CellPath d)} (hL : L ⊆ cubePaths d N)
    (F : CellPath d → List ℕ) (p : CellPath d) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u ≤ v) (hv : v ≤ 1) :
    0 ≤ unitProfile L F N B p v-unitProfile L F N B p u ∧
      unitProfile L F N B p v-unitProfile L F N B p u ≤ (d : ℝ)*(v-u) := by
  have hN0 : 0 < (N : ℝ) := by exact_mod_cast hN
  have hm := regularizedProfile_increment hN hL F hB p
    (mul_nonneg hN0.le hu) (mul_le_mul_of_nonneg_left huv hN0.le)
    (by nlinarith : (N : ℝ)*v ≤ N)
  refine ⟨hm.1,hm.2.trans_eq ?_⟩
  field_simp

theorem unitProfile_monotoneOn {N B : ℕ} (hN : 0 < N) (hB : 0 < B)
    {L : Finset (CellPath d)} (hL : L ⊆ cubePaths d N)
    (F : CellPath d → List ℕ) (p : CellPath d) :
    MonotoneOn (unitProfile L F N B p) (Icc 0 1) := by
  intro u hu v hv huv
  exact sub_nonneg.mp (unitProfile_increment hN hB hL F p hu.1 huv hv.2).1

theorem unitProfile_lipschitzOn {N B : ℕ} (hN : 0 < N) (hB : 0 < B)
    {L : Finset (CellPath d)} (hL : L ⊆ cubePaths d N)
    (F : CellPath d → List ℕ) (p : CellPath d) :
    LipschitzOnWith (d : NNReal) (unitProfile L F N B p) (Icc 0 1) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro u hu v hv
  rcases le_total v u with hvu | huv
  · have hi := unitProfile_increment hN hB hL F p hv.1 hvu hu.2
    simpa only [Real.dist_eq,abs_of_nonneg hi.1,abs_of_nonneg (sub_nonneg.mpr hvu),
      NNReal.coe_natCast] using hi.2
  · have hi := unitProfile_increment hN hB hL F p hu.1 huv hv.2
    rw [dist_comm,Real.dist_eq,abs_of_nonneg hi.1,Real.dist_eq,abs_of_nonpos (sub_nonpos.mpr huv)]
    simpa only [NNReal.coe_natCast,neg_sub] using hi.2

theorem unitProfile_range {N B : ℕ} (hN : 0 < N) (hB : 0 < B)
    {L : Finset (CellPath d)} (hL : L ⊆ cubePaths d N)
    (F : CellPath d → List ℕ) (p : CellPath d) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    unitProfile L F N B p u ∈ Icc (0 : ℝ) (d : ℝ) := by
  have h := unitProfile_increment hN hB hL F p (u := 0) (v := u) (by rfl) hu.1 hu.2
  rw [unitProfile_zero,sub_zero,sub_zero] at h
  exact ⟨h.1,h.2.trans (mul_le_of_le_one_right (Nat.cast_nonneg d) hu.2)⟩

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_RegularizationProperties
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Unit-scale profiles and conditional mass ratios of the original classes -/

namespace Falconer.Regularization
open MeasureTheory Set
variable {d : ℕ}

theorem sourceUnitProfile_at_depth (Q : DyadicCube d) (μ : Measure (Space d))
    {N : ℕ} (hN : 0 < N) (B : ℕ) (p : CellPath d) (j : ℕ) :
    sourceUnitProfile Q μ N B p ((j:ℝ)/N) = sourceProfile Q μ N B p j := by
  unfold sourceUnitProfile unitProfile sourceProfile
  congr 1
  field_simp

theorem sourceUnitProfile_properties (Q : DyadicCube d) (μ : Measure (Space d))
    {N B : ℕ} (hN : 0 < N) (hB : 0 < B) (p : CellPath d) :
    Continuous (sourceUnitProfile Q μ N B p) ∧
    sourceUnitProfile Q μ N B p 0 = 0 ∧
    MonotoneOn (sourceUnitProfile Q μ N B p) (Icc 0 1) ∧
    LipschitzOnWith (d : NNReal) (sourceUnitProfile Q μ N B p) (Icc 0 1) ∧
    ∀ u ∈ Icc (0:ℝ) 1, sourceUnitProfile Q μ N B p u ∈ Icc (0:ℝ) d := by
  have hL : regularizationLeaves Q μ N ⊆ cubePaths d N := Finset.filter_subset _ _
  exact ⟨unitProfile_continuous _ _ _ _ _,unitProfile_zero _ _ _ _ _,
    unitProfile_monotoneOn hN hB hL _ _,unitProfile_lipschitzOn hN hB hL _ _,
    fun _ hu => unitProfile_range hN hB hL _ _ hu⟩

theorem sourceUnitProfile_lower_from_grid (Q : DyadicCube d) (μ : Measure (Space d))
    {N B : ℕ} (hN : 0 < N) (hB : 0 < B) (p : CellPath d)
    {s E : ℝ} (hs : 0 ≤ s)
    (hgrid : ∀ j ≤ N, s*(j:ℝ)/(N:ℝ)-E ≤ sourceProfile Q μ N B p j)
    {u : ℝ} (hu : u ∈ Icc (0:ℝ) 1) :
    s*u-E-s/N ≤ sourceUnitProfile Q μ N B p u := by
  have hNp : 0 < (N:ℝ) := by exact_mod_cast hN
  let j := Nat.floor ((N:ℝ)*u)
  have hfloor : (j:ℝ) ≤ (N:ℝ)*u := Nat.floor_le (mul_nonneg hNp.le hu.1)
  have hnext : (N:ℝ)*u < (j:ℝ)+1 := Nat.lt_floor_add_one _
  have hj : j ≤ N := by
    exact_mod_cast hfloor.trans (mul_le_of_le_one_right hNp.le hu.2)
  have hju : (j:ℝ)/(N:ℝ) ≤ u := (div_le_iff₀ hNp).mpr (by simpa [mul_comm] using hfloor)
  have hj0 : 0 ≤ (j:ℝ)/(N:ℝ) := by positivity
  have hm := (sourceUnitProfile_properties Q μ hN hB p).2.2.1
    ⟨hj0,hju.trans hu.2⟩ hu hju
  rw [sourceUnitProfile_at_depth Q μ hN B p j] at hm
  have hsj := mul_le_mul_of_nonneg_left
    ((le_div_iff₀ hNp).mpr (by simpa [mul_comm] using hnext.le)) hs
  have he : s*((j:ℝ)+1)/(N:ℝ) = s*(j:ℝ)/(N:ℝ)+s/N := by ring
  rw [← mul_div_assoc,he] at hsj
  linarith [hgrid j hj]

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_DyadicCenters
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The actual dyadic centers as one translated integer grid

The graph packing estimates apply to centers of descendants of the
original parent cube. Their integer labels and common translation are
identified exactly, in every ambient dimension.
-/

namespace Falconer
attribute [local instance] Classical.propDecidable

/-- The translation includes half a child side. Its contribution cancels
in every displacement used by the retained graph. -/
theorem DyadicCube.descendant_center_grid {d n : ℕ} (Q : DyadicCube d)
    (p : List (Fin d → Bool)) (hp : p.length = n) :
    (Q.descendant p).center =
      WithLp.toLp 2 (fun i => Q.origin i + (Q.side / (2 : ℝ)^n)/2) +
        scaledGridPoint ((2 : ℝ)^n / Q.side) (dyadicCode p) := by
  ext i
  simp only [PiLp.add_apply, scaledGridPoint_apply,
    Q.descendant_center, hp]
  field_simp

theorem DyadicCube.center_sub_eq_grid_sub {d n : ℕ} (Q : DyadicCube d)
    (p q : List (Fin d → Bool)) (hp : p.length = n) (hq : q.length = n) :
    (Q.descendant p).center - (Q.descendant q).center =
      scaledGridPoint ((2 : ℝ)^n / Q.side) (dyadicCode p) -
      scaledGridPoint ((2 : ℝ)^n / Q.side) (dyadicCode q) := by
  rw [Q.descendant_center_grid p hp, Q.descendant_center_grid q hq]
  abel

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_DyadicBallCount
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Local counts of actual all-dimensional dyadic ancestors -/

namespace Falconer
open Metric Set

theorem dyadic_center_diameter_count {d n L : ℕ} (Q : DyadicCube d) (hQ : 0 < Q.side)
    (S : Finset (List (Fin d → Bool))) (hS : ∀ p ∈ S, p.length = n)
    {r : ℝ} (hL : r*((2:ℝ)^n/Q.side) ≤ L)
    (hdiam : ∀ p ∈ S, ∀ q ∈ S, dist (Q.descendant p).center (Q.descendant q).center ≤ r) :
    S.card ≤ (2*L+1)^d := by
  classical
  by_cases hne : S.Nonempty
  · obtain ⟨q,hq⟩ := hne
    have hi : Set.InjOn dyadicCode (S : Set (List (Fin d → Bool))) := by
      intro p hp t ht he
      exact dyadicCode_injective_at_depth (hS p hp) (hS t ht) he
    rw [← Finset.card_image_of_injOn hi]
    apply grid_ball_card (by positivity) hL (S.image dyadicCode) (dyadicCode q)
    intro z hz
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hz
    rw [← Q.center_sub_eq_grid_sub p q (hS p hp) (hS q hq)]
    simpa only [dist_eq_norm] using hdiam p hp q hq
  · simp only [Finset.not_nonempty_iff_eq_empty.mp hne,Finset.card_empty,Nat.zero_le]

theorem DyadicCube.center_distance_ancestor {d n g : ℕ} (Q : DyadicCube d)
    (hQ : 0 < Q.side) (p : List (Fin d → Bool)) (hp : p.length = n) (hg : g ≤ n) :
    dist (Q.descendant p).center (Q.descendant (p.take g)).center ≤
      Real.sqrt d * (Q.side/(2:ℝ)^g) := by
  have h := (Q.descendant (p.take g)).dist_le (Q.descendant_side_pos hQ _).le
    (Q.center_mem_ancestor hQ p g)
    ((Q.descendant (p.take g)).center_mem (Q.descendant_side_pos hQ _))
  simpa only [Q.descendant_side,List.length_take,hp,min_eq_left hg] using h

theorem dyadic_ancestor_ball_count {d n g : ℕ} (Q : DyadicCube d) (hQ : 0 < Q.side)
    (S : Finset (List (Fin d → Bool))) (hS : ∀ p ∈ S, p.length = n) (hg : g ≤ n)
    (x : Space d) {r C : ℝ} (_hC : 0 ≤ C) (hr : r ≤ C*(Q.side/(2:ℝ)^g))
    (hball : ∀ p ∈ S, dist (Q.descendant p).center x ≤ r) :
    (S.image (List.take g)).card ≤ (2*Nat.ceil (2*C+2*Real.sqrt d)+1)^d := by
  classical
  let a := Q.side/(2:ℝ)^g
  have ha : 0 < a := by dsimp [a]; positivity
  have hcenter (p : List (Fin d → Bool)) (hp : p ∈ S) :
      dist (Q.descendant (p.take g)).center x ≤ r+Real.sqrt d*a := by
    calc
      _ ≤ dist (Q.descendant (p.take g)).center (Q.descendant p).center +
          dist (Q.descendant p).center x := dist_triangle _ _ _
      _ ≤ Real.sqrt d*a+r := add_le_add
        (by simpa only [dist_comm] using Q.center_distance_ancestor hQ p (hS p hp) hg) (hball p hp)
      _ = _ := add_comm _ _
  apply dyadic_center_diameter_count (n := g) Q hQ (S.image (List.take g))
    (fun p hp => by
      obtain ⟨q,hq',rfl⟩ := Finset.mem_image.mp hp
      simp only [List.length_take,hS q hq',min_eq_left hg])
    (r := 2*r+2*Real.sqrt d*a)
  · have hc : 2*C+2*Real.sqrt d ≤ (Nat.ceil (2*C+2*Real.sqrt d):ℝ) := Nat.le_ceil _
    have hh : 2*r+2*Real.sqrt d*a ≤ (2*C+2*Real.sqrt d)*a := by nlinarith [hr]
    calc
      _ ≤ ((2*C+2*Real.sqrt d)*a)*((2:ℝ)^g/Q.side) :=
        mul_le_mul_of_nonneg_right hh (by positivity)
      _ = 2*C+2*Real.sqrt d := by dsimp [a]; field_simp
      _ ≤ _ := hc
  · intro p hp q hq
    obtain ⟨p',hp',rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨q',hq',rfl⟩ := Finset.mem_image.mp hq
    calc
      _ ≤ dist (Q.descendant (p'.take g)).center x +
          dist x (Q.descendant (q'.take g)).center := dist_triangle _ _ _
      _ ≤ (r+Real.sqrt d*a)+(r+Real.sqrt d*a) :=
        add_le_add (hcenter p' hp') (by simpa only [dist_comm] using hcenter q' hq')
      _ = _ := by ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_ProfileBalls
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Ball bounds obtained from actual occupied-cell profile estimates -/

namespace Falconer.Regularization
open MeasureTheory Set Metric
open scoped ENNReal
variable {d : ℕ}

theorem cellsMeetingBall_card (Q : DyadicCube d) (hQ : 0 < Q.side)
    (n : ℕ) (x : Space d) {r C : ℝ} (hC : 0 ≤ C) (hr : r ≤ C*(Q.side/(2:ℝ)^n)) :
    (cellsMeetingBall Q n x r).card ≤ (2*Nat.ceil (2*C+4*Real.sqrt d)+1)^d := by
  classical
  let S := cellsMeetingBall Q n x r
  have hS (p) (hp : p ∈ S) : p.length = n :=
    (mem_cubePaths _ _ _).mp (Finset.mem_filter.mp hp).1
  have hcenter (p) (hp : p ∈ S) :
      dist (Q.descendant p).center x ≤ (C+Real.sqrt d)*(Q.side/(2:ℝ)^n) := by
    obtain ⟨y,hy,hyb⟩ := (Finset.mem_filter.mp hp).2
    have hc := (Q.descendant p).dist_le (Q.descendant_side_pos hQ p).le
      ((Q.descendant p).center_mem (Q.descendant_side_pos hQ p)) hy
    rw [Q.descendant_side,hS p hp] at hc
    have hb := (mem_ball.mp hyb).le
    have hh := (dist_triangle (Q.descendant p).center y x).trans (add_le_add hc hb)
    nlinarith
  have hh := dyadic_ancestor_ball_count Q hQ S hS (le_refl n) x
    (C := C+Real.sqrt d) (by positivity) (le_refl _) hcenter
  have he : S.image (List.take n) = S := by
    ext p
    constructor
    · intro hp
      obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
      simpa only [List.take_of_length_le (hS q hq).le] using hq
    · intro hp
      exact Finset.mem_image.mpr ⟨p,hp,List.take_of_length_le (hS p hp).le⟩
  rw [he] at hh
  have hc : 2*(C+Real.sqrt d)+2*Real.sqrt d = 2*C+4*Real.sqrt d := by ring
  simpa only [hc] using hh

theorem measure_ball_le_cell_count (Q : DyadicCube d) (hQ : 0 < Q.side)
    (ρ : Measure (Space d)) [IsFiniteMeasure ρ] (hcarry : ρ Q.carrierᶜ = 0)
    (n : ℕ) (x : Space d) (r : ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hcell : ∀ p ∈ cubePaths d n, 0 < ρ (Q.descendant p).carrier →
      (ρ (Q.descendant p).carrier).toReal ≤ M) :
    (ρ (ball x r)).toReal ≤ (cellsMeetingBall Q n x r).card*M := by
  classical
  let S := cellsMeetingBall Q n x r
  have hcover : ball x r ⊆ leafUnion Q S ∪ Q.carrierᶜ := by
    intro y hy
    by_cases hyQ : y ∈ Q.carrier
    · obtain ⟨p,hp,hyp⟩ := Q.mem_descendant_at_depth n hyQ
      exact Or.inl (mem_iUnion₂.mpr ⟨p,Finset.mem_filter.mpr ⟨hp,y,hyp,hy⟩,hyp⟩)
    · exact Or.inr hyQ
  have hmass : ρ (ball x r) ≤ ρ (leafUnion Q S) := by
    apply (measure_mono hcover).trans
    have hh := measure_union_le (leafUnion Q S) Q.carrierᶜ (μ := ρ)
    rwa [hcarry,add_zero] at hh
  calc
    _ ≤ (ρ (leafUnion Q S)).toReal := ENNReal.toReal_mono (measure_ne_top _ _) hmass
    _ = ∑ p ∈ S, (ρ (Q.descendant p).carrier).toReal :=
      restriction_total_mass_real Q hQ ρ (Finset.filter_subset _ _)
    _ ≤ ∑ _p ∈ S, M := by
      apply Finset.sum_le_sum
      intro p hp
      by_cases hpos : 0 < ρ (Q.descendant p).carrier
      · exact hcell p (Finset.mem_filter.mp hp).1 hpos
      · rw [nonpos_iff_eq_zero.mp (le_of_not_gt hpos),ENNReal.toReal_zero]
        exact hM
    _ = _ := by simp [S]

theorem sourceClass_root_null (Q : DyadicCube d) (hQ : 0 < Q.side)
    (μ : Measure (Space d)) (N B : ℕ) (p : CellPath d) :
    sourceClass Q μ N B p Q.carrierᶜ = 0 := by
  simp only [sourceClass,normalizedClass,classMeasure,Measure.smul_apply,smul_eq_mul]
  rw [Measure.restrict_apply Q.measurable.compl]
  have he : Q.carrierᶜ ∩ leafUnion Q
      (classLeaves (regularizationLeaves Q μ N) (regularizationLabel Q μ N B)
        (regularizationLabel Q μ N B p)) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact hx.1 (leafUnion_subset Q hQ _ hx.2)
  rw [he,measure_empty,mul_zero]

theorem sourceClass_ball_upper (Q : DyadicCube d) (hQ : 0 < Q.side)
    (μ : Measure (Space d)) [IsProbabilityMeasure μ] {N B : ℕ} (hN : 0 < N) (hB : 0 < B)
    {lam : ℝ} (hwidth : (B:ℝ) ≤ lam*(N:ℝ))
    (hlarge : (2:ℝ)^(N/B+2) ≤ ((2:ℝ)^N)^lam)
    {p₀ : CellPath d} (hp₀ : p₀ ∈ regularizationLeaves Q μ N)
    {n : ℕ} (hn : n ≤ N) (x : Space d) {C : ℝ} (hC : 0 ≤ C) :
    (sourceClass Q μ N B p₀ (ball x (C*(Q.side/(2:ℝ)^n)))).toReal ≤
      ((2*Nat.ceil (2*C+4*Real.sqrt d)+1)^d:ℕ)*
        (((2:ℝ)^N)^(((d:ℝ)+1)*lam)*((2:ℝ)^N)^(-sourceProfile Q μ N B p₀ n)) := by
  have : IsProbabilityMeasure (sourceClass Q μ N B p₀) :=
    regularization_class_probability Q hQ μ N B hp₀
  have hh := measure_ball_le_cell_count Q hQ (sourceClass Q μ N B p₀)
    (sourceClass_root_null Q hQ μ N B p₀) n x (C*(Q.side/(2:ℝ)^n)) (by positivity)
    (fun p hp hpos => (sourceClass_occupied_comparison Q hQ μ hN hB hwidth hlarge hp₀ hn
      ((mem_cubePaths _ _ _).mp hp) hpos).2)
  apply hh.trans
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact_mod_cast cellsMeetingBall_card Q hQ n x hC (le_refl _)

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_ConditionalBalls
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Full conditional class laws, normalized by the actual cell mass

The profile is only a comparison for that mass. The conditional measure
is the original restricted class law divided by its own cell mass.
-/

namespace Falconer.Regularization
open Set MeasureTheory Metric
open scoped ENNReal
variable {d : ℕ}

theorem conditional_real_le (ρ : Measure (Space d)) [IsFiniteMeasure ρ]
    (A T : Set (Space d)) :
    (ProbabilityTheory.cond ρ A T).toReal ≤ (ρ T).toReal/(ρ A).toReal := by
  unfold ProbabilityTheory.cond
  simp only [Measure.smul_apply,smul_eq_mul,ENNReal.toReal_mul,ENNReal.toReal_inv]
  have hh : ((ρ.restrict A) T).toReal ≤ (ρ T).toReal :=
    ENNReal.toReal_mono (measure_ne_top _ _) (Measure.restrict_apply_le _ _)
  simpa only [div_eq_mul_inv,mul_comm] using
    mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr (show 0 ≤ (ρ A).toReal from ENNReal.toReal_nonneg))

theorem sourceClass_conditional_probability (Q : DyadicCube d) (hQ : 0 < Q.side)
    (μ : Measure (Space d)) [IsProbabilityMeasure μ] (N B : ℕ)
    {p₀ : CellPath d} (hp₀ : p₀ ∈ regularizationLeaves Q μ N) (P : CellPath d)
    (hPpos : 0 < sourceClass Q μ N B p₀ (Q.descendant P).carrier) :
    IsProbabilityMeasure (ProbabilityTheory.cond (sourceClass Q μ N B p₀) (Q.descendant P).carrier) := by
  have : IsProbabilityMeasure (sourceClass Q μ N B p₀) :=
    regularization_class_probability Q hQ μ N B hp₀
  exact ProbabilityTheory.cond_isProbabilityMeasure hPpos.ne'

theorem sourceClass_conditional_ball_upper (Q : DyadicCube d) (hQ : 0 < Q.side)
    (μ : Measure (Space d)) [IsProbabilityMeasure μ] {N B : ℕ} (hN : 0 < N) (hB : 0 < B)
    {lam : ℝ} (hwidth : (B:ℝ) ≤ lam*(N:ℝ))
    (hlarge : (2:ℝ)^(N/B+2) ≤ ((2:ℝ)^N)^lam)
    {p₀ : CellPath d} (hp₀ : p₀ ∈ regularizationLeaves Q μ N)
    {p n : ℕ} (hpN : p ≤ N) (hn : n ≤ N) {P : CellPath d} (hP : P.length = p)
    (hPpos : 0 < sourceClass Q μ N B p₀ (Q.descendant P).carrier)
    (x : Space d) {C : ℝ} (hC : 0 ≤ C) :
    (ProbabilityTheory.cond (sourceClass Q μ N B p₀) (Q.descendant P).carrier
      (ball x (C*(Q.side/(2:ℝ)^n)))).toReal ≤
      ((2*Nat.ceil (2*C+4*Real.sqrt d)+1)^d:ℕ)*((2:ℝ)^N)^
        (sourceProfile Q μ N B p₀ p-sourceProfile Q μ N B p₀ n+2*((d:ℝ)+1)*lam) := by
  have : IsProbabilityMeasure (sourceClass Q μ N B p₀) :=
    regularization_class_probability Q hQ μ N B hp₀
  let R : ℝ := (2:ℝ)^N
  let c : ℝ := ((d:ℝ)+1)*lam
  let mp := sourceProfile Q μ N B p₀ p
  let mn := sourceProfile Q μ N B p₀ n
  let D : ℝ := ((2*Nat.ceil (2*C+4*Real.sqrt d)+1)^d:ℕ)
  have hRp : 0 < R := by dsimp [R]; positivity
  have hb := sourceClass_ball_upper Q hQ μ hN hB hwidth hlarge hp₀ hn x hC
  have hl := (sourceClass_occupied_comparison Q hQ μ hN hB hwidth hlarge hp₀ hpN hP hPpos).1
  have hc := conditional_real_le (sourceClass Q μ N B p₀) (Q.descendant P).carrier
    (ball x (C*(Q.side/(2:ℝ)^n)))
  have hratio := div_le_div₀ (show 0 ≤ D*(R^c*R^(-mn)) by dsimp [D]; positivity)
    hb (show 0 < R^(-c)*R^(-mp) by positivity) (show R^(-c)*R^(-mp) ≤
      (sourceClass Q μ N B p₀ (Q.descendant P).carrier).toReal by
        simpa only [c,mp,R,neg_mul] using hl)
  apply (hc.trans hratio).trans_eq
  change (D*(R^c*R^(-mn)))/(R^(-c)*R^(-mp)) = D*R^(mp-mn+2*((d:ℝ)+1)*lam)
  rw [mul_div_assoc,← Real.rpow_add hRp,← Real.rpow_add hRp,← Real.rpow_sub hRp]
  congr 2
  dsimp [c]
  ring

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_RescaledConditional
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual affine rescaling of a conditional class probability -/

namespace Falconer.Regularization
open Set MeasureTheory Metric
open scoped ENNReal
variable {d : ℕ}

theorem cellScaleMap_continuous (p : ℕ) (c : Space d) : Continuous (cellScaleMap p c) := by
  change Continuous (fun z : Space d => (2:ℝ)^p • (z-c))
  exact (continuous_id.sub continuous_const).const_smul ((2:ℝ)^p)

theorem cellScaleMap_preimage_ball (p : ℕ) (c x : Space d) (r : ℝ) :
    cellScaleMap p c ⁻¹' ball x r = ball (c+((2:ℝ)^p)⁻¹ • x) (r/(2:ℝ)^p) := by
  ext z
  have hs : 0 < (2:ℝ)^p := by positivity
  have he : (2:ℝ)^p • (z-c)-x = (2:ℝ)^p • (z-(c+((2:ℝ)^p)⁻¹ • x)) := by
    simp only [smul_sub,smul_add,smul_smul,mul_inv_cancel₀ hs.ne',one_smul]
    abel
  simp only [mem_preimage,mem_ball,dist_eq_norm,cellScaleMap]
  rw [he,norm_smul,Real.norm_eq_abs,abs_of_pos hs,lt_div_iff₀ hs]
  simp only [mul_comm]

theorem rescaled_conditional_ball_apply (ρ : Measure (Space d)) (p : ℕ) (c : Space d)
    (P : Set (Space d)) (x : Space d) (r : ℝ) :
    (Measure.map (cellScaleMap p c) (ProbabilityTheory.cond ρ P)) (ball x r) =
      ProbabilityTheory.cond ρ P (ball (c+((2:ℝ)^p)⁻¹ • x) (r/(2:ℝ)^p)) := by
  rw [Measure.map_apply (cellScaleMap_continuous p c).measurable measurableSet_ball,
    cellScaleMap_preimage_ball]

theorem sourceClass_rescaled_dyadic_ball (Q : DyadicCube d) (hQ : Q.side = 1)
    (μ : Measure (Space d)) [IsProbabilityMeasure μ] {N B : ℕ} (hN : 0 < N) (hB : 0 < B)
    {lam : ℝ} (hwidth : (B:ℝ) ≤ lam*(N:ℝ))
    (hlarge : (2:ℝ)^(N/B+2) ≤ ((2:ℝ)^N)^lam)
    {p₀ : CellPath d} (hp₀ : p₀ ∈ regularizationLeaves Q μ N)
    {p n : ℕ} (hpn : p ≤ n) (hn : n ≤ N) {P : CellPath d} (hP : P.length = p)
    (hPpos : 0 < sourceClass Q μ N B p₀ (Q.descendant P).carrier)
    (x : Space d) {C : ℝ} (hC : 0 ≤ C) :
    ((Measure.map (cellScaleMap p (Q.descendant P).center)
      (ProbabilityTheory.cond (sourceClass Q μ N B p₀) (Q.descendant P).carrier))
        (ball x (C/(2:ℝ)^(n-p)))).toReal ≤
      ((2*Nat.ceil (2*C+4*Real.sqrt d)+1)^d:ℕ)*((2:ℝ)^N)^
        (sourceProfile Q μ N B p₀ p-sourceProfile Q μ N B p₀ n+2*((d:ℝ)+1)*lam) := by
  rw [rescaled_conditional_ball_apply]
  have hr : (C/(2:ℝ)^(n-p))/(2:ℝ)^p = C*(Q.side/(2:ℝ)^n) := by
    rw [div_div,← pow_add,Nat.sub_add_cancel hpn,hQ]
    ring
  rw [hr]
  exact sourceClass_conditional_ball_upper Q (by rw [hQ]; norm_num) μ hN hB hwidth hlarge hp₀
    (hpn.trans hn) hn hP hPpos _ hC

theorem dyadic_radius_bracket {m : ℕ} {r : ℝ}
    (hmin : 1/(2:ℝ)^m ≤ r) (hmax : r ≤ 1) :
    ∃ j ≤ m, r ≤ 1/(2:ℝ)^j ∧ 1/(2:ℝ)^j ≤ 2*r := by
  induction m with
  | zero =>
    refine ⟨0,le_rfl,?_,?_⟩
    · simpa using hmax
    · norm_num at hmin ⊢
      linarith
  | succ m ih =>
    by_cases hcoarse : 1/(2:ℝ)^m ≤ r
    · obtain ⟨j,hj,hr,hjr⟩ := ih hcoarse
      exact ⟨j,hj.trans (Nat.le_succ m),hr,hjr⟩
    · refine ⟨m,Nat.le_succ m,(lt_of_not_ge hcoarse).le,?_⟩
      have he : 1/(2:ℝ)^m = 2*(1/(2:ℝ)^(m+1)) := by rw [pow_succ]; field_simp
      rw [he]
      linarith

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Measures_ConditionalFrostman
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite-scale Frostman bounds for the full rescaled conditional laws -/

namespace Falconer.Regularization
open Set MeasureTheory Metric
open scoped ENNReal
variable {d : ℕ}

theorem profile_drop_weight (m : ℝ → ℝ) {N : ℕ} (hN : 0 < N) (s E : ℝ)
    {p n t : ℕ} (hpn : p ≤ n) (hnt : n ≤ t) :
    ((2:ℝ)^N)^(m p-m n+E) ≤
      ((2:ℝ)^N)^(profileDrop m N s p t+E)*(1/(2:ℝ)^(n-p))^s := by
  have hR : 0 < (2:ℝ)^N := by positivity
  have hd : (1/(2:ℝ)^(n-p))^s = ((2:ℝ)^N)^(-s*(n-p:ℕ)/N) := by
    rw [one_div,Real.inv_rpow (by positivity),dyadic_power_rpow_as_R hN,
      ← Real.rpow_neg hR.le]
    congr 1
    ring
  rw [hd,← Real.rpow_add hR]
  apply Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num))
  have hh := PlanarFalconer.intervalMin_le (fun k : ℕ => m k-s*(k:ℝ)/N) hpn hnt
  dsimp only [profileDrop]
  rw [Nat.cast_sub hpn]
  calc
    m p-m n+E ≤ m p-(PlanarFalconer.intervalMin
      (fun k : ℕ => m k-s*(k:ℝ)/N) p t+s*(n:ℝ)/N)+E := by linarith
    _ = _ := by ring

theorem sourceClass_conditional_frostman (Q : DyadicCube d) (hQ : Q.side = 1)
    (μ : Measure (Space d)) [IsProbabilityMeasure μ] {N B : ℕ} (hN : 0 < N) (hB : 0 < B)
    {lam s : ℝ} (hs : 0 ≤ s) (hwidth : (B:ℝ) ≤ lam*(N:ℝ))
    (hlarge : (2:ℝ)^(N/B+2) ≤ ((2:ℝ)^N)^lam)
    {p₀ : CellPath d} (hp₀ : p₀ ∈ regularizationLeaves Q μ N)
    {p t : ℕ} (hpt : p ≤ t) (htN : t ≤ N) {P : CellPath d} (hP : P.length = p)
    (hPpos : 0 < sourceClass Q μ N B p₀ (Q.descendant P).carrier) :
    ∀ x : Space d, ∀ r : ℝ, 1/(2:ℝ)^(t-p) ≤ r → r ≤ 1 →
      (Measure.map (cellScaleMap p (Q.descendant P).center)
        (ProbabilityTheory.cond (sourceClass Q μ N B p₀) (Q.descendant P).carrier)) (ball x r) ≤
      ENNReal.ofReal ((((2*Nat.ceil (2+4*Real.sqrt d)+1)^d:ℕ):ℝ)*(2:ℝ)^s*
        ((2:ℝ)^N)^(profileDrop (sourceProfile Q μ N B p₀) N s p t+2*((d:ℝ)+1)*lam)*r^s) := by
  have hside : 0 < Q.side := by rw [hQ]; norm_num
  let α := Measure.map (cellScaleMap p (Q.descendant P).center)
    (ProbabilityTheory.cond (sourceClass Q μ N B p₀) (Q.descendant P).carrier)
  have : IsProbabilityMeasure (ProbabilityTheory.cond (sourceClass Q μ N B p₀)
      (Q.descendant P).carrier) := sourceClass_conditional_probability Q hside μ N B hp₀ P hPpos
  have : IsFiniteMeasure α := by dsimp [α]; infer_instance
  let m := sourceProfile Q μ N B p₀
  let E := 2*((d:ℝ)+1)*lam
  let D : ℝ := ((2*Nat.ceil (2+4*Real.sqrt d)+1)^d:ℕ)
  let R : ℝ := (2:ℝ)^N
  intro x r hr hr₁
  obtain ⟨j,hj,hrj,hjr⟩ := dyadic_radius_bracket hr hr₁
  have hn : p+j ≤ t := by omega
  have hball := sourceClass_rescaled_dyadic_ball Q hQ μ hN hB hwidth hlarge hp₀
    (Nat.le_add_right p j) (hn.trans htN) hP hPpos x (show (0:ℝ) ≤ 1 by norm_num)
  simp only [Nat.add_sub_cancel_left,mul_one] at hball
  have hmono : (α (ball x r)).toReal ≤ (α (ball x (1/(2:ℝ)^j))).toReal :=
    ENNReal.toReal_mono (measure_ne_top α _) (measure_mono (ball_subset_ball hrj))
  have hweight := profile_drop_weight m hN s E (Nat.le_add_right p j) hn
  simp only [Nat.add_sub_cancel_left] at hweight
  have hrpow : (1/(2:ℝ)^j)^s ≤ (2*r)^s :=
    Real.rpow_le_rpow (by positivity) hjr hs
  have hbound : (α (ball x r)).toReal ≤ D*(2:ℝ)^s*R^(profileDrop m N s p t+E)*r^s := by
    calc
      _ ≤ D*R^(m p-m ((p+j:ℕ):ℝ)+E) := hmono.trans hball
      _ ≤ D*(R^(profileDrop m N s p t+E)*(1/(2:ℝ)^j)^s) :=
        mul_le_mul_of_nonneg_left hweight (by dsimp [D]; positivity)
      _ ≤ D*(R^(profileDrop m N s p t+E)*(2*r)^s) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hrpow (by positivity))
          (by dsimp [D]; positivity)
      _ = _ := by rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) (by linarith [hrj,hjr])]; ring
  change α (ball x r) ≤ _
  rw [← ENNReal.ofReal_toReal (measure_ne_top α _)]
  exact ENNReal.ofReal_le_ofReal hbound

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_TroublesomePair
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Measurable troublesome pairs use the full original conditional source law -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal
variable {d : ℕ}

theorem measurable_normalized_vector {X : Type*} [MeasurableSpace X]
    {f : X → Space d} (hf : Measurable f) :
    Measurable (fun x => NormedSpace.normalize (f x)) :=
  hf.norm.inv.smul hf

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_RegularizationRadialGain
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Recombining the actual radial regularization classes without a class-count loss -/

namespace Falconer.Regularization
open Set MeasureTheory NormedSpace
open scoped ENNReal
variable {d : ℕ}

theorem normalized_regularization_class_eq_cond (Q : DyadicCube d) (μ : Measure (Space d))
    (N B : ℕ) (T : List ℕ) :
    normalizedClass Q μ (regularizationLeaves Q μ N) (regularizationLabel Q μ N B) T =
      ProbabilityTheory.cond μ (regularizationSet Q μ N B T) := by
  unfold normalizedClass classMeasure ProbabilityTheory.cond regularizationSet
  rw [Measure.restrict_apply_univ]

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_SourceClassOriginalLaws
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Source regularization preserves almost-everywhere bounds for the original reverse laws -/

namespace Falconer.Regularization
open Set MeasureTheory
variable {d : ℕ}

theorem sourceClass_absolutelyContinuous_ol (Q : DyadicCube d) (μ : Measure (Space d))
    (N B : ℕ) (p : CellPath d) : sourceClass Q μ N B p ≪ μ := by
  unfold sourceClass
  rw [normalized_regularization_class_eq_cond]
  exact ProbabilityTheory.cond_absolutelyContinuous

theorem sourceClass_conditional_absolutelyContinuous (Q : DyadicCube d)
    (μ : Measure (Space d)) (N B : ℕ) (p P : CellPath d) :
    ProbabilityTheory.cond (sourceClass Q μ N B p) (Q.descendant P).carrier ≪ μ :=
  ProbabilityTheory.cond_absolutelyContinuous.trans (sourceClass_absolutelyContinuous_ol Q μ N B p)

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ReverseLawTransfer
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Original reverse cap and slab bounds on the coarser middle scale -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal
variable {d : ℕ}

theorem reverse_caps_transfer (μ ρ ν : Measure (Space d)) (hρ : ρ ≪ μ)
    {G G' : Set (Space d × Space d)} (hsub : G' ⊆ G)
    {N M : ℕ} (hMN : M ≤ N) {K K' q : ℝ} (hK : K ≤ K')
    (hcap : ∀ᵐ z ∂μ, ∀ r : ℝ, 1/(2:ℝ)^N ≤ r → r ≤ 1 →
      ∀ u : Space d, ‖u‖ = 1 →
        ν {x | (z,x) ∈ G ∧ dist (normalize (x-z)) u < r} ≤ ENNReal.ofReal (K*r^q)) :
    ∀ᵐ z ∂ρ, ∀ w : Sphere d, ∀ j : ℕ, j ≤ M →
      ν {x | (z,x) ∈ G' ∧ dist (normalize (x-z)) (w:Space d) < 1/(2:ℝ)^j} ≤
        ENNReal.ofReal (K'*(1/(2:ℝ)^j)^q) := by
  filter_upwards [hρ.ae_le hcap] with z hz
  intro w j hj
  have hr : 1/(2:ℝ)^N ≤ 1/(2:ℝ)^j :=
    one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) (hj.trans hMN))
  have hr1 : 1/(2:ℝ)^j ≤ 1 := (div_le_one (by positivity)).mpr (one_le_pow₀ (by norm_num))
  have hmono : ν {x | (z,x) ∈ G' ∧ dist (normalize (x-z)) (w:Space d) < 1/(2:ℝ)^j} ≤
      ν {x | (z,x) ∈ G ∧ dist (normalize (x-z)) (w:Space d) < 1/(2:ℝ)^j} :=
    measure_mono (fun _ hx => ⟨hsub hx.1,hx.2⟩)
  apply hmono.trans ((hz _ hr hr1 w (sphere_norm w)).trans ?_)
  exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hK (by positivity))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_ReverseCapsAllRadii
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reverse-cap bounds under source restriction at every original radius -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal
variable {d : ℕ}

theorem reverse_caps_all_radii (μ ρ ν : Measure (Space d)) (hρ : ρ ≪ μ)
    {G G' : Set (Space d × Space d)} (hsub : G' ⊆ G)
    {N v : ℕ} (hvN : v ≤ N) {K K' q : ℝ} (hK : K ≤ K')
    (hcap : ∀ᵐ z ∂μ, ∀ r : ℝ, 1/(2:ℝ)^N ≤ r → r ≤ 1 →
      ∀ u : Space d, ‖u‖ = 1 →
        ν {x | (z,x) ∈ G ∧ dist (normalize (x-z)) u < r} ≤ ENNReal.ofReal (K*r^q)) :
    ∀ᵐ z ∂ρ, ∀ r : ℝ, 1/(2:ℝ)^v ≤ r → r ≤ 1 →
      ∀ u : Space d, ‖u‖ = 1 →
        ν {x | (z,x) ∈ G' ∧ dist (normalize (x-z)) u < r} ≤ ENNReal.ofReal (K'*r^q) := by
  filter_upwards [hρ.ae_le hcap] with z hz
  intro r hr hr1 u hu
  have hδ : 1/(2:ℝ)^N ≤ 1/(2:ℝ)^v :=
    one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) hvN)
  have hm : ν {x | (z,x) ∈ G' ∧ dist (normalize (x-z)) u < r} ≤
      ν {x | (z,x) ∈ G ∧ dist (normalize (x-z)) u < r} :=
    measure_mono (fun _ hx => ⟨hsub hx.1,hx.2⟩)
  apply hm.trans ((hz r (hδ.trans hr) hr1 u hu).trans ?_)
  exact ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_right hK (Real.rpow_nonneg ((by positivity : (0:ℝ) ≤ 1/(2:ℝ)^v).trans hr) _))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_OccupiedRadialTree
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Occupied dyadic trees with a common full-measure source core -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}
attribute [local instance] Classical.propDecidable

theorem DyadicCube.emptyTreeCells_measurable (Q : DyadicCube d)
    (μ : Measure (Space d)) (N : ℕ) : MeasurableSet (Q.emptyTreeCells μ N) := by
  apply Finset.measurableSet_biUnion
  intro n _
  exact Finset.measurableSet_biUnion _ (fun p _ => (Q.descendant p).measurable)

theorem DyadicCube.emptyTreeCells_null (Q : DyadicCube d)
    (μ : Measure (Space d)) (N : ℕ) : μ (Q.emptyTreeCells μ N) = 0 := by
  apply le_antisymm _ zero_le
  apply (measure_biUnion_finset_le _ _).trans
  apply Finset.sum_nonpos
  intro n _
  apply (measure_biUnion_finset_le _ _).trans
  apply Finset.sum_nonpos
  intro p hp
  obtain ⟨hp,hno⟩ := Finset.mem_sdiff.mp hp
  have hn : ¬ 0 < μ (Q.descendant p).carrier := by
    intro h
    exact hno (Finset.mem_filter.mpr ⟨hp,h⟩)
  exact le_of_not_gt hn

theorem DyadicCube.occupiedTreeCore_measurable (Q : DyadicCube d)
    (μ : Measure (Space d)) (N : ℕ) : MeasurableSet (Q.occupiedTreeCore μ N) :=
  Q.measurable.diff (Q.emptyTreeCells_measurable μ N)

theorem DyadicCube.occupiedTreeCore_full (Q : DyadicCube d)
    (μ : Measure (Space d)) (N : ℕ) (hroot : μ Q.carrierᶜ = 0) :
    μ (Q.occupiedTreeCore μ N)ᶜ = 0 := by
  classical
  have he : (Q.occupiedTreeCore μ N)ᶜ = Q.carrierᶜ ∪ Q.emptyTreeCells μ N := by
    ext x
    simp only [occupiedTreeCore,mem_compl_iff,mem_sdiff,mem_union]
    tauto
  rw [he]
  apply le_antisymm _ zero_le
  exact (measure_union_le _ _).trans_eq (by rw [hroot,Q.emptyTreeCells_null,zero_add])

theorem DyadicCube.occupiedTreeCore_cover (Q : DyadicCube d)
    (μ : Measure (Space d)) {N n : ℕ} (hn : n ≤ N)
    {x : Space d} (hx : x ∈ Q.occupiedTreeCore μ N) :
    ∃ p ∈ Q.occupiedPaths μ n, x ∈ (Q.descendant p).carrier := by
  classical
  obtain ⟨p,hp,hxp⟩ := Q.mem_descendant_at_depth n hx.1
  refine ⟨p,?_,hxp⟩
  by_contra hno
  exact hx.2 (mem_iUnion₂.mpr ⟨n,Finset.mem_range.mpr (by omega),
    mem_iUnion₂.mpr ⟨p,Finset.mem_sdiff.mpr ⟨hp,hno⟩,hxp⟩⟩)

theorem DyadicCube.occupied_parent (Q : DyadicCube d) (hQ : 0 < Q.side)
    (μ : Measure (Space d)) {a b : ℕ} (hab : a ≤ b)
    {p : List (Fin d → Bool)} (hp : p ∈ Q.occupiedPaths μ b) :
    p.take a ∈ Q.occupiedPaths μ a ∧
      (Q.descendant p).carrier ⊆ (Q.descendant (p.take a)).carrier := by
  obtain ⟨hp,hpos⟩ := Finset.mem_filter.mp hp
  have hlen := (mem_cubePaths d b p).mp hp
  have hsub := Regularization.descendant_subset_take Q hQ p a
  refine ⟨Finset.mem_filter.mpr ⟨?_,hpos.trans_le (measure_mono hsub)⟩,hsub⟩
  exact (mem_cubePaths d a _).mpr (by simp only [List.length_take,hlen,Nat.min_eq_left hab])

theorem DyadicCube.occupied_diameter_bound (Q : DyadicCube d) (hQ : 0 < Q.side)
    (μ : Measure (Space d)) {n : ℕ} {p : List (Fin d → Bool)}
    (hp : p ∈ Q.occupiedPaths μ n) {y z : Space d}
    (hy : y ∈ (Q.descendant p).carrier) (hz : z ∈ (Q.descendant p).carrier) :
    ‖y-z‖ ≤ Real.sqrt d*(Q.side/(2:ℝ)^n) := by
  have hlen := (mem_cubePaths d n p).mp (Finset.mem_filter.mp hp).1
  simpa only [dist_eq_norm,Q.descendant_side,hlen] using
    (Q.descendant p).dist_le (Q.descendant_side_pos hQ p).le hy hz

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_OccupiedCellSeparation
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Separation extends from the full source set to sufficiently small occupied cells -/

namespace Falconer
open Set MeasureTheory
variable {d : ℕ}
attribute [local instance] Classical.propDecidable

theorem exists_mem_cell_source (μ : Measure (Space d)) (A C : Set (Space d))
    (hA : μ Aᶜ = 0) (hC : 0 < μ C) : ∃ z ∈ C, z ∈ A := by
  by_contra hn
  have hsub : C ⊆ Aᶜ := by
    intro z hz hzA
    exact hn ⟨z,hz,hzA⟩
  exact (not_le_of_gt hC) ((measure_mono hsub).trans_eq hA)

theorem occupied_cell_separation (Q : DyadicCube d) (hQ : 0 < Q.side)
    (μ : Measure (Space d)) (A B : Set (Space d)) (hA : μ Aᶜ = 0)
    {s : ℝ} (hsep : ∀ z ∈ A, ∀ x ∈ B, s ≤ ‖z-x‖)
    {n : ℕ} (hsmall : Real.sqrt d*(Q.side/(2:ℝ)^n) ≤ s/2)
    {P : List (Fin d → Bool)} (hP : P ∈ Q.occupiedPaths μ n) :
    ∀ x ∈ B, ∀ y ∈ (Q.descendant P).carrier, s/2 ≤ ‖y-x‖ := by
  obtain ⟨z,hz,hzA⟩ := exists_mem_cell_source μ A (Q.descendant P).carrier hA
    (Finset.mem_filter.mp hP).2
  intro x hx y hy
  have hd := Q.occupied_diameter_bound hQ μ hP hz hy
  have ht := norm_sub_le_norm_sub_add_norm_sub z y x
  have hs := hsep z hzA x hx
  linarith

theorem occupied_cell_center_separation (Q : DyadicCube d) (hQ : 0 < Q.side)
    (μ : Measure (Space d)) (A B : Set (Space d)) (hA : μ Aᶜ = 0)
    {s : ℝ} (hsep : ∀ z ∈ A, ∀ x ∈ B, s ≤ ‖z-x‖)
    {n : ℕ} (hsmall : Real.sqrt d*(Q.side/(2:ℝ)^n) ≤ s/2)
    {P : List (Fin d → Bool)} (hP : P ∈ Q.occupiedPaths μ n) :
    ∀ x ∈ B, s/2 ≤ ‖(Q.descendant P).center-x‖ := by
  intro x hx
  exact occupied_cell_separation Q hQ μ A B hA hsep hsmall hP x hx _
    ((Q.descendant P).center_mem (Q.descendant_side_pos hQ P))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_RadialCollisionMass
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Measurable radial collision masses and the original-pin Fubini identity -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal
variable {d : ℕ}

theorem radialCollisionRelation_measurable (δ : ℝ) :
    MeasurableSet {p : (Space d × Space d) × Space d |
      dist (normalize (p.2-p.1.2)) (normalize (p.1.1-p.1.2)) ≤ δ} := by
  exact measurableSet_le
    ((measurable_normalized_vector (measurable_snd.sub measurable_fst.snd)).dist
      (measurable_normalized_vector (measurable_fst.fst.sub measurable_fst.snd)))
    measurable_const

theorem radialCollisionMass_measurable (μ : Measure (Space d)) [SFinite μ] (δ : ℝ) :
    Measurable (radialCollisionMass μ δ) :=
  measurable_measure_prodMk_left (radialCollisionRelation_measurable δ)

theorem radial_collision_original_pin_fubini (μ ν : Measure (Space d))
    [SFinite μ] [SFinite ν] (G : Set (Space d × Space d)) (_hG : MeasurableSet G)
    (z : Space d) (δ : ℝ) :
    (∫⁻ x in {x | (z,x) ∈ G}, radialCollisionMass μ δ (z,x) ∂ν) =
      ∫⁻ y, ν {x | (z,x) ∈ G ∧
        dist (normalize (y-x)) (normalize (z-x)) ≤ δ} ∂μ := by
  let A : Set (Space d × Space d) :=
    {p | dist (normalize (p.2-p.1)) (normalize (z-p.1)) ≤ δ}
  have hA : MeasurableSet A := by
    exact measurableSet_le
      ((measurable_normalized_vector (measurable_snd.sub measurable_fst)).dist
        (measurable_normalized_vector (measurable_const.sub measurable_fst)))
      measurable_const
  calc
    _ = ((ν.restrict {x | (z,x) ∈ G}).prod μ) A := (Measure.prod_apply hA).symm
    _ = ∫⁻ y, (ν.restrict {x | (z,x) ∈ G}) {x | (x,y) ∈ A} ∂μ :=
      Measure.prod_apply_symm hA
    _ = _ := by
      apply lintegral_congr
      intro y
      have hAy : MeasurableSet {x : Space d | (x,y) ∈ A} :=
        hA.preimage (measurable_id.prodMk measurable_const)
      rw [Measure.restrict_apply hAy]
      congr 1
      ext x
      simp only [A,mem_inter_iff,mem_ofPred_eq]
      exact and_comm

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Measures_CellwiseCollisionPruning
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Combining conditional-cell radial pruning with the original source weights -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ} {ι : Type*}

theorem cellwise_radial_collision_pruning (μ ν : Measure (Space d))
    [IsFiniteMeasure μ] [SFinite ν]
    (I : Finset ι) (Q : ι → Set (Space d))
    (hQ : ∀ i ∈ I, MeasurableSet (Q i)) (hpos : ∀ i ∈ I, μ (Q i) ≠ 0)
    (hdisj : (I : Set ι).PairwiseDisjoint Q)
    (G : Set (Space d × Space d)) (hG : MeasurableSet G)
    (H : ι → Set (Space d × Space d)) (hH : ∀ i ∈ I, MeasurableSet (H i))
    (δ : ℝ) (F : ι → ℝ≥0∞) (cost : ℝ≥0∞)
    (hcost : ∀ i ∈ I, ((ProbabilityTheory.cond μ (Q i)).prod ν)
      ((G ∩ (Q i ×ˢ univ)) \ H i) ≤ cost)
    (hlocal : ∀ i ∈ I, ∀ p ∈ H i,
      radialCollisionMass (ProbabilityTheory.cond μ (Q i)) δ p ≤ F i) :
    ∃ G' : Set (Space d × Space d), MeasurableSet G' ∧ G' ⊆ G ∧
      (μ.prod ν) (G \ G') ≤ cost*μ univ ∧
      ∀ i ∈ I, ∀ p ∈ G', p.1 ∈ Q i →
        radialCollisionMass (ProbabilityTheory.cond μ (Q i)) δ p ≤ F i := by
  classical
  let E := fun i => (G ∩ (Q i ×ˢ univ)) \ H i
  let D := ⋃ i ∈ I, E i ∩ (Q i ×ˢ univ)
  have hE : ∀ i ∈ I, MeasurableSet (E i) := fun i hi =>
    (hG.inter ((hQ i hi).prod MeasurableSet.univ)).diff (hH i hi)
  have hD : MeasurableSet D := Finset.measurableSet_biUnion I
    (fun i hi => (hE i hi).inter ((hQ i hi).prod MeasurableSet.univ))
  refine ⟨G \ D,hG.diff hD,sdiff_subset,?_,?_⟩
  · apply (measure_mono _).trans
      (conditional_cellwise_pair_deletion μ ν I Q E hQ hE hpos hdisj cost hcost)
    intro p hp
    by_contra hn
    exact hp.2 ⟨hp.1,hn⟩
  · intro i hi p hp hpQ
    apply hlocal i hi p
    by_contra hn
    apply hp.2
    exact mem_iUnion₂.mpr ⟨i,hi,⟨⟨⟨hp.1,hpQ,mem_univ _⟩,hn⟩,hpQ,mem_univ _⟩⟩

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Measures_FiniteRelativePruning
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite pruning relative to the incoming measurable relation -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal BigOperators
variable {X : Type*} [MeasurableSpace X]

theorem finite_relative_pruning (μ : Measure X) (G : Set X) (hG : MeasurableSet G)
    (J : ℕ) (cost : ℕ → ℝ≥0∞) (P : ℕ → X → Prop)
    (hlocal : ∀ j < J, ∃ H : Set X, MeasurableSet H ∧ H ⊆ G ∧
      μ (G \ H) ≤ cost j ∧ ∀ x ∈ H, P j x) :
    ∃ H : Set X, MeasurableSet H ∧ H ⊆ G ∧
      μ (G \ H) ≤ ∑ j ∈ Finset.range J, cost j ∧ ∀ j < J, ∀ x ∈ H, P j x := by
  classical
  have hex : ∀ j : ℕ, ∃ H : Set X, MeasurableSet H ∧ H ⊆ G ∧
      (j < J → μ (G \ H) ≤ cost j ∧ ∀ x ∈ H, P j x) := by
    intro j
    by_cases hj : j < J
    · obtain ⟨H,hH,hHG,hcost,hP⟩ := hlocal j hj
      exact ⟨H,hH,hHG,fun _ => ⟨hcost,hP⟩⟩
    · exact ⟨G,hG,Subset.rfl,fun h => (hj h).elim⟩
  choose H hH hHG hrest using hex
  let B := ⋃ j ∈ Finset.range J, G \ H j
  have hB : MeasurableSet B := Finset.measurableSet_biUnion _ (fun j _ => hG.diff (hH j))
  refine ⟨G \ B,hG.diff hB,sdiff_subset,?_,?_⟩
  · have hsub : G \ (G \ B) ⊆ B := by
      intro x hx
      by_contra hn
      exact hx.2 ⟨hx.1,hn⟩
    apply (measure_mono hsub).trans
    apply (measure_biUnion_finset_le _ _).trans
    exact Finset.sum_le_sum (fun j hj => (hrest j (Finset.mem_range.mp hj)).1)
  · intro j hj x hx
    apply (hrest j hj).2 x
    by_contra hn
    exact hx.2 (mem_iUnion₂.mpr ⟨j,Finset.mem_range.mpr hj,⟨hx.1,hn⟩⟩)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_FiniteCellwiseCollision
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite families of local collision prunings with their original cell weights -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal BigOperators
variable {d : ℕ} {ι : Type*}

theorem cellwise_collision_pruning_of_exists (μ ν : Measure (Space d))
    [IsFiniteMeasure μ] [SFinite ν]
    (I : Finset ι) (Q : ι → Set (Space d))
    (hQ : ∀ i ∈ I, MeasurableSet (Q i)) (hpos : ∀ i ∈ I, μ (Q i) ≠ 0)
    (hdisj : (I : Set ι).PairwiseDisjoint Q)
    (G : Set (Space d × Space d)) (hG : MeasurableSet G)
    (δ : ℝ) (F : ι → ℝ≥0∞) (cost : ℝ≥0∞)
    (hlocal : ∀ i ∈ I, ∃ H : Set (Space d × Space d), MeasurableSet H ∧
      ((ProbabilityTheory.cond μ (Q i)).prod ν) ((G ∩ (Q i ×ˢ univ)) \ H) ≤ cost ∧
      ∀ p ∈ H, radialCollisionMass (ProbabilityTheory.cond μ (Q i)) δ p ≤ F i) :
    ∃ H : Set (Space d × Space d), MeasurableSet H ∧ H ⊆ G ∧
      (μ.prod ν) (G \ H) ≤ cost*μ univ ∧
      ∀ i ∈ I, ∀ p ∈ H, p.1 ∈ Q i →
        radialCollisionMass (ProbabilityTheory.cond μ (Q i)) δ p ≤ F i := by
  classical
  have hex : ∀ i, ∃ H : Set (Space d × Space d), MeasurableSet H ∧
      (i ∈ I → ((ProbabilityTheory.cond μ (Q i)).prod ν)
        ((G ∩ (Q i ×ˢ univ)) \ H) ≤ cost ∧
        ∀ p ∈ H, radialCollisionMass (ProbabilityTheory.cond μ (Q i)) δ p ≤ F i) := by
    intro i
    by_cases hi : i ∈ I
    · obtain ⟨H,hH,hcost,hbound⟩ := hlocal i hi
      exact ⟨H,hH,fun _ => ⟨hcost,hbound⟩⟩
    · exact ⟨∅,MeasurableSet.empty,fun h => (hi h).elim⟩
  choose H hH hrest using hex
  exact cellwise_radial_collision_pruning μ ν I Q hQ hpos hdisj G hG H (fun i _ => hH i)
    δ F cost (fun i hi => (hrest i hi).1) (fun i hi => (hrest i hi).2)

theorem finite_cellwise_collision_pruning (μ ν : Measure (Space d))
    [IsFiniteMeasure μ] [SFinite ν]
    (J : ℕ) (I : ℕ → Finset ι) (Q : ℕ → ι → Set (Space d))
    (hQ : ∀ j < J, ∀ i ∈ I j, MeasurableSet (Q j i))
    (hpos : ∀ j < J, ∀ i ∈ I j, μ (Q j i) ≠ 0)
    (hdisj : ∀ j < J, (I j : Set ι).PairwiseDisjoint (Q j))
    (G : Set (Space d × Space d)) (hG : MeasurableSet G)
    (δ : ℕ → ℝ) (F : ℕ → ι → ℝ≥0∞) (cost : ℕ → ℝ≥0∞)
    (hlocal : ∀ j < J, ∀ i ∈ I j, ∃ H : Set (Space d × Space d), MeasurableSet H ∧
      ((ProbabilityTheory.cond μ (Q j i)).prod ν) ((G ∩ (Q j i ×ˢ univ)) \ H) ≤ cost j ∧
      ∀ p ∈ H, radialCollisionMass (ProbabilityTheory.cond μ (Q j i)) (δ j) p ≤ F j i) :
    ∃ H : Set (Space d × Space d), MeasurableSet H ∧ H ⊆ G ∧
      (μ.prod ν) (G \ H) ≤ ∑ j ∈ Finset.range J, cost j*μ univ ∧
      ∀ j < J, ∀ i ∈ I j, ∀ p ∈ H, p.1 ∈ Q j i →
        radialCollisionMass (ProbabilityTheory.cond μ (Q j i)) (δ j) p ≤ F j i := by
  have hlevels : ∀ j < J, ∃ H : Set (Space d × Space d), MeasurableSet H ∧ H ⊆ G ∧
      (μ.prod ν) (G \ H) ≤ cost j*μ univ ∧
      ∀ p ∈ H, ∀ i ∈ I j, p.1 ∈ Q j i →
        radialCollisionMass (ProbabilityTheory.cond μ (Q j i)) (δ j) p ≤ F j i := by
    intro j hj
    obtain ⟨H,hH,hHG,hcost,hbound⟩ := cellwise_collision_pruning_of_exists μ ν (I j) (Q j)
      (hQ j hj) (hpos j hj) (hdisj j hj) G hG (δ j) (F j) (cost j) (hlocal j hj)
    exact ⟨H,hH,hHG,hcost,fun p hp i hi hpQ => hbound i hi p hp hpQ⟩
  obtain ⟨H,hH,hHG,hcost,hbound⟩ := finite_relative_pruning (μ.prod ν) G hG J
    (fun j => cost j*μ univ) (fun j p => ∀ i ∈ I j, p.1 ∈ Q j i →
      radialCollisionMass (ProbabilityTheory.cond μ (Q j i)) (δ j) p ≤ F j i) hlevels
  exact ⟨H,hH,hHG,hcost,fun j hj i hi p hp hpQ => hbound j hj p hp i hi hpQ⟩

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Measures_FiberDensityPruning
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Density pruning uses the original fibers in every retained cell -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {P X ι : Type*} [MeasurableSpace P] [MeasurableSpace X]

theorem fiberDensityBad_measurable (μ : Measure X) [SFinite μ]
    (G : Set (P × X)) (hG : MeasurableSet G) (Q : ι → Set X)
    (I : Finset ι) (hQ : ∀ i ∈ I, MeasurableSet (Q i)) (θ : ℝ≥0∞) :
    MeasurableSet (fiberDensityBad μ G Q I θ) := by
  apply hG.inter
  apply Finset.measurableSet_biUnion I
  intro i hi
  have hS : MeasurableSet ((univ ×ˢ Q i) ∩ G) := (MeasurableSet.univ.prod (hQ i hi)).inter hG
  have hm : Measurable (fun p => μ (Q i ∩ Prod.mk p ⁻¹' G)) := by
    convert measurable_measure_prodMk_left (ν := μ) hS using 1
    all_goals try with_reducible_and_instances rfl
    ext p
    congr 1
    ext x
    simp only [mem_inter_iff,mem_preimage,mem_prod,mem_univ,true_and]
  exact (measurableSet_lt hm measurable_const).prod (hQ i hi)

omit [MeasurableSpace P] in
theorem fiberDensityBad_fiber_mass (μ : Measure X) (G : Set (P × X))
    (Q : ι → Set X) (I : Finset ι) (hQ : ∀ i ∈ I, MeasurableSet (Q i))
    (hdisj : (I : Set ι).PairwiseDisjoint Q) (θ : ℝ≥0∞) (p : P) :
    μ (Prod.mk p ⁻¹' fiberDensityBad μ G Q I θ) ≤ θ*μ univ := by
  classical
  let D := I.filter (fun i => μ (Q i ∩ Prod.mk p ⁻¹' G) < θ*μ (Q i))
  have hs : Prod.mk p ⁻¹' fiberDensityBad μ G Q I θ =
      ⋃ i ∈ D, Q i ∩ Prod.mk p ⁻¹' G := by
    ext x
    simp only [fiberDensityBad,mem_preimage,mem_inter_iff,mem_iUnion,mem_prod,
      mem_ofPred_eq,D,Finset.mem_filter]
    aesop
  have hsum : ∑ i ∈ I, μ (Q i) ≤ μ univ := by
    rw [← measure_biUnion_finset hdisj hQ]
    exact measure_mono (subset_univ _)
  rw [hs]
  calc
    _ ≤ ∑ i ∈ D, μ (Q i ∩ Prod.mk p ⁻¹' G) := measure_biUnion_finset_le D _
    _ ≤ ∑ i ∈ D, θ*μ (Q i) := Finset.sum_le_sum (fun i hi => (Finset.mem_filter.mp hi).2.le)
    _ ≤ ∑ i ∈ I, θ*μ (Q i) := Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    _ = θ*(∑ i ∈ I, μ (Q i)) := (Finset.mul_sum _ _ _).symm
    _ ≤ θ*μ univ := mul_le_mul' le_rfl hsum

theorem fiberDensityBad_product_mass (ν : Measure P) (μ : Measure X) [SFinite μ]
    (G : Set (P × X)) (hG : MeasurableSet G) (Q : ι → Set X)
    (I : Finset ι) (hQ : ∀ i ∈ I, MeasurableSet (Q i))
    (hdisj : (I : Set ι).PairwiseDisjoint Q) (θ : ℝ≥0∞) :
    (ν.prod μ) (fiberDensityBad μ G Q I θ) ≤ (θ*μ univ)*ν univ := by
  rw [Measure.prod_apply (fiberDensityBad_measurable μ G hG Q I hQ θ)]
  calc
    _ ≤ ∫⁻ _p, θ*μ univ ∂ν := lintegral_mono (fiberDensityBad_fiber_mass μ G Q I hQ hdisj θ)
    _ = _ := by rw [lintegral_const,mul_comm]

omit [MeasurableSpace P] in
theorem fiberDensity_retained (μ : Measure X) (G : Set (P × X))
    (Q : ι → Set X) (I : Finset ι) (θ : ℝ≥0∞) {p : P} {x : X}
    (hx : (p,x) ∈ G \ fiberDensityBad μ G Q I θ)
    {i : ι} (hi : i ∈ I) (hxi : x ∈ Q i) :
    θ*μ (Q i) ≤ μ (Q i ∩ Prod.mk p ⁻¹' G) := by
  by_contra! hlt
  apply hx.2
  refine ⟨hx.1,mem_iUnion.mpr ⟨i,mem_iUnion.mpr ⟨hi,?_⟩⟩⟩
  exact ⟨hlt,hxi⟩

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Measures_DensityCellCharge
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Charging the full masses of hit children before the final density deletion -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {X ι : Type*} [MeasurableSpace X]

theorem density_hit_children_charge (μ : Measure X) (S P T : Set X)
    (hS : MeasurableSet S) (Q : ι → Set X) (I : Finset ι)
    (hQ : ∀ i ∈ I, MeasurableSet (Q i)) (hdisj : (I : Set ι).PairwiseDisjoint Q)
    {θ F : ℝ≥0∞} (hθ : 0 < θ) (hθtop : θ ≠ ∞)
    (hdensity : ∀ i ∈ I, θ*μ (Q i) ≤ μ (Q i ∩ S))
    (hlocal : ∀ i ∈ I, Q i ∩ S ⊆ P ∩ T)
    (htest : μ (P ∩ T) ≤ F*μ P) :
    (∑ i ∈ I, μ (Q i)) ≤ (θ⁻¹*F)*μ P := by
  have hi : (I : Set ι).PairwiseDisjoint (fun i => Q i ∩ S) := by
    intro i hi j hj hij
    exact (hdisj hi hj hij).mono inter_subset_left inter_subset_left
  have hm : θ*(∑ i ∈ I, μ (Q i)) ≤ F*μ P := by
    calc
      _ = ∑ i ∈ I, θ*μ (Q i) := Finset.mul_sum _ _ _
      _ ≤ ∑ i ∈ I, μ (Q i ∩ S) := Finset.sum_le_sum hdensity
      _ = μ (⋃ i ∈ I, Q i ∩ S) := (measure_biUnion_finset hi (fun i hi => (hQ i hi).inter hS)).symm
      _ ≤ μ (P ∩ T) := measure_mono (iUnion₂_subset hlocal)
      _ ≤ _ := htest
  calc
    _ = θ⁻¹*(θ*(∑ i ∈ I, μ (Q i))) := by
      rw [← mul_assoc,ENNReal.inv_mul_cancel hθ.ne' hθtop,one_mul]
    _ ≤ θ⁻¹*(F*μ P) := mul_le_mul' le_rfl hm
    _ = _ := (mul_assoc _ _ _).symm

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Measures_MultiscaleDensityPruning
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Simultaneous density pruning at finitely many endpoint depths -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {P X ι : Type*} [MeasurableSpace P] [MeasurableSpace X]

theorem multiscaleFiberBad_measurable (μ : Measure X) [SFinite μ]
    (G : Set (P × X)) (hG : MeasurableSet G) (Q : ℕ → ι → Set X)
    (I : ℕ → Finset ι) (θ : ℝ≥0∞) (J : ℕ)
    (hQ : ∀ j ≤ J, ∀ i ∈ I j, MeasurableSet (Q j i)) : MeasurableSet (multiscaleFiberBad μ G Q I θ J) := by
  apply Finset.measurableSet_biUnion
  intro j hj
  exact fiberDensityBad_measurable μ G hG (Q j) (I j) (hQ j (by simpa using hj)) θ

theorem multiscaleFiberBad_mass (ν : Measure P) (μ : Measure X) [SFinite μ]
    (G : Set (P × X)) (hG : MeasurableSet G) (Q : ℕ → ι → Set X)
    (I : ℕ → Finset ι) (J : ℕ)
    (hQ : ∀ j ≤ J, ∀ i ∈ I j, MeasurableSet (Q j i))
    (hdisj : ∀ j ≤ J, (I j : Set ι).PairwiseDisjoint (Q j)) (θ : ℝ≥0∞) :
    (ν.prod μ) (multiscaleFiberBad μ G Q I θ J) ≤ (J+1:ℝ≥0∞)*(θ*μ univ)*ν univ := by
  calc
    _ ≤ ∑ j ∈ Finset.range (J+1), (ν.prod μ) (fiberDensityBad μ G (Q j) (I j) θ) :=
      measure_biUnion_finset_le _ _
    _ ≤ ∑ _j ∈ Finset.range (J+1), (θ*μ univ)*ν univ := by
      apply Finset.sum_le_sum
      intro j hj
      have hjJ : j ≤ J := by simpa using hj
      exact fiberDensityBad_product_mass ν μ G hG (Q j) (I j) (hQ j hjJ) (hdisj j hjJ) θ
    _ = _ := by simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,Nat.cast_add,Nat.cast_one]; ring

omit [MeasurableSpace P] in
theorem multiscaleFiber_retained (μ : Measure X) (G : Set (P × X))
    (Q : ℕ → ι → Set X) (I : ℕ → Finset ι) (θ : ℝ≥0∞) (J : ℕ)
    {p : P} {x : X} (hx : (p,x) ∈ G \ multiscaleFiberBad μ G Q I θ J)
    {j : ℕ} (hj : j ≤ J) {i : ι} (hi : i ∈ I j) (hxi : x ∈ Q j i) :
    θ*μ (Q j i) ≤ μ (Q j i ∩ Prod.mk p ⁻¹' G) := by
  apply fiberDensity_retained μ G (Q j) (I j) θ ⟨hx.1,?_⟩ hi hxi
  intro hbad
  apply hx.2
  exact mem_iUnion.mpr ⟨j,mem_iUnion.mpr ⟨by simpa using hj,hbad⟩⟩

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_RadialFreezing
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Freezing radial directions in a source cell away from its pin -/

namespace Falconer
open NormedSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem normalize_distance_scaled {u v : E} {r : ℝ}
    (hu : r ≤ ‖u‖) (hv : v ≠ 0) :
    r*dist (normalize u) (normalize v) ≤ 2*dist u v := by
  have he : ‖u‖ • (normalize u-normalize v) =
      u-v+(‖v‖-‖u‖) • normalize v := by
    rw [smul_sub,norm_smul_normalize,sub_smul,norm_smul_normalize]
    abel
  have hb := norm_add_le (u-v) ((‖v‖-‖u‖) • normalize v)
  rw [← he,norm_smul,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _),
    norm_smul,Real.norm_eq_abs,norm_normalize hv,mul_one] at hb
  have hn := abs_norm_sub_norm_le v u
  rw [norm_sub_rev v u] at hn
  rw [dist_eq_norm,dist_eq_norm]
  have hh := mul_le_mul_of_nonneg_right hu (norm_nonneg (normalize u-normalize v))
  linarith

theorem perpendicular_normalize_self (v : E) : perpendicularPart (normalize v) v = 0 := by
  by_cases hv : v = 0
  · simp [hv,perpendicularPart,NormedSpace.normalize]
  · have he : v = ‖v‖ • normalize v := (norm_smul_normalize v).symm
    calc
      _ = perpendicularPart (normalize v) (‖v‖ • normalize v) := congrArg _ he
      _ = ‖v‖ • perpendicularPart (normalize v) (normalize v) := perpendicularPart_smul _ _ _
      _ = 0 := by simp [perpendicularPart,norm_normalize hv]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Measures_FiniteMassMultiplication
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite multiplication of the charged hit-cell masses -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal BigOperators
variable {ι : Type*} [DecidableEq ι]

theorem finite_parent_mass_step (P C : Finset ι) (parent : ι → ι)
    (wp wc : ι → ℝ≥0∞) (F : ℝ≥0∞) (hparent : ∀ i ∈ C, parent i ∈ P)
    (hcharge : ∀ p ∈ P, (∑ i ∈ C with parent i = p, wc i) ≤ F*wp p) :
    (∑ i ∈ C, wc i) ≤ F*(∑ p ∈ P, wp p) := by
  classical
  calc
    _ = ∑ p ∈ P, ∑ i ∈ C with parent i = p, wc i :=
      (Finset.sum_fiberwise_of_maps_to hparent wc).symm
    _ ≤ ∑ p ∈ P, F*wp p := Finset.sum_le_sum hcharge
    _ = _ := (Finset.mul_sum _ _ _).symm

theorem finite_mass_multiplication (I : ℕ → Finset ι) (parent : ℕ → ι → ι)
    (w : ℕ → ι → ℝ≥0∞) (F : ℕ → ℝ≥0∞) (J : ℕ)
    (hparent : ∀ j < J, ∀ i ∈ I (j+1), parent j i ∈ I j)
    (hcharge : ∀ j < J, ∀ p ∈ I j,
      (∑ i ∈ I (j+1) with parent j i = p, w (j+1) i) ≤ F j*w j p) :
    (∑ i ∈ I J, w J i) ≤ (∏ j ∈ Finset.range J, F j)*(∑ i ∈ I 0, w 0 i) := by
  classical
  induction J with
  | zero => simp
  | succ J ih =>
    have hs : (∑ i ∈ I (J+1), w (J+1) i) ≤ F J*(∑ i ∈ I J, w J i) :=
      finite_parent_mass_step (I J) (I (J+1)) (parent J) (w J) (w (J+1)) (F J)
        (hparent J (Nat.lt_succ_self _)) (by
          intro p hp
          exact hcharge J (Nat.lt_succ_self _) p hp)
    have hprev := ih (fun j hj => hparent j (Nat.lt_succ_of_lt hj))
      (fun j hj => hcharge j (Nat.lt_succ_of_lt hj))
    calc
      _ ≤ F J*(∑ i ∈ I J, w J i) := hs
      _ ≤ F J*((∏ j ∈ Finset.range J, F j)*(∑ i ∈ I 0, w 0 i)) := mul_le_mul' le_rfl hprev
      _ = _ := by rw [Finset.prod_range_succ]; ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_RadialCapCollision
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A hit child lies in a slightly enlarged radial collision ball -/

namespace Falconer
open NormedSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem radial_cap_child_distance (x z q y u : E) {r D s : ℝ}
    (hs : 0 < s) (hyx : s ≤ ‖y-x‖) (hzx : z ≠ x)
    (hzcap : ‖normalize (z-x)-u‖ ≤ r) (hqcap : ‖normalize (q-x)-u‖ ≤ r)
    (hyz : ‖y-z‖ ≤ D) :
    dist (normalize (y-x)) (normalize (q-x)) ≤ 2*D/s+2*r := by
  have hnear : dist (normalize (y-x)) (normalize (z-x)) ≤ 2*D/s := by
    apply (le_div_iff₀ hs).mpr
    have hh := normalize_distance_scaled hyx (sub_ne_zero.mpr hzx)
    simp only [dist_eq_norm,sub_sub_sub_cancel_right] at hh ⊢
    nlinarith
  have hcap : dist (normalize (z-x)) (normalize (q-x)) ≤ 2*r := by
    rw [dist_eq_norm]
    have hh := norm_sub_le_norm_sub_add_norm_sub (normalize (z-x)) u (normalize (q-x))
    rw [norm_sub_rev u] at hh
    linarith
  exact (dist_triangle _ _ _).trans (add_le_add hnear hcap)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Measures_CollisionDensityCharge
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Original fiber densities multiply local radial collision tests -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal
variable {d : ℕ} {ι : Type*}

theorem collision_density_children_charge (μ : Measure (Space d))
    (G : Set (Space d × Space d)) (hG : MeasurableSet G)
    (Q : ℕ → ι → Set (Space d)) (I : ℕ → Finset ι) (J j : ℕ) (hj : j ≤ J)
    (C : Finset ι) (hCI : C ⊆ I j) (P : Set (Space d)) (x u : Space d)
    {r D s : ℝ} {θ F : ℝ≥0∞} (hs : 0 < s) (hθ : 0 < θ) (hθtop : θ ≠ ∞)
    (hQ : ∀ i ∈ C, MeasurableSet (Q j i)) (hdisj : (C : Set ι).PairwiseDisjoint (Q j))
    (hparent : ∀ i ∈ C, Q j i ⊆ P)
    (hdiam : ∀ i ∈ C, ∀ y ∈ Q j i, ∀ z ∈ Q j i, ‖y-z‖ ≤ D)
    (hsep : ∀ i ∈ C, ∀ y ∈ Q j i, s ≤ ‖y-x‖)
    (hhit : ∀ i ∈ C, ∃ z ∈ Q j i,
      (x,z) ∈ G \ multiscaleFiberBad μ G Q I θ J ∧ ‖normalize (z-x)-u‖ ≤ r)
    (htest : ∀ q ∈ P, (x,q) ∈ G \ multiscaleFiberBad μ G Q I θ J →
      ‖normalize (q-x)-u‖ ≤ r →
      μ (P ∩ {y | dist (normalize (y-x)) (normalize (q-x)) ≤ 2*D/s+2*r}) ≤ F*μ P) :
    (∑ i ∈ C, μ (Q j i)) ≤ (θ⁻¹*F)*μ P := by
  classical
  by_cases hC : C.Nonempty
  · obtain ⟨i,hi⟩ := hC
    obtain ⟨q,hqQ,hq,hqcap⟩ := hhit i hi
    let T : Set (Space d) := {y | dist (normalize (y-x)) (normalize (q-x)) ≤ 2*D/s+2*r}
    apply density_hit_children_charge μ (Prod.mk x ⁻¹' G) P T
      (hG.preimage (by fun_prop)) (Q j) C hQ hdisj hθ hθtop
    · intro i hi
      obtain ⟨z,hzQ,hz,_⟩ := hhit i hi
      exact multiscaleFiber_retained μ G Q I θ J hz hj (hCI hi) hzQ
    · intro i hi y hy
      obtain ⟨z,hzQ,_hz,hzcap⟩ := hhit i hi
      have hzx : z ≠ x := by
        intro he
        have hh := hsep i hi z hzQ
        rw [he,sub_self,norm_zero] at hh
        linarith
      exact ⟨hparent i hi hy.1,radial_cap_child_distance x z q y u hs
        (hsep i hi y hy.1) hzx hzcap hqcap (hdiam i hi y hy.1 z hzQ)⟩
    · exact htest q (hparent i hi hqQ) hq hqcap
  · have he : C = ∅ := Finset.not_nonempty_iff_eq_empty.mp hC
    simp only [he,Finset.sum_empty,zero_le]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Measures_MultiscaleCollisionMass
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Multiplying full conditional radial collision bounds over a source tree -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal BigOperators
variable {d : ℕ} {ι : Type*} [DecidableEq ι]

theorem multiscale_collision_cap_mass (μ : Measure (Space d))
    (G : Set (Space d × Space d)) (hG : MeasurableSet G)
    (Q : ℕ → ι → Set (Space d)) (I : ℕ → Finset ι) (parent : ℕ → ι → ι)
    (J : ℕ) (x u : Space d) (r s : ℝ) (D : ℕ → ℝ) (θ : ℝ≥0∞) (F : ℕ → ℝ≥0∞)
    (hs : 0 < s) (hθ : 0 < θ) (hθtop : θ ≠ ∞)
    (hQ : ∀ j ≤ J, ∀ i ∈ I j, MeasurableSet (Q j i))
    (hdisj : ∀ j ≤ J, (I j : Set ι).PairwiseDisjoint (Q j))
    (hparent : ∀ j < J, ∀ i ∈ I (j+1),
      parent j i ∈ I j ∧ Q (j+1) i ⊆ Q j (parent j i))
    (hdiam : ∀ j < J, ∀ i ∈ I (j+1), ∀ y ∈ Q (j+1) i, ∀ z ∈ Q (j+1) i, ‖y-z‖ ≤ D j)
    (hsep : ∀ j < J, ∀ i ∈ I (j+1), ∀ y ∈ Q (j+1) i, s ≤ ‖y-x‖)
    (hlocal : ∀ j < J, ∀ p ∈ I j, ∀ q ∈ Q j p, (x,q) ∈ G →
      μ (Q j p ∩ {y | dist (normalize (y-x)) (normalize (q-x)) ≤ 2*D j/s+2*r}) ≤
        F j*μ (Q j p))
    (hcover : ∀ z ∈ retainedRadialCap μ G Q I θ J x u r, ∃ i ∈ I J, z ∈ Q J i) :
    μ (retainedRadialCap μ G Q I θ J x u r) ≤
      (∏ j ∈ Finset.range J, θ⁻¹*F j)*μ univ := by
  classical
  let H := radialCapHitCells μ G Q I θ J x u r
  have hHI (j : ℕ) : H j ⊆ I j := Finset.filter_subset _ _
  have hmem {j : ℕ} {i : ι} (hi : i ∈ H j) :
      ∃ z ∈ Q j i, z ∈ retainedRadialCap μ G Q I θ J x u r := (Finset.mem_filter.mp hi).2
  have hparents : ∀ j < J, ∀ i ∈ H (j+1), parent j i ∈ H j := by
    intro j hj i hi
    obtain ⟨z,hz,hcap⟩ := hmem hi
    obtain ⟨hp,hsub⟩ := hparent j hj i (hHI _ hi)
    exact Finset.mem_filter.mpr ⟨hp,z,hsub hz,hcap⟩
  have hcharge : ∀ j < J, ∀ p ∈ H j,
      (∑ i ∈ H (j+1) with parent j i = p, μ (Q (j+1) i)) ≤
        (θ⁻¹*F j)*μ (Q j p) := by
    intro j hj p hp
    let C := (H (j+1)).filter (fun i => parent j i = p)
    have hCI : C ⊆ I (j+1) := fun i hi => hHI _ (Finset.mem_filter.mp hi).1
    have hCQ : ∀ i ∈ C, Q (j+1) i ⊆ Q j p := by
      intro i hi
      have hs := (hparent j hj i (hCI hi)).2
      rwa [(Finset.mem_filter.mp hi).2] at hs
    have hCdisj : (C : Set ι).PairwiseDisjoint (Q (j+1)) := by
      intro i hi k hk hne
      exact hdisj (j+1) (by omega) (hCI hi) (hCI hk) hne
    have hh := collision_density_children_charge μ G hG Q I J (j+1) (by omega)
      C hCI (Q j p) x u hs hθ hθtop
      (fun i hi => hQ (j+1) (by omega) i (hCI hi)) hCdisj hCQ
      (fun i hi => hdiam j hj i (hCI hi))
      (fun i hi => hsep j hj i (hCI hi))
      (fun i hi => by
        obtain ⟨z,hz,hcap⟩ := hmem (Finset.mem_filter.mp hi).1
        exact ⟨z,hz,hcap.1,hcap.2⟩)
      (fun q hqp hq _ => hlocal j hj p (hHI _ hp) q hqp hq.1)
    exact hh
  have hmul := finite_mass_multiplication H parent (fun j i => μ (Q j i))
    (fun j => θ⁻¹*F j) J hparents hcharge
  have hsub : retainedRadialCap μ G Q I θ J x u r ⊆ ⋃ i ∈ H J, Q J i := by
    intro z hz
    obtain ⟨i,hi,hzi⟩ := hcover z hz
    exact mem_iUnion.mpr ⟨i,mem_iUnion.mpr ⟨Finset.mem_filter.mpr ⟨hi,z,hzi,hz⟩,hzi⟩⟩
  have hzero : (∑ i ∈ H 0, μ (Q 0 i)) ≤ μ univ := by
    rw [← measure_biUnion_finset (fun i hi k hk hik =>
      hdisj 0 (Nat.zero_le _) (hHI _ hi) (hHI _ hk) hik)
      (fun i hi => hQ 0 (Nat.zero_le _) i (hHI _ hi))]
    exact measure_mono (subset_univ _)
  calc
    _ ≤ μ (⋃ i ∈ H J, Q J i) := measure_mono hsub
    _ ≤ ∑ i ∈ H J, μ (Q J i) := measure_biUnion_finset_le _ _
    _ ≤ (∏ j ∈ Finset.range J, θ⁻¹*F j)*(∑ i ∈ H 0, μ (Q 0 i)) := hmul
    _ ≤ _ := mul_le_mul' le_rfl hzero

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Measures_CollisionPruningMultiplication
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Multiplying conditional-source radial estimates at retained original witnesses -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal BigOperators
variable {d : ℕ} {ι : Type*} [DecidableEq ι]

theorem conditional_radial_collision_test (μ : Measure (Space d)) [IsFiniteMeasure μ]
    (P : Set (Space d)) (hP : MeasurableSet P) (x z : Space d) (r : ℝ) (F : ℝ≥0∞)
    (h : radialCollisionMass (ProbabilityTheory.cond μ P) r (z,x) ≤ F) :
    μ (P ∩ {y | dist (normalize (y-x)) (normalize (z-x)) ≤ r}) ≤ F*μ P := by
  rw [← ProbabilityTheory.cond_mul_eq_inter hP _ μ]
  exact mul_le_mul' h le_rfl

theorem radial_collision_pruning_multiplication (μ ν : Measure (Space d))
    [IsFiniteMeasure μ] [SFinite ν]
    (G : Set (Space d × Space d)) (hG : MeasurableSet G)
    (Q : ℕ → ι → Set (Space d)) (I : ℕ → Finset ι) (parent : ℕ → ι → ι)
    (J : ℕ) (D W : ℕ → ℝ) (r s : ℝ) (θ : ℝ≥0∞) (F : ℕ → ℝ≥0∞)
    (hs : 0 < s) (hθ : 0 < θ) (hθtop : θ ≠ ∞)
    (hQ : ∀ j ≤ J, ∀ i ∈ I j, MeasurableSet (Q j i))
    (hdisj : ∀ j ≤ J, (I j : Set ι).PairwiseDisjoint (Q j))
    (hparent : ∀ j < J, ∀ i ∈ I (j+1),
      parent j i ∈ I j ∧ Q (j+1) i ⊆ Q j (parent j i))
    (hdiam : ∀ j < J, ∀ i ∈ I (j+1), ∀ y ∈ Q (j+1) i, ∀ z ∈ Q (j+1) i, ‖y-z‖ ≤ D j)
    (hsep : ∀ x, (∃ z, (x,z) ∈ G) → ∀ j < J, ∀ i ∈ I (j+1),
      ∀ y ∈ Q (j+1) i, s ≤ ‖y-x‖)
    (hwidth : ∀ j < J, 2*D j/s+2*r ≤ W j)
    (hlocal : ∀ j < J, ∀ p ∈ I j, ∀ x z, (x,z) ∈ G → z ∈ Q j p →
      radialCollisionMass (ProbabilityTheory.cond μ (Q j p)) (W j) (z,x) ≤ F j)
    (hcover : ∀ x z, (x,z) ∈ G → ∃ i ∈ I J, z ∈ Q J i) :
    ∃ G' : Set (Space d × Space d), MeasurableSet G' ∧ G' ⊆ G ∧
      (ν.prod μ) (G \ G') ≤ (J+1:ℝ≥0∞)*(θ*μ univ)*ν univ ∧
      ∀ x u : Space d,
        μ {z | (x,z) ∈ G' ∧ ‖normalize (z-x)-u‖ ≤ r} ≤
          (∏ j ∈ Finset.range J, θ⁻¹*F j)*μ univ := by
  let Bad := multiscaleFiberBad μ G Q I θ J
  have hBad : MeasurableSet Bad := multiscaleFiberBad_measurable μ G hG Q I θ J hQ
  let G' := G \ Bad
  have hG' : MeasurableSet G' := hG.diff hBad
  refine ⟨G',hG',sdiff_subset,?_,?_⟩
  · apply (measure_mono _).trans (multiscaleFiberBad_mass ν μ G hG Q I J hQ hdisj θ)
    intro p hp
    by_contra hb
    exact hp.2 ⟨hp.1,hb⟩
  · intro x u
    by_cases hx : ∃ z, (x,z) ∈ G
    · apply multiscale_collision_cap_mass μ G hG Q I parent J x u r s D θ F hs hθ hθtop
        hQ hdisj hparent hdiam (hsep x hx)
      · intro j hj p hp z hz hzg
        apply (measure_mono _).trans
          (conditional_radial_collision_test μ (Q j p) (hQ j hj.le p hp) x z (W j) (F j)
            (hlocal j hj p hp x z hzg hz))
        rintro y ⟨hy,hclose⟩
        exact ⟨hy,hclose.trans (hwidth j hj)⟩
      · intro z hz
        exact hcover x z hz.1.1
    · have he : {z | (x,z) ∈ G' ∧ ‖normalize (z-x)-u‖ ≤ r} = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro z hz
        exact hx ⟨z,hz.1.1⟩
      rw [he,measure_empty]
      exact zero_le

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_SourceCollisionMultiplication
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The radial multiplication theorem in source-first original-pair coordinates -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal BigOperators
variable {d : ℕ} {ι : Type*} [DecidableEq ι]

theorem source_collision_pruning_multiplication (μ ν : Measure (Space d))
    [IsFiniteMeasure μ] [SFinite ν]
    (G : Set (Space d × Space d)) (hG : MeasurableSet G)
    (Q : ℕ → ι → Set (Space d)) (I : ℕ → Finset ι) (parent : ℕ → ι → ι)
    (J : ℕ) (D W : ℕ → ℝ) (r s : ℝ) (θ : ℝ≥0∞) (F : ℕ → ℝ≥0∞)
    (hs : 0 < s) (hθ : 0 < θ) (hθtop : θ ≠ ∞)
    (hQ : ∀ j ≤ J, ∀ i ∈ I j, MeasurableSet (Q j i))
    (hdisj : ∀ j ≤ J, (I j : Set ι).PairwiseDisjoint (Q j))
    (hparent : ∀ j < J, ∀ i ∈ I (j+1),
      parent j i ∈ I j ∧ Q (j+1) i ⊆ Q j (parent j i))
    (hdiam : ∀ j < J, ∀ i ∈ I (j+1), ∀ y ∈ Q (j+1) i, ∀ z ∈ Q (j+1) i, ‖y-z‖ ≤ D j)
    (hsep : ∀ x, (∃ z, (z,x) ∈ G) → ∀ j < J, ∀ i ∈ I (j+1),
      ∀ y ∈ Q (j+1) i, s ≤ ‖y-x‖)
    (hwidth : ∀ j < J, 2*D j/s+2*r ≤ W j)
    (hlocal : ∀ j < J, ∀ p ∈ I j, ∀ z x, (z,x) ∈ G → z ∈ Q j p →
      radialCollisionMass (ProbabilityTheory.cond μ (Q j p)) (W j) (z,x) ≤ F j)
    (hcover : ∀ z x, (z,x) ∈ G → ∃ i ∈ I J, z ∈ Q J i) :
    ∃ G' : Set (Space d × Space d), MeasurableSet G' ∧ G' ⊆ G ∧
      (μ.prod ν) (G \ G') ≤ (J+1:ℝ≥0∞)*(θ*μ univ)*ν univ ∧
      ∀ x u : Space d,
        μ {z | (z,x) ∈ G' ∧ ‖normalize (z-x)-u‖ ≤ r} ≤
          (∏ j ∈ Finset.range J, θ⁻¹*F j)*μ univ := by
  let Gs := Prod.swap ⁻¹' G
  have hGs : MeasurableSet Gs := hG.preimage measurable_swap
  obtain ⟨H,hH,hHG,hdel,hcap⟩ := radial_collision_pruning_multiplication μ ν Gs hGs
    Q I parent J D W r s θ F hs hθ hθtop hQ hdisj hparent hdiam hsep hwidth
    (fun j hj p hp x z hx hz => hlocal j hj p hp z x hx hz) (fun x z hx => hcover z x hx)
  refine ⟨Prod.swap ⁻¹' H,hH.preimage measurable_swap,fun p hp => hHG hp,?_,?_⟩
  · have he : G \ Prod.swap ⁻¹' H = Prod.swap ⁻¹' (Gs \ H) := by
      ext p
      simp only [mem_sdiff,mem_preimage,Gs,Prod.swap_swap]
    rw [he,← Measure.map_apply measurable_swap (hGs.diff hH),Measure.prod_swap]
    exact hdel
  · exact hcap

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Measures_LocalPruningGain
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Original cellwise deletions followed by radial density multiplication -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal BigOperators
variable {d : ℕ} {ι : Type*} [DecidableEq ι]

theorem radial_gain_of_local_prunings (μ ν : Measure (Space d))
    [IsFiniteMeasure μ] [SFinite ν]
    (G : Set (Space d × Space d)) (hG : MeasurableSet G)
    (Q : ℕ → ι → Set (Space d)) (I : ℕ → Finset ι) (parent : ℕ → ι → ι)
    (J : ℕ) (D W : ℕ → ℝ) (r s : ℝ) (θ : ℝ≥0∞) (F cost : ℕ → ℝ≥0∞)
    (hs : 0 < s) (hθ : 0 < θ) (hθtop : θ ≠ ∞)
    (hQ : ∀ j ≤ J, ∀ i ∈ I j, MeasurableSet (Q j i))
    (hpos : ∀ j < J, ∀ i ∈ I j, μ (Q j i) ≠ 0)
    (hdisj : ∀ j ≤ J, (I j : Set ι).PairwiseDisjoint (Q j))
    (hparent : ∀ j < J, ∀ i ∈ I (j+1),
      parent j i ∈ I j ∧ Q (j+1) i ⊆ Q j (parent j i))
    (hdiam : ∀ j < J, ∀ i ∈ I (j+1), ∀ y ∈ Q (j+1) i, ∀ z ∈ Q (j+1) i, ‖y-z‖ ≤ D j)
    (hsep : ∀ x, (∃ z, (z,x) ∈ G) → ∀ j < J, ∀ i ∈ I (j+1),
      ∀ y ∈ Q (j+1) i, s ≤ ‖y-x‖)
    (hwidth : ∀ j < J, 2*D j/s+2*r ≤ W j)
    (hlocal : ∀ j < J, ∀ i ∈ I j, ∃ H : Set (Space d × Space d), MeasurableSet H ∧
      ((ProbabilityTheory.cond μ (Q j i)).prod ν) ((G ∩ (Q j i ×ˢ univ)) \ H) ≤ cost j ∧
      ∀ p ∈ H, radialCollisionMass (ProbabilityTheory.cond μ (Q j i)) (W j) p ≤ F j)
    (hcover : ∀ z x, (z,x) ∈ G → ∃ i ∈ I J, z ∈ Q J i) :
    ∃ G' : Set (Space d × Space d), MeasurableSet G' ∧ G' ⊆ G ∧
      (μ.prod ν) (G \ G') ≤ (∑ j ∈ Finset.range J, cost j*μ univ)+
        (J+1:ℝ≥0∞)*(θ*μ univ)*ν univ ∧
      ∀ x u : Space d,
        μ {z | (z,x) ∈ G' ∧ ‖normalize (z-x)-u‖ ≤ r} ≤
          (∏ j ∈ Finset.range J, θ⁻¹*F j)*μ univ := by
  obtain ⟨H,hH,hHG,hdel,hbound⟩ := finite_cellwise_collision_pruning μ ν J I Q
    (fun j hj => hQ j hj.le) hpos (fun j hj => hdisj j hj.le) G hG W
    (fun j _ => F j) cost hlocal
  obtain ⟨G',hG',hsub,hdel',hcap⟩ := source_collision_pruning_multiplication μ ν H hH
    Q I parent J D W r s θ F hs hθ hθtop hQ hdisj hparent hdiam
    (fun x hx => hsep x (by obtain ⟨z,hz⟩ := hx; exact ⟨z,hHG hz⟩)) hwidth
    (fun j hj i hi z x hz hzi => hbound j hj i hi (z,x) hz hzi)
    (fun z x hz => hcover z x (hHG hz))
  refine ⟨G',hG',hsub.trans hHG,?_,hcap⟩
  have hdiff : G \ G' ⊆ (G \ H) ∪ (H \ G') := by
    intro p hp
    by_cases hpH : p ∈ H
    · exact Or.inr ⟨hpH,hp.2⟩
    · exact Or.inl ⟨hp.1,hpH⟩
  exact (measure_mono hdiff).trans ((measure_union_le _ _).trans (add_le_add hdel hdel'))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_DyadicLocalGain
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Applying local radial collision prunings on the actual occupied dyadic tree -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal BigOperators
variable {d : ℕ}
attribute [local instance] Classical.propDecidable

theorem dyadic_gain_of_local_prunings (μ ν : Measure (Space d))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (Q : DyadicCube d) (hQ : 0 < Q.side) (N J : ℕ) (depth : ℕ → ℕ)
    (hdepth : ∀ j ≤ J, depth j ≤ N) (hmono : ∀ j < J, depth j ≤ depth (j+1))
    (A P : Set (Space d)) (hA : μ Aᶜ = 0) {s : ℝ} (hs : 0 < s)
    (hsep : ∀ z ∈ A, ∀ x ∈ P, s ≤ ‖z-x‖)
    (G : Set (Space d × Space d)) (hG : MeasurableSet G)
    (hGcore : G ⊆ Q.occupiedTreeCore μ N ×ˢ P)
    (r : ℝ) (W : ℕ → ℝ) (θ : ℝ≥0∞) (F cost : ℕ → ℝ≥0∞)
    (hθ : 0 < θ) (hθtop : θ ≠ ∞)
    (hsmall : ∀ j < J, Real.sqrt d*(Q.side/(2:ℝ)^depth (j+1)) ≤ s/2)
    (hwidth : ∀ j < J, 2*(Real.sqrt d*(Q.side/(2:ℝ)^depth (j+1)))/(s/2)+2*r ≤ W j)
    (hlocal : ∀ j < J, ∀ p ∈ Q.occupiedPaths μ (depth j),
      ∃ H : Set (Space d × Space d), MeasurableSet H ∧
      ((ProbabilityTheory.cond μ (Q.descendant p).carrier).prod ν)
        ((G ∩ ((Q.descendant p).carrier ×ˢ univ)) \ H) ≤ cost j ∧
      ∀ z ∈ H, radialCollisionMass (ProbabilityTheory.cond μ (Q.descendant p).carrier)
        (W j) z ≤ F j) :
    ∃ G' : Set (Space d × Space d), MeasurableSet G' ∧ G' ⊆ G ∧
      (μ.prod ν) (G \ G') ≤ (∑ j ∈ Finset.range J, cost j)+(J+1:ℝ≥0∞)*θ ∧
      ∀ x u : Space d, μ {z | (z,x) ∈ G' ∧ ‖normalize (z-x)-u‖ ≤ r} ≤
        ∏ j ∈ Finset.range J, θ⁻¹*F j := by
  have hpos : ∀ j < J, ∀ p ∈ Q.occupiedPaths μ (depth j),
      μ (Q.descendant p).carrier ≠ 0 := fun _ _ _ hp => (Finset.mem_filter.mp hp).2.ne'
  have hdisj : ∀ j ≤ J, (Q.occupiedPaths μ (depth j) : Set (List (Fin d → Bool))).PairwiseDisjoint
      (fun p => (Q.descendant p).carrier) := by
    intro j _ p hp q hq hpq
    exact Q.descendants_disjoint
      (((mem_cubePaths d (depth j) p).mp (Finset.mem_filter.mp hp).1).trans
        ((mem_cubePaths d (depth j) q).mp (Finset.mem_filter.mp hq).1).symm) hpq
  obtain ⟨G',hG',hsub,hdel,hbound⟩ := radial_gain_of_local_prunings μ ν G hG
    (fun _ p => (Q.descendant p).carrier) (fun j => Q.occupiedPaths μ (depth j))
    (fun j p => p.take (depth j)) J
    (fun j => Real.sqrt d*(Q.side/(2:ℝ)^depth (j+1))) W r (s/2) θ F cost
    (by positivity) hθ hθtop (fun _ _ p _ => (Q.descendant p).measurable) hpos hdisj
    (fun j hj _ hp => Q.occupied_parent hQ μ (hmono j hj) hp)
    (fun _ _ _ hp _ hy _ hz => Q.occupied_diameter_bound hQ μ hp hy hz)
    (fun x hx j hj p hp y hy => occupied_cell_separation Q hQ μ A P hA hsep
      (hsmall j hj) hp x (by obtain ⟨z,hz⟩ := hx; exact (hGcore hz).2) y hy)
    hwidth hlocal
    (fun z x hz => Q.occupiedTreeCore_cover μ (hdepth J le_rfl) (hGcore hz).1)
  refine ⟨G',hG',hsub,?_,?_⟩
  · simpa only [measure_univ,mul_one] using hdel
  · intro x u
    simpa only [measure_univ,mul_one] using hbound x u

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_OneScaleParameters
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Choosing the comparison loss before the compactness contact margin -/

namespace Falconer

theorem one_scale_loss_choice (d : ℕ) {ε gain : ℝ} (hε : 0 < ε) (hgain : 0 < gain) :
    ∃ τ : ℝ, 0 < τ ∧ (2*(d:ℝ)+4)*τ ≤ ε/2 ∧
      (20*(2*(d:ℝ)+4)+4)*τ ≤ gain/8 ∧ 2*τ ≤ gain := by
  let L : ℝ := 2*(d:ℝ)+4
  have hL : 0 < L := by dsimp [L]; positivity
  have hS : 0 < 20*L+4 := by positivity
  let τ := min (min (ε/(2*L)) (gain/(8*(20*L+4)))) (gain/2)
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have hτε : τ ≤ ε/(2*L) := (min_le_left _ _).trans (min_le_left _ _)
  have hτgain : τ ≤ gain/(8*(20*L+4)) := (min_le_left _ _).trans (min_le_right _ _)
  refine ⟨τ,hτ,?_,?_,?_⟩
  · change L*τ ≤ ε/2
    calc
      _ ≤ L*(ε/(2*L)) := mul_le_mul_of_nonneg_left hτε hL.le
      _ = _ := by field_simp
  · change (20*L+4)*τ ≤ gain/8
    calc
      _ ≤ (20*L+4)*(gain/(8*(20*L+4))) := mul_le_mul_of_nonneg_left hτgain hS.le
      _ = _ := by field_simp
  · have hh : τ ≤ gain/2 := min_le_right _ _
    linarith

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_RelativeClasswiseRadialGain
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Recombining relative pair refinements with the original source-class weights -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal BigOperators
variable {d : ℕ} {ι : Type*}

theorem relative_classwise_radial_gain (μ ν : Measure (Space d))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (G₀ : Set (Space d × Space d)) (hG₀ : MeasurableSet G₀)
    (I : Finset ι) (S : ι → Set (Space d)) (G : ι → Set (Space d × Space d))
    (hS : ∀ i ∈ I, MeasurableSet (S i)) (hG : ∀ i ∈ I, MeasurableSet (G i))
    (hpos : ∀ i ∈ I, μ (S i) ≠ 0) (hdisj : (I : Set ι).PairwiseDisjoint S)
    (t C : ℝ≥0∞) (r : ℝ)
    (hcost : ∀ i ∈ I, (ν.prod (ProbabilityTheory.cond μ (S i))) (G₀ \ G i) ≤ t)
    (hcap : ∀ i ∈ I, ∀ x u : Space d,
      ProbabilityTheory.cond μ (S i) {z | (x,z) ∈ G i ∧ ‖normalize (z-x)-u‖ ≤ r} ≤ C) :
    ∃ H : Set (Space d × Space d), MeasurableSet H ∧ H ⊆ G₀ ∧
      (ν.prod μ) (G₀ \ H) ≤ μ (⋃ i ∈ I, S i)ᶜ+t ∧
      ∀ x u : Space d, μ {z | (x,z) ∈ H ∧ ‖normalize (z-x)-u‖ ≤ r} ≤ C := by
  classical
  let U := ⋃ i ∈ I, G i ∩ (univ ×ˢ S i)
  let H := G₀ ∩ U
  have hH : MeasurableSet H := hG₀.inter (Finset.measurableSet_biUnion I
    (fun i hi => (hG i hi).inter (MeasurableSet.univ.prod (hS i hi))))
  have hmass : (∑ i ∈ I, μ (S i)) ≤ 1 := by
    rw [← measure_biUnion_finset hdisj hS]
    exact (measure_mono (subset_univ _)).trans_eq (measure_univ)
  have hreconstruct (i : ι) (hi : i ∈ I) (E : Set (Space d × Space d)) :
      μ (S i)*((ν.prod (ProbabilityTheory.cond μ (S i))) E) =
        (ν.prod (μ.restrict (S i))) E := by
    rw [ProbabilityTheory.cond,Measure.prod_smul_right,Measure.smul_apply,smul_eq_mul,
      ← mul_assoc,ENNReal.mul_inv_cancel (hpos i hi) (measure_ne_top μ _),one_mul]
  refine ⟨H,hH,inter_subset_left,?_,?_⟩
  · have hsub : G₀ \ H ⊆ (univ ×ˢ (⋃ i ∈ I, S i)ᶜ) ∪
        ⋃ i ∈ I, (G₀ \ G i) ∩ (univ ×ˢ S i) := by
      intro p hp
      by_cases hs : p.2 ∈ ⋃ i ∈ I, S i
      · obtain ⟨i,hi,hsi⟩ := mem_iUnion₂.mp hs
        right
        refine mem_iUnion₂.mpr ⟨i,hi,⟨hp.1,?_⟩,mem_univ _,hsi⟩
        intro hgi
        exact hp.2 ⟨hp.1,mem_iUnion₂.mpr ⟨i,hi,hgi,mem_univ _,hsi⟩⟩
      · exact Or.inl ⟨mem_univ _,hs⟩
    calc
      _ ≤ (ν.prod μ) (univ ×ˢ (⋃ i ∈ I, S i)ᶜ)+
          (ν.prod μ) (⋃ i ∈ I, (G₀ \ G i) ∩ (univ ×ˢ S i)) :=
        (measure_mono hsub).trans (measure_union_le _ _)
      _ ≤ μ (⋃ i ∈ I, S i)ᶜ+
          ∑ i ∈ I, (ν.prod μ) ((G₀ \ G i) ∩ (univ ×ˢ S i)) := by
        simp only [Measure.prod_prod,measure_univ,one_mul]
        exact add_le_add le_rfl (measure_biUnion_finset_le _ _)
      _ ≤ μ (⋃ i ∈ I, S i)ᶜ+∑ i ∈ I, μ (S i)*t := by
        apply add_le_add le_rfl (Finset.sum_le_sum ?_)
        intro i hi
        rw [← Measure.restrict_apply (hG₀.diff (hG i hi)),← Measure.prod_restrict,
          Measure.restrict_univ,← hreconstruct i hi]
        exact mul_le_mul' le_rfl (hcost i hi)
      _ = μ (⋃ i ∈ I, S i)ᶜ+(∑ i ∈ I, μ (S i))*t := by rw [Finset.sum_mul]
      _ ≤ _ := add_le_add le_rfl ((mul_le_mul' hmass le_rfl).trans_eq (one_mul t))
  · intro x u
    let A := fun i => {z | (x,z) ∈ G i ∧ ‖normalize (z-x)-u‖ ≤ r}
    have hsub : {z | (x,z) ∈ H ∧ ‖normalize (z-x)-u‖ ≤ r} ⊆ ⋃ i ∈ I, S i ∩ A i := by
      intro z hz
      obtain ⟨i,hi,hgi,hsi⟩ := mem_iUnion₂.mp hz.1.2
      exact mem_iUnion₂.mpr ⟨i,hi,hsi.2,hgi,hz.2⟩
    calc
      _ ≤ ∑ i ∈ I, μ (S i ∩ A i) :=
        (measure_mono hsub).trans (measure_biUnion_finset_le _ _)
      _ = ∑ i ∈ I, μ (S i)*ProbabilityTheory.cond μ (S i) (A i) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [← ProbabilityTheory.cond_mul_eq_inter (hS i hi) (A i) μ,mul_comm]
      _ ≤ ∑ i ∈ I, μ (S i)*C := Finset.sum_le_sum (fun i hi =>
        mul_le_mul' le_rfl (hcap i hi x u))
      _ = (∑ i ∈ I, μ (S i))*C := (Finset.sum_mul _ _ _).symm
      _ ≤ C := (mul_le_mul' hmass le_rfl).trans_eq (one_mul C)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_RelativeRegularizationGain
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Recombining a relative radial refinement of each actual regularization class -/

namespace Falconer.Regularization
open Set MeasureTheory NormedSpace
open scoped ENNReal
variable {d : ℕ}

theorem relative_regularization_radial_gain (Q : DyadicCube d) (hQ : 0 < Q.side)
    (μ ν : Measure (Space d)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (G₀ : Set (Space d × Space d)) (hG₀ : MeasurableSet G₀)
    (hroot : μ Q.carrierᶜ = 0) {N H : ℕ} (hH : 0 < H) (hNH : H ≤ N) (hdN : d+3 ≤ N)
    {threshold : ℝ≥0∞} (hthreshold : 0 < threshold) (t C : ℝ≥0∞) (r : ℝ)
    (hlocal : ∀ T ∈ regularizationIndex Q μ N (N/H) threshold,
      ∃ G : Set (Space d × Space d), MeasurableSet G ∧
        (ν.prod (normalizedClass Q μ (regularizationLeaves Q μ N)
          (regularizationLabel Q μ N (N/H)) T)) (G₀ \ G) ≤ t ∧
        ∀ x u : Space d,
          normalizedClass Q μ (regularizationLeaves Q μ N)
            (regularizationLabel Q μ N (N/H)) T
            {z | (x,z) ∈ G ∧ ‖normalize (z-x)-u‖ ≤ r} ≤ C) :
    ∃ G : Set (Space d × Space d), MeasurableSet G ∧ G ⊆ G₀ ∧
      (ν.prod μ) (G₀ \ G) ≤ ((2:ℝ≥0∞)^(2*N))⁻¹+(N^(4*H+2):ℕ)*threshold+t ∧
      ∀ x u : Space d, μ {z | (x,z) ∈ G ∧ ‖normalize (z-x)-u‖ ≤ r} ≤ C := by
  classical
  let I := regularizationIndex Q μ N (N/H) threshold
  let S := regularizationSet Q μ N (N/H)
  have hex : ∀ T : List ℕ, ∃ G : Set (Space d × Space d), MeasurableSet G ∧
      (T ∈ I → (ν.prod (ProbabilityTheory.cond μ (S T))) (G₀ \ G) ≤ t ∧
        ∀ x u : Space d, ProbabilityTheory.cond μ (S T)
          {z | (x,z) ∈ G ∧ ‖normalize (z-x)-u‖ ≤ r} ≤ C) := by
    intro T
    by_cases hT : T ∈ I
    · obtain ⟨G,hm,hc,hg⟩ := hlocal T hT
      rw [normalized_regularization_class_eq_cond] at hc hg
      exact ⟨G,hm,fun _ => ⟨hc,hg⟩⟩
    · exact ⟨∅,MeasurableSet.empty,fun h => (hT h).elim⟩
  choose G hm hg using hex
  have hpos : ∀ T ∈ I, μ (S T) ≠ 0 := by
    intro T hT
    exact (hthreshold.trans_le (regularizationSet_mass Q μ N (N/H) threshold hT)).ne'
  have hdisj : (I : Set (List ℕ)).PairwiseDisjoint S := by
    intro T _ U _ hTU
    exact regularizationSet_disjoint Q hQ μ N (N/H) hTU
  obtain ⟨G',hG',hsub,hc,hcap⟩ := relative_classwise_radial_gain μ ν G₀ hG₀ I S G
    (fun T _ => regularizationSet_measurable Q μ N (N/H) T) (fun T _ => hm T)
    hpos hdisj t C r (fun T hT => (hg T hT).1) (fun T hT => (hg T hT).2)
  refine ⟨G',hG',hsub,hc.trans (add_le_add ?_ le_rfl),hcap⟩
  exact regularization_discarded_global Q hQ μ hroot hH hNH hdN threshold

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_SourceRelativeRegularization
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Relative recombination in source-first coordinates -/

namespace Falconer.Regularization
open Set MeasureTheory NormedSpace
open scoped ENNReal
variable {d : ℕ}

theorem source_relative_regularization_gain (Q : DyadicCube d) (hQ : 0 < Q.side)
    (μ ν : Measure (Space d)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (G₀ : Set (Space d × Space d)) (hG₀ : MeasurableSet G₀)
    (hroot : μ Q.carrierᶜ = 0) {N H : ℕ} (hH : 0 < H) (hNH : H ≤ N) (hdN : d+3 ≤ N)
    {threshold : ℝ≥0∞} (hthreshold : 0 < threshold) (t C : ℝ≥0∞) (r : ℝ)
    (hlocal : ∀ p ∈ regularizationLeaves Q μ N,
      regularizationLabel Q μ N (N/H) p ∈ regularizationIndex Q μ N (N/H) threshold →
      ∃ G : Set (Space d × Space d), MeasurableSet G ∧
        ((sourceClass Q μ N (N/H) p).prod ν) (G₀ \ G) ≤ t ∧
        ∀ x u : Space d, sourceClass Q μ N (N/H) p
          {z | (z,x) ∈ G ∧ ‖normalize (z-x)-u‖ ≤ r} ≤ C) :
    ∃ G : Set (Space d × Space d), MeasurableSet G ∧ G ⊆ G₀ ∧
      (μ.prod ν) (G₀ \ G) ≤ ((2:ℝ≥0∞)^(2*N))⁻¹+(N^(4*H+2):ℕ)*threshold+t ∧
      ∀ x u : Space d, μ {z | (z,x) ∈ G ∧ ‖normalize (z-x)-u‖ ≤ r} ≤ C := by
  let S := Prod.swap ⁻¹' G₀
  have hS : MeasurableSet S := hG₀.preimage measurable_swap
  have hclasses : ∀ T ∈ regularizationIndex Q μ N (N/H) threshold,
      ∃ G : Set (Space d × Space d), MeasurableSet G ∧
        (ν.prod (normalizedClass Q μ (regularizationLeaves Q μ N)
          (regularizationLabel Q μ N (N/H)) T)) (S \ G) ≤ t ∧
        ∀ x u : Space d, normalizedClass Q μ (regularizationLeaves Q μ N)
          (regularizationLabel Q μ N (N/H)) T
          {z | (x,z) ∈ G ∧ ‖normalize (z-x)-u‖ ≤ r} ≤ C := by
    intro T hT
    have hT' := hT
    simp only [regularizationIndex,Finset.mem_filter] at hT'
    obtain ⟨p,hp,hpT⟩ := Finset.mem_image.mp hT'.1
    have : IsProbabilityMeasure (normalizedClass Q μ (regularizationLeaves Q μ N)
        (regularizationLabel Q μ N (N/H)) T) := by
      simpa only [sourceClass,hpT] using regularization_class_probability Q hQ μ N (N/H) hp
    obtain ⟨G,hG,hd,hc⟩ := hlocal p hp (hpT.symm ▸ hT)
    refine ⟨Prod.swap ⁻¹' G,hG.preimage measurable_swap,?_,?_⟩
    · have he : S \ Prod.swap ⁻¹' G = Prod.swap ⁻¹' (G₀ \ G) := rfl
      rw [he,← Measure.map_apply measurable_swap (hG₀.diff hG),Measure.prod_swap]
      simpa only [sourceClass,hpT] using hd
    · simpa only [sourceClass,hpT,mem_preimage,Prod.swap_prod_mk] using hc
  obtain ⟨G,hG,hsub,hd,hc⟩ := relative_regularization_radial_gain Q hQ μ ν S hS
    hroot hH hNH hdN hthreshold t C r hclasses
  refine ⟨Prod.swap ⁻¹' G,hG.preimage measurable_swap,fun z hz => hsub hz,?_,hc⟩
  have he : G₀ \ Prod.swap ⁻¹' G = Prod.swap ⁻¹' (S \ G) := by
    ext z
    simp only [mem_sdiff,mem_preimage,S,Prod.swap_swap]
  rw [he,← Measure.map_apply measurable_swap (hS.diff hG),Measure.prod_swap]
  exact hd

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_WeakRadialTotalCost
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Absorbing the actual regularization and radial deletion costs -/

namespace Falconer
open scoped ENNReal

theorem weak_radial_total_real_cost (J k : ℕ) {A lam a b f : ℝ}
    (hA : 0 ≤ A) (hlam : 0 < lam) (ha : 0 < a) (hb : 0 < b) (hf : 0 < f) :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ((2:ℝ)^N)^(-2:ℝ)+(N:ℝ)^k*((2:ℝ)^N)^(-lam)+
        (J:ℝ)*(A*((2:ℝ)^N)^(-a)+((2:ℝ)^N)^(-b))+
        ((J:ℝ)+1)*((2:ℝ)^N)^(-f) ≤ ((2:ℝ)^N)^(-c) := by
  let q := min (lam/2) (min a (min b (min f 2)))
  have hq : 0 < q := lt_min (half_pos hlam) (lt_min ha (lt_min hb (lt_min hf (by norm_num))))
  have hql : q ≤ lam/2 := min_le_left _ _
  have hqa : q ≤ a := (min_le_right _ _).trans (min_le_left _ _)
  have hqb : q ≤ b := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hqf : q ≤ f := (min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hq2 : q ≤ 2 := (min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  let D : ℝ := 2+(J:ℝ)*A+(J:ℝ)+((J:ℝ)+1)
  obtain ⟨N₁,h₁⟩ := PlanarFalconer.fixed_polynomial_subpower k (half_pos hlam)
  obtain ⟨N₂,h₂⟩ := Regularization.fixed_constant_absorbed (half_pos hq) D
  refine ⟨q/2,half_pos hq,max 1 (max N₁ N₂),?_⟩
  intro N hN
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast ((le_max_left _ _).trans hN)
  have hN₁ : N₁ ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hN₂ : N₂ ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  let R : ℝ := (2:ℝ)^N
  have hR1 : 1 ≤ R := one_le_pow₀ (by norm_num)
  have hR : 0 < R := zero_lt_one.trans_le hR1
  have hp : (N:ℝ)^k ≤ R^(lam/2) :=
    (pow_le_pow_left₀ (Nat.cast_nonneg _) (by linarith : (N:ℝ) ≤ 4*(N:ℝ)+1) k).trans (h₁ N hN₁)
  have hpoly : (N:ℝ)^k*R^(-lam) ≤ R^(-q) := by
    calc
      _ ≤ R^(lam/2)*R^(-lam) := mul_le_mul_of_nonneg_right hp (by positivity)
      _ = R^(-(lam/2)) := by rw [← Real.rpow_add hR]; congr 1; ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hR1 (by linarith)
  have hbound : R^(-2:ℝ)+(N:ℝ)^k*R^(-lam)+
      (J:ℝ)*(A*R^(-a)+R^(-b))+((J:ℝ)+1)*R^(-f) ≤ D*R^(-q) := by
    have h2 := Real.rpow_le_rpow_of_exponent_le hR1 (neg_le_neg hq2)
    have ha' := Real.rpow_le_rpow_of_exponent_le hR1 (neg_le_neg hqa)
    have hb' := Real.rpow_le_rpow_of_exponent_le hR1 (neg_le_neg hqb)
    have hf' := Real.rpow_le_rpow_of_exponent_le hR1 (neg_le_neg hqf)
    calc
      _ ≤ R^(-q)+R^(-q)+(J:ℝ)*(A*R^(-q)+R^(-q))+((J:ℝ)+1)*R^(-q) := by
        gcongr
      _ = _ := by dsimp [D]; ring
  apply hbound.trans
  calc
    _ ≤ R^(q/2)*R^(-q) := mul_le_mul_of_nonneg_right (h₂ N hN₂) (by positivity)
    _ = R^(-(q/2)) := by rw [← Real.rpow_add hR]; congr 1; ring

theorem dyadic_thin_cost (N : ℕ) : ((2:ℝ≥0∞)^(2*N))⁻¹ =
    ENNReal.ofReal (((2:ℝ)^N)^(-2:ℝ)) := by
  rw [Real.rpow_neg (by positivity),Real.rpow_two,
    ENNReal.ofReal_inv_of_pos (by positivity),ENNReal.ofReal_pow (by positivity)]
  rw [ENNReal.ofReal_pow (by norm_num : (0:ℝ) ≤ 2),ENNReal.ofReal_ofNat,
    ← pow_mul,Nat.mul_comm 2 N]

theorem weak_radial_total_cost (J k : ℕ) {A lam a b f : ℝ}
    (hA : 0 ≤ A) (hlam : 0 < lam) (ha : 0 < a) (hb : 0 < b) (hf : 0 < f) :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ((2:ℝ≥0∞)^(2*N))⁻¹+(N^k:ℕ)*ENNReal.ofReal (((2:ℝ)^N)^(-lam))+
        (J:ℝ≥0∞)*(ENNReal.ofReal (A*((2:ℝ)^N)^(-a))+ENNReal.ofReal (((2:ℝ)^N)^(-b)))+
        (J+1:ℝ≥0∞)*ENNReal.ofReal (((2:ℝ)^N)^(-f)) ≤ ENNReal.ofReal (((2:ℝ)^N)^(-c)) := by
  obtain ⟨c,hc,N₀,hN₀⟩ := weak_radial_total_real_cost J k hA hlam ha hb hf
  refine ⟨c,hc,N₀,fun N hN => ?_⟩
  have hh := ENNReal.ofReal_le_ofReal (hN₀ N hN)
  rw [dyadic_thin_cost]
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  simp (disch := positivity) only [ENNReal.ofReal_add,ENNReal.ofReal_mul,
    ENNReal.ofReal_pow,ENNReal.ofReal_natCast,ENNReal.ofReal_one]
  norm_cast

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Measures_PairCorePruning
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Core restrictions and density pruning preserve the original pair-cost ledger -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {X Y ι : Type*} [MeasurableSpace X] [MeasurableSpace Y]

theorem product_core_compl_null (ν : Measure X) (μ : Measure Y) [SFinite μ] (P : Set X) (S : Set Y)
    (hP : ν Pᶜ = 0) (hS : μ Sᶜ = 0) : (ν.prod μ) (P ×ˢ S)ᶜ = 0 := by
  apply le_antisymm _ zero_le
  calc
    _ ≤ (ν.prod μ) (Pᶜ ×ˢ univ ∪ univ ×ˢ Sᶜ) := by
      apply measure_mono
      intro p hp
      by_cases hx : p.1 ∈ P
      · exact Or.inr ⟨mem_univ _,fun hy => hp ⟨hx,hy⟩⟩
      · exact Or.inl ⟨hx,mem_univ _⟩
    _ ≤ (ν.prod μ) (Pᶜ ×ˢ univ)+(ν.prod μ) (univ ×ˢ Sᶜ) := measure_union_le _ _
    _ = 0 := by simp only [Measure.prod_prod,hP,hS,zero_mul,mul_zero,add_zero]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_RelativePairCore
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Discarding null source and pin sets relative to the incoming relation -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

theorem relative_pair_core_null (μ : Measure X) (ν : Measure Y) [SFinite ν]
    (G : Set (X × Y)) (A : Set X) (P : Set Y) (hA : μ Aᶜ = 0) (hP : ν Pᶜ = 0) :
    (μ.prod ν) (G \ (G ∩ (A ×ˢ P))) = 0 := by
  apply le_antisymm _ zero_le
  apply (measure_mono (show G \ (G ∩ (A ×ˢ P)) ⊆ (A ×ˢ P)ᶜ from ?_)).trans_eq
    (product_core_compl_null μ ν A P hA hP)
  intro x hx hcore
  exact hx.2 ⟨hx.1,hcore⟩

theorem relative_pruning_cost_trans {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (G H K : Set X) {a b : ℝ≥0∞} (hGH : μ (G \ H) ≤ a) (hHK : μ (H \ K) ≤ b) :
    μ (G \ K) ≤ a+b := by
  have hsub : G \ K ⊆ (G \ H) ∪ (H \ K) := by
    intro x hx
    by_cases hh : x ∈ H
    · exact Or.inr ⟨hh,hx.2⟩
    · exact Or.inl ⟨hx.1,hh⟩
  exact (measure_mono hsub).trans ((measure_union_le _ _).trans (add_le_add hGH hHK))

namespace Regularization
variable {d : ℕ}

theorem source_class_pair_core (Q : DyadicCube d) (hQ : 0 < Q.side)
    (μ ν : Measure (Space d)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (N B : ℕ) (p : CellPath d) (hp : p ∈ regularizationLeaves Q μ N)
    (A P : Set (Space d)) (hA : MeasurableSet A) (hP : MeasurableSet P)
    (hAfull : μ Aᶜ = 0) (hPfull : ν Pᶜ = 0)
    (G : Set (Space d × Space d)) (hG : MeasurableSet G) :
    ∃ G₀ : Set (Space d × Space d), MeasurableSet G₀ ∧ G₀ ⊆ G ∧
      G₀ ⊆ (A ∩ Q.occupiedTreeCore (sourceClass Q μ N B p) N) ×ˢ P ∧
      ((sourceClass Q μ N B p).prod ν) (G \ G₀) = 0 := by
  let ρ := sourceClass Q μ N B p
  have : IsProbabilityMeasure ρ := regularization_class_probability Q hQ μ N B hp
  let S := A ∩ Q.occupiedTreeCore ρ N
  have hS : MeasurableSet S := hA.inter (Q.occupiedTreeCore_measurable ρ N)
  have hSfull : ρ Sᶜ = 0 := by
    rw [show Sᶜ = Aᶜ ∪ (Q.occupiedTreeCore ρ N)ᶜ by exact compl_inter _ _]
    apply le_antisymm _ zero_le
    apply (measure_union_le _ _).trans_eq
    rw [sourceClass_absolutelyContinuous_ol Q μ N B p hAfull,
      Q.occupiedTreeCore_full ρ N (sourceClass_root_null Q hQ μ N B p),add_zero]
  refine ⟨G ∩ (S ×ˢ P),hG.inter (hS.prod hP),inter_subset_left,inter_subset_right,?_⟩
  exact relative_pair_core_null ρ ν G S P hSfull hPfull

end Regularization
end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_RadialCollisionWidths
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Fixed-width radial collision tests at nearby dyadic depths -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem radialCollisionMass_mono (μ : Measure (Space d)) (p : Space d × Space d)
    {δ δ' : ℝ} (h : δ ≤ δ') : radialCollisionMass μ δ p ≤ radialCollisionMass μ δ' p :=
  measure_mono (fun _ hy => hy.trans h)

theorem dyadic_width_rounding (C : ℝ) :
    ∃ J : ℕ, ∀ n : ℕ, J ≤ n → C/(2:ℝ)^n ≤ 1/(2:ℝ)^(n-J) := by
  obtain ⟨J,hJ⟩ := Regularization.fixed_constant_absorbed (by norm_num : (0:ℝ) < 1) C
  have hC : C ≤ (2:ℝ)^J := by simpa only [Real.rpow_one] using hJ J le_rfl
  refine ⟨J,fun n hn => ?_⟩
  have he : 1/(2:ℝ)^(n-J) = (2:ℝ)^J/(2:ℝ)^n := by
    conv_rhs => rw [show n = J+(n-J) by omega,pow_add]
    field_simp
  rw [he]
  exact div_le_div_of_nonneg_right hC (by positivity)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_RelativeScaleBudget
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform constant absorption when passing from the full to the middle scale -/

namespace Falconer

theorem dyadic_relative_scale_bound (N k : ℕ) {α β : ℝ}
    (h : (N:ℝ)*α ≤ (k:ℝ)*β) : ((2:ℝ)^N)^α ≤ ((2:ℝ)^k)^β := by
  rw [← Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 2),
    ← Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 2)]
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) h

theorem eventually_relative_scale_constant {η : ℝ} (hη : 0 < η) (C : ℝ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ k : ℕ, ∀ α β : ℝ,
      (N:ℝ)*(η+α) ≤ (k:ℝ)*β →
      C*((2:ℝ)^N)^α ≤ ((2:ℝ)^k)^β := by
  obtain ⟨N₀,hN₀⟩ := Regularization.fixed_constant_absorbed hη C
  refine ⟨N₀,fun N hN k α β hbudget => ?_⟩
  calc
    _ ≤ ((2:ℝ)^N)^η*((2:ℝ)^N)^α :=
      mul_le_mul_of_nonneg_right (hN₀ N hN) (by positivity)
    _ = ((2:ℝ)^N)^(η+α) := (Real.rpow_add (by positivity) _ _).symm
    _ ≤ _ := dyadic_relative_scale_bound N k hbudget

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_OneScaleGeometry
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Fixed normalization and collision widths for the three-interval argument -/

namespace Falconer

theorem cellContraction_pos (d : ℕ) : 0 < cellContraction d := by
  unfold cellContraction
  positivity

theorem cellContraction_le_one (d : ℕ) : cellContraction d ≤ 1 := by
  unfold cellContraction
  apply (div_le_one (by positivity)).mpr
  nlinarith [Real.sqrt_nonneg (d:ℝ)]

theorem cellContraction_sqrt (d : ℕ) : cellContraction d*Real.sqrt d ≤ 1/4 := by
  unfold cellContraction
  rw [one_div,mul_comm,← div_eq_mul_inv]
  apply (div_le_iff₀ (by positivity : 0 < 4*(Real.sqrt (d:ℝ)+1))).mpr
  ring_nf
  linarith

theorem dyadic_collision_width (d : ℕ) {s C : ℝ} (hs : 0 < s)
    (hC : 4*Real.sqrt d/s+2 ≤ C) {v N : ℕ} (hvN : v ≤ N) :
    2*(Real.sqrt d*(1/(2:ℝ)^v))/(s/2)+2*(1/(2:ℝ)^N) ≤ C/(2:ℝ)^v := by
  have hδ : 1/(2:ℝ)^N ≤ 1/(2:ℝ)^v :=
    one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) hvN)
  have he : 2*(Real.sqrt d*(1/(2:ℝ)^v))/(s/2) =
      (4*Real.sqrt d/s)*(1/(2:ℝ)^v) := by
    field_simp
    ring
  rw [he]
  calc
    _ ≤ (4*Real.sqrt d/s)*(1/(2:ℝ)^v)+2*(1/(2:ℝ)^v) := by linarith
    _ = (4*Real.sqrt d/s+2)/(2:ℝ)^v := by ring
    _ ≤ _ := div_le_div_of_nonneg_right hC (by positivity)

theorem eventually_cell_diameter_small (d : ℕ) {γ s : ℝ}
    (hγ : 0 < γ) (hs : 0 < s) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ n : ℕ, γ*(N:ℝ) ≤ n →
      Real.sqrt d/(2:ℝ)^n ≤ s/2 := by
  obtain ⟨N₀,hN₀⟩ := Regularization.fixed_constant_absorbed hγ (2*Real.sqrt d/s)
  refine ⟨N₀,fun N hN n hn => ?_⟩
  have hh : 2*Real.sqrt d/s ≤ (2:ℝ)^n := by
    apply (hN₀ N hN).trans
    have hb : (N:ℝ)*γ ≤ (n:ℝ)*1 := by nlinarith
    simpa only [Real.rpow_one] using dyadic_relative_scale_bound N n hb
  have hh' := (div_le_iff₀ hs).mp hh
  apply (div_le_iff₀ (by positivity : 0 < (2:ℝ)^n)).mpr
  nlinarith

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_MiddleScaleGeometry
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform radial freezing from the integer contact margin -/

namespace Falconer

theorem middle_freeze_bound {b s : ℝ} (hb : 0 < b) (hs : 0 < s)
    {p v : ℕ} (hpv : p ≤ v) (hvp : v ≤ 2*p)
    (hlarge : 1/(2*b*s) ≤ (2:ℝ)^(2*p-v)) :
    (1/2:ℝ)/(b*(2:ℝ)^p*s) ≤ 1/(2:ℝ)^(v-p) := by
  have he : (2:ℝ)^(2*p-v)*(2:ℝ)^(v-p) = (2:ℝ)^p := by
    rw [← pow_add,show 2*p-v+(v-p) = p by omega]
  have hh : (1/2:ℝ) ≤ (2:ℝ)^(2*p-v)*b*s := by
    have h := (div_le_iff₀ (show 0 < 2*b*s by positivity)).mp hlarge
    nlinarith
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  simp only [one_mul]
  calc
    (1/2:ℝ)*(2:ℝ)^(v-p) ≤ ((2:ℝ)^(2*p-v)*b*s)*(2:ℝ)^(v-p) :=
      mul_le_mul_of_nonneg_right hh (by positivity)
    _ = b*(2:ℝ)^p*s := by rw [← he]; ring

theorem eventually_uniform_middle_freeze {b s γ : ℝ}
    (hb : 0 < b) (hs : 0 < s) (hγ : 0 < γ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ p v : ℕ, p ≤ v →
      γ*(N:ℝ) ≤ 2*(p:ℝ)-(v:ℝ) →
      (1/2:ℝ)/(b*(2:ℝ)^p*s) ≤ 1/(2:ℝ)^(v-p) := by
  obtain ⟨N₀,hN₀⟩ := Regularization.fixed_constant_absorbed hγ (1/(2*b*s))
  refine ⟨N₀,fun N hN p v hpv hmargin => ?_⟩
  have hvp : v ≤ 2*p := by
    have hnonneg : 0 ≤ γ*(N:ℝ) := mul_nonneg hγ.le (Nat.cast_nonneg N)
    have hh : (v:ℝ) ≤ (2*p:ℕ) := by push_cast; linarith
    exact_mod_cast hh
  apply middle_freeze_bound hb hs hpv hvp
  apply (hN₀ N hN).trans
  have hh : (N:ℝ)*γ ≤ ((2*p-v:ℕ):ℝ)*1 := by
    rw [Nat.cast_sub hvp]
    push_cast
    nlinarith
  simpa only [Real.rpow_one] using dyadic_relative_scale_bound N (2*p-v) hh

theorem eventually_integer_margin {γ : ℝ} (hγ : 0 < γ) (L : ℕ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ n : ℕ, γ*(N:ℝ) ≤ (n:ℝ) → L ≤ n := by
  obtain ⟨N₀,hN₀⟩ := exists_nat_gt ((L:ℝ)/γ)
  refine ⟨N₀,fun N hN n hn => ?_⟩
  have hN' : (N₀:ℝ) ≤ N := by exact_mod_cast hN
  have hL : (L:ℝ) < γ*(N₀:ℝ) := by
    have hh := (div_lt_iff₀ hγ).mp hN₀
    nlinarith
  have hn' : (L:ℝ) ≤ n := by
    have hh := mul_le_mul_of_nonneg_left hN' hγ.le
    linarith
  exact_mod_cast hn'

theorem middle_width_rounding {b H C : ℝ} (p v J : ℕ) (hpv : p ≤ v)
    (hJ : J ≤ v-p) (hC : b*H*C ≤ (2:ℝ)^J) :
    (b*(2:ℝ)^p*H)*(C/(2:ℝ)^v) ≤ 1/(2:ℝ)^((v-p)-J) := by
  have hv : (2:ℝ)^v = (2:ℝ)^p*(2:ℝ)^(v-p) := by
    rw [← pow_add,Nat.add_sub_of_le hpv]
  have hw : (2:ℝ)^(v-p) = (2:ℝ)^J*(2:ℝ)^((v-p)-J) := by
    rw [← pow_add,Nat.add_sub_of_le hJ]
  calc
    _ = (b*H*C)/(2:ℝ)^(v-p) := by rw [hv]; field_simp
    _ ≤ (2:ℝ)^J/(2:ℝ)^(v-p) := div_le_div_of_nonneg_right hC (by positivity)
    _ = _ := by rw [hw]; field_simp

theorem eventually_contact_middle_depth {γ : ℝ} (hγ : 0 < γ) (J M₀ : ℕ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ k : ℕ, ∀ Δ : ℝ,
      γ ≤ Δ → Δ*(N:ℝ)-1 ≤ (k:ℝ) →
      M₀ ≤ k-J ∧ (N:ℝ)*Δ ≤ 2*((k-J:ℕ):ℝ) := by
  let L : ℕ := max (J+M₀+1) (2*J+2)
  obtain ⟨N₀,hN₀⟩ := exists_nat_gt ((L:ℝ)/γ)
  refine ⟨N₀,fun N hN k Δ hγΔ hgap => ?_⟩
  have hNN : (N₀:ℝ) ≤ N := by exact_mod_cast hN
  have hlarge : (L:ℝ) < γ*(N:ℝ) := by
    have hh := (div_lt_iff₀ hγ).mp hN₀
    nlinarith
  have hγN : γ*(N:ℝ) ≤ Δ*(N:ℝ) :=
    mul_le_mul_of_nonneg_right hγΔ (Nat.cast_nonneg N)
  have hfirst : J+M₀ ≤ k := by
    have hL : ((J+M₀+1:ℕ):ℝ) ≤ L := by exact_mod_cast le_max_left (J+M₀+1) (2*J+2)
    have hh : ((J+M₀:ℕ):ℝ) ≤ k := by push_cast at hL ⊢; linarith
    exact_mod_cast hh
  have hsecond : 2*J+1 ≤ k := by
    have hL : ((2*J+2:ℕ):ℝ) ≤ L := by exact_mod_cast le_max_right (J+M₀+1) (2*J+2)
    have hh : ((2*J+1:ℕ):ℝ) ≤ k := by push_cast at hL ⊢; linarith
    exact_mod_cast hh
  refine ⟨by omega,?_⟩
  rw [Nat.cast_sub (by omega : J ≤ k)]
  have hh : 2*(J:ℝ)+1 ≤ k := by exact_mod_cast hsecond
  nlinarith

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_UniformMiddleGeometry
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One fixed angular coarsening works for every interval with the contact margins -/

namespace Falconer

theorem uniform_middle_geometry {σ r γ : ℝ} (hσ : 0 < σ) (hr : 0 < r)
    (hγ : 0 < γ) (H C : ℝ) (M₀ : ℕ) :
    ∃ J N₀ : ℕ, ∀ N ≥ N₀, ∀ p v : ℕ, ∀ Δ : ℝ,
      p ≤ v → γ ≤ Δ → Δ*(N:ℝ)-1 ≤ (v-p:ℕ) →
      γ*(N:ℝ) ≤ 2*(p:ℝ)-(v:ℝ) →
      let M := (v-p)-J
      J ≤ v-p ∧ M₀ ≤ M ∧ (N:ℝ)*Δ ≤ 2*(M:ℝ) ∧
      8*(1/4:ℝ)^2/((σ*(2:ℝ)^p)*r) ≤ 1/(2:ℝ)^M ∧
      ((σ*(2:ℝ)^p)*H)*(C/(2:ℝ)^v) ≤ 1/(2:ℝ)^M := by
  obtain ⟨J,hJ⟩ := Regularization.fixed_constant_absorbed (by norm_num : (0:ℝ) < 1) (σ*H*C)
  have hC : σ*H*C ≤ (2:ℝ)^J := by simpa only [Real.rpow_one] using hJ J le_rfl
  obtain ⟨N₁,hN₁⟩ := eventually_uniform_middle_freeze hσ hr hγ
  obtain ⟨N₂,hN₂⟩ := eventually_contact_middle_depth hγ J (M₀+1)
  refine ⟨J,max N₁ N₂,?_⟩
  intro N hN p v Δ hpv hγΔ hgap hmargin
  dsimp only
  obtain ⟨hM,hwidth⟩ := hN₂ N ((le_max_right _ _).trans hN) (v-p) Δ hγΔ hgap
  have hJk : J ≤ v-p := by omega
  refine ⟨hJk,by omega,hwidth,?_,middle_width_rounding p v J hpv hJk hC⟩
  have hh := hN₁ N ((le_max_left _ _).trans hN) p v hpv hmargin
  have hδ : 1/(2:ℝ)^(v-p) ≤ 1/(2:ℝ)^((v-p)-J) :=
    one_div_le_one_div_of_le (by positivity)
      (pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _))
  norm_num only [show 8*(1/4:ℝ)^2 = 1/2 by norm_num]
  exact hh.trans hδ

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_RadialZoom
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Positive affine changes of scale preserve original radial directions -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal
variable {d : ℕ}

theorem zoomPairSet_measurable (e : Space d ≃ₜ Space d)
    {G : Set (Space d × Space d)} (hG : MeasurableSet G) : MeasurableSet (zoomPairSet e G) :=
  hG.preimage (e.symm.measurable.prodMap e.symm.measurable)

theorem radial_collision_zoom (μ : Measure (Space d)) {a : ℝ} (ha : 0 < a)
    (c z x : Space d) (θ : ℝ) :
    radialCollisionMass (Measure.map (radialZoom a ha.ne' c) μ) θ
      (radialZoom a ha.ne' c z,radialZoom a ha.ne' c x) = radialCollisionMass μ θ (z,x) := by
  let e := radialZoom a ha.ne' c
  unfold radialCollisionMass
  rw [Measure.map_apply e.measurable (by
    apply measurableSet_le _ measurable_const
    exact (measurable_normalized_vector (measurable_id.sub measurable_const)).dist measurable_const)]
  congr 1
  ext y
  dsimp only [e]
  simp only [mem_preimage,mem_ofPred_eq,radialZoom_sub,normalize_smul_of_pos ha]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_RadialZoomLaw
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Original radial laws and source balls under positive affine rescaling -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal
variable {d : ℕ}

theorem radialZoom_preimage_ball {a : ℝ} (ha : 0 < a) (c x : Space d) (r : ℝ) :
    radialZoom a ha.ne' c ⁻¹' Metric.ball x r = Metric.ball (c+a⁻¹ • x) (r/a) := by
  ext z
  have he : a • (z-c)-x = a • (z-(c+a⁻¹ • x)) := by
    simp only [smul_sub,smul_add,smul_smul,mul_inv_cancel₀ ha.ne',one_smul]
    abel
  simp only [mem_preimage,Metric.mem_ball,dist_eq_norm,radialZoom_apply]
  rw [he,norm_smul,Real.norm_eq_abs,abs_of_pos ha,lt_div_iff₀ ha]
  rw [mul_comm a]

theorem radialZoom_ball_apply (μ : Measure (Space d)) {a : ℝ} (ha : 0 < a)
    (c x : Space d) (r : ℝ) :
    Measure.map (radialZoom a ha.ne' c) μ (Metric.ball x r) =
      μ (Metric.ball (c+a⁻¹ • x) (r/a)) := by
  rw [Measure.map_apply (radialZoom a ha.ne' c).measurable Metric.isOpen_ball.measurableSet,
    radialZoom_preimage_ball ha]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_RadialZoomFiniteBalls
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite-scale conditional balls and reverse caps after a fixed contraction -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal
variable {d : ℕ}

theorem radialZoom_ae_iff (μ : Measure (Space d)) {a : ℝ} (ha : 0 < a)
    (c : Space d) (P : Space d → Prop) :
    (∀ᵐ x ∂Measure.map (radialZoom a ha.ne' c) μ, P x) ↔
      ∀ᵐ x ∂μ, P (radialZoom a ha.ne' c x) := by
  have h := MeasurableEquiv.map_ae (radialZoom a ha.ne' c).toMeasurableEquiv μ
  change Filter.map (radialZoom a ha.ne' c) (ae μ) =
    ae (Measure.map (radialZoom a ha.ne' c) μ) at h
  rw [← h]
  rfl

theorem radialZoom_scaled_ball_bound (μ : Measure (Space d))
    {a δ K L s : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hK : 1 ≤ K)
    (hL : 0 < L) (hs : 0 ≤ s) (hmass : μ univ ≤ 1) (c : Space d)
    (hball : ∀ x : Space d, ∀ r : ℝ, δ ≤ r → r ≤ 1/L →
      μ (Metric.ball x r) ≤ ENNReal.ofReal (K*(L*r)^s)) :
    ∀ x : Space d, ∀ r : ℝ, 0 < r → δ ≤ r →
      Measure.map (radialZoom a ha.ne' c) μ (Metric.ball x r) ≤
        ENNReal.ofReal (K*a^(-s)*(L*r)^s) := by
  intro x r hr hδ
  rw [radialZoom_ball_apply μ ha]
  have hrra : r ≤ r/a := (le_div_iff₀ ha).mpr (mul_le_of_le_one_right hr.le ha1)
  have he : K*(L*(r/a))^s = K*a^(-s)*(L*r)^s := by
    rw [show L*(r/a) = (L*r)/a by ring,
      Real.div_rpow (mul_pos hL hr).le ha.le,div_eq_mul_inv,← Real.rpow_neg ha.le]
    ring
  rw [← he]
  by_cases hsmall : r/a ≤ 1/L
  · exact hball _ _ (hδ.trans hrra) hsmall
  · have hscale : 1 ≤ L*(r/a) := by
      have hh := (lt_of_not_ge hsmall)
      have hh' := (div_lt_iff₀ hL).mp hh
      nlinarith
    have hp := Real.one_le_rpow hscale hs
    have hcoeff : 1 ≤ K*(L*(r/a))^s := by nlinarith
    exact ((measure_mono (subset_univ _)).trans hmass).trans
      (by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hcoeff)

theorem norm_radialZoom_sub {a : ℝ} (ha : 0 < a) (c x y : Space d) :
    ‖radialZoom a ha.ne' c x-radialZoom a ha.ne' c y‖ = a*‖x-y‖ := by
  rw [radialZoom_sub,norm_smul,Real.norm_eq_abs,abs_of_pos ha]

theorem radialZoom_reverse_cap (ν : Measure (Space d)) {a : ℝ} (ha : 0 < a)
    (c z u : Space d) (r : ℝ) (G : Set (Space d × Space d)) (hG : MeasurableSet G) :
    Measure.map (radialZoom a ha.ne' c) ν
      {x | (radialZoom a ha.ne' c z,x) ∈ zoomPairSet (radialZoom a ha.ne' c) G ∧
        dist (normalize (x-radialZoom a ha.ne' c z)) u < r} =
      ν {x | (z,x) ∈ G ∧ dist (normalize (x-z)) u < r} := by
  let e := radialZoom a ha.ne' c
  have hm : MeasurableSet {x | (e z,x) ∈ zoomPairSet e G ∧
      dist (normalize (x-e z)) u < r} :=
    ((zoomPairSet_measurable e hG).preimage (measurable_const.prodMk measurable_id)).inter
      (measurableSet_lt ((measurable_normalized_vector
        (measurable_id.sub measurable_const)).dist measurable_const) measurable_const)
  rw [Measure.map_apply e.measurable hm]
  congr 1
  ext x
  simp only [mem_preimage,mem_ofPred_eq,mem_zoomPairSet]
  dsimp only [e]
  rw [radialZoom_sub,normalize_smul_of_pos ha]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_RadialCollisionDeletion
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Threshold deletion for the full conditional radial collision mass -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem radial_collision_pair_integral (μ ν : Measure (Space d))
    [SFinite μ] [SFinite ν] (G : Set (Space d × Space d)) (hG : MeasurableSet G) (δ : ℝ) :
    (∫⁻ p in G, radialCollisionMass μ δ p ∂μ.prod ν) =
      ∫⁻ z, (∫⁻ x in {x | (z,x) ∈ G}, radialCollisionMass μ δ (z,x) ∂ν) ∂μ := by
  rw [← lintegral_indicator hG,lintegral_prod _
    ((radialCollisionMass_measurable μ δ).indicator hG).aemeasurable]
  apply lintegral_congr
  intro z
  have hGz : MeasurableSet {x : Space d | (z,x) ∈ G} :=
    hG.preimage (measurable_const.prodMk measurable_id)
  rw [← lintegral_indicator hGz]
  rfl

theorem radial_collision_bad_mass (μ ν : Measure (Space d))
    [SFinite μ] [SFinite ν] (G : Set (Space d × Space d)) (hG : MeasurableSet G)
    (δ : ℝ) {F C : ℝ≥0∞} (hF : F ≠ 0) (hFtop : F ≠ ∞)
    (hmean : ∀ᵐ z ∂μ, (∫⁻ x in {x | (z,x) ∈ G}, radialCollisionMass μ δ (z,x) ∂ν) ≤ C) :
    (μ.prod ν) (G ∩ {p | F < radialCollisionMass μ δ p}) ≤ C*μ univ/F := by
  have hmeas := radialCollisionMass_measurable μ δ
  have htotal : (∫⁻ p in G, radialCollisionMass μ δ p ∂μ.prod ν) ≤ C*μ univ := by
    rw [radial_collision_pair_integral μ ν G hG δ]
    exact (lintegral_mono_ae hmean).trans_eq (lintegral_const C)
  have hm : ((μ.prod ν).restrict G) {p | F ≤ radialCollisionMass μ δ p} ≤
      (∫⁻ p in G, radialCollisionMass μ δ p ∂μ.prod ν)/F :=
    meas_ge_le_lintegral_div hmeas.aemeasurable hF hFtop
  calc
    _ = ((μ.prod ν).restrict G) {p | F < radialCollisionMass μ δ p} := by
      rw [Measure.restrict_apply (measurableSet_lt measurable_const hmeas),inter_comm]
    _ ≤ ((μ.prod ν).restrict G) {p | F ≤ radialCollisionMass μ δ p} :=
      measure_mono (fun p hp => show F ≤ radialCollisionMass μ δ p from
        (show F < radialCollisionMass μ δ p from hp).le)
    _ ≤ (∫⁻ p in G, radialCollisionMass μ δ p ∂μ.prod ν)/F := hm
    _ ≤ _ := ENNReal.div_le_div_right htotal F

theorem radial_collision_pruning (μ ν : Measure (Space d))
    [SFinite μ] [SFinite ν] (G : Set (Space d × Space d)) (hG : MeasurableSet G)
    (δ : ℝ) {F C : ℝ≥0∞} (hF : F ≠ 0) (hFtop : F ≠ ∞)
    (hmean : ∀ᵐ z ∂μ, (∫⁻ x in {x | (z,x) ∈ G}, radialCollisionMass μ δ (z,x) ∂ν) ≤ C) :
    ∃ H : Set (Space d × Space d), MeasurableSet H ∧ H ⊆ G ∧
      (μ.prod ν) (G \ H) ≤ C*μ univ/F ∧ ∀ p ∈ H, radialCollisionMass μ δ p ≤ F := by
  let H := G ∩ {p | radialCollisionMass μ δ p ≤ F}
  refine ⟨H,hG.inter (measurableSet_le (radialCollisionMass_measurable μ δ) measurable_const),
    inter_subset_left,?_,fun _ hp => hp.2⟩
  have he : G \ H = G ∩ {p | F < radialCollisionMass μ δ p} := by
    ext p
    simp only [H,mem_sdiff,mem_inter_iff,mem_ofPred_eq,not_and,not_le]
    tauto
  rw [he]
  exact radial_collision_bad_mass μ ν G hG δ hF hFtop hmean

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_RadialAngleCaps
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Two radial caps control near-collinear affine triples -/

namespace Falconer
open Set Metric MeasureTheory NormedSpace
open scoped ENNReal
variable {n : ℕ}

theorem displacementAngle_two_caps (p q z : Space n) (hq : q ≠ p) (hz : z ≠ p)
    {r : ℝ} (hr : 0 < r) (ha : displacementAngle p q z ≤ r) :
    dist (normalize (z-p)) (normalize (q-p)) < 3*r ∨
      dist (normalize (z-p)) (-normalize (q-p)) < 3*r := by
  let u := normalize (q-p)
  let v := normalize (z-p)
  have hu : ‖u‖ = 1 := norm_normalize (sub_ne_zero.mpr hq)
  have hv : ‖v‖ = 1 := norm_normalize (sub_ne_zero.mpr hz)
  have hv0 : v ≠ 0 := norm_ne_zero_iff.mp (by rw [hv]; norm_num)
  rcases perpendicular_direction_two_caps hu hv0 ha with hl | hr'
  · left
    have hh : ‖u-v‖ ≤ 2*r := by
      simpa only [hv,inv_one,one_smul,div_one] using hl
    change ‖v-u‖ < 3*r
    rw [norm_sub_rev]
    linarith
  · right
    have hh : ‖u+v‖ ≤ 2*r := by
      simpa only [hv,inv_one,neg_smul,one_smul,div_one,sub_neg_eq_add] using hr'
    change ‖v-(-u)‖ < 3*r
    rw [sub_neg_eq_add,add_comm]
    linarith

theorem radial_angle_sublevel (μ : Measure (Space n)) (G : Set (Space n × Space n))
    (p q : Space n) (hq : q ≠ p) (hdiag : ∀ z, (p,z) ∈ G → z ≠ p)
    {r K ℓ : ℝ} (hr : 0 < r)
    (hcap : ∀ u : Space n, ‖u‖ = 1 →
      μ {z | (p,z) ∈ G ∧ dist (normalize (z-p)) u < 3*r} ≤
        ENNReal.ofReal (K*(3*r)^ℓ)) :
    μ {z | (p,z) ∈ G ∧ displacementAngle p q z ≤ r} ≤
      2*ENNReal.ofReal (K*(3*r)^ℓ) := by
  let u := normalize (q-p)
  have hu : ‖u‖ = 1 := norm_normalize (sub_ne_zero.mpr hq)
  have hsub : {z | (p,z) ∈ G ∧ displacementAngle p q z ≤ r} ⊆
      {z | (p,z) ∈ G ∧ dist (normalize (z-p)) u < 3*r} ∪
      {z | (p,z) ∈ G ∧ dist (normalize (z-p)) (-u) < 3*r} := by
    rintro z ⟨hz,ha⟩
    rcases displacementAngle_two_caps p q z hq (hdiag z hz) hr ha with h | h
    · exact Or.inl ⟨hz,h⟩
    · exact Or.inr ⟨hz,h⟩
  have hh := (measure_mono hsub).trans ((measure_union_le _ _).trans
    (add_le_add (hcap u hu) (hcap (-u) (by simpa only [norm_neg] using hu))))
  exact hh.trans_eq (by ring)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_ReverseRadialGeometry
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reverse radial caps bound collisions of original source directions -/

namespace Falconer
open NormedSpace
variable {n : ℕ}

theorem unit_perpendicular_norm_symm {u v : Space n} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    ‖perpendicularPart u v‖ = ‖perpendicularPart v u‖ := by
  have h₁ := norm_perpendicularPart_sq hu v
  have h₂ := norm_perpendicularPart_sq hv u
  rw [hu] at h₂
  rw [hv] at h₁
  rw [real_inner_comm u v] at h₂
  nlinarith [norm_nonneg (perpendicularPart u v),norm_nonneg (perpendicularPart v u)]

theorem perpendicularPart_neg_left (u v : Space n) :
    perpendicularPart (-u) v = perpendicularPart u v := by
  simp [perpendicularPart,neg_smul]

theorem reverse_radial_angle_identity (x z y : Space n) (hz : z ≠ x) (hy : y ≠ z) :
    ‖y-z‖*displacementAngle z y x =
      ‖perpendicularPart (normalize (z-x)) (y-z)‖ := by
  have hx : x-z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz)
  have hy0 : y-z ≠ 0 := sub_ne_zero.mpr hy
  have hsym := unit_perpendicular_norm_symm (norm_normalize hy0) (norm_normalize hx)
  have hneg : normalize (x-z) = -normalize (z-x) := by
    simp only [NormedSpace.normalize,norm_sub_rev x z]
    rw [show x-z = -(z-x) by abel,smul_neg]
  have he : perpendicularPart (normalize (z-x)) (y-z) =
      ‖y-z‖ • perpendicularPart (normalize (z-x)) (normalize (y-z)) := by
    rw [← perpendicularPart_smul,norm_smul_normalize]
  rw [he,norm_smul,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)]
  congr 1
  change ‖perpendicularPart (normalize (y-z)) (normalize (x-z))‖ = _
  rw [hsym,hneg,perpendicularPart_neg_left]

theorem reverse_radial_collision_angle (x z y : Space n) (hz : z ≠ x) (hy : y ≠ z)
    {D δ : ℝ} (hD : ‖y-x‖ ≤ D)
    (hclose : dist (normalize (y-x)) (normalize (z-x)) ≤ δ) :
    displacementAngle z y x ≤ D*δ/‖y-z‖ := by
  have hu : ‖normalize (z-x)‖ = 1 := norm_normalize (sub_ne_zero.mpr hz)
  have hperp : ‖perpendicularPart (normalize (z-x)) (normalize (y-x))‖ ≤ δ := by
    have hh := norm_perpendicularPart_le hu (normalize (y-x)-normalize (z-x))
    rw [perpendicularPart_sub] at hh
    have he : perpendicularPart (normalize (z-x)) (normalize (z-x)) = 0 := by
      simp [perpendicularPart,hu]
    rw [he,sub_zero] at hh
    exact hh.trans hclose
  have hraw : ‖perpendicularPart (normalize (z-x)) (y-z)‖ ≤ D*δ := by
    have he : y-z = (y-x)-(z-x) := by abel
    rw [he,perpendicularPart_sub,perpendicular_normalize_self,sub_zero]
    have he' : perpendicularPart (normalize (z-x)) (y-x) =
        ‖y-x‖ • perpendicularPart (normalize (z-x)) (normalize (y-x)) := by
      rw [← perpendicularPart_smul,norm_smul_normalize]
    rw [he',norm_smul,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)]
    exact mul_le_mul hD hperp (norm_nonneg _) ((norm_nonneg _).trans hD)
  apply (le_div_iff₀ (norm_pos_iff.mpr (sub_ne_zero.mpr hy))).mpr
  rw [mul_comm,reverse_radial_angle_identity x z y hz hy]
  exact hraw

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_RadialZoomPruning
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Pulling conditional radial pruning back to the unchanged original pair law -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem radial_pruning_unzoom (μ ν : Measure (Space d)) [SFinite μ] [SFinite ν]
    {a : ℝ} (ha : 0 < a) (c : Space d)
    (G : Set (Space d × Space d)) (hG : MeasurableSet G)
    (H : Set (Space d × Space d)) (hH : MeasurableSet H)
    (hsub : H ⊆ zoomPairSet (radialZoom a ha.ne' c) G)
    (θ : ℝ) (F E : ℝ≥0∞)
    (hdel : ((Measure.map (radialZoom a ha.ne' c) μ).prod
      (Measure.map (radialZoom a ha.ne' c) ν))
      (zoomPairSet (radialZoom a ha.ne' c) G \ H) ≤ E)
    (hbound : ∀ p ∈ H, radialCollisionMass (Measure.map (radialZoom a ha.ne' c) μ) θ p ≤ F) :
    ∃ G' : Set (Space d × Space d), MeasurableSet G' ∧ G' ⊆ G ∧
      (μ.prod ν) (G \ G') ≤ E ∧ ∀ p ∈ G', radialCollisionMass μ θ p ≤ F := by
  let e := radialZoom a ha.ne' c
  let G' := (Prod.map e e) ⁻¹' H
  have hG' : MeasurableSet G' := hH.preimage (e.measurable.prodMap e.measurable)
  refine ⟨G',hG',?_,?_,?_⟩
  · intro p hp
    exact (mem_zoomPairSet e G p.1 p.2).mp (hsub hp)
  · have he : (Prod.map e e) ⁻¹' (zoomPairSet e G \ H) = G \ G' := by
      ext p
      change ((e p.1,e p.2) ∈ zoomPairSet e G ∧ (e p.1,e p.2) ∉ H) ↔
        ((p.1,p.2) ∈ G ∧ (e p.1,e p.2) ∉ H)
      rw [mem_zoomPairSet]
    rw [← he,← Measure.map_apply (e.measurable.prodMap e.measurable)
      ((zoomPairSet_measurable e hG).diff hH),← Measure.map_prod_map μ ν e.measurable e.measurable]
    exact hdel
  · intro p hp
    have hh := hbound (e p.1,e p.2) hp
    rwa [radial_collision_zoom μ ha c p.1 p.2 θ] at hh

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_ProfileIncrementFrostman
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Turning a contact-interval profile inequality into actual conditional ball bounds -/

namespace Falconer.Regularization
open Set MeasureTheory Metric
open scoped ENNReal
variable {d : ℕ}

theorem profileDrop_le_of_increment (m : ℝ → ℝ) (N : ℕ) (s E : ℝ)
    {p t : ℕ} (hpt : p ≤ t)
    (hinc : ∀ n, p ≤ n → n ≤ t → s*(n-p:ℕ)/N-E ≤ m n-m p) :
    profileDrop m N s p t ≤ E := by
  obtain ⟨i,hpi,hit,hmin⟩ := PlanarFalconer.intervalMin_attained
    (fun n : ℕ => m n-s*(n:ℝ)/N) hpt
  unfold profileDrop
  rw [hmin]
  have hh := hinc i hpi hit
  rw [Nat.cast_sub hpi] at hh
  have he : s*((i:ℝ)-(p:ℝ))/N = s*(i:ℝ)/N-s*(p:ℝ)/N := by ring
  rw [he] at hh
  linarith

theorem sourceClass_conditional_frostman_of_increment (Q : DyadicCube d) (hQ : Q.side = 1)
    (μ : Measure (Space d)) [IsProbabilityMeasure μ] {N B : ℕ} (hN : 0 < N) (hB : 0 < B)
    {lam s E : ℝ} (hs : 0 ≤ s) (hwidth : (B:ℝ) ≤ lam*(N:ℝ))
    (hlarge : (2:ℝ)^(N/B+2) ≤ ((2:ℝ)^N)^lam)
    {p₀ : CellPath d} (hp₀ : p₀ ∈ regularizationLeaves Q μ N)
    {p t : ℕ} (hpt : p ≤ t) (htN : t ≤ N) {P : CellPath d} (hP : P.length = p)
    (hPpos : 0 < sourceClass Q μ N B p₀ (Q.descendant P).carrier)
    (hinc : ∀ n, p ≤ n → n ≤ t →
      s*(n-p:ℕ)/N-E ≤ sourceProfile Q μ N B p₀ n-sourceProfile Q μ N B p₀ p) :
    ∀ x : Space d, ∀ r : ℝ, 1/(2:ℝ)^(t-p) ≤ r → r ≤ 1 →
      (Measure.map (cellScaleMap p (Q.descendant P).center)
        (ProbabilityTheory.cond (sourceClass Q μ N B p₀) (Q.descendant P).carrier)) (ball x r) ≤
      ENNReal.ofReal ((((2*Nat.ceil (2+4*Real.sqrt d)+1)^d:ℕ):ℝ)*(2:ℝ)^s*
        ((2:ℝ)^N)^(E+2*((d:ℝ)+1)*lam)*r^s) := by
  intro x r hr hr1
  apply (sourceClass_conditional_frostman Q hQ μ hN hB hs hwidth hlarge hp₀ hpt htN hP hPpos x r hr hr1).trans
  apply ENNReal.ofReal_le_ofReal
  have hr0 : 0 ≤ r := (show 0 ≤ 1/(2:ℝ)^(t-p) by positivity).trans hr
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hr0 s)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num))
  exact add_le_add (profileDrop_le_of_increment _ N s E hpt hinc) le_rfl

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Measures_OriginalConditionalFrostman
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Conditional source-ball estimates before changing the original coordinates -/

namespace Falconer.Regularization
open Set MeasureTheory Metric
open scoped ENNReal
variable {d : ℕ}

theorem sourceClass_original_conditional_frostman (Q : DyadicCube d) (hQ : Q.side = 1)
    (μ : Measure (Space d)) [IsProbabilityMeasure μ] {N B : ℕ} (hN : 0 < N) (hB : 0 < B)
    {lam s E : ℝ} (hs : 0 ≤ s) (hwidth : (B:ℝ) ≤ lam*(N:ℝ))
    (hlarge : (2:ℝ)^(N/B+2) ≤ ((2:ℝ)^N)^lam)
    {p₀ : CellPath d} (hp₀ : p₀ ∈ regularizationLeaves Q μ N)
    {p t : ℕ} (hpt : p ≤ t) (htN : t ≤ N) {P : CellPath d} (hP : P.length = p)
    (hPpos : 0 < sourceClass Q μ N B p₀ (Q.descendant P).carrier)
    (hinc : ∀ n, p ≤ n → n ≤ t →
      s*(n-p:ℕ)/N-E ≤ sourceProfile Q μ N B p₀ n-sourceProfile Q μ N B p₀ p) :
    ∀ x : Space d, ∀ r : ℝ, 1/(2:ℝ)^t ≤ r → r ≤ 1/(2:ℝ)^p →
      ProbabilityTheory.cond (sourceClass Q μ N B p₀) (Q.descendant P).carrier (ball x r) ≤
      ENNReal.ofReal ((((2*Nat.ceil (2+4*Real.sqrt d)+1)^d:ℕ):ℝ)*(2:ℝ)^s*
        ((2:ℝ)^N)^(E+2*((d:ℝ)+1)*lam)*((2:ℝ)^p*r)^s) := by
  intro x r hr hr1
  have hpow : 0 < (2:ℝ)^p := by positivity
  have hscale : (2:ℝ)^p*(1/(2:ℝ)^t) = 1/(2:ℝ)^(t-p) := by
    conv_lhs => rw [show t = p+(t-p) by omega,pow_add]
    field_simp
  have hlo : 1/(2:ℝ)^(t-p) ≤ (2:ℝ)^p*r := by
    rw [← hscale]
    exact mul_le_mul_of_nonneg_left hr hpow.le
  have hhi : (2:ℝ)^p*r ≤ 1 := by
    calc
      _ ≤ (2:ℝ)^p*(1/(2:ℝ)^p) := mul_le_mul_of_nonneg_left hr1 hpow.le
      _ = 1 := by field_simp
  have hh := sourceClass_conditional_frostman_of_increment Q hQ μ hN hB hs hwidth hlarge
    hp₀ hpt htN hP hPpos hinc (cellScaleMap p (Q.descendant P).center x) ((2:ℝ)^p*r) hlo hhi
  rw [rescaled_conditional_ball_apply] at hh
  have hc : (Q.descendant P).center+((2:ℝ)^p)⁻¹ • cellScaleMap p (Q.descendant P).center x = x := by
    simp only [cellScaleMap,smul_smul,inv_mul_cancel₀ hpow.ne',one_smul]
    abel
  have hrad : ((2:ℝ)^p*r)/(2:ℝ)^p = r := by field_simp
  rwa [hc,hrad] at hh

theorem sourceClass_original_conditional_frostman_power (Q : DyadicCube d) (hQ : Q.side = 1)
    (μ : Measure (Space d)) [IsProbabilityMeasure μ] {N B : ℕ} (hN : 0 < N) (hB : 0 < B)
    {lam s E η : ℝ} (hs : 0 ≤ s) (hwidth : (B:ℝ) ≤ lam*(N:ℝ))
    (hlarge : (2:ℝ)^(N/B+2) ≤ ((2:ℝ)^N)^lam)
    {p₀ : CellPath d} (hp₀ : p₀ ∈ regularizationLeaves Q μ N)
    {p t : ℕ} (hpt : p ≤ t) (htN : t ≤ N) {P : CellPath d} (hP : P.length = p)
    (hPpos : 0 < sourceClass Q μ N B p₀ (Q.descendant P).carrier)
    (hinc : ∀ n, p ≤ n → n ≤ t →
      s*(n-p:ℕ)/N-E ≤ sourceProfile Q μ N B p₀ n-sourceProfile Q μ N B p₀ p)
    (hcoef : (((2*Nat.ceil (2+4*Real.sqrt d)+1)^d:ℕ):ℝ)*(2:ℝ)^s*
      ((2:ℝ)^N)^(E+2*((d:ℝ)+1)*lam) ≤ ((2:ℝ)^N)^η) :
    ∀ x : Space d, ∀ r : ℝ, 1/(2:ℝ)^t ≤ r → r ≤ 1/(2:ℝ)^p →
      ProbabilityTheory.cond (sourceClass Q μ N B p₀) (Q.descendant P).carrier (ball x r) ≤
        ENNReal.ofReal (((2:ℝ)^N)^η*((2:ℝ)^p*r)^s) := by
  intro x r hr hr1
  apply (sourceClass_original_conditional_frostman Q hQ μ hN hB hs hwidth hlarge hp₀
    hpt htN hP hPpos hinc x r hr hr1).trans
  apply ENNReal.ofReal_le_ofReal
  have hr0 : 0 ≤ r := (by positivity : (0:ℝ) ≤ 1/(2:ℝ)^t).trans hr
  exact mul_le_mul_of_nonneg_right hcoef (Real.rpow_nonneg (by positivity) _)

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_ConditionalCellGeometry
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Original conditional laws stay within the actual dyadic cell diameter -/

namespace Falconer.Regularization
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem conditional_cell_pair_geometry (Q : DyadicCube d) (hQ : Q.side = 1)
    (ρ : Measure (Space d)) (P : CellPath d) {g : ℕ} (hP : P.length = g)
    {D : ℝ} (hD : Real.sqrt d ≤ D)
    (G : Set (Space d × Space d))
    (hpin : ∀ z x, (z,x) ∈ G → ∀ y ∈ (Q.descendant P).carrier, ‖y-x‖ ≤ D) :
    ∀ᵐ z ∂ProbabilityTheory.cond ρ (Q.descendant P).carrier,
      ∀ᵐ y ∂ProbabilityTheory.cond ρ (Q.descendant P).carrier,
        ‖y-z‖ ≤ D/(2:ℝ)^g ∧ ∀ x, (z,x) ∈ G → ‖y-x‖ ≤ D := by
  apply ProbabilityTheory.ae_cond_of_forall_mem (Q.descendant P).measurable
  intro z hz
  apply ProbabilityTheory.ae_cond_of_forall_mem (Q.descendant P).measurable
  intro y hy
  refine ⟨?_,fun x hx => hpin z x hx y hy⟩
  have hside : 0 ≤ (Q.descendant P).side := by rw [Q.descendant_side,hQ]; positivity
  have hh := (Q.descendant P).dist_le hside hy hz
  rw [dist_eq_norm,Q.descendant_side,hQ,hP] at hh
  apply hh.trans
  simpa only [mul_one_div] using div_le_div_of_nonneg_right hD
    (by positivity : (0:ℝ) ≤ 2^g)

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_ReverseRadialMass
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Original reverse cap bounds control radial collision pins -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal
variable {n : ℕ}

theorem reverse_radial_collision_mass (ν : Measure (Space n))
    (G : Set (Space n × Space n)) (z y : Space n) (hy : y ≠ z)
    (hdiag : ∀ x, (z,x) ∈ G → x ≠ z) {D δ K q : ℝ}
    (hD : 0 < D) (hδ : 0 < δ)
    (hbound : ∀ x, (z,x) ∈ G → ‖y-x‖ ≤ D)
    (hcap : ∀ u : Space n, ‖u‖ = 1 →
      ν {x | (z,x) ∈ G ∧ dist (normalize (x-z)) u < 3*(D*δ/‖y-z‖)} ≤
        ENNReal.ofReal (K*(3*(D*δ/‖y-z‖))^q)) :
    ν {x | (z,x) ∈ G ∧ dist (normalize (y-x)) (normalize (z-x)) ≤ δ} ≤
      2*ENNReal.ofReal (K*(3*(D*δ/‖y-z‖))^q) := by
  have hr : 0 < D*δ/‖y-z‖ := div_pos (mul_pos hD hδ)
    (norm_pos_iff.mpr (sub_ne_zero.mpr hy))
  apply (measure_mono (show
    {x | (z,x) ∈ G ∧ dist (normalize (y-x)) (normalize (z-x)) ≤ δ} ⊆
      {x | (z,x) ∈ G ∧ displacementAngle z y x ≤ D*δ/‖y-z‖} from ?_)).trans
    (radial_angle_sublevel ν G z y hy hdiag hr hcap)
  rintro x ⟨hx,hclose⟩
  exact ⟨hx,reverse_radial_collision_angle x z y (Ne.symm (hdiag x hx)) hy (hbound x hx) hclose⟩

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_ReverseRadialTruncation
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A truncated-kernel bound for the mass of original collision pins -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal
variable {n : ℕ}

theorem reverse_radial_collision_truncated (ν : Measure (Space n))
    (G : Set (Space n × Space n)) (z y : Space n)
    (hdiag : ∀ x, (z,x) ∈ G → x ≠ z) {D δ K q : ℝ}
    (hD : 1 ≤ D) (hδ : 0 < δ) (hK : 1 ≤ K) (hq : 0 ≤ q)
    (hmass : ν univ ≤ 1) (hyz : ‖y-z‖ ≤ 1)
    (hbound : ∀ x, (z,x) ∈ G → ‖y-x‖ ≤ D)
    (hcap : ∀ r : ℝ, δ ≤ r → ∀ u : Space n, ‖u‖ = 1 →
      ν {x | (z,x) ∈ G ∧ dist (normalize (x-z)) u < r} ≤
        ENNReal.ofReal (K*r^q)) :
    ν {x | (z,x) ∈ G ∧ dist (normalize (y-x)) (normalize (z-x)) ≤ δ} ≤
      ENNReal.ofReal ((2*K*(3*D)^q)*(δ/max ‖y-z‖ δ)^q) := by
  have hD0 : 0 < D := lt_of_lt_of_le zero_lt_one hD
  by_cases hnear : ‖y-z‖ ≤ δ
  · rw [max_eq_right hnear,div_self hδ.ne',Real.one_rpow,mul_one]
    have hp : 1 ≤ (3*D)^q := Real.one_le_rpow (by linarith) hq
    have hL : 1 ≤ 2*K*(3*D)^q := by nlinarith
    exact ((measure_mono (subset_univ _)).trans hmass).trans
      (by simpa using ENNReal.ofReal_le_ofReal hL)
  · have hr : δ < ‖y-z‖ := lt_of_not_ge hnear
    have hr0 : 0 < ‖y-z‖ := hδ.trans hr
    have hy : y ≠ z := sub_ne_zero.mp (norm_pos_iff.mp hr0)
    have hrange : δ ≤ 3*(D*δ/‖y-z‖) := by
      rw [show 3*(D*δ/‖y-z‖) = 3*D*δ/‖y-z‖ by ring]
      apply (le_div_iff₀ hr0).mpr
      nlinarith
    have hh := reverse_radial_collision_mass ν G z y hy hdiag hD0 hδ hbound
      (fun u hu => hcap (3*(D*δ/‖y-z‖)) hrange u hu)
    apply hh.trans_eq
    rw [max_eq_left hr.le]
    rw [show 3*(D*δ/‖y-z‖) = (3*D)*(δ/‖y-z‖) by ring,
      Real.mul_rpow (by positivity) (by positivity)]
    conv_lhs =>
      lhs
      rw [show (2:ℝ≥0∞) = ENNReal.ofReal (2:ℝ) by norm_num]
    rw [← ENNReal.ofReal_mul (by norm_num)]
    congr 1
    ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_CriticalPotential
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The logarithmic potential bound at the critical ball exponent

Unlike the strictly subcritical energy estimate, the finite critical estimate
has one bounded contribution per dyadic scale. It is used on the outer
intervals of the radial profile argument.
-/

namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal
variable {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]

theorem regularized_potential_critical (μ : Measure X) (x : X)
    {K q : ℝ} (hq : 0 ≤ q) (g k : ℕ)
    (hball : ∀ n : ℕ, n ≤ g+k →
      μ (ball x (1/(2:ℝ)^n)) ≤ ENNReal.ofReal (K*(1/(2:ℝ)^n)^q)) :
    (∫⁻ y in ball x (1/(2:ℝ)^g),
      ENNReal.ofReal ((1/(dist x y+1/(2:ℝ)^(g+k)))^q) ∂μ) ≤
      ENNReal.ofReal K+(k:ℝ≥0∞)*ENNReal.ofReal (K*(2:ℝ)^q) := by
  apply (regularized_potential_dyadic μ x hq g k).trans
  have hstart : ENNReal.ofReal (((2:ℝ)^g)^q)*μ (ball x (1/(2:ℝ)^g)) ≤
      ENNReal.ofReal K := by
    calc
      _ ≤ ENNReal.ofReal (((2:ℝ)^g)^q)*ENNReal.ofReal (K*(1/(2:ℝ)^g)^q) :=
        mul_le_mul_right (hball g (by omega)) _
      _ = _ := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        calc
          _ = K*((((2:ℝ)^g)^q)*(1/(2:ℝ)^g)^q) := by ring
          _ = K := by rw [dyadic_potential_start,sub_self,Real.rpow_zero,mul_one]
  have hterm (j : ℕ) (hj : j ∈ Finset.range k) :
      ENNReal.ofReal (((2:ℝ)^(g+j+1))^q)*μ (ball x (1/(2:ℝ)^(g+j))) ≤
      ENNReal.ofReal (K*(2:ℝ)^q) := by
    calc
      _ ≤ ENNReal.ofReal (((2:ℝ)^(g+j+1))^q)*
          ENNReal.ofReal (K*(1/(2:ℝ)^(g+j))^q) :=
        mul_le_mul_right (hball (g+j) (by have := Finset.mem_range.mp hj; omega)) _
      _ = _ := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        calc
          _ = K*((((2:ℝ)^(g+j+1))^q)*(1/(2:ℝ)^(g+j))^q) := by ring
          _ = K*(2:ℝ)^q := by
            rw [dyadic_potential_weight,sub_self,Real.rpow_zero,mul_one]
  calc
    _ ≤ ENNReal.ofReal K+∑ j ∈ Finset.range k, ENNReal.ofReal (K*(2:ℝ)^q) :=
      add_le_add hstart (Finset.sum_le_sum hterm)
    _ = _ := by simp

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_CriticalScalarPotential
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Critical dyadic inverse potentials of a nonnegative statistic -/

namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal
variable {X : Type*} [MeasurableSpace X]

theorem regularized_scalar_potential_critical (μ : Measure X) (a : X → ℝ)
    (ha : Measurable a) (ha0 : ∀ x, 0 ≤ a x)
    {K q : ℝ} (hq : 0 ≤ q) (g k : ℕ)
    (hsmall : ∀ j : ℕ, j ≤ g+k →
      μ {x | a x < 1/(2:ℝ)^j} ≤ ENNReal.ofReal (K*(1/(2:ℝ)^j)^q)) :
    (∫⁻ x in {x | a x < 1/(2:ℝ)^g},
      ENNReal.ofReal ((1/(a x+1/(2:ℝ)^(g+k)))^q) ∂μ) ≤
      ENNReal.ofReal K+(k:ℝ≥0∞)*ENNReal.ofReal (K*(2:ℝ)^q) := by
  have hpre (j : ℕ) : a ⁻¹' ball (0:ℝ) (1/(2:ℝ)^j) = {x | a x < 1/(2:ℝ)^j} := by
    ext x
    simp only [mem_preimage,mem_ball,Real.dist_eq,sub_zero,abs_of_nonneg (ha0 x),mem_ofPred_eq]
  have hball (j : ℕ) (hj : j ≤ g+k) :
      (Measure.map a μ) (ball (0:ℝ) (1/(2:ℝ)^j)) ≤
        ENNReal.ofReal (K*(1/(2:ℝ)^j)^q) := by
    rw [Measure.map_apply ha measurableSet_ball,hpre]
    exact hsmall j hj
  have hh := regularized_potential_critical (Measure.map a μ) (0:ℝ) hq g k hball
  have hf : Measurable (fun z : ℝ =>
      ENNReal.ofReal ((1/(dist 0 z+1/(2:ℝ)^(g+k)))^q)) := by fun_prop
  have he : (∫⁻ z in ball (0:ℝ) (1/(2:ℝ)^g),
      ENNReal.ofReal ((1/(dist 0 z+1/(2:ℝ)^(g+k)))^q) ∂Measure.map a μ) =
      ∫⁻ x in {x | a x < 1/(2:ℝ)^g},
        ENNReal.ofReal ((1/(a x+1/(2:ℝ)^(g+k)))^q) ∂μ := by
    rw [← lintegral_indicator measurableSet_ball,lintegral_map
      (hf.indicator measurableSet_ball) ha,
      ← lintegral_indicator (measurableSet_lt ha measurable_const)]
    apply lintegral_congr
    intro x
    by_cases hx : a x < 1/(2:ℝ)^g
    · have hz : a x ∈ ball (0:ℝ) (1/(2:ℝ)^g) := by
        change x ∈ a ⁻¹' ball (0:ℝ) (1/(2:ℝ)^g)
        rw [hpre]
        exact hx
      rw [indicator_of_mem hz,indicator_of_mem (show x ∈ {x | a x < 1/(2:ℝ)^g} from hx)]
      simp only [Real.dist_eq,zero_sub,abs_neg,abs_of_nonneg (ha0 x)]
    · have hz : a x ∉ ball (0:ℝ) (1/(2:ℝ)^g) := by
        change x ∉ a ⁻¹' ball (0:ℝ) (1/(2:ℝ)^g)
        rw [hpre]
        exact hx
      rw [indicator_of_notMem hz,indicator_of_notMem (show x ∉ {x | a x < 1/(2:ℝ)^g} from hx)]
  rw [he] at hh
  exact hh

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_TruncatedScalarPotential
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The maximum-truncated kernel and its dyadic sublevel bound -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {X : Type*} [MeasurableSpace X]

theorem inverse_max_le_two_inverse_add {x r : ℝ} (hx : 0 ≤ x) (hr : 0 < r) :
    1/max x r ≤ 2/(x+r) := by
  apply (div_le_div_iff₀ (hr.trans_le (le_max_right x r)) (by positivity)).mpr
  have h₁ := le_max_left x r
  have h₂ := le_max_right x r
  linarith

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_CriticalTruncatedPotential
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Critical maximum-truncated potentials with logarithmic scale loss -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {X : Type*} [MeasurableSpace X]

theorem truncated_scalar_potential_critical (μ : Measure X) (a : X → ℝ)
    (ha : Measurable a) (ha0 : ∀ x, 0 ≤ a x)
    {K q : ℝ} (hq : 0 ≤ q) (g k : ℕ)
    (hsmall : ∀ j : ℕ, j ≤ g+k →
      μ {x | a x < 1/(2:ℝ)^j} ≤ ENNReal.ofReal (K*(1/(2:ℝ)^j)^q)) :
    (∫⁻ x in {x | a x < 1/(2:ℝ)^g},
      ENNReal.ofReal ((1/max (a x) (1/(2:ℝ)^(g+k)))^q) ∂μ) ≤
      ENNReal.ofReal ((2:ℝ)^q)*
        (ENNReal.ofReal K+(k:ℝ≥0∞)*ENNReal.ofReal (K*(2:ℝ)^q)) := by
  have hp (x : X) : (1/max (a x) (1/(2:ℝ)^(g+k)))^q ≤
      (2:ℝ)^q*(1/(a x+1/(2:ℝ)^(g+k)))^q := by
    have hax := ha0 x
    calc
      _ ≤ (2/(a x+1/(2:ℝ)^(g+k)))^q := Real.rpow_le_rpow (by positivity)
        (inverse_max_le_two_inverse_add (ha0 x) (by positivity)) hq
      _ = _ := by
        rw [show 2/(a x+1/(2:ℝ)^(g+k)) = 2*(1/(a x+1/(2:ℝ)^(g+k))) by ring,
          Real.mul_rpow (by norm_num) (by positivity)]
  calc
    _ ≤ ∫⁻ x in {x | a x < 1/(2:ℝ)^g},
        ENNReal.ofReal ((2:ℝ)^q)*ENNReal.ofReal ((1/(a x+1/(2:ℝ)^(g+k)))^q) ∂μ := by
      apply lintegral_mono
      intro x
      dsimp only
      rw [← ENNReal.ofReal_mul (by positivity)]
      exact ENNReal.ofReal_le_ofReal (hp x)
    _ = ENNReal.ofReal ((2:ℝ)^q)*(∫⁻ x in {x | a x < 1/(2:ℝ)^g},
        ENNReal.ofReal ((1/(a x+1/(2:ℝ)^(g+k)))^q) ∂μ) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ _ := mul_le_mul' le_rfl
      (regularized_scalar_potential_critical μ a ha ha0 hq g k hsmall)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_RadialCollisionMean
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Original-pin radial collision means on a profile interval

The comparison source is the full conditional source law. The reverse pin
law remains a restriction of the original pin measure; no fiber is normalized.
-/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal
variable {d : ℕ}

theorem radial_collision_mean_bound (μ ν : Measure (Space d))
    [SFinite μ] [SFinite ν] (G : Set (Space d × Space d)) (hG : MeasurableSet G)
    (z : Space d) {D Kν Kμ q : ℝ} (hD : 1 ≤ D) (hKν : 1 ≤ Kν) (hq : 0 ≤ q)
    (hmass : ν univ ≤ 1) (g k : ℕ)
    (hdiag : ∀ x, (z,x) ∈ G → x ≠ z)
    (hsource : ∀ᵐ y ∂μ, ‖y-z‖ < 1/(2:ℝ)^g ∧
      ∀ x, (z,x) ∈ G → ‖y-x‖ ≤ D)
    (hball : ∀ j : ℕ, j ≤ g+k →
      μ {y | ‖y-z‖ < 1/(2:ℝ)^j} ≤ ENNReal.ofReal (Kμ*(1/(2:ℝ)^j)^q))
    (hcap : ∀ r : ℝ, 1/(2:ℝ)^(g+k) ≤ r → ∀ u : Space d, ‖u‖ = 1 →
      ν {x | (z,x) ∈ G ∧ dist (normalize (x-z)) u < r} ≤ ENNReal.ofReal (Kν*r^q)) :
    (∫⁻ x in {x | (z,x) ∈ G}, radialCollisionMass μ (1/(2:ℝ)^(g+k)) (z,x) ∂ν) ≤
      ENNReal.ofReal (2*Kν*(3*D)^q*(1/(2:ℝ)^(g+k))^q)*
        (ENNReal.ofReal ((2:ℝ)^q)*
          (ENNReal.ofReal Kμ+(k:ℝ≥0∞)*ENNReal.ofReal (Kμ*(2:ℝ)^q))) := by
  let δ : ℝ := 1/(2:ℝ)^(g+k)
  let L : ℝ := 2*Kν*(3*D)^q
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hD0 : 0 < D := lt_of_lt_of_le zero_lt_one hD
  have hK0 : 0 < Kν := lt_of_lt_of_le zero_lt_one hKν
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hS : μ.restrict {y | ‖y-z‖ < 1/(2:ℝ)^g} = μ :=
    Measure.restrict_eq_self_of_ae_mem (hsource.mono fun _ h => h.1)
  have hp : ∀ᵐ y ∂μ,
      ν {x | (z,x) ∈ G ∧ dist (normalize (y-x)) (normalize (z-x)) ≤ δ} ≤
        ENNReal.ofReal (L*δ^q)*ENNReal.ofReal ((1/max ‖y-z‖ δ)^q) := by
    filter_upwards [hsource] with y hy
    have hy1 : ‖y-z‖ ≤ 1 := hy.1.le.trans (by
      apply (div_le_one (by positivity)).mpr
      exact one_le_pow₀ (by norm_num))
    have hh := reverse_radial_collision_truncated ν G z y hdiag hD hδ hKν hq hmass hy1 hy.2 hcap
    apply hh.trans_eq
    change ENNReal.ofReal (L*(δ/max ‖y-z‖ δ)^q) = _
    rw [show δ/max ‖y-z‖ δ = δ*(1/max ‖y-z‖ δ) by ring,
      Real.mul_rpow hδ.le (by positivity)]
    rw [← ENNReal.ofReal_mul (mul_nonneg hL (Real.rpow_nonneg hδ.le _))]
    congr 1
    ring
  rw [radial_collision_original_pin_fubini μ ν G hG z]
  calc
    _ ≤ ∫⁻ y, ENNReal.ofReal (L*δ^q)*ENNReal.ofReal ((1/max ‖y-z‖ δ)^q) ∂μ :=
      lintegral_mono_ae hp
    _ = ENNReal.ofReal (L*δ^q)*(∫⁻ y in {y | ‖y-z‖ < 1/(2:ℝ)^g},
        ENNReal.ofReal ((1/max ‖y-z‖ δ)^q) ∂μ) := by
      rw [hS,lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ _ := mul_le_mul' le_rfl
      (truncated_scalar_potential_critical μ (fun y => ‖y-z‖) (by fun_prop)
        (fun _ => norm_nonneg _) hq g k hball)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_RadialMeanPowers
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The logarithmic radial mean loss is absorbed by a small scale power -/

namespace Falconer

theorem dyadic_radial_power_cancel (g k : ℕ) (q : ℝ) :
    ((2:ℝ)^g)^q*(1/(2:ℝ)^(g+k))^q = ((2:ℝ)^k)^(-q) := by
  calc
    _ = (((2:ℝ)^g)*(1/(2:ℝ)^(g+k)))^q :=
      (Real.mul_rpow (by positivity) (by positivity)).symm
    _ = (1/(2:ℝ)^k)^q := by congr 1; rw [pow_add]; field_simp
    _ = _ := by rw [one_div,Real.inv_rpow (by positivity),Real.rpow_neg (by positivity)]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_RadialMeanPowerBound
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform power form of the original-pin radial mean bound -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal
variable {d : ℕ}

theorem ennreal_radial_mean_coefficient {a b c : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (k : ℕ) :
    ENNReal.ofReal a*(ENNReal.ofReal c*
      (ENNReal.ofReal b+(k:ℝ≥0∞)*ENNReal.ofReal (b*c))) =
        ENNReal.ofReal (a*c*(b+(k:ℝ)*(b*c))) := by
  have he : ENNReal.ofReal b+(k:ℝ≥0∞)*ENNReal.ofReal (b*c) =
      ENNReal.ofReal (b+(k:ℝ)*(b*c)) := by
    rw [ENNReal.ofReal_add hb (by positivity),
      ENNReal.ofReal_mul (Nat.cast_nonneg k),ENNReal.ofReal_natCast]
  rw [he,← ENNReal.ofReal_mul hc,← ENNReal.ofReal_mul ha]
  congr 1
  ring

theorem radial_cap_extend_large (ν : Measure (Space d)) (G : Set (Space d × Space d))
    (z : Space d) {δ K q : ℝ} (hK : 1 ≤ K) (hq : 0 ≤ q) (hmass : ν univ ≤ 1)
    (hcap : ∀ r : ℝ, δ ≤ r → r ≤ 1 → ∀ u : Space d, ‖u‖ = 1 →
      ν {x | (z,x) ∈ G ∧ dist (normalize (x-z)) u < r} ≤ ENNReal.ofReal (K*r^q)) :
    ∀ r : ℝ, δ ≤ r → ∀ u : Space d, ‖u‖ = 1 →
      ν {x | (z,x) ∈ G ∧ dist (normalize (x-z)) u < r} ≤ ENNReal.ofReal (K*r^q) := by
  intro r hr u hu
  by_cases hr1 : r ≤ 1
  · exact hcap r hr hr1 u hu
  · have hr1' : 1 ≤ r := (lt_of_not_ge hr1).le
    have hp : 1 ≤ r^q := Real.one_le_rpow hr1' hq
    have hb : 1 ≤ K*r^q := by nlinarith
    exact ((measure_mono (subset_univ _)).trans hmass).trans
      (by simpa using ENNReal.ofReal_le_ofReal hb)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_UniformOuterRadial
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A common outer-radial cutoff for all contact exponents above a fixed positive floor -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal
variable {d : ℕ}

theorem eventually_radial_mean_coefficient_uniform {D η₀ q : ℝ} (hD : 1 ≤ D) (hη₀ : 0 < η₀) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ η : ℝ, η₀ ≤ η → ∀ g k : ℕ, k ≤ N →
      (2*((2:ℝ)^N)^η*(3*D)^q*(1/(2:ℝ)^(g+k))^q)*
        (2:ℝ)^q*(((2:ℝ)^N)^η*((2:ℝ)^g)^q+
          (k:ℝ)*(((2:ℝ)^N)^η*((2:ℝ)^g)^q*(2:ℝ)^q)) ≤
      ((2:ℝ)^N)^(3*η)*((2:ℝ)^k)^(-q) := by
  let B := 2*(3*D)^q*(2:ℝ)^q
  let C := B*(1+(2:ℝ)^q)
  have hD0 : 0 < D := lt_of_lt_of_le zero_lt_one hD
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  obtain ⟨N₀,hN₀⟩ := PlanarFalconer.fixed_linear_subpower C hC hη₀
  refine ⟨N₀,fun N hN η hηge g k hk => ?_⟩
  let R : ℝ := (2:ℝ)^N
  have hR : 0 < R := by dsimp [R]; positivity
  have hcoef : B*(1+(k:ℝ)*(2:ℝ)^q) ≤ R^η := by
    apply le_trans ?_ ((hN₀ N hN).trans (Real.rpow_le_rpow_of_exponent_le
      (one_le_pow₀ (by norm_num)) hηge))
    have hkn : (k:ℝ) ≤ N := by exact_mod_cast hk
    have hp : 0 ≤ (2:ℝ)^q := by positivity
    have hnum : 1+(k:ℝ)*(2:ℝ)^q ≤ (1+(2:ℝ)^q)*(1+2*(N:ℝ)) := by
      nlinarith [show (0:ℝ) ≤ N from Nat.cast_nonneg N]
    exact (mul_le_mul_of_nonneg_left hnum hB).trans_eq (by dsimp [C]; ring)
  calc
    _ = (B*(1+(k:ℝ)*(2:ℝ)^q))*(R^η*R^η)*
        (((2:ℝ)^g)^q*(1/(2:ℝ)^(g+k))^q) := by dsimp [B,R]; ring
    _ = (B*(1+(k:ℝ)*(2:ℝ)^q))*R^(2*η)*((2:ℝ)^k)^(-q) := by
      rw [dyadic_radial_power_cancel,← Real.rpow_add hR,show η+η = 2*η by ring]
    _ ≤ R^η*R^(2*η)*((2:ℝ)^k)^(-q) := by gcongr
    _ = _ := by
      rw [← Real.rpow_add hR,show η+2*η = 3*η by ring]

theorem eventually_radial_collision_mean_uniform {D η₀ q : ℝ}
    (hD : 1 ≤ D) (hη₀ : 0 < η₀) (hq : 0 ≤ q) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ η : ℝ, η₀ ≤ η → ∀ g k : ℕ, k ≤ N →
      ∀ (μ ν : Measure (Space d)) [SFinite μ] [SFinite ν],
      ∀ (G : Set (Space d × Space d)), MeasurableSet G → ∀ z : Space d,
      ν univ ≤ 1 → (∀ x, (z,x) ∈ G → x ≠ z) →
      (∀ᵐ y ∂μ, ‖y-z‖ < 1/(2:ℝ)^g ∧ ∀ x, (z,x) ∈ G → ‖y-x‖ ≤ D) →
      (∀ j : ℕ, j ≤ g+k → μ {y | ‖y-z‖ < 1/(2:ℝ)^j} ≤
        ENNReal.ofReal ((((2:ℝ)^N)^η*((2:ℝ)^g)^q)*(1/(2:ℝ)^j)^q)) →
      (∀ r : ℝ, 1/(2:ℝ)^(g+k) ≤ r → r ≤ 1 → ∀ u : Space d, ‖u‖ = 1 →
        ν {x | (z,x) ∈ G ∧ dist (normalize (x-z)) u < r} ≤
          ENNReal.ofReal (((2:ℝ)^N)^η*r^q)) →
      (∫⁻ x in {x | (z,x) ∈ G}, radialCollisionMass μ (1/(2:ℝ)^(g+k)) (z,x) ∂ν) ≤
        ENNReal.ofReal (((2:ℝ)^N)^(3*η)*((2:ℝ)^k)^(-q)) := by
  obtain ⟨N₀,hN₀⟩ := eventually_radial_mean_coefficient_uniform hD hη₀
  refine ⟨N₀,?_⟩
  intro N hN η hηge g k hk μ ν _ _ G hG z hmass hdiag hsource hball hcap
  have hK : 1 ≤ ((2:ℝ)^N)^η := Real.one_le_rpow (one_le_pow₀ (by norm_num)) (hη₀.trans_le hηge).le
  have hb := radial_collision_mean_bound μ ν G hG z hD hK hq hmass g k hdiag hsource hball
    (radial_cap_extend_large ν G z hK hq hmass hcap)
  apply hb.trans
  rw [ennreal_radial_mean_coefficient (by positivity) (by positivity) (by positivity)]
  exact ENNReal.ofReal_le_ofReal (hN₀ N hN η hηge g k hk)

theorem outer_radial_interval_pruning_uniform {D η₀ q : ℝ}
    (hD : 1 ≤ D) (hη₀ : 0 < η₀) (hq : 0 ≤ q) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ η : ℝ, η₀ ≤ η → ∀ g k : ℕ, k ≤ N →
      ∀ (μ ν : Measure (Space d)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν],
      ∀ (G : Set (Space d × Space d)), MeasurableSet G →
      (∀ z x, (z,x) ∈ G → x ≠ z) →
      (∀ᵐ z ∂μ,
        (∀ᵐ y ∂μ, ‖y-z‖ < 1/(2:ℝ)^g ∧ ∀ x, (z,x) ∈ G → ‖y-x‖ ≤ D) ∧
        (∀ j : ℕ, j ≤ g+k → μ {y | ‖y-z‖ < 1/(2:ℝ)^j} ≤
          ENNReal.ofReal ((((2:ℝ)^N)^η*((2:ℝ)^g)^q)*(1/(2:ℝ)^j)^q)) ∧
        (∀ r : ℝ, 1/(2:ℝ)^(g+k) ≤ r → r ≤ 1 → ∀ u : Space d, ‖u‖ = 1 →
          ν {x | (z,x) ∈ G ∧ dist (normalize (x-z)) u < r} ≤
            ENNReal.ofReal (((2:ℝ)^N)^η*r^q))) →
      ∃ H : Set (Space d × Space d), MeasurableSet H ∧ H ⊆ G ∧
        (μ.prod ν) (G \ H) ≤ ENNReal.ofReal (((2:ℝ)^N)^(-η)) ∧
        ∀ p ∈ H, radialCollisionMass μ (1/(2:ℝ)^(g+k)) p ≤
          ENNReal.ofReal (((2:ℝ)^N)^(4*η)*((2:ℝ)^k)^(-q)) := by
  obtain ⟨N₀,hN₀⟩ := eventually_radial_collision_mean_uniform (d := d) hD hη₀ hq
  refine ⟨N₀,?_⟩
  intro N hN η hηge g k hk μ ν _ _ G hG hdiag hdata
  let R : ℝ := (2:ℝ)^N
  let S : ℝ := ((2:ℝ)^k)^(-q)
  have hR : 0 < R := by dsimp [R]; positivity
  have hS : 0 < S := by dsimp [S]; positivity
  have hF : 0 < R^(4*η)*S := by positivity
  have hmean : ∀ᵐ z ∂μ,
      (∫⁻ x in {x | (z,x) ∈ G}, radialCollisionMass μ (1/(2:ℝ)^(g+k)) (z,x) ∂ν) ≤
        ENNReal.ofReal (R^(3*η)*S) := by
    filter_upwards [hdata] with z hz
    exact hN₀ N hN η hηge g k hk μ ν G hG z (by simp) (hdiag z) hz.1 hz.2.1 hz.2.2
  obtain ⟨H,hH,hHG,hcost,hcap⟩ := radial_collision_pruning μ ν G hG
    (1/(2:ℝ)^(g+k)) (ENNReal.ofReal_pos.mpr hF).ne' ENNReal.ofReal_ne_top hmean
  refine ⟨H,hH,hHG,hcost.trans_eq ?_,hcap⟩
  rw [measure_univ,mul_one,← ENNReal.ofReal_div_of_pos hF]
  congr 1
  calc
    (R^(3*η)*S)/(R^(4*η)*S) = R^(3*η)/R^(4*η) := by
      exact mul_div_mul_right _ _ (ne_of_gt hS)
    _ = R^(3*η-4*η) := (Real.rpow_sub hR _ _).symm
    _ = R^(-η) := by congr 1; ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_OuterRadialWidths
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Outer-interval pruning with the fixed widths used by the cell multiplication lemma -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal
variable {d : ℕ}

theorem dyadic_shifted_decay {g v J : ℕ} (h : g+J ≤ v) (q : ℝ) :
    ((2:ℝ)^((v-J)-g))^(-q) = ((2:ℝ)^J)^q*((2:ℝ)^(v-g))^(-q) := by
  have he : v-g = J+((v-J)-g) := by omega
  conv_rhs => rw [he,pow_add]
  rw [Real.mul_rpow (by positivity) (by positivity),Real.rpow_neg (by positivity)]
  rw [← mul_assoc,← Real.rpow_add (by positivity),add_neg_cancel,Real.rpow_zero,one_mul]

theorem outer_radial_interval_fixed_width {D η₀ q : ℝ}
    (hD : 1 ≤ D) (hη₀ : 0 < η₀) (hq : 0 ≤ q) (C : ℝ) :
    ∃ J N₀ : ℕ, ∀ N ≥ N₀, ∀ η : ℝ, η₀ ≤ η →
      ∀ g v : ℕ, g+J ≤ v → v ≤ N →
      ∀ (μ ν : Measure (Space d)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν],
      ∀ (G : Set (Space d × Space d)), MeasurableSet G →
      (∀ z x, (z,x) ∈ G → x ≠ z) →
      (∀ᵐ z ∂μ,
        (∀ᵐ y ∂μ, ‖y-z‖ < 1/(2:ℝ)^g ∧ ∀ x, (z,x) ∈ G → ‖y-x‖ ≤ D) ∧
        (∀ j : ℕ, j ≤ v → μ {y | ‖y-z‖ < 1/(2:ℝ)^j} ≤
          ENNReal.ofReal ((((2:ℝ)^N)^η*((2:ℝ)^g)^q)*(1/(2:ℝ)^j)^q)) ∧
        (∀ r : ℝ, 1/(2:ℝ)^v ≤ r → r ≤ 1 → ∀ u : Space d, ‖u‖ = 1 →
          ν {x | (z,x) ∈ G ∧ dist (normalize (x-z)) u < r} ≤
            ENNReal.ofReal (((2:ℝ)^N)^η*r^q))) →
      ∃ H : Set (Space d × Space d), MeasurableSet H ∧ H ⊆ G ∧
        (μ.prod ν) (G \ H) ≤ ENNReal.ofReal (((2:ℝ)^N)^(-η)) ∧
        ∀ p ∈ H, radialCollisionMass μ (C/(2:ℝ)^v) p ≤
          ENNReal.ofReal (((2:ℝ)^N)^(5*η)*((2:ℝ)^(v-g))^(-q)) := by
  obtain ⟨J,hJ⟩ := dyadic_width_rounding C
  obtain ⟨N₁,hN₁⟩ := outer_radial_interval_pruning_uniform (d := d) hD hη₀ hq
  obtain ⟨N₂,hN₂⟩ := Regularization.fixed_constant_absorbed hη₀ (((2:ℝ)^J)^q)
  refine ⟨J,max N₁ N₂,?_⟩
  intro N hN η hη g v hgv hvN μ ν _ _ G hG hdiag hdata
  have hJv : J ≤ v := by omega
  have hg : g ≤ v-J := by omega
  have he : g+((v-J)-g) = v-J := Nat.add_sub_of_le hg
  have hr : 1/(2:ℝ)^v ≤ 1/(2:ℝ)^(v-J) := by
    apply one_div_le_one_div_of_le (by positivity)
    exact pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _)
  have hdata' : ∀ᵐ z ∂μ,
      (∀ᵐ y ∂μ, ‖y-z‖ < 1/(2:ℝ)^g ∧ ∀ x, (z,x) ∈ G → ‖y-x‖ ≤ D) ∧
      (∀ j : ℕ, j ≤ g+((v-J)-g) → μ {y | ‖y-z‖ < 1/(2:ℝ)^j} ≤
        ENNReal.ofReal ((((2:ℝ)^N)^η*((2:ℝ)^g)^q)*(1/(2:ℝ)^j)^q)) ∧
      (∀ r : ℝ, 1/(2:ℝ)^(g+((v-J)-g)) ≤ r → r ≤ 1 → ∀ u : Space d, ‖u‖ = 1 →
        ν {x | (z,x) ∈ G ∧ dist (normalize (x-z)) u < r} ≤
          ENNReal.ofReal (((2:ℝ)^N)^η*r^q)) := by
    filter_upwards [hdata] with z hz
    refine ⟨hz.1,fun j hj => hz.2.1 j (by omega),?_⟩
    intro r hrr hr1 u hu
    rw [he] at hrr
    exact hz.2.2 r (hr.trans hrr) hr1 u hu
  obtain ⟨H,hH,hHG,hdel,hbound⟩ := hN₁ N ((le_max_left _ _).trans hN) η hη g
    ((v-J)-g) (by omega) μ ν G hG hdiag hdata'
  refine ⟨H,hH,hHG,hdel,fun p hp => ?_⟩
  apply (radialCollisionMass_mono μ p (hJ v hJv)).trans
  rw [← he]
  apply (hbound p hp).trans
  apply ENNReal.ofReal_le_ofReal
  rw [dyadic_shifted_decay hgv]
  have hconst : ((2:ℝ)^J)^q ≤ ((2:ℝ)^N)^η :=
    (hN₂ N ((le_max_right _ _).trans hN)).trans
      (Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num)) hη)
  calc
    _ = (((2:ℝ)^N)^(4*η)*((2:ℝ)^J)^q)*((2:ℝ)^(v-g))^(-q) := by ring
    _ ≤ (((2:ℝ)^N)^(4*η)*((2:ℝ)^N)^η)*((2:ℝ)^(v-g))^(-q) := by gcongr
    _ = _ := by rw [← Real.rpow_add (by positivity),show 4*η+η = 5*η by ring]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_OuterRadialCell
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Outer radial pruning for a full conditional law in an original source cell -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal
variable {d : ℕ}

theorem outer_radial_cell_pruning {D η₀ q : ℝ}
    (hD : 1 ≤ D) (hη₀ : 0 < η₀) (hq : 0 ≤ q) (C : ℝ) :
    ∃ J N₀ : ℕ, ∀ N ≥ N₀, ∀ η : ℝ, η₀ ≤ η →
      ∀ g v : ℕ, g+J ≤ v → v ≤ N →
      ∀ (μ ν : Measure (Space d)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν],
      ∀ (G : Set (Space d × Space d)), MeasurableSet G →
      (∀ z x, (z,x) ∈ G → x ≠ z) →
      (∀ᵐ z ∂μ, ∀ᵐ y ∂μ,
        ‖y-z‖ ≤ D/(2:ℝ)^g ∧ ∀ x, (z,x) ∈ G → ‖y-x‖ ≤ D) →
      (∀ x : Space d, ∀ r : ℝ, 1/(2:ℝ)^v ≤ r → r ≤ 1/(2:ℝ)^g →
        μ (Metric.ball x r) ≤ ENNReal.ofReal (((2:ℝ)^N)^η*((2:ℝ)^g*r)^q)) →
      (∀ᵐ z ∂μ, ∀ r : ℝ, 1/(2:ℝ)^v ≤ r → r ≤ 1 → ∀ u : Space d, ‖u‖ = 1 →
        ν {x | (z,x) ∈ G ∧ dist (normalize (x-z)) u < r} ≤
          ENNReal.ofReal (((2:ℝ)^N)^η*r^q)) →
      ∃ H : Set (Space d × Space d), MeasurableSet H ∧ H ⊆ G ∧
        (μ.prod ν) (G \ H) ≤ ENNReal.ofReal (((2:ℝ)^N)^(-(2*η))) ∧
        ∀ p ∈ H, radialCollisionMass μ (C/(2:ℝ)^v) p ≤
          ENNReal.ofReal (((2:ℝ)^N)^(10*η)*((2:ℝ)^(v-g))^(-q)) := by
  have hD0 : 0 < D := zero_lt_one.trans_le hD
  let a : ℝ := 1/(2*D)
  have ha : 0 < a := by dsimp [a]; positivity
  have ha1 : a ≤ 1 := by dsimp [a]; apply (div_le_one (by positivity)).mpr; linarith
  have haD : a*D = 1/2 := by dsimp [a]; field_simp
  let e := radialZoom a ha.ne' (0 : Space d)
  obtain ⟨J,N₁,hN₁⟩ := outer_radial_interval_fixed_width (d := d)
    (by norm_num : (1:ℝ) ≤ 1) (mul_pos (by norm_num : (0:ℝ) < 2) hη₀) hq C
  obtain ⟨N₂,hN₂⟩ := Regularization.fixed_constant_absorbed hη₀ (a^(-q))
  refine ⟨J,max N₁ N₂,?_⟩
  intro N hN η hη g v hgv hvN μ ν _ _ G hG hdiag hgeom hball hcap
  let R : ℝ := (2:ℝ)^N
  have hR : 0 < R := by dsimp [R]; positivity
  have hR1 : 1 ≤ R := one_le_pow₀ (by norm_num)
  have hη0 : 0 < η := hη₀.trans_le hη
  have hK : 1 ≤ R^η := Real.one_le_rpow hR1 hη0.le
  have hcoeff : a^(-q) ≤ R^η :=
    (hN₂ N ((le_max_right _ _).trans hN)).trans
      (Real.rpow_le_rpow_of_exponent_le hR1 hη)
  have hcoeff' : R^η*a^(-q) ≤ R^(2*η) := by
    calc
      _ ≤ R^η*R^η := mul_le_mul_of_nonneg_left hcoeff (by positivity)
      _ = _ := by rw [← Real.rpow_add hR]; congr 1; ring
  have hballs := radialZoom_scaled_ball_bound μ ha ha1 hK
    (by positivity : 0 < (2:ℝ)^g) hq (by simp) (0 : Space d) hball
  have hdata : ∀ᵐ z ∂Measure.map e μ,
      (∀ᵐ y ∂Measure.map e μ, ‖y-z‖ < 1/(2:ℝ)^g ∧
        ∀ x, (z,x) ∈ zoomPairSet e G → ‖y-x‖ ≤ 1) ∧
      (∀ j : ℕ, j ≤ v → Measure.map e μ {y | ‖y-z‖ < 1/(2:ℝ)^j} ≤
        ENNReal.ofReal ((R^(2*η)*((2:ℝ)^g)^q)*(1/(2:ℝ)^j)^q)) ∧
      (∀ r : ℝ, 1/(2:ℝ)^v ≤ r → r ≤ 1 → ∀ u : Space d, ‖u‖ = 1 →
        Measure.map e ν {x | (z,x) ∈ zoomPairSet e G ∧ dist (normalize (x-z)) u < r} ≤
          ENNReal.ofReal (R^(2*η)*r^q)) := by
    rw [radialZoom_ae_iff μ ha]
    filter_upwards [hgeom,hcap] with z hz hc
    refine ⟨?_,?_,?_⟩
    · rw [radialZoom_ae_iff μ ha]
      filter_upwards [hz] with y hy
      constructor
      · rw [norm_radialZoom_sub ha]
        calc
          _ ≤ a*(D/(2:ℝ)^g) := mul_le_mul_of_nonneg_left hy.1 ha.le
          _ = (1/2:ℝ)/(2:ℝ)^g := by rw [← mul_div_assoc,haD]
          _ < _ := div_lt_div_of_pos_right (by norm_num) (by positivity)
      · intro x hx
        let x₀ := e.symm x
        have hx' : (e.symm (e z),e.symm x) ∈ G := hx
        have hx₀ : (z,x₀) ∈ G := by simpa only [e.symm_apply_apply] using hx'
        have hxx : e x₀ = x := e.apply_symm_apply x
        rw [← hxx]
        change ‖radialZoom a ha.ne' 0 y-radialZoom a ha.ne' 0 x₀‖ ≤ _
        rw [norm_radialZoom_sub ha]
        exact (mul_le_mul_of_nonneg_left (hy.2 x₀ hx₀) ha.le).trans (by rw [haD]; norm_num)
    · intro j hj
      have hrj : 1/(2:ℝ)^v ≤ 1/(2:ℝ)^j :=
        one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) hj)
      have hb := hballs (e z) (1/(2:ℝ)^j) (by positivity) hrj
      change Measure.map e μ (Metric.ball (e z) (1/(2:ℝ)^j)) ≤ _
      apply hb.trans
      apply ENNReal.ofReal_le_ofReal
      rw [Real.mul_rpow (by positivity) (by positivity)]
      calc
        _ = (R^η*a^(-q))*(((2:ℝ)^g)^q*(1/(2:ℝ)^j)^q) := by ring
        _ ≤ R^(2*η)*(((2:ℝ)^g)^q*(1/(2:ℝ)^j)^q) :=
          mul_le_mul_of_nonneg_right hcoeff' (by positivity)
        _ = _ := by ring
    · intro r hr hr1 u hu
      rw [radialZoom_reverse_cap ν ha _ z u r G hG]
      apply (hc r hr hr1 u hu).trans
      apply ENNReal.ofReal_le_ofReal
      have hr0 : 0 ≤ r := (by positivity : (0:ℝ) ≤ 1/(2:ℝ)^v).trans hr
      exact mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_exponent_le hR1 (by linarith)) (Real.rpow_nonneg hr0 q)
  have hdiag' : ∀ z x, (z,x) ∈ zoomPairSet e G → x ≠ z := by
    intro z x hx heq
    have hh := hdiag (e.symm z) (e.symm x) hx
    exact hh (congrArg e.symm heq)
  haveI : IsProbabilityMeasure (Measure.map e μ) := Measure.isProbabilityMeasure_map e.measurable.aemeasurable
  haveI : IsProbabilityMeasure (Measure.map e ν) := Measure.isProbabilityMeasure_map e.measurable.aemeasurable
  obtain ⟨H,hH,hHG,hdel,hbound⟩ := hN₁ N ((le_max_left _ _).trans hN) (2*η)
    (by linarith) g v hgv hvN (Measure.map e μ) (Measure.map e ν) (zoomPairSet e G)
    (zoomPairSet_measurable e hG) hdiag' hdata
  have hbound' : ∀ p ∈ H, radialCollisionMass (Measure.map e μ) (C/(2:ℝ)^v) p ≤
      ENNReal.ofReal (R^(10*η)*((2:ℝ)^(v-g))^(-q)) := by
    intro p hp
    simpa only [show 5*(2*η) = 10*η by ring] using hbound p hp
  exact radial_pruning_unzoom μ ν ha 0 G hG H hH hHG _ _ _ hdel hbound'

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_SourceClassOuterRadial
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Outer-interval pruning for the actual regularized conditional source laws -/

namespace Falconer.Regularization
open Set MeasureTheory NormedSpace
open scoped ENNReal
variable {d : ℕ}

theorem source_class_outer_radial_pruning (Q : DyadicCube d) (hQ : Q.side = 1)
    {D η₀ q : ℝ} (hD : 1 ≤ D) (hDdim : Real.sqrt d ≤ D)
    (hη₀ : 0 < η₀) (hq : 0 ≤ q) (C : ℝ) :
    ∃ J N₀ : ℕ, ∀ N ≥ N₀, ∀ η : ℝ, η₀ ≤ η →
      ∀ g v : ℕ, g+J ≤ v → v ≤ N →
      ∀ (μ ν : Measure (Space d)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν],
      ∀ B : ℕ, 0 < N → 0 < B → ∀ lam E : ℝ,
      (B:ℝ) ≤ lam*(N:ℝ) → (2:ℝ)^(N/B+2) ≤ ((2:ℝ)^N)^lam →
      ∀ p₀ ∈ regularizationLeaves Q μ N, ∀ P : CellPath d, P.length = g →
      0 < sourceClass Q μ N B p₀ (Q.descendant P).carrier →
      (∀ n, g ≤ n → n ≤ v →
        q*(n-g:ℕ)/N-E ≤ sourceProfile Q μ N B p₀ n-sourceProfile Q μ N B p₀ g) →
      (((2*Nat.ceil (2+4*Real.sqrt d)+1)^d:ℕ):ℝ)*(2:ℝ)^q*
        ((2:ℝ)^N)^(E+2*((d:ℝ)+1)*lam) ≤ ((2:ℝ)^N)^η →
      ∀ G : Set (Space d × Space d), MeasurableSet G →
      (∀ z x, (z,x) ∈ G → x ≠ z) →
      (∀ z x, (z,x) ∈ G → ∀ y ∈ (Q.descendant P).carrier, ‖y-x‖ ≤ D) →
      (∀ᵐ z ∂ProbabilityTheory.cond (sourceClass Q μ N B p₀) (Q.descendant P).carrier,
        ∀ r : ℝ, 1/(2:ℝ)^v ≤ r → r ≤ 1 → ∀ u : Space d, ‖u‖ = 1 →
        ν {x | (z,x) ∈ G ∧ dist (normalize (x-z)) u < r} ≤
          ENNReal.ofReal (((2:ℝ)^N)^η*r^q)) →
      ∃ H : Set (Space d × Space d), MeasurableSet H ∧ H ⊆ G ∧
        ((ProbabilityTheory.cond (sourceClass Q μ N B p₀) (Q.descendant P).carrier).prod ν)
          (G \ H) ≤ ENNReal.ofReal (((2:ℝ)^N)^(-(2*η))) ∧
        ∀ p ∈ H, radialCollisionMass
          (ProbabilityTheory.cond (sourceClass Q μ N B p₀) (Q.descendant P).carrier)
          (C/(2:ℝ)^v) p ≤ ENNReal.ofReal (((2:ℝ)^N)^(10*η)*((2:ℝ)^(v-g))^(-q)) := by
  obtain ⟨J,N₀,hN₀⟩ := outer_radial_cell_pruning (d := d) hD hη₀ hq C
  refine ⟨J,N₀,?_⟩
  intro N hN η hη g v hgv hvN μ ν _ _ B hNp hB lam E hwidth hlarge
    p₀ hp₀ P hP hpos hinc hcoef G hG hdiag hpin hcap
  have hside : 0 < Q.side := by rw [hQ]; norm_num
  have : IsProbabilityMeasure (ProbabilityTheory.cond (sourceClass Q μ N B p₀)
      (Q.descendant P).carrier) := sourceClass_conditional_probability Q hside μ N B hp₀ P hpos
  exact hN₀ N hN η hη g v hgv hvN _ ν G hG hdiag
    (conditional_cell_pair_geometry Q hQ _ P hP hDdim G hpin)
    (sourceClass_original_conditional_frostman_power Q hQ μ hNp hB hq hwidth hlarge
      hp₀ (by omega) hvN hP hpos hinc hcoef) hcap

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_ProfileDerivativePoint
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # An interior profile derivative exceeds any smaller secant slope -/

namespace Falconer
open Set MeasureTheory
open scoped NNReal

theorem lipschitz_unit_interval_derivative_point {f : ℝ → ℝ} {K : ℝ≥0} {r : ℝ}
    (hf : LipschitzOnWith K f (Icc 0 1)) (hinc : r < f 1-f 0) :
    ∃ A ∈ Ioo 0 1, ∃ l : ℝ, HasDerivAt f l A ∧ r < l := by
  have hfu : LipschitzOnWith K f (uIcc 0 1) := by
    simpa only [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] using hf
  have hac : AbsolutelyContinuousOnInterval f 0 1 := hfu.absolutelyContinuousOnInterval
  by_contra hn
  push Not at hn
  have hbound : (fun x => deriv f x) ≤ᵐ[volume.restrict (Icc 0 1)] fun _ => r := by
    change ∀ᵐ x ∂volume.restrict (Icc (0:ℝ) 1), deriv f x ≤ r
    rw [ae_restrict_iff' measurableSet_Icc]
    filter_upwards [hac.ae_differentiableAt,volume.ae_ne (0:ℝ),volume.ae_ne (1:ℝ)] with x hd hx0 hx1 hx
    have hi : x ∈ Ioo (0:ℝ) 1 := ⟨lt_of_le_of_ne hx.1 (Ne.symm hx0),lt_of_le_of_ne hx.2 hx1⟩
    have hdx : DifferentiableAt ℝ f x := hd (by simpa only [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] using hx)
    exact hn x hi (deriv f x) hdx.hasDerivAt
  have hh := intervalIntegral.integral_mono_ae_restrict (by norm_num : (0:ℝ) ≤ 1)
    hac.intervalIntegrable_deriv (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => r) volume 0 1) hbound
  rw [hac.integral_deriv_eq_sub,intervalIntegral.integral_const] at hh
  norm_num at hh
  linarith

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_ProfileSuffixMinimum
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The future minimum of a scale profile on the unit interval -/

namespace Falconer
open Set
open scoped NNReal

theorem profileSuffixMinimum_attained {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc 0 1)) {u : ℝ} (hu : u ∈ Icc 0 1) :
    ∃ v ∈ Icc u 1, profileSuffixMinimum f u = f v ∧
      ∀ w ∈ Icc u 1, f v ≤ f w := by
  obtain ⟨v,hv,hm⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hu.2)
    (hf.mono (Icc_subset_Icc hu.1 le_rfl))
  refine ⟨v,hv,?_,hm⟩
  exact (show IsLeast (f '' Icc u 1) (f v) from
    ⟨mem_image_of_mem f hv,by rintro _ ⟨w,hw,rfl⟩; exact hm hw⟩).csInf_eq

theorem profileSuffixMinimum_le {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc 0 1)) {u w : ℝ} (hu : u ∈ Icc 0 1)
    (hw : w ∈ Icc u 1) : profileSuffixMinimum f u ≤ f w := by
  obtain ⟨v,_,he,hm⟩ := profileSuffixMinimum_attained hf hu
  rw [he]
  exact hm w hw

theorem profileSuffixMinimum_monotone {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc 0 1)) : MonotoneOn (profileSuffixMinimum f) (Icc 0 1) := by
  intro u hu v hv huv
  obtain ⟨w,hw,he,_⟩ := profileSuffixMinimum_attained hf hv
  rw [he]
  exact profileSuffixMinimum_le hf hu ⟨huv.trans hw.1,hw.2⟩

theorem profileSuffixMinimum_lipschitz {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : LipschitzOnWith K f (Icc 0 1)) :
    LipschitzOnWith K (profileSuffixMinimum f) (Icc 0 1) := by
  have hc := hf.continuousOn
  have hmono := profileSuffixMinimum_monotone hc
  have hstep {u v : ℝ} (hu : u ∈ Icc 0 1) (hv : v ∈ Icc 0 1) (huv : u ≤ v) :
      profileSuffixMinimum f v-profileSuffixMinimum f u ≤ K*(v-u) := by
    obtain ⟨w,hw,he,hm⟩ := profileSuffixMinimum_attained hc hu
    by_cases hwv : v ≤ w
    · have hle := profileSuffixMinimum_le hc hv ⟨hwv,hw.2⟩
      rw [he]
      nlinarith [mul_nonneg K.coe_nonneg (sub_nonneg.mpr huv)]
    · have hwv' : w ≤ v := (lt_of_not_ge hwv).le
      have hle := profileSuffixMinimum_le hc hv ⟨le_rfl,hv.2⟩
      have hd := hf.dist_le_mul w ⟨hu.1.trans hw.1,hw.2⟩ v hv
      rw [Real.dist_eq,Real.dist_eq,abs_of_nonpos (sub_nonpos.mpr hwv')] at hd
      have hfv : f v-f w ≤ K*(v-w) := by
        linarith [le_abs_self (f w-f v),neg_le_abs (f w-f v)]
      rw [he]
      nlinarith [mul_nonneg K.coe_nonneg (sub_nonneg.mpr hw.1)]
  apply LipschitzOnWith.of_dist_le_mul
  intro u hu v hv
  rcases le_total u v with huv | hvu
  · rw [Real.dist_eq,Real.dist_eq,abs_of_nonpos (sub_nonpos.mpr (hmono hu hv huv)),
      abs_of_nonpos (sub_nonpos.mpr huv)]
    simpa only [neg_sub] using hstep hu hv huv
  · rw [Real.dist_eq,Real.dist_eq,abs_of_nonneg (sub_nonneg.mpr (hmono hv hu hvu)),
      abs_of_nonneg (sub_nonneg.mpr hvu)]
    exact hstep hv hu hvu

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_ProfileSuffixContact
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Positive slopes of the future minimum occur at contact points -/

namespace Falconer
open Set Filter
open scoped Topology

theorem profileSuffixMinimum_locally_constant_of_gap {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc 0 1)) {A : ℝ} (hA : A ∈ Ioo 0 1)
    (hgap : profileSuffixMinimum f A < f A) :
    profileSuffixMinimum f =ᶠ[𝓝 A] fun _ => profileSuffixMinimum f A := by
  obtain ⟨w,hw,he,_⟩ := profileSuffixMinimum_attained hf ⟨hA.1.le,hA.2.le⟩
  have hAw : A < w := by
    by_contra hn
    have heq : w = A := le_antisymm (le_of_not_gt hn) hw.1
    rw [heq] at he
    linarith
  have hcA : ContinuousAt f A := hf.continuousAt (Icc_mem_nhds hA.1 hA.2)
  obtain ⟨η,hη,hclose⟩ := Metric.continuousAt_iff.mp hcA
    ((f A-profileSuffixMinimum f A)/2) (by linarith)
  have hnear : ∀ᶠ u in 𝓝 A, u ∈ Ioo 0 w ∧ dist u A < η := by
    filter_upwards [Ioo_mem_nhds hA.1 hAw,Metric.ball_mem_nhds A hη] with u hu hb
    exact ⟨hu,hb⟩
  filter_upwards [hnear] with u hu
  have huI : u ∈ Icc 0 1 := ⟨hu.1.1.le,(hu.1.2.le.trans hw.2)⟩
  apply le_antisymm
  · rw [he]
    exact profileSuffixMinimum_le hf huI ⟨hu.1.2.le,hw.2⟩
  · obtain ⟨z,hz,hez,_⟩ := profileSuffixMinimum_attained hf huI
    rw [hez]
    by_cases hAz : A ≤ z
    · exact profileSuffixMinimum_le hf ⟨hA.1.le,hA.2.le⟩ ⟨hAz,hz.2⟩
    · have hzA : z < A := lt_of_not_ge hAz
      have hd : dist z A < η := by
        rw [Real.dist_eq,abs_of_neg (sub_neg.mpr hzA)]
        have huabs : |u-A| < η := by simpa only [Real.dist_eq] using hu.2
        have hh' := (neg_le_abs (u-A)).trans_lt huabs
        linarith [hz.1]
      have hc := hclose hd
      rw [Real.dist_eq] at hc
      have hh := (neg_le_abs (f z-f A)).trans_lt hc
      linarith

theorem profileSuffixMinimum_contact_of_pos_deriv {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc 0 1)) {A l : ℝ} (hA : A ∈ Ioo 0 1)
    (hd : HasDerivAt (profileSuffixMinimum f) l A) (hl : 0 < l) :
    profileSuffixMinimum f A = f A := by
  have hle := profileSuffixMinimum_le hf ⟨hA.1.le,hA.2.le⟩ ⟨le_rfl,hA.2.le⟩
  apply le_antisymm hle
  by_contra hn
  have he := profileSuffixMinimum_locally_constant_of_gap hf hA (lt_of_not_ge hn)
  have hz : HasDerivAt (profileSuffixMinimum f) 0 A :=
    (hasDerivAt_const A (profileSuffixMinimum f A)).congr_of_eventuallyEq he
  have hh := hd.unique hz
  linarith

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_ProfileRightContact
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Right contact points of a profile's future minimum -/

namespace Falconer
open Set Filter
open scoped Topology NNReal

theorem hasDerivAt_right_secant_lower {f : ℝ → ℝ} {A l r : ℝ}
    (hd : HasDerivAt f l A) (hr : r < l) :
    ∃ η > 0, ∀ w, A < w → w < A+η → r*(w-A) < f w-f A := by
  have he : ∀ᶠ w in 𝓝[>] A, r < slope f A w :=
    (hd.tendsto_slope.mono_left (nhdsGT_le_nhdsNE A)).eventually (eventually_gt_nhds hr)
  obtain ⟨η,hη,heη⟩ := Metric.eventually_nhds_iff_ball.mp
    (eventually_nhdsWithin_iff.mp he)
  refine ⟨η,hη,fun w hw hwd => ?_⟩
  have hs := heη w (by
    change dist w A < η
    rw [Real.dist_eq,abs_of_pos (sub_pos.mpr hw)]
    linarith) hw
  rw [slope_def_field] at hs
  exact (lt_div_iff₀ (sub_pos.mpr hw)).mp hs

theorem profileSuffixMinimum_right_contact {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : LipschitzOnWith K f (Icc 0 1)) {A l T : ℝ}
    (hA : A ∈ Ioo 0 1) (hd : HasDerivAt (profileSuffixMinimum f) l A)
    (hl : 0 < l) (hAT : A < T) (hT : T ≤ 1) :
    ∃ B, A < B ∧ B < T ∧ profileSuffixMinimum f B = f B := by
  let F := profileSuffixMinimum f
  have hFL := profileSuffixMinimum_lipschitz hf
  have hc := hf.continuousOn
  have hmono := profileSuffixMinimum_monotone hc
  obtain ⟨η,hη,hgrowth⟩ := hasDerivAt_right_secant_lower hd hl
  let y := A+min η (T-A)/2
  have hmin : 0 < min η (T-A) := lt_min hη (sub_pos.mpr hAT)
  have hAy : A < y := by dsimp [y]; linarith
  have hyT : y < T := by dsimp [y]; linarith [min_le_right η (T-A)]
  have hyη : y < A+η := by dsimp [y]; linarith [min_le_left η (T-A)]
  have hyI : y ∈ Icc (0:ℝ) 1 := ⟨hA.1.le.trans hAy.le,hyT.le.trans hT⟩
  have hFy : F A < F y := by
    have hh := hgrowth y hAy hyη
    dsimp [F]
    linarith
  let v := (F A+F y)/2
  have hv : v ∈ Icc (F A) (F y) := by dsimp [v]; constructor <;> linarith
  obtain ⟨u,hu,heu⟩ := intermediate_value_Icc hAy.le
    (hFL.continuousOn.mono (Icc_subset_Icc hA.1.le hyI.2)) hv
  have hAu : A < u := by
    by_contra hn
    have heq : u = A := le_antisymm (le_of_not_gt hn) hu.1
    rw [heq] at heu
    change F A = v at heu
    dsimp [v] at heu
    linarith
  have hFu : F u < F y := by
    change F u = v at heu
    dsimp [v] at heu
    linarith
  have huI : u ∈ Icc (0:ℝ) 1 := ⟨hA.1.le.trans hu.1,hu.2.trans hyI.2⟩
  obtain ⟨B,hB,heB,_⟩ := profileSuffixMinimum_attained hc huI
  have huB : u ≤ B := hB.1
  have hBI : B ∈ Icc (0:ℝ) 1 := ⟨huI.1.trans huB,hB.2⟩
  have hBy : B < y := by
    by_contra hn
    have hh := profileSuffixMinimum_le hc hyI ⟨le_of_not_gt hn,hB.2⟩
    change F u = f B at heB
    linarith
  refine ⟨B,hAu.trans_le huB,hBy.trans hyT,?_⟩
  apply le_antisymm (profileSuffixMinimum_le hc hBI ⟨le_rfl,hB.2⟩)
  rw [← heB]
  exact hmono huI hBI huB

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_ProfileContactInterval
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The three contact intervals used by radial improvement

This proves Lemma `prep:contact` of the supplied manuscript. The proof only
needs the Lipschitz and lower-profile hypotheses; monotonicity is not needed.
-/

namespace Falconer
open Set
open scoped NNReal

theorem profile_sub_linear_lipschitz {m : ℝ → ℝ} {K : ℝ≥0}
    (hm : LipschitzOnWith K m (Icc 0 1)) (q : ℝ) :
    LipschitzOnWith (Real.toNNReal ((K:ℝ)+|q|)) (fun u => m u-q*u) (Icc 0 1) := by
  apply LipschitzOnWith.of_dist_le'
  intro x hx y hy
  rw [Real.dist_eq,Real.dist_eq]
  calc
    |(m x-q*x)-(m y-q*y)| = |(m x-m y)-q*(x-y)| := by congr 1; ring
    _ ≤ |m x-m y|+|q*(x-y)| := abs_sub _ _
    _ ≤ (K:ℝ)*|x-y|+|q| *|x-y| := by
      rw [abs_mul]
      exact add_le_add (by simpa only [Real.dist_eq] using hm.dist_le_mul x hx y hy) le_rfl
    _ = ((K:ℝ)+|q|)*|x-y| := by ring

theorem profile_contact_interval {m : ℝ → ℝ} {K : ℝ≥0} {q t s : ℝ}
    (hm : LipschitzOnWith K m (Icc 0 1)) (hzero : m 0 = 0)
    (hlower : ∀ u ∈ Icc (0:ℝ) 1, s*u ≤ m u) (hqt : q < t) (hts : t < s) :
    ∃ A B : ℝ, 0 < A ∧ A < B ∧ B < 1 ∧ B < 2*A ∧
      (∀ w ∈ Icc 0 A, q*w ≤ m w) ∧
      (∀ w ∈ Icc A B, t*(w-A) ≤ m w-m A) ∧
      (∀ w ∈ Icc B 1, q*(w-B) ≤ m w-m B) := by
  let g := fun u => m u-q*u
  let F := profileSuffixMinimum g
  have hg := profile_sub_linear_lipschitz hm q
  have hgc := hg.continuousOn
  have hFL := profileSuffixMinimum_lipschitz hg
  have hF0 : F 0 = 0 := by
    apply le_antisymm
    · simpa [F,g,hzero] using profileSuffixMinimum_le hgc
        (show (0:ℝ) ∈ Icc 0 1 by constructor <;> norm_num)
        (show (0:ℝ) ∈ Icc 0 1 by constructor <;> norm_num)
    · obtain ⟨z,hz,he,_⟩ := profileSuffixMinimum_attained hgc
        (show (0:ℝ) ∈ Icc 0 1 by constructor <;> norm_num)
      change 0 ≤ profileSuffixMinimum g 0
      rw [he]
      have hh := hlower z hz
      have hp := mul_nonneg (sub_nonneg.mpr (hqt.trans hts).le) hz.1
      change 0 ≤ m z-q*z
      nlinarith
  have hF1 : F 1 = m 1-q := by
    obtain ⟨z,hz,he,_⟩ := profileSuffixMinimum_attained hgc
      (show (1:ℝ) ∈ Icc 0 1 by constructor <;> norm_num)
    have hz1 : z = 1 := le_antisymm hz.2 hz.1
    simpa [F,g,hz1] using he
  have hinc : t-q < F 1-F 0 := by
    rw [hF0,hF1]
    have hh := hlower 1 (by constructor <;> norm_num)
    linarith
  obtain ⟨A,hA,l,hd,hl⟩ := lipschitz_unit_interval_derivative_point hFL hinc
  have hl0 : 0 < l := (sub_pos.mpr hqt).trans hl
  have hcontactA : F A = g A := profileSuffixMinimum_contact_of_pos_deriv hgc hA hd hl0
  obtain ⟨η,hη,hsec⟩ := hasDerivAt_right_secant_lower hd hl
  let T := min (2*A) (min 1 (A+η))
  have hAT : A < T := by
    dsimp [T]
    exact lt_min (by linarith [hA.1]) (lt_min hA.2 (by linarith))
  have hT1 : T ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  obtain ⟨B,hAB,hBT,hcontactB⟩ := profileSuffixMinimum_right_contact hg hA hd hl0 hAT hT1
  have hB1 : B < 1 := hBT.trans_le hT1
  have hB2 : B < 2*A := hBT.trans_le (min_le_left _ _)
  have hBη : B < A+η := hBT.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨A,B,hA.1,hAB,hB1,hB2,?_,?_,?_⟩
  · intro w hw
    have hwI : w ∈ Icc (0:ℝ) 1 := ⟨hw.1,hw.2.trans hA.2.le⟩
    have hp := mul_nonneg (sub_nonneg.mpr (hqt.trans hts).le) hw.1
    nlinarith [hlower w hwI]
  · intro w hw
    by_cases he : w = A
    · subst w
      simp
    have hAw : A < w := lt_of_le_of_ne hw.1 (Ne.symm he)
    have hh := hsec w hAw (hw.2.trans_lt hBη)
    have hwI : w ∈ Icc (0:ℝ) 1 := ⟨hA.1.le.trans hw.1,hw.2.trans hB1.le⟩
    have hFw := profileSuffixMinimum_le hgc hwI ⟨le_rfl,hwI.2⟩
    change F w ≤ g w at hFw
    change (t-q)*(w-A) < F w-F A at hh
    rw [hcontactA] at hh
    dsimp [g] at hh hFw
    linarith
  · intro w hw
    have hBI : B ∈ Icc (0:ℝ) 1 := ⟨(hA.1.trans hAB).le,hB1.le⟩
    have hh := profileSuffixMinimum_le hgc hBI hw
    rw [hcontactB] at hh
    linarith

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_ProfileCompactness
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.PlanarFalconer.unitCircle_compactSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Compactness of normalized Lipschitz scale profiles -/

namespace Falconer
open Set Metric Filter BoundedContinuousFunction
open scoped Topology NNReal

theorem normalizedLipschitzProfiles_closed (K : ℝ≥0) :
    IsClosed (normalizedLipschitzProfiles K) := by
  have hzero : IsClosed {f : BoundedProfile | f ⟨0,by constructor <;> norm_num⟩ = 0} :=
    isClosed_eq (continuous_eval_const _) continuous_const
  have hlip : IsClosed {f : BoundedProfile | LipschitzWith K f} := by
    have he : {f : BoundedProfile | LipschitzWith K f} =
        ⋂ x : ProfileDomain, ⋂ y : ProfileDomain,
          {f : BoundedProfile | dist (f x) (f y) ≤ (K:ℝ)*dist x y} := by
      ext f
      simp only [mem_ofPred_eq,mem_iInter]
      exact ⟨fun h x y => h.dist_le_mul x y,fun h => LipschitzWith.of_dist_le_mul h⟩
    rw [he]
    exact isClosed_iInter fun x => isClosed_iInter fun y =>
      isClosed_le ((continuous_eval_const x).dist (continuous_eval_const y)) continuous_const
  exact hzero.inter hlip

theorem normalizedLipschitzProfiles_compact (K : ℝ≥0) :
    IsCompact (normalizedLipschitzProfiles K) := by
  apply arzela_ascoli₂ (Icc (-(K:ℝ)) K) isCompact_Icc _
    (normalizedLipschitzProfiles_closed K)
  · intro f x hf
    have hh := hf.2.dist_le_mul x ⟨0,by constructor <;> norm_num⟩
    rw [hf.1,Real.dist_eq,sub_zero] at hh
    have hx : dist x (⟨0,by constructor <;> norm_num⟩ : ProfileDomain) ≤ 1 := by
      change dist (x:ℝ) 0 ≤ 1
      simpa only [Real.dist_eq,sub_zero,abs_of_nonneg x.property.1] using x.property.2
    have hb : |f x| ≤ (K:ℝ) := hh.trans (by simpa using mul_le_mul_of_nonneg_left hx K.coe_nonneg)
    exact abs_le.mp hb
  · apply Metric.equicontinuous_of_continuity_modulus (fun r => (K:ℝ)*r)
      (by simpa only [mul_zero] using
        (tendsto_const_nhds.mul tendsto_id : Tendsto (fun r : ℝ => (K:ℝ)*r) (𝓝 0) (𝓝 ((K:ℝ)*0))))
    intro x y f
    exact f.property.2.dist_le_mul x y

theorem normalized_profile_subsequence {K : ℝ≥0} (f : ℕ → BoundedProfile)
    (hf : ∀ n, f n ∈ normalizedLipschitzProfiles K) :
    ∃ m ∈ normalizedLipschitzProfiles K, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ u : ProfileDomain, |f (φ n) u-m u| < ε := by
  obtain ⟨m,hm,φ,hφ,hlim⟩ := (normalizedLipschitzProfiles_compact K).tendsto_subseq hf
  refine ⟨m,hm,φ,hφ,fun ε hε => ?_⟩
  have he : ∀ᶠ n in atTop, dist (f (φ n)) m < ε :=
    (tendsto_iff_dist_tendsto_zero.mp hlim).eventually (eventually_lt_nhds hε)
  obtain ⟨N,hN⟩ := eventually_atTop.mp he
  refine ⟨N,fun n hn u => ?_⟩
  exact (show |f (φ n) u-m u| ≤ dist (f (φ n)) m from by simpa only [Real.dist_eq] using
      (dist_coe_le_dist (f := f (φ n)) (g := m) u)).trans_lt (hN n hn)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_ProfileUniformLimit
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform limits of the actual real-variable profiles -/

namespace Falconer
open Set Filter Metric BoundedContinuousFunction
open scoped Topology NNReal

theorem normalized_real_profile_subsequence {K : ℝ≥0} (f : ℕ → ℝ → ℝ)
    (hLip : ∀ n, LipschitzOnWith K (f n) (Icc 0 1)) (hzero : ∀ n, f n 0 = 0) :
    ∃ m : ℝ → ℝ, LipschitzOnWith K m (Icc 0 1) ∧ m 0 = 0 ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ u ∈ Icc (0:ℝ) 1, |f (φ n) u-m u| < ε := by
  let F : ℕ → BoundedProfile := fun n => boundedProfileOfReal (f n) (hLip n).continuousOn
  have hF : ∀ n, F n ∈ normalizedLipschitzProfiles K := by
    intro n
    refine ⟨hzero n,LipschitzWith.of_dist_le_mul ?_⟩
    intro u v
    exact (hLip n).dist_le_mul u u.property v v.property
  obtain ⟨m,hm,φ,hφ,hlim⟩ := normalized_profile_subsequence F hF
  refine ⟨profileOfBounded m,?_,?_,φ,hφ,?_⟩
  · apply LipschitzOnWith.of_dist_le_mul
    intro u hu v hv
    have hh := hm.2.dist_le_mul (profileClamp u) (profileClamp v)
    simpa only [profileOfBounded,Subtype.dist_eq,profileClamp_val hu,profileClamp_val hv] using hh
  · have he : profileClamp 0 = (⟨0,by constructor <;> norm_num⟩ : ProfileDomain) := by
      apply Subtype.ext
      exact profileClamp_val (by constructor <;> norm_num)
    simpa only [profileOfBounded,he] using hm.1
  · intro ε hε
    obtain ⟨N,hN⟩ := hlim ε hε
    refine ⟨N,fun n hn u hu => ?_⟩
    have hh := hN n hn (profileClamp u)
    change |f (φ n) (profileClamp u)-m (profileClamp u)| < ε at hh
    simpa only [profileOfBounded,profileClamp_val hu] using hh

theorem uniform_profile_limit_lower {f : ℕ → ℝ → ℝ} {m : ℝ → ℝ}
    {φ : ℕ → ℕ} {e : ℕ → ℝ} {s : ℝ} (hφ : StrictMono φ)
    (he : Tendsto e atTop (𝓝 0))
    (hlower : ∀ n, ∀ u ∈ Icc (0:ℝ) 1, s*u-e n ≤ f n u)
    (hlim : ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ u ∈ Icc (0:ℝ) 1,
      |f (φ n) u-m u| < ε) :
    ∀ u ∈ Icc (0:ℝ) 1, s*u ≤ m u := by
  intro u hu
  have hf : Tendsto (fun n => f (φ n) u) atTop (𝓝 (m u)) := by
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    obtain ⟨N,hN⟩ := hlim ε hε
    exact ⟨N,fun n hn => hN n hn u hu⟩
  have hsum := hf.add (he.comp hφ.tendsto_atTop)
  simp only [add_zero] at hsum
  apply ge_of_tendsto hsum
  exact Filter.Eventually.of_forall fun n => by
    change s*u ≤ f (φ n) u+e (φ n)
    linarith [hlower (φ n) u hu]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_ProfileContactStability
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Fixed contact intervals for profiles with vanishing comparison losses -/

namespace Falconer
open Set Filter
open scoped Topology NNReal

theorem profile_sequence_contact {K : ℝ≥0} (f : ℕ → ℝ → ℝ)
    (hLip : ∀ n, LipschitzOnWith K (f n) (Icc 0 1)) (hzero : ∀ n, f n 0 = 0)
    {e : ℕ → ℝ} (he : Tendsto e atTop (𝓝 0)) {q t s : ℝ}
    (hlower : ∀ n, ∀ u ∈ Icc (0:ℝ) 1, s*u-e n ≤ f n u)
    (hqt : q < t) (hts : t < s) :
    ∃ A B : ℝ, ∃ φ : ℕ → ℕ,
      0 < A ∧ A < B ∧ B < 1 ∧ B < 2*A ∧ StrictMono φ ∧
      ∀ η > 0, ∃ N : ℕ, ∀ n ≥ N,
        (∀ w ∈ Icc 0 A, q*w-η ≤ f (φ n) w) ∧
        (∀ w ∈ Icc A B, t*(w-A)-η ≤ f (φ n) w-f (φ n) A) ∧
        (∀ w ∈ Icc B 1, q*(w-B)-η ≤ f (φ n) w-f (φ n) B) := by
  obtain ⟨m,hm,hm0,φ,hφ,hlim⟩ := normalized_real_profile_subsequence f hLip hzero
  have hmlower := uniform_profile_limit_lower hφ he hlower hlim
  obtain ⟨A,B,hA,hAB,hB,hBA,hfirst,hmiddle,hlast⟩ :=
    profile_contact_interval hm hm0 hmlower hqt hts
  refine ⟨A,B,φ,hA,hAB,hB,hBA,hφ,fun η hη => ?_⟩
  obtain ⟨N,hN⟩ := hlim (η/2) (by linarith)
  refine ⟨N,fun n hn => ⟨?_,?_,?_⟩⟩
  · intro w hw
    have hwI : w ∈ Icc (0:ℝ) 1 := ⟨hw.1,hw.2.trans (hAB.trans hB).le⟩
    have hc := (abs_lt.mp (hN n hn w hwI)).1
    linarith [hfirst w hw]
  · intro w hw
    have hwI : w ∈ Icc (0:ℝ) 1 := ⟨hA.le.trans hw.1,hw.2.trans hB.le⟩
    have hc := (abs_lt.mp (hN n hn w hwI)).1
    have hca := (abs_lt.mp (hN n hn A ⟨hA.le,(hAB.trans hB).le⟩)).2
    linarith [hmiddle w hw]
  · intro w hw
    have hwI : w ∈ Icc (0:ℝ) 1 := ⟨(hA.trans hAB).le.trans hw.1,hw.2⟩
    have hc := (abs_lt.mp (hN n hn w hwI)).1
    have hcb := (abs_lt.mp (hN n hn B ⟨(hA.trans hAB).le,hB.le⟩)).2
    linarith [hlast w hw]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_ProfileRoundContact
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Contact intervals tolerate the rounding of their initial dyadic depth -/

namespace Falconer
open Set Filter
open scoped NNReal Topology

theorem profile_contact_move_left {f : ℝ → ℝ} {K : ℝ≥0}
    (hLip : LipschitzOnWith K f (Icc 0 1)) {a A B s E ε : ℝ}
    (ha : 0 ≤ a) (haA : a ≤ A) (hAB : A ≤ B) (hB : B ≤ 1)
    (hs : 0 ≤ s) (hclose : A-a ≤ ε)
    (hcontact : ∀ w ∈ Icc A B, s*(w-A)-E ≤ f w-f A) :
    ∀ w ∈ Icc a B, s*(w-a)-E-((K:ℝ)+s)*ε ≤ f w-f a := by
  have hA0 : 0 ≤ A := ha.trans haA
  have ha1 : a ≤ 1 := (haA.trans hAB).trans hB
  have hA1 : A ≤ 1 := hAB.trans hB
  have hfa : |f A-f a| ≤ (K:ℝ)*(A-a) := by
    simpa only [Real.dist_eq,abs_of_nonneg (sub_nonneg.mpr haA)] using
      hLip.dist_le_mul A ⟨hA0,hA1⟩ a ⟨ha,ha1⟩
  have hK := K.coe_nonneg
  intro w hw
  by_cases hAw : A ≤ w
  · have hh := hcontact w ⟨hAw,hw.2⟩
    have he := mul_le_mul_of_nonneg_left hclose (add_nonneg hK hs)
    nlinarith [neg_abs_le (f A-f a)]
  · have hwA : w ≤ A := (lt_of_not_ge hAw).le
    have hw1 : w ≤ 1 := hw.2.trans hB
    have hfw : |f w-f a| ≤ (K:ℝ)*(w-a) := by
      simpa only [Real.dist_eq,abs_of_nonneg (sub_nonneg.mpr hw.1)] using
        hLip.dist_le_mul w ⟨ha.trans hw.1,hw1⟩ a ⟨ha,ha1⟩
    have hE : 0 ≤ E := by
      have hh := hcontact A ⟨le_rfl,hAB⟩
      simp only [sub_self,mul_zero,zero_sub] at hh
      linarith
    have hwe : w-a ≤ ε := (sub_le_sub_right hwA a).trans hclose
    nlinarith [neg_abs_le (f w-f a),mul_le_mul_of_nonneg_left hwe (add_nonneg hK hs)]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_RoundedProfileContact
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The three contact inequalities at actual integer dyadic depths -/

namespace Falconer
open Set
open scoped NNReal

theorem floor_depth_ratio_bounds {A : ℝ} (hA : 0 ≤ A) {N : ℕ} (hN : 0 < N) :
    0 ≤ (Nat.floor (A*(N:ℝ)):ℝ)/(N:ℝ) ∧
    (Nat.floor (A*(N:ℝ)):ℝ)/(N:ℝ) ≤ A ∧
    A-(Nat.floor (A*(N:ℝ)):ℝ)/(N:ℝ) ≤ 1/(N:ℝ) := by
  have hNp : 0 < (N:ℝ) := by exact_mod_cast hN
  have hlo := Nat.floor_le (mul_nonneg hA hNp.le)
  have hhi := Nat.lt_floor_add_one (A*(N:ℝ))
  refine ⟨by positivity,(div_le_iff₀ hNp).mpr hlo,?_⟩
  apply (le_div_iff₀ hNp).mpr
  have he : (A-(Nat.floor (A*(N:ℝ)):ℝ)/(N:ℝ))*(N:ℝ) =
      A*(N:ℝ)-(Nat.floor (A*(N:ℝ)):ℝ) := by field_simp
  rw [he]
  linarith

theorem rounded_profile_contact {f : ℝ → ℝ} {K : ℝ≥0}
    (hLip : LipschitzOnWith K f (Icc 0 1)) {A B q t E : ℝ}
    (hA : 0 ≤ A) (hAB : A ≤ B) (hB : B ≤ 1) (hq : 0 ≤ q) (ht : 0 ≤ t)
    (hfirst : ∀ w ∈ Icc 0 A, q*w-E ≤ f w)
    (hmiddle : ∀ w ∈ Icc A B, t*(w-A)-E ≤ f w-f A)
    (hlast : ∀ w ∈ Icc B 1, q*(w-B)-E ≤ f w-f B)
    {N : ℕ} (hN : 0 < N) :
    let a := Nat.floor (A*(N:ℝ))
    let b := Nat.floor (B*(N:ℝ))
    (∀ j : ℕ, j ≤ a → q*(j:ℝ)/N-E ≤ f ((j:ℝ)/N)) ∧
    (∀ j : ℕ, a ≤ j → j ≤ b →
      t*(j-a:ℕ)/N-E-((K:ℝ)+t)/N ≤ f ((j:ℝ)/N)-f ((a:ℝ)/N)) ∧
    (∀ j : ℕ, b ≤ j → j ≤ N →
      q*(j-b:ℕ)/N-E-((K:ℝ)+q)/N ≤ f ((j:ℝ)/N)-f ((b:ℝ)/N)) := by
  dsimp only
  let a := Nat.floor (A*(N:ℝ))
  let b := Nat.floor (B*(N:ℝ))
  have ha := floor_depth_ratio_bounds hA hN
  have hb := floor_depth_ratio_bounds (hA.trans hAB) hN
  have hNp : 0 < (N:ℝ) := by exact_mod_cast hN
  have hma := profile_contact_move_left hLip ha.1 ha.2.1 hAB hB ht ha.2.2 hmiddle
  have hlb := profile_contact_move_left hLip hb.1 hb.2.1 hB (le_refl (1:ℝ)) hq hb.2.2 hlast
  refine ⟨?_,?_,?_⟩
  · intro j hj
    have hjA : (j:ℝ)/N ≤ A := (div_le_div_of_nonneg_right (by exact_mod_cast hj) hNp.le).trans ha.2.1
    simpa only [mul_div_assoc] using hfirst ((j:ℝ)/N) ⟨by positivity,hjA⟩
  · intro j haj hjb
    have hlo : (a:ℝ)/N ≤ (j:ℝ)/N := div_le_div_of_nonneg_right (by exact_mod_cast haj) hNp.le
    have hhi : (j:ℝ)/N ≤ B := (div_le_div_of_nonneg_right (by exact_mod_cast hjb) hNp.le).trans hb.2.1
    have hh := hma ((j:ℝ)/N) ⟨hlo,hhi⟩
    rw [Nat.cast_sub haj]
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    ring
  · intro j hbj hjN
    have hlo : (b:ℝ)/N ≤ (j:ℝ)/N := div_le_div_of_nonneg_right (by exact_mod_cast hbj) hNp.le
    have hhi : (j:ℝ)/N ≤ 1 := (div_le_one hNp).mpr (by exact_mod_cast hjN)
    have hh := hlb ((j:ℝ)/N) ⟨hlo,hhi⟩
    rw [Nat.cast_sub hbj]
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_RoundedContactWidth
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integer contact widths retain the real interval length up to one unit -/

namespace Falconer

theorem rounded_contact_width {A B : ℝ} (hA : 0 ≤ A) (hAB : A ≤ B) (N : ℕ) :
    let a := Nat.floor (A*(N:ℝ))
    let b := Nat.floor (B*(N:ℝ))
    (B-A)*(N:ℝ)-1 ≤ (b-a:ℕ) ∧ (b-a:ℕ) ≤ (B-A)*(N:ℝ)+1 := by
  have hB : 0 ≤ B := hA.trans hAB
  have hN : (0:ℝ) ≤ N := Nat.cast_nonneg N
  have hab := Nat.floor_mono (mul_le_mul_of_nonneg_right hAB hN)
  have haLo := Nat.floor_le (mul_nonneg hA hN)
  have hbLo := Nat.floor_le (mul_nonneg hB hN)
  have haHi := Nat.lt_floor_add_one (A*(N:ℝ))
  have hbHi := Nat.lt_floor_add_one (B*(N:ℝ))
  dsimp only
  rw [Nat.cast_sub hab]
  constructor <;> nlinarith

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_UniformFrostmanProfiles
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One regularization choice for all measures with the fixed Frostman bound -/

namespace Falconer.Regularization
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem uniform_frostman_profile_envelope (hd : 0 < d) (Q : DyadicCube d) (hQ : 0 < Q.side)
    {s C lam : ℝ} (hC : 0 ≤ C) (hlam : 0 < lam) :
    ∃ H N₀ : ℕ, 0 < H ∧
      (∀ N ≥ N₀, 0 < N ∧ 0 < N/H ∧ N/(N/H)+1 ≤ 2*H ∧
        ((N/H:ℕ):ℝ) ≤ lam*(N:ℝ) ∧ (2:ℝ)^(N/(N/H)+2) ≤ ((2:ℝ)^N)^lam) ∧
      ∀ N ≥ N₀, ∀ (μ : Measure (Space d)) [IsProbabilityMeasure μ],
      (∀ x : Space d, ∀ r > 0, μ (Metric.ball x r) ≤ ENNReal.ofReal (C*r^s)) →
      ∀ p ∈ regularizationLeaves Q μ N,
        regularizationLabel Q μ N (N/H) p ∈ regularizationIndex Q μ N (N/H)
          (ENNReal.ofReal (((2:ℝ)^N)^(-lam))) →
        ∀ j ≤ N, s*(j:ℝ)/(N:ℝ)-((d:ℝ)+3)*lam ≤ sourceProfile Q μ N (N/H) p j := by
  obtain ⟨H,N₁,hH,hscales⟩ := PlanarFalconer.exists_regularization_block_control hlam
  obtain ⟨N₂,hconst⟩ := fixed_constant_absorbed hlam (C*(2*Real.sqrt d*Q.side)^s)
  refine ⟨H,max N₁ N₂,hH,fun N hN => hscales N ((le_max_left _ _).trans hN),?_⟩
  intro N hN μ _ hball p hp hret j hj
  have hs := hscales N ((le_max_left _ _).trans hN)
  apply sourceProfile_frostman_lower Q hQ μ hs.1 hs.2.1 hs.2.2.2.1 hs.2.2.2.2 hp
    (retained_label_real_mass_lower Q μ hret) _ hj
  intro k hk P hP
  have hh := dyadic_cell_frostman_profile_bound hd Q hQ μ hC hball hs.1 P
  rw [hP] at hh
  exact hh.trans (mul_le_mul_of_nonneg_right (hconst N ((le_max_right _ _).trans hN)) (by positivity))

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_UniformProfileContact
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform contact intervals for almost Frostman regularization profiles -/

namespace Falconer
open Set Filter
open scoped NNReal Topology

theorem uniform_profile_contact (K : ℝ≥0) {q t s τ : ℝ}
    (hqt : q < t) (hts : t < s) (hτ : 0 < τ) :
    ∃ ε γ : ℝ, 0 < ε ∧ 0 < γ ∧ ∀ f : ℝ → ℝ,
      LipschitzOnWith K f (Icc 0 1) → f 0 = 0 →
      (∀ u ∈ Icc (0:ℝ) 1, s*u-ε ≤ f u) → RobustProfileContact f q t τ γ := by
  classical
  by_contra hno
  push Not at hno
  let e : ℕ → ℝ := fun n => 1/((n:ℝ)+1)
  have hepos (n : ℕ) : 0 < e n := by dsimp [e]; positivity
  have hc (n : ℕ) : ∃ f : ℝ → ℝ, LipschitzOnWith K f (Icc 0 1) ∧ f 0 = 0 ∧
      (∀ u ∈ Icc (0:ℝ) 1, s*u-e n ≤ f u) ∧ ¬RobustProfileContact f q t τ (e n) :=
    hno (e n) (e n) (hepos n) (hepos n)
  choose f hLip hzero hlower hfail using hc
  have he : Tendsto e atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨A,B,φ,hA,hAB,hB,hBA,hφ,hcontacts⟩ :=
    profile_sequence_contact f hLip hzero he hlower hqt hts
  have hgap : 0 < τ*(B-A) := mul_pos hτ (sub_pos.mpr hAB)
  obtain ⟨I₀,hI₀⟩ := hcontacts (τ*(B-A)) hgap
  have hem := he.comp hφ.tendsto_atTop
  have heA := hem.eventually (eventually_lt_nhds hA)
  have heAB := hem.eventually (eventually_lt_nhds (sub_pos.mpr hAB))
  have heB := hem.eventually (eventually_lt_nhds (sub_pos.mpr hB))
  have heBA := hem.eventually (eventually_lt_nhds (sub_pos.mpr hBA))
  obtain ⟨i,hi,hiA,hiAB,hiB,hiBA⟩ :=
    ((eventually_ge_atTop I₀).and (heA.and (heAB.and (heB.and heBA)))).exists
  simp only [Function.comp_apply] at hiA hiAB hiB hiBA
  apply hfail (φ i)
  obtain ⟨hfirst,hmiddle,hlast⟩ := hI₀ i hi
  exact ⟨A,B,hiA.le,by linarith,by linarith,by linarith,hfirst,hmiddle,hlast⟩

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_SourceClassContact
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform contact intervals for every retained regularized Frostman class -/

namespace Falconer.Regularization
open Set MeasureTheory Filter
open scoped Topology NNReal ENNReal
variable {d : ℕ}

theorem source_classes_uniform_contact (hd : 0 < d) (Q : DyadicCube d) (hQ : 0 < Q.side)
    {s q t τ C : ℝ}
    (hs : 0 ≤ s) (hqt : q < t) (hts : t < s) (hτ : 0 < τ) (hC : 0 ≤ C) :
    ∃ lam γ : ℝ, 0 < lam ∧ 0 < γ ∧ lam ≤ τ*γ ∧ ∃ H N₀ : ℕ, 0 < H ∧
      (∀ N ≥ N₀, 0 < N ∧ 0 < N/H ∧ N/(N/H)+1 ≤ 2*H ∧
        ((N/H:ℕ):ℝ) ≤ lam*(N:ℝ) ∧ (2:ℝ)^(N/(N/H)+2) ≤ ((2:ℝ)^N)^lam) ∧
      ∀ N ≥ N₀, ∀ (μ : Measure (Space d)) [IsProbabilityMeasure μ],
        (∀ x : Space d, ∀ r > 0, μ (Metric.ball x r) ≤ ENNReal.ofReal (C*r^s)) →
      ∀ p ∈ regularizationLeaves Q μ N,
        regularizationLabel Q μ N (N/H) p ∈ regularizationIndex Q μ N (N/H)
          (ENNReal.ofReal (((2:ℝ)^N)^(-lam))) →
        RobustProfileContact (sourceUnitProfile Q μ N (N/H) p) q t τ γ := by
  obtain ⟨ε,γ,hε,hγ,hcontact⟩ := uniform_profile_contact (d:ℝ≥0) hqt hts hτ
  let lam : ℝ := min (ε/(2*((d:ℝ)+3))) (τ*γ)
  have hlam : 0 < lam := by dsimp [lam]; positivity
  have hsmalllam : ((d:ℝ)+3)*lam ≤ ε/2 := by
    calc
      _ ≤ ((d:ℝ)+3)*(ε/(2*((d:ℝ)+3))) :=
        mul_le_mul_of_nonneg_left (min_le_left _ _) (by positivity)
      _ = _ := by field_simp
  obtain ⟨H,N₁,hH,hcontrol,henvelope⟩ := uniform_frostman_profile_envelope hd Q hQ hC hlam
  have hsmall : ∀ᶠ N : ℕ in atTop, s/(N:ℝ) < ε/2 :=
    (tendsto_const_div_atTop_nhds_zero_nat s).eventually (eventually_lt_nhds (by linarith : (0:ℝ) < ε/2))
  obtain ⟨N₂,hN₂⟩ := eventually_atTop.mp hsmall
  refine ⟨lam,γ,hlam,hγ,min_le_right _ _,H,max N₁ (max N₂ H),hH,
    fun N hN => hcontrol N ((le_max_left _ _).trans hN),?_⟩
  intro N hN μ _ hball p hp hret
  have hHN : H ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  have hNp : 0 < N := hH.trans_le hHN
  have hBN : 0 < N/H := Nat.div_pos hHN hH
  have hprop := sourceUnitProfile_properties Q μ hNp hBN p
  apply hcontact _ hprop.2.2.2.1 hprop.2.1
  intro u hu
  have hgrid := henvelope N ((le_max_left _ _).trans hN) μ hball p hp hret
  have hlow := sourceUnitProfile_lower_from_grid Q μ hNp hBN p hs hgrid hu
  have hsn := hN₂ N ((le_max_left _ _).trans ((le_max_right _ _).trans hN))
  linarith

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_UniformContactDepths
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform integer-depth margins from the compactness contact theorem -/

namespace Falconer

theorem uniform_contact_depth_bounds {A B γ : ℝ} (hγ : 0 < γ)
    (hA : γ ≤ A) (hAB : A+γ ≤ B) (hB : B+γ ≤ 1) (hBA : B+γ ≤ 2*A)
    {N : ℕ} (hN : 0 < N) (hlarge : 4 ≤ γ*(N:ℝ)) :
    let a := Nat.floor (A*(N:ℝ))
    let b := Nat.floor (B*(N:ℝ))
    a ≤ b ∧ b ≤ N ∧ (γ/2)*(N:ℝ) ≤ (a:ℝ) ∧
      (γ/2)*(N:ℝ) ≤ (b-a:ℕ) ∧ γ*(N:ℝ) ≤ (N-b:ℕ) ∧
      (γ/2)*(N:ℝ) ≤ 2*(a:ℝ)-(b:ℝ) := by
  have hNp : 0 < (N:ℝ) := by exact_mod_cast hN
  have hA0 : 0 ≤ A := hγ.le.trans hA
  have hB0 : 0 ≤ B := by linarith
  have hAB' : A ≤ B := by linarith
  let a := Nat.floor (A*(N:ℝ))
  let b := Nat.floor (B*(N:ℝ))
  have haLo : (a:ℝ) ≤ A*(N:ℝ) := Nat.floor_le (mul_nonneg hA0 hNp.le)
  have hbLo : (b:ℝ) ≤ B*(N:ℝ) := Nat.floor_le (mul_nonneg hB0 hNp.le)
  have haHi : A*(N:ℝ) < (a:ℝ)+1 := Nat.lt_floor_add_one _
  have hbHi : B*(N:ℝ) < (b:ℝ)+1 := Nat.lt_floor_add_one _
  have hab : a ≤ b := Nat.floor_mono (mul_le_mul_of_nonneg_right hAB' hNp.le)
  have hbN : b ≤ N := Nat.floor_le_of_le (by nlinarith [mul_le_mul_of_nonneg_right hB hNp.le])
  have hAm := mul_le_mul_of_nonneg_right hA hNp.le
  have hABm := mul_le_mul_of_nonneg_right hAB hNp.le
  have hBm := mul_le_mul_of_nonneg_right hB hNp.le
  have hBAm := mul_le_mul_of_nonneg_right hBA hNp.le
  refine ⟨hab,hbN,?_,?_,?_,?_⟩
  · nlinarith
  · rw [Nat.cast_sub hab]
    nlinarith
  · rw [Nat.cast_sub hbN]
    nlinarith
  · nlinarith

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_SourceClassIntervals
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual integer-depth three-interval data for each retained source class -/

namespace Falconer.Regularization
open Set MeasureTheory
open scoped NNReal
variable {d : ℕ}

theorem source_class_contact_intervals (Q : DyadicCube d) (μ : Measure (Space d))
    {N B : ℕ} (hN : 0 < N) (hB : 0 < B) (p : CellPath d)
    {q t τ γ : ℝ} (hq : 0 ≤ q) (ht : 0 ≤ t) (hγ : 0 < γ)
    (hlarge : 4 ≤ γ*(N:ℝ))
    (hcontact : RobustProfileContact (sourceUnitProfile Q μ N B p) q t τ γ) :
    ∃ A B' : ℝ, ∃ a b : ℕ,
      γ ≤ B'-A ∧ B'-A ≤ 1 ∧ a ≤ b ∧ b ≤ N ∧
      (B'-A)*(N:ℝ)-1 ≤ (b-a:ℕ) ∧ (b-a:ℕ) ≤ (B'-A)*(N:ℝ)+1 ∧
      (γ/2)*(N:ℝ) ≤ (a:ℝ) ∧ (γ/2)*(N:ℝ) ≤ (b-a:ℕ) ∧
      γ*(N:ℝ) ≤ (N-b:ℕ) ∧ (γ/2)*(N:ℝ) ≤ 2*(a:ℝ)-(b:ℝ) ∧
      (∀ j : ℕ, j ≤ a → q*(j:ℝ)/N-τ*(B'-A) ≤ sourceProfile Q μ N B p j) ∧
      (∀ j : ℕ, a ≤ j → j ≤ b →
        t*(j-a:ℕ)/N-τ*(B'-A)-((d:ℝ)+t)/N ≤
          sourceProfile Q μ N B p j-sourceProfile Q μ N B p a) ∧
      (∀ j : ℕ, b ≤ j → j ≤ N →
        q*(j-b:ℕ)/N-τ*(B'-A)-((d:ℝ)+q)/N ≤
          sourceProfile Q μ N B p j-sourceProfile Q μ N B p b) := by
  obtain ⟨A,B',hA,hAB,hB',hBA,hfirst,hmiddle,hlast⟩ := hcontact
  have hA0 : 0 ≤ A := hγ.le.trans hA
  have hAB' : A ≤ B' := by linarith
  have hB1 : B' ≤ 1 := by linarith
  have hround := rounded_profile_contact
    (sourceUnitProfile_properties Q μ hN hB p).2.2.2.1 hA0 hAB' hB1 hq ht
    hfirst hmiddle hlast hN
  have hdepth := uniform_contact_depth_bounds hγ hA hAB hB' hBA hN hlarge
  have hgap := rounded_contact_width hA0 hAB' N
  refine ⟨A,B',Nat.floor (A*(N:ℝ)),Nat.floor (B'*(N:ℝ)),by linarith,by linarith,
    hdepth.1,hdepth.2.1,hgap.1,hgap.2,hdepth.2.2.1,hdepth.2.2.2.1,
    hdepth.2.2.2.2.1,hdepth.2.2.2.2.2,?_⟩
  simpa only [sourceUnitProfile_at_depth Q μ hN B p,NNReal.coe_natCast] using hround

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_ContactLossBudget
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform comparison of contact-profile losses with the middle angular scale -/

namespace Falconer

theorem dyadic_rpow_div_depth {N : ℕ} (hN : 0 < N) (κ : ℝ) :
    ((2:ℝ)^N)^(κ/(N:ℝ)) = (2:ℝ)^κ := by
  rw [← Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 2)]
  congr 1
  field_simp

theorem inverse_dyadic_neg_power (M : ℕ) (ε : ℝ) :
    (1/(2:ℝ)^M)^(-ε) = ((2:ℝ)^M)^ε := by
  rw [one_div,Real.inv_rpow (by positivity),Real.rpow_neg (by positivity),inv_inv]

theorem contact_loss_le (d : ℕ) {τ γ Δ lam : ℝ}
    (hτ : 0 ≤ τ) (hγΔ : γ ≤ Δ) (hlam : lam ≤ τ*γ) :
    τ*γ+τ*Δ+2*((d:ℝ)+1)*lam ≤ ((2*(d:ℝ)+4)*τ)*Δ := by
  have hγ : τ*γ ≤ τ*Δ := mul_le_mul_of_nonneg_left hγΔ hτ
  have hlam' : 2*((d:ℝ)+1)*lam ≤ 2*((d:ℝ)+1)*(τ*Δ) :=
    mul_le_mul_of_nonneg_left (hlam.trans hγ) (by positivity)
  nlinarith

theorem contact_loss_relative_budget {d : ℕ} {τ γ Δ lam ε : ℝ} {N M : ℕ}
    (hτ : 0 ≤ τ) (hγΔ : γ ≤ Δ) (hlam : lam ≤ τ*γ)
    (hsmall : (2*(d:ℝ)+4)*τ ≤ ε/2)
    (hwidth : (N:ℝ)*Δ ≤ 2*(M:ℝ)) :
    (N:ℝ)*(τ*γ+τ*Δ+2*((d:ℝ)+1)*lam) ≤ (M:ℝ)*ε := by
  have hsum := contact_loss_le d hτ hγΔ hlam
  have hc : 0 ≤ (2*(d:ℝ)+4)*τ := by positivity
  calc
    _ ≤ (N:ℝ)*(((2*(d:ℝ)+4)*τ)*Δ) :=
      mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg N)
    _ = ((N:ℝ)*Δ)*((2*(d:ℝ)+4)*τ) := by ring
    _ ≤ (2*(M:ℝ))*((2*(d:ℝ)+4)*τ) := mul_le_mul_of_nonneg_right hwidth hc
    _ ≤ (2*(M:ℝ))*(ε/2) := mul_le_mul_of_nonneg_left hsmall (by positivity)
    _ = _ := by ring

theorem eventually_contact_frostman_coefficient (d : ℕ) {τ γ ε : ℝ}
    (hτ : 0 < τ) (hγ : 0 < γ) (hsmall : (2*(d:ℝ)+4)*τ ≤ ε/2)
    (C κ : ℝ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, 0 < N → ∀ M : ℕ, ∀ Δ lam : ℝ,
      γ ≤ Δ → lam ≤ τ*γ → (N:ℝ)*Δ ≤ 2*(M:ℝ) →
      C*((2:ℝ)^N)^(τ*Δ+κ/(N:ℝ)+2*((d:ℝ)+1)*lam) ≤ (1/(2:ℝ)^M)^(-ε) := by
  obtain ⟨N₀,hN₀⟩ := eventually_relative_scale_constant (mul_pos hτ hγ) (C*(2:ℝ)^κ)
  refine ⟨N₀,?_⟩
  intro N hN hNp M Δ lam hγΔ hlam hwidth
  have hbudget := contact_loss_relative_budget hτ.le hγΔ hlam hsmall hwidth
  have hh := hN₀ N hN M (τ*Δ+2*((d:ℝ)+1)*lam) ε (by nlinarith [hbudget])
  rw [inverse_dyadic_neg_power]
  apply le_trans ?_ hh
  have he : τ*Δ+κ/(N:ℝ)+2*((d:ℝ)+1)*lam =
      κ/(N:ℝ)+(τ*Δ+2*((d:ℝ)+1)*lam) := by ring
  rw [he,Real.rpow_add (by positivity),dyadic_rpow_div_depth hNp]
  ring_nf
  exact le_rfl

theorem eventually_contact_outer_coefficient (d : ℕ) {τ γ : ℝ}
    (hτ : 0 < τ) (hγ : 0 < γ) (C κ : ℝ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, 0 < N → ∀ Δ lam : ℝ,
      γ ≤ Δ → lam ≤ τ*γ →
      C*((2:ℝ)^N)^(τ*Δ+κ/(N:ℝ)+2*((d:ℝ)+1)*lam) ≤
        ((2:ℝ)^N)^(((2*(d:ℝ)+4)*τ)*Δ) := by
  obtain ⟨N₀,hN₀⟩ := Regularization.fixed_constant_absorbed (mul_pos hτ hγ) (C*(2:ℝ)^κ)
  refine ⟨N₀,?_⟩
  intro N hN hNp Δ lam hγΔ hlam
  have hR : 0 < (2:ℝ)^N := by positivity
  have he : τ*Δ+κ/(N:ℝ)+2*((d:ℝ)+1)*lam =
      κ/(N:ℝ)+(τ*Δ+2*((d:ℝ)+1)*lam) := by ring
  calc
    _ = (C*(2:ℝ)^κ)*((2:ℝ)^N)^(τ*Δ+2*((d:ℝ)+1)*lam) := by
      rw [he,Real.rpow_add hR,dyadic_rpow_div_depth hNp]
      ring
    _ ≤ ((2:ℝ)^N)^(τ*γ)*((2:ℝ)^N)^(τ*Δ+2*((d:ℝ)+1)*lam) :=
      mul_le_mul_of_nonneg_right (hN₀ N hN) (by positivity)
    _ = ((2:ℝ)^N)^(τ*γ+τ*Δ+2*((d:ℝ)+1)*lam) := by
      rw [← Real.rpow_add hR]
      congr 1
      ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num))
      (contact_loss_le d hτ.le hγΔ hlam)

theorem middle_scale_power_decay {N M : ℕ} {Δ gain : ℝ}
    (hgain : 0 ≤ gain) (hwidth : (N:ℝ)*Δ ≤ 2*(M:ℝ)) :
    (1/(2:ℝ)^M)^gain ≤ ((2:ℝ)^N)^(-gain*Δ/2) := by
  have he : (1/(2:ℝ)^M)^gain = ((2:ℝ)^M)^(-gain) := by
    rw [one_div,Real.inv_rpow (by positivity),Real.rpow_neg (by positivity)]
  rw [he]
  apply dyadic_relative_scale_bound M N
  have hh := mul_le_mul_of_nonneg_left hwidth hgain
  nlinarith

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_ThreeIntervalCost
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A uniform power bound for the three local deletions and density pruning -/

namespace Falconer

theorem eventually_three_interval_cost {τ γ L gain : ℝ}
    (hτ : 0 < τ) (hγ : 0 < γ) (hL : 1 ≤ 2*L) (hgain : 2*τ ≤ gain) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ M : ℕ, ∀ Δ : ℝ, γ ≤ Δ →
      (N:ℝ)*Δ ≤ 2*(M:ℝ) →
      2*((2:ℝ)^N)^(-(2*(L*τ*Δ)))+2*(1/(2:ℝ)^M)^gain+
        4*((2:ℝ)^N)^(-(τ*Δ)) ≤ ((2:ℝ)^N)^(-(τ*γ/2)) := by
  have hη : 0 < τ*γ/2 := by positivity
  obtain ⟨N₀,hN₀⟩ := Regularization.fixed_constant_absorbed hη 8
  refine ⟨N₀,?_⟩
  intro N hN M Δ hγΔ hwidth
  let R : ℝ := (2:ℝ)^N
  have hR : 0 < R := by dsimp [R]; positivity
  have hR1 : 1 ≤ R := one_le_pow₀ (by norm_num)
  have hΔ0 : 0 ≤ Δ := hγ.le.trans hγΔ
  have hbase : τ*γ ≤ τ*Δ := mul_le_mul_of_nonneg_left hγΔ hτ.le
  have houtExp : τ*γ ≤ 2*(L*τ*Δ) := by
    have hh := mul_le_mul_of_nonneg_right hL (mul_nonneg hτ.le hΔ0)
    nlinarith
  have hmidExp : τ*γ ≤ gain*Δ/2 := by
    have hh := mul_le_mul_of_nonneg_right hgain hΔ0
    nlinarith
  have hout : R^(-(2*(L*τ*Δ))) ≤ R^(-(τ*γ)) :=
    Real.rpow_le_rpow_of_exponent_le hR1 (by linarith)
  have hmid : (1/(2:ℝ)^M)^gain ≤ R^(-(τ*γ)) :=
    (middle_scale_power_decay (by linarith : 0 ≤ gain) hwidth).trans
      (Real.rpow_le_rpow_of_exponent_le hR1 (by linarith))
  have hdensity : R^(-(τ*Δ)) ≤ R^(-(τ*γ)) :=
    Real.rpow_le_rpow_of_exponent_le hR1 (by linarith)
  calc
    _ ≤ 8*R^(-(τ*γ)) := by nlinarith
    _ ≤ R^(τ*γ/2)*R^(-(τ*γ)) :=
      mul_le_mul_of_nonneg_right (hN₀ N hN) (by positivity)
    _ = _ := by rw [← Real.rpow_add hR]; congr 1; ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_ThreeIntervalPower
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The gain on the middle interval absorbs all three density losses -/

namespace Falconer
open scoped ENNReal

theorem three_interval_radial_power (g₀ g₁ g₂ N : ℕ) (hsum : g₀+g₁+g₂ = N)
    {q c β γ e₀ e₂ η : ℝ} (hc : 0 ≤ c)
    (hwidth : β*(N:ℝ) ≤ g₁) (hbudget : e₀+e₂+3*η+γ ≤ c*β) :
    ((2:ℝ)^N)^(e₀+e₂+3*η)*((2:ℝ)^g₀)^(-q)*
      ((2:ℝ)^g₁)^(-q-c)*((2:ℝ)^g₂)^(-q) ≤ ((2:ℝ)^N)^(-q-γ) := by
  have hp (n : ℕ) (t : ℝ) : ((2:ℝ)^n)^t = (2:ℝ)^((n:ℝ)*t) :=
    (Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 2) n t).symm
  simp_rw [hp,← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
  have hn : (0:ℝ) ≤ N := Nat.cast_nonneg N
  have hsum' : (g₀:ℝ)+g₁+g₂ = N := by exact_mod_cast hsum
  nlinarith [congrArg (fun z : ℝ => z*q) hsum',
    mul_le_mul_of_nonneg_left hbudget hn,mul_le_mul_of_nonneg_left hwidth hc]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_ThreeIntervalShift
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The three-interval gain with a fixed coarsening of the middle radial scale -/

namespace Falconer

theorem three_interval_shifted_power {a b N J : ℕ} (hab : a ≤ b) (hbN : b ≤ N)
    (hJ : J ≤ b-a) {q c β γ η ξ : ℝ} (hc : 0 ≤ c)
    (hwidth : β*(N:ℝ) ≤ (b-a:ℕ))
    (hconst : ((2:ℝ)^J)^(q+c) ≤ ((2:ℝ)^N)^ξ)
    (hbudget : 20*η+4*ξ+γ ≤ c*β) :
    ((2:ℝ)^N)^(20*η+3*ξ)*((2:ℝ)^a)^(-q)*
      (1/(2:ℝ)^((b-a)-J))^(q+c)*((2:ℝ)^(N-b))^(-q) ≤
        ((2:ℝ)^N)^(-q-γ) := by
  have hR : 0 < (2:ℝ)^N := by positivity
  have hmid : (1/(2:ℝ)^((b-a)-J))^(q+c) =
      ((2:ℝ)^J)^(q+c)*((2:ℝ)^(b-a))^(-q-c) := by
    rw [one_div,Real.inv_rpow (by positivity),← Real.rpow_neg (by positivity)]
    have hh := dyadic_shifted_decay (g := 0) (v := b-a) (by simpa using hJ) (q+c)
    simpa only [Nat.sub_zero,zero_add,neg_add_rev,sub_eq_add_neg,add_comm] using hh
  rw [hmid]
  calc
    _ ≤ ((2:ℝ)^N)^(20*η+3*ξ)*((2:ℝ)^a)^(-q)*
        (((2:ℝ)^N)^ξ*((2:ℝ)^(b-a))^(-q-c))*((2:ℝ)^(N-b))^(-q) := by
      gcongr
    _ = ((2:ℝ)^N)^(10*η+(10*η+ξ)+3*ξ)*((2:ℝ)^a)^(-q)*
        ((2:ℝ)^(b-a))^(-q-c)*((2:ℝ)^(N-b))^(-q) := by
      conv_rhs => rw [show 10*η+(10*η+ξ)+3*ξ = (20*η+3*ξ)+ξ by ring,Real.rpow_add hR]
      ring
    _ ≤ _ := three_interval_radial_power a (b-a) (N-b) N (by omega) hc hwidth (by linarith)

theorem three_interval_relative_budget {L τ Δ gain γ : ℝ}
    (hΔ : 0 ≤ Δ) (hγ : γ ≤ Δ) (hgain : 0 ≤ gain)
    (hsmall : (20*L+4)*τ ≤ gain/8) :
    20*(L*τ*Δ)+4*(τ*Δ)+(gain*γ/8) ≤ (gain/2)*(Δ/2) := by
  have hscaled := mul_le_mul_of_nonneg_right hsmall hΔ
  have hmargin := mul_le_mul_of_nonneg_left hγ hgain
  nlinarith

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_ThreeIntervalProduct
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual three conditional factors, including the density penalties -/

namespace Falconer
open scoped ENNReal

theorem three_density_factor_product {R A B C η ξ : ℝ} (hR : 0 < R)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (_hC : 0 ≤ C) :
    ((ENNReal.ofReal (R^(-ξ)))⁻¹*ENNReal.ofReal (R^(10*η)*A))*
      ((ENNReal.ofReal (R^(-ξ)))⁻¹*ENNReal.ofReal B)*
      ((ENNReal.ofReal (R^(-ξ)))⁻¹*ENNReal.ofReal (R^(10*η)*C)) =
      ENNReal.ofReal (R^(20*η+3*ξ)*A*B*C) := by
  have hi : (ENNReal.ofReal (R^(-ξ)))⁻¹ = ENNReal.ofReal (R^ξ) := by
    rw [← ENNReal.ofReal_inv_of_pos (by positivity),Real.rpow_neg hR.le,inv_inv]
  rw [hi]
  rw [← ENNReal.ofReal_mul (by positivity),← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity),← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  have hp : R^ξ*R^(10*η)*R^ξ*R^ξ*R^(10*η) = R^(20*η+3*ξ) := by
    rw [← Real.rpow_add hR,← Real.rpow_add hR,← Real.rpow_add hR,← Real.rpow_add hR]
    congr 1
    ring
  calc
    _ = (R^ξ*R^(10*η)*R^ξ*R^ξ*R^(10*η))*A*B*C := by ring
    _ = _ := by rw [hp]

theorem three_interval_density_product_bound {a b N J : ℕ}
    (hab : a ≤ b) (hbN : b ≤ N) (hJ : J ≤ b-a)
    {q c β γ η ξ : ℝ} (hc : 0 ≤ c)
    (hwidth : β*(N:ℝ) ≤ (b-a:ℕ))
    (hconst : ((2:ℝ)^J)^(q+c) ≤ ((2:ℝ)^N)^ξ)
    (hbudget : 20*η+4*ξ+γ ≤ c*β) :
    ((ENNReal.ofReal (((2:ℝ)^N)^(-ξ)))⁻¹*
        ENNReal.ofReal (((2:ℝ)^N)^(10*η)*((2:ℝ)^a)^(-q)))*
      ((ENNReal.ofReal (((2:ℝ)^N)^(-ξ)))⁻¹*
        ENNReal.ofReal ((1/(2:ℝ)^((b-a)-J))^(q+c)))*
      ((ENNReal.ofReal (((2:ℝ)^N)^(-ξ)))⁻¹*
        ENNReal.ofReal (((2:ℝ)^N)^(10*η)*((2:ℝ)^(N-b))^(-q))) ≤
      ENNReal.ofReal (((2:ℝ)^N)^(-q-γ)) := by
  rw [three_density_factor_product (by positivity) (by positivity) (by positivity) (by positivity)]
  exact ENNReal.ofReal_le_ofReal (three_interval_shifted_power hab hbN hJ hc hwidth hconst hbudget)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_ThreeIntervalData
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual four dyadic depths and three collision factors -/

namespace Falconer
open scoped ENNReal BigOperators

theorem threeIntervalDepth_le {a b N : ℕ} (hab : a ≤ b) (hbN : b ≤ N)
    {j : ℕ} (hj : j ≤ 3) : threeIntervalDepth a b N j ≤ N := by
  interval_cases j <;> norm_num [threeIntervalDepth] <;> omega

theorem threeIntervalDepth_mono {a b N : ℕ} (hab : a ≤ b) (hbN : b ≤ N)
    {j : ℕ} (hj : j < 3) : threeIntervalDepth a b N j ≤ threeIntervalDepth a b N (j+1) := by
  interval_cases j <;> norm_num [threeIntervalDepth] <;> assumption

theorem threeIntervalDepth_child {a b N : ℕ} (hab : a ≤ b) (hbN : b ≤ N)
    {j : ℕ} (hj : j < 3) : a ≤ threeIntervalDepth a b N (j+1) := by
  interval_cases j <;> norm_num [threeIntervalDepth] <;> omega

theorem threeIntervalFactor_product {a b N J : ℕ}
    (hab : a ≤ b) (hbN : b ≤ N) (hJ : J ≤ b-a)
    {q c β γ η ξ : ℝ} (hc : 0 ≤ c)
    (hwidth : β*(N:ℝ) ≤ (b-a:ℕ))
    (hconst : ((2:ℝ)^J)^(q+c) ≤ ((2:ℝ)^N)^ξ)
    (hbudget : 20*η+4*ξ+γ ≤ c*β) :
    (∏ j ∈ Finset.range 3, (ENNReal.ofReal (((2:ℝ)^N)^(-ξ)))⁻¹*
      threeIntervalFactor a b N J q c η j) ≤ ENNReal.ofReal (((2:ℝ)^N)^(-q-γ)) := by
  simpa [Finset.prod_range_succ,threeIntervalFactor] using
    three_interval_density_product_bound hab hbN hJ hc hwidth hconst hbudget

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_ThreeIntervalDyadicGain
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The three-interval cap gain on the actual occupied source tree -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal BigOperators
variable {d : ℕ}

theorem three_interval_dyadic_gain (μ ν : Measure (Space d))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (Q : DyadicCube d) (hQ : 0 < Q.side) {a b N J : ℕ}
    (hab : a ≤ b) (hbN : b ≤ N) (hJ : J ≤ b-a)
    (A P : Set (Space d)) (hA : μ Aᶜ = 0) {s : ℝ} (hs : 0 < s)
    (hsep : ∀ z ∈ A, ∀ x ∈ P, s ≤ ‖z-x‖)
    (G : Set (Space d × Space d)) (hG : MeasurableSet G)
    (hGcore : G ⊆ Q.occupiedTreeCore μ N ×ˢ P)
    (W : ℕ → ℝ) (cost : ℕ → ℝ≥0∞)
    {q c β γ η ξ : ℝ} (hc : 0 ≤ c)
    (hwidth : β*(N:ℝ) ≤ (b-a:ℕ))
    (hconst : ((2:ℝ)^J)^(q+c) ≤ ((2:ℝ)^N)^ξ)
    (hbudget : 20*η+4*ξ+γ ≤ c*β)
    (hsmall : ∀ j < 3,
      Real.sqrt d*(Q.side/(2:ℝ)^(threeIntervalDepth a b N (j+1))) ≤ s/2)
    (hW : ∀ j < 3,
      2*(Real.sqrt d*(Q.side/(2:ℝ)^(threeIntervalDepth a b N (j+1))))/(s/2)+
        2*(1/(2:ℝ)^N) ≤ W j)
    (hlocal : ∀ j < 3, ∀ p ∈ Q.occupiedPaths μ (threeIntervalDepth a b N j),
      ∃ H : Set (Space d × Space d), MeasurableSet H ∧
      ((ProbabilityTheory.cond μ (Q.descendant p).carrier).prod ν)
        ((G ∩ ((Q.descendant p).carrier ×ˢ univ)) \ H) ≤ cost j ∧
      ∀ z ∈ H, radialCollisionMass (ProbabilityTheory.cond μ (Q.descendant p).carrier)
        (W j) z ≤ threeIntervalFactor a b N J q c η j) :
    ∃ G' : Set (Space d × Space d), MeasurableSet G' ∧ G' ⊆ G ∧
      (μ.prod ν) (G \ G') ≤ (∑ j ∈ Finset.range 3, cost j)+
        4*ENNReal.ofReal (((2:ℝ)^N)^(-ξ)) ∧
      ∀ x u : Space d, μ {z | (z,x) ∈ G' ∧ ‖normalize (z-x)-u‖ ≤ 1/(2:ℝ)^N} ≤
        ENNReal.ofReal (((2:ℝ)^N)^(-q-γ)) := by
  obtain ⟨G',hG',hsub,hdel,hbound⟩ := dyadic_gain_of_local_prunings μ ν Q hQ N 3
    (threeIntervalDepth a b N) (fun _ hj => threeIntervalDepth_le hab hbN hj)
    (fun _ hj => threeIntervalDepth_mono hab hbN hj) A P hA hs hsep G hG hGcore
    (1/(2:ℝ)^N) W (ENNReal.ofReal (((2:ℝ)^N)^(-ξ)))
    (threeIntervalFactor a b N J q c η) cost (by positivity) ENNReal.ofReal_ne_top hsmall hW hlocal
  refine ⟨G',hG',hsub,?_,fun x u => (hbound x u).trans ?_⟩
  · norm_num at hdel
    exact hdel
  · exact threeIntervalFactor_product hab hbN hJ hc hwidth hconst hbudget

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_NonendpointContactGain
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Nonendpoint one-scale gain for an actual source class with a contact interval

All three local estimates are applied to the original conditional source laws.
The incoming relation and pin law are never renormalized.
-/

namespace Falconer.Regularization
open Set MeasureTheory NormedSpace
open scoped ENNReal BigOperators
attribute [local instance] Classical.propDecidable

theorem nonendpoint_contact_gain (hpublished : PublishedPlanarFurstenberg)
    {h : ℕ} {t q : ℝ} (hq : (h:ℝ) < q) (hq' : q-(h:ℝ) ≤ 1/2)
    (hqt : q < t) (ht : t-(h:ℝ) < 1)
    (Q : DyadicCube (h+2)) (hQ : Q.side = 1)
    {D s : ℝ} (hD : 1 ≤ D) (hDdim : Real.sqrt (h+2:ℕ) ≤ D) (hs : 0 < s) :
    ∃ ε gain : ℝ, 0 < ε ∧ 0 < gain ∧
      ∀ τ γ : ℝ, 0 < τ → 0 < γ →
        (2*((h+2:ℕ):ℝ)+4)*τ ≤ ε/2 →
        (20*(2*((h+2:ℕ):ℝ)+4)+4)*τ ≤ gain/8 → 2*τ ≤ gain →
      ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ (μ ν : Measure (Space (h+2))) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν],
      ∀ B : ℕ, 0 < B → ∀ lam : ℝ, 0 ≤ lam → lam ≤ τ*γ →
        (B:ℝ) ≤ lam*(N:ℝ) → (2:ℝ)^(N/B+2) ≤ ((2:ℝ)^N)^lam →
      ∀ p₀ ∈ regularizationLeaves Q μ N,
        RobustProfileContact (sourceUnitProfile Q μ N B p₀) q t τ γ →
      ∀ A P : Set (Space (h+2)), MeasurableSet A → MeasurableSet P →
        μ Aᶜ = 0 → ν Pᶜ = 0 →
        (∀ z ∈ A, ∀ x ∈ P, s ≤ ‖z-x‖) →
        (∀ y ∈ Q.carrier, ∀ x ∈ P, ‖y-x‖ ≤ D) →
      ∀ G : Set (Space (h+2) × Space (h+2)), MeasurableSet G →
        (∀ᵐ z ∂μ, ∀ r : ℝ, 1/(2:ℝ)^N ≤ r → r ≤ 1 →
          ∀ u : Space (h+2), ‖u‖ = 1 →
            ν {x | (z,x) ∈ G ∧ dist (normalize (x-z)) u < r} ≤
              ENNReal.ofReal (((2:ℝ)^N)^(τ*γ)*r^q)) →
      ∃ G' : Set (Space (h+2) × Space (h+2)), MeasurableSet G' ∧ G' ⊆ G ∧
        ((sourceClass Q μ N B p₀).prod ν) (G \ G') ≤
          ENNReal.ofReal (((2:ℝ)^N)^(-(τ*γ/2))) ∧
        ∀ x u : Space (h+2), sourceClass Q μ N B p₀
          {z | (z,x) ∈ G' ∧ ‖normalize (z-x)-u‖ ≤ 1/(2:ℝ)^N} ≤
            ENNReal.ofReal (((2:ℝ)^N)^(-q-gain*γ/8)) := by
  obtain ⟨ε,gain,hε,hgain,M₀,hmiddle⟩ :=
    nonendpoint_source_class_middle_pruning hpublished hq hq' hqt ht
  refine ⟨ε,gain,hε,hgain,?_⟩
  intro τ γ hτ hγ hτε hτgain hτgain'
  let L : ℝ := 2*((h+2:ℕ):ℝ)+4
  let σ : ℝ := cellContraction (h+2)
  let C : ℝ := 4*Real.sqrt (h+2:ℕ)/s+2
  have hL : 1 ≤ L := by dsimp [L]; have hh := Nat.cast_nonneg (α := ℝ) (h+2); linarith only [hh]
  have hq0 : 0 ≤ q := by have hh := Nat.cast_nonneg (α := ℝ) h; linarith
  have ht0 : 0 ≤ t := hq0.trans hqt.le
  have hside : 0 < Q.side := by rw [hQ]; norm_num
  have hσ : 0 < σ := cellContraction_pos _
  have hη₀ : 0 < L*τ*γ := by positivity
  obtain ⟨Jo,No,houter⟩ := source_class_outer_radial_pruning Q hQ hD hDdim hη₀ hq0 C
  obtain ⟨Jm,Nm,hgeom⟩ := uniform_middle_geometry hσ (by positivity : 0 < s/2)
    (by positivity : 0 < γ/2) D C M₀
  obtain ⟨Na,hmargin⟩ := eventually_integer_margin (by positivity : 0 < γ/2) Jo
  obtain ⟨Ns,hsmall⟩ := eventually_cell_diameter_small (h+2) (by positivity : 0 < γ/2) hs
  let K : ℝ := (((2*Nat.ceil (2+4*Real.sqrt (h+2:ℕ))+1)^(h+2):ℕ):ℝ)
  obtain ⟨Nf,hfirst⟩ := eventually_contact_outer_coefficient (h+2) hτ hγ (K*(2:ℝ)^q) 0
  obtain ⟨Nl,hlast⟩ := eventually_contact_outer_coefficient (h+2) hτ hγ
    (K*(2:ℝ)^q) (((h+2:ℕ):ℝ)+q)
  obtain ⟨Nt,htcoef⟩ := eventually_contact_frostman_coefficient (h+2) hτ hγ hτε
    (K*(2:ℝ)^t*σ^(-t)) (((h+2:ℕ):ℝ)+t)
  obtain ⟨Nc,hconst⟩ := fixed_constant_absorbed (mul_pos hτ hγ)
    (((2:ℝ)^Jm)^(q+gain/2))
  obtain ⟨Nd,hcost⟩ := eventually_three_interval_cost hτ hγ
    (by linarith : 1 ≤ 2*L) hτgain'
  obtain ⟨Nlarge,hlarge⟩ := exists_nat_gt (4/γ)
  let N₀ := max 1 (max No (max Nm (max Na (max Ns (max Nf (max Nl (max Nt
    (max Nc (max Nd Nlarge)))))))))
  refine ⟨N₀,?_⟩
  intro N hN μ ν _ _ B hB lam hlam hlamτ hblock hblock'
    p₀ hp₀ hcontact A P hA hP hAfull hPfull hsep hpin G hG hcap
  change max 1 (max No (max Nm (max Na (max Ns (max Nf (max Nl (max Nt
    (max Nc (max Nd Nlarge))))))))) ≤ N at hN
  simp only [max_le_iff] at hN
  rcases hN with ⟨h1,hNo,hNm,hNa,hNs,hNf,hNl,hNt,hNc,hNd,hNL⟩
  have hNp : 0 < N := by omega
  have hNN : (Nlarge:ℝ) ≤ N := by exact_mod_cast hNL
  have hlarge' : 4 ≤ γ*(N:ℝ) := by
    have hh := (div_lt_iff₀ hγ).mp hlarge
    nlinarith only [hh,hNN,hγ]
  obtain ⟨α,β,a,b,hγΔ,hΔ1,hab,hbN,hgap,_,ha,_,hNb,hfreeze,hi₀,hi₁,hi₂⟩ :=
    source_class_contact_intervals Q μ hNp hB p₀ hq0 ht0 hγ hlarge' hcontact
  let Δ := β-α
  let η := L*τ*Δ
  let ξ := τ*Δ
  let M := (b-a)-Jm
  have hΔ : 0 < Δ := hγ.trans_le hγΔ
  have hη : L*τ*γ ≤ η := mul_le_mul_of_nonneg_left hγΔ (by positivity)
  obtain ⟨hJm,hM,hNM,hfr,hwi⟩ := hgeom N hNm a b Δ hab
    (by dsimp [Δ]; linarith only [hγΔ,hγ]) hgap hfreeze
  have hJoA : Jo ≤ a := hmargin N hNa a ha
  have hJoB : b+Jo ≤ N := by
    have hh := hmargin N hNa (N-b) (by linarith only [hNb,hγ])
    omega
  have hsmallA : Real.sqrt (h+2:ℕ)*(Q.side/(2:ℝ)^a) ≤ s/2 := by
    rw [hQ,mul_one_div]
    exact hsmall N hNs a ha
  have hsmallAll {n : ℕ} (han : a ≤ n) :
      Real.sqrt (h+2:ℕ)*(Q.side/(2:ℝ)^n) ≤ s/2 := by
    apply le_trans _ hsmallA
    exact mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_left hside.le (by positivity)
        (pow_le_pow_right₀ (by norm_num) han)) (Real.sqrt_nonneg _)
  have hcoef₀ : K*(2:ℝ)^q*((2:ℝ)^N)^(τ*Δ+2*(((h+2:ℕ):ℝ)+1)*lam) ≤
      ((2:ℝ)^N)^η := by
    simpa only [zero_div,add_zero] using hfirst N hNf hNp Δ lam hγΔ hlamτ
  have hcoef₂ := hlast N hNl hNp Δ lam hγΔ hlamτ
  have hcoef₁ : K*(2:ℝ)^t*((2:ℝ)^N)^
      ((τ*Δ+(((h+2:ℕ):ℝ)+t)/(N:ℝ))+2*(((h+2:ℕ):ℝ)+1)*lam)*σ^(-t) ≤
      (1/(2:ℝ)^M)^(-ε) := by
    convert htcoef N hNt hNp M Δ lam hγΔ hlamτ hNM using 1 <;> first | rfl | ring
  have hreverseOuter : ((2:ℝ)^N)^(τ*γ) ≤ ((2:ℝ)^N)^η := by
    apply Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num))
    have hh := mul_le_mul_of_nonneg_right hL (mul_nonneg hτ.le hγ.le)
    dsimp [η]
    nlinarith only [hh,hη]
  have hreverseMiddle : ((2:ℝ)^N)^(τ*γ) ≤ (1/(2:ℝ)^M)^(-ε) := by
    rw [inverse_dyadic_neg_power]
    apply dyadic_relative_scale_bound
    have hh := contact_loss_relative_budget hτ.le hγΔ hlamτ hτε hNM
    have hx : 0 ≤ (N:ℝ)*(τ*Δ+2*(((h+2:ℕ):ℝ)+1)*lam) := by positivity
    nlinarith only [hh,hx]
  let ρ := sourceClass Q μ N B p₀
  have : IsProbabilityMeasure ρ := regularization_class_probability Q hside μ N B hp₀
  have hρA : ρ Aᶜ = 0 := sourceClass_absolutelyContinuous_ol Q μ N B p₀ hAfull
  obtain ⟨G₀,hG₀,hG₀G,hG₀core,hnull⟩ :=
    source_class_pair_core Q hside μ ν N B p₀ hp₀ A P hA hP hAfull hPfull G hG
  have hcore : G₀ ⊆ Q.occupiedTreeCore ρ N ×ˢ P := fun _ hz => ⟨(hG₀core hz).1.2,(hG₀core hz).2⟩
  have hdiag {z x : Space (h+2)} (hz : (z,x) ∈ G₀) : z ≠ x := by
    have hh := hsep z (hG₀core hz).1.1 x (hG₀core hz).2
    intro he
    simp only [he,sub_self,norm_zero] at hh
    exact (not_le_of_gt hs) hh
  let cost : ℕ → ℝ≥0∞ := fun j => if j = 1 then 2*ENNReal.ofReal ((1/(2:ℝ)^M)^gain)
    else ENNReal.ofReal (((2:ℝ)^N)^(-(2*η)))
  have hlocal : ∀ j < 3, ∀ p ∈ Q.occupiedPaths ρ (threeIntervalDepth a b N j),
      ∃ H : Set (Space (h+2) × Space (h+2)), MeasurableSet H ∧
      ((ProbabilityTheory.cond ρ (Q.descendant p).carrier).prod ν)
        ((G₀ ∩ ((Q.descendant p).carrier ×ˢ univ)) \ H) ≤ cost j ∧
      ∀ z ∈ H, radialCollisionMass (ProbabilityTheory.cond ρ (Q.descendant p).carrier)
        (C/(2:ℝ)^(threeIntervalDepth a b N (j+1))) z ≤
          threeIntervalFactor a b N Jm q (gain/2) η j := by
    intro j hj p hp
    have hpPos : 0 < ρ (Q.descendant p).carrier := (Finset.mem_filter.mp hp).2
    have hpLen : p.length = threeIntervalDepth a b N j :=
      (mem_cubePaths _ _ _).mp (Finset.mem_filter.mp hp).1
    let V := G₀ ∩ ((Q.descendant p).carrier ×ˢ univ)
    have hV : MeasurableSet V := hG₀.inter ((Q.descendant p).measurable.prod MeasurableSet.univ)
    have hVG : V ⊆ G := inter_subset_left.trans hG₀G
    have hVdiag : ∀ z x, (z,x) ∈ V → x ≠ z := fun _ _ hz => (hdiag hz.1).symm
    have hVpin : ∀ z x, (z,x) ∈ V → ∀ y ∈ (Q.descendant p).carrier, ‖y-x‖ ≤ D :=
      fun _ _ hz y hy => hpin y (Q.descendant_subset p hy) _ (hG₀core hz.1).2
    have hac := sourceClass_conditional_absolutelyContinuous Q μ N B p₀ p
    interval_cases j
    · have hlen : p.length = 0 := by simpa [threeIntervalDepth] using hpLen
      obtain ⟨H,hH,_,hd,hk⟩ := houter N hNo η hη 0 a (by omega) (hab.trans hbN)
        μ ν B hNp hB lam (τ*Δ) hblock hblock' p₀ hp₀ p hlen hpPos
        (by intro n _ hn; simpa only [Nat.sub_zero,sourceProfile,Nat.cast_zero,regularizedProfile_zero,sub_zero] using hi₀ n hn)
        hcoef₀ V hV hVdiag hVpin
        (reverse_caps_all_radii μ _ ν hac hVG (hab.trans hbN) hreverseOuter hcap)
      refine ⟨H,hH,?_,?_⟩
      · simpa [cost] using hd
      · simpa [threeIntervalDepth,threeIntervalFactor] using hk
    · have hlen : p.length = a := by simpa [threeIntervalDepth] using hpLen
      have hp' : p ∈ Q.occupiedPaths ρ a := by simpa [threeIntervalDepth] using hp
      let w₀ : Sphere (h+2) := ⟨EuclideanSpace.basisFun (Fin (h+2)) ℝ 0,by
        simpa only [Metric.mem_sphere,dist_zero_right] using
          (EuclideanSpace.basisFun (Fin (h+2)) ℝ).norm_eq_one 0⟩
      obtain ⟨H,hH,_,hd,hk⟩ := hmiddle M hM Q hQ μ ν (by simp) N B hNp hB lam
        (τ*Δ+(((h+2:ℕ):ℝ)+t)/(N:ℝ)) σ (by positivity) hlam hσ
        (cellContraction_le_one _) (cellContraction_sqrt _) hblock hblock' p₀ hp₀
        a b hab hbN (Nat.sub_le _ _) p hlen hpPos
        (by intro n hn hn'; have hh := hi₁ n hn hn'; linarith only [hh]) hcoef₁ w₀ V hV
        (fun z x hz => ⟨hdiag hz.1,hz.2.1⟩)
        (reverse_caps_transfer μ _ ν hac hVG ((Nat.sub_le _ _).trans ((Nat.sub_le _ _).trans hbN))
          hreverseMiddle hcap)
        (s/2) D (C/(2:ℝ)^b) (by positivity) hfr hwi (by
          intro x hx
          obtain ⟨z,hz⟩ := hx
          refine ⟨occupied_cell_center_separation Q hside ρ A P hρA hsep hsmallA hp'
            x (hG₀core hz.1).2,?_⟩
          exact ProbabilityTheory.ae_cond_of_forall_mem (Q.descendant p).measurable
            (fun y hy => hVpin z x hz y hy))
      refine ⟨H,hH,?_,?_⟩
      · simpa [cost] using hd
      · simpa [threeIntervalDepth,threeIntervalFactor,M] using hk
    · have hlen : p.length = b := by simpa [threeIntervalDepth] using hpLen
      obtain ⟨H,hH,_,hd,hk⟩ := houter N hNo η hη b N hJoB le_rfl
        μ ν B hNp hB lam (τ*Δ+(((h+2:ℕ):ℝ)+q)/(N:ℝ)) hblock hblock' p₀ hp₀ p hlen hpPos
        (by intro n hn hn'; have hh := hi₂ n hn hn'; linarith only [hh])
        hcoef₂ V hV hVdiag hVpin (reverse_caps_all_radii μ _ ν hac hVG le_rfl hreverseOuter hcap)
      refine ⟨H,hH,?_,?_⟩
      · simpa [cost] using hd
      · simpa [threeIntervalDepth,threeIntervalFactor] using hk
  have hβ : (Δ/2)*(N:ℝ) ≤ (b-a:ℕ) := by
    have hh : ((b-a)-Jm:ℕ) ≤ b-a := Nat.sub_le _ _
    have hh' : (M:ℝ) ≤ (b-a:ℕ) := by exact_mod_cast hh
    nlinarith only [hh',hNM]
  have hconst' : ((2:ℝ)^Jm)^(q+gain/2) ≤ ((2:ℝ)^N)^ξ :=
    (hconst N hNc).trans (Real.rpow_le_rpow_of_exponent_le
      (one_le_pow₀ (by norm_num)) (mul_le_mul_of_nonneg_left hγΔ hτ.le))
  have hbudget : 20*η+4*ξ+gain*γ/8 ≤ (gain/2)*(Δ/2) :=
    three_interval_relative_budget hΔ.le hγΔ hgain.le hτgain
  obtain ⟨G',hG',hsub,hdel,hcaps⟩ := three_interval_dyadic_gain ρ ν Q hside hab hbN hJm
    A P hρA hs hsep G₀ hG₀ hcore
    (fun j => C/(2:ℝ)^(threeIntervalDepth a b N (j+1))) cost
    (by positivity : 0 ≤ gain/2) hβ hconst' hbudget
    (fun j hj => hsmallAll (threeIntervalDepth_child hab hbN hj))
    (fun j hj => by
      rw [hQ]
      exact dyadic_collision_width (h+2) hs le_rfl
        (threeIntervalDepth_le hab hbN (by omega))) hlocal
  refine ⟨G',hG',hsub.trans hG₀G,?_,hcaps⟩
  have hz : (ρ.prod ν) (G \ G₀) ≤ 0 := hnull.le
  have htotal := relative_pruning_cost_trans (ρ.prod ν) G G₀ G' hz hdel
  rw [zero_add] at htotal
  apply htotal.trans
  have hc := hcost N hNd M Δ hγΔ hNM
  have he : (∑ j ∈ Finset.range 3, cost j)+4*ENNReal.ofReal (((2:ℝ)^N)^(-ξ)) =
      ENNReal.ofReal (2*((2:ℝ)^N)^(-(2*η))+2*(1/(2:ℝ)^M)^gain+
        4*((2:ℝ)^N)^(-ξ)) := by
    rw [ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_add (by positivity) (by positivity)]
    simp only [Finset.sum_range_succ,Finset.sum_range_zero,cost,show (0:ℕ) ≠ 1 by omega,
      show (2:ℕ) ≠ 1 by omega,ite_false, if_false,ite_true, if_true,zero_add,
      ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2),
      ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 4),ENNReal.ofReal_ofNat]
    ring
  rw [he]
  exact ENNReal.ofReal_le_ofReal hc

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_NonendpointOneScale
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform nonendpoint one-scale radial improvement

This is one orientation of the preparation lemma. The input reverse caps are
measured using the original probability laws and incoming pair relation.
-/

namespace Falconer.Regularization
open Set MeasureTheory NormedSpace
open scoped ENNReal

theorem nonendpoint_one_scale_gain_oai (hpublished : PublishedPlanarFurstenberg)
    {h : ℕ} {α t q C D s : ℝ}
    (hq : (h:ℝ) < q) (hq' : q-(h:ℝ) ≤ 1/2) (hqt : q < t)
    (ht : t-(h:ℝ) < 1) (htα : t < α) (hC : 0 ≤ C)
    (Q : DyadicCube (h+2)) (hQ : Q.side = 1)
    (hD : 1 ≤ D) (hDdim : Real.sqrt (h+2:ℕ) ≤ D) (hs : 0 < s) :
    ∃ ε c : ℝ, 0 < ε ∧ 0 < c ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ (μ ν : Measure (Space (h+2))) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν],
        μ Q.carrierᶜ = 0 →
        (∀ y : Space (h+2), ∀ r > 0, μ (Metric.ball y r) ≤ ENNReal.ofReal (C*r^α)) →
      ∀ A P : Set (Space (h+2)), MeasurableSet A → MeasurableSet P →
        μ Aᶜ = 0 → ν Pᶜ = 0 →
        (∀ z ∈ A, ∀ x ∈ P, s ≤ ‖z-x‖) →
        (∀ y ∈ Q.carrier, ∀ x ∈ P, ‖y-x‖ ≤ D) →
      ∀ G : Set (Space (h+2) × Space (h+2)), MeasurableSet G →
        (∀ᵐ z ∂μ, ∀ r : ℝ, 1/(2:ℝ)^N ≤ r → r ≤ 1 →
          ∀ u : Space (h+2), ‖u‖ = 1 →
            ν {x | (z,x) ∈ G ∧ dist (normalize (x-z)) u < r} ≤
              ENNReal.ofReal (((2:ℝ)^N)^ε*r^q)) →
      ∃ G' : Set (Space (h+2) × Space (h+2)), MeasurableSet G' ∧ G' ⊆ G ∧
        (μ.prod ν) (G \ G') ≤ ENNReal.ofReal (((2:ℝ)^N)^(-c)) ∧
        ∀ x u : Space (h+2), μ {z | (z,x) ∈ G' ∧ ‖normalize (z-x)-u‖ ≤ 1/(2:ℝ)^N} ≤
          ENNReal.ofReal (((2:ℝ)^N)^(-q-c)) := by
  obtain ⟨ε₁,gain,hε₁,hgain,hclass⟩ := nonendpoint_contact_gain hpublished hq hq' hqt ht
    Q hQ hD hDdim hs
  obtain ⟨τ,hτ,hτε,hτgain,hτgain'⟩ := one_scale_loss_choice (h+2) hε₁ hgain
  have hside : 0 < Q.side := by rw [hQ]; norm_num
  have hα : 0 ≤ α := by
    have hh := Nat.cast_nonneg (α := ℝ) h
    linarith only [hh,hq,hqt,htα]
  obtain ⟨lam,γ,hlam,hγ,hlamτ,H,Nc,hH,hcontrols,hcontact⟩ :=
    source_classes_uniform_contact (by omega : 0 < h+2) Q hside hα hqt htα hτ hC
  obtain ⟨Ng,hNg⟩ := hclass τ γ hτ hγ hτε hτgain hτgain'
  obtain ⟨c₀,hc₀,Nd,hNd⟩ := weak_radial_total_cost 0 (4*H+2)
    (A := 0) (by norm_num) hlam (by norm_num : (0:ℝ) < 1)
    (by norm_num : (0:ℝ) < 1) (by positivity : 0 < τ*γ/2)
  let c := min c₀ (gain*γ/8)
  have hc : 0 < c := lt_min hc₀ (by positivity)
  refine ⟨τ*γ,c,mul_pos hτ hγ,hc,max H (max (h+2+3) (max Nc (max Ng Nd))),?_⟩
  intro N hN μ ν _ _ hroot hfrost A P hA hP hAfull hPfull hsep hpin G hG hcap
  simp only [max_le_iff] at hN
  obtain ⟨hHN,hdN,hNc,hNg',hNd'⟩ := hN
  obtain ⟨hNp,hNB,_,hblock,hblock'⟩ := hcontrols N hNc
  have hlocal : ∀ p ∈ regularizationLeaves Q μ N,
      regularizationLabel Q μ N (N/H) p ∈ regularizationIndex Q μ N (N/H)
        (ENNReal.ofReal (((2:ℝ)^N)^(-lam))) →
      ∃ G' : Set (Space (h+2) × Space (h+2)), MeasurableSet G' ∧
        ((sourceClass Q μ N (N/H) p).prod ν) (G \ G') ≤
          ENNReal.ofReal (((2:ℝ)^N)^(-(τ*γ/2))) ∧
        ∀ x u : Space (h+2), sourceClass Q μ N (N/H) p
          {z | (z,x) ∈ G' ∧ ‖normalize (z-x)-u‖ ≤ 1/(2:ℝ)^N} ≤
            ENNReal.ofReal (((2:ℝ)^N)^(-q-gain*γ/8)) := by
    intro p hp hret
    obtain ⟨G',hG',_,hdel,hbound⟩ := hNg N hNg' μ ν (N/H) hNB lam hlam.le hlamτ
      hblock hblock' p hp (hcontact N hNc μ hfrost p hp hret)
      A P hA hP hAfull hPfull hsep hpin G hG hcap
    exact ⟨G',hG',hdel,hbound⟩
  obtain ⟨G',hG',hsub,hdel,hbound⟩ := source_relative_regularization_gain Q hside μ ν G hG
    hroot hH hHN hdN (by positivity : 0 < ENNReal.ofReal (((2:ℝ)^N)^(-lam)))
    (ENNReal.ofReal (((2:ℝ)^N)^(-(τ*γ/2))))
    (ENNReal.ofReal (((2:ℝ)^N)^(-q-gain*γ/8))) (1/(2:ℝ)^N) hlocal
  refine ⟨G',hG',hsub,?_,?_⟩
  · apply hdel.trans
    have hd : ((2:ℝ≥0∞)^(2*N))⁻¹+(N^(4*H+2):ℕ)*ENNReal.ofReal (((2:ℝ)^N)^(-lam))+
        ENNReal.ofReal (((2:ℝ)^N)^(-(τ*γ/2))) ≤ ENNReal.ofReal (((2:ℝ)^N)^(-c₀)) := by
      simpa only [Nat.cast_zero,zero_mul,zero_add,add_zero,Nat.cast_one,one_mul] using hNd N hNd'
    exact hd.trans (ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_le
      (one_le_pow₀ (by norm_num)) (neg_le_neg (min_le_left _ _))))
  · intro x u
    apply (hbound x u).trans (ENNReal.ofReal_le_ofReal
      (Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num)) ?_))
    have hh : c ≤ gain*γ/8 := min_le_right _ _
    linarith only [hh]

end Falconer.Regularization

end OAI
end

theorem solution : type_of% @OAI.Falconer.Regularization.nonendpoint_one_scale_gain_oai := @OAI.Falconer.Regularization.nonendpoint_one_scale_gain_oai
