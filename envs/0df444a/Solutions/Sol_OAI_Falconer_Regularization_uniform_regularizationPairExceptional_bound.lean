-- Prove2me | solution 1 for OAI.Falconer.Regularization.uniform_regularizationPairExceptional_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T22:00:09.787518+00:00
-- url     : https://prove2.me/submissions/c021d3ca-793d-4a6d-8b8f-bee02330aa6d

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ088F002

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

theorem sum_inverse_power_dyadic {ι : Type*} (S : Finset ι) (r : ι → ℝ)
    {s : ℝ} (hs : 0 ≤ s) (g k : ℕ)
    (hr : ∀ i ∈ S, 0 < r i) (hmin : ∀ i ∈ S, 1/(2:ℝ)^(g+k) ≤ r i) :
    (∑ i ∈ S, (1/r i)^s) ≤ (S.card:ℝ)*((2:ℝ)^g)^s +
      ∑ j ∈ Finset.range k,
        ((S.filter fun i => r i < 1/(2:ℝ)^(g+j)).card:ℝ)*((2:ℝ)^(g+j+1))^s := by
  classical
  calc
    _ ≤ ∑ i ∈ S, (((2:ℝ)^g)^s+∑ j ∈ Finset.range k,
        if r i < 1/(2:ℝ)^(g+j) then ((2:ℝ)^(g+j+1))^s else 0) :=
      Finset.sum_le_sum (fun i hi => inverse_power_dyadic (hr i hi) hs g k (hmin i hi))
    _ = _ := by
      rw [Finset.sum_add_distrib,Finset.sum_comm]
      simp only [Finset.sum_const,nsmul_eq_mul]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      rw [← Finset.sum_filter]
      simp

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

theorem intervalMin_le (A : ℕ → ℝ) {a t i : ℕ} (hai : a ≤ i) (hit : i ≤ t) :
    intervalMin A a t ≤ A i := finiteMin_le A (Finset.mem_Icc.mpr ⟨hai,hit⟩)

theorem height_nonneg (A : ℕ → ℝ) {a p : ℕ} (hap : a ≤ p) :
    0 ≤ height A a p := sub_nonneg.mpr (intervalMin_le A hap le_rfl)

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

theorem angular_profile_power_weight (m : ℝ → ℝ) {N : ℕ} (hN : 0 < N)
    (s E : ℝ) {g h p : ℕ} (hgh : g ≤ h) (hhp : h ≤ p) :
    (((2:ℝ)^N)^(m p-m h+E)*((2:ℝ)^h)^s)/((2:ℝ)^p)^s ≤
      ((2:ℝ)^N)^(PlanarFalconer.height (fun n : ℕ => m n-s*(n:ℝ)/N) g p+E) := by
  have hp : 0 < (2:ℝ)^N := by positivity
  rw [dyadic_power_rpow_as_R hN h,dyadic_power_rpow_as_R hN p,
    ← Real.rpow_add hp,← Real.rpow_sub hp]
  apply Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num))
  have hh := PlanarFalconer.intervalMin_le (fun n : ℕ => m n-s*(n:ℝ)/N) hgh hhp
  dsimp only [PlanarFalconer.height]
  linarith

theorem angular_profile_power_sum (m : ℝ → ℝ) {N : ℕ} (hN : 0 < N)
    (s E : ℝ) {g p : ℕ} (hgp : g ≤ p) :
    ((((2:ℝ)^N)^(m p-m g+E)*((2:ℝ)^g)^s +
      ∑ j ∈ Finset.range (p-g),
        ((2:ℝ)^N)^(m p-m (g+j)+E)*((2:ℝ)^(g+j+1))^s))/((2:ℝ)^p)^s ≤
      (1+(2:ℝ)^s*(p-g:ℕ))*
        ((2:ℝ)^N)^(PlanarFalconer.height (fun n : ℕ => m n-s*(n:ℝ)/N) g p+E) := by
  let Z := ((2:ℝ)^N)^(PlanarFalconer.height (fun n : ℕ => m n-s*(n:ℝ)/N) g p+E)
  rw [add_div,Finset.sum_div]
  have hbase := angular_profile_power_weight m hN s E (g := g) le_rfl hgp
  have hsum : (∑ j ∈ Finset.range (p-g),
      (((2:ℝ)^N)^(m p-m (g+j)+E)*((2:ℝ)^(g+j+1))^s)/((2:ℝ)^p)^s) ≤
        (p-g:ℕ)*((2:ℝ)^s*Z) := by
    calc
      _ ≤ ∑ _j ∈ Finset.range (p-g), ((2:ℝ)^s*Z) := by
        apply Finset.sum_le_sum
        intro j hj
        have hj' := Finset.mem_range.mp hj
        have hh := angular_profile_power_weight m hN s E (g := g) (h := g+j) (p := p)
          (by omega) (by omega)
        simp only [Nat.cast_add] at hh
        rw [pow_succ,Real.mul_rpow (by positivity) (by positivity)]
        have he : (((2:ℝ)^N)^(m p-m (g+j)+E)*(((2:ℝ)^(g+j))^s*(2:ℝ)^s))/((2:ℝ)^p)^s =
            (2:ℝ)^s*((((2:ℝ)^N)^(m p-m (g+j)+E)*((2:ℝ)^(g+j))^s)/((2:ℝ)^p)^s) := by ring
        rw [he]
        exact mul_le_mul_of_nonneg_left hh (by positivity)
      _ = _ := by simp
  change _ ≤ (1+(2:ℝ)^s*(p-g:ℕ))*Z
  change _ ≤ Z at hbase
  nlinarith

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
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
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

theorem perpendicular_direction_measure {d : ℕ} (ν : Measure (Sphere d))
    {v : Space d} (hv : v ≠ 0) {W L s : ℝ} (hW : 0 < W)
    (hball : ∀ x : Space d, ν {w : Sphere d | dist (w:Space d) x < 3*W/‖v‖} ≤
      ENNReal.ofReal (L*(3*W/‖v‖)^s)) :
    ν {w : Sphere d | ‖perpendicularPart (w:Space d) v‖ ≤ W} ≤
      2*ENNReal.ofReal (L*(3*W/‖v‖)^s) := by
  let u := ‖v‖⁻¹ • v
  have hsmall : 2*W/‖v‖ < 3*W/‖v‖ := by
    apply (div_lt_div_iff_of_pos_right (norm_pos_iff.mpr hv)).mpr
    linarith
  have hsub : {w : Sphere d | ‖perpendicularPart (w:Space d) v‖ ≤ W} ⊆
      {w : Sphere d | dist (w:Space d) u < 3*W/‖v‖} ∪
      {w : Sphere d | dist (w:Space d) (-u) < 3*W/‖v‖} := by
    intro w hw
    rcases perpendicular_direction_two_caps (sphere_norm w) hv hw with h | h
    · exact Or.inl (by simpa only [Set.mem_ofPred_eq,dist_eq_norm,u] using h.trans_lt hsmall)
    · exact Or.inr (by simpa only [Set.mem_ofPred_eq,dist_eq_norm,u,neg_smul] using h.trans_lt hsmall)
  exact (measure_mono hsub).trans ((measure_union_le _ _).trans
    ((add_le_add (hball u) (hball (-u))).trans_eq (by ring)))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_AngularTubeCount
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The mean and exceptional mass of a finite original tube count -/

namespace Falconer
open MeasureTheory Set
open scoped ENNReal

theorem angularTubeEvent_measurable {d : ℕ} (v : Space d) (W : ℝ) :
    MeasurableSet (angularTubeEvent v W) := by
  have hc : Continuous (fun w : Sphere d => v-inner ℝ (w:Space d) v • (w:Space d)) :=
    continuous_const.sub ((continuous_subtype_val.inner (𝕜 := ℝ) continuous_const).smul continuous_subtype_val)
  exact measurableSet_le hc.norm.measurable measurable_const

theorem finiteTubeCount_eq_sum {d : ℕ} {ι : Type*} (S : Finset ι)
    (v : ι → Space d) (W : ℝ) (w : Sphere d) :
    (finiteTubeCount S v W w : ℝ≥0∞) =
      ∑ i ∈ S, (angularTubeEvent (v i) W).indicator (fun _ => (1:ℝ≥0∞)) w := by
  classical
  simp only [finiteTubeCount,Finset.natCast_card_filter,Set.indicator_apply]

theorem finiteTubeCount_measurable {d : ℕ} {ι : Type*} (S : Finset ι)
    (v : ι → Space d) (W : ℝ) :
    Measurable (fun w : Sphere d => (finiteTubeCount S v W w : ℝ≥0∞)) := by
  simp_rw [finiteTubeCount_eq_sum]
  exact Finset.measurable_sum S (fun i _ =>
    measurable_const.indicator (angularTubeEvent_measurable (v i) W))

theorem finiteTubeCount_mean {d : ℕ} {ι : Type*} (S : Finset ι)
    (v : ι → Space d) (W : ℝ) (ν : Measure (Sphere d)) :
    (∫⁻ w, (finiteTubeCount S v W w : ℝ≥0∞) ∂ν) =
      ∑ i ∈ S, ν (angularTubeEvent (v i) W) := by
  simp_rw [finiteTubeCount_eq_sum]
  rw [lintegral_finsetSum S (fun i _ =>
    measurable_const.indicator (angularTubeEvent_measurable (v i) W))]
  apply Finset.sum_congr rfl
  intro i _
  rw [lintegral_indicator_const (angularTubeEvent_measurable (v i) W),one_mul]

theorem finiteTubeCount_exceptional {d : ℕ} {ι : Type*} (S : Finset ι)
    (v : ι → Space d) (W : ℝ) (ν : Measure (Sphere d))
    {T : ℝ≥0∞} (hT : T ≠ 0) (hTfin : T ≠ ⊤) :
    ν {w | T < (finiteTubeCount S v W w : ℝ≥0∞)} ≤
      (∑ i ∈ S, ν (angularTubeEvent (v i) W))/T := by
  have hsub : {w | T < (finiteTubeCount S v W w : ℝ≥0∞)} ⊆
      {w | T ≤ (finiteTubeCount S v W w : ℝ≥0∞)} := by
    intro w hw
    exact (show T < (finiteTubeCount S v W w : ℝ≥0∞) from hw).le
  apply (measure_mono hsub).trans
  rw [← finiteTubeCount_mean S v W ν]
  exact meas_ge_le_lintegral_div (finiteTubeCount_measurable S v W).aemeasurable hT hTfin

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_AngularTubeMean
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Tube-count means for a spherical law with a finite-scale ball bound -/

namespace Falconer
open MeasureTheory Set Metric
open scoped ENNReal

theorem sphere_ball_bound_extended {d : ℕ} (ν : Measure (Sphere d))
    {δ L s : ℝ} (hmass : ν univ ≤ 1) (hL : 1 ≤ L) (hs : 0 ≤ s)
    (hball : ∀ x : Space d, ∀ r : ℝ, δ ≤ r → r ≤ 1 →
      ν {w : Sphere d | dist (w:Space d) x < r} ≤ ENNReal.ofReal (L*r^s))
    (x : Space d) {r : ℝ} (hr : δ ≤ r) :
    ν {w : Sphere d | dist (w:Space d) x < r} ≤ ENNReal.ofReal (L*r^s) := by
  by_cases hr₁ : r ≤ 1
  · exact hball x r hr hr₁
  · have hpow : 1 ≤ r^s := Real.one_le_rpow (le_of_not_ge hr₁) hs
    have hprod : 1 ≤ L*r^s := one_le_mul_of_one_le_of_one_le hL hpow
    exact (measure_mono (subset_univ _)).trans (hmass.trans
      (by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hprod))

theorem tube_mean_inverse_power {d : ℕ} {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (a : ι) (v : ι → Space d) (ν : Measure (Sphere d))
    {δ W L s : ℝ} (hW : 0 < W) (hL : 1 ≤ L) (hs : 0 ≤ s) (hmass : ν univ ≤ 1)
    (hball : ∀ x : Space d, ∀ r : ℝ, δ ≤ r → r ≤ 1 →
      ν {w : Sphere d | dist (w:Space d) x < r} ≤ ENNReal.ofReal (L*r^s))
    (hv : ∀ i ∈ S.erase a, v i ≠ 0)
    (hscale : ∀ i ∈ S.erase a, δ ≤ 3*W/‖v i‖) :
    (∫⁻ w, (finiteTubeCount S v W w : ℝ≥0∞) ∂ν) ≤
      1+ENNReal.ofReal (2*L*(3*W)^s*(∑ i ∈ S.erase a, (1/‖v i‖)^s)) := by
  classical
  have hL₀ : 0 ≤ L := zero_le_one.trans hL
  have hsum : (∑ i ∈ S.erase a, 2*ENNReal.ofReal (L*(3*W/‖v i‖)^s)) =
      ENNReal.ofReal (2*L*(3*W)^s*(∑ i ∈ S.erase a, (1/‖v i‖)^s)) := by
    rw [Finset.mul_sum,ENNReal.ofReal_sum_of_nonneg]
    · apply Finset.sum_congr rfl
      intro i hi
      have he : 2*ENNReal.ofReal (L*(3*W/‖v i‖)^s) =
          ENNReal.ofReal (2*(L*(3*W/‖v i‖)^s)) := by
        rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
        norm_num
      rw [he]
      congr 1
      rw [Real.div_rpow (by positivity : 0 ≤ 3*W) (norm_nonneg _),
        one_div,Real.inv_rpow (norm_nonneg _)]
      ring
    · intro i _
      positivity
  rw [finiteTubeCount_mean]
  calc
    _ ≤ ∑ i ∈ insert a (S.erase a), ν (angularTubeEvent (v i) W) :=
      Finset.sum_le_sum_of_subset (by intro i hi; by_cases h : i=a <;> simp [h,hi])
    _ = ν (angularTubeEvent (v a) W)+∑ i ∈ S.erase a, ν (angularTubeEvent (v i) W) :=
      Finset.sum_insert (Finset.notMem_erase a S)
    _ ≤ 1+∑ i ∈ S.erase a, 2*ENNReal.ofReal (L*(3*W/‖v i‖)^s) := by
      apply add_le_add ((measure_mono (subset_univ _)).trans hmass)
      apply Finset.sum_le_sum
      intro i hi
      exact perpendicular_direction_measure ν (hv i hi) hW
        (fun x => sphere_ball_bound_extended ν hmass hL hs hball x (hscale i hi))
    _ = _ := by rw [hsum]

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
-- module Solutions.OAIQ088_FD.Falconer_Fourier_FourierLebesgue
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory ComplexConjugate
open scoped ENNReal NNReal RealInnerProductSpace FourierTransform

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

theorem sourceFourier_integral_swap (μ : Measure V) [IsFiniteMeasure μ]
    (f : V → ℂ) (hf : Integrable f) :
    (∫ ξ, f ξ * sourceFourier μ ξ) = ∫ x, 𝓕 f x ∂μ := by
  have hi : Integrable (fun z : V × V =>
      f z.1 * Complex.exp (⟪z.2, (-(2*Real.pi)) • z.1⟫ * Complex.I))
      (volume.prod μ) := by
    apply (hf.norm.comp_fst μ).mono
    · exact hf.aestronglyMeasurable.comp_fst.mul (by fun_prop)
    · filter_upwards with z
      simp [Complex.norm_exp]
  simp only [sourceFourier, charFun_apply, ← integral_const_mul]
  rw [integral_integral_swap hi]
  apply integral_congr_ae
  filter_upwards with x
  rw [Real.fourier_eq']
  apply integral_congr_ae
  filter_upwards with ξ
  simp only [inner_smul_right, Complex.ofReal_mul, Complex.ofReal_neg,
    Complex.ofReal_ofNat, smul_eq_mul, real_inner_comm x ξ]
  ring_nf

theorem sourceFourier_difference (μ : Measure V) [IsFiniteMeasure μ] (ξ : V) :
    sourceFourier (μ ∗ μ.map (fun x => -x)) ξ = (‖sourceFourier μ ξ‖^2 : ℂ) := by
  have hr := charFun_map_smul (μ := μ) (-1 : ℝ) ((-(2*Real.pi)) • ξ)
  simp only [neg_one_smul, charFun_neg] at hr
  rw [sourceFourier, charFun_conv, hr, Complex.mul_conj]
  exact_mod_cast Complex.normSq_eq_norm_sq _

theorem gaussian_lebesgue_integrable {b : ℝ} (hb : 0 < b) :
    Integrable (fun ξ : V => Real.exp (-b * ‖ξ‖^2)) := by
  have h := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
    (V := V) (b := (b : ℂ)) hb 0 (0 : V)
  simpa [Complex.norm_exp, ← Complex.ofReal_pow] using h.norm

theorem source_gaussian_fourier {b : ℝ} (hb : 0 < b) (x : V) :
    𝓕 (fun ξ : V => (Real.exp (-b * ‖ξ‖^2) : ℂ)) x =
      ((Real.pi / b)^(Module.finrank ℝ V / 2 : ℝ) *
        Real.exp (-(Real.pi^2 / b) * ‖x‖^2) : ℝ) := by
  have he : (fun ξ : V => (Real.exp (-b * ‖ξ‖^2) : ℂ)) =
      (fun ξ : V => Complex.exp (-(b : ℂ) * ‖ξ‖^2)) := by
    funext ξ
    push_cast
    rfl
  rw [he, fourier_gaussian_innerProductSpace (b := (b : ℂ)) hb,
    Complex.ofReal_mul, ← Complex.ofReal_div,
    Complex.ofReal_cpow (by positivity)]
  push_cast
  congr 1
  congr 1
  ring

theorem gaussian_lebesgue_square (μ : Measure V) [IsFiniteMeasure μ]
    {b : ℝ} (hb : 0 < b) :
    (∫ ξ : V, Real.exp (-b * ‖ξ‖^2) * ‖sourceFourier μ ξ‖^2) =
      (Real.pi/b)^(Module.finrank ℝ V / 2 : ℝ) *
        ∫ x, ∫ y, Real.exp (-(Real.pi^2/b) * ‖x-y‖^2) ∂μ ∂μ := by
  let ρ := μ ∗ μ.map (fun x => -x)
  have hf : Integrable (fun ξ : V => (Real.exp (-b * ‖ξ‖^2) : ℂ)) :=
    (gaussian_lebesgue_integrable (V := V) hb).ofReal
  have h := sourceFourier_integral_swap ρ _ hf
  simp only [ρ, sourceFourier_difference, source_gaussian_fourier hb] at h
  have hconv : (∫ z : V, Real.exp (-(Real.pi^2/b) * ‖z‖^2) ∂ρ) =
      ∫ x, ∫ y, Real.exp (-(Real.pi^2/b) * ‖x-y‖^2) ∂μ ∂μ := by
    rw [show ρ = μ ∗ μ.map (fun x => -x) from rfl, integral_conv]
    · apply integral_congr_ae
      filter_upwards with x
      rw [integral_map (by fun_prop) (by fun_prop)]
      simp only [sub_eq_add_neg]
    · apply (integrable_const (1 : ℝ)).mono (by fun_prop)
      filter_upwards with z
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), norm_one]
      apply Real.exp_le_one_iff.mpr
      exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (div_nonneg (sq_nonneg _) hb.le)) (sq_nonneg _)
  have hc : (∫ ξ : V, (Real.exp (-b * ‖ξ‖^2) * ‖sourceFourier μ ξ‖^2 : ℝ)) =
      ∫ x, (Real.pi/b)^(Module.finrank ℝ V / 2 : ℝ) *
        Real.exp (-(Real.pi^2/b) * ‖x‖^2) ∂ρ := by
    apply Complex.ofReal_injective
    simpa only [← Complex.ofReal_pow, ← Complex.ofReal_mul, integral_complex_ofReal] using h
  rw [hc, integral_const_mul, hconv]

theorem gaussian_sourceFourier_integrable (μ : Measure V) [IsFiniteMeasure μ]
    {b : ℝ} (hb : 0 < b) :
    Integrable (fun ξ : V => Real.exp (-b*‖ξ‖^2)*‖sourceFourier μ ξ‖^2) := by
  apply ((gaussian_lebesgue_integrable (V := V) hb).mul_const ((μ.real univ)^2)).mono
  · unfold sourceFourier
    fun_prop
  · filter_upwards with ξ
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity),
      Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_charFun_le _) 2

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
-- module Solutions.OAIQ088_FD.Falconer_Angular_SphereNormalization
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Measurable sphere normalization with a fixed value at zero -/

namespace Falconer
open Set MeasureTheory NormedSpace
variable {d : ℕ}

theorem normalizeToSphere_measurable (w₀ : Sphere d) :
    Measurable (normalizeToSphere w₀) := by
  apply Measurable.subtype_mk
  exact Measurable.ite (by simp)
    measurable_const (measurable_id.norm.inv.smul measurable_id)

end Falconer

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

theorem classLeaves_disjoint (L : Finset (CellPath d))
    (f : CellPath d → List ℕ) {T U : List ℕ} (h : T ≠ U) :
    Disjoint (classLeaves L f T) (classLeaves L f U) := by
  classical
  apply Finset.disjoint_left.mpr
  intro p hp hq
  exact h ((Finset.mem_filter.mp hp).2.symm.trans (Finset.mem_filter.mp hq).2)

theorem leafUnion_classes (Q : DyadicCube d) (L : Finset (CellPath d))
    (f : CellPath d → List ℕ) :
    (⋃ T ∈ L.image f, leafUnion Q (classLeaves L f T)) = leafUnion Q L := by
  classical
  ext z
  constructor
  · intro hz
    obtain ⟨T,_,hz⟩ := mem_iUnion₂.mp hz
    obtain ⟨p,hp,hz⟩ := mem_iUnion₂.mp hz
    exact mem_iUnion₂.mpr ⟨p,(Finset.mem_filter.mp hp).1,hz⟩
  · intro hz
    obtain ⟨p,hp,hz⟩ := mem_iUnion₂.mp hz
    exact mem_iUnion₂.mpr ⟨f p,Finset.mem_image.mpr ⟨p,hp,rfl⟩,
      mem_iUnion₂.mpr ⟨p,by simp [classLeaves,hp],hz⟩⟩

theorem class_mass_sum (Q : DyadicCube d) (hQ : 0 < Q.side) (μ : Measure (Space d))
    {N : ℕ} {L : Finset (CellPath d)} (hL : L ⊆ cubePaths d N)
    (f : CellPath d → List ℕ) :
    (∑ T ∈ L.image f, classMeasure Q μ L f T univ) = μ (leafUnion Q L) := by
  classical
  simp only [classMeasure, Measure.restrict_apply_univ]
  rw [← leafUnion_classes Q L f]
  symm
  apply measure_biUnion_finset
  · intro T _ U _ hne
    exact leafUnion_disjoint Q hQ (fun _ hp => hL (Finset.mem_filter.mp hp).1)
      (fun _ hp => hL (Finset.mem_filter.mp hp).1) (classLeaves_disjoint L f hne)
  · intro T _; exact leafUnion_measurable Q _

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

theorem normalizedClass_apply (Q : DyadicCube d) (μ : Measure (Space d))
    (L : Finset (CellPath d)) (f : CellPath d → List ℕ) (T : List ℕ)
    (S : Set (Space d)) :
    normalizedClass Q μ L f T S =
      (μ (leafUnion Q (classLeaves L f T)))⁻¹ *
        μ (S ∩ leafUnion Q (classLeaves L f T)) := by
  simp only [normalizedClass, classMeasure, univ_inter,
    Measure.smul_apply, smul_eq_mul,
    Measure.restrict_apply' (leafUnion_measurable Q _)]

end Falconer.Regularization

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

end Falconer.Regularization

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
-- module Solutions.OAIQ088_FD.Falconer_Recursion_ProfilePacking
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Local occupied-cell counts from the original class profiles -/

namespace Falconer.Regularization
open Set MeasureTheory Metric
open scoped ENNReal
variable {d : ℕ}

theorem occupied_center_count_le (Q : DyadicCube d) (hQ : 0 < Q.side)
    (ν : Measure (Space d)) [IsFiniteMeasure ν] {g p : ℕ} (hgp : g ≤ p)
    (x : Space d) {r C lo hi : ℝ} (hC : 0 ≤ C) (hr : r ≤ C*(Q.side/(2:ℝ)^g))
    (hlo : 0 < lo) (hhi : 0 ≤ hi)
    (hfine : ∀ q ∈ cubePaths d p, 0 < ν (Q.descendant q).carrier →
      lo ≤ (ν (Q.descendant q).carrier).toReal)
    (hcoarse : ∀ q ∈ cubePaths d g, 0 < ν (Q.descendant q).carrier →
      (ν (Q.descendant q).carrier).toReal ≤ hi) :
    ((occupiedCenterCells Q ν p x r).card:ℝ) ≤
      ((2*Nat.ceil (2*C+2*Real.sqrt d)+1)^d:ℕ)*hi/lo := by
  classical
  let S := occupiedCenterCells Q ν p x r
  let T := S.image (List.take g)
  have hS : S ⊆ cubePaths d p := Finset.filter_subset _ _
  have hT : T ⊆ cubePaths d g := by
    intro c hc
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hc
    have hl := (mem_cubePaths _ _ _).mp (hS hq)
    simp only [mem_cubePaths,List.length_take,hl,min_eq_left hgp]
  have hpos {q : CellPath d} (hq : q ∈ S) : 0 < ν (Q.descendant q).carrier :=
    (Finset.mem_filter.mp hq).2.1
  have hparent (q : CellPath d) : (Q.descendant q).carrier ⊆
      (Q.descendant (q.take g)).carrier := descendant_subset_take Q hQ q g
  have hcard : (T.card:ℝ) ≤ ((2*Nat.ceil (2*C+2*Real.sqrt d)+1)^d:ℕ) := by
    exact_mod_cast dyadic_ancestor_ball_count Q hQ S
      (fun q hq => (mem_cubePaths _ _ _).mp (hS hq)) hgp x hC hr
      (fun q hq => (mem_ball.mp (Finset.mem_filter.mp hq).2.2).le)
  have hcover : leafUnion Q S ⊆ leafUnion Q T := by
    intro z hz
    obtain ⟨q,hq,hz⟩ := mem_iUnion₂.mp hz
    exact mem_iUnion₂.mpr ⟨q.take g,Finset.mem_image.mpr ⟨q,hq,rfl⟩,hparent q hz⟩
  have hsum : (S.card:ℝ)*lo ≤ (T.card:ℝ)*hi := by
    calc
      _ = ∑ _q ∈ S, lo := by simp
      _ ≤ ∑ q ∈ S, (ν (Q.descendant q).carrier).toReal :=
        Finset.sum_le_sum (fun q hq => hfine q (hS hq) (hpos hq))
      _ = (ν (leafUnion Q S)).toReal := (restriction_total_mass_real Q hQ ν hS).symm
      _ ≤ (ν (leafUnion Q T)).toReal :=
        ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hcover)
      _ = ∑ q ∈ T, (ν (Q.descendant q).carrier).toReal := restriction_total_mass_real Q hQ ν hT
      _ ≤ ∑ _q ∈ T, hi := by
        apply Finset.sum_le_sum
        intro c hc
        apply hcoarse c (hT hc)
        obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hc
        exact (hpos hq).trans_le (measure_mono (hparent q))
      _ = _ := by simp
  exact (le_div_iff₀ hlo).mpr (hsum.trans (mul_le_mul_of_nonneg_right hcard hhi))

theorem sourceClass_local_count (Q : DyadicCube d) (hQ : 0 < Q.side)
    (μ : Measure (Space d)) [IsProbabilityMeasure μ] {N B : ℕ} (hN : 0 < N) (hB : 0 < B)
    {lam : ℝ} (hwidth : (B:ℝ) ≤ lam*(N:ℝ))
    (hlarge : (2:ℝ)^(N/B+2) ≤ ((2:ℝ)^N)^lam)
    {p₀ : CellPath d} (hp₀ : p₀ ∈ regularizationLeaves Q μ N)
    {g p : ℕ} (hgp : g ≤ p) (hpN : p ≤ N) (x : Space d) {C : ℝ} (hC : 0 ≤ C) :
    ((occupiedCenterCells Q (sourceClass Q μ N B p₀) p x (C/(2:ℝ)^g)).card:ℝ) ≤
      ((2*Nat.ceil (2*(C/Q.side)+2*Real.sqrt d)+1)^d:ℕ)*((2:ℝ)^N)^
        (sourceProfile Q μ N B p₀ p-sourceProfile Q μ N B p₀ g+2*((d:ℝ)+1)*lam) := by
  have : IsProbabilityMeasure (sourceClass Q μ N B p₀) :=
    regularization_class_probability Q hQ μ N B hp₀
  let R : ℝ := (2:ℝ)^N
  have hRp : 0 < R := by dsimp [R]; positivity
  have hh := occupied_center_count_le Q hQ (sourceClass Q μ N B p₀) hgp x
    (C := C/Q.side) (by positivity) (r := C/(2:ℝ)^g)
    (div_mul_div_cancel₀ (ne_of_gt hQ)).ge
    (lo := R^(-((d:ℝ)+1)*lam)*R^(-sourceProfile Q μ N B p₀ p)) (by positivity)
    (hi := R^(((d:ℝ)+1)*lam)*R^(-sourceProfile Q μ N B p₀ g)) (by positivity)
    (fun q hq hpos => (sourceClass_occupied_comparison Q hQ μ hN hB hwidth hlarge hp₀ hpN
      ((mem_cubePaths _ _ _).mp hq) hpos).1)
    (fun q hq hpos => (sourceClass_occupied_comparison Q hQ μ hN hB hwidth hlarge hp₀ (hgp.trans hpN)
      ((mem_cubePaths _ _ _).mp hq) hpos).2)
  apply hh.trans_eq
  rw [mul_div_assoc]
  congr 1
  rw [← Real.rpow_add hRp,← Real.rpow_add hRp,← Real.rpow_sub hRp]
  congr 1
  ring

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_ParallelProfile
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The inverse-power sum for actual parallel-test centers

The critical kernel exponent is arbitrary here so the application can
use d/2. Every counted center belongs to the original normalized class.
-/

namespace Falconer.Regularization
open Set Metric MeasureTheory
variable {d : ℕ}

theorem parallel_inverse_power_sum (Q : DyadicCube d) (hQ : Q.side = 1)
    (ρ : Measure (Space d)) {s : ℝ} (hs : 0 ≤ s) {g p : ℕ} (hgp : g ≤ p)
    {P : CellPath d} (hP : P.length = p) :
    (∑ c ∈ (parallelTestCells Q ρ g p P).erase P,
      (1/dist (Q.descendant c).center (Q.descendant P).center)^s) ≤
      ((parallelTestCells Q ρ g p P).card:ℝ)*((2:ℝ)^g)^s +
        ∑ j ∈ Finset.range (p-g),
          ((occupiedCenterCells Q ρ p (Q.descendant P).center (1/(2:ℝ)^(g+j))).card:ℝ)*
            ((2:ℝ)^(g+j+1))^s := by
  classical
  let S := (parallelTestCells Q ρ g p P).erase P
  let r := fun c => dist (Q.descendant c).center (Q.descendant P).center
  have hside : 0 < Q.side := by rw [hQ]; norm_num
  have hsep (c : CellPath d) (hc : c ∈ S) : 1/(2:ℝ)^p ≤ r c := by
    have hc' := Finset.mem_of_mem_erase hc
    have hl := (mem_cubePaths _ _ _).mp (Finset.mem_filter.mp hc').1
    simpa only [hQ] using Q.centers_separated hside hl hP (Finset.ne_of_mem_erase hc)
  have hr (c : CellPath d) (hc : c ∈ S) : 0 < r c :=
    lt_of_lt_of_le (by positivity : 0 < 1/(2:ℝ)^p) (hsep c hc)
  have hh := sum_inverse_power_dyadic S r hs g (p-g) hr (fun c hc => by
    simpa only [Nat.add_sub_of_le hgp] using hsep c hc)
  apply hh.trans
  apply add_le_add
  · apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact_mod_cast Finset.card_le_card (Finset.erase_subset P (parallelTestCells Q ρ g p P))
  · apply Finset.sum_le_sum
    intro j _
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    apply Nat.cast_le.mpr
    apply Finset.card_le_card
    intro c hc
    obtain ⟨hc,hrc⟩ := Finset.mem_filter.mp hc
    have hc' := Finset.mem_filter.mp (Finset.mem_of_mem_erase hc)
    exact Finset.mem_filter.mpr ⟨hc'.1,hc'.2.1,hrc⟩

theorem sourceClass_parallel_inverse_power (Q : DyadicCube d) (hQ : Q.side = 1)
    (μ : Measure (Space d)) [IsProbabilityMeasure μ] {N B : ℕ} (hN : 0 < N) (hB : 0 < B)
    {lam s : ℝ} (hs : 0 ≤ s) (hwidth : (B:ℝ) ≤ lam*(N:ℝ))
    (hlarge : (2:ℝ)^(N/B+2) ≤ ((2:ℝ)^N)^lam)
    {p₀ : CellPath d} (hp₀ : p₀ ∈ regularizationLeaves Q μ N)
    {g p : ℕ} (hgp : g ≤ p) (hpN : p ≤ N) {P : CellPath d} (hP : P.length = p) :
    (∑ c ∈ (parallelTestCells Q (sourceClass Q μ N B p₀) g p P).erase P,
      (1/dist (Q.descendant c).center (Q.descendant P).center)^s)/((2:ℝ)^p)^s ≤
      (parallelPackingConstant d:ℝ)*(1+(2:ℝ)^s*(p-g:ℕ))*
        ((2:ℝ)^N)^(PlanarFalconer.height
          (fun n : ℕ => sourceProfile Q μ N B p₀ n-s*(n:ℝ)/N) g p+2*((d:ℝ)+1)*lam) := by
  have hside : 0 < Q.side := by rw [hQ]; norm_num
  let m := sourceProfile Q μ N B p₀
  let E := 2*((d:ℝ)+1)*lam
  let ρ := sourceClass Q μ N B p₀
  let R : ℝ := (2:ℝ)^N
  let D : ℝ := parallelPackingConstant d
  have hpack {g p : ℕ} (hgp : g ≤ p) (hpN : p ≤ N) (x : Space d) {C : ℝ} (hC : 0 ≤ C) :=
    sourceClass_local_count Q hside μ hN hB hwidth hlarge hp₀ hgp hpN x hC
  have hbase : ((parallelTestCells Q ρ g p P).card:ℝ) ≤ D*R^(m p-m g+E) := by
    have hh := hpack hgp hpN (Q.descendant P).center (show 0 ≤ 10*((d:ℝ)+1) by positivity)
    simp only [hQ,div_one] at hh
    apply hh.trans
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    dsimp only [D,parallelPackingConstant]
    have he : 2*(10*((d:ℝ)+1)) = 20*((d:ℝ)+1) := by ring
    rw [he]
    exact_mod_cast le_max_left ((2*Nat.ceil (20*((d:ℝ)+1)+2*Real.sqrt d)+1)^d)
      ((2*Nat.ceil (2+2*Real.sqrt d)+1)^d)
  have hterm (j : ℕ) (hj : j ∈ Finset.range (p-g)) :
      ((occupiedCenterCells Q ρ p (Q.descendant P).center (1/(2:ℝ)^(g+j))).card:ℝ) ≤
        D*R^(m p-m (g+j)+E) := by
    have hj' := Finset.mem_range.mp hj
    have hh := hpack (g := g+j) (p := p) (by omega) hpN (Q.descendant P).center
      (show (0:ℝ) ≤ 1 by norm_num)
    simp only [hQ,div_one,mul_one,Nat.cast_add] at hh
    apply hh.trans
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    dsimp only [D,parallelPackingConstant]
    exact_mod_cast le_max_right ((2*Nat.ceil (20*((d:ℝ)+1)+2*Real.sqrt d)+1)^d)
      ((2*Nat.ceil (2+2*Real.sqrt d)+1)^d)
  have hsum := parallel_inverse_power_sum Q hQ ρ hs hgp hP
  have hb : (∑ c ∈ (parallelTestCells Q ρ g p P).erase P,
      (1/dist (Q.descendant c).center (Q.descendant P).center)^s) ≤
      D*(R^(m p-m g+E)*((2:ℝ)^g)^s+
        ∑ j ∈ Finset.range (p-g), R^(m p-m (g+j)+E)*((2:ℝ)^(g+j+1))^s) := by
    apply hsum.trans
    rw [mul_add,Finset.mul_sum]
    apply add_le_add
    · simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hbase (by positivity : 0 ≤ ((2:ℝ)^g)^s)
    · apply Finset.sum_le_sum
      intro j hj
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (hterm j hj)
        (by positivity : 0 ≤ ((2:ℝ)^(g+j+1))^s)
  apply (div_le_div_of_nonneg_right hb (by positivity)).trans
  rw [mul_div_assoc]
  have hh := mul_le_mul_of_nonneg_left (angular_profile_power_sum m hN s E hgp)
    (show 0 ≤ D by dsimp [D]; positivity)
  simpa only [D,R,m,E,mul_assoc] using hh

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ParallelGood
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Literal parallel-test good sets and their directional buffer -/

namespace Falconer
open Set MeasureTheory Metric
open scoped ENNReal

namespace Regularization
variable {d : ℕ}

theorem parallelGoodSet_measurable (Q : DyadicCube d) (ρ : Measure (Space d))
    (g p : ℕ) (P : CellPath d) (W T : ℝ) :
    MeasurableSet (parallelGoodSet Q ρ g p P W T) := by
  classical
  unfold parallelGoodSet
  split_ifs
  · exact measurableSet_le (finiteTubeCount_measurable _ _ _) measurable_const
  · exact MeasurableSet.empty

theorem parallelGoodSet_exceptional (Q : DyadicCube d) (ρ : Measure (Space d))
    (g p : ℕ) (P : CellPath d) (hocc : 0 < ρ (Q.descendant P).carrier)
    (W : ℝ) {T : ℝ} (hT : 0 < T) (ν : Measure (Sphere d)) :
    ν (parallelGoodSet Q ρ g p P W T)ᶜ ≤
      (∫⁻ w, (parallelTestCount Q ρ g p P W w : ℝ≥0∞) ∂ν)/ENNReal.ofReal T := by
  classical
  have he : (parallelGoodSet Q ρ g p P W T)ᶜ =
      {w | ENNReal.ofReal T < (parallelTestCount Q ρ g p P W w : ℝ≥0∞)} := by
    ext w
    simp only [parallelGoodSet,ite_eq_left hocc,mem_compl_iff,mem_ofPred_eq,not_le]
  rw [he]
  exact (finiteTubeCount_exceptional _ _ _ ν (by positivity) ENNReal.ofReal_ne_top).trans_eq
    (by rw [← finiteTubeCount_mean]; rfl)

end Regularization
end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ParallelMean
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Parallel-test averages for the original regularized class -/

namespace Falconer.Regularization
open Set Metric MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem dyadic_center_difference_bound (Q : DyadicCube d) (hQ : 0 < Q.side)
    (p q : CellPath d) :
    ‖(Q.descendant p).center-(Q.descendant q).center‖ ≤ Real.sqrt d*Q.side := by
  rw [← dist_eq_norm]
  exact Q.dist_le hQ.le
    (Q.descendant_subset p ((Q.descendant p).center_mem (Q.descendant_side_pos hQ p)))
    (Q.descendant_subset q ((Q.descendant q).center_mem (Q.descendant_side_pos hQ q)))

theorem sourceClass_parallel_mean (Q : DyadicCube d) (hQ : Q.side = 1)
    (μ : Measure (Space d)) [IsProbabilityMeasure μ] {N B : ℕ} (hN : 0 < N) (hB : 0 < B)
    {lam s : ℝ} (hs : 0 ≤ s) (hwidth : (B:ℝ) ≤ lam*(N:ℝ))
    (hlarge : (2:ℝ)^(N/B+2) ≤ ((2:ℝ)^N)^lam)
    {p₀ : CellPath d} (hp₀ : p₀ ∈ regularizationLeaves Q μ N)
    {g p : ℕ} (hgp : g ≤ p) (hpN : p ≤ N) {P : CellPath d} (hP : P.length = p)
    (ν : Measure (Sphere d)) {δ W L : ℝ} (hδ : 0 ≤ δ) (hW : 0 < W)
    (hL : 1 ≤ L) (hmass : ν univ ≤ 1) (hscale : δ*Real.sqrt d ≤ 3*W)
    (hball : ∀ x : Space d, ∀ r : ℝ, δ ≤ r → r ≤ 1 →
      ν {w : Sphere d | dist (w:Space d) x < r} ≤ ENNReal.ofReal (L*r^s)) :
    (∫⁻ w, (parallelTestCount Q (sourceClass Q μ N B p₀) g p P W w : ℝ≥0∞) ∂ν) ≤
      1+ENNReal.ofReal (2*L*(3*W)^s*((2:ℝ)^p)^s*(parallelPackingConstant d:ℝ)*
        (1+(2:ℝ)^s*(p-g:ℕ))*((2:ℝ)^N)^(PlanarFalconer.height
          (fun n : ℕ => sourceProfile Q μ N B p₀ n-s*(n:ℝ)/N) g p+2*((d:ℝ)+1)*lam)) := by
  classical
  let S := parallelTestCells Q (sourceClass Q μ N B p₀) g p P
  let v := fun c => (Q.descendant c).center-(Q.descendant P).center
  have hside : 0 < Q.side := by rw [hQ]; norm_num
  have hv (c : CellPath d) (hc : c ∈ S.erase P) : v c ≠ 0 := by
    have hc' := Finset.mem_of_mem_erase hc
    have hl := (mem_cubePaths _ _ _).mp (Finset.mem_filter.mp hc').1
    have hh := Q.centers_separated hside hl hP (Finset.ne_of_mem_erase hc)
    intro hz
    have hz' : dist (Q.descendant c).center (Q.descendant P).center = 0 := by
      rw [dist_eq_norm]
      exact norm_eq_zero.mpr hz
    rw [hz'] at hh
    exact (not_le_of_gt (by positivity : 0 < Q.side/(2:ℝ)^p)) hh
  have hsc (c : CellPath d) (hc : c ∈ S.erase P) : δ ≤ 3*W/‖v c‖ := by
    apply (le_div_iff₀ (norm_pos_iff.mpr (hv c hc))).mpr
    have hh := dyadic_center_difference_bound Q hside c P
    rw [hQ,mul_one] at hh
    exact (mul_le_mul_of_nonneg_left hh hδ).trans hscale
  have hm := tube_mean_inverse_power S P v ν hW hL hs hmass hball hv hsc
  apply hm.trans
  apply add_le_add le_rfl
  apply ENNReal.ofReal_le_ofReal
  have hi := sourceClass_parallel_inverse_power Q hQ μ hN hB hs hwidth hlarge hp₀ hgp hpN hP
  have hip := (div_le_iff₀ (by positivity : 0 < ((2:ℝ)^p)^s)).mp hi
  have hh := mul_le_mul_of_nonneg_left hip (by positivity : 0 ≤ 2*L*(3*W)^s)
  calc
    _ = 2*L*(3*W)^s * ∑ c ∈ (parallelTestCells Q (sourceClass Q μ N B p₀) g p P).erase P,
        (1/dist (Q.descendant c).center (Q.descendant P).center)^s := by
      simp only [S,v,dist_eq_norm]
    _ ≤ _ := hh
    _ = _ := by ring

theorem parallel_mean_width_cancellation {A s : ℝ} (hA : 0 ≤ A) (p : ℕ) :
    (3*(A/(2:ℝ)^p))^s*((2:ℝ)^p)^s = (3*A)^s := by
  rw [← Real.mul_rpow (by positivity) (by positivity)]
  congr 1
  field_simp

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ParallelNumerics
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Scale cancellation and absorption for the parallel-test average -/

namespace Falconer.Regularization

theorem parallel_mean_scale_identity {R : ℝ} (hR : 0 < R)
    (d : ℕ) (s sig K D n : ℝ) (p : ℕ) :
    2*R^sig*(3*((2*R^(500*sig))/(2:ℝ)^p))^s*((2:ℝ)^p)^s*D*
        (1+(2:ℝ)^s*n)*R^(K+2*((d:ℝ)+1)*sig) =
      (2*(6:ℝ)^s*D*(1+(2:ℝ)^s*n))*R^(K+(2*((d:ℝ)+1)+1+500*s)*sig) := by
  have hc := parallel_mean_width_cancellation (show 0 ≤ 2*R^(500*sig) by positivity) p (s := s)
  have he : 3*(2*R^(500*sig)) = 6*R^(500*sig) := by ring
  calc
    _ = 2*R^sig*((3*((2*R^(500*sig))/(2:ℝ)^p))^s*((2:ℝ)^p)^s)*D*
        (1+(2:ℝ)^s*n)*R^(K+2*((d:ℝ)+1)*sig) := by ring
    _ = 2*R^sig*((6:ℝ)^s*R^(500*sig*s))*D*(1+(2:ℝ)^s*n)*R^(K+2*((d:ℝ)+1)*sig) := by
      rw [hc,he,Real.mul_rpow (by norm_num : (0:ℝ) ≤ 6) (by positivity),← Real.rpow_mul hR.le]
    _ = (2*(6:ℝ)^s*D*(1+(2:ℝ)^s*n))*(R^sig*R^(500*sig*s)*R^(K+2*((d:ℝ)+1)*sig)) := by ring
    _ = _ := by
      rw [← Real.rpow_add hR,← Real.rpow_add hR]
      congr 2
      ring

theorem parallel_coefficient_bound {D s n : ℝ} (hD : 0 ≤ D) (_hn : 0 ≤ n)
    {N : ℕ} (hnN : n ≤ N) :
    2*(6:ℝ)^s*D*(1+(2:ℝ)^s*n) ≤
      (2*(6:ℝ)^s*D*(1+(2:ℝ)^s))*(1+2*(N:ℝ)) := by
  have hp : 0 ≤ (2:ℝ)^s := by positivity
  have hN : 0 ≤ (N:ℝ) := Nat.cast_nonneg N
  have hh : 1+(2:ℝ)^s*n ≤ (1+(2:ℝ)^s)*(1+2*(N:ℝ)) := by
    nlinarith [mul_le_mul_of_nonneg_left hnN hp,mul_nonneg hp hN]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hh (show 0 ≤ 2*(6:ℝ)^s*D by positivity)

theorem one_add_power_absorb {R E sig : ℝ} (hR : 1 ≤ R) (hE : 0 ≤ E)
    (htwo : 2 ≤ R^sig) : 1+R^E ≤ R^(E+sig) := by
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have hp : 1 ≤ R^E := Real.one_le_rpow hR hE
  calc
    _ ≤ 2*R^E := by linarith
    _ ≤ R^sig*R^E := mul_le_mul_of_nonneg_right htwo (by positivity)
    _ = _ := by rw [← Real.rpow_add hRp]; congr 1; ring

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ParallelScaleMean
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The manuscript parallel-test mean at its actual width -/

namespace Falconer.Regularization
open Set MeasureTheory Metric
open scoped ENNReal
variable {d : ℕ}

theorem sourceClass_parallel_scale_mean (Q : DyadicCube d) (hQ : Q.side = 1)
    (μ : Measure (Space d)) [IsProbabilityMeasure μ] {N B : ℕ} (hN : 0 < N) (hB : 0 < B)
    {sig s : ℝ} (hsig : 0 < sig) (hs : 0 ≤ s) (hwidth : (B:ℝ) ≤ sig*(N:ℝ))
    (hlarge : (2:ℝ)^(N/B+2) ≤ ((2:ℝ)^N)^sig)
    (hroot : Real.sqrt d ≤ ((2:ℝ)^N)^(500*sig))
    {p₀ : CellPath d} (hp₀ : p₀ ∈ regularizationLeaves Q μ N)
    {g p : ℕ} (hgp : g ≤ p) (hpN : p ≤ N) {P : CellPath d} (hP : P.length = p)
    (ν : Measure (Sphere d)) (hmass : ν univ ≤ 1)
    (hball : ∀ x : Space d, ∀ r : ℝ, ((2:ℝ)^N)^(-1:ℝ) ≤ r → r ≤ 1 →
      ν {w : Sphere d | dist (w:Space d) x < r} ≤ ENNReal.ofReal (((2:ℝ)^N)^sig*r^s)) :
    (∫⁻ w, (parallelTestCount Q (sourceClass Q μ N B p₀) g p P
      ((2*((2:ℝ)^N)^(500*sig))/(2:ℝ)^p) w : ℝ≥0∞) ∂ν) ≤
      1+ENNReal.ofReal ((2*(6:ℝ)^s*(parallelPackingConstant d:ℝ)*(1+(2:ℝ)^s*(p-g:ℕ)))*
        ((2:ℝ)^N)^(PlanarFalconer.height
          (fun n : ℕ => sourceProfile Q μ N B p₀ n-s*(n:ℝ)/N) g p+
            (2*((d:ℝ)+1)+1+500*s)*sig)) := by
  let R : ℝ := (2:ℝ)^N
  have hR : 1 ≤ R := one_le_pow₀ (by norm_num)
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have hp2 : (2:ℝ)^p ≤ R := pow_le_pow_right₀ (by norm_num) hpN
  have hscale : R^(-1:ℝ)*Real.sqrt d ≤ 3*((2*R^(500*sig))/(2:ℝ)^p) := by
    calc
      _ = Real.sqrt d/R := by rw [Real.rpow_neg_one]; ring
      _ ≤ R^(500*sig)/R := div_le_div_of_nonneg_right hroot hRp.le
      _ ≤ R^(500*sig)/(2:ℝ)^p := div_le_div_of_nonneg_left (by positivity) (by positivity) hp2
      _ ≤ _ := by
        have hh : 0 ≤ R^(500*sig)/(2:ℝ)^p := by positivity
        nlinarith [show 3*((2*R^(500*sig))/(2:ℝ)^p) = 6*(R^(500*sig)/(2:ℝ)^p) by ring]
  have hm := sourceClass_parallel_mean Q hQ μ hN hB hs hwidth hlarge hp₀ hgp hpN hP ν
    (by positivity : 0 ≤ R^(-1:ℝ)) (by positivity : 0 < (2*R^(500*sig))/(2:ℝ)^p)
    (Real.one_le_rpow hR hsig.le) hmass hscale hball
  rw [parallel_mean_scale_identity hRp] at hm
  exact hm

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_AllDimensionalParallelExceptional
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Uniform exceptional mass of all-dimensional parallel tests

The numerical linear-subpower estimate is independent of dimension.
The parallel tests use the original class centers and the original sphere law.
-/

namespace Falconer.Regularization
open Set MeasureTheory Metric
open scoped ENNReal
variable {d : ℕ}

theorem uniform_parallel_exceptional {sig : ℝ} (hsig : 0 < sig) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (Q : DyadicCube d), Q.side = 1 →
      ∀ (μ : Measure (Space d)) [IsProbabilityMeasure μ], ∀ B : ℕ,
      0 < B → (B:ℝ) ≤ sig*(N:ℝ) → (2:ℝ)^(N/B+2) ≤ ((2:ℝ)^N)^sig →
      ∀ p₀ ∈ regularizationLeaves Q μ N, ∀ g p : ℕ, g ≤ p → p ≤ N →
      ∀ P : CellPath d, P.length = p →
      0 < sourceClass Q μ N B p₀ (Q.descendant P).carrier →
      ∀ ν : Measure (Sphere d), ν univ ≤ 1 →
      (∀ x : Space d, ∀ r : ℝ, ((2:ℝ)^N)^(-1:ℝ) ≤ r → r ≤ 1 →
        ν {w : Sphere d | dist (w:Space d) x < r} ≤
          ENNReal.ofReal (((2:ℝ)^N)^sig*r^((d:ℝ)/2))) →
      ν (parallelGoodSet Q (sourceClass Q μ N B p₀) g p P
        ((2*((2:ℝ)^N)^(500*sig))/(2:ℝ)^p)
        (((2:ℝ)^N)^(PlanarFalconer.height
          (fun n : ℕ => sourceProfile Q μ N B p₀ n-((d:ℝ)/2)*(n:ℝ)/N) g p+
            1000*((d:ℝ)+1)*sig)))ᶜ ≤ ENNReal.ofReal (((2:ℝ)^N)^(-sig)) := by
  let s : ℝ := (d:ℝ)/2
  let D : ℝ := parallelPackingConstant d
  let A : ℝ := 2*((d:ℝ)+1)+1+500*s
  let C : ℝ := 2*(6:ℝ)^s*D*(1+(2:ℝ)^s)
  have hs : 0 ≤ s := by dsimp [s]; positivity
  obtain ⟨N₁,hpoly⟩ := PlanarFalconer.fixed_linear_subpower C (by dsimp [C,D]; positivity) hsig
  obtain ⟨N₂,hroot⟩ := fixed_constant_absorbed (by positivity : 0 < 500*sig) (Real.sqrt d)
  obtain ⟨N₃,htwo⟩ := fixed_constant_absorbed hsig 2
  refine ⟨max 1 (max N₁ (max N₂ N₃)),?_⟩
  intro N hN Q hQ μ inst B hB hwidth hlarge p₀ hp₀ g p hgp hpN P hP hocc ν hmass hball
  have hNp : 0 < N := lt_of_lt_of_le (by omega : 0 < 1) ((le_max_left _ _).trans hN)
  have hN₁ : N₁ ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hN₂ : N₂ ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hN))
  have hN₃ : N₃ ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hN))
  let R : ℝ := (2:ℝ)^N
  let K := PlanarFalconer.height (fun n : ℕ => sourceProfile Q μ N B p₀ n-s*(n:ℝ)/N) g p
  let W := (2*R^(500*sig))/(2:ℝ)^p
  have hR : 1 ≤ R := one_le_pow₀ (by norm_num)
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have hK : 0 ≤ K := PlanarFalconer.height_nonneg _ hgp
  have hm := sourceClass_parallel_scale_mean Q hQ μ hNp hB hsig hs hwidth hlarge
    (hroot N hN₂) hp₀ hgp hpN hP ν hmass hball
  have hcoef : 2*(6:ℝ)^s*D*(1+(2:ℝ)^s*(p-g:ℕ)) ≤ R^sig := by
    apply (parallel_coefficient_bound (N := N) (show 0 ≤ D by dsimp [D]; positivity)
      (Nat.cast_nonneg (p-g)) (by exact_mod_cast (Nat.sub_le p g).trans hpN)).trans
    exact hpoly N hN₁
  have hmean : (∫⁻ w, (parallelTestCount Q (sourceClass Q μ N B p₀) g p P W w : ℝ≥0∞) ∂ν) ≤
      ENNReal.ofReal (R^(K+(A+2)*sig)) := by
    apply hm.trans
    calc
      _ ≤ 1+ENNReal.ofReal (R^sig*R^(K+A*sig)) :=
        add_le_add le_rfl (ENNReal.ofReal_le_ofReal
          (mul_le_mul_of_nonneg_right hcoef (by positivity)))
      _ = ENNReal.ofReal (1+R^(K+(A+1)*sig)) := by
        rw [← Real.rpow_add hRp]
        have he : sig+(K+A*sig) = K+(A+1)*sig := by ring
        rw [he,ENNReal.ofReal_add (by positivity) (by positivity),ENNReal.ofReal_one]
      _ ≤ ENNReal.ofReal (R^(K+(A+2)*sig)) := by
        apply ENNReal.ofReal_le_ofReal
        have he : 0 ≤ K+(A+1)*sig := by dsimp [A]; positivity
        have hh := one_add_power_absorb hR he (htwo N hN₃)
        have heq : K+(A+1)*sig+sig = K+(A+2)*sig := by ring
        simpa only [heq] using hh
  apply (parallelGoodSet_exceptional Q (sourceClass Q μ N B p₀) g p P hocc W
    (show 0 < R^(K+1000*((d:ℝ)+1)*sig) by positivity) ν).trans
  apply (ENNReal.div_le_div_right hmean _).trans
  rw [← ENNReal.ofReal_div_of_pos (by positivity),← Real.rpow_sub hRp]
  apply ENNReal.ofReal_le_ofReal
  apply Real.rpow_le_rpow_of_exponent_le hR
  dsimp [A,s]
  have hd : 0 ≤ (d:ℝ) := Nat.cast_nonneg d
  nlinarith

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_DistanceFourierDifference
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory ComplexConjugate

theorem integral_distanceDifferenceMeasure (μ : Measure ℝ) (F : ℝ → ℂ)
    (hF : StronglyMeasurable F) :
    (∫ s, F s ∂distanceDifferenceMeasure μ) = ∫ z, F (z.1-z.2) ∂μ.prod μ :=
  integral_map_of_stronglyMeasurable (by fun_prop) hF

theorem charFun_distanceDifferenceMeasure (μ : Measure ℝ) [IsFiniteMeasure μ] (r : ℝ) :
    charFun (distanceDifferenceMeasure μ) r = (‖charFun μ r‖^2:ℂ) := by
  rw [charFun_apply_real,integral_distanceDifferenceMeasure μ _ (by fun_prop)]
  have he : (fun z : ℝ × ℝ => Complex.exp ((r*(z.1-z.2):ℝ)*Complex.I)) =
      fun z => Complex.exp ((r*z.1:ℝ)*Complex.I) *
        conj (Complex.exp ((r*z.2:ℝ)*Complex.I)) := by
    funext z
    rw [← Complex.exp_conj,← Complex.exp_add]
    congr 1
    simp only [map_mul,Complex.conj_ofReal,Complex.conj_I,Complex.ofReal_sub,Complex.ofReal_mul]
    ring
  simp only [Complex.ofReal_mul] at he
  rw [he,integral_prod_mul (fun x : ℝ => Complex.exp ((r:ℂ)*x*Complex.I))
    (fun y : ℝ => conj (Complex.exp ((r:ℂ)*y*Complex.I))),integral_conj,← charFun_apply_real,Complex.mul_conj]
  exact_mod_cast Complex.normSq_eq_norm_sq (charFun μ r)

theorem integral_charFun_scale_swap (μ ν : Measure ℝ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (A : ℝ) :
    (∫ s, charFun μ (A*s) ∂ν) = ∫ r, charFun ν (A*r) ∂μ := by
  simp only [charFun_apply_real]
  rw [integral_integral_swap]
  · apply integral_congr_ae
    filter_upwards with r
    apply integral_congr_ae
    filter_upwards with s
    congr 2
    push_cast
    ring
  · exact (integrable_const (1:ℝ)).mono (by fun_prop)
      (by filter_upwards with z; simp [Function.uncurry,Complex.norm_exp])

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_DistanceSincKernel
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem distanceSincKernel_nonneg (u s : ℝ) : 0 ≤ distanceSincKernel u s := sq_nonneg _

theorem distanceSincKernel_le_one (u s : ℝ) : distanceSincKernel u s ≤ 1 := by
  have h := Real.abs_sinc_le_one (u*s)
  dsimp [distanceSincKernel]
  exact (sq_abs _).symm.trans_le ((pow_le_pow_left₀ (abs_nonneg _) h 2).trans_eq (by norm_num))

theorem continuous_distanceSincKernel (u : ℝ) : Continuous (distanceSincKernel u) :=
  (Real.continuous_sinc.comp (continuous_const.mul continuous_id)).pow 2

theorem exists_distanceSincKernel : ∃ u : ℝ, 0 < u ∧ 2*u ≤ 1 ∧
    ∀ s : ℝ, |s| ≤ 100 → (1/4:ℝ) ≤ distanceSincKernel u s := by
  obtain ⟨δ,hδ,hclose⟩ := Metric.continuousAt_iff.mp
    Real.continuous_sinc.continuousAt (1/2:ℝ) (by norm_num)
  let u := min (δ/201) (1/4:ℝ)
  have hu : 0 < u := lt_min (by positivity) (by norm_num)
  refine ⟨u,hu,by have := min_le_right (δ/201) (1/4:ℝ); dsimp [u]; linarith,?_⟩
  intro s hs
  have hb : |u*s| < δ := by
    rw [abs_mul,abs_of_pos hu]
    have h₁ := mul_le_mul_of_nonneg_left hs hu.le
    have h₂ := min_le_left (δ/201) (1/4:ℝ)
    dsimp [u] at h₁ ⊢
    nlinarith
  have hc := hclose (show dist (u*s) 0 < δ by simpa [Real.dist_eq] using hb)
  rw [Real.dist_eq,Real.sinc_zero] at hc
  have hp : 1/2 < Real.sinc (u*s) := by have := (abs_lt.mp hc).1; linarith
  dsimp [distanceSincKernel]
  nlinarith

theorem interval_exp_eq_sinc (u s : ℝ) :
    (∫ r in -u..u, Complex.exp ((r*s:ℝ)*Complex.I)) =
      ((2*u*Real.sinc (u*s):ℝ):ℂ) := by
  by_cases hs : s = 0
  · simp [hs]
    ring
  have h := intervalIntegral.integral_comp_mul_right
    (fun t : ℝ => Complex.exp (t*Complex.I)) (a := -u) (b := u) hs
  rw [neg_mul,integral_exp_mul_I_eq_sinc] at h
  rw [h]
  simp only [Complex.real_smul,Complex.ofReal_inv,Complex.ofReal_mul,
    Complex.ofReal_ofNat]
  have hs' : (s:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs
  field_simp

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_DistanceFrequencyBox
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal

theorem distanceFrequencyBox_mass {u : ℝ} (hu : 0 ≤ u) :
    distanceFrequencyBox u univ = ENNReal.ofReal (2*u) := by
  simp only [distanceFrequencyBox,Measure.restrict_apply_univ,Real.volume_Ioc]
  apply (ENNReal.ofReal_eq_ofReal_iff (sub_nonneg.mpr (neg_le_self hu))
    (mul_nonneg (by norm_num) hu)).2
  ring

theorem distanceFrequencyBox_charFun {u : ℝ} (hu : 0 ≤ u) (s : ℝ) :
    charFun (distanceFrequencyBox u) s = ((2*u*Real.sinc (u*s):ℝ):ℂ) := by
  rw [charFun_apply_real]
  change (∫ r in Ioc (-u) u, Complex.exp ((s:ℂ)*r*Complex.I)) = _
  rw [← intervalIntegral.integral_of_le (by linarith : -u ≤ u)]
  simpa only [Complex.ofReal_mul,mul_comm (s:ℂ)] using interval_exp_eq_sinc u s

theorem distanceFrequencyBox_difference_charFun {u : ℝ} (hu : 0 ≤ u) (s : ℝ) :
    charFun (distanceDifferenceMeasure (distanceFrequencyBox u)) s =
      (((2*u)^2 * distanceSincKernel u s:ℝ):ℂ) := by
  rw [charFun_distanceDifferenceMeasure,distanceFrequencyBox_charFun hu,
    Complex.norm_real,Real.norm_eq_abs,← Complex.ofReal_pow,sq_abs]
  congr 1
  dsimp [distanceSincKernel]
  ring

theorem distanceFrequencyBox_difference_le_volume {u : ℝ} (hu : 0 ≤ u) :
    distanceDifferenceMeasure (distanceFrequencyBox u) ≤ ENNReal.ofReal (2*u) • volume := by
  apply Measure.le_iff.mpr
  intro S hS
  rw [distanceDifferenceMeasure,Measure.map_apply (by fun_prop) hS,
    Measure.prod_apply (hS.preimage (by fun_prop))]
  calc
    _ ≤ ∫⁻ x, volume S ∂distanceFrequencyBox u := by
      apply lintegral_mono
      intro x
      calc
        _ ≤ volume ((fun y : ℝ => x-y) ⁻¹' S) := Measure.restrict_apply_le _ _
        _ = volume S := (volume.measurePreserving_sub_left x).measure_preimage hS.nullMeasurableSet
    _ = _ := by
      rw [lintegral_const,distanceFrequencyBox_mass hu,Measure.smul_apply,smul_eq_mul,mul_comm]

theorem distanceFrequencyBox_difference_supported {u : ℝ} :
    ∀ᵐ s ∂distanceDifferenceMeasure (distanceFrequencyBox u), s ∈ Icc (-2*u) (2*u) := by
  rw [distanceDifferenceMeasure,ae_map_iff (by fun_prop) (by measurability)]
  have hm : ∀ᵐ x ∂distanceFrequencyBox u, x ∈ Ioc (-u) u := ae_restrict_mem measurableSet_Ioc
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hm,
    Measure.quasiMeasurePreserving_snd.ae hm] with z hz₁ hz₂
  exact ⟨by linarith [hz₁.1,hz₂.2],by linarith [hz₁.2,hz₂.1]⟩

theorem distanceFrequencyBox_difference_le_band {u : ℝ} (hu : 0 ≤ u) :
    distanceDifferenceMeasure (distanceFrequencyBox u) ≤
      ENNReal.ofReal (2*u) • volume.restrict (Icc (-2*u) (2*u)) := by
  calc
    _ = (distanceDifferenceMeasure (distanceFrequencyBox u)).restrict (Icc (-2*u) (2*u)) :=
      (Measure.restrict_eq_self_of_ae_mem distanceFrequencyBox_difference_supported).symm
    _ ≤ (ENNReal.ofReal (2*u) • volume).restrict (Icc (-2*u) (2*u)) :=
      Measure.restrict_mono (Subset.refl _) (distanceFrequencyBox_difference_le_volume hu)
    _ = _ := Measure.restrict_smul _ _ _

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_DistanceSincSpectralIdentity
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem distanceSincKernel_integrable (μ : Measure ℝ) [IsFiniteMeasure μ] (u A : ℝ) :
    Integrable (fun s => distanceSincKernel u (A*s)) μ := by
  apply (integrable_const (1:ℝ)).mono
  · exact ((continuous_distanceSincKernel u).comp
      (continuous_const.mul continuous_id)).aestronglyMeasurable
  · filter_upwards with s
    rw [Real.norm_eq_abs,abs_of_nonneg (distanceSincKernel_nonneg _ _),norm_one]
    exact distanceSincKernel_le_one _ _

theorem charFun_sq_integrable_finite (μ ν : Measure ℝ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (A : ℝ) :
    Integrable (fun r => ‖charFun μ (A*r)‖^2) ν := by
  apply (integrable_const ((μ.real univ)^2)).mono
  · exact ((measurable_charFun.comp (measurable_const.mul measurable_id)).norm.pow_const 2).aestronglyMeasurable
  · filter_upwards with r
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _),Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_charFun_le _) 2

theorem distanceSincKernel_spectral_identity (μ : Measure ℝ) [IsFiniteMeasure μ]
    {u : ℝ} (hu : 0 ≤ u) (A : ℝ) :
    (2*u)^2 * (∫ s, distanceSincKernel u (A*s) ∂distanceDifferenceMeasure μ) =
      ∫ r, ‖charFun μ (A*r)‖^2 ∂distanceDifferenceMeasure (distanceFrequencyBox u) := by
  have h := integral_charFun_scale_swap
    (distanceDifferenceMeasure (distanceFrequencyBox u)) (distanceDifferenceMeasure μ) A
  simp only [distanceFrequencyBox_difference_charFun hu,charFun_distanceDifferenceMeasure] at h
  have hr : (∫ s, (2*u)^2 * distanceSincKernel u (A*s) ∂distanceDifferenceMeasure μ) =
      ∫ r, ‖charFun μ (A*r)‖^2 ∂distanceDifferenceMeasure (distanceFrequencyBox u) := by
    apply Complex.ofReal_injective
    simpa only [← Complex.ofReal_pow,integral_complex_ofReal] using h
  rwa [integral_const_mul] at hr

theorem distanceSincKernel_frequency_bound (μ : Measure ℝ) [IsFiniteMeasure μ]
    {u : ℝ} (hu : 0 < u) (A : ℝ) :
    (2*u) * (∫ s, distanceSincKernel u (A*s) ∂distanceDifferenceMeasure μ) ≤
      ∫ r in Icc (-2*u) (2*u), ‖charFun μ (A*r)‖^2 := by
  have hi := charFun_sq_integrable_finite μ (volume.restrict (Icc (-2*u) (2*u))) A
  have hb := integral_mono_measure (distanceFrequencyBox_difference_le_band hu.le)
    (Filter.Eventually.of_forall (fun r => sq_nonneg ‖charFun μ (A*r)‖))
    (hi.smul_measure ENNReal.ofReal_ne_top)
  rw [integral_smul_measure,ENNReal.toReal_ofReal (by positivity : 0 ≤ 2*u),smul_eq_mul,
    ← distanceSincKernel_spectral_identity μ hu.le A] at hb
  nlinarith

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_DistanceSincCollision
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem distanceSincKernel_collision_bound (ν : Measure ℝ) [IsFiniteMeasure ν]
    {u A : ℝ} (hA : 0 < A)
    (hu : ∀ s : ℝ, |s| ≤ 100 → (1/4:ℝ) ≤ distanceSincKernel u s) :
    ν.real {s : ℝ | |s| ≤ 100/A} ≤ 4 * ∫ s, distanceSincKernel u (A*s) ∂ν := by
  let S : Set ℝ := {s | |s| ≤ 100/A}
  have hS : MeasurableSet S := by dsimp [S]; measurability
  have hb := integral_mono ((integrable_const (1/4:ℝ)).indicator hS)
    (distanceSincKernel_integrable ν u A) (show ∀ s, S.indicator (fun _ => (1/4:ℝ)) s ≤
      distanceSincKernel u (A*s) from by
      intro s
      by_cases hs : s ∈ S
      · rw [Set.indicator_of_mem hs]
        apply hu
        rw [abs_mul,abs_of_pos hA]
        have h := (le_div_iff₀ hA).mp hs
        nlinarith
      · rw [Set.indicator_of_notMem hs]
        exact distanceSincKernel_nonneg _ _)
  rw [integral_indicator_const _ hS,smul_eq_mul] at hb
  dsimp [S] at hb
  linarith

theorem integral_scale_Icc (f : ℝ → ℝ) {A u : ℝ} (hA : 0 < A) (hu : 0 ≤ u) :
    A * (∫ r in Icc (-u) u, f (A*r)) = ∫ r in Icc (-A*u) (A*u), f r := by
  rw [integral_Icc_eq_integral_Ioc,integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : -u ≤ u),
    ← intervalIntegral.integral_of_le (by nlinarith : -A*u ≤ A*u)]
  have h := intervalIntegral.smul_integral_comp_mul_left f (a := -u) (b := u) A
  simpa only [smul_eq_mul,mul_neg,neg_mul] using h

theorem distanceSincKernel_scaled_frequency_bound (μ : Measure ℝ) [IsFiniteMeasure μ]
    {u A : ℝ} (hu : 0 < u) (hu₁ : 2*u ≤ 1) (hA : 0 < A) :
    A*(2*u) * (∫ s, distanceSincKernel u (A*s) ∂distanceDifferenceMeasure μ) ≤
      ∫ r in Icc (-A) A, ‖charFun μ r‖^2 := by
  have h := mul_le_mul_of_nonneg_left (distanceSincKernel_frequency_bound μ hu A) hA.le
  rw [show -2*u = -(2*u) by ring,integral_scale_Icc (fun r => ‖charFun μ r‖^2) hA (by positivity)] at h
  have hs : Icc (-A*(2*u)) (A*(2*u)) ⊆ Icc (-A) A := by
    intro r hr
    constructor <;> nlinarith [hr.1,hr.2]
  have hi : IntegrableOn (fun r => ‖charFun μ r‖^2) (Icc (-A) A) := by
    simpa only [one_mul,IntegrableOn] using charFun_sq_integrable_finite μ (volume.restrict (Icc (-A) A)) 1
  have hb := integral_mono_measure (Measure.restrict_mono hs le_rfl)
    (Filter.Eventually.of_forall (fun r => sq_nonneg ‖charFun μ r‖)) hi
  apply le_trans ?_ hb
  simpa only [mul_assoc] using h

theorem finite_measure_distance_collision_fourier : ∃ C : ℝ, 0 < C ∧
    ∀ (μ : Measure ℝ) [IsFiniteMeasure μ] (A : ℝ), 0 < A →
      A * (μ.prod μ).real {z : ℝ × ℝ | |z.1-z.2| ≤ 100/A} ≤
        C * ∫ r in Icc (-A) A, ‖charFun μ r‖^2 := by
  obtain ⟨u,hu,hu₁,hkernel⟩ := exists_distanceSincKernel
  refine ⟨2/u,by positivity,?_⟩
  intro μ _ A hA
  have hl := distanceSincKernel_collision_bound (distanceDifferenceMeasure μ) hA hkernel
  have hh := distanceSincKernel_scaled_frequency_bound μ hu hu₁ hA
  have he : (distanceDifferenceMeasure μ).real {s : ℝ | |s| ≤ 100/A} =
      (μ.prod μ).real {z : ℝ × ℝ | |z.1-z.2| ≤ 100/A} := by
    simp only [measureReal_def,distanceDifferenceMeasure]
    rw [Measure.map_apply (by fun_prop) (by measurability)]
    rfl
  rw [he] at hl
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hu).mpr
  have h₁ := mul_le_mul_of_nonneg_left hl (show 0 ≤ A*u by positivity)
  have h₂ := mul_le_mul_of_nonneg_left hh (by norm_num : (0:ℝ) ≤ 2)
  nlinarith

end PlanarFalconer

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

theorem profileDrop_nonneg (m : ℝ → ℝ) (N : ℕ) (s : ℝ) {p t : ℕ} (hpt : p ≤ t) :
    0 ≤ profileDrop m N s p t := by
  exact sub_nonneg.mpr (PlanarFalconer.intervalMin_le _ le_rfl hpt)

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
-- module Solutions.OAIQ088_FD.Falconer_Geometry_FiniteScaleBall
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite-scale balls and the support of the actual rescaled laws -/

namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal

variable {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]

theorem finite_scale_ball_extend (μ : Measure X) {δ K s : ℝ}
    (hmass : μ univ ≤ 1) (hK : 1 ≤ K) (hs : 0 ≤ s)
    (hball : ∀ x : X, ∀ r : ℝ, δ ≤ r → r ≤ 1 →
      μ (ball x r) ≤ ENNReal.ofReal (K*r^s)) :
    ∀ x : X, ∀ r : ℝ, δ ≤ r → μ (ball x r) ≤ ENNReal.ofReal (K*r^s) := by
  intro x r hr
  by_cases hr₁ : r ≤ 1
  · exact hball x r hr hr₁
  · have hp : 1 ≤ K*r^s := one_le_mul_of_one_le_of_one_le hK
      (Real.one_le_rpow (le_of_not_ge hr₁) hs)
    exact (measure_mono (subset_univ _)).trans (hmass.trans
      (by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp))

namespace Regularization
variable {d : ℕ}

theorem rescaled_cell_norm_bound (Q : DyadicCube d) (hQ : Q.side = 1)
    (P : CellPath d) {z : Space d} (hz : z ∈ (Q.descendant P).carrier) :
    ‖cellScaleMap P.length (Q.descendant P).center z‖ ≤ Real.sqrt d := by
  have hs : 0 < (Q.descendant P).side := by rw [Q.descendant_side,hQ]; positivity
  have hdist := (Q.descendant P).dist_le hs.le hz ((Q.descendant P).center_mem hs)
  rw [cellScaleMap,norm_smul,Real.norm_eq_abs,abs_of_pos (by positivity : 0 < (2:ℝ)^P.length)]
  rw [dist_eq_norm] at hdist
  calc
    _ ≤ (2:ℝ)^P.length*(Real.sqrt d*(Q.descendant P).side) :=
      mul_le_mul_of_nonneg_left hdist (by positivity)
    _ = Real.sqrt d := by rw [Q.descendant_side,hQ]; field_simp

theorem rescaled_conditional_support (Q : DyadicCube d) (hQ : Q.side = 1)
    (ρ : Measure (Space d)) (P : CellPath d) :
    ∀ᵐ z ∂Measure.map (cellScaleMap P.length (Q.descendant P).center)
      (ProbabilityTheory.cond ρ (Q.descendant P).carrier), ‖z‖ ≤ Real.sqrt d := by
  rw [ae_map_iff (cellScaleMap_continuous _ _).measurable.aemeasurable
    (isClosed_le continuous_norm continuous_const).measurableSet]
  exact ProbabilityTheory.ae_cond_of_forall_mem (Q.descendant P).measurable
    (fun z hz => rescaled_cell_norm_bound Q hQ P hz)

end Regularization
end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_FrequencyGeometry
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Frequency-ball preimages under the radial map -/

namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem scaled_unit_difference {w u : E} (hw : ‖w‖ = 1) (hu : ‖u‖ = 1)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a*‖w-u‖ ≤ 2*‖a • w-b • u‖ := by
  have hab : |a-b| ≤ ‖a • w-b • u‖ := by
    have h := abs_norm_sub_norm_le (a • w) (b • u)
    simpa only [norm_smul,Real.norm_eq_abs,abs_of_nonneg ha,abs_of_nonneg hb,hw,hu,mul_one] using h
  have he : a • (w-u) = (a • w-b • u)+(b-a) • u := by module
  have h := norm_add_le (a • w-b • u) ((b-a) • u)
  rw [← he,norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg ha,hu,mul_one,
    abs_sub_comm b a] at h
  linarith

theorem radial_direction_close {w : E} (hw : ‖w‖ = 1) {v : E}
    (hv : v ≠ 0) {t r B : ℝ} (hB : 0 < B) (ht : B ≤ |t|)
    (hr : ‖t • w-v‖ < r) :
    ‖w-‖v‖⁻¹ • v‖ < 2*r/B ∨ ‖w-(-‖v‖⁻¹ • v)‖ < 2*r/B := by
  have hvp := norm_pos_iff.mpr hv
  let u := ‖v‖⁻¹ • v
  have hu : ‖u‖ = 1 := by
    simp only [u,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hvp),inv_mul_cancel₀ hvp.ne']
  have hvu : ‖v‖ • u = v := by simp [u,smul_smul,hvp.ne']
  rcases le_total 0 t with ht₀ | ht₀
  · left
    have h := scaled_unit_difference hw hu ht₀ (norm_nonneg v)
    rw [hvu] at h
    rw [abs_of_nonneg ht₀] at ht
    apply (lt_div_iff₀ hB).mpr
    have hn := norm_nonneg (w-u)
    nlinarith
  · right
    rw [neg_smul]
    change ‖w-(-u)‖ < 2*r/B
    have h := scaled_unit_difference (show ‖-w‖ = 1 by simpa only [norm_neg] using hw)
      hu (neg_nonneg.mpr ht₀) (norm_nonneg v)
    rw [hvu,neg_smul,smul_neg,neg_neg] at h
    have he : ‖-w-u‖ = ‖w-(-u)‖ := by
      rw [show -w-u = -(w-(-u)) by abel,norm_neg]
    rw [he] at h
    rw [abs_of_nonpos ht₀] at ht
    apply (lt_div_iff₀ hB).mpr
    have hn := norm_nonneg (w-(-u))
    nlinarith

theorem radial_norm_interval {w v : E} (hw : ‖w‖ = 1) {t r : ℝ}
    (hr : ‖t • w-v‖ < r) : |t| ∈ Ioo (‖v‖-r) (‖v‖+r) := by
  have h := (abs_norm_sub_norm_le (t • w) v).trans_lt hr
  simp only [norm_smul,Real.norm_eq_abs,hw,mul_one] at h
  rw [abs_lt] at h
  constructor <;> linarith [h.1,h.2]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Measures_FrequencyMeasure
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Ball bounds for an actual radial frequency-shell pushforward -/

namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal

theorem radialWindow_mem {a r t : ℝ} (h : |t| ∈ Ioo (a-r) (a+r)) :
    t ∈ radialWindow a r := by
  rcases le_total 0 t with ht | ht
  · left
    simpa only [abs_of_nonneg ht] using h
  · right
    rw [abs_of_nonpos ht] at h
    exact ⟨by linarith [h.2],by linarith [h.1]⟩

theorem radialWindow_volume {a r : ℝ} (hr : 0 ≤ r) :
    volume (radialWindow a r) ≤ ENNReal.ofReal (4*r) := by
  calc
    _ ≤ volume (Ioo (a-r) (a+r))+volume (Ioo (-a-r) (-a+r)) := measure_union_le _ _
    _ = ENNReal.ofReal (4*r) := by
      rw [Real.volume_Ioo,Real.volume_Ioo,← ENNReal.ofReal_add (by linarith) (by linarith)]
      congr 1
      ring

theorem radial_frequency_preimage {d : ℕ} {B r : ℝ} (hB : 0 < B) (_hr : 0 < r)
    (v : Space d) :
    radialFrequencyMap ⁻¹' ball v r ∩ (radialFrequencyAnnulus B ×ˢ (univ : Set (Sphere d))) ⊆
      radialWindow ‖v‖ r ×ˢ
        ({w : Sphere d | dist (w:Space d) (‖v‖⁻¹ • v) < 2*r/B} ∪
         {w : Sphere d | dist (w:Space d) (-‖v‖⁻¹ • v) < 2*r/B}) := by
  rintro ⟨t,w⟩ ⟨hball,hann⟩
  have hdist : ‖t • (w:Space d)-v‖ < r := by
    simpa only [mem_preimage,mem_ball,dist_eq_norm,radialFrequencyMap] using hball
  refine ⟨radialWindow_mem (radial_norm_interval (sphere_norm w) hdist),?_⟩
  by_cases hv : v = 0
  · left
    have ht : B < r := by
      have hh : |t| < r := by
        simpa only [hv,sub_zero,norm_smul,Real.norm_eq_abs,sphere_norm,mul_one] using hdist
      exact hann.1.1.trans_lt hh
    simp only [hv,norm_zero,inv_zero,zero_smul,dist_zero_right,sphere_norm,mem_ofPred_eq]
    apply (lt_div_iff₀ hB).mpr
    linarith
  · simpa only [dist_eq_norm,mem_union,mem_ofPred_eq,neg_smul] using
      radial_direction_close (sphere_norm w) hv hB hann.1.1 hdist

theorem radial_frequency_ball_bound {d : ℕ} (ν : Measure (Sphere d)) [IsFiniteMeasure ν]
    {B r δ L s : ℝ} (hB : 0 < B) (hr : 0 < r) (hL : 1 ≤ L) (hs : 0 ≤ s)
    (hmass : ν univ ≤ 1) (hscale : δ ≤ 2*r/B)
    (hball : ∀ x : Space d, ∀ a : ℝ, δ ≤ a → a ≤ 1 →
      ν {w : Sphere d | dist (w:Space d) x < a} ≤ ENNReal.ofReal (L*a^s))
    (v : Space d) :
    radialFrequencyMeasure ν B (ball v r) ≤ ENNReal.ofReal (8*r*L*(2*r/B)^s) := by
  let A := radialFrequencyAnnulus B
  let C := {w : Sphere d | dist (w:Space d) (‖v‖⁻¹ • v) < 2*r/B} ∪
    {w : Sphere d | dist (w:Space d) (-‖v‖⁻¹ • v) < 2*r/B}
  have hν : ν C ≤ 2*ENNReal.ofReal (L*(2*r/B)^s) := by
    calc
      _ ≤ ν {w : Sphere d | dist (w:Space d) (‖v‖⁻¹ • v) < 2*r/B}+
          ν {w : Sphere d | dist (w:Space d) (-‖v‖⁻¹ • v) < 2*r/B} := measure_union_le _ _
      _ ≤ ENNReal.ofReal (L*(2*r/B)^s)+ENNReal.ofReal (L*(2*r/B)^s) :=
        add_le_add (sphere_ball_bound_extended ν hmass hL hs hball _ hscale)
          (sphere_ball_bound_extended ν hmass hL hs hball _ hscale)
      _ = _ := (two_mul _).symm
  have hm : Measurable (@radialFrequencyMap d) := by unfold radialFrequencyMap; fun_prop
  rw [radialFrequencyMeasure,Measure.map_apply hm measurableSet_ball]
  have he : ((volume.restrict A).prod ν) (radialFrequencyMap ⁻¹' ball v r) =
      (volume.prod ν) ((radialFrequencyMap ⁻¹' ball v r) ∩ (A ×ˢ univ)) := by
    rw [Measure.restrict_prod_eq_prod_univ,Measure.restrict_apply (measurableSet_ball.preimage hm)]
  rw [he]
  calc
    _ ≤ (volume.prod ν) (radialWindow ‖v‖ r ×ˢ C) :=
      measure_mono (radial_frequency_preimage hB hr v)
    _ = volume (radialWindow ‖v‖ r)*ν C := Measure.prod_prod _ _
    _ ≤ ENNReal.ofReal (4*r)*(2*ENNReal.ofReal (L*(2*r/B)^s)) :=
      mul_le_mul' (radialWindow_volume hr.le) hν
    _ = _ := by
      rw [show (2:ℝ≥0∞) = ENNReal.ofReal (2:ℝ) by norm_num,
        ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2),
        ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianMass
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Gaussian mass at a finite Frostman scale

Only ball bounds at radii at least `B⁻¹` are used. This is the spatial
Gaussian estimate in the proof of the half-dimensional Fourier estimate.
-/

namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal NNReal

theorem gaussianBallConstant_summable (k : ℕ) :
    Summable (fun n : ℕ => Real.exp (-(n:ℝ))*((n:ℝ)+1)^k) := by
  have h := (summable_nat_add_iff 1).mpr
    (Real.summable_pow_mul_exp_neg_nat_mul k (r := 1) zero_lt_one)
  have he (n : ℕ) : Real.exp (-(n:ℝ))*((n:ℝ)+1)^k =
      Real.exp 1 * (((n+1:ℕ):ℝ)^k*Real.exp (-1*((n+1:ℕ):ℝ))) := by
    have he' : Real.exp 1*Real.exp (-1*((n+1:ℕ):ℝ)) = Real.exp (-(n:ℝ)) := by
      rw [← Real.exp_add]
      congr 1
      push_cast
      ring
    rw [← he']
    push_cast
    ring
  simpa only [he] using h.mul_left (Real.exp 1)

theorem gaussianBallConstant_nonneg (k : ℕ) : 0 ≤ gaussianBallConstant k :=
  tsum_nonneg (fun n => by positivity)

variable {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [BorelSpace X]

omit [MeasurableSpace X] [BorelSpace X] in
theorem gaussian_pointwise_majorant {B : ℝ} (hB : 0 < B) (x y : X) :
    ENNReal.ofReal (Real.exp (-(B*dist x y)^2)) ≤
      ∑' n : ℕ, gaussianMassTerm x B n y := by
  let n := Nat.floor (B*dist x y)
  have hn : (n:ℝ) ≤ B*dist x y := Nat.floor_le (by positivity)
  have hn' : B*dist x y < (n:ℝ)+1 := Nat.lt_floor_add_one _
  have hball : y ∈ ball x (((n:ℝ)+1)/B) := by
    rw [mem_ball,dist_comm,lt_div_iff₀ hB]
    simpa only [mul_comm] using hn'
  have hsq : (n:ℝ) ≤ (n:ℝ)^2 := by
    have hh : n ≤ n^2 := by nlinarith
    exact_mod_cast hh
  have hle : Real.exp (-(B*dist x y)^2) ≤ Real.exp (-(n:ℝ)) := by
    apply Real.exp_le_exp.mpr
    nlinarith [sq_nonneg (B*dist x y-(n:ℝ))]
  calc
    _ ≤ ENNReal.ofReal (Real.exp (-(n:ℝ))) := ENNReal.ofReal_le_ofReal hle
    _ = gaussianMassTerm x B n y := by
      rw [gaussianMassTerm,indicator_of_mem hball]
    _ ≤ _ := ENNReal.le_tsum (f := fun j => gaussianMassTerm x B j y) n

theorem gaussian_mass_bound (μ : Measure X) {B K s : ℝ} {k : ℕ}
    (hB : 0 < B) (hK : 0 ≤ K) (hsk : s ≤ k)
    (hb : ∀ x : X, ∀ r : ℝ, 1/B ≤ r → μ (ball x r) ≤ ENNReal.ofReal (K*r^s))
    (x : X) :
    (∫⁻ y, ENNReal.ofReal (Real.exp (-(B*dist x y)^2)) ∂μ) ≤
      ENNReal.ofReal (K*(1/B)^s*gaussianBallConstant k) := by
  have hterm (n : ℕ) : (∫⁻ y, gaussianMassTerm x B n y ∂μ) ≤
      ENNReal.ofReal (K*(1/B)^s) *
        ENNReal.ofReal (Real.exp (-(n:ℝ))*((n:ℝ)+1)^k) := by
    rw [gaussianMassTerm,lintegral_indicator_const measurableSet_ball]
    have hr : 1/B ≤ ((n:ℝ)+1)/B := by
      exact (div_le_div_iff_of_pos_right hB).mpr (by linarith [Nat.cast_nonneg (α := ℝ) n])
    have hp : (((n:ℝ)+1)/B)^s ≤ (1/B)^s*((n:ℝ)+1)^k := by
      rw [div_eq_mul_inv, Real.mul_rpow (by positivity) (inv_nonneg.mpr hB.le),one_div]
      have hh : ((n:ℝ)+1)^s ≤ ((n:ℝ)+1)^(k:ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith [Nat.cast_nonneg (α := ℝ) n]) hsk
      rw [Real.rpow_natCast] at hh
      nlinarith [Real.rpow_nonneg (inv_nonneg.mpr hB.le) s]
    calc
      _ ≤ ENNReal.ofReal (Real.exp (-(n:ℝ)))*ENNReal.ofReal (K*(((n:ℝ)+1)/B)^s) :=
        mul_le_mul_right (hb x _ hr) _
      _ ≤ ENNReal.ofReal (Real.exp (-(n:ℝ)))*
          ENNReal.ofReal (K*((1/B)^s*((n:ℝ)+1)^k)) := by
        gcongr
      _ = _ := by
        rw [← ENNReal.ofReal_mul (by positivity),← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring
  calc
    _ ≤ ∫⁻ y, ∑' n : ℕ, gaussianMassTerm x B n y ∂μ :=
      lintegral_mono (gaussian_pointwise_majorant hB x)
    _ = ∑' n : ℕ, ∫⁻ y, gaussianMassTerm x B n y ∂μ :=
      lintegral_tsum (fun n => (measurable_const.indicator measurableSet_ball).aemeasurable)
    _ ≤ ∑' n : ℕ, ENNReal.ofReal (K*(1/B)^s)*
        ENNReal.ofReal (Real.exp (-(n:ℝ))*((n:ℝ)+1)^k) := ENNReal.tsum_le_tsum hterm
    _ = _ := by
      rw [ENNReal.tsum_mul_left,← ENNReal.ofReal_tsum_of_nonneg
        (fun n : ℕ => by positivity) (gaussianBallConstant_summable k),
        ← ENNReal.ofReal_mul (by positivity)]
      rfl

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianEnergy
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The all-dimensional Gaussian Fourier energy bound -/

namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal RealInnerProductSpace

variable {d : ℕ}

theorem gaussian_mass_bound_real (μ : Measure (Space d)) {B K s : ℝ} {k : ℕ}
    (hB : 0 < B) (hK : 0 ≤ K) (hsk : s ≤ k)
    (hb : ∀ x : Space d, ∀ r : ℝ, 1/B ≤ r →
      μ (ball x r) ≤ ENNReal.ofReal (K*r^s)) (x : Space d) :
    (∫ y, Real.exp (-(B*dist x y)^2) ∂μ) ≤ K*(1/B)^s*gaussianBallConstant k := by
  rw [integral_eq_lintegral_of_nonneg_ae (by filter_upwards with y; positivity)
    (by fun_prop)]
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top (gaussian_mass_bound μ hB hK hsk hb x)
  rwa [ENNReal.toReal_ofReal (mul_nonneg (mul_nonneg hK (by positivity))
    (gaussianBallConstant_nonneg k))] at h

theorem gaussian_energy_bound (μ : Measure (Space d)) [IsFiniteMeasure μ]
    {B K s : ℝ} {k : ℕ} (hB : 0 < B) (hK : 0 ≤ K) (hsk : s ≤ k)
    (hb : ∀ x : Space d, ∀ r : ℝ, 1/B ≤ r →
      μ (ball x r) ≤ ENNReal.ofReal (K*r^s)) :
    (∫ x, ∫ y, Real.exp (-(B*dist x y)^2) ∂μ ∂μ) ≤
      μ.real univ*(K*(1/B)^s*gaussianBallConstant k) := by
  have hi : Integrable (fun z : Space d × Space d =>
      Real.exp (-(B*dist z.1 z.2)^2)) (μ.prod μ) := by
    apply (integrable_const (1:ℝ)).mono (by fun_prop)
    filter_upwards with z
    rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),norm_one]
    exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (sq_nonneg _))
  calc
    _ ≤ ∫ _ : Space d, K*(1/B)^s*gaussianBallConstant k ∂μ :=
      integral_mono hi.integral_prod_left (integrable_const _)
        (gaussian_mass_bound_real μ hB hK hsk hb)
    _ = _ := by rw [integral_const,smul_eq_mul]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianLocalization
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Gaussian smoothing of a bounded frequency-shell measure -/

namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal

variable {d : ℕ}

theorem gaussian_localization_pointwise {B : ℝ} (hB : 1 ≤ B) (u v : Space d)
    (hv : ‖v‖ ≤ 2*B) :
    Real.exp (-2*(dist u v)^2) ≤
      (Real.exp 1*Real.exp (-‖u‖^2/(16*B^2)))*Real.exp (-(dist u v)^2) := by
  have hB₀ : 0 < B := zero_lt_one.trans_le hB
  have htri : ‖u‖ ≤ dist u v+‖v‖ := by
    simpa only [dist_zero_right] using dist_triangle u v 0
  have hsq : ‖u‖^2 ≤ 2*(dist u v)^2+8*B^2 := by
    have hsum : ‖u‖ ≤ dist u v+2*B := htri.trans (by linarith)
    have ha := sq_nonneg (dist u v-2*B)
    have hb := mul_nonneg (sub_nonneg.mpr hsum) (show 0 ≤ dist u v+2*B+‖u‖ by positivity)
    nlinarith
  have hnum : ‖u‖^2 ≤ (16*B^2)*((dist u v)^2+1) := by
    have hbase : 1 ≤ B^2 := by nlinarith
    have hh := mul_nonneg (show 0 ≤ 16*B^2-2 by linarith) (sq_nonneg (dist u v))
    nlinarith
  have hdiv : ‖u‖^2/(16*B^2) ≤ (dist u v)^2+1 :=
    (div_le_iff₀ (by positivity)).mpr (by nlinarith [hnum])
  rw [← Real.exp_add,← Real.exp_add]
  apply Real.exp_le_exp.mpr
  simp only [neg_div]
  linarith

theorem gaussian_localized_mass (ρ : Measure (Space d)) [IsFiniteMeasure ρ]
    {B A q : ℝ} {k : ℕ} (hB : 1 ≤ B) (hA : 0 ≤ A) (hq : q ≤ k)
    (hsupport : ∀ᵐ v ∂ρ, ‖v‖ ≤ 2*B)
    (hball : ∀ x : Space d, ∀ r : ℝ, 1 ≤ r →
      ρ (ball x r) ≤ ENNReal.ofReal (A*r^q)) (u : Space d) :
    (∫ v, Real.exp (-2*(dist u v)^2) ∂ρ) ≤
      Real.exp 1*A*gaussianBallConstant k*Real.exp (-‖u‖^2/(16*B^2)) := by
  have hint (a : ℝ) (ha : 0 ≤ a) :
      Integrable (fun v => Real.exp (-a*(dist u v)^2)) ρ := by
    apply (integrable_const (1:ℝ)).mono (by fun_prop)
    filter_upwards with v
    rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),norm_one]
    exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ha) (sq_nonneg _))
  have hpotential : (∫ v, Real.exp (-(dist u v)^2) ∂ρ) ≤ A*gaussianBallConstant k := by
    have h := gaussian_mass_bound_real ρ (B := 1) zero_lt_one hA hq
      (by simpa only [div_one] using hball) u
    simpa using h
  have h1 : Integrable (fun v => Real.exp (-(dist u v)^2)) ρ := by
    simpa only [neg_mul,one_mul] using hint 1 zero_le_one
  calc
    _ ≤ ∫ v, (Real.exp 1*Real.exp (-‖u‖^2/(16*B^2)))*
        Real.exp (-(dist u v)^2) ∂ρ := by
      apply integral_mono_ae (hint 2 (by norm_num))
        (h1.const_mul _)
      filter_upwards [hsupport] with v hv
      exact gaussian_localization_pointwise hB u v hv
    _ = (Real.exp 1*Real.exp (-‖u‖^2/(16*B^2)))*
        (∫ v, Real.exp (-(dist u v)^2) ∂ρ) := integral_const_mul _ _
    _ ≤ (Real.exp 1*Real.exp (-‖u‖^2/(16*B^2)))*(A*gaussianBallConstant k) :=
      mul_le_mul_of_nonneg_left hpotential (by positivity)
    _ = _ := by ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Shells_FrequencyShell
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Gaussian localization for the actual frequency-shell law -/

namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem measurableSet_radialFrequencyAnnulus (B : ℝ) : MeasurableSet (radialFrequencyAnnulus B) :=
  (isClosed_le continuous_const continuous_abs).measurableSet.inter
    (isClosed_le continuous_abs continuous_const).measurableSet

theorem radial_frequency_support (ν : Measure (Sphere d)) [IsFiniteMeasure ν] (B : ℝ) :
    ∀ᵐ v ∂radialFrequencyMeasure ν B, B ≤ ‖v‖ ∧ ‖v‖ ≤ 2*B := by
  have hm : Measurable (@radialFrequencyMap d) := by unfold radialFrequencyMap; fun_prop
  rw [radialFrequencyMeasure,ae_map_iff (p := fun v : Space d => B ≤ ‖v‖ ∧ ‖v‖ ≤ 2*B) hm.aemeasurable
    ((isClosed_le continuous_const continuous_norm).measurableSet.inter
      (isClosed_le continuous_norm continuous_const).measurableSet)]
  apply (Measure.ae_prod_iff_ae_ae (by measurability)).mpr
  filter_upwards [self_mem_ae_restrict (measurableSet_radialFrequencyAnnulus B)] with t ht
  change B ≤ |t| ∧ |t| ≤ 2*B at ht
  exact Filter.Eventually.of_forall (fun w => by
    simpa only [radialFrequencyMap,norm_smul,Real.norm_eq_abs,sphere_norm,mul_one] using ht)

theorem radial_frequency_polynomial_balls (ν : Measure (Sphere d)) [IsFiniteMeasure ν]
    {B R L s : ℝ} (hB : 1 ≤ B) (hBR : B ≤ R) (hL : 1 ≤ L) (hs : 0 ≤ s)
    (hmass : ν univ ≤ 1)
    (hball : ∀ x : Space d, ∀ r : ℝ, 1/R ≤ r → r ≤ 1 →
      ν {w : Sphere d | dist (w:Space d) x < r} ≤ ENNReal.ofReal (L*r^s)) :
    ∀ x : Space d, ∀ r : ℝ, 1 ≤ r →
      radialFrequencyMeasure ν B (ball x r) ≤
        ENNReal.ofReal ((8*(2:ℝ)^s*L/B^s)*r^(s+1)) := by
  have hB₀ : 0 < B := zero_lt_one.trans_le hB
  have hR₀ : 0 < R := hB₀.trans_le hBR
  intro x r hr
  have hr₀ : 0 < r := zero_lt_one.trans_le hr
  have hscale : 1/R ≤ 2*r/B := by
    have h₁ : 1/R ≤ 1/B := one_div_le_one_div_of_le hB₀ hBR
    exact h₁.trans ((div_le_div_iff_of_pos_right hB₀).mpr (by linarith))
  have h := radial_frequency_ball_bound ν hB₀ hr₀ hL hs hmass hscale hball x
  have he : 8*r*L*(2*r/B)^s = (8*(2:ℝ)^s*L/B^s)*r^(s+1) := by
    rw [Real.div_rpow (by positivity) hB₀.le,
      Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hr₀.le,
      Real.rpow_add hr₀,Real.rpow_one]
    ring
  simpa only [he] using h

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_FrequencyIntervals
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Covering the actual radial interval by its dyadic frequency annuli -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem radial_interval_cover_step (n : ℕ) :
    Icc (-((2:ℝ)^(n+1))) ((2:ℝ)^(n+1)) ⊆
      Icc (-((2:ℝ)^n)) ((2:ℝ)^n) ∪ radialFrequencyAnnulus ((2:ℝ)^n) := by
  intro t ht
  have hh : |t| ≤ (2:ℝ)^(n+1) := abs_le.mpr ht
  by_cases hs : |t| ≤ (2:ℝ)^n
  · exact Or.inl (abs_le.mp hs)
  · right
    refine ⟨(le_of_not_ge hs),?_⟩
    simpa only [pow_succ,mul_comm] using hh

theorem radial_interval_measure_step (ν : Measure (Sphere d)) [IsFiniteMeasure ν] (n : ℕ) :
    radialIntervalMeasure ν ((2:ℝ)^(n+1)) ≤
      radialIntervalMeasure ν ((2:ℝ)^n)+radialFrequencyMeasure ν ((2:ℝ)^n) := by
  have hvol : volume.restrict (Icc (-((2:ℝ)^(n+1))) ((2:ℝ)^(n+1))) ≤
      volume.restrict (Icc (-((2:ℝ)^n)) ((2:ℝ)^n))+
        volume.restrict (radialFrequencyAnnulus ((2:ℝ)^n)) :=
    (Measure.restrict_mono (radial_interval_cover_step n) le_rfl).trans (Measure.restrict_union_le _ _)
  have hm : Measurable (@radialFrequencyMap d) := by unfold radialFrequencyMap; fun_prop
  have h := Measure.map_mono (Measure.prod_mono hvol (le_refl ν)) hm
  simpa only [radialIntervalMeasure,radialFrequencyMeasure,Measure.add_prod,
    Measure.map_add _ _ hm] using h

theorem radial_interval_dyadic_cover (ν : Measure (Sphere d)) [IsFiniteMeasure ν] (n : ℕ) :
    radialIntervalMeasure ν ((2:ℝ)^n) ≤ radialIntervalMeasure ν 1+
      ∑ j ∈ Finset.range n, radialFrequencyMeasure ν ((2:ℝ)^j) := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      _ ≤ radialIntervalMeasure ν ((2:ℝ)^n)+radialFrequencyMeasure ν ((2:ℝ)^n) :=
        radial_interval_measure_step ν n
      _ ≤ (radialIntervalMeasure ν 1+∑ j ∈ Finset.range n, radialFrequencyMeasure ν ((2:ℝ)^j))+
          radialFrequencyMeasure ν ((2:ℝ)^n) := add_le_add ih le_rfl
      _ = _ := by rw [Finset.sum_range_succ,add_assoc]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianShellEnergy
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A broad Gaussian weight at the original finite spatial scale -/

namespace Falconer
open Set Metric MeasureTheory
variable {d : ℕ}

private theorem double_gaussian_mono (μ : Measure (Space d)) [IsFiniteMeasure μ]
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    (∫ x, ∫ y, Real.exp (-b*‖x-y‖^2) ∂μ ∂μ) ≤
      ∫ x, ∫ y, Real.exp (-a*‖x-y‖^2) ∂μ ∂μ := by
  have hi (c : ℝ) (hc : 0 ≤ c) :
      Integrable (fun z : Space d × Space d => Real.exp (-c*‖z.1-z.2‖^2)) (μ.prod μ) := by
    apply (integrable_const (1:ℝ)).mono (by fun_prop)
    filter_upwards with z
    rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),norm_one]
    exact Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hc) (sq_nonneg _))
  rw [← integral_prod _ (hi b (ha.trans hab)),← integral_prod _ (hi a ha)]
  apply integral_mono (hi b (ha.trans hab)) (hi a ha)
  intro z
  apply Real.exp_le_exp.mpr
  nlinarith [mul_le_mul_of_nonneg_right hab (sq_nonneg ‖z.1-z.2‖)]

theorem gaussian_shell_energy_bound (μ : Measure (Space d)) [IsFiniteMeasure μ]
    {B K s : ℝ} {k : ℕ} (hB : 0 < B) (hK : 0 ≤ K) (hsk : s ≤ k)
    (hb : ∀ x : Space d, ∀ r : ℝ, 1/B ≤ r →
      μ (ball x r) ≤ ENNReal.ofReal (K*r^s)) :
    (∫ ξ : Space d, Real.exp (-‖ξ‖^2/(16*B^2))*‖PlanarFalconer.sourceFourier μ ξ‖^2) ≤
      (16*Real.pi*B^2)^((d:ℝ)/2)*(μ.real univ*(K*(1/B)^s*gaussianBallConstant k)) := by
  have hb' : 0 < 1/(16*B^2) := by positivity
  have he (ξ : Space d) : -‖ξ‖^2/(16*B^2) = -(1/(16*B^2))*‖ξ‖^2 := by ring
  simp_rw [he]
  rw [PlanarFalconer.gaussian_lebesgue_square μ hb']
  have h₁ : Real.pi/(1/(16*B^2)) = 16*Real.pi*B^2 := by field_simp
  have h₂ : Real.pi^2/(1/(16*B^2)) = 16*Real.pi^2*B^2 := by field_simp
  rw [h₁,h₂]
  have hcoeff : B^2 ≤ 16*Real.pi^2*B^2 := by
    have hp : 1 ≤ Real.pi^2 := by nlinarith [Real.pi_gt_three]
    nlinarith [sq_nonneg B]
  have hm := double_gaussian_mono μ (sq_nonneg B) hcoeff
  have hd : (∫ x, ∫ y, Real.exp (-B^2*‖x-y‖^2) ∂μ ∂μ) =
      ∫ x, ∫ y, Real.exp (-(B*dist x y)^2) ∂μ ∂μ := by
    apply integral_congr_ae
    filter_upwards with x
    apply integral_congr_ae
    filter_upwards with y
    rw [dist_eq_norm]
    congr 1
    ring
  rw [hd] at hm
  have hfinal := hm.trans (gaussian_energy_bound μ hB hK hsk hb)
  have hdim : Module.finrank ℝ (Space d) = d := by simp [Space]
  simpa only [hdim] using mul_le_mul_of_nonneg_left hfinal
    (Real.rpow_nonneg (by positivity : 0 ≤ 16*Real.pi*B^2) ((d:ℝ)/2))


theorem gaussian_shell_energy_lintegral (μ : Measure (Space d)) [IsFiniteMeasure μ]
    {B K s : ℝ} {k : ℕ} (hB : 0 < B) (hK : 0 ≤ K) (hsk : s ≤ k)
    (hb : ∀ x : Space d, ∀ r : ℝ, 1/B ≤ r →
      μ (ball x r) ≤ ENNReal.ofReal (K*r^s)) :
    (∫⁻ ξ : Space d, ENNReal.ofReal (Real.exp (-‖ξ‖^2/(16*B^2)))*
      ENNReal.ofReal (‖PlanarFalconer.sourceFourier μ ξ‖^2)) ≤
      ENNReal.ofReal ((16*Real.pi*B^2)^((d:ℝ)/2)*
        (μ.real univ*(K*(1/B)^s*gaussianBallConstant k))) := by
  have hi : Integrable (fun ξ : Space d => Real.exp (-‖ξ‖^2/(16*B^2))*
      ‖PlanarFalconer.sourceFourier μ ξ‖^2) := by
    have he (ξ : Space d) : -‖ξ‖^2/(16*B^2) = -(1/(16*B^2))*‖ξ‖^2 := by ring
    simp_rw [he]
    exact PlanarFalconer.gaussian_sourceFourier_integrable μ (by positivity : 0 < 1/(16*B^2))
  calc
    _ = ∫⁻ ξ : Space d, ENNReal.ofReal (Real.exp (-‖ξ‖^2/(16*B^2))*
        ‖PlanarFalconer.sourceFourier μ ξ‖^2) :=
      lintegral_congr (fun ξ => (ENNReal.ofReal_mul (Real.exp_pos _).le).symm)
    _ = ENNReal.ofReal (∫ ξ : Space d, Real.exp (-‖ξ‖^2/(16*B^2))*
        ‖PlanarFalconer.sourceFourier μ ξ‖^2) :=
      (ofReal_integral_eq_lintegral_ofReal hi (by filter_upwards with ξ; positivity)).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal (gaussian_shell_energy_bound μ hB hK hsk hb)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_CriticalScale
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact cancellation at the half-dimensional frequency scale -/

namespace Falconer

theorem critical_gaussian_scale {B C : ℝ} (hB : 0 < B) (hC : 0 ≤ C) (s : ℝ) :
    (C*B^2)^s*(1/B)^s/B^s = C^s := by
  have hp : (B^2)^s = B^s*B^s := by
    rw [pow_two,Real.mul_rpow hB.le hB.le]
  rw [Real.mul_rpow hC (sq_nonneg B),hp,one_div,Real.inv_rpow hB.le]
  field_simp [ne_of_gt (Real.rpow_pos_of_pos hB s)]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Measures_WeightedIntegralSquare
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory Filter

theorem weighted_integral_square {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (w f : α → ℝ) (hw : ∀ x, 0 ≤ w x) (hiw : Integrable w μ)
    (hif : Integrable (fun x => w x * f x) μ)
    (hif₂ : Integrable (fun x => w x * (f x)^2) μ) :
    (∫ x, w x * f x ∂μ)^2 ≤ (∫ x, w x ∂μ) * (∫ x, w x * (f x)^2 ∂μ) := by
  let W := ∫ x, w x ∂μ
  let V := ∫ x, w x * f x ∂μ
  let U := ∫ x, w x * (f x)^2 ∂μ
  have hW : 0 ≤ W := integral_nonneg hw
  by_cases hz : W = 0
  · have hwz : w =ᵐ[μ] 0 := (integral_eq_zero_iff_of_nonneg hw hiw).mp hz
    have hvz : V = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards [hwz] with x hx
      simp [hx]
    change V^2 ≤ W*U
    simp [hvz,hz]
  · have hWp : 0 < W := lt_of_le_of_ne hW (Ne.symm hz)
    have hn : 0 ≤ ∫ x, w x * (f x - V/W)^2 ∂μ :=
      integral_nonneg (fun x => mul_nonneg (hw x) (sq_nonneg _))
    have he (x : α) : w x * (f x - V/W)^2 =
        w x*(f x)^2 - (2*(V/W))*(w x*f x) + (V/W)^2*w x := by ring
    simp_rw [he] at hn
    have hiSub : Integrable (fun x => w x*(f x)^2 - (2*(V/W))*(w x*f x)) μ :=
      hif₂.sub (hif.const_mul (2*(V/W)))
    rw [integral_add hiSub (hiw.const_mul ((V/W)^2)),
      integral_sub hif₂ (hif.const_mul (2*(V/W))), integral_const_mul, integral_const_mul] at hn
    change 0 ≤ U - (2*(V/W))*V + (V/W)^2*W at hn
    have hc : U - (2*(V/W))*V + (V/W)^2*W = U - V^2/W := by
      field_simp
      ring
    rw [hc] at hn
    change V^2 ≤ W*U
    have hh := (div_le_iff₀ hWp).mp (show V^2/W ≤ U by linarith)
    nlinarith

theorem norm_integral_coeff_square {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (c F : α → ℂ) (hic : Integrable c μ)
    (hi₁ : Integrable (fun x => ‖c x‖ * ‖F x‖) μ)
    (hi₂ : Integrable (fun x => ‖c x‖ * ‖F x‖^2) μ) :
    ‖∫ x, c x * F x ∂μ‖^2 ≤
      (∫ x, ‖c x‖ ∂μ) * (∫ x, ‖c x‖ * ‖F x‖^2 ∂μ) := by
  have hn : ‖∫ x, c x * F x ∂μ‖ ≤ ∫ x, ‖c x‖ * ‖F x‖ ∂μ := by
    simpa only [norm_mul] using norm_integral_le_integral_norm (fun x => c x * F x)
  exact (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans
    (weighted_integral_square μ (fun x => ‖c x‖) (fun x => ‖F x‖)
      (fun x => norm_nonneg _) hic.norm hi₁ hi₂)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianConvolution
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Gaussian convolution of a finite measure Fourier transform -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal FourierTransform RealInnerProductSpace
variable {d : ℕ}

theorem sourceFourier_phase (μ : Measure (Space d)) (v : Space d) :
    PlanarFalconer.sourceFourier μ v = ∫ x, euclideanFourierPhase v x ∂μ := by
  simp only [PlanarFalconer.sourceFourier,charFun_apply,inner_smul_right,euclideanFourierPhase]

theorem shifted_gaussian_fourier (v x : Space d) :
    𝓕 (fun u : Space d => (Real.exp (-2*‖u-v‖^2):ℂ)) x =
      euclideanFourierPhase v x*
        (((Real.pi/2)^((d:ℝ)/2)*Real.exp (-(Real.pi^2/2)*‖x‖^2):ℝ):ℂ) := by
  have h := congrFun (VectorFourier.fourierIntegral_comp_add_right Real.fourierChar
    (volume : Measure (Space d)) (innerₗ (Space d))
    (fun u : Space d => (Real.exp (-2*‖u‖^2):ℂ)) (-v)) x
  change 𝓕 (fun u : Space d => (Real.exp (-2*‖u+(-v)‖^2):ℂ)) x =
    Real.fourierChar (inner ℝ (-v) x) •
      𝓕 (fun u : Space d => (Real.exp (-2*‖u‖^2):ℂ)) x at h
  rw [PlanarFalconer.source_gaussian_fourier (by norm_num : (0:ℝ) < 2)] at h
  have hp : (Real.fourierChar (inner ℝ (-v) x) : ℂ) = euclideanFourierPhase v x := by
    rw [Real.fourierChar_apply,euclideanFourierPhase,inner_neg_left,real_inner_comm x v]
    congr 1
    push_cast
    ring
  have hd : Module.finrank ℝ (Space d) = d := by simp [Space]
  simpa only [hd,sub_eq_add_neg,Circle.smul_def,smul_eq_mul,hp] using h

theorem gaussian_convolution_identity (β : Measure (Space d)) [IsFiniteMeasure β]
    (v : Space d) :
    (∫ u : Space d, (Real.exp (-2*‖u-v‖^2):ℂ)*PlanarFalconer.sourceFourier β u) =
      (((Real.pi/2:ℝ)^((d:ℝ)/2):ℝ):ℂ)*
        ∫ x, (Real.exp (-(Real.pi^2/2)*‖x‖^2):ℂ)*euclideanFourierPhase v x ∂β := by
  have hi : Integrable (fun u : Space d => (Real.exp (-2*‖u-v‖^2):ℂ)) :=
    ((PlanarFalconer.gaussian_lebesgue_integrable (V := Space d) (by norm_num : (0:ℝ)<2)).comp_sub_right v).ofReal
  rw [PlanarFalconer.sourceFourier_integral_swap β _ hi]
  simp only [shifted_gaussian_fourier,Complex.ofReal_mul]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with x
  ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianDamping
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Damping a finite source measure and recovering its Fourier transform -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal FourierTransform
variable {d : ℕ}

theorem sourceFourier_gaussianDampedMeasure (β : Measure (Space d)) (v : Space d) :
    PlanarFalconer.sourceFourier (gaussianDampedMeasure β) v =
      ∫ x, (Real.exp (-(Real.pi^2/2)*‖x‖^2):ℂ)*euclideanFourierPhase v x ∂β := by
  rw [sourceFourier_phase,gaussianDampedMeasure,
    integral_withDensity_eq_integral_toReal_smul (by fun_prop)
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  filter_upwards with x
  rw [ENNReal.toReal_ofReal (Real.exp_pos _).le,Complex.real_smul]

/-- Exact convolution formula, before the Cauchy--Schwarz bound. -/
theorem gaussian_convolution_damped (β : Measure (Space d)) [IsFiniteMeasure β]
    (v : Space d) :
    (∫ u : Space d, (Real.exp (-2*‖u-v‖^2):ℂ)*PlanarFalconer.sourceFourier β u) =
      (((Real.pi/2:ℝ)^((d:ℝ)/2):ℝ):ℂ)*
        PlanarFalconer.sourceFourier (gaussianDampedMeasure β) v := by
  rw [gaussian_convolution_identity,sourceFourier_gaussianDampedMeasure]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianSmoothing
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Weighted Cauchy--Schwarz for Gaussian Fourier smoothing -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem gaussian_fourier_power_integrable (β : Measure (Space d)) [IsFiniteMeasure β]
    (v : Space d) (k : ℕ) :
    Integrable (fun u : Space d => Real.exp (-2*‖u-v‖^2)*
      ‖PlanarFalconer.sourceFourier β u‖^k) := by
  have hG := (PlanarFalconer.gaussian_lebesgue_integrable (V := Space d)
    (by norm_num : (0:ℝ) < 2)).comp_sub_right v
  apply (hG.mul_const ((β.real univ)^k)).mono (by unfold PlanarFalconer.sourceFourier; fun_prop)
  filter_upwards with u
  rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (by positivity),
    abs_of_nonneg (by positivity)]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  apply pow_le_pow_left₀ (norm_nonneg _)
  exact norm_charFun_le _

theorem gaussian_translate_integral (v : Space d) :
    (∫ u : Space d, Real.exp (-2*‖u-v‖^2)) = (Real.pi/2)^((d:ℝ)/2) := by
  rw [integral_sub_right_eq_self (fun u : Space d => Real.exp (-2*‖u‖^2)) v]
  simpa only [Space,finrank_euclideanSpace_fin] using
    GaussianFourier.integral_rexp_neg_mul_sq_norm (V := Space d) (by norm_num : (0:ℝ) < 2)

theorem gaussian_smoothing_square (β : Measure (Space d)) [IsFiniteMeasure β] (v : Space d) :
    ‖PlanarFalconer.sourceFourier (gaussianDampedMeasure β) v‖^2 ≤
      ((Real.pi/2)^((d:ℝ)/2))⁻¹ *
        ∫ u : Space d, Real.exp (-2*‖u-v‖^2)*‖PlanarFalconer.sourceFourier β u‖^2 := by
  let C : ℝ := (Real.pi/2)^((d:ℝ)/2)
  have hC : 0 < C := Real.rpow_pos_of_pos (by positivity) _
  have hG := (PlanarFalconer.gaussian_lebesgue_integrable (V := Space d)
    (by norm_num : (0:ℝ) < 2)).comp_sub_right v
  have h1 : Integrable (fun u : Space d =>
      ‖(Real.exp (-2*‖u-v‖^2):ℂ)‖*‖PlanarFalconer.sourceFourier β u‖) := by
    simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),pow_one] using
      gaussian_fourier_power_integrable β v 1
  have h2 : Integrable (fun u : Space d =>
      ‖(Real.exp (-2*‖u-v‖^2):ℂ)‖*‖PlanarFalconer.sourceFourier β u‖^2) := by
    simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)] using
      gaussian_fourier_power_integrable β v 2
  have h := PlanarFalconer.norm_integral_coeff_square volume
    (fun u : Space d => (Real.exp (-2*‖u-v‖^2):ℂ)) (PlanarFalconer.sourceFourier β)
    hG.ofReal h1 h2
  rw [gaussian_convolution_damped] at h
  simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (show 0 < (Real.pi/2)^((d:ℝ)/2) from hC),
    abs_of_pos (Real.exp_pos _),mul_pow] at h
  rw [gaussian_translate_integral] at h
  change C^2*‖PlanarFalconer.sourceFourier (gaussianDampedMeasure β) v‖^2 ≤
    C*(∫ u : Space d, Real.exp (-2*‖u-v‖^2)*‖PlanarFalconer.sourceFourier β u‖^2) at h
  have h' : C*‖PlanarFalconer.sourceFourier (gaussianDampedMeasure β) v‖^2 ≤
      ∫ u : Space d, Real.exp (-2*‖u-v‖^2)*‖PlanarFalconer.sourceFourier β u‖^2 := by
    apply (mul_le_mul_iff_right₀ hC).mp
    nlinarith only [h]
  calc
    _ ≤ (∫ u : Space d, Real.exp (-2*‖u-v‖^2)*‖PlanarFalconer.sourceFourier β u‖^2)/C :=
      (le_div_iff₀ hC).mpr (by simpa only [mul_comm] using h')
    _ = _ := by dsimp [C]; ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_IntegratedSmoothing
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integrating Gaussian smoothing against the actual frequency law -/

namespace Falconer
open Set MeasureTheory Metric
open scoped ENNReal
variable {d : ℕ}

theorem gaussian_smoothing_lintegral (β : Measure (Space d)) [IsFiniteMeasure β]
    (v : Space d) :
    ENNReal.ofReal (‖PlanarFalconer.sourceFourier (gaussianDampedMeasure β) v‖^2) ≤
      ENNReal.ofReal (((Real.pi/2)^((d:ℝ)/2))⁻¹)*
        ∫⁻ u : Space d, ENNReal.ofReal (Real.exp (-2*‖u-v‖^2))*
          ENNReal.ofReal (‖PlanarFalconer.sourceFourier β u‖^2) := by
  have h := ENNReal.ofReal_le_ofReal (gaussian_smoothing_square β v)
  rw [ENNReal.ofReal_mul (by positivity),
    ofReal_integral_eq_lintegral_ofReal (gaussian_fourier_power_integrable β v 2)
      (by filter_upwards with u; positivity)] at h
  convert h using 2
  all_goals try with_reducible_and_instances rfl
  apply lintegral_congr
  intro u
  exact (ENNReal.ofReal_mul (Real.exp_pos _).le).symm

theorem gaussian_integrated_smoothing (β ρ : Measure (Space d))
    [IsFiniteMeasure β] [IsFiniteMeasure ρ]
    {B A q : ℝ} {k : ℕ} (hB : 1 ≤ B) (hA : 0 ≤ A) (hq : q ≤ k)
    (hsupport : ∀ᵐ v ∂ρ, ‖v‖ ≤ 2*B)
    (hball : ∀ x : Space d, ∀ r : ℝ, 1 ≤ r →
      ρ (ball x r) ≤ ENNReal.ofReal (A*r^q)) :
    (∫⁻ v, ENNReal.ofReal (‖PlanarFalconer.sourceFourier (gaussianDampedMeasure β) v‖^2) ∂ρ) ≤
      ENNReal.ofReal ((((Real.pi/2)^((d:ℝ)/2))⁻¹)*(Real.exp 1*A*gaussianBallConstant k))*
        ∫⁻ u : Space d, ENNReal.ofReal (Real.exp (-‖u‖^2/(16*B^2)))*
          ENNReal.ofReal (‖PlanarFalconer.sourceFourier β u‖^2) := by
  let C : ℝ := ((Real.pi/2)^((d:ℝ)/2))⁻¹
  let D : ℝ := Real.exp 1*A*gaussianBallConstant k
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hD : 0 ≤ D := mul_nonneg (mul_nonneg (Real.exp_pos _).le hA) (gaussianBallConstant_nonneg k)
  have hswap : (∫⁻ v, ∫⁻ u : Space d, ENNReal.ofReal (Real.exp (-2*‖u-v‖^2))*
      ENNReal.ofReal (‖PlanarFalconer.sourceFourier β u‖^2) ∂volume ∂ρ) =
      ∫⁻ u : Space d, ∫⁻ v, ENNReal.ofReal (Real.exp (-2*‖u-v‖^2))*
        ENNReal.ofReal (‖PlanarFalconer.sourceFourier β u‖^2) ∂ρ ∂volume := by
    apply lintegral_lintegral_swap
    unfold PlanarFalconer.sourceFourier
    fun_prop
  have hinner (u : Space d) :
      (∫⁻ v, ENNReal.ofReal (Real.exp (-2*‖u-v‖^2)) ∂ρ) ≤
        ENNReal.ofReal D*ENNReal.ofReal (Real.exp (-‖u‖^2/(16*B^2))) := by
    have hi : Integrable (fun v : Space d => Real.exp (-2*‖u-v‖^2)) ρ := by
      apply (integrable_const (1:ℝ)).mono (by fun_prop)
      filter_upwards with v
      rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),norm_one]
      exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by norm_num) (sq_nonneg _))
    rw [← ofReal_integral_eq_lintegral_ofReal hi (by filter_upwards with v; positivity),
      ← ENNReal.ofReal_mul hD]
    apply ENNReal.ofReal_le_ofReal
    simpa only [dist_eq_norm] using gaussian_localized_mass ρ hB hA hq hsupport hball u
  calc
    _ ≤ ∫⁻ v, ENNReal.ofReal C*(∫⁻ u : Space d, ENNReal.ofReal (Real.exp (-2*‖u-v‖^2))*
        ENNReal.ofReal (‖PlanarFalconer.sourceFourier β u‖^2)) ∂ρ :=
      lintegral_mono (gaussian_smoothing_lintegral β)
    _ = ENNReal.ofReal C*(∫⁻ u : Space d, ∫⁻ v,
        ENNReal.ofReal (Real.exp (-2*‖u-v‖^2))*
          ENNReal.ofReal (‖PlanarFalconer.sourceFourier β u‖^2) ∂ρ) := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,hswap]
    _ = ENNReal.ofReal C*(∫⁻ u : Space d,
        (∫⁻ v, ENNReal.ofReal (Real.exp (-2*‖u-v‖^2)) ∂ρ)*
          ENNReal.ofReal (‖PlanarFalconer.sourceFourier β u‖^2)) := by
      congr 1
      apply lintegral_congr
      intro u
      exact lintegral_mul_const' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal C*(∫⁻ u : Space d,
        (ENNReal.ofReal D*ENNReal.ofReal (Real.exp (-‖u‖^2/(16*B^2))))*
          ENNReal.ofReal (‖PlanarFalconer.sourceFourier β u‖^2)) := by
      gcongr with u
      exact hinner u
    _ = _ := by
      simp_rw [mul_assoc]
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,← mul_assoc,← ENNReal.ofReal_mul hC]
      simp only [C,D,mul_assoc]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianAmplification
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Undoing Gaussian damping on a bounded original probability -/

namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem gaussianAmplifiedMeasure_le (μ : Measure (Space d)) {D : ℝ} (hD : 0 ≤ D)
    (hsupport : ∀ᵐ x ∂μ, ‖x‖ ≤ D) :
    gaussianAmplifiedMeasure μ ≤ ENNReal.ofReal (Real.exp ((Real.pi^2/2)*D^2)) • μ := by
  calc
    _ ≤ μ.withDensity (fun _ => ENNReal.ofReal (Real.exp ((Real.pi^2/2)*D^2))) := by
      apply withDensity_mono
      filter_upwards [hsupport] with x hx
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_left ((sq_le_sq₀ (norm_nonneg _) hD).mpr hx) (by positivity)
    _ = _ := withDensity_const _

theorem gaussianAmplifiedMeasure_finite (μ : Measure (Space d)) [IsFiniteMeasure μ]
    {D : ℝ} (hD : 0 ≤ D) (hsupport : ∀ᵐ x ∂μ, ‖x‖ ≤ D) :
    IsFiniteMeasure (gaussianAmplifiedMeasure μ) := by
  constructor
  apply ((gaussianAmplifiedMeasure_le μ hD hsupport) univ).trans_lt
  change ENNReal.ofReal (Real.exp ((Real.pi^2/2)*D^2))*μ univ < ∞
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top μ univ)

theorem gaussianDampedMeasure_amplified (μ : Measure (Space d)) :
    gaussianDampedMeasure (gaussianAmplifiedMeasure μ) = μ := by
  rw [gaussianDampedMeasure,gaussianAmplifiedMeasure,← withDensity_mul μ (by fun_prop) (by fun_prop)]
  have he : (fun x : Space d => ENNReal.ofReal (Real.exp ((Real.pi^2/2)*‖x‖^2))) *
      (fun x => ENNReal.ofReal (Real.exp (-(Real.pi^2/2)*‖x‖^2))) = fun _ => (1:ℝ≥0∞) := by
    funext x
    dsimp only [Pi.mul_apply]
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le,← Real.exp_add]
    have hz : (Real.pi^2/2)*‖x‖^2+(-(Real.pi^2/2))*‖x‖^2 = 0 := by ring
    rw [hz,Real.exp_zero,ENNReal.ofReal_one]
  rw [he,withDensity_const,one_smul]

theorem gaussianAmplifiedMeasure_ball_bound (μ : Measure (Space d))
    {D δ K s : ℝ} (hD : 0 ≤ D) (hsupport : ∀ᵐ x ∂μ, ‖x‖ ≤ D)
    (hb : ∀ x : Space d, ∀ r : ℝ, δ ≤ r →
      μ (ball x r) ≤ ENNReal.ofReal (K*r^s)) :
    ∀ x : Space d, ∀ r : ℝ, δ ≤ r →
      gaussianAmplifiedMeasure μ (ball x r) ≤
        ENNReal.ofReal ((Real.exp ((Real.pi^2/2)*D^2)*K)*r^s) := by
  intro x r hr
  calc
    _ ≤ (ENNReal.ofReal (Real.exp ((Real.pi^2/2)*D^2)) • μ) (ball x r) :=
      (gaussianAmplifiedMeasure_le μ hD hsupport) _
    _ = ENNReal.ofReal (Real.exp ((Real.pi^2/2)*D^2))*μ (ball x r) := by rfl
    _ ≤ ENNReal.ofReal (Real.exp ((Real.pi^2/2)*D^2))*ENNReal.ofReal (K*r^s) :=
      mul_le_mul_right (hb x r hr) _
    _ = _ := by rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]; congr 1; ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Shells_HalfDimensionalShell
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The critical half-dimensional estimate on one frequency shell -/

namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem halfDimensionalShellConstant_nonneg (d : ℕ) :
    0 ≤ halfDimensionalShellConstant d := by
  have h₁ := gaussianBallConstant_nonneg (Nat.ceil ((d:ℝ)/2+1))
  have h₂ := gaussianBallConstant_nonneg (Nat.ceil ((d:ℝ)/2))
  unfold halfDimensionalShellConstant
  positivity

theorem damped_half_dimensional_shell (β : Measure (Space d)) [IsFiniteMeasure β]
    (ν : Measure (Sphere d)) [IsFiniteMeasure ν]
    {B R K L : ℝ} (hB : 1 ≤ B) (hBR : B ≤ R) (hK : 0 ≤ K) (hL : 1 ≤ L)
    (hmass : ν univ ≤ 1)
    (hβ : ∀ x : Space d, ∀ r : ℝ, 1/B ≤ r →
      β (ball x r) ≤ ENNReal.ofReal (K*r^((d:ℝ)/2)))
    (hν : ∀ x : Space d, ∀ r : ℝ, 1/R ≤ r → r ≤ 1 →
      ν {w : Sphere d | dist (w:Space d) x < r} ≤ ENNReal.ofReal (L*r^((d:ℝ)/2))) :
    (∫⁻ v, ENNReal.ofReal (‖PlanarFalconer.sourceFourier (gaussianDampedMeasure β) v‖^2)
      ∂radialFrequencyMeasure ν B) ≤
        ENNReal.ofReal (halfDimensionalShellConstant d*β.real univ*K*L) := by
  let s : ℝ := (d:ℝ)/2
  let A : ℝ := 8*(2:ℝ)^s*L/B^s
  let C : ℝ := ((Real.pi/2)^s)⁻¹
  let D : ℝ := Real.exp 1*A*gaussianBallConstant (Nat.ceil (s+1))
  have hB₀ : 0 < B := zero_lt_one.trans_le hB
  have hs : 0 ≤ s := by dsimp [s]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hD : 0 ≤ D := mul_nonneg (mul_nonneg (Real.exp_pos _).le hA) (gaussianBallConstant_nonneg _)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hbase := gaussian_integrated_smoothing β (radialFrequencyMeasure ν B) hB hA
    (Nat.le_ceil (s+1)) ((radial_frequency_support ν B).mono (fun _ h => h.2))
    (radial_frequency_polynomial_balls ν hB hBR hL hs hmass hν)
  have henergy := gaussian_shell_energy_lintegral β hB₀ hK (Nat.le_ceil s) hβ
  calc
    _ ≤ ENNReal.ofReal (C*D)*
        ∫⁻ u : Space d, ENNReal.ofReal (Real.exp (-‖u‖^2/(16*B^2)))*
          ENNReal.ofReal (‖PlanarFalconer.sourceFourier β u‖^2) := hbase
    _ ≤ ENNReal.ofReal (C*D)*ENNReal.ofReal ((16*Real.pi*B^2)^s*
        (β.real univ*(K*(1/B)^s*gaussianBallConstant (Nat.ceil s)))) :=
      mul_le_mul_right henergy _
    _ = ENNReal.ofReal (C*D*((16*Real.pi*B^2)^s*
        (β.real univ*(K*(1/B)^s*gaussianBallConstant (Nat.ceil s))))) :=
      (ENNReal.ofReal_mul (mul_nonneg hC hD)).symm
    _ = _ := by
      congr 1
      calc
        C*D*((16*Real.pi*B^2)^s*(β.real univ*(K*(1/B)^s*gaussianBallConstant (Nat.ceil s)))) =
            (C*(Real.exp 1*8*(2:ℝ)^s*gaussianBallConstant (Nat.ceil (s+1)))*
              gaussianBallConstant (Nat.ceil s)*β.real univ*K*L)*
                ((16*Real.pi*B^2)^s*(1/B)^s/B^s) := by dsimp [D,A]; ring
        _ = _ := by
          rw [critical_gaussian_scale hB₀ (by positivity : (0:ℝ) ≤ 16*Real.pi)]
          dsimp [halfDimensionalShellConstant,C,s]
          ring


/-- One frequency shell for a bounded original probability, with no lower-scale ball bounds. -/
theorem half_dimensional_shell (μ : Measure (Space d)) [IsProbabilityMeasure μ]
    (ν : Measure (Sphere d)) [IsFiniteMeasure ν]
    {D B R K L : ℝ} (hD : 0 ≤ D) (hsupport : ∀ᵐ x ∂μ, ‖x‖ ≤ D)
    (hB : 1 ≤ B) (hBR : B ≤ R) (hK : 0 ≤ K) (hL : 1 ≤ L) (hmass : ν univ ≤ 1)
    (hμ : ∀ x : Space d, ∀ r : ℝ, 1/B ≤ r →
      μ (ball x r) ≤ ENNReal.ofReal (K*r^((d:ℝ)/2)))
    (hν : ∀ x : Space d, ∀ r : ℝ, 1/R ≤ r → r ≤ 1 →
      ν {w : Sphere d | dist (w:Space d) x < r} ≤ ENNReal.ofReal (L*r^((d:ℝ)/2))) :
    (∫⁻ v, ENNReal.ofReal (‖PlanarFalconer.sourceFourier μ v‖^2) ∂radialFrequencyMeasure ν B) ≤
      ENNReal.ofReal (halfDimensionalShellConstant d*
        (Real.exp ((Real.pi^2/2)*D^2))^2*K*L) := by
  let E := Real.exp ((Real.pi^2/2)*D^2)
  let := gaussianAmplifiedMeasure_finite μ hD hsupport
  have hβ : (gaussianAmplifiedMeasure μ).real univ ≤ E := by
    have hh := gaussianAmplifiedMeasure_le μ hD hsupport univ
    simp only [Measure.smul_apply,smul_eq_mul,measure_univ,mul_one] at hh
    have hh' := ENNReal.toReal_mono ENNReal.ofReal_ne_top hh
    simpa only [measureReal_def,E,ENNReal.toReal_ofReal (Real.exp_pos _).le] using hh'
  have h := damped_half_dimensional_shell (gaussianAmplifiedMeasure μ) ν hB hBR
    (mul_nonneg (Real.exp_pos _).le hK) hL hmass
    (gaussianAmplifiedMeasure_ball_bound μ hD hsupport hμ) hν
  rw [gaussianDampedMeasure_amplified] at h
  refine h.trans ?_
  apply ENNReal.ofReal_le_ofReal
  have hC := halfDimensionalShellConstant_nonneg d
  calc
    halfDimensionalShellConstant d*(gaussianAmplifiedMeasure μ).real univ*(E*K)*L ≤
        halfDimensionalShellConstant d*E*(E*K)*L := by
      gcongr
    _ = _ := by dsimp [E]; ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_HalfDimensionalFourier
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The half-dimensional Fourier bound at the required dyadic scales -/

namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem radial_unit_interval_mass (ν : Measure (Sphere d)) [IsFiniteMeasure ν]
    (hmass : ν univ ≤ 1) : radialIntervalMeasure ν 1 univ ≤ 2 := by
  have hm : Measurable (@radialFrequencyMap d) := by unfold radialFrequencyMap; fun_prop
  rw [radialIntervalMeasure,Measure.map_apply hm MeasurableSet.univ,preimage_univ]
  rw [← univ_prod_univ,Measure.prod_prod,Measure.restrict_apply_univ,Real.volume_Icc]
  norm_num
  exact (mul_le_mul_right hmass 2).trans_eq (mul_one _)

theorem radial_low_fourier (μ : Measure (Space d)) [IsProbabilityMeasure μ]
    (ν : Measure (Sphere d)) [IsFiniteMeasure ν] (hmass : ν univ ≤ 1) :
    (∫⁻ v, ENNReal.ofReal (‖PlanarFalconer.sourceFourier μ v‖^2)
      ∂radialIntervalMeasure ν 1) ≤ 2 := by
  calc
    _ ≤ ∫⁻ _v, (1:ℝ≥0∞) ∂radialIntervalMeasure ν 1 := by
      apply lintegral_mono
      intro v
      have hn : ‖PlanarFalconer.sourceFourier μ v‖ ≤ 1 := by
        simpa [PlanarFalconer.sourceFourier] using
          norm_charFun_le (μ := μ) ((-(2*Real.pi)) • v)
      have hsq := pow_le_pow_left₀ (norm_nonneg _) hn 2
      simpa only [one_pow,ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hsq
    _ = radialIntervalMeasure ν 1 univ := by simp
    _ ≤ 2 := radial_unit_interval_mass ν hmass

theorem dyadic_half_dimensional_fourier (μ : Measure (Space d)) [IsProbabilityMeasure μ]
    (ν : Measure (Sphere d)) [IsFiniteMeasure ν]
    {D R K L : ℝ} (hD : 0 ≤ D) (hsupport : ∀ᵐ x ∂μ, ‖x‖ ≤ D)
    (n : ℕ) (hR : (2:ℝ)^n ≤ R) (hK : 1 ≤ K) (hL : 1 ≤ L) (hmass : ν univ ≤ 1)
    (hμ : ∀ x : Space d, ∀ r : ℝ, 1/(2:ℝ)^n ≤ r → r ≤ 1 →
      μ (ball x r) ≤ ENNReal.ofReal (K*r^((d:ℝ)/2)))
    (hν : ∀ x : Space d, ∀ r : ℝ, 1/R ≤ r → r ≤ 1 →
      ν {w : Sphere d | dist (w:Space d) x < r} ≤ ENNReal.ofReal (L*r^((d:ℝ)/2))) :
    (∫⁻ v, ENNReal.ofReal (‖PlanarFalconer.sourceFourier μ v‖^2)
      ∂radialIntervalMeasure ν ((2:ℝ)^n)) ≤
      ENNReal.ofReal (2+(n:ℝ)*(halfDimensionalShellConstant d*
        (Real.exp ((Real.pi^2/2)*D^2))^2*K*L)) := by
  let T : ℝ := halfDimensionalShellConstant d*(Real.exp ((Real.pi^2/2)*D^2))^2*K*L
  have hT : 0 ≤ T := by
    have := halfDimensionalShellConstant_nonneg d
    dsimp [T]
    positivity
  have hμ' := finite_scale_ball_extend μ (by simp) hK (show 0 ≤ (d:ℝ)/2 by positivity) hμ
  have hterm (j : ℕ) (hj : j ∈ Finset.range n) :
      (∫⁻ v, ENNReal.ofReal (‖PlanarFalconer.sourceFourier μ v‖^2)
        ∂radialFrequencyMeasure ν ((2:ℝ)^j)) ≤ ENNReal.ofReal T := by
    have hjn : j ≤ n := (Finset.mem_range.mp hj).le
    have hB : 1 ≤ (2:ℝ)^j := one_le_pow₀ (by norm_num)
    have hBn : (2:ℝ)^j ≤ (2:ℝ)^n := pow_le_pow_right₀ (by norm_num) hjn
    apply half_dimensional_shell μ ν hD hsupport hB (hBn.trans hR) (zero_le_one.trans hK) hL hmass
    · intro x r hr
      exact hμ' x r ((one_div_le_one_div_of_le (by positivity) hBn).trans hr)
    · exact hν
  calc
    _ ≤ ∫⁻ v, ENNReal.ofReal (‖PlanarFalconer.sourceFourier μ v‖^2)
        ∂(radialIntervalMeasure ν 1+∑ j ∈ Finset.range n, radialFrequencyMeasure ν ((2:ℝ)^j)) :=
      lintegral_mono' (radial_interval_dyadic_cover ν n) le_rfl
    _ = (∫⁻ v, ENNReal.ofReal (‖PlanarFalconer.sourceFourier μ v‖^2) ∂radialIntervalMeasure ν 1)+
        ∑ j ∈ Finset.range n, ∫⁻ v, ENNReal.ofReal (‖PlanarFalconer.sourceFourier μ v‖^2)
          ∂radialFrequencyMeasure ν ((2:ℝ)^j) := by
      rw [lintegral_add_measure,lintegral_finsetSum_measure]
    _ ≤ 2+∑ _j ∈ Finset.range n, ENNReal.ofReal T :=
      add_le_add (radial_low_fourier μ ν hmass) (Finset.sum_le_sum hterm)
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
      rw [← ENNReal.ofReal_natCast,← ENNReal.ofReal_mul (by positivity),
        show (2:ℝ≥0∞) = ENNReal.ofReal (2:ℝ) by norm_num,
        ← ENNReal.ofReal_add (by norm_num) (by positivity)]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_ProjectionLaw
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual scalar projection law and its sinc collision bound -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal RealInnerProductSpace
variable {d : ℕ}

theorem charFun_scalarProjectionLaw (μ : Measure (Space d)) (w : Space d) (r : ℝ) :
    charFun (scalarProjectionLaw μ w) r = charFun μ (r • w) := by
  rw [charFun_apply,scalarProjectionLaw,integral_map (by fun_prop) (by fun_prop),charFun_apply]
  apply integral_congr_ae
  filter_upwards with x
  simp only [inner_smul_right,real_inner_eq_re_inner]
  congr 2

theorem norm_charFun_scalarProjectionLaw (μ : Measure (Space d)) [IsFiniteMeasure μ]
    (w : Space d) (r : ℝ) :
    ‖charFun (scalarProjectionLaw μ w) (2*Real.pi*r)‖ =
      ‖PlanarFalconer.sourceFourier μ (r • w)‖ := by
  rw [charFun_scalarProjectionLaw,PlanarFalconer.sourceFourier]
  have he : (-(2*Real.pi)) • (r • w) = -((2*Real.pi*r) • w) := by module
  rw [he,charFun_neg]
  exact (Complex.norm_conj _).symm

theorem scalarProjectionLaw_collision (μ : Measure (Space d)) [IsFiniteMeasure μ]
    (w : Space d) (ε : ℝ) :
    ((scalarProjectionLaw μ w).prod (scalarProjectionLaw μ w))
      {z : ℝ × ℝ | |z.1-z.2| ≤ ε} = projectionCollision μ w ε := by
  have hm : Measurable (fun x : Space d => inner ℝ x w) := by fun_prop
  rw [scalarProjectionLaw,Measure.map_prod_map μ μ hm hm,
    Measure.map_apply (hm.prodMap hm) (by measurability)]
  congr 1
  ext z
  simp only [mem_preimage,mem_ofPred_eq,Prod.map_fst,Prod.map_snd,inner_sub_left]

theorem projection_collision_fourier : ∃ C : ℝ, 0 < C ∧
    ∀ (μ : Measure (Space d)) [IsFiniteMeasure μ] (w : Space d) (A : ℝ), 0 < A →
      A*(projectionCollision μ w (100/A)).toReal ≤
        C*∫ r in Icc (-A) A, ‖charFun (scalarProjectionLaw μ w) r‖^2 := by
  obtain ⟨C,hC,hbound⟩ := PlanarFalconer.finite_measure_distance_collision_fourier
  refine ⟨C,hC,?_⟩
  intro μ _ w A hA
  have h := hbound (scalarProjectionLaw μ w) A hA
  simpa only [measureReal_def,scalarProjectionLaw_collision] using h

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_TestWidths
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The width and buffer scales of the all-dimensional tests

These are the exponents 500 and 50 in the all-dimensional test family.
-/

namespace Falconer

theorem angularTestWidth_zero (N : ℕ) (σ : ℝ) (J n : ℕ) :
    angularTestWidth N σ J 0 n = 2/(2:ℝ)^n*((2:ℝ)^N)^(500*σ) := by
  simp [angularTestWidth]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_ProjectionGood
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Measurable projection tests on the full conditional probability -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem measurable_projectionCollision (μ : Measure (Space d)) [IsFiniteMeasure μ] (W : ℝ) :
    Measurable (fun w : Sphere d => projectionCollision μ (w:Space d) W) := by
  let S := {p : Sphere d × (Space d × Space d) |
    |inner ℝ (p.2.1-p.2.2) (p.1:Space d)| ≤ W}
  have hS : MeasurableSet S := by
    dsimp [S]
    exact measurableSet_le (by fun_prop) measurable_const
  exact measurable_measure_prodMk_left hS

theorem measurableSet_projectionGoodSet (μ : Measure (Space d)) [IsFiniteMeasure μ] (W T : ℝ) :
    MeasurableSet (projectionGoodSet μ W T) :=
  measurableSet_le (measurable_projectionCollision μ W) measurable_const

theorem projectionGoodSet_exceptional (μ : Measure (Space d)) [IsFiniteMeasure μ]
    (ν : Measure (Sphere d)) (W : ℝ) {T : ℝ} (hT : 0 < T) :
    ν (projectionGoodSet μ W T)ᶜ ≤
      (∫⁻ w : Sphere d, projectionCollision μ (w:Space d) W ∂ν)/ENNReal.ofReal T := by
  have hsub : (projectionGoodSet μ W T)ᶜ ⊆
      {w : Sphere d | ENNReal.ofReal T ≤ projectionCollision μ (w:Space d) W} := by
    intro w hw
    change ¬ projectionCollision μ (w:Space d) W ≤ ENNReal.ofReal T at hw
    exact (lt_of_not_ge hw).le
  exact (measure_mono hsub).trans (meas_ge_le_lintegral_div
    (measurable_projectionCollision μ W).aemeasurable
    (ENNReal.ofReal_pos.mpr hT).ne' ENNReal.ofReal_ne_top)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_ProjectionRescaling
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Projection collisions under the actual cell rescaling -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem projectionCollision_cellScaleMap (ρ : Measure (Space d)) [IsFiniteMeasure ρ]
    (p : ℕ) (c w : Space d) (W : ℝ) :
    projectionCollision (Measure.map (Regularization.cellScaleMap p c) ρ) w ((2:ℝ)^p*W) =
      projectionCollision ρ w W := by
  have hm := (Regularization.cellScaleMap_continuous p c).measurable
  rw [projectionCollision,Measure.map_prod_map ρ ρ hm hm,
    Measure.map_apply (hm.prodMap hm) (by measurability)]
  congr 1
  ext z
  simp only [mem_preimage,mem_ofPred_eq,Prod.map_fst,Prod.map_snd]
  have he : Regularization.cellScaleMap p c z.1-Regularization.cellScaleMap p c z.2 =
      (2:ℝ)^p • (z.1-z.2) := by unfold Regularization.cellScaleMap; module
  have hp : 0 < (2:ℝ)^p := by positivity
  rw [he,real_inner_smul_left,abs_mul,abs_of_pos hp]
  exact mul_le_mul_iff_right₀ hp

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_ProjectionSinc
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Scalar sinc comparison on the required all-dimensional projection -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem projection_collision_band : ∃ C : ℝ, 0 < C ∧
    ∀ (μ : Measure (Space d)) [IsFiniteMeasure μ] (w : Space d) (A H : ℝ),
      0 < A → 0 ≤ H → A ≤ 2*Real.pi*H →
      A*(projectionCollision μ w (100/A)).toReal ≤
        C*(2*Real.pi)*(∫ r in Icc (-H) H, ‖PlanarFalconer.sourceFourier μ (r • w)‖^2) := by
  obtain ⟨C,hC,hbound⟩ := projection_collision_fourier (d := d)
  refine ⟨C,hC,?_⟩
  intro μ _ w A H hA hH hAH
  have hi : IntegrableOn (fun r => ‖charFun (scalarProjectionLaw μ w) r‖^2)
      (Icc (-(2*Real.pi*H)) (2*Real.pi*H)) := by
    simpa only [one_mul,IntegrableOn] using PlanarFalconer.charFun_sq_integrable_finite
      (scalarProjectionLaw μ w) (volume.restrict (Icc (-(2*Real.pi*H)) (2*Real.pi*H))) 1
  have hsub : Icc (-A) A ⊆ Icc (-(2*Real.pi*H)) (2*Real.pi*H) := by
    intro r hr
    constructor <;> linarith [hr.1,hr.2]
  have hmono := integral_mono_measure (Measure.restrict_mono hsub le_rfl)
    (Filter.Eventually.of_forall (fun r => sq_nonneg ‖charFun (scalarProjectionLaw μ w) r‖)) hi
  have hscale := PlanarFalconer.integral_scale_Icc
    (fun r => ‖charFun (scalarProjectionLaw μ w) r‖^2)
    (A := 2*Real.pi) (u := H) (by positivity) hH
  simp_rw [norm_charFun_scalarProjectionLaw] at hscale
  have he : -(2*Real.pi)*H = -(2*Real.pi*H) := by ring
  rw [he] at hscale
  calc
    _ ≤ C*(∫ r in Icc (-A) A, ‖charFun (scalarProjectionLaw μ w) r‖^2) := hbound μ w A hA
    _ ≤ C*(∫ r in Icc (-(2*Real.pi*H)) (2*Real.pi*H),
        ‖charFun (scalarProjectionLaw μ w) r‖^2) := mul_le_mul_of_nonneg_left hmono hC.le
    _ = _ := by rw [← hscale]; ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_RadialIntervalEnergy
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Converting the proved frequency bound back to angular averages -/

namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem radial_interval_lintegral (μ : Measure (Space d)) [IsFiniteMeasure μ]
    (ν : Measure (Sphere d)) [IsFiniteMeasure ν] (H : ℝ) :
    (∫⁻ v, ENNReal.ofReal (‖PlanarFalconer.sourceFourier μ v‖^2) ∂radialIntervalMeasure ν H) =
      ∫⁻ r : ℝ in Icc (-H) H, ∫⁻ w : Sphere d,
        ENNReal.ofReal (‖PlanarFalconer.sourceFourier μ (r • (w:Space d))‖^2) ∂ν := by
  rw [radialIntervalMeasure,lintegral_map (by unfold PlanarFalconer.sourceFourier; fun_prop)
    (by unfold radialFrequencyMap; fun_prop)]
  exact lintegral_prod _ (by unfold radialFrequencyMap PlanarFalconer.sourceFourier; fun_prop)

theorem dyadic_half_dimensional_average (μ : Measure (Space d)) [IsProbabilityMeasure μ]
    (ν : Measure (Sphere d)) [IsFiniteMeasure ν]
    {D R K L : ℝ} (hD : 0 ≤ D) (hsupport : ∀ᵐ x ∂μ, ‖x‖ ≤ D)
    (n : ℕ) (hR : (2:ℝ)^n ≤ R) (hK : 1 ≤ K) (hL : 1 ≤ L) (hmass : ν univ ≤ 1)
    (hμ : ∀ x : Space d, ∀ r : ℝ, 1/(2:ℝ)^n ≤ r → r ≤ 1 →
      μ (ball x r) ≤ ENNReal.ofReal (K*r^((d:ℝ)/2)))
    (hν : ∀ x : Space d, ∀ r : ℝ, 1/R ≤ r → r ≤ 1 →
      ν {w : Sphere d | dist (w:Space d) x < r} ≤ ENNReal.ofReal (L*r^((d:ℝ)/2))) :
    (∫⁻ w : Sphere d, (∫⁻ r : ℝ in Icc (-((2:ℝ)^n)) ((2:ℝ)^n),
      ENNReal.ofReal (‖PlanarFalconer.sourceFourier μ (r • (w:Space d))‖^2)) ∂ν) ≤
      ENNReal.ofReal (2+(n:ℝ)*(halfDimensionalShellConstant d*
        (Real.exp ((Real.pi^2/2)*D^2))^2*K*L)) := by
  have hswap : (∫⁻ w : Sphere d, (∫⁻ r : ℝ in Icc (-((2:ℝ)^n)) ((2:ℝ)^n),
      ENNReal.ofReal (‖PlanarFalconer.sourceFourier μ (r • (w:Space d))‖^2)) ∂ν) =
      ∫⁻ r : ℝ in Icc (-((2:ℝ)^n)) ((2:ℝ)^n), ∫⁻ w : Sphere d,
        ENNReal.ofReal (‖PlanarFalconer.sourceFourier μ (r • (w:Space d))‖^2) ∂ν := by
    apply lintegral_lintegral_swap
    unfold PlanarFalconer.sourceFourier
    fun_prop
  rw [hswap,← radial_interval_lintegral]
  exact dyadic_half_dimensional_fourier μ ν hD hsupport n hR hK hL hmass hμ hν

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_ProjectionCollisionMean
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Averaged projection collisions from the half-dimensional Fourier bound -/

namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem projection_collision_lintegral_band : ∃ C : ℝ, 0 < C ∧
    ∀ (μ : Measure (Space d)) [IsFiniteMeasure μ] (w : Space d) (ε H : ℝ),
      0 < ε → 0 ≤ H → 100/ε ≤ 2*Real.pi*H →
      projectionCollision μ w ε ≤ ENNReal.ofReal (C*ε)*
        ∫⁻ r : ℝ in Icc (-H) H, ENNReal.ofReal (‖PlanarFalconer.sourceFourier μ (r • w)‖^2) := by
  obtain ⟨C,hC,hbound⟩ := projection_collision_band (d := d)
  refine ⟨C*(2*Real.pi)/100,by positivity,?_⟩
  intro μ _ w ε H hε hH hscale
  have hA : 0 < 100/ε := by positivity
  have h := hbound μ w (100/ε) H hA hH hscale
  have hw : 100/(100/ε) = ε := by field_simp
  rw [hw] at h
  have hi : IntegrableOn (fun r : ℝ => ‖PlanarFalconer.sourceFourier μ (r • w)‖^2)
      (Icc (-H) H) := by
    have hc : Continuous (fun r : ℝ => ‖PlanarFalconer.sourceFourier μ (r • w)‖^2) := by
      unfold PlanarFalconer.sourceFourier
      fun_prop
    exact hc.continuousOn.integrableOn_compact isCompact_Icc
  have hr : (projectionCollision μ w ε).toReal ≤ (C*(2*Real.pi)/100*ε)*
      ∫ r in Icc (-H) H, ‖PlanarFalconer.sourceFourier μ (r • w)‖^2 := by
    apply (le_of_mul_le_mul_left _ hA)
    calc
      _ ≤ C*(2*Real.pi)*(∫ r in Icc (-H) H, ‖PlanarFalconer.sourceFourier μ (r • w)‖^2) := h
      _ = _ := by field_simp
  have hp : projectionCollision μ w ε ≠ ∞ := measure_ne_top (μ.prod μ) _
  rw [← ENNReal.ofReal_toReal hp]
  have hh := ENNReal.ofReal_le_ofReal hr
  rwa [ENNReal.ofReal_mul (by positivity),
    ofReal_integral_eq_lintegral_ofReal hi (by filter_upwards with r; positivity)] at hh

theorem averaged_projection_collision : ∃ C : ℝ, 0 < C ∧
    ∀ (μ : Measure (Space d)) [IsProbabilityMeasure μ]
      (ν : Measure (Sphere d)) [IsFiniteMeasure ν] (D R K L : ℝ),
      0 ≤ D → (∀ᵐ x ∂μ, ‖x‖ ≤ D) → ∀ n : ℕ, (2:ℝ)^n ≤ R → 1 ≤ K → 1 ≤ L →
      ν univ ≤ 1 →
      (∀ x : Space d, ∀ r : ℝ, 1/(2:ℝ)^n ≤ r → r ≤ 1 →
        μ (ball x r) ≤ ENNReal.ofReal (K*r^((d:ℝ)/2))) →
      (∀ x : Space d, ∀ r : ℝ, 1/R ≤ r → r ≤ 1 →
        ν {w : Sphere d | dist (w:Space d) x < r} ≤ ENNReal.ofReal (L*r^((d:ℝ)/2))) →
      ∀ ε : ℝ, 0 < ε → 100/ε ≤ 2*Real.pi*((2:ℝ)^n) →
      (∫⁻ w : Sphere d, projectionCollision μ (w:Space d) ε ∂ν) ≤
        ENNReal.ofReal (C*ε*(2+(n:ℝ)*(halfDimensionalShellConstant d*
          (Real.exp ((Real.pi^2/2)*D^2))^2*K*L))) := by
  obtain ⟨C,hC,hpoint⟩ := projection_collision_lintegral_band (d := d)
  refine ⟨C,hC,?_⟩
  intro μ _ ν _ D R K L hD hsupport n hR hK hL hmass hμ hν ε hε hscale
  calc
    _ ≤ ∫⁻ w : Sphere d, ENNReal.ofReal (C*ε)*
        (∫⁻ r : ℝ in Icc (-((2:ℝ)^n)) ((2:ℝ)^n),
          ENNReal.ofReal (‖PlanarFalconer.sourceFourier μ (r • (w:Space d))‖^2)) ∂ν :=
      lintegral_mono (fun w => hpoint μ (w:Space d) ε ((2:ℝ)^n) hε (by positivity) hscale)
    _ = ENNReal.ofReal (C*ε)*(∫⁻ w : Sphere d,
        (∫⁻ r : ℝ in Icc (-((2:ℝ)^n)) ((2:ℝ)^n),
          ENNReal.ofReal (‖PlanarFalconer.sourceFourier μ (r • (w:Space d))‖^2)) ∂ν) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (C*ε)*ENNReal.ofReal (2+(n:ℝ)*(halfDimensionalShellConstant d*
        (Real.exp ((Real.pi^2/2)*D^2))^2*K*L)) :=
      mul_le_mul_right (dyadic_half_dimensional_average μ ν hD hsupport n hR hK hL hmass hμ hν) _
    _ = _ := (ENNReal.ofReal_mul (by positivity)).symm

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_ProjectionProfileAlgebra
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Scalar absorption for the projection-test average -/

namespace Falconer

theorem projection_profile_scalar_bound {R H C F A k a sig n N : ℝ}
    (hR : 1 ≤ R) (hH : 0 < H) (hC : 0 ≤ C) (hF : 0 ≤ F) (hA : 0 ≤ A)
    (hk : 0 ≤ k) (ha : 0 ≤ a) (hsig : 0 < sig) (hn : 0 ≤ n) (hnN : n ≤ N)
    (hcoef : (4*C+2*C*F*A)*(1+2*N) ≤ R^sig) :
    C*(2*R^(500*sig)/H)*(2+n*(F*(A*R^(k+a*sig))*R^sig)) ≤
      (1/H)*R^(k+(a+502)*sig) := by
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have hpower : 1 ≤ R^(k+(a+1)*sig) := Real.one_le_rpow hR (by positivity)
  have hinner : 2+n*(F*(A*R^(k+a*sig))*R^sig) ≤
      (2+n*F*A)*R^(k+(a+1)*sig) := by
    have he : R^(k+a*sig)*R^sig = R^(k+(a+1)*sig) := by
      rw [← Real.rpow_add hRp]
      congr 1
      ring
    calc
      _ = 2+(n*F*A)*(R^(k+a*sig)*R^sig) := by ring
      _ = 2+(n*F*A)*R^(k+(a+1)*sig) := by rw [he]
      _ ≤ 2*R^(k+(a+1)*sig)+(n*F*A)*R^(k+(a+1)*sig) := by nlinarith
      _ = _ := by ring
  have hpoly : 2*C*(2+n*F*A) ≤ (4*C+2*C*F*A)*(1+2*N) := by
    have hN : 0 ≤ N := hn.trans hnN
    have hn' : n ≤ 2*N := by linarith
    have hc : 0 ≤ 2*C*F*A := by positivity
    have hh := mul_le_mul_of_nonneg_left hn' hc
    have hh' : 0 ≤ 4*C*(2*N) := by positivity
    nlinarith
  calc
    _ ≤ C*(2*R^(500*sig)/H)*((2+n*F*A)*R^(k+(a+1)*sig)) :=
      mul_le_mul_of_nonneg_left hinner (by positivity)
    _ = (1/H)*(2*C*(2+n*F*A))*R^(k+(a+501)*sig) := by
      have he : R^(500*sig)*R^(k+(a+1)*sig) = R^(k+(a+501)*sig) := by
        rw [← Real.rpow_add hRp]
        congr 1
        ring
      rw [← he]
      ring
    _ ≤ (1/H)*R^sig*R^(k+(a+501)*sig) := by
      gcongr
      exact hpoly.trans hcoef
    _ = _ := by
      rw [mul_assoc,← Real.rpow_add hRp]
      congr 2
      ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_ProjectionProfileMean
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform projection averages for a finite-scale profile loss -/

namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem uniform_projection_profile_mean {sig D A a : ℝ}
    (hsig : 0 < sig) (hD : 0 ≤ D) (hA : 1 ≤ A) (ha : 0 ≤ a) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ n ≤ N, ∀ k : ℝ, 0 ≤ k →
      ∀ (μ : Measure (Space d)) [IsProbabilityMeasure μ]
        (ν : Measure (Sphere d)) [IsFiniteMeasure ν],
      (∀ᵐ x ∂μ, ‖x‖ ≤ D) → ν univ ≤ 1 →
      (∀ x : Space d, ∀ r : ℝ, 1/(2:ℝ)^n ≤ r → r ≤ 1 →
        μ (ball x r) ≤ ENNReal.ofReal
          (A*((2:ℝ)^N)^(k+a*sig)*r^((d:ℝ)/2))) →
      (∀ x : Space d, ∀ r : ℝ, 1/(2:ℝ)^N ≤ r → r ≤ 1 →
        ν {w : Sphere d | dist (w:Space d) x < r} ≤
          ENNReal.ofReal (((2:ℝ)^N)^sig*r^((d:ℝ)/2))) →
      (∫⁻ w : Sphere d, projectionCollision μ (w:Space d)
        (2*((2:ℝ)^N)^(500*sig)/(2:ℝ)^n) ∂ν) ≤
      ENNReal.ofReal ((1/(2:ℝ)^n)*((2:ℝ)^N)^(k+(a+502)*sig)) := by
  obtain ⟨C,hC,hmean⟩ := averaged_projection_collision (d := d)
  let F := halfDimensionalShellConstant d*(Real.exp ((Real.pi^2/2)*D^2))^2
  have hF : 0 ≤ F := mul_nonneg (halfDimensionalShellConstant_nonneg d) (sq_nonneg _)
  have hA₀ : 0 ≤ A := zero_le_one.trans hA
  obtain ⟨N₁,hpoly⟩ := PlanarFalconer.fixed_linear_subpower
    (4*C+2*C*F*A) (by positivity) hsig
  obtain ⟨N₂,hscale⟩ := Regularization.fixed_constant_absorbed
    (by positivity : 0 < 500*sig) (25/Real.pi)
  refine ⟨max N₁ N₂,?_⟩
  intro N hN n hn k hk μ _ ν _ hsupport hmass hμ hν
  let R : ℝ := (2:ℝ)^N
  let H : ℝ := (2:ℝ)^n
  have hR : 1 ≤ R := one_le_pow₀ (by norm_num)
  have hH : 0 < H := by positivity
  have hK : 1 ≤ A*R^(k+a*sig) := one_le_mul_of_one_le_of_one_le hA
    (Real.one_le_rpow hR (by positivity))
  have hL : 1 ≤ R^sig := Real.one_le_rpow hR hsig.le
  have hscale' : 100/(2*R^(500*sig)/H) ≤ 2*Real.pi*H := by
    have hh : 25/Real.pi ≤ R^(500*sig) := hscale N ((le_max_right _ _).trans hN)
    have hp : 0 < R^(500*sig) := by positivity
    have hpi : 0 < Real.pi := Real.pi_pos
    have hlow : 25 ≤ Real.pi*R^(500*sig) := by
      simpa only [mul_comm] using (div_le_iff₀ hpi).mp hh
    apply (div_le_iff₀ (by positivity : 0 < 2*R^(500*sig)/H)).mpr
    have he : (2*Real.pi*H)*(2*R^(500*sig)/H) = 4*(Real.pi*R^(500*sig)) := by
      field_simp
      ring
    rw [he]
    linarith
  have hm := hmean μ ν D R (A*R^(k+a*sig)) (R^sig) hD hsupport n
    (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hn) hK hL hmass hμ hν
    (2*R^(500*sig)/H) (by positivity) hscale'
  apply hm.trans
  apply ENNReal.ofReal_le_ofReal
  exact projection_profile_scalar_bound hR hH hC.le hF hA₀ hk ha hsig
    (Nat.cast_nonneg n) (by exact_mod_cast hn) (hpoly N ((le_max_left _ _).trans hN))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_ProjectionExceptional
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exceptional mass for the original conditional-class projection tests -/

namespace Falconer.Regularization
open Set Metric MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem uniform_projection_exceptional {sig : ℝ} (hsig : 0 < sig) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (Q : DyadicCube d), Q.side = 1 →
      ∀ (μ : Measure (Space d)) [IsProbabilityMeasure μ], ∀ B : ℕ,
      0 < B → (B:ℝ) ≤ sig*(N:ℝ) → (2:ℝ)^(N/B+2) ≤ ((2:ℝ)^N)^sig →
      ∀ p₀ ∈ regularizationLeaves Q μ N, ∀ p t : ℕ, p ≤ t → t ≤ N →
      ∀ P : CellPath d, P.length = p →
      0 < sourceClass Q μ N B p₀ (Q.descendant P).carrier →
      ∀ ν : Measure (Sphere d), ν univ ≤ 1 →
      (∀ x : Space d, ∀ r : ℝ, ((2:ℝ)^N)^(-1:ℝ) ≤ r → r ≤ 1 →
        ν {w : Sphere d | dist (w:Space d) x < r} ≤
          ENNReal.ofReal (((2:ℝ)^N)^sig*r^((d:ℝ)/2))) →
      ν (projectionGoodSet
        (ProbabilityTheory.cond (sourceClass Q μ N B p₀) (Q.descendant P).carrier)
        (2*((2:ℝ)^N)^(500*sig)/(2:ℝ)^t)
        ((1/(2:ℝ)^(t-p))*((2:ℝ)^N)^(
          profileDrop (sourceProfile Q μ N B p₀) N ((d:ℝ)/2) p t+
          1000*((d:ℝ)+1)*sig)))ᶜ ≤ ENNReal.ofReal (((2:ℝ)^N)^(-sig)) := by
  let s : ℝ := (d:ℝ)/2
  let A : ℝ := (((2*Nat.ceil (2+4*Real.sqrt d)+1)^d:ℕ):ℝ)*(2:ℝ)^s
  have hs : 0 ≤ s := by dsimp [s]; positivity
  have hA : 1 ≤ A := by
    apply one_le_mul_of_one_le_of_one_le
    · exact_mod_cast one_le_pow₀ (show (1:ℕ) ≤ 2*Nat.ceil (2+4*Real.sqrt d)+1 by omega)
    · exact Real.one_le_rpow (by norm_num) hs
  obtain ⟨N₁,hmean⟩ := uniform_projection_profile_mean (d := d) hsig
    (Real.sqrt_nonneg d) hA (show 0 ≤ 2*((d:ℝ)+1) by positivity)
  refine ⟨max 1 N₁,?_⟩
  intro N hN Q hQ μ _ B hB hwidth hlarge p₀ hp₀ p t hpt htN P hP hocc ν hmass hball
  have hNp : 0 < N := lt_of_lt_of_le (by omega : 0 < 1) ((le_max_left _ _).trans hN)
  have hside : 0 < Q.side := by rw [hQ]; norm_num
  let ρ := ProbabilityTheory.cond (sourceClass Q μ N B p₀) (Q.descendant P).carrier
  let α := Measure.map (cellScaleMap p (Q.descendant P).center) ρ
  have : IsProbabilityMeasure ρ := sourceClass_conditional_probability Q hside μ N B hp₀ P hocc
  have : IsProbabilityMeasure α := by dsimp [α]; (first | exact Measure.isProbabilityMeasure_map (by first | (apply Continuous.aemeasurable; apply cellScaleMap_continuous <;> assumption)) | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))
  have : IsFiniteMeasure ν := ⟨hmass.trans_lt (by norm_num)⟩
  let R : ℝ := (2:ℝ)^N
  let H : ℝ := (2:ℝ)^(t-p)
  let k := profileDrop (sourceProfile Q μ N B p₀) N s p t
  have hR : 1 ≤ R := one_le_pow₀ (by norm_num)
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have hHp : 0 < H := by positivity
  have hsupport : ∀ᵐ z ∂α, ‖z‖ ≤ Real.sqrt d := by
    simpa only [hP] using rescaled_conditional_support Q hQ (sourceClass Q μ N B p₀) P
  have hν : ∀ x : Space d, ∀ r : ℝ, 1/(2:ℝ)^N ≤ r → r ≤ 1 →
      ν {w : Sphere d | dist (w:Space d) x < r} ≤ ENNReal.ofReal (R^sig*r^((d:ℝ)/2)) := by
    intro x r hr hr₁
    apply hball x r _ hr₁
    simpa only [Real.rpow_neg_one,one_div] using hr
  have hm := hmean N ((le_max_right _ _).trans hN) (t-p) (by omega) k
    (profileDrop_nonneg _ _ _ hpt) α ν hsupport hmass
    (sourceClass_conditional_frostman Q hQ μ hNp hB hs hwidth hlarge hp₀ hpt htN hP hocc) hν
  have hpow : (2:ℝ)^t = (2:ℝ)^p*(2:ℝ)^(t-p) := by
    rw [← pow_add]
    congr 1
    omega
  have hscale : (2:ℝ)^p*(2*R^(500*sig)/(2:ℝ)^t) = 2*R^(500*sig)/H := by
    rw [hpow]
    dsimp [H]
    field_simp
  have hgood : projectionGoodSet α (2*R^(500*sig)/H)
      ((1/H)*R^(k+1000*((d:ℝ)+1)*sig)) =
      projectionGoodSet ρ (2*R^(500*sig)/(2:ℝ)^t)
      ((1/H)*R^(k+1000*((d:ℝ)+1)*sig)) := by
    rw [← hscale]
    ext w
    simp only [projectionGoodSet,mem_ofPred_eq,α,
      projectionCollision_cellScaleMap]
  change ν (projectionGoodSet ρ _ _)ᶜ ≤ _
  rw [← hgood]
  apply (projectionGoodSet_exceptional α ν _ (by positivity :
    0 < (1/H)*R^(k+1000*((d:ℝ)+1)*sig))).trans
  apply (ENNReal.div_le_div_right hm _).trans
  rw [← ENNReal.ofReal_div_of_pos (by positivity)]
  have he : ((1/H)*R^(k+(2*((d:ℝ)+1)+502)*sig))/
      ((1/H)*R^(k+1000*((d:ℝ)+1)*sig)) =
      R^((k+(2*((d:ℝ)+1)+502)*sig)-(k+1000*((d:ℝ)+1)*sig)) := by
    rw [mul_div_mul_left _ _ (by positivity : (1/H) ≠ 0),← Real.rpow_sub hRp]
  rw [he]
  apply ENNReal.ofReal_le_ofReal
  apply Real.rpow_le_rpow_of_exponent_le hR
  have hd : 0 ≤ (d:ℝ) := Nat.cast_nonneg d
  nlinarith

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_ConditionalProjectionTest
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Literal occupied-anchor projection tests -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

namespace Regularization

theorem conditionalProjectionGoodSet_measurable (Q : DyadicCube d)
    (ρ : Measure (Space d)) [IsFiniteMeasure ρ] (P : CellPath d) (W T : ℝ) :
    MeasurableSet (conditionalProjectionGoodSet Q ρ P W T) := by
  classical
  unfold conditionalProjectionGoodSet
  split_ifs
  · exact measurableSet_projectionGoodSet _ _ _
  · exact MeasurableSet.empty

end Regularization
end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_DescriptorTests
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual all-dimensional tests indexed by policy descriptors

The policy list is scalar. Its tests use original occupied cells and the
full conditional probability of the current ambient-dimensional class.
The tolerance is the manuscript's 500-sigma width at every level.
-/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
open PlanarFalconer (PolicyDescriptor descriptorAnchor descriptorLength)

variable {d : ℕ}

theorem descriptorGoodDirections_measurable (Q : DyadicCube d) (ρ : Measure (Space d))
    [IsFiniteMeasure ρ] (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ)
    (P : List (Fin d → Bool)) (b : PolicyDescriptor) :
    MeasurableSet (descriptorGoodDirections Q ρ m N σ J i P b) := by
  cases b with
  | parallel g p => exact Regularization.parallelGoodSet_measurable _ _ _ _ _ _ _
  | projection p t => exact Regularization.conditionalProjectionGoodSet_measurable _ _ _ _ _

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_DescriptorMasks
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual anchored masks and retained pair tests in every dimension

The angular set at an anchor is tested against the full conditional law.
Masks use finite spherical nets at one eighth of the manuscript's buffer
radius. Their construction is independent of the number of anchor cells.
-/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff Topology
open PlanarFalconer (PolicyDescriptor descriptorAnchor descriptorLength)
variable {d : ℕ}

theorem descriptorEndpointGood_measurable (Q : DyadicCube d) (ρ : Measure (Space d))
    [IsFiniteMeasure ρ] (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ)
    (b : PolicyDescriptor) :
    MeasurableSet (descriptorEndpointGood Q ρ m N σ J i b) := by
  classical
  have hm : MeasurableSet (⋂ p ∈ cubePaths d (descriptorAnchor b),
      {z : Space d × Sphere d | z.1 ∈ (Q.descendant p).carrier →
        z.2 ∈ descriptorGoodDirections Q ρ m N σ J i p b}) := by
    apply Finset.measurableSet_biInter
    intro p _
    convert ((Q.descendant p).measurable.preimage measurable_fst).compl.union
      ((descriptorGoodDirections_measurable Q ρ m N σ J i p b).preimage measurable_snd) using 1
    all_goals try with_reducible_and_instances rfl
    ext z
    simp only [mem_ofPred_eq,mem_union,mem_compl_iff,mem_preimage,imp_iff_not_or]
  convert hm using 1
  all_goals try with_reducible_and_instances rfl
  ext z
  simp [descriptorEndpointGood]

theorem descriptorEndpointGood_on_cell (Q : DyadicCube d) (ρ : Measure (Space d))
    (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ) (b : PolicyDescriptor)
    (p : List (Fin d → Bool)) (hp : p.length = descriptorAnchor b)
    {x : Space d} (hx : x ∈ (Q.descendant p).carrier) (w : Sphere d) :
    (x,w) ∈ descriptorEndpointGood Q ρ m N σ J i b ↔
      w ∈ descriptorGoodDirections Q ρ m N σ J i p b := by
  constructor
  · exact fun h => h p ((mem_cubePaths _ _ _).mpr hp) hx
  · intro hw q hq hxq
    have hqp : q = p := by
      by_contra hn
      exact Set.disjoint_left.mp
        (Q.descendants_disjoint (((mem_cubePaths _ _ _).mp hq).trans hp.symm) hn) hxq hx
    simpa only [hqp] using hw

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_DescriptorExceptional
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exceptional-direction bounds for each actual level-zero descriptor

The angular measure is a restriction of the original opposite marginal;
its cap constant is never divided by a class mass.
-/

namespace Falconer.Regularization
open Set MeasureTheory
open scoped ENNReal
open PlanarFalconer (PolicyDescriptor descriptorAnchor)
variable {d : ℕ}

 theorem uniform_descriptor_exceptional {σ : ℝ} (hσ : 0 < σ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (Q : DyadicCube d), Q.side = 1 →
      ∀ (μ : Measure (Space d)) [IsProbabilityMeasure μ], ∀ B : ℕ,
      0 < B → (B:ℝ) ≤ σ*(N:ℝ) → (2:ℝ)^(N/B+2) ≤ ((2:ℝ)^N)^σ →
      ∀ p₀ ∈ regularizationLeaves Q μ N, ∀ b : PolicyDescriptor, descriptorValid N b →
      ∀ P : CellPath d, P.length = descriptorAnchor b →
      0 < sourceClass Q μ N B p₀ (Q.descendant P).carrier →
      ∀ ν : Measure (Sphere d), ν univ ≤ 1 →
      (∀ x : Space d, ∀ r : ℝ, ((2:ℝ)^N)^(-1:ℝ) ≤ r → r ≤ 1 →
        ν {w : Sphere d | dist (w:Space d) x < r} ≤
          ENNReal.ofReal (((2:ℝ)^N)^σ*r^((d:ℝ)/2))) →
      ∀ J : ℕ,
      ν (descriptorGoodDirections Q (sourceClass Q μ N B p₀)
        (fun u => sourceUnitProfile Q μ N B p₀ (u/N)) N σ J 0 P b)ᶜ ≤
        ENNReal.ofReal (((2:ℝ)^N)^(-σ)) := by
  obtain ⟨Np,hp⟩ := uniform_parallel_exceptional (d := d) hσ
  obtain ⟨Nt,ht⟩ := uniform_projection_exceptional (d := d) hσ
  refine ⟨max 1 (max Np Nt),?_⟩
  intro N hN Q hQ μ _ B hB hwidth hlarge p₀ hp₀ b hb P hP hocc ν hmass hball J
  have hNp : 0 < N := by omega
  have hwidthEq (n : ℕ) : angularTestWidth N σ J 0 n =
      2*((2:ℝ)^N)^(500*σ)/(2:ℝ)^n := by
    rw [angularTestWidth_zero]
    ring
  cases b with
  | parallel g p =>
    have hh := hp N (by omega) Q hQ μ B hB hwidth hlarge p₀ hp₀
      g p hb.1 hb.2 P hP hocc ν hmass hball
    simpa only [descriptorGoodDirections,hwidthEq,sourceUnitProfile_at_depth Q μ hNp] using hh
  | projection p t =>
    have hh := ht N (by omega) Q hQ μ B hB hwidth hlarge p₀ hp₀
      p t hb.1 hb.2 P hP hocc ν hmass hball
    have hgood : descriptorGoodDirections Q (sourceClass Q μ N B p₀)
        (fun u => sourceUnitProfile Q μ N B p₀ (u/N)) N σ J 0 P (.projection p t) =
        projectionGoodSet (ProbabilityTheory.cond (sourceClass Q μ N B p₀) (Q.descendant P).carrier)
          (2*((2:ℝ)^N)^(500*σ)/(2:ℝ)^t)
          ((1/(2:ℝ)^(t-p))*((2:ℝ)^N)^(
            profileDrop (sourceProfile Q μ N B p₀) N ((d:ℝ)/2) p t+1000*((d:ℝ)+1)*σ)) := by
      simp only [descriptorGoodDirections,conditionalProjectionGoodSet,ite_eq_left hocc,
        hwidthEq,profileDrop,sourceUnitProfile_at_depth Q μ hNp]
    rw [hgood]
    exact hh

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Measures_ClassSupport
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Original support and occupied anchors of the normalized classes -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

 theorem ae_occupied_anchors (Q : DyadicCube d) (ρ : Measure (Space d)) :
    ∀ᵐ x ∂ρ, ∀ P : List (Fin d → Bool), x ∈ (Q.descendant P).carrier →
      0 < ρ (Q.descendant P).carrier := by
  apply ae_all_iff.mpr
  intro P
  by_cases hp : 0 < ρ (Q.descendant P).carrier
  · exact Filter.Eventually.of_forall (fun _ _ => hp)
  · have hz : ρ (Q.descendant P).carrier = 0 := le_antisymm (not_lt.mp hp) (by positivity)
    have he : ∀ᵐ x ∂ρ, x ∉ (Q.descendant P).carrier := ae_iff.mpr (by simpa using hz)
    filter_upwards [he] with x hx
    exact fun hp => (hx hp).elim

namespace Regularization

 theorem normalizedClass_absolutelyContinuous (Q : DyadicCube d) (μ : Measure (Space d))
    (L : Finset (CellPath d)) (f : CellPath d → List ℕ) (T : List ℕ) :
    normalizedClass Q μ L f T ≪ μ :=
  Measure.smul_absolutelyContinuous.trans (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)

 theorem sourceClass_absolutelyContinuous (Q : DyadicCube d) (μ : Measure (Space d))
    (N B : ℕ) (p : CellPath d) : sourceClass Q μ N B p ≪ μ :=
  normalizedClass_absolutelyContinuous Q μ _ _ _

 theorem normalizedClass_parent (Q : DyadicCube d) (hQ : 0 < Q.side)
    (μ : Measure (Space d)) (L : Finset (CellPath d)) (f : CellPath d → List ℕ) (T : List ℕ) :
    normalizedClass Q μ L f T Q.carrierᶜ = 0 := by
  rw [normalizedClass_apply]
  have he : Q.carrierᶜ ∩ leafUnion Q (classLeaves L f T) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact hx.1 (leafUnion_subset Q hQ _ hx.2)
  rw [he,measure_empty,mul_zero]

 theorem sourceClass_parent (Q : DyadicCube d) (hQ : 0 < Q.side)
    (μ : Measure (Space d)) (N B : ℕ) (p : CellPath d) :
    sourceClass Q μ N B p Q.carrierᶜ = 0 :=
  normalizedClass_parent Q hQ μ _ _ _

end Regularization
end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianLebesgue
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A Lebesgue density for the standard Gaussian used in the band estimates -/

namespace Falconer
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal FourierTransform
variable {d : ℕ}

instance gaussianLebesgue_finite : IsFiniteMeasure (gaussianLebesgue d) := by
  apply isFiniteMeasure_withDensity
  rw [← ofReal_integral_eq_lintegral_ofReal
    (PlanarFalconer.gaussian_lebesgue_integrable (by norm_num : (0:ℝ) < 1/2))
    (Filter.Eventually.of_forall (fun _ => (Real.exp_pos _).le))]
  exact ENNReal.ofReal_ne_top

instance normalizedGaussianLebesgue_finite : IsFiniteMeasure (normalizedGaussianLebesgue d) := by
  refine ⟨?_⟩
  change ENNReal.ofReal (gaussianVolumeNormalization d)*gaussianLebesgue d univ < ∞
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_RadialSphereLaw
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Sphere-valued original radial laws, with a harmless diagonal value -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal
variable {d : ℕ}

theorem originalRadialSphereLaw_apply (w₀ : Sphere d) (ν : Measure (Space d))
    (G : Set (Space d × Space d)) (z : Space d) (B : Set (Sphere d)) (hB : MeasurableSet B) :
    originalRadialSphereLaw w₀ ν G z B =
      ν {x | (z,x) ∈ G ∧ normalizeToSphere w₀ (x-z) ∈ B} := by
  have hm : Measurable (fun x : Space d => normalizeToSphere w₀ (x-z)) :=
    (normalizeToSphere_measurable w₀).comp (measurable_id.sub measurable_const)
  rw [originalRadialSphereLaw,Measure.map_apply hm hB,Measure.restrict_apply (hB.preimage hm)]
  congr 1
  ext x
  exact and_comm

theorem originalRadialSphereLaw_mass_le (w₀ : Sphere d) (ν : Measure (Space d))
    (G : Set (Space d × Space d)) (z : Space d) :
    originalRadialSphereLaw w₀ ν G z Set.univ ≤ ν Set.univ := by
  rw [originalRadialSphereLaw_apply w₀ ν G z Set.univ MeasurableSet.univ]
  exact measure_mono (subset_univ _)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ValidDescriptors
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A polynomial finite family containing every descriptor used at a scale -/

namespace Falconer
open PlanarFalconer (PolicyDescriptor)
attribute [local instance] Classical.propDecidable

 theorem mem_validDescriptors (N : ℕ) (b : PolicyDescriptor) :
    b ∈ validDescriptors N ↔ descriptorValid N b := by
  constructor
  · exact fun hb => (Finset.mem_filter.mp hb).2
  · intro hb
    apply Finset.mem_filter.mpr
    refine ⟨?_,hb⟩
    cases b with
    | parallel g p =>
      apply Finset.mem_union_left
      apply Finset.mem_image.mpr
      exact ⟨(g,p),Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by
        change g ≤ p ∧ p ≤ N at hb; omega),Finset.mem_range.mpr (by
        change g ≤ p ∧ p ≤ N at hb; omega)⟩,rfl⟩
    | projection p t =>
      apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      exact ⟨(p,t),Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by
        change p ≤ t ∧ t ≤ N at hb; omega),Finset.mem_range.mpr (by
        change p ≤ t ∧ t ≤ N at hb; omega)⟩,rfl⟩

 theorem validDescriptors_card (N : ℕ) : (validDescriptors N).card ≤ 2*(N+1)^2 := by
  apply (Finset.card_filter_le _ _).trans
  apply (Finset.card_union_le _ _).trans
  have hp := Finset.card_image_le (s := Finset.range (N+1) ×ˢ Finset.range (N+1))
    (f := fun p => PolicyDescriptor.parallel p.1 p.2)
  have ht := Finset.card_image_le (s := Finset.range (N+1) ×ˢ Finset.range (N+1))
    (f := fun p => PolicyDescriptor.projection p.1 p.2)
  simpa only [Finset.card_product,Finset.card_range,pow_two,two_mul] using Nat.add_le_add hp ht

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_DescriptorTestBad
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Original-pair failure of the level-zero tests, before smoothing -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
open PlanarFalconer (PolicyDescriptor)
variable {d : ℕ}

 theorem descriptorTestBad_measurable (w₀ : Sphere d) (Q : DyadicCube d)
    (ρ : Measure (Space d)) [IsFiniteMeasure ρ] (profile : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J : ℕ) (b : PolicyDescriptor)
    {G : Set (Space d × Space d)} (hG : MeasurableSet G) :
    MeasurableSet (descriptorTestBad w₀ Q ρ profile N σ J b G) :=
  hG.inter (((descriptorEndpointGood_measurable Q ρ profile N σ J 0 b).preimage
    (measurable_fst.prodMk ((normalizeToSphere_measurable w₀).comp
      (measurable_snd.sub measurable_fst)))).compl)

namespace Regularization

 theorem uniform_source_test_bad_mass {σ : ℝ} (hσ : 0 < σ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (Q : DyadicCube d), Q.side = 1 →
      ∀ (μ : Measure (Space d)) [IsProbabilityMeasure μ], ∀ B : ℕ,
      0 < B → (B:ℝ) ≤ σ*(N:ℝ) → (2:ℝ)^(N/B+2) ≤ ((2:ℝ)^N)^σ →
      ∀ p₀ ∈ regularizationLeaves Q μ N, ∀ b : PolicyDescriptor, descriptorValid N b →
      ∀ (ν : Measure (Space d)) [IsProbabilityMeasure ν], ∀ w₀ : Sphere d,
      ∀ G : Set (Space d × Space d), MeasurableSet G →
      (∀ᵐ x ∂sourceClass Q μ N B p₀, ∀ u : Space d, ∀ r : ℝ,
        ((2:ℝ)^N)^(-1:ℝ) ≤ r → r ≤ 1 →
        originalRadialSphereLaw w₀ ν G x {w : Sphere d | dist (w:Space d) u < r} ≤
          ENNReal.ofReal (((2:ℝ)^N)^σ*r^((d:ℝ)/2))) →
      ∀ J : ℕ,
      ((sourceClass Q μ N B p₀).prod ν)
        (descriptorTestBad w₀ Q (sourceClass Q μ N B p₀)
          (fun u => sourceUnitProfile Q μ N B p₀ (u/N)) N σ J b G) ≤
        ENNReal.ofReal (((2:ℝ)^N)^(-σ)) := by
  obtain ⟨N₀,h₀⟩ := uniform_descriptor_exceptional (d := d) hσ
  refine ⟨N₀,?_⟩
  intro N hN Q hQ μ _ B hB hwidth hlarge p₀ hp₀ b hb ν _ w₀ G hG hcap J
  let ρ := sourceClass Q μ N B p₀
  let profile := fun u => sourceUnitProfile Q μ N B p₀ (u/N)
  have hside : 0 < Q.side := by rw [hQ]; norm_num
  let : IsProbabilityMeasure ρ := regularization_class_probability Q hside μ N B hp₀
  have hcarry : ∀ᵐ x ∂ρ, x ∈ Q.carrier := ae_iff.mpr (sourceClass_parent Q hside μ N B p₀)
  have hmass : ∀ᵐ x ∂ρ,
      ν {y | (x,y) ∈ descriptorTestBad w₀ Q ρ profile N σ J b G} ≤
        ENNReal.ofReal (((2:ℝ)^N)^(-σ)) := by
    filter_upwards [hcap,hcarry,ae_occupied_anchors Q ρ] with x hcx hx hocc
    obtain ⟨P,hP,hxp⟩ := Q.mem_descendant_at_depth (PlanarFalconer.descriptorAnchor b) hx
    have hlen := (mem_cubePaths _ _ _).mp hP
    let V := originalRadialSphereLaw w₀ ν G x
    have hv : V univ ≤ 1 := (originalRadialSphereLaw_mass_le w₀ ν G x).trans (by simp)
    have hh := h₀ N hN Q hQ μ B hB hwidth hlarge p₀ hp₀ b hb P hlen
      (hocc P hxp) V hv hcx J
    rw [originalRadialSphereLaw_apply w₀ ν G x _
      (descriptorGoodDirections_measurable Q ρ profile N σ J 0 P b).compl] at hh
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    ext y
    simp only [descriptorTestBad,mem_inter_iff,mem_ofPred_eq,mem_compl_iff,
      descriptorEndpointGood_on_cell Q ρ profile N σ J 0 b P hlen hxp]
  rw [Measure.prod_apply (descriptorTestBad_measurable w₀ Q ρ profile N σ J b hG)]
  exact (lintegral_mono_ae hmass).trans_eq (by rw [lintegral_const,measure_univ,mul_one])

end Regularization
end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_AllTestsRestoration
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One exceptional set restores every policy descriptor at the scale -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
open PlanarFalconer (PolicyDescriptor)
variable {d : ℕ}

 theorem allDescriptorTestBad_measurable (w₀ : Sphere d) (Q : DyadicCube d)
    (ρ : Measure (Space d)) [IsFiniteMeasure ρ] (profile : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J : ℕ) {G : Set (Space d × Space d)} (hG : MeasurableSet G) :
    MeasurableSet (allDescriptorTestBad w₀ Q ρ profile N σ J G) :=
  Finset.measurableSet_biUnion _ (fun b _ =>
    descriptorTestBad_measurable w₀ Q ρ profile N σ J b hG)

 theorem allDescriptorTestBad_mass (w₀ : Sphere d) (Q : DyadicCube d)
    (ρ ν : Measure (Space d)) (profile : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J : ℕ)
    (G : Set (Space d × Space d)) {ε : ℝ≥0∞}
    (hbad : ∀ b, descriptorValid N b →
      (ρ.prod ν) (descriptorTestBad w₀ Q ρ profile N σ J b G) ≤ ε) :
    (ρ.prod ν) (allDescriptorTestBad w₀ Q ρ profile N σ J G) ≤
      (2*(N+1)^2:ℕ)*ε := by
  apply (measure_biUnion_finset_le _ _).trans
  calc
    _ ≤ ∑ _b ∈ validDescriptors N, ε := Finset.sum_le_sum
      (fun b hb => hbad b ((mem_validDescriptors N b).mp hb))
    _ = ((validDescriptors N).card:ℝ≥0∞)*ε := by simp
    _ ≤ _ := mul_le_mul' (by exact_mod_cast validDescriptors_card N) le_rfl

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ClassRecombination
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianLebesgue_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.normalizedGaussianLebesgue_finite _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact recombination with the original class masses -/

namespace Falconer.Regularization
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

 theorem classMeasure_eq_mass_smul (Q : DyadicCube d) (μ : Measure (Space d))
    [IsFiniteMeasure μ] (L : Finset (CellPath d)) (f : CellPath d → List ℕ) (T : List ℕ)
    (hT : classMeasure Q μ L f T univ ≠ 0) :
    classMeasure Q μ L f T =
      classMeasure Q μ L f T univ • normalizedClass Q μ L f T := by
  let : IsFiniteMeasure (classMeasure Q μ L f T) := by unfold classMeasure; infer_instance
  rw [normalizedClass,smul_smul,ENNReal.mul_inv_cancel hT (measure_ne_top _ _),one_smul]

 theorem retained_class_mass_sum_le_one (Q : DyadicCube d) (hQ : 0 < Q.side)
    (μ : Measure (Space d)) [IsProbabilityMeasure μ]
    {N : ℕ} {L : Finset (CellPath d)} (hL : L ⊆ cubePaths d N)
    (f : CellPath d → List ℕ) (F : Finset (List ℕ)) (hF : F ⊆ L.image f) :
    (∑ T ∈ F, classMeasure Q μ L f T univ) ≤ 1 := by
  apply (Finset.sum_le_sum_of_subset hF).trans
  rw [class_mass_sum Q hQ μ hL f]
  exact prob_le_one

 theorem class_original_pair_bad_mass (Q : DyadicCube d) (μ ν : Measure (Space d))
    [IsFiniteMeasure μ] [SFinite ν] (L : Finset (CellPath d)) (f : CellPath d → List ℕ)
    (T : List ℕ) (hT : classMeasure Q μ L f T univ ≠ 0)
    (B : Set (Space d × Space d)) (hB : MeasurableSet B) {ε : ℝ≥0∞}
    (hsmall : ((normalizedClass Q μ L f T).prod ν) B ≤ ε) :
    (μ.prod ν) ((leafUnion Q (classLeaves L f T) ×ˢ univ) ∩ B) ≤
      classMeasure Q μ L f T univ*ε := by
  have he : (μ.prod ν) ((leafUnion Q (classLeaves L f T) ×ˢ univ) ∩ B) =
      ((classMeasure Q μ L f T).prod ν) B := by
    change _ = ((μ.restrict (leafUnion Q (classLeaves L f T))).prod ν) B
    conv_rhs => rw [← Measure.restrict_univ (μ := ν)]
    rw [Measure.prod_restrict,Measure.restrict_apply hB,inter_comm]
  have hp : (classMeasure Q μ L f T).prod ν =
      classMeasure Q μ L f T univ • ((normalizedClass Q μ L f T).prod ν) := by
    conv_lhs => rw [classMeasure_eq_mass_smul Q μ L f T hT]
    rw [Measure.prod_smul_left]
  rw [he,hp,Measure.smul_apply,smul_eq_mul]
  exact mul_le_mul' le_rfl hsmall

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ClassBadRecombination
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianLebesgue_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.normalizedGaussianLebesgue_finite _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Original class masses do not introduce a class-count loss -/

namespace Falconer.Regularization
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

 theorem retained_classes_bad_mass (Q : DyadicCube d) (hQ : 0 < Q.side)
    (μ ν : Measure (Space d)) [IsProbabilityMeasure μ] [SFinite ν]
    {N : ℕ} {L : Finset (CellPath d)} (hL : L ⊆ cubePaths d N)
    (f : CellPath d → List ℕ) (F : Finset (List ℕ)) (hF : F ⊆ L.image f)
    (hpos : ∀ T ∈ F, classMeasure Q μ L f T univ ≠ 0)
    (B : List ℕ → Set (Space d × Space d)) (hB : ∀ T ∈ F, MeasurableSet (B T))
    {ε : ℝ≥0∞} (hsmall : ∀ T ∈ F, ((normalizedClass Q μ L f T).prod ν) (B T) ≤ ε) :
    (μ.prod ν) (⋃ T ∈ F, (leafUnion Q (classLeaves L f T) ×ˢ univ) ∩ B T) ≤ ε := by
  apply (measure_biUnion_finset_le F _).trans
  calc
    _ ≤ ∑ T ∈ F, classMeasure Q μ L f T univ*ε := Finset.sum_le_sum
      (fun T hT => class_original_pair_bad_mass Q μ ν L f T (hpos T hT) (B T) (hB T hT) (hsmall T hT))
    _ = (∑ T ∈ F, classMeasure Q μ L f T univ)*ε := (Finset.sum_mul ..).symm
    _ ≤ 1*ε := mul_le_mul' (retained_class_mass_sum_le_one Q hQ μ hL f F hF) le_rfl
    _ = ε := one_mul ε

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_PairExceptional
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianLebesgue_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.normalizedGaussianLebesgue_finite _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Two-sided exceptional sets measured on the original pair -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem pairExceptional_mass (μ ν : Measure (Space d))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (A B : Set (Space d)) (D E : Set (Space d × Space d)) (hE : MeasurableSet E) :
    (μ.prod ν) (pairExceptional A B D E) ≤
      μ Aᶜ + ν Bᶜ + (μ.prod ν) D + (ν.prod μ) E := by
  apply (measure_union_le _ _).trans
  apply add_le_add ?_ ?_
  · apply (measure_union_le _ _).trans
    apply add_le_add ?_ le_rfl
    apply (measure_union_le _ _).trans
    simp only [Measure.prod_prod,measure_univ,mul_one,one_mul]
    exact le_rfl
  · exact le_of_eq ((Measure.measurePreserving_swap (μ := μ) (ν := ν)).measure_preimage hE.nullMeasurableSet)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_RegularizationTestBad
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Recombining the actual class test failures on the original product law -/

namespace Falconer.Regularization
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem sourceClass_eq_normalized (Q : DyadicCube d) (μ : Measure (Space d))
    (N B : ℕ) (p : CellPath d) (T : List ℕ) (hp : regularizationLabel Q μ N B p = T) :
    sourceClass Q μ N B p =
      normalizedClass Q μ (regularizationLeaves Q μ N) (regularizationLabel Q μ N B) T := by
  unfold sourceClass
  rw [hp]

theorem regularizationTestBad_measurable (w₀ : Sphere d) (Q : DyadicCube d)
    (μ : Measure (Space d)) [IsProbabilityMeasure μ]
    (N B : ℕ) (t : ℝ≥0∞) (σ : ℝ) (J : ℕ) (p : List ℕ → CellPath d)
    (hp : ∀ T ∈ regularizationIndex Q μ N B t, p T ∈ regularizationLeaves Q μ N)
    (hQ : 0 < Q.side) {G : Set (Space d × Space d)} (hG : MeasurableSet G) :
    MeasurableSet (regularizationTestBad w₀ Q μ N B t σ J p G) := by
  apply Finset.measurableSet_biUnion
  intro T hT
  let : IsProbabilityMeasure (sourceClass Q μ N B (p T)) :=
    regularization_class_probability Q hQ μ N B (hp T hT)
  exact ((regularizationSet_measurable Q μ N B T).prod MeasurableSet.univ).inter
    (allDescriptorTestBad_measurable w₀ Q _ _ N σ J hG)

theorem uniform_regularization_test_bad_mass {σ : ℝ} (hσ : 0 < σ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (Q : DyadicCube d), Q.side = 1 →
      ∀ (μ ν : Measure (Space d)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν],
      ∀ B : ℕ, 0 < B → (B:ℝ) ≤ σ*(N:ℝ) →
        (2:ℝ)^(N/B+2) ≤ ((2:ℝ)^N)^σ →
      ∀ t : ℝ≥0∞, 0 < t → ∀ p : List ℕ → CellPath d,
      (∀ T ∈ regularizationIndex Q μ N B t, p T ∈ regularizationLeaves Q μ N) →
      (∀ T ∈ regularizationIndex Q μ N B t, regularizationLabel Q μ N B (p T) = T) →
      ∀ (w₀ : Sphere d) (G : Set (Space d × Space d)), MeasurableSet G →
      (∀ᵐ x ∂μ, ∀ u : Space d, ∀ r : ℝ,
        ((2:ℝ)^N)^(-1:ℝ) ≤ r → r ≤ 1 →
        originalRadialSphereLaw w₀ ν G x {w : Sphere d | dist (w:Space d) u < r} ≤
          ENNReal.ofReal (((2:ℝ)^N)^σ*r^((d:ℝ)/2))) →
      ∀ J : ℕ, (μ.prod ν) (regularizationTestBad w₀ Q μ N B t σ J p G) ≤
        (2*(N+1)^2:ℕ)*ENNReal.ofReal (((2:ℝ)^N)^(-σ)) := by
  obtain ⟨N₀,h₀⟩ := uniform_source_test_bad_mass (d := d) hσ
  refine ⟨N₀,?_⟩
  intro N hN Q hQ μ ν _ _ B hB hwidth hlarge t ht p hp hlabel w₀ G hG hcap J
  have hside : 0 < Q.side := by rw [hQ]; norm_num
  apply retained_classes_bad_mass Q hside μ ν
    (fun P hP => (Finset.mem_filter.mp hP).1)
    (regularizationLabel Q μ N B) (regularizationIndex Q μ N B t)
    (fun T hT => (Finset.mem_filter.mp hT).1)
  · intro T hT
    exact (ht.trans_le (Finset.mem_filter.mp hT).2).ne'
  · intro T hT
    let : IsProbabilityMeasure (sourceClass Q μ N B (p T)) :=
      regularization_class_probability Q hside μ N B (hp T hT)
    exact allDescriptorTestBad_measurable w₀ Q _ _ N σ J hG
  · intro T hT
    change ((normalizedClass Q μ (regularizationLeaves Q μ N)
      (regularizationLabel Q μ N B) T).prod ν)
      (allDescriptorTestBad w₀ Q (sourceClass Q μ N B (p T))
        (fun u => sourceUnitProfile Q μ N B (p T) (u/N)) N σ J G) ≤ _
    rw [← sourceClass_eq_normalized Q μ N B (p T) T (hlabel T hT)]
    apply allDescriptorTestBad_mass
    intro b hb
    exact h₀ N hN Q hQ μ B hB hwidth hlarge (p T) (hp T hT) b hb ν w₀ G hG
      ((sourceClass_absolutelyContinuous Q μ N B (p T)).ae_le hcap) J

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_RegularizationPairBounds
attribute [-instance] _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Measurability, range and original-pair cost of the assembled mask -/

namespace Falconer.Regularization
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem uniform_regularizationPairExceptional_bound_oai {σ : ℝ} (hσ : 0 < σ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (Q₁ Q₂ : DyadicCube d), Q₁.side = 1 → Q₂.side = 1 →
      ∀ (μ ν : Measure (Space d)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν],
      ∀ (B₁ B₂ : ℕ), 0 < B₁ → 0 < B₂ →
      (B₁:ℝ) ≤ σ*N → (B₂:ℝ) ≤ σ*N →
      (2:ℝ)^(N/B₁+2) ≤ ((2:ℝ)^N)^σ → (2:ℝ)^(N/B₂+2) ≤ ((2:ℝ)^N)^σ →
      ∀ (t₁ t₂ : ℝ≥0∞), 0 < t₁ → 0 < t₂ → ∀ p₁ p₂ : List ℕ → CellPath d,
      (∀ T ∈ regularizationIndex Q₁ μ N B₁ t₁, p₁ T ∈ regularizationLeaves Q₁ μ N) →
      (∀ T ∈ regularizationIndex Q₂ ν N B₂ t₂, p₂ T ∈ regularizationLeaves Q₂ ν N) →
      (∀ T ∈ regularizationIndex Q₁ μ N B₁ t₁, regularizationLabel Q₁ μ N B₁ (p₁ T) = T) →
      (∀ T ∈ regularizationIndex Q₂ ν N B₂ t₂, regularizationLabel Q₂ ν N B₂ (p₂ T) = T) →
      ∀ (w₀ : Sphere d) (G : Set (Space d × Space d)), MeasurableSet G →
      (∀ᵐ x ∂μ, ∀ u : Space d, ∀ r : ℝ, ((2:ℝ)^N)^(-1:ℝ) ≤ r → r ≤ 1 →
        originalRadialSphereLaw w₀ ν G x {w : Sphere d | dist (w:Space d) u < r} ≤
          ENNReal.ofReal (((2:ℝ)^N)^σ*r^((d:ℝ)/2))) →
      (∀ᵐ y ∂ν, ∀ u : Space d, ∀ r : ℝ, ((2:ℝ)^N)^(-1:ℝ) ≤ r → r ≤ 1 →
        originalRadialSphereLaw w₀ μ (Prod.swap ⁻¹' G) y {w : Sphere d | dist (w:Space d) u < r} ≤
          ENNReal.ofReal (((2:ℝ)^N)^σ*r^((d:ℝ)/2))) →
      ∀ κ : ℝ,
      (μ.prod ν) (regularizationPairExceptional Q₁ Q₂ μ ν N B₁ B₂ t₁ t₂ σ κ p₁ p₂ w₀ G) ≤
        μ (retainedRegion Q₁ μ N B₁ t₁)ᶜ + ν (retainedRegion Q₂ ν N B₂ t₂)ᶜ +
          (4*(N+1)^2:ℕ)*ENNReal.ofReal (((2:ℝ)^N)^(-σ)) := by
  obtain ⟨N₀,h₀⟩ := uniform_regularization_test_bad_mass (d := d) hσ
  refine ⟨N₀,?_⟩
  intro N hN Q₁ Q₂ hQ₁ hQ₂ μ ν _ _ B₁ B₂ hB₁ hB₂ hw₁ hw₂ hl₁ hl₂
    t₁ t₂ ht₁ ht₂ p₁ p₂ hp₁ hp₂ he₁ he₂ w₀ G hG hc₁ hc₂ κ
  have hside₂ : 0 < Q₂.side := by rw [hQ₂]; norm_num
  have hm₂ := regularizationTestBad_measurable w₀ Q₂ ν N B₂ t₂ σ
    (PlanarFalconer.sourceSmoothingLevels σ κ) p₂ hp₂ hside₂ (hG.preimage measurable_swap)
  have hb₁ := h₀ N hN Q₁ hQ₁ μ ν B₁ hB₁ hw₁ hl₁ t₁ ht₁ p₁ hp₁ he₁ w₀ G hG hc₁
    (PlanarFalconer.sourceSmoothingLevels σ κ)
  have hb₂ := h₀ N hN Q₂ hQ₂ ν μ B₂ hB₂ hw₂ hl₂ t₂ ht₂ p₂ hp₂ he₂ w₀
    (Prod.swap ⁻¹' G) (hG.preimage measurable_swap) hc₂ (PlanarFalconer.sourceSmoothingLevels σ κ)
  apply (pairExceptional_mass μ ν _ _ _ _ hm₂).trans
  calc
    _ ≤ μ (retainedRegion Q₁ μ N B₁ t₁)ᶜ + ν (retainedRegion Q₂ ν N B₂ t₂)ᶜ +
        (2*(N+1)^2:ℕ)*ENNReal.ofReal (((2:ℝ)^N)^(-σ)) +
        (2*(N+1)^2:ℕ)*ENNReal.ofReal (((2:ℝ)^N)^(-σ)) :=
      add_le_add (add_le_add le_rfl hb₁) hb₂
    _ = _ := by
      have hn : 4*(N+1)^2 = 2*(N+1)^2+2*(N+1)^2 := by omega
      rw [hn,Nat.cast_add,add_mul]
      exact add_assoc _ _ _

end Falconer.Regularization

end OAI
end

theorem solution : type_of% @OAI.Falconer.Regularization.uniform_regularizationPairExceptional_bound_oai := @OAI.Falconer.Regularization.uniform_regularizationPairExceptional_bound_oai
