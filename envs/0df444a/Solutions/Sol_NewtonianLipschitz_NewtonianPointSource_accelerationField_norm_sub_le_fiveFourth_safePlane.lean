-- Prove2me | solution 1 for NewtonianLipschitz.NewtonianPointSource.accelerationField_norm_sub_le_fiveFourth_safePlane
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T04:11:32.762179+00:00
-- url     : https://prove2.me/submissions/0a6f6e46-a7fc-463a-8fe8-c77fb5cd4ca9

module
public import Definitions.Def_NewtonianLipschitz_PhysicalTangentialAllAxes
public import Definitions.Def_NewtonianLipschitz_SafePlaneFiniteDifference
public import Theorems.Thm_NewtonianLipschitz_NewtonianPointSource_accelerationField_contDiffAt
public import Theorems.Thm_NewtonianLipschitz_NewtonianPointSource_accelerationField_fderiv_any_safe_axis_tangent_le
public import Theorems.Thm_NewtonianLipschitz_NewtonianPointSource_finiteDifferentialAcceleration_cons
public import Theorems.Thm_NewtonianLipschitz_NewtonianPointSource_finiteDifferentialAcceleration_nil
public import Theorems.Thm_NewtonianLipschitz_coordinateAbs_apply
public import Theorems.Thm_NewtonianLipschitz_cycleIndex_one
public import Theorems.Thm_NewtonianLipschitz_cycleIndex_two
public import Theorems.Thm_NewtonianLipschitz_cycleIndex_zero
public import Theorems.Thm_NewtonianLipschitz_cycleVec_one
public import Theorems.Thm_NewtonianLipschitz_cycleVec_two
public import Theorems.Thm_NewtonianLipschitz_cycleVec_zero
public import Theorems.Thm_NewtonianLipschitz_normalizedVector_one
public import Theorems.Thm_NewtonianLipschitz_normalizedVector_two
public import Theorems.Thm_NewtonianLipschitz_normalizedVector_zero
public import Theorems.Thm_NewtonianLipschitz_ofLp_toPhysicalVec3
public import Theorems.Thm_NewtonianLipschitz_swapYZIndex_one
public import Theorems.Thm_NewtonianLipschitz_swapYZIndex_two
public import Theorems.Thm_NewtonianLipschitz_swapYZIndex_zero
public import Theorems.Thm_NewtonianLipschitz_swapYZVec_one
public import Theorems.Thm_NewtonianLipschitz_swapYZVec_two
public import Theorems.Thm_NewtonianLipschitz_swapYZVec_zero
public import Theorems.Thm_NewtonianLipschitz_toPhysicalVec3_apply
public import Theorems.Thm_NewtonianLipschitz_toPhysicalVec3_zero
attribute [local simp] NewtonianLipschitz.NewtonianPointSource.finiteDifferentialAcceleration_cons
attribute [local simp] NewtonianLipschitz.NewtonianPointSource.finiteDifferentialAcceleration_nil
attribute [local simp] NewtonianLipschitz.coordinateAbs_apply
attribute [local simp] NewtonianLipschitz.cycleIndex_one
attribute [local simp] NewtonianLipschitz.cycleIndex_two
attribute [local simp] NewtonianLipschitz.cycleIndex_zero
attribute [local simp] NewtonianLipschitz.cycleVec_one
attribute [local simp] NewtonianLipschitz.cycleVec_two
attribute [local simp] NewtonianLipschitz.cycleVec_zero
attribute [local simp] NewtonianLipschitz.normalizedVector_one
attribute [local simp] NewtonianLipschitz.normalizedVector_two
attribute [local simp] NewtonianLipschitz.normalizedVector_zero
attribute [local simp] NewtonianLipschitz.ofLp_toPhysicalVec3
attribute [local simp] NewtonianLipschitz.swapYZIndex_one
attribute [local simp] NewtonianLipschitz.swapYZIndex_two
attribute [local simp] NewtonianLipschitz.swapYZIndex_zero
attribute [local simp] NewtonianLipschitz.swapYZVec_one
attribute [local simp] NewtonianLipschitz.swapYZVec_two
attribute [local simp] NewtonianLipschitz.swapYZVec_zero
attribute [local simp] NewtonianLipschitz.toPhysicalVec3_apply
attribute [local simp] NewtonianLipschitz.toPhysicalVec3_zero



set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz
namespace NewtonianLipschitz
namespace NewtonianPointSource
theorem _root_.solution
    (c : NewtonianPointSource) (x y : Vec3) (d : ℝ) (i : Fin 3)
    (hd : 0 < d) (hxy : x i = y i)
    (hsafe : d ≤ x i ∨ x i ≤ -d) :
    ‖c.accelerationField x - c.accelerationField y‖ ≤
      ((1 / d ^ 3) *
        (c.gravitationalParameter * (5 / 4 : ℝ))) * ‖x - y‖ := by
  let v : Vec3 := y - x
  let line : ℝ → Vec3 := fun t => x + t • v
  let fieldLine : ℝ → Vec3 :=
    fun t => c.accelerationField (line t)
  let fieldLineDeriv : ℝ → Vec3 :=
    fun t => (fderiv ℝ c.accelerationField (line t)) v
  let B : ℝ :=
    (1 / d ^ 3) * (c.gravitationalParameter * (5 / 4 : ℝ))
  have hvi : v i = 0 := by
    change y i - x i = 0
    linarith
  have hcoordinate (t : ℝ) : line t i = x i := by
    change (x + t • v) i = x i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      hvi, mul_zero, add_zero]
  have hsafeabs : d ≤ |x i| := by
    rcases hsafe with hpos | hneg
    · exact hpos.trans (le_abs_self _)
    · have hn : d ≤ -(x i) := by linarith
      exact hn.trans (neg_le_abs _)
  have hlineclear (t : ℝ) : d ≤ |line t i| := by
    rw [hcoordinate t]
    exact hsafeabs
  have hnonzero (t : ℝ) : line t ≠ 0 := by
    intro hz
    have hzero := congrArg (fun z : Vec3 => z i) hz
    simp only [Pi.zero_apply] at hzero
    have hclear := hlineclear t
    rw [hzero, abs_zero] at hclear
    linarith
  have hlineDeriv (t : ℝ) : HasDerivAt line v t := by
    change HasDerivAt (fun s : ℝ => x + s • v) v t
    simpa using ((hasDerivAt_id t).smul_const v).const_add x
  have hphysicalDifferentiable (t : ℝ) :
      DifferentiableAt ℝ c.accelerationField (line t) :=
    (c.accelerationField_contDiffAt (line t)
      (hnonzero t)).differentiableAt_one
  have hfieldDeriv (t : ℝ) :
      HasDerivAt fieldLine (fieldLineDeriv t) t := by
    exact (hphysicalDifferentiable t).hasFDerivAt.comp_hasDerivAt
      t (hlineDeriv t)
  have hderivBound (t : ℝ) :
      ‖fieldLineDeriv t‖ ≤ B * ‖v‖ :=
    c.accelerationField_fderiv_any_safe_axis_tangent_le
      (line t) v d hd i (hlineclear t) hvi
  have hmean :
      ‖fieldLine 1 - fieldLine 0‖ ≤ B * ‖v‖ :=
    norm_image_sub_le_of_norm_deriv_le_segment_01'
      (f := fieldLine) (f' := fieldLineDeriv)
      (C := B * ‖v‖)
      (fun t _ => (hfieldDeriv t).hasDerivWithinAt)
      (fun t _ => hderivBound t)
  have hstart : fieldLine 0 = c.accelerationField x := by
    dsimp [fieldLine, line]
    simp
  have hend : fieldLine 1 = c.accelerationField y := by
    change c.accelerationField (x + (1 : ℝ) • v) =
      c.accelerationField y
    congr 1
    rw [one_smul]
    dsimp [v]
    abel
  change ‖c.accelerationField x - c.accelerationField y‖ ≤
    B * ‖x - y‖
  calc
    ‖c.accelerationField x - c.accelerationField y‖
        = ‖fieldLine 1 - fieldLine 0‖ := by
          rw [hstart, hend]
          exact norm_sub_rev _ _
    _ ≤ B * ‖v‖ := hmean
    _ = B * ‖x - y‖ := by
      dsimp [v]
      rw [norm_sub_rev]
end NewtonianPointSource
end NewtonianLipschitz
