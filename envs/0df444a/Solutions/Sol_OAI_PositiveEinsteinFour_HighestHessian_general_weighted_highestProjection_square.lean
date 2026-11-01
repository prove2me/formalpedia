-- Prove2me | solution 1 for OAI.PositiveEinsteinFour.HighestHessian.general_weighted_highestProjection_square
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T19:42:28.708984+00:00
-- url     : https://prove2.me/submissions/97a1732e-02f3-406b-b03e-1951e271c539

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ091C015
import Theorems.Thm_OAI_PositiveEinsteinFour_HighestHessian_generalCurvaturePairing_add_left
import Theorems.Thm_OAI_PositiveEinsteinFour_HighestHessian_generalCurvaturePairing_add_right
import Theorems.Thm_OAI_PositiveEinsteinFour_HighestHessian_generalCurvaturePairing_comm
import Theorems.Thm_OAI_PositiveEinsteinFour_HighestHessian_generalCurvaturePairing_highestProjection
import Theorems.Thm_OAI_PositiveEinsteinFour_HighestHessian_generalCurvaturePairing_self
import Theorems.Thm_OAI_PositiveEinsteinFour_HighestHessian_generalCurvaturePairing_smul_left
import Theorems.Thm_OAI_PositiveEinsteinFour_HighestHessian_generalCurvaturePairing_smul_right
import Theorems.Thm_OAI_PositiveEinsteinFour_HighestHessian_totalMinus_energy_of_condition
import Theorems.Thm_OAI_PositiveEinsteinFour_HighestHessian_totalPlus_energy_of_condition

section
-- module Solutions.OAIQ091_EF.EinsteinFour_HighestLinear
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact linear equations and their elementary eliminations. -/

namespace PositiveEinsteinFour.HighestHessian

noncomputable section

open scoped BigOperators
open Bianchi TraceHessian

theorem Equations.pivot_0 {c : Fin 50 → ℝ} (h : Equations c) :
    c 0 = -(freeCoordinates c) 6 - (freeCoordinates c) 7 - 2 * (freeCoordinates c) 15 + (freeCoordinates c) 17 := by
  dsimp [freeCoordinates]
  linear_combination (-1) * h.eq1 + (1) * h.eq6 + (1) * h.eq11 + (-1) * h.eq24 + (1) * h.eq32 + (-2) * h.eq33

theorem Equations.pivot_1 {c : Fin 50 → ℝ} (h : Equations c) :
    c 1 = -(freeCoordinates c) 0 - (freeCoordinates c) 7 - (freeCoordinates c) 17 := by
  dsimp [freeCoordinates]
  linear_combination (1) * h.eq1

theorem Equations.pivot_2 {c : Fin 50 → ℝ} (h : Equations c) :
    c 2 = (freeCoordinates c) 2 + (freeCoordinates c) 5 - (freeCoordinates c) 8 - (freeCoordinates c) 18 := by
  dsimp [freeCoordinates]
  linear_combination (1) * h.eq2 + (1) * h.eq21

theorem Equations.pivot_3 {c : Fin 50 → ℝ} (h : Equations c) :
    c 3 = (freeCoordinates c) 3 - (freeCoordinates c) 4 - (freeCoordinates c) 9 + (freeCoordinates c) 13 := by
  dsimp [freeCoordinates]
  linear_combination (1) * h.eq8 + (1) * h.eq22 + (-1) * h.eq30

theorem Equations.pivot_4 {c : Fin 50 → ℝ} (h : Equations c) :
    c 4 = -(freeCoordinates c) 1 - (freeCoordinates c) 10 - (freeCoordinates c) 20 := by
  dsimp [freeCoordinates]
  linear_combination (1) * h.eq4

theorem Equations.pivot_5 {c : Fin 50 → ℝ} (h : Equations c) :
    c 5 = -(freeCoordinates c) 10 + (freeCoordinates c) 11 + 2 * (freeCoordinates c) 12 + (freeCoordinates c) 20 := by
  dsimp [freeCoordinates]
  linear_combination (-1) * h.eq4 + (1) * h.eq12 + (1) * h.eq18 + (1) * h.eq23 + (1) * h.eq31 + (-2) * h.eq34

theorem Equations.pivot_6 {c : Fin 50 → ℝ} (h : Equations c) :
    c 6 = -(freeCoordinates c) 1 - (freeCoordinates c) 12 - (freeCoordinates c) 20 := by
  dsimp [freeCoordinates]
  linear_combination (1) * h.eq4 + (-1) * h.eq12 + (1) * h.eq34

theorem Equations.pivot_7 {c : Fin 50 → ℝ} (h : Equations c) :
    c 7 = (freeCoordinates c) 3 - (freeCoordinates c) 4 := by
  dsimp [freeCoordinates]
  linear_combination (1) * h.eq22

theorem Equations.pivot_8 {c : Fin 50 → ℝ} (h : Equations c) :
    c 8 = -(freeCoordinates c) 2 - (freeCoordinates c) 5 + (freeCoordinates c) 8 + (freeCoordinates c) 14 := by
  dsimp [freeCoordinates]
  linear_combination (1) * h.eq20 + (-1) * h.eq21 + (1) * h.eq29

theorem Equations.pivot_9 {c : Fin 50 → ℝ} (h : Equations c) :
    c 9 = (freeCoordinates c) 0 + (freeCoordinates c) 7 + (freeCoordinates c) 15 := by
  dsimp [freeCoordinates]
  linear_combination (1) * h.eq24 + (1) * h.eq33

theorem Equations.pivot_10 {c : Fin 50 → ℝ} (h : Equations c) :
    c 10 = (freeCoordinates c) 9 - (freeCoordinates c) 13 := by
  dsimp [freeCoordinates]
  linear_combination (1) * h.eq30

theorem Equations.pivot_11 {c : Fin 50 → ℝ} (h : Equations c) :
    c 11 = -(freeCoordinates c) 3 + (freeCoordinates c) 13 := by
  dsimp [freeCoordinates]
  linear_combination (1) * h.eq35

theorem Equations.pivot_12 {c : Fin 50 → ℝ} (h : Equations c) :
    c 12 = (freeCoordinates c) 10 - (freeCoordinates c) 12 := by
  dsimp [freeCoordinates]
  linear_combination (1) * h.eq34

theorem Equations.pivot_13 {c : Fin 50 → ℝ} (h : Equations c) :
    c 13 = -(freeCoordinates c) 6 - (freeCoordinates c) 7 - (freeCoordinates c) 15 := by
  dsimp [freeCoordinates]
  linear_combination (1) * h.eq32 + (-1) * h.eq33

theorem Equations.pivot_14 {c : Fin 50 → ℝ} (h : Equations c) :
    c 14 = (freeCoordinates c) 2 - (freeCoordinates c) 8 := by
  dsimp [freeCoordinates]
  linear_combination (1) * h.eq36

theorem Equations.pivot_15 {c : Fin 50 → ℝ} (h : Equations c) :
    c 15 = (freeCoordinates c) 14 - (freeCoordinates c) 18 := by
  dsimp [freeCoordinates]
  linear_combination (1) * h.eq2 + (-1) * h.eq7 + (1) * h.eq20 + (1) * h.eq29

theorem Equations.pivot_16 {c : Fin 50 → ℝ} (h : Equations c) :
    c 16 = -(freeCoordinates c) 5 + (freeCoordinates c) 18 := by
  dsimp [freeCoordinates]
  linear_combination (-1) * h.eq2 + (1) * h.eq10 + (-1) * h.eq21 + (1) * h.eq36

theorem Equations.pivot_17 {c : Fin 50 → ℝ} (h : Equations c) :
    c 17 = (freeCoordinates c) 15 - (freeCoordinates c) 17 := by
  dsimp [freeCoordinates]
  linear_combination (1) * h.eq1 + (-1) * h.eq11 + (1) * h.eq24 + (1) * h.eq33

theorem Equations.pivot_18 {c : Fin 50 → ℝ} (h : Equations c) :
    c 18 = -(freeCoordinates c) 11 - (freeCoordinates c) 12 - (freeCoordinates c) 20 := by
  dsimp [freeCoordinates]
  linear_combination (1) * h.eq4 + (-1) * h.eq5 + (-1) * h.eq12 + (-1) * h.eq18 + (-1) * h.eq23 + (-1) * h.eq31 + (1) * h.eq34

theorem Equations.pivot_19 {c : Fin 50 → ℝ} (h : Equations c) :
    c 19 = (freeCoordinates c) 4 - (freeCoordinates c) 13 := by
  dsimp [freeCoordinates]
  linear_combination (-1) * h.eq9 + (-1) * h.eq22 + (-1) * h.eq35

theorem Equations.pivot_20 {c : Fin 50 → ℝ} (h : Equations c) :
    c 20 = (freeCoordinates c) 7 + 2 * (freeCoordinates c) 15 - (freeCoordinates c) 16 - (freeCoordinates c) 17 := by
  dsimp [freeCoordinates]
  linear_combination (1) * h.eq0 + (1) * h.eq1 + (-1) * h.eq6 + (-1) * h.eq11 + (1) * h.eq24 + (-1) * h.eq32 + (2) * h.eq33

theorem Equations.pivot_22 {c : Fin 50 → ℝ} (h : Equations c) :
    c 22 = -(freeCoordinates c) 2 - (freeCoordinates c) 5 := by
  dsimp [freeCoordinates]
  linear_combination (-1) * h.eq21

theorem Equations.pivot_23 {c : Fin 50 → ℝ} (h : Equations c) :
    c 23 = -(freeCoordinates c) 3 + (freeCoordinates c) 4 - (freeCoordinates c) 13 - (freeCoordinates c) 19 := by
  dsimp [freeCoordinates]
  linear_combination (1) * h.eq3 + (-1) * h.eq8 + (-1) * h.eq22 + (1) * h.eq30

theorem Equations.pivot_25 {c : Fin 50 → ℝ} (h : Equations c) :
    c 25 = -(freeCoordinates c) 8 - (freeCoordinates c) 14 := by
  dsimp [freeCoordinates]
  linear_combination (-1) * h.eq29

theorem Equations.pivot_27 {c : Fin 50 → ℝ} (h : Equations c) :
    c 27 = -(freeCoordinates c) 7 - (freeCoordinates c) 15 := by
  dsimp [freeCoordinates]
  linear_combination (-1) * h.eq33

theorem Equations.pivot_28 {c : Fin 50 → ℝ} (h : Equations c) :
    c 28 = -(freeCoordinates c) 10 + (freeCoordinates c) 11 + (freeCoordinates c) 12 := by
  dsimp [freeCoordinates]
  linear_combination (1) * h.eq31 + (-1) * h.eq34

theorem Equations.pivot_30 {c : Fin 50 → ℝ} (h : Equations c) :
    c 30 = -(freeCoordinates c) 13 - (freeCoordinates c) 19 := by
  dsimp [freeCoordinates]
  linear_combination (1) * h.eq3 + (-1) * h.eq8 + (-1) * h.eq19 + (1) * h.eq30

theorem Equations.pivot_32 {c : Fin 50 → ℝ} (h : Equations c) :
    c 32 = -(freeCoordinates c) 12 - (freeCoordinates c) 20 := by
  dsimp [freeCoordinates]
  linear_combination (1) * h.eq4 + (-1) * h.eq12 + (-1) * h.eq23 + (1) * h.eq34

theorem Equations.pivot_33 {c : Fin 50 → ℝ} (h : Equations c) :
    c 33 = -(freeCoordinates c) 15 + (freeCoordinates c) 16 + (freeCoordinates c) 17 := by
  dsimp [freeCoordinates]
  linear_combination (-1) * h.eq0 + (-1) * h.eq1 + (1) * h.eq6 + (1) * h.eq11 + (-1) * h.eq17 + (-1) * h.eq24 + (1) * h.eq32 + (-1) * h.eq33


end
end PositiveEinsteinFour.HighestHessian

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_HighestConstraints
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Bianchi.derivativeQuaternion_matrix _root_.OAI.PositiveEinsteinFour.Bianchi.rawGradientGenerator_matrix _root_.OAI.PositiveEinsteinFour.Bianchi.rawMatrixRotation_matrix _root_.OAI.PositiveEinsteinFour.Geometry.matrixSlot_apply _root_.OAI.PositiveEinsteinFour.QuaternionFrame.frameMatrix_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Extraction of the exact scalar equations from an actual Hessian. -/

namespace PositiveEinsteinFour.HighestHessian

noncomputable section

open scoped BigOperators
open Bianchi TraceHessian

theorem coordinate_constraint_0 (c : Fin 50 → ℝ)
    (ht : hessianTrace (raw c) = 0)
    (_hb : ∀ i r, divergence (raw c) i r = 0) :
    c 0 + c 20 + c 35 + c 45 = 0 := by
  have h := congrArg (fun M : Mat => M 0 0) ht
  simp [hessianTrace, ofCoordinates, Fin.sum_univ_succ] at h
  change c 0 + (c 20 + (c 35 + c 45)) = 0 at h
  linear_combination h

theorem coordinate_constraint_1 (c : Fin 50 → ℝ)
    (ht : hessianTrace (raw c) = 0)
    (_hb : ∀ i r, divergence (raw c) i r = 0) :
    c 1 + c 21 + c 36 + c 46 = 0 := by
  have h := congrArg (fun M : Mat => M 1 1) ht
  simp [hessianTrace, ofCoordinates, Fin.sum_univ_succ] at h
  change c 1 + (c 21 + (c 36 + c 46)) = 0 at h
  linear_combination h

theorem coordinate_constraint_2 (c : Fin 50 → ℝ)
    (ht : hessianTrace (raw c) = 0)
    (_hb : ∀ i r, divergence (raw c) i r = 0) :
    c 2 + c 22 + c 37 + c 47 = 0 := by
  have h := congrArg (fun M : Mat => M 0 1) ht
  simp [hessianTrace, ofCoordinates, Fin.sum_univ_succ] at h
  change c 2 + (c 22 + (c 37 + c 47)) = 0 at h
  linear_combination h

theorem coordinate_constraint_3 (c : Fin 50 → ℝ)
    (ht : hessianTrace (raw c) = 0)
    (_hb : ∀ i r, divergence (raw c) i r = 0) :
    c 3 + c 23 + c 38 + c 48 = 0 := by
  have h := congrArg (fun M : Mat => M 0 2) ht
  simp [hessianTrace, ofCoordinates, Fin.sum_univ_succ] at h
  change c 3 + (c 23 + (c 38 + c 48)) = 0 at h
  linear_combination h

theorem coordinate_constraint_4 (c : Fin 50 → ℝ)
    (ht : hessianTrace (raw c) = 0)
    (_hb : ∀ i r, divergence (raw c) i r = 0) :
    c 4 + c 24 + c 39 + c 49 = 0 := by
  have h := congrArg (fun M : Mat => M 1 2) ht
  simp [hessianTrace, ofCoordinates, Fin.sum_univ_succ] at h
  change c 4 + (c 24 + (c 39 + c 49)) = 0 at h
  linear_combination h

theorem coordinate_constraint_5 (c : Fin 50 → ℝ)
    (_ht : hessianTrace (raw c) = 0)
    (hb : ∀ i r, divergence (raw c) i r = 0) :
    -c 5 - c 12 - c 18 = 0 := by
  have h := congrArg (fun q : Vec => q 0) (hb 0 0)
  simp [divergence, ofCoordinates, quaternion, Fin.sum_univ_succ] at h
  linear_combination h

theorem coordinate_constraint_6 (c : Fin 50 → ℝ)
    (_ht : hessianTrace (raw c) = 0)
    (hb : ∀ i r, divergence (raw c) i r = 0) :
    c 0 - c 13 + c 17 = 0 := by
  have h := congrArg (fun q : Vec => q 1) (hb 0 0)
  simp [divergence, ofCoordinates, quaternion, Fin.sum_univ_succ] at h
  linear_combination h

theorem coordinate_constraint_7 (c : Fin 50 → ℝ)
    (_ht : hessianTrace (raw c) = 0)
    (hb : ∀ i r, divergence (raw c) i r = 0) :
    c 2 + c 8 - c 15 = 0 := by
  have h := congrArg (fun q : Vec => q 2) (hb 0 0)
  simp [divergence, ofCoordinates, quaternion, Fin.sum_univ_succ] at h
  linear_combination h

theorem coordinate_constraint_8 (c : Fin 50 → ℝ)
    (_ht : hessianTrace (raw c) = 0)
    (hb : ∀ i r, divergence (raw c) i r = 0) :
    c 3 - c 7 + c 10 = 0 := by
  have h := congrArg (fun q : Vec => q 3) (hb 0 0)
  simp [divergence, ofCoordinates, quaternion, Fin.sum_univ_succ] at h
  linear_combination h

theorem coordinate_constraint_9 (c : Fin 50 → ℝ)
    (_ht : hessianTrace (raw c) = 0)
    (hb : ∀ i r, divergence (raw c) i r = 0) :
    -c 7 - c 11 - c 19 = 0 := by
  have h := congrArg (fun q : Vec => q 0) (hb 0 1)
  simp [divergence, ofCoordinates, quaternion, Fin.sum_univ_succ] at h
  linear_combination h

theorem coordinate_constraint_10 (c : Fin 50 → ℝ)
    (_ht : hessianTrace (raw c) = 0)
    (hb : ∀ i r, divergence (raw c) i r = 0) :
    c 2 - c 14 + c 16 = 0 := by
  have h := congrArg (fun q : Vec => q 1) (hb 0 1)
  simp [divergence, ofCoordinates, quaternion, Fin.sum_univ_succ] at h
  linear_combination h

theorem coordinate_constraint_11 (c : Fin 50 → ℝ)
    (_ht : hessianTrace (raw c) = 0)
    (hb : ∀ i r, divergence (raw c) i r = 0) :
    c 1 + c 9 - c 17 = 0 := by
  have h := congrArg (fun q : Vec => q 2) (hb 0 1)
  simp [divergence, ofCoordinates, quaternion, Fin.sum_univ_succ] at h
  linear_combination h

theorem coordinate_constraint_12 (c : Fin 50 → ℝ)
    (_ht : hessianTrace (raw c) = 0)
    (hb : ∀ i r, divergence (raw c) i r = 0) :
    c 4 - c 6 + c 12 = 0 := by
  have h := congrArg (fun q : Vec => q 3) (hb 0 1)
  simp [divergence, ofCoordinates, quaternion, Fin.sum_univ_succ] at h
  linear_combination h

theorem coordinate_constraint_17 (c : Fin 50 → ℝ)
    (_ht : hessianTrace (raw c) = 0)
    (hb : ∀ i r, divergence (raw c) i r = 0) :
    -c 20 - c 27 - c 33 = 0 := by
  have h := congrArg (fun q : Vec => q 0) (hb 1 0)
  simp [divergence, ofCoordinates, quaternion, Fin.sum_univ_succ] at h
  linear_combination h

theorem coordinate_constraint_18 (c : Fin 50 → ℝ)
    (_ht : hessianTrace (raw c) = 0)
    (hb : ∀ i r, divergence (raw c) i r = 0) :
    c 5 - c 28 + c 32 = 0 := by
  have h := congrArg (fun q : Vec => q 1) (hb 1 0)
  simp [divergence, ofCoordinates, quaternion, Fin.sum_univ_succ] at h
  linear_combination h

theorem coordinate_constraint_19 (c : Fin 50 → ℝ)
    (_ht : hessianTrace (raw c) = 0)
    (hb : ∀ i r, divergence (raw c) i r = 0) :
    c 7 + c 23 - c 30 = 0 := by
  have h := congrArg (fun q : Vec => q 2) (hb 1 0)
  simp [divergence, ofCoordinates, quaternion, Fin.sum_univ_succ] at h
  linear_combination h

theorem coordinate_constraint_20 (c : Fin 50 → ℝ)
    (_ht : hessianTrace (raw c) = 0)
    (hb : ∀ i r, divergence (raw c) i r = 0) :
    c 8 - c 22 + c 25 = 0 := by
  have h := congrArg (fun q : Vec => q 3) (hb 1 0)
  simp [divergence, ofCoordinates, quaternion, Fin.sum_univ_succ] at h
  linear_combination h

theorem coordinate_constraint_21 (c : Fin 50 → ℝ)
    (_ht : hessianTrace (raw c) = 0)
    (hb : ∀ i r, divergence (raw c) i r = 0) :
    -c 22 - c 26 - c 34 = 0 := by
  have h := congrArg (fun q : Vec => q 0) (hb 1 1)
  simp [divergence, ofCoordinates, quaternion, Fin.sum_univ_succ] at h
  linear_combination h

theorem coordinate_constraint_22 (c : Fin 50 → ℝ)
    (_ht : hessianTrace (raw c) = 0)
    (hb : ∀ i r, divergence (raw c) i r = 0) :
    c 7 - c 29 + c 31 = 0 := by
  have h := congrArg (fun q : Vec => q 1) (hb 1 1)
  simp [divergence, ofCoordinates, quaternion, Fin.sum_univ_succ] at h
  linear_combination h

theorem coordinate_constraint_23 (c : Fin 50 → ℝ)
    (_ht : hessianTrace (raw c) = 0)
    (hb : ∀ i r, divergence (raw c) i r = 0) :
    c 6 + c 24 - c 32 = 0 := by
  have h := congrArg (fun q : Vec => q 2) (hb 1 1)
  simp [divergence, ofCoordinates, quaternion, Fin.sum_univ_succ] at h
  linear_combination h

theorem coordinate_constraint_24 (c : Fin 50 → ℝ)
    (_ht : hessianTrace (raw c) = 0)
    (hb : ∀ i r, divergence (raw c) i r = 0) :
    c 9 - c 21 + c 27 = 0 := by
  have h := congrArg (fun q : Vec => q 3) (hb 1 1)
  simp [divergence, ofCoordinates, quaternion, Fin.sum_univ_succ] at h
  linear_combination h

theorem coordinate_constraint_29 (c : Fin 50 → ℝ)
    (_ht : hessianTrace (raw c) = 0)
    (hb : ∀ i r, divergence (raw c) i r = 0) :
    -c 25 - c 37 - c 43 = 0 := by
  have h := congrArg (fun q : Vec => q 0) (hb 2 0)
  simp [divergence, ofCoordinates, quaternion, Fin.sum_univ_succ] at h
  linear_combination h

theorem coordinate_constraint_30 (c : Fin 50 → ℝ)
    (_ht : hessianTrace (raw c) = 0)
    (hb : ∀ i r, divergence (raw c) i r = 0) :
    c 10 - c 38 + c 42 = 0 := by
  have h := congrArg (fun q : Vec => q 1) (hb 2 0)
  simp [divergence, ofCoordinates, quaternion, Fin.sum_univ_succ] at h
  linear_combination h

theorem coordinate_constraint_31 (c : Fin 50 → ℝ)
    (_ht : hessianTrace (raw c) = 0)
    (hb : ∀ i r, divergence (raw c) i r = 0) :
    c 12 + c 28 - c 40 = 0 := by
  have h := congrArg (fun q : Vec => q 2) (hb 2 0)
  simp [divergence, ofCoordinates, quaternion, Fin.sum_univ_succ] at h
  linear_combination h

theorem coordinate_constraint_32 (c : Fin 50 → ℝ)
    (_ht : hessianTrace (raw c) = 0)
    (hb : ∀ i r, divergence (raw c) i r = 0) :
    c 13 - c 27 + c 35 = 0 := by
  have h := congrArg (fun q : Vec => q 3) (hb 2 0)
  simp [divergence, ofCoordinates, quaternion, Fin.sum_univ_succ] at h
  linear_combination h

theorem coordinate_constraint_33 (c : Fin 50 → ℝ)
    (_ht : hessianTrace (raw c) = 0)
    (hb : ∀ i r, divergence (raw c) i r = 0) :
    -c 27 - c 36 - c 44 = 0 := by
  have h := congrArg (fun q : Vec => q 0) (hb 2 1)
  simp [divergence, ofCoordinates, quaternion, Fin.sum_univ_succ] at h
  linear_combination h

theorem coordinate_constraint_34 (c : Fin 50 → ℝ)
    (_ht : hessianTrace (raw c) = 0)
    (hb : ∀ i r, divergence (raw c) i r = 0) :
    c 12 - c 39 + c 41 = 0 := by
  have h := congrArg (fun q : Vec => q 1) (hb 2 1)
  simp [divergence, ofCoordinates, quaternion, Fin.sum_univ_succ] at h
  linear_combination h

theorem coordinate_constraint_35 (c : Fin 50 → ℝ)
    (_ht : hessianTrace (raw c) = 0)
    (hb : ∀ i r, divergence (raw c) i r = 0) :
    c 11 + c 29 - c 42 = 0 := by
  have h := congrArg (fun q : Vec => q 2) (hb 2 1)
  simp [divergence, ofCoordinates, quaternion, Fin.sum_univ_succ] at h
  linear_combination h

theorem coordinate_constraint_36 (c : Fin 50 → ℝ)
    (_ht : hessianTrace (raw c) = 0)
    (hb : ∀ i r, divergence (raw c) i r = 0) :
    c 14 - c 26 + c 37 = 0 := by
  have h := congrArg (fun q : Vec => q 3) (hb 2 1)
  simp [divergence, ofCoordinates, quaternion, Fin.sum_univ_succ] at h
  linear_combination h

/-- The geometric tensor constraints imply the displayed independent system. -/
theorem equations_of_constraints (c : Fin 50 → ℝ)
    (ht : hessianTrace (raw c) = 0)
    (hb : ∀ i r, divergence (raw c) i r = 0) : Equations c where
  eq0 := coordinate_constraint_0 c ht hb
  eq1 := coordinate_constraint_1 c ht hb
  eq2 := coordinate_constraint_2 c ht hb
  eq3 := coordinate_constraint_3 c ht hb
  eq4 := coordinate_constraint_4 c ht hb
  eq5 := coordinate_constraint_5 c ht hb
  eq6 := coordinate_constraint_6 c ht hb
  eq7 := coordinate_constraint_7 c ht hb
  eq8 := coordinate_constraint_8 c ht hb
  eq9 := coordinate_constraint_9 c ht hb
  eq10 := coordinate_constraint_10 c ht hb
  eq11 := coordinate_constraint_11 c ht hb
  eq12 := coordinate_constraint_12 c ht hb
  eq17 := coordinate_constraint_17 c ht hb
  eq18 := coordinate_constraint_18 c ht hb
  eq19 := coordinate_constraint_19 c ht hb
  eq20 := coordinate_constraint_20 c ht hb
  eq21 := coordinate_constraint_21 c ht hb
  eq22 := coordinate_constraint_22 c ht hb
  eq23 := coordinate_constraint_23 c ht hb
  eq24 := coordinate_constraint_24 c ht hb
  eq29 := coordinate_constraint_29 c ht hb
  eq30 := coordinate_constraint_30 c ht hb
  eq31 := coordinate_constraint_31 c ht hb
  eq32 := coordinate_constraint_32 c ht hb
  eq33 := coordinate_constraint_33 c ht hb
  eq34 := coordinate_constraint_34 c ht hb
  eq35 := coordinate_constraint_35 c ht hb
  eq36 := coordinate_constraint_36 c ht hb

end
end PositiveEinsteinFour.HighestHessian

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_HighestHessian
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Geometry.matrixSlot_apply _root_.OAI.PositiveEinsteinFour.HighestHessian.coupledOperator_coordinates _root_.OAI.PositiveEinsteinFour.HighestHessian.vectorHessian_hessianVector _root_.OAI.PositiveEinsteinFour.QuaternionFrame.frameMatrix_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every actual highest Hessian has the twenty-one displayed coordinates. -/

namespace PositiveEinsteinFour.HighestHessian

noncomputable section

open scoped BigOperators
open Bianchi TraceHessian

private theorem entry_reconstruction_0 (c : Fin 50 → ℝ)
    (ht : hessianTrace (raw c) = 0)
    (hb : ∀ i r, divergence (raw c) i r = 0) :
    rawEntries c 0 = entries (freeCoordinates c) 0 := by
  have e0 := (equations_of_constraints c ht hb).pivot_0
  have e1 := (equations_of_constraints c ht hb).pivot_1
  have e2 := (equations_of_constraints c ht hb).pivot_2
  have e3 := (equations_of_constraints c ht hb).pivot_3
  have e4 := (equations_of_constraints c ht hb).pivot_4
  simp only [rawEntries_0, entries_0, e0, e1, e2, e3, e4]

private theorem entry_reconstruction_1 (c : Fin 50 → ℝ)
    (ht : hessianTrace (raw c) = 0)
    (hb : ∀ i r, divergence (raw c) i r = 0) :
    rawEntries c 1 = entries (freeCoordinates c) 1 := by
  have e5 := (equations_of_constraints c ht hb).pivot_5
  have e6 := (equations_of_constraints c ht hb).pivot_6
  have e7 := (equations_of_constraints c ht hb).pivot_7
  have e8 := (equations_of_constraints c ht hb).pivot_8
  have e9 := (equations_of_constraints c ht hb).pivot_9
  simp only [rawEntries_1, entries_1, e5, e6, e7, e8, e9]

private theorem entry_reconstruction_2 (c : Fin 50 → ℝ)
    (ht : hessianTrace (raw c) = 0)
    (hb : ∀ i r, divergence (raw c) i r = 0) :
    rawEntries c 2 = entries (freeCoordinates c) 2 := by
  have e10 := (equations_of_constraints c ht hb).pivot_10
  have e11 := (equations_of_constraints c ht hb).pivot_11
  have e12 := (equations_of_constraints c ht hb).pivot_12
  have e13 := (equations_of_constraints c ht hb).pivot_13
  have e14 := (equations_of_constraints c ht hb).pivot_14
  simp only [rawEntries_2, entries_2, e10, e11, e12, e13, e14]

private theorem entry_reconstruction_3 (c : Fin 50 → ℝ)
    (ht : hessianTrace (raw c) = 0)
    (hb : ∀ i r, divergence (raw c) i r = 0) :
    rawEntries c 3 = entries (freeCoordinates c) 3 := by
  have e15 := (equations_of_constraints c ht hb).pivot_15
  have e16 := (equations_of_constraints c ht hb).pivot_16
  have e17 := (equations_of_constraints c ht hb).pivot_17
  have e18 := (equations_of_constraints c ht hb).pivot_18
  have e19 := (equations_of_constraints c ht hb).pivot_19
  simp only [rawEntries_3, entries_3, e15, e16, e17, e18, e19]

private theorem entry_reconstruction_4 (c : Fin 50 → ℝ)
    (ht : hessianTrace (raw c) = 0)
    (hb : ∀ i r, divergence (raw c) i r = 0) :
    rawEntries c 4 = entries (freeCoordinates c) 4 := by
  have e20 := (equations_of_constraints c ht hb).pivot_20
  have e22 := (equations_of_constraints c ht hb).pivot_22
  have e23 := (equations_of_constraints c ht hb).pivot_23
  simp only [rawEntries_4, entries_4, e20, e22, e23, freeCoordinates_0, freeCoordinates_1]

private theorem entry_reconstruction_5 (c : Fin 50 → ℝ)
    (ht : hessianTrace (raw c) = 0)
    (hb : ∀ i r, divergence (raw c) i r = 0) :
    rawEntries c 5 = entries (freeCoordinates c) 5 := by
  have e25 := (equations_of_constraints c ht hb).pivot_25
  have e27 := (equations_of_constraints c ht hb).pivot_27
  have e28 := (equations_of_constraints c ht hb).pivot_28
  simp only [rawEntries_5, entries_5, e25, e27, e28, freeCoordinates_2, freeCoordinates_3]

private theorem entry_reconstruction_6 (c : Fin 50 → ℝ)
    (ht : hessianTrace (raw c) = 0)
    (hb : ∀ i r, divergence (raw c) i r = 0) :
    rawEntries c 6 = entries (freeCoordinates c) 6 := by
  have e30 := (equations_of_constraints c ht hb).pivot_30
  have e32 := (equations_of_constraints c ht hb).pivot_32
  have e33 := (equations_of_constraints c ht hb).pivot_33
  simp only [rawEntries_6, entries_6, e30, e32, e33, freeCoordinates_4, freeCoordinates_5]

private theorem entry_reconstruction_7 (c : Fin 50 → ℝ)
    (_ht : hessianTrace (raw c) = 0)
    (_hb : ∀ i r, divergence (raw c) i r = 0) :
    rawEntries c 7 = entries (freeCoordinates c) 7 := by
  simp only [rawEntries_7, entries_7,
    freeCoordinates_6, freeCoordinates_7, freeCoordinates_8, freeCoordinates_9, freeCoordinates_10]

private theorem entry_reconstruction_8 (c : Fin 50 → ℝ)
    (_ht : hessianTrace (raw c) = 0)
    (_hb : ∀ i r, divergence (raw c) i r = 0) :
    rawEntries c 8 = entries (freeCoordinates c) 8 := by
  simp only [rawEntries_8, entries_8,
    freeCoordinates_11, freeCoordinates_12, freeCoordinates_13, freeCoordinates_14, freeCoordinates_15]

private theorem entry_reconstruction_9 (c : Fin 50 → ℝ)
    (_ht : hessianTrace (raw c) = 0)
    (_hb : ∀ i r, divergence (raw c) i r = 0) :
    rawEntries c 9 = entries (freeCoordinates c) 9 := by
  simp only [rawEntries_9, entries_9,
    freeCoordinates_16, freeCoordinates_17, freeCoordinates_18, freeCoordinates_19, freeCoordinates_20]

/-- The actual trace and Bianchi constraints determine every nonfree entry. -/
theorem raw_reconstruction (c : Fin 50 → ℝ)
    (ht : hessianTrace (raw c) = 0)
    (hb : ∀ i r, divergence (raw c) i r = 0) :
    raw c = highest (freeCoordinates c) := by
  unfold raw highest
  congr 1
  funext k
  fin_cases k
  · exact entry_reconstruction_0 c ht hb
  · exact entry_reconstruction_1 c ht hb
  · exact entry_reconstruction_2 c ht hb
  · exact entry_reconstruction_3 c ht hb
  · exact entry_reconstruction_4 c ht hb
  · exact entry_reconstruction_5 c ht hb
  · exact entry_reconstruction_6 c ht hb
  · exact entry_reconstruction_7 c ht hb
  · exact entry_reconstruction_8 c ht hb
  · exact entry_reconstruction_9 c ht hb

theorem raw_coordinates (X : Hessian)
    (hs : ∀ i j, X i j = X j i)
    (hm : ∀ i j, symmetric (X i j) ∧ traceFree (X i j)) :
    raw (coordinates X) = X := by
  funext i j
  fin_cases i <;> fin_cases j
  · simpa using (coordinates_eq (X 0 0) (hm 0 0).1 (hm 0 0).2)
  · simpa using (coordinates_eq (X 0 1) (hm 0 1).1 (hm 0 1).2)
  · simpa using (coordinates_eq (X 0 2) (hm 0 2).1 (hm 0 2).2)
  · simpa using (coordinates_eq (X 0 3) (hm 0 3).1 (hm 0 3).2)
  · simpa using ((coordinates_eq (X 0 1) (hm 0 1).1 (hm 0 1).2).trans (hs 0 1))
  · simpa using (coordinates_eq (X 1 1) (hm 1 1).1 (hm 1 1).2)
  · simpa using (coordinates_eq (X 1 2) (hm 1 2).1 (hm 1 2).2)
  · simpa using (coordinates_eq (X 1 3) (hm 1 3).1 (hm 1 3).2)
  · simpa using ((coordinates_eq (X 0 2) (hm 0 2).1 (hm 0 2).2).trans (hs 0 2))
  · simpa using ((coordinates_eq (X 1 2) (hm 1 2).1 (hm 1 2).2).trans (hs 1 2))
  · simpa using (coordinates_eq (X 2 2) (hm 2 2).1 (hm 2 2).2)
  · simpa using (coordinates_eq (X 2 3) (hm 2 3).1 (hm 2 3).2)
  · simpa using ((coordinates_eq (X 0 3) (hm 0 3).1 (hm 0 3).2).trans (hs 0 3))
  · simpa using ((coordinates_eq (X 1 3) (hm 1 3).1 (hm 1 3).2).trans (hs 1 3))
  · simpa using ((coordinates_eq (X 2 3) (hm 2 3).1 (hm 2 3).2).trans (hs 2 3))
  · simpa using (coordinates_eq (X 3 3) (hm 3 3).1 (hm 3 3).2)

/-- Every actual highest Hessian has the displayed twenty-one coordinates.
Only derivative symmetry, matrix symmetry/trace, and Bianchi are used. -/
theorem exists_highest (X : Hessian) (hX : condition X) :
    ∃ c : Fin 21 → ℝ, highest c = X := by
  obtain ⟨hs, hm, ht, hb⟩ := hX
  have hr := raw_coordinates X hs hm
  refine ⟨freeCoordinates (coordinates X), ?_⟩
  rw [← raw_reconstruction (coordinates X) (by rw [hr]; exact ht)
    (by rw [hr]; exact hb)]
  exact hr

end
end PositiveEinsteinFour.HighestHessian

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_HighestCondition
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Bianchi.derivativeQuaternion_matrix _root_.OAI.PositiveEinsteinFour.Bianchi.rawGradientGenerator_matrix _root_.OAI.PositiveEinsteinFour.Bianchi.rawMatrixRotation_matrix _root_.OAI.PositiveEinsteinFour.Geometry.matrixSlot_apply _root_.OAI.PositiveEinsteinFour.QuaternionFrame.frameMatrix_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The displayed highest coordinates satisfy every original tensor constraint. -/

namespace PositiveEinsteinFour.HighestHessian

noncomputable section

open scoped BigOperators
open Bianchi TraceHessian

/-- Symmetry is built into the two derivative slots of the coordinate array. -/
theorem highest_derivative_symmetric (c : Fin 21 → ℝ) (i j : Fin 4) :
    highest c i j = highest c j i := by
  fin_cases i <;> fin_cases j <;> rfl

theorem highest_matrix_symmetric (c : Fin 21 → ℝ) (i j : Fin 4) :
    symmetric (highest c i j) := by
  intro a b
  fin_cases i <;> fin_cases j <;> fin_cases a <;> fin_cases b <;>
    simp [ofCoordinates]

theorem highest_matrix_traceFree (c : Fin 21 → ℝ) (i j : Fin 4) :
    traceFree (highest c i j) := by
  fin_cases i <;> fin_cases j <;>
    simp [traceFree, ofCoordinates, Fin.sum_univ_succ]
  all_goals ring

theorem highest_trace (c : Fin 21 → ℝ) : hessianTrace (highest c) = 0 := by
  ext a b
  change (∑ i, highest c i i a b) = 0
  fin_cases a <;> fin_cases b <;>
    simp [ofCoordinates, Fin.sum_univ_succ]
  all_goals ring

theorem highest_divergence (c : Fin 21 → ℝ) (i : Fin 4) (r : Fin 3) :
    divergence (highest c) i r = 0 := by
  ext u
  fin_cases i <;> fin_cases r <;> fin_cases u <;>
    simp [divergence, quaternion, Fin.sum_univ_succ]
  all_goals simp [ofCoordinates]
  all_goals ring

/-- The concrete constrained-space description in both directions. -/
theorem highest_condition (c : Fin 21 → ℝ) : condition (highest c) := by
  refine ⟨highest_derivative_symmetric c, ?_, highest_trace c, highest_divergence c⟩
  intro i j
  exact ⟨highest_matrix_symmetric c i j, highest_matrix_traceFree c i j⟩

end
end PositiveEinsteinFour.HighestHessian

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_HighestGram
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The Casimir lower bound with arbitrary symmetric matrix coefficients.
Positive semidefiniteness is applied to each actual tensor coordinate. -/

namespace PositiveEinsteinFour.HighestHessian

open scoped BigOperators
open Bianchi TraceHessian

noncomputable section

/-- A positive semidefinite coefficient matrix gives a nonnegative
Gram form on the entire four-slot tensor space. -/
theorem hessianGram_nonneg (A : Mat) (hA : A.PosSemidef) (F : Fin 3 → Hessian) :
    0 ≤ hessianGram A F := by
  have hp (p : TensorIndex) :
      0 ≤ ∑ r, ∑ s, A r s * tensorCoordinates (F r) p * tensorCoordinates (F s) p := by
    have h := hA.dotProduct_mulVec_nonneg (fun r => tensorCoordinates (F r) p)
    simp only [dotProduct, Matrix.mulVec, star_trivial, Finset.mul_sum] at h
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    apply Finset.sum_congr rfl
    intro r _
    apply Finset.sum_congr rfl
    intro s _
    ring
  have he : hessianGram A F = ∑ p : TensorIndex,
      ∑ r, ∑ s, A r s * tensorCoordinates (F r) p * tensorCoordinates (F s) p := by
    unfold hessianGram
    simp_rw [← tensorCoordinates_pairing]
    simp only [Finset.mul_sum]
    calc
      _ = ∑ r, ∑ p : TensorIndex, ∑ s,
          A r s * (tensorCoordinates (F r) p * tensorCoordinates (F s) p) := by
        apply Finset.sum_congr rfl
        intro r _
        rw [Finset.sum_comm]
      _ = ∑ p : TensorIndex, ∑ r, ∑ s,
          A r s * (tensorCoordinates (F r) p * tensorCoordinates (F s) p) := Finset.sum_comm
      _ = _ := by simp only [mul_assoc]
  rw [he]
  exact Finset.sum_nonneg fun p _ => hp p

/-- Adding a scalar identity adds that scalar times the total energy. -/
theorem hessianGram_shift (A : Mat) (x : ℝ) (F : Fin 3 → Hessian) :
    hessianGram (A + x • (1 : Mat)) F =
      hessianGram A F + x * ∑ r, hessianNormSq (F r) := by
  simp only [hessianGram, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
    smul_eq_mul, add_mul, Finset.sum_add_distrib, mul_ite, mul_zero, mul_one,
    ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true, if_true,
    hessianPairing_self, Finset.mul_sum]

/-- The sharp lower constant follows from the two proved Casimir energies
and positive semidefinite shifted Weyl matrices; no eigenframe is used. -/
theorem generalCasimirCurvatureForm_lower (A U : Mat) (X : Hessian)
    (hX : condition X) (x y : ℝ)
    (hA : (A + x • (1 : Mat)).PosSemidef)
    (hU : (U + y • (1 : Mat)).PosSemidef) :
    (4 - 2 * x - 2 * y) * hessianNormSq X ≤ generalCasimirCurvatureForm A U X := by
  have hp := hessianGram_nonneg _ hA (fun r => totalPlus r X)
  have hm := hessianGram_nonneg _ hU (fun r => totalMinus r X)
  rw [hessianGram_shift] at hp hm
  have hplus := totalPlus_energy_of_condition X hX
  have hminus := totalMinus_energy_of_condition X hX
  simp only [Fin.sum_univ_three] at hp hm
  rw [hplus] at hp
  rw [hminus] at hm
  unfold generalCasimirCurvatureForm
  nlinarith only [hp, hm]

/-- Positivity includes the closed sectional boundary. -/
theorem generalCasimirCurvatureForm_nonneg (A U : Mat) (X : Hessian)
    (hX : condition X) (x y : ℝ)
    (hA : (A + x • (1 : Mat)).PosSemidef)
    (hU : (U + y • (1 : Mat)).PosSemidef) (hxy : x + y ≤ 2) :
    0 ≤ generalCasimirCurvatureForm A U X := by
  have h := generalCasimirCurvatureForm_lower A U X hX x y hA hU
  have hn : 0 ≤ hessianNormSq X := by
    unfold hessianNormSq
    exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  exact (mul_nonneg (by linarith) hn).trans h

end
end PositiveEinsteinFour.HighestHessian

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_HighestProjection
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The orthogonal projection is constructed from the actual tensor subspace. -/

namespace PositiveEinsteinFour.HighestHessian

noncomputable section

open scoped BigOperators
open Bianchi TraceHessian

theorem hessianVector_injective : Function.Injective hessianVector := by
  intro X Y h
  simpa only [vectorHessian_hessianVector] using congrArg vectorHessian h

theorem highestProjection_has_coordinates (X : Hessian) :
    ∃ c : Fin 21 → ℝ, highest c = highestProjection X := by
  have h := highestSubspace.starProjection_apply_mem (hessianVector X)
  obtain ⟨c, hc⟩ := h
  refine ⟨c, hessianVector_injective ?_⟩
  change hessianVector (highest c) =
    highestSubspace.starProjection (hessianVector X) at hc
  simpa only [highestProjection, hessianVector_vectorHessian] using hc

end
end PositiveEinsteinFour.HighestHessian

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_WeylEstimates01
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! The arbitrary-frame weighted Hessian square in the original Green form. -/

namespace PositiveEinsteinFour.HighestHessian

open scoped BigOperators
open Matrix Bianchi TraceHessian PositiveEinsteinFour.Geometry CurvatureContraction

noncomputable section

/-- The local square uses the actual orthogonal projection, with arbitrary
symmetric matrix coefficients and no pointwise eigenframe. -/
theorem general_weighted_highestProjection_square_oai (A U : Mat)
    (hA : symmetric A) (hU : symmetric U) (X L : Hessian) (hX : condition X)
    (x y m : ℝ) (hm : 0 < m)
    (hAx : (A + x • (1 : Mat)).PosSemidef)
    (hUy : (U + y • (1 : Mat)).PosSemidef) (hxy : x + y ≤ 2) :
    0 ≤ (m / 6) * generalCurvaturePairing A U X X +
      generalCurvaturePairing A U X L / 6 +
      generalCurvaturePairing A U (highestProjection L) (highestProjection L) / (24 * m) := by
  obtain ⟨c, rfl⟩ := exists_highest X hX
  obtain ⟨d, hd⟩ := highestProjection_has_coordinates L
  have hsum : condition (highest c + (1 / (2 * m)) • highestProjection L) := by
    rw [← hd, ← highest_smul, ← highest_add]
    exact highest_condition _
  have hq := generalCasimirCurvatureForm_nonneg A U _ hsum x y hAx hUy hxy
  rw [← generalCurvaturePairing_self] at hq
  have he : (m / 6) * generalCurvaturePairing A U
      (highest c + (1 / (2 * m)) • highestProjection L)
      (highest c + (1 / (2 * m)) • highestProjection L) =
      (m / 6) * generalCurvaturePairing A U (highest c) (highest c) +
        generalCurvaturePairing A U (highest c) L / 6 +
        generalCurvaturePairing A U (highestProjection L) (highestProjection L) / (24 * m) := by
    rw [generalCurvaturePairing_add_left]
    simp only [generalCurvaturePairing_add_right, generalCurvaturePairing_smul_left,
      generalCurvaturePairing_smul_right]
    rw [generalCurvaturePairing_comm A U hA hU (highestProjection L) (highest c),
      generalCurvaturePairing_highestProjection A U (highest c) L (highest_condition c)]
    field_simp [hm.ne']
    ring
  rw [← he]
  exact mul_nonneg (by positivity) hq

end
end PositiveEinsteinFour.HighestHessian
end


end OAI
end

theorem solution : type_of% @OAI.PositiveEinsteinFour.HighestHessian.general_weighted_highestProjection_square_oai := @OAI.PositiveEinsteinFour.HighestHessian.general_weighted_highestProjection_square_oai
