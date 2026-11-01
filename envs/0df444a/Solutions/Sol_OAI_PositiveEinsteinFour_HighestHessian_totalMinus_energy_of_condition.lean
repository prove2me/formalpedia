-- Prove2me | solution 1 for OAI.PositiveEinsteinFour.HighestHessian.totalMinus_energy_of_condition
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T19:47:01.721003+00:00
-- url     : https://prove2.me/submissions/2b4a7f4b-74c9-488e-a8bd-9be1799102a1

import Mathlib
import Definitions.Def_OAIQ091C018
import Theorems.Thm_OAI_PositiveEinsteinFour_HighestHessian_totalMinus_highest

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
-- module Solutions.OAIQ091_EF.EinsteinFour_TensorPairing
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Skew matrix actions on the actual four tensor slots. -/

namespace PositiveEinsteinFour.TraceHessian

noncomputable section

open scoped BigOperators

/-- The usual reindexing proof for a real skew-adjoint matrix. -/
theorem skew_matrix_pairing {ι : Type*} [Fintype ι]
    (A : ι → ι → ℝ) (hA : ∀ i j, A i j = -A j i) (x y : ι → ℝ) :
    (∑ i, (∑ j, A i j * x j) * y i) =
      -(∑ i, x i * (∑ j, A i j * y j)) := by
  calc
    _ = ∑ i, ∑ j, A i j * x j * y i := by simp_rw [Finset.sum_mul]
    _ = ∑ j, ∑ i, A i j * x j * y i := Finset.sum_comm
    _ = ∑ j, -(∑ i, x j * (A j i * y i)) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [hA i j]
      ring
    _ = _ := by simp_rw [← Finset.mul_sum]; rw [Finset.sum_neg_distrib]

theorem hessianPairing_add_left (X Y Z : Hessian) :
    hessianPairing (X + Y) Z = hessianPairing X Z + hessianPairing Y Z := by
  change (∑ a, ∑ b, ∑ i, ∑ j, (X i j a b + Y i j a b) * Z i j a b) = _
  simp only [add_mul, hessianPairing, Finset.sum_add_distrib]

theorem hessianPairing_smul_left (r : ℝ) (X Y : Hessian) :
    hessianPairing (r • X) Y = r * hessianPairing X Y := by
  change (∑ a, ∑ b, ∑ i, ∑ j, (r * X i j a b) * Y i j a b) = _
  simp only [mul_assoc, hessianPairing, ← Finset.mul_sum]

end
end PositiveEinsteinFour.TraceHessian

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_HighestMinusCoordinates
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact coordinate action of the three total minus rotations. -/

namespace PositiveEinsteinFour.HighestHessian

noncomputable section

open scoped BigOperators
open Bianchi TraceHessian

private theorem minus_coordinate_casimir_0 (c : Fin 21 → ℝ) :
    minusCoordinates 0 (minusCoordinates 0 c) 0 +
      minusCoordinates 1 (minusCoordinates 1 c) 0 +
      minusCoordinates 2 (minusCoordinates 2 c) 0 = -8 * c 0 := by
  simp; ring

private theorem minus_coordinate_casimir_1 (c : Fin 21 → ℝ) :
    minusCoordinates 0 (minusCoordinates 0 c) 1 +
      minusCoordinates 1 (minusCoordinates 1 c) 1 +
      minusCoordinates 2 (minusCoordinates 2 c) 1 = -8 * c 1 := by
  simp; ring

private theorem minus_coordinate_casimir_2 (c : Fin 21 → ℝ) :
    minusCoordinates 0 (minusCoordinates 0 c) 2 +
      minusCoordinates 1 (minusCoordinates 1 c) 2 +
      minusCoordinates 2 (minusCoordinates 2 c) 2 = -8 * c 2 := by
  simp; ring

private theorem minus_coordinate_casimir_3 (c : Fin 21 → ℝ) :
    minusCoordinates 0 (minusCoordinates 0 c) 3 +
      minusCoordinates 1 (minusCoordinates 1 c) 3 +
      minusCoordinates 2 (minusCoordinates 2 c) 3 = -8 * c 3 := by
  simp; ring

private theorem minus_coordinate_casimir_4 (c : Fin 21 → ℝ) :
    minusCoordinates 0 (minusCoordinates 0 c) 4 +
      minusCoordinates 1 (minusCoordinates 1 c) 4 +
      minusCoordinates 2 (minusCoordinates 2 c) 4 = -8 * c 4 := by
  simp; ring

private theorem minus_coordinate_casimir_5 (c : Fin 21 → ℝ) :
    minusCoordinates 0 (minusCoordinates 0 c) 5 +
      minusCoordinates 1 (minusCoordinates 1 c) 5 +
      minusCoordinates 2 (minusCoordinates 2 c) 5 = -8 * c 5 := by
  simp; ring

private theorem minus_coordinate_casimir_6 (c : Fin 21 → ℝ) :
    minusCoordinates 0 (minusCoordinates 0 c) 6 +
      minusCoordinates 1 (minusCoordinates 1 c) 6 +
      minusCoordinates 2 (minusCoordinates 2 c) 6 = -8 * c 6 := by
  simp; ring

private theorem minus_coordinate_casimir_7 (c : Fin 21 → ℝ) :
    minusCoordinates 0 (minusCoordinates 0 c) 7 +
      minusCoordinates 1 (minusCoordinates 1 c) 7 +
      minusCoordinates 2 (minusCoordinates 2 c) 7 = -8 * c 7 := by
  simp; ring

private theorem minus_coordinate_casimir_8 (c : Fin 21 → ℝ) :
    minusCoordinates 0 (minusCoordinates 0 c) 8 +
      minusCoordinates 1 (minusCoordinates 1 c) 8 +
      minusCoordinates 2 (minusCoordinates 2 c) 8 = -8 * c 8 := by
  simp; ring

private theorem minus_coordinate_casimir_9 (c : Fin 21 → ℝ) :
    minusCoordinates 0 (minusCoordinates 0 c) 9 +
      minusCoordinates 1 (minusCoordinates 1 c) 9 +
      minusCoordinates 2 (minusCoordinates 2 c) 9 = -8 * c 9 := by
  simp; ring

private theorem minus_coordinate_casimir_10 (c : Fin 21 → ℝ) :
    minusCoordinates 0 (minusCoordinates 0 c) 10 +
      minusCoordinates 1 (minusCoordinates 1 c) 10 +
      minusCoordinates 2 (minusCoordinates 2 c) 10 = -8 * c 10 := by
  simp; ring

private theorem minus_coordinate_casimir_11 (c : Fin 21 → ℝ) :
    minusCoordinates 0 (minusCoordinates 0 c) 11 +
      minusCoordinates 1 (minusCoordinates 1 c) 11 +
      minusCoordinates 2 (minusCoordinates 2 c) 11 = -8 * c 11 := by
  simp; ring

private theorem minus_coordinate_casimir_12 (c : Fin 21 → ℝ) :
    minusCoordinates 0 (minusCoordinates 0 c) 12 +
      minusCoordinates 1 (minusCoordinates 1 c) 12 +
      minusCoordinates 2 (minusCoordinates 2 c) 12 = -8 * c 12 := by
  simp; ring

private theorem minus_coordinate_casimir_13 (c : Fin 21 → ℝ) :
    minusCoordinates 0 (minusCoordinates 0 c) 13 +
      minusCoordinates 1 (minusCoordinates 1 c) 13 +
      minusCoordinates 2 (minusCoordinates 2 c) 13 = -8 * c 13 := by
  simp; ring

private theorem minus_coordinate_casimir_14 (c : Fin 21 → ℝ) :
    minusCoordinates 0 (minusCoordinates 0 c) 14 +
      minusCoordinates 1 (minusCoordinates 1 c) 14 +
      minusCoordinates 2 (minusCoordinates 2 c) 14 = -8 * c 14 := by
  simp; ring

private theorem minus_coordinate_casimir_15 (c : Fin 21 → ℝ) :
    minusCoordinates 0 (minusCoordinates 0 c) 15 +
      minusCoordinates 1 (minusCoordinates 1 c) 15 +
      minusCoordinates 2 (minusCoordinates 2 c) 15 = -8 * c 15 := by
  simp; ring

private theorem minus_coordinate_casimir_16 (c : Fin 21 → ℝ) :
    minusCoordinates 0 (minusCoordinates 0 c) 16 +
      minusCoordinates 1 (minusCoordinates 1 c) 16 +
      minusCoordinates 2 (minusCoordinates 2 c) 16 = -8 * c 16 := by
  simp; ring

private theorem minus_coordinate_casimir_17 (c : Fin 21 → ℝ) :
    minusCoordinates 0 (minusCoordinates 0 c) 17 +
      minusCoordinates 1 (minusCoordinates 1 c) 17 +
      minusCoordinates 2 (minusCoordinates 2 c) 17 = -8 * c 17 := by
  simp; ring

private theorem minus_coordinate_casimir_18 (c : Fin 21 → ℝ) :
    minusCoordinates 0 (minusCoordinates 0 c) 18 +
      minusCoordinates 1 (minusCoordinates 1 c) 18 +
      minusCoordinates 2 (minusCoordinates 2 c) 18 = -8 * c 18 := by
  simp; ring

private theorem minus_coordinate_casimir_19 (c : Fin 21 → ℝ) :
    minusCoordinates 0 (minusCoordinates 0 c) 19 +
      minusCoordinates 1 (minusCoordinates 1 c) 19 +
      minusCoordinates 2 (minusCoordinates 2 c) 19 = -8 * c 19 := by
  simp; ring

private theorem minus_coordinate_casimir_20 (c : Fin 21 → ℝ) :
    minusCoordinates 0 (minusCoordinates 0 c) 20 +
      minusCoordinates 1 (minusCoordinates 1 c) 20 +
      minusCoordinates 2 (minusCoordinates 2 c) 20 = -8 * c 20 := by
  simp; ring

theorem minus_coordinate_casimir (c : Fin 21 → ℝ) :
    minusCoordinates 0 (minusCoordinates 0 c) +
      minusCoordinates 1 (minusCoordinates 1 c) +
      minusCoordinates 2 (minusCoordinates 2 c) = (-8 : ℝ) • c := by
  funext k
  fin_cases k
  · exact minus_coordinate_casimir_0 c
  · exact minus_coordinate_casimir_1 c
  · exact minus_coordinate_casimir_2 c
  · exact minus_coordinate_casimir_3 c
  · exact minus_coordinate_casimir_4 c
  · exact minus_coordinate_casimir_5 c
  · exact minus_coordinate_casimir_6 c
  · exact minus_coordinate_casimir_7 c
  · exact minus_coordinate_casimir_8 c
  · exact minus_coordinate_casimir_9 c
  · exact minus_coordinate_casimir_10 c
  · exact minus_coordinate_casimir_11 c
  · exact minus_coordinate_casimir_12 c
  · exact minus_coordinate_casimir_13 c
  · exact minus_coordinate_casimir_14 c
  · exact minus_coordinate_casimir_15 c
  · exact minus_coordinate_casimir_16 c
  · exact minus_coordinate_casimir_17 c
  · exact minus_coordinate_casimir_18 c
  · exact minus_coordinate_casimir_19 c
  · exact minus_coordinate_casimir_20 c


end
end PositiveEinsteinFour.HighestHessian

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_HighestMinus
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
attribute [-simp] _root_.OAI.PositiveEinsteinFour.HighestHessian.coupledOperator_coordinates _root_.OAI.PositiveEinsteinFour.HighestHessian.vectorHessian_hessianVector
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The minus Casimir energy and curvature bound on actual highest Hessians. -/

namespace PositiveEinsteinFour.HighestHessian

noncomputable section

open scoped BigOperators
open Bianchi TraceHessian

/-- The actual total-minus Casimir is spin one. -/
theorem totalMinus_casimir (c : Fin 21 → ℝ) :
    totalMinus 0 (totalMinus 0 (highest c)) +
      totalMinus 1 (totalMinus 1 (highest c)) +
      totalMinus 2 (totalMinus 2 (highest c)) = (-8 : ℝ) • highest c := by
  simp_rw [totalMinus_highest]
  rw [← highest_add, ← highest_add, minus_coordinate_casimir, highest_smul]

theorem rightQuaternion_skew (s : Fin 3) (i j : Fin 4) :
    rightQuaternion s i j = -rightQuaternion s j i := by
  fin_cases s <;> fin_cases i <;> fin_cases j <;> norm_num [rightQuaternion]

theorem minusKernel_skew (s : Fin 3) (p q : TensorIndex) :
    minusKernel s p q = -minusKernel s q p := by
  unfold minusKernel
  rw [rightQuaternion_skew s p.1 q.1, rightQuaternion_skew s p.2.1 q.2.1]
  simp only [eq_comm (a := q.1) (b := p.1),
    eq_comm (a := q.2.1) (b := p.2.1),
    eq_comm (a := q.2.2.1) (b := p.2.2.1),
    eq_comm (a := q.2.2.2) (b := p.2.2.2)]
  split_ifs <;> ring

theorem totalMinus_coordinates (s : Fin 3) (X : Hessian) (p : TensorIndex) :
    tensorCoordinates (totalMinus s X) p =
      ∑ q : TensorIndex, minusKernel s p q * tensorCoordinates X q := by
  rcases p with ⟨i, j, a, b⟩
  simp [tensorCoordinates, totalMinus, minusKernel,
    Fintype.sum_prod_type, add_mul, Finset.sum_add_distrib, ite_mul, ite_and]

theorem totalMinus_skew (s : Fin 3) (X Y : Hessian) :
    hessianPairing (totalMinus s X) Y = -hessianPairing X (totalMinus s Y) := by
  have h := skew_matrix_pairing (minusKernel s) (minusKernel_skew s)
    (tensorCoordinates X) (tensorCoordinates Y)
  simp_rw [← totalMinus_coordinates] at h
  rw [tensorCoordinates_pairing, tensorCoordinates_pairing] at h
  exact h

theorem totalMinus_energy (c : Fin 21 → ℝ) :
    hessianNormSq (totalMinus 0 (highest c)) +
      hessianNormSq (totalMinus 1 (highest c)) +
      hessianNormSq (totalMinus 2 (highest c)) = 8 * hessianNormSq (highest c) := by
  have h0 := totalMinus_skew 0 (totalMinus 0 (highest c)) (highest c)
  have h1 := totalMinus_skew 1 (totalMinus 1 (highest c)) (highest c)
  have h2 := totalMinus_skew 2 (totalMinus 2 (highest c)) (highest c)
  have h := congrArg (fun X => hessianPairing X (highest c)) (totalMinus_casimir c)
  simp only [hessianPairing_add_left, hessianPairing_smul_left] at h
  rw [h0, h1, h2] at h
  simp only [hessianPairing_self] at h
  linarith

/-- The minus energy identity applies to every actual constrained Hessian. -/
theorem totalMinus_energy_of_condition_oai (X : Hessian) (hX : condition X) :
    hessianNormSq (totalMinus 0 X) + hessianNormSq (totalMinus 1 X) +
      hessianNormSq (totalMinus 2 X) = 8 * hessianNormSq X := by
  obtain ⟨c, rfl⟩ := exists_highest X hX
  exact totalMinus_energy c

end
end PositiveEinsteinFour.HighestHessian

end OAI
end

theorem solution : type_of% @OAI.PositiveEinsteinFour.HighestHessian.totalMinus_energy_of_condition_oai := @OAI.PositiveEinsteinFour.HighestHessian.totalMinus_energy_of_condition_oai
