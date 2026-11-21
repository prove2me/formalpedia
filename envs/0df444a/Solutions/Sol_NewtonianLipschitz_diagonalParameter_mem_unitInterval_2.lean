-- Prove2me | solution 2 for NewtonianLipschitz.diagonalParameter_mem_unitInterval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:44:05.050171+00:00
-- url     : https://prove2.me/submissions/3ef7d057-8b8c-4fd9-b6cc-618d98888cb9

module
public import Definitions.Def_NewtonianLipschitz_JacobianMatrix
public import Definitions.Def_NewtonianLipschitz_ScalarMaximum
public import Definitions.Def_NewtonianLipschitz_NormalizedSharpBound
public import Theorems.Thm_NewtonianLipschitz_diagonalParameter_sq


set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz
namespace NewtonianLipschitz
theorem _root_.solution
    (u v : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    diagonalParameter u v ∈ Set.Icc (0 : ℝ) 1 := by
  obtain ⟨ht0, hsq⟩ := diagonalParameter_sq u v
  have hu : 0 ≤ (1 - u) * (1 + u) :=
    mul_nonneg (by linarith) (by linarith)
  have hv : 0 ≤ (1 - v) * (1 + v) :=
    mul_nonneg (by linarith) (by linarith)
  constructor
  · exact ht0
  · nlinarith [hu, hv]
end NewtonianLipschitz
