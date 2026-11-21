-- Prove2me | solution 1 for NewtonianLipschitz.lateralRowNumerator_swapped_le_dominant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:42:02.629473+00:00
-- url     : https://prove2.me/submissions/d1c5a90c-3a29-4b8b-85e6-1cfb8e2d090d

module
public import Mathlib
public import Definitions.Def_NewtonianLipschitz_JacobianRows
public import Theorems.Thm_NewtonianLipschitz_lateralRowNumerator_le_dominant

set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz
namespace NewtonianLipschitz
theorem _root_.solution
    (u v : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    lateralRowNumerator v u ≤ dominantRowNumerator u v := by
  calc
    lateralRowNumerator v u ≤ dominantRowNumerator v u :=
      lateralRowNumerator_le_dominant v u hv0 hv1 hu0 hu1
    _ = dominantRowNumerator u v := by
      unfold dominantRowNumerator
      ring
end NewtonianLipschitz
