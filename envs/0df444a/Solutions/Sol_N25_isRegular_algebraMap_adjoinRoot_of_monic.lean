-- Prove2me | solution 1 for N25.isRegular_algebraMap_adjoinRoot_of_monic
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:35:57.440163+00:00
-- url     : https://prove2.me/submissions/7e6455aa-3353-4952-b361-dd74de1d1824

import Mathlib

/-! Regularity in monic root extensions and two-element regular-sequence swaps. -/
noncomputable section

namespace N25

open Polynomial

/-! ## Scalar regularity in a monic root extension -/

/-- A nonzero scalar remains regular after adjoining a root of a monic
polynomial over a domain.  The monic root extension is free, hence flat,
over the base ring. -/
theorem _root_.solution
    {A : Type*} [CommRing A] [NoZeroDivisors A]
    (p : A[X]) (hp : p.Monic) {a : A} (ha : a ≠ 0) :
    IsRegular (algebraMap A (AdjoinRoot p) a) := by
  letI : Module.Free A (AdjoinRoot p) := hp.free_adjoinRoot
  have hscalar : IsSMulRegular (AdjoinRoot p) a :=
    Module.Flat.isSMulRegular_of_isRegular (IsRegular.of_ne_zero' ha)
  have hleft : IsLeftRegular (algebraMap A (AdjoinRoot p) a) := by
    intro x y hxy
    apply hscalar
    simpa only [Algebra.smul_def] using hxy
  refine ⟨hleft, ?_⟩
  intro x y hxy
  apply hleft
  simpa only [mul_comm] using hxy

end N25
