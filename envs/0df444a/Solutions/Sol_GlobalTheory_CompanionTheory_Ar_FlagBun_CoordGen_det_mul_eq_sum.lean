-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.FlagBun.CoordGen.det_mul_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:17:24.940905+00:00
-- url     : https://prove2.me/submissions/fa4e3731-dcee-42ae-acec-581b81f0c5ea

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_CoordTieCompEquiv
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_FrameMatrixChartRatios

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.FlagBun.CoordGen
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun
namespace GlobalTheory.CompanionTheory.Ar.FlagBun.CoordGen
theorem _root_.solution {R : Type*} [CommRing R] {m p : Type*} [Fintype m] [DecidableEq m] [Fintype p]
    [DecidableEq p] (A : Matrix m p R) (C : Matrix p m R) :
    (A * C).det = ∑ f : m → p, (∏ i, A i (f i)) * (C.submatrix f id).det := by
  have h : (A * C) = fun i => ∑ j, A i j • C j := by
    ext i k
    simp [Matrix.mul_apply, Finset.sum_apply]
  calc (A * C).det = Matrix.detRowAlternating (fun i => ∑ j, A i j • C j) := by rw [h]; rfl
    _ = ∑ f : m → p, Matrix.detRowAlternating (fun i => A i (f i) • C (f i)) :=
        (Matrix.detRowAlternating (n := m) (R := R)).toMultilinearMap.map_sum _
    _ = _ := by
        refine Finset.sum_congr rfl fun f _ => ?_
        have := (Matrix.detRowAlternating (n := m) (R := R)).toMultilinearMap.map_smul_univ
          (fun i => A i (f i)) (fun i => C (f i))
        exact this.trans (by rw [smul_eq_mul]; rfl)
end GlobalTheory.CompanionTheory.Ar.FlagBun.CoordGen
