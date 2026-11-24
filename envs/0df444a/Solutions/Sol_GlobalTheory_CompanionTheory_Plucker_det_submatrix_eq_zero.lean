-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Plucker.det_submatrix_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:08:33.455621+00:00
-- url     : https://prove2.me/submissions/9c1af930-3221-4626-9640-f5e14a18ae0c

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_ConvGrOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_MulConjTransposeEqOneOfOrthonormal
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ConvergenceGroupOfBlockDet

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Plucker
variable {ι : Type} [Fintype ι] [DecidableEq ι] {m : Type} [Fintype m] [DecidableEq m]
variable {R : Type} [CommRing R]
namespace GlobalTheory.CompanionTheory.Plucker
theorem _root_.solution (M : Matrix ι ι R) (t u : Sub ι m) (f : m → ι) (hf : Function.Injective f)
    (hr : ∀ a, f a ∈ t.1) (h0 : cmp M t u = 0) : (M.submatrix f (en u)).det = 0 := by
  have h1 : ∀ a, ∃ c, en t c = f a := fun a => by
    have : f a ∈ Set.range (en t) := by rw [range_en]; exact hr a
    exact this
  choose s hs using h1
  have hinj : Function.Injective s := fun a b h => hf (by rw [← hs a, ← hs b, h])
  let σ : Equiv.Perm m := Equiv.ofBijective s (Finite.injective_iff_bijective.mp hinj)
  have hM : M.submatrix f (en u) = (M.submatrix (en t) (en u)).submatrix σ id := by
    ext a c
    simp [σ, hs]
  rw [hM, det_permute, ← cmp_apply, h0, mul_zero]
end GlobalTheory.CompanionTheory.Plucker
