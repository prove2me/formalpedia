-- Prove2me | solution 1 for GlobalTheory.AffinePoints.volume_coords_image_zeroSet
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:27:44.977083+00:00
-- url     : https://prove2.me/submissions/bd44dd54-ed72-4e5f-9531-f4e86cda6af0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsApplyEqZeroAndEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HasAlgebraicChartsOfIsStandardSmooth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_RingKrullDimQuotientEqOfMemMinimalPrimes
import Definitions.Def_ReciprocityTheory_SemistableReduction_AeBlockSphereEvalNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsNeZeroIsStandardSmoothOfRelativeDimension
import Theorems.Thm_GlobalTheory_AffinePoints_aeval_coords
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_ae_eval_ne_zero_of_ne_zero_fin


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.AffinePoints
open Topology Filter Set MvPolynomial MeasureTheory Module
open scoped Manifold ContDiff
variable {A : Type} [CommRing A] [Algebra ℂ A] {d : ℕ}
namespace GlobalTheory.AffinePoints
theorem _root_.solution [IsDomain A] (g : MvPolynomial (Fin d) ℂ →ₐ[ℂ] A)
    (hg : @Algebra.IsAlgebraic _ A _ _ g.toRingHom.toAlgebra) {f : A} (hf : f ≠ 0) :
    volume (coords g '' {p : A →ₐ[ℂ] ℂ | p f = 0}) = 0 := by
  letI : Algebra (MvPolynomial (Fin d) ℂ) A := g.toRingHom.toAlgebra
  obtain ⟨r, hr, c, hc⟩ := (hg.isAlgebraic f).exists_nonzero_dvd
    (mem_nonZeroDivisors_of_ne_zero hf)
  refine measure_mono_null ?_ (ReciprocityTheory.MultiplicativeHeights.ae_eval_ne_zero_of_ne_zero_fin d r hr)
  rintro _ ⟨p, hp, rfl⟩
  have h1 : eval (coords g p) r = p (g r) := aeval_coords g p r
  have h2 : g r = f * c := hc
  simp only [mem_compl_iff, mem_setOf_eq, not_not]
  rw [h1, h2, map_mul, hp, zero_mul]
end GlobalTheory.AffinePoints
