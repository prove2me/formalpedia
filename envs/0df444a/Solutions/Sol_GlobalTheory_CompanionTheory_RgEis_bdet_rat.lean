-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEis.bdet_rat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:51:22.103855+00:00
-- url     : https://prove2.me/submissions/213ab4db-1b7e-4ed5-b3b0-bae1dc6b52fd

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_ConvGrOf
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_BlockDeterminantLaw
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEis_bdet_val

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
open scoped ComplexConjugate
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgEis
open PositivityTheory.RgEis
variable {R : Type} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι]
variable {E : Type} [Field E]
open Classical
namespace GlobalTheory.CompanionTheory.RgEis
theorem _root_.solution (A : Ad E R) (hi : Function.Injective A.i) (s : Set ι) {p : GL ι R}
    (hp : p ∈ stab R s) (hr : p ∈ A.ratGL ι) : ∃ x, bdet s p = Units.map A.i.toMonoidHom x := by
  obtain ⟨g, rfl⟩ := hr
  set d : E := ((g : Matrix ι ι E).submatrix (Subtype.val : s → ι) Subtype.val).det with hd
  have hval : ((bdet s (Matrix.GeneralLinearGroup.map A.i g) : Rˣ) : R) = A.i d := by
    rw [bdet_val s hp, hd, RingHom.map_det]
    congr 1
  have hd0 : d ≠ 0 := by
    intro h0
    have hu := (bdet s (Matrix.GeneralLinearGroup.map A.i g)).isUnit
    rw [hval, h0, map_zero] at hu
    have h10 : (0 : R) = 1 := by
      have := isUnit_zero_iff.1 hu
      exact this
    exact zero_ne_one (hi (by rw [map_zero, map_one, h10]) : (0 : E) = 1)
  refine ⟨Units.mk0 d hd0, Units.ext ?_⟩
  rw [hval]
  rfl
end GlobalTheory.CompanionTheory.RgEis
