-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEis.continuousOn_bdet
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:13:59.003608+00:00
-- url     : https://prove2.me/submissions/936bcbf9-8706-4b55-96fb-a5a62f7c2f3f

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_ConvGrOf
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_BlockDeterminantLaw
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEis_bdet_val
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEis_bdet_inv

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
variable [TopologicalSpace R] [IsTopologicalRing R]
namespace GlobalTheory.CompanionTheory.RgEis
theorem _root_.solution (s : Set ι) :
    ContinuousOn (bdet s) (stab R s : Set (GL ι R)) := by
  classical
  have hm (p : (stab R s : Set (GL ι R))) : (p : GL ι R) ∈ stab R s := p.2
  rw [continuousOn_iff_continuous_restrict, Units.continuous_iff]
  constructor
  · refine Continuous.congr (f := fun p : (stab R s : Set (GL ι R)) =>
      (((p : GL ι R) : Matrix ι ι R).submatrix (Subtype.val : s → ι) Subtype.val).det)
      ((Units.continuous_val.comp continuous_subtype_val).matrix_submatrix _ _ |>.matrix_det)
      fun p => (bdet_val s (hm p)).symm
  · refine Continuous.congr (f := fun p : (stab R s : Set (GL ι R)) =>
      ((((p : GL ι R)⁻¹ : GL ι R) : Matrix ι ι R).submatrix (Subtype.val : s → ι) Subtype.val).det)
      (((Units.continuous_val.comp continuous_inv).comp continuous_subtype_val).matrix_submatrix _ _ |>.matrix_det)
      fun p => ?_
    show _ = (((bdet s (p : GL ι R))⁻¹ : Rˣ) : R)
    rw [bdet_inv s (hm p), bdet_val s (inv_mem (hm p))]
end GlobalTheory.CompanionTheory.RgEis
