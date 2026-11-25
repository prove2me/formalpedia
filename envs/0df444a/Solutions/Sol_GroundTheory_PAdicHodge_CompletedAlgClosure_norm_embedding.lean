-- Prove2me | solution 1 for GroundTheory.PAdicHodge.CompletedAlgClosure.norm_embedding
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:28:33.378798+00:00
-- url     : https://prove2.me/submissions/644f430a-39f8-463a-8791-c131f75a8487

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_CompletedAlgClosure
import Theorems.Thm_GroundTheory_PAdicHodge_SpectralAlgClosure_norm_eq_spectralNorm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
variable (K : Type*) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
open GroundTheory.PAdicHodge.CompletedAlgClosure
variable (L : Type*) [NormedField L] [NormedAlgebra K L] [Algebra.IsAlgebraic K L]
namespace GroundTheory.PAdicHodge.CompletedAlgClosure
theorem _root_.solution (x : L) : ‖embedding K L x‖ = ‖x‖ := by
  set ι : L →ₐ[K] SpectralAlgClosure K := IsAlgClosed.lift
  have h1 : ‖embedding K L x‖ = ‖ι x‖ := by
    change ‖((ι x : SpectralAlgClosure K) : CompletedAlgClosure K)‖ = _
    exact UniformSpace.Completion.norm_coe _
  rw [h1, SpectralAlgClosure.norm_eq_spectralNorm]
  have h2 : spectralNorm K (SpectralAlgClosure K) (ι x) = spectralNorm K L x := by
    simp only [spectralNorm, minpoly.algHom_eq ι ι.injective x]
  rw [h2]
  exact (spectralNorm_unique_field_norm_ext (f := NormedField.toAbsoluteValue L)
    (fun k => norm_algebraMap' L k) x).symm
end GroundTheory.PAdicHodge.CompletedAlgClosure
