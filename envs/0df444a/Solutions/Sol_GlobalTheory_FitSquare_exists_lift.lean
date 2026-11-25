-- Prove2me | solution 1 for GlobalTheory.FitSquare.exists_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:42:19.098598+00:00
-- url     : https://prove2.me/submissions/6c977cc1-5480-4d30-945f-617525500c5a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DetMemSpanAdjugate

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.FitSquare
variable {R : Type} [CommRing R]
namespace GlobalTheory.FitSquare
theorem _root_.solution {ι N M : Type} [Fintype ι] [DecidableEq ι] [AddCommGroup N] [Module R N]
    [AddCommGroup M] [Module R M] (h : (ι → R) →ₗ[R] M) (g : N →ₗ[R] M)
    (hh : ∀ y, ∃ z, g z = h y) : ∃ l : (ι → R) →ₗ[R] N, g ∘ₗ l = h := by
  choose z hz using hh
  refine ⟨(Pi.basisFun R ι).constr R (fun i => z (Pi.basisFun R ι i)), ?_⟩
  apply (Pi.basisFun R ι).ext
  intro i
  rw [LinearMap.comp_apply, Module.Basis.constr_basis, hz]
end GlobalTheory.FitSquare
