-- Prove2me | solution 1 for GlobalTheory.FinEt.isIso_of_mem_isoLocus
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:45:49.453406+00:00
-- url     : https://prove2.me/submissions/0f55ed1e-a89c-4823-8aab-bc0e67f606d3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoIffBijectiveOverAlgClosed
import Theorems.Thm_GlobalTheory_FinEt_isIso_iff_isoLocus_eq_univ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits TopologicalSpace AlgebraicGeometry
universe u
noncomputable section
open GlobalTheory GlobalTheory.FinEt
attribute [local simp] pullback.lift_fst pullback.lift_snd pullback.lift_fst_assoc
  pullback.lift_snd_assoc
variable {S : Scheme.{u}} {X Y : Over S}
namespace GlobalTheory.FinEt
theorem _root_.solution [PreconnectedSpace S] (f : X ⟶ Y)
    [IsFinite X.hom] [Etale X.hom] [IsFinite Y.hom] [Etale Y.hom] {s : S} (hs : s ∈ isoLocus f) :
    IsIso f :=
  (isIso_iff_isoLocus_eq_univ f).mpr ((isClopen_isoLocus f).eq_univ ⟨s, hs⟩)
end GlobalTheory.FinEt
