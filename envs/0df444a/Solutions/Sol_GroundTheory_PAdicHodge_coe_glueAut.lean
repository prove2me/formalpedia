-- Prove2me | solution 1 for GroundTheory.PAdicHodge.coe_glueAut
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:28:40.344801+00:00
-- url     : https://prove2.me/submissions/7d8b50c3-29da-4826-9605-64904bcf00bd

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_FWGlue
import Theorems.Thm_GroundTheory_PAdicHodge_coe_glueHom

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
variable {F E : Type*} [Field F] [Field E] [Algebra F E] {ι : Type*}
variable (Ω : IntermediateField F E) (N : ι → IntermediateField F E) (hN : ∀ i, N i ≤ Ω)
  (hdir : Directed (· ≤ ·) N) (hcov : ∀ x ∈ Ω, ∃ i, x ∈ N i) (f : ∀ i, N i →ₐ[F] N i)
  (hf : ∀ i j (h : N i ≤ N j) (x : N i), ((f j ⟨x, h x.2⟩ : N j) : E) = ((f i x : N i) : E))
namespace GroundTheory.PAdicHodge
theorem _root_.solution [Algebra.IsAlgebraic F Ω] (i : ι) (x : Ω) (hx : (x : E) ∈ N i) :
    ((glueAut Ω N hN hdir hcov f hf x : Ω) : E) = ((f i ⟨x, hx⟩ : N i) : E) :=
  coe_glueHom Ω N hN hdir hcov f hf i x hx
end GroundTheory.PAdicHodge
