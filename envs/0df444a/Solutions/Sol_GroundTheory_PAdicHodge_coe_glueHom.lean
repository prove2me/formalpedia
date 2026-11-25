-- Prove2me | solution 1 for GroundTheory.PAdicHodge.coe_glueHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:18:12.954057+00:00
-- url     : https://prove2.me/submissions/84462269-d718-4240-8dcd-342adaac827e

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_FWGlue

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
theorem _root_.solution (i : ι) (x : Ω) (hx : (x : E) ∈ N i) :
    ((glueHom Ω N hN hdir hcov f hf x : Ω) : E) = ((f i ⟨x, hx⟩ : N i) : E) :=
  glueFun_eq Ω N hdir hcov f hf i x hx
end GroundTheory.PAdicHodge
