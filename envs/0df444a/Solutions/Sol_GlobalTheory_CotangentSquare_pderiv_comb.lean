-- Prove2me | solution 1 for GlobalTheory.CotangentSquare.pderiv_comb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:06:54.779571+00:00
-- url     : https://prove2.me/submissions/a0215ef0-1eb6-4c03-b5d2-27cecb33dd74

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CotangentMapInjectiveOfSquarePresentationAtPoint

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory GlobalTheory.CotangentSquare
open MvPolynomial
variable {O B σ : Type} [CommRing O] [CommRing B]
namespace GlobalTheory.CotangentSquare
theorem _root_.solution [Fintype σ] (η : MvPolynomial σ B →+* O) (f g : σ → MvPolynomial σ B)
    (hf : ∀ i, η (f i) = 0) (k : MvPolynomial σ B) (hk : k ∈ firstOrderKer η) (l : σ) :
    η (pderiv l (∑ i, g i * f i + k)) = ∑ i, η (g i) * η (pderiv l (f i)) := by
  have := hk.2 l
  simp [map_sum, pderiv_mul, hf, this]
end GlobalTheory.CotangentSquare
