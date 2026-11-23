-- Prove2me | solution 1 for GlobalTheory.TriangularityLowCoeff.iterDer_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:43:26.214177+00:00
-- url     : https://prove2.me/submissions/5707b510-7faf-4d6d-82ec-218f5ad8922a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CoeffAnnihilatedOfAevalMemKerPow
import Theorems.Thm_GlobalTheory_TriangularityLowCoeff_der_mem_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory GlobalTheory.TriangularityLowCoeff
open MvPolynomial
namespace GlobalTheory.TriangularityLowCoeff
theorem _root_.solution {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {d : ℕ}
    (D : Fin d → Derivation R A A) (J : Ideal A) :
    ∀ (L : List (Fin d)) (m : ℕ) (x : A), x ∈ J ^ (L.length + m) → iterDer D L x ∈ J ^ m
  | [], m, x, hx => by simpa [iterDer] using hx
  | i :: L, m, x, hx => by
    show iterDer D L (D i x) ∈ J ^ m
    apply solution D J L m
    apply der_mem_pow (D i) J
    have e : L.length + m + 1 = (i :: L).length + m := by simp; omega
    rw [e]; exact hx
end GlobalTheory.TriangularityLowCoeff
