-- Prove2me | solution 1 for GlobalTheory.TriangularityLowCoeff.aeval_mem_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:38:56.257642+00:00
-- url     : https://prove2.me/submissions/c2987113-e157-4ae4-95e3-49686211d60f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CoeffAnnihilatedOfAevalMemKerPow

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
theorem _root_.solution {R B : Type} [CommRing R] [CommRing B] [Algebra R B] {d : ℕ}
    (ε : B →ₐ[R] R) (y : Fin d → B) (hy : ∀ i, ε (y i) = 0) (n : ℕ) (Q : MvPolynomial (Fin d) R)
    (hQ : Q ∈ idealOfVars (Fin d) R ^ n) : aeval y Q ∈ RingHom.ker ε ^ n := by
  have h1 : Ideal.map (aeval y) (idealOfVars (Fin d) R) ≤ RingHom.ker ε := by
    rw [idealOfVars, Ideal.map_span, Ideal.span_le]
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    simp [RingHom.mem_ker, hy]
  have h2 := Ideal.mem_map_of_mem (aeval y) hQ
  rw [Ideal.map_pow] at h2
  exact Ideal.pow_right_mono h1 n h2
end GlobalTheory.TriangularityLowCoeff
