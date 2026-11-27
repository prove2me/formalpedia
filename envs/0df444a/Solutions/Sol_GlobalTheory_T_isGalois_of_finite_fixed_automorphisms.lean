-- Prove2me | solution 1 for GlobalTheory.T.isGalois_of_finite_fixed_automorphisms
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:33:41.353794+00:00
-- url     : https://prove2.me/submissions/b4a1cffe-f527-493e-a7c0-c668ea06bfc1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaloisOfFiniteGeneratingAutomorphisms
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaloisOfFiniteGeneratingAutomorphismsStatement
import Theorems.Thm_GlobalTheory_galois_of_finite_generating_automorphisms


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K K' : Type) [Field K] [Field K'] (i : K →+* K'), i.Finite → ∀ (Γ : Type) [Finite Γ] (s : Γ → (K' ≃+* K')), (∀ g x, s g (i x) = i x) → (∀ y : K', (∀ g, s g y = y) → y ∈ i.range) → (letI := i.toAlgebra; IsGalois K K') ∧ ∀ σ : K' ≃+* K', (∀ x, σ (i x) = i x) → σ ∈ Submonoid.closure (Set.range s) := by
  first | exact @GlobalTheory.galois_of_finite_generating_automorphisms | exact GlobalTheory.galois_of_finite_generating_automorphisms | (intros; apply GlobalTheory.galois_of_finite_generating_automorphisms <;> assumption)
end _root_.GlobalTheory.T
