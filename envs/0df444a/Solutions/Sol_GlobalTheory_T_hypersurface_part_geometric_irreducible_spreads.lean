-- Prove2me | solution 1 for GlobalTheory.T.hypersurface_part_geometric_irreducible_spreads
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:56:54.576475+00:00
-- url     : https://prove2.me/submissions/4699a974-cc54-400f-b931-c90e30e245ec

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HypersurfacePartGeometricIrreducibleSpreads
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HypersurfacePartGeometricIrreducibleSpreadsStatement
import Theorems.Thm_GlobalTheory_hypersurface_part_preirreducible_spreads


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (A : Type) [CommRing A] (σ : Type) [Finite σ] (f g : MvPolynomial σ A) (i : σ), (∀ (k : Type) [Field k] (ψ : A →+* k), MvPolynomial.map ψ f ≠ 0) → (∀ (k : Type) [Field k] (ψ : A →+* k) (Q : σ → k), MvPolynomial.eval Q (MvPolynomial.map ψ f) = 0 → MvPolynomial.eval Q (MvPolynomial.map ψ g) ≠ 0 → MvPolynomial.eval Q (MvPolynomial.pderiv i (MvPolynomial.map ψ f)) ≠ 0) → ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (φ : A →+* Ω), IsPreirreducible (PrimeSpectrum.zeroLocus {MvPolynomial.map φ f} \ PrimeSpectrum.zeroLocus {MvPolynomial.map φ g}) → ∃ (a : A) (I : Finset A), φ a ≠ 0 ∧ (∀ c ∈ I, φ c = 0) ∧ ∀ (k : Type) [Field k] [IsAlgClosed k] (ψ : A →+* k), ψ a ≠ 0 → (∀ c ∈ I, ψ c = 0) → IsPreirreducible (PrimeSpectrum.zeroLocus {MvPolynomial.map ψ f} \ PrimeSpectrum.zeroLocus {MvPolynomial.map ψ g}) := by
  first | exact @GlobalTheory.hypersurface_part_preirreducible_spreads | exact GlobalTheory.hypersurface_part_preirreducible_spreads | (intros; apply GlobalTheory.hypersurface_part_preirreducible_spreads <;> assumption)
end _root_.GlobalTheory.T
