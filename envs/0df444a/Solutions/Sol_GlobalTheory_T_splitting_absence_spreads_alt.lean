-- Prove2me | solution 1 for GlobalTheory.T.splitting_absence_spreads_alt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:40:37.933532+00:00
-- url     : https://prove2.me/submissions/60571c48-df8a-4d85-b49e-12c26b92736f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SplittingAbsenceSpreads
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SplittingAbsenceSpreadsStatement
import Theorems.Thm_GlobalTheory_splitting_absence_spreads


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
theorem _root_.solution : ∀ (A : Type) [CommRing A] (σ : Type) [Finite σ] (f g : MvPolynomial σ A) (D : ℕ) (Ω : Type) [Field Ω] [IsAlgClosed Ω] (φ : A →+* Ω), ¬ (∃ u v : MvPolynomial σ Ω, u.totalDegree ≤ D ∧ v.totalDegree ≤ D ∧ u * v = MvPolynomial.map φ f ∧ ∃ P Q : σ → Ω, MvPolynomial.eval P u = 0 ∧ MvPolynomial.eval P (MvPolynomial.map φ g) ≠ 0 ∧ MvPolynomial.eval Q v = 0 ∧ MvPolynomial.eval Q (MvPolynomial.map φ g) ≠ 0) → ∃ (a : A) (I : Finset A), φ a ≠ 0 ∧ (∀ c ∈ I, φ c = 0) ∧ ∀ (k : Type) [Field k] (ψ : A →+* k), ψ a ≠ 0 → (∀ c ∈ I, ψ c = 0) → ¬ (∃ u v : MvPolynomial σ k, u.totalDegree ≤ D ∧ v.totalDegree ≤ D ∧ u * v = MvPolynomial.map ψ f ∧ ∃ P Q : σ → k, MvPolynomial.eval P u = 0 ∧ MvPolynomial.eval P (MvPolynomial.map ψ g) ≠ 0 ∧ MvPolynomial.eval Q v = 0 ∧ MvPolynomial.eval Q (MvPolynomial.map ψ g) ≠ 0) := by
  first | exact @GlobalTheory.splitting_absence_spreads | exact GlobalTheory.splitting_absence_spreads | (intros; apply GlobalTheory.splitting_absence_spreads <;> assumption)
end _root_.GlobalTheory.T
