-- Prove2me | solution 1 for GlobalTheory.splitting_absence_spreads
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:33:51.707797+00:00
-- url     : https://prove2.me/submissions/e49fb30f-9069-4cca-98b8-3361f4d387b5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NoCommonZeroSpreadsConstructibleNbhdStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SplittingAbsenceSpreads
import Theorems.Thm_GlobalTheory_SplitSpread_bad_iff
import Theorems.Thm_GlobalTheory_T_no_common_zero_spreads_constructible_nbhd


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
namespace GlobalTheory
theorem _root_.solution : ∀ (A : Type) [CommRing A] (σ : Type) [Finite σ] (f g : MvPolynomial σ A) (D : ℕ) (Ω : Type) [Field Ω] [IsAlgClosed Ω] (φ : A →+* Ω), ¬ (∃ u v : MvPolynomial σ Ω, u.totalDegree ≤ D ∧ v.totalDegree ≤ D ∧ u * v = MvPolynomial.map φ f ∧ ∃ P Q : σ → Ω, MvPolynomial.eval P u = 0 ∧ MvPolynomial.eval P (MvPolynomial.map φ g) ≠ 0 ∧ MvPolynomial.eval Q v = 0 ∧ MvPolynomial.eval Q (MvPolynomial.map φ g) ≠ 0) → ∃ (a : A) (I : Finset A), φ a ≠ 0 ∧ (∀ c ∈ I, φ c = 0) ∧ ∀ (k : Type) [Field k] (ψ : A →+* k), ψ a ≠ 0 → (∀ c ∈ I, ψ c = 0) → ¬ (∃ u v : MvPolynomial σ k, u.totalDegree ≤ D ∧ v.totalDegree ≤ D ∧ u * v = MvPolynomial.map ψ f ∧ ∃ P Q : σ → k, MvPolynomial.eval P u = 0 ∧ MvPolynomial.eval P (MvPolynomial.map ψ g) ≠ 0 ∧ MvPolynomial.eval Q v = 0 ∧ MvPolynomial.eval Q (MvPolynomial.map ψ g) ≠ 0) := by
  intro A _ σ _ f g D Ω _ _ φ hbad
  have h0 : ¬ ∃ z : GlobalTheory.SplitSpread.Var σ D → Ω, ∀ j,
      MvPolynomial.eval₂ φ z (GlobalTheory.SplitSpread.eqs A D f g j) = 0 := by
    rw [GlobalTheory.SplitSpread.bad_iff]; exact hbad
  obtain ⟨a, I, ha, hI, hk⟩ := GlobalTheory.T.no_common_zero_spreads_constructible_nbhd A _ _ (GlobalTheory.SplitSpread.eqs A D f g) Ω φ h0
  refine ⟨a, I, ha, hI, fun k _ ψ hψa hψI hb => hk k ψ hψa hψI ?_⟩
  exact (GlobalTheory.SplitSpread.bad_iff f g D k ψ).mpr hb
end GlobalTheory
