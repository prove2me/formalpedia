-- Prove2me | solution 1 for GlobalTheory.preirreducibleSpace_fibre_standardEtale_spreads
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:56:21.322338+00:00
-- url     : https://prove2.me/submissions/c3114207-ff1d-4040-ad15-4c9a18cbdb86

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HypersurfacePartGeometricIrreducibleSpreadsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_StandardEtaleMvPolynomialHypersurfaceStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PreirreducibleSpaceFibreHypersurfaceSpectrumIffStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PreirreducibleFibreStandardEtaleSpreads
import Theorems.Thm_GlobalTheory_preirreducibleSpace_tensor_congr_fibreChart
import Theorems.Thm_GlobalTheory_T_hypersurface_part_geometric_irreducible_spreads
import Theorems.Thm_GlobalTheory_T_preirreducibleSpace_fibreHypersurface_spectrum_iff
import Theorems.Thm_GlobalTheory_T_standardEtale_localization_away_quotient_span


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
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (n : ℕ) [Algebra (MvPolynomial (Fin n) A) B] [IsScalarTower A (MvPolynomial (Fin n) A) B], Algebra.IsStandardEtale (MvPolynomial (Fin n) A) B → ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra A Ω], PreirreducibleSpace (PrimeSpectrum (Ω ⊗[A] B)) → ∃ (a : A) (I : Finset A), algebraMap A Ω a ≠ 0 ∧ (∀ c ∈ I, algebraMap A Ω c = 0) ∧ ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra A k], algebraMap A k a ≠ 0 → (∀ c ∈ I, algebraMap A k c = 0) → PreirreducibleSpace (PrimeSpectrum (k ⊗[A] B)) := by
  intro A B _ _ _ n _ _ hB Ω _ _ _ hΩ
  obtain ⟨f, g, hf, hd, ⟨e⟩⟩ := GlobalTheory.T.standardEtale_localization_away_quotient_span A B n hB
  have hΩ' := (GlobalTheory.T.preirreducibleSpace_fibreHypersurface_spectrum_iff A _ f g Ω).1 ((preirreducibleSpace_tensor_congr_fibreChart A _ _ Ω e).1 hΩ)
  obtain ⟨a, I, ha, hI, hk⟩ := GlobalTheory.T.hypersurface_part_geometric_irreducible_spreads A (Option (Fin n)) f g none hf hd Ω (algebraMap A Ω) hΩ'
  refine ⟨a, I, ha, hI, ?_⟩
  intro k _ _ _ hak hIk
  exact (preirreducibleSpace_tensor_congr_fibreChart A _ _ k e).2
    ((GlobalTheory.T.preirreducibleSpace_fibreHypersurface_spectrum_iff A _ f g k).2 (hk k (algebraMap A k) hak hIk))
end GlobalTheory
