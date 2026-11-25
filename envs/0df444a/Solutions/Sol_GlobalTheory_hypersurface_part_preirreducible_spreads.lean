-- Prove2me | solution 1 for GlobalTheory.hypersurface_part_preirreducible_spreads
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:50:44.557045+00:00
-- url     : https://prove2.me/submissions/12a5822d-d9b0-42db-9e1a-9f8f393f1247

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SplittingAbsenceSpreadsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HypersurfaceDiffIsPreirreducibleOfNoSplittingStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NoSplittingFactorisationOfPderivNeZeroStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HypersurfacePartGeometricIrreducibleSpreads
import Theorems.Thm_GlobalTheory_T_hypersurface_diff_isPreirreducible_of_no_splitting
import Theorems.Thm_GlobalTheory_T_no_splitting_factorisation_of_pderiv_ne_zero
import Theorems.Thm_GlobalTheory_T_splitting_absence_spreads_alt


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
theorem _root_.solution : ∀ (A : Type) [CommRing A] (σ : Type) [Finite σ] (f g : MvPolynomial σ A) (i : σ), (∀ (k : Type) [Field k] (ψ : A →+* k), MvPolynomial.map ψ f ≠ 0) → (∀ (k : Type) [Field k] (ψ : A →+* k) (Q : σ → k), MvPolynomial.eval Q (MvPolynomial.map ψ f) = 0 → MvPolynomial.eval Q (MvPolynomial.map ψ g) ≠ 0 → MvPolynomial.eval Q (MvPolynomial.pderiv i (MvPolynomial.map ψ f)) ≠ 0) → ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (φ : A →+* Ω), IsPreirreducible (PrimeSpectrum.zeroLocus {MvPolynomial.map φ f} \ PrimeSpectrum.zeroLocus {MvPolynomial.map φ g}) → ∃ (a : A) (I : Finset A), φ a ≠ 0 ∧ (∀ c ∈ I, φ c = 0) ∧ ∀ (k : Type) [Field k] [IsAlgClosed k] (ψ : A →+* k), ψ a ≠ 0 → (∀ c ∈ I, ψ c = 0) → IsPreirreducible (PrimeSpectrum.zeroLocus {MvPolynomial.map ψ f} \ PrimeSpectrum.zeroLocus {MvPolynomial.map ψ g}) := by
  intro A _ σ _ f g i h0 hd Ω _ _ φ hirr
  have h3 := GlobalTheory.T.no_splitting_factorisation_of_pderiv_ne_zero Ω σ (MvPolynomial.map φ f) (MvPolynomial.map φ g) i f.totalDegree
    (hd Ω φ) hirr
  obtain ⟨a, I, ha, hI, h⟩ := GlobalTheory.T.splitting_absence_spreads_alt A σ f g f.totalDegree Ω φ h3
  refine ⟨a, I, ha, hI, fun k _ _ ψ hψa hψI => ?_⟩
  refine GlobalTheory.T.hypersurface_diff_isPreirreducible_of_no_splitting k σ (MvPolynomial.map ψ f) (MvPolynomial.map ψ g) f.totalDegree
    (h0 k ψ) ?_ (h k ψ hψa hψI)
  exact Finset.sup_mono (MvPolynomial.support_map_subset ψ f)
end GlobalTheory
