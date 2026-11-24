-- Prove2me | solution 1 for GlobalTheory.MultiHilbert.finite_colourPiece
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:00:38.154587+00:00
-- url     : https://prove2.me/submissions/0230f93b-cf65-43e0-a71c-dac2ced491ba

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsMultigradedHilbertPoly
import Theorems.Thm_GlobalTheory_MultiHilbert_weight_colour_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.MultiHilbert
open MvPolynomial
variable {K σ : Type} [Field K] {r : ℕ} (col : σ → Fin r)
namespace GlobalTheory.MultiHilbert
theorem _root_.solution [Finite σ] (n : Fin r → ℕ) :
    Module.Finite K (weightedHomogeneousSubmodule K
      (fun i => (Pi.single (col i) 1 : Fin r → ℕ)) n) := by
  have hfin : {d : σ →₀ ℕ |
      Finsupp.weight (fun i => (Pi.single (col i) 1 : Fin r → ℕ)) d = n}.Finite := by
    refine (Finsupp.finite_of_degree_le (σ := σ) (∑ k, n k)).subset fun d hd => ?_
    have hd' : Finsupp.weight (fun i => (Pi.single (col i) 1 : Fin r → ℕ)) d = n := hd
    have : ∑ k, n k = d.degree := by
      rw [← hd']
      simp only [weight_colour_apply]
      rw [Finset.sum_comm]
      simp [Finsupp.degree_apply]
    exact this.ge
  have hle : weightedHomogeneousSubmodule K (fun i => (Pi.single (col i) 1 : Fin r → ℕ)) n ≤
      Submodule.span K ((fun d => (monomial d (1 : K) : MvPolynomial σ K)) '' {d : σ →₀ ℕ |
      Finsupp.weight (fun i => (Pi.single (col i) 1 : Fin r → ℕ)) d = n}) := by
    intro F hF
    rw [F.as_sum]
    refine Submodule.sum_mem _ fun d hd => ?_
    have : monomial d (coeff d F) = coeff d F • (monomial d (1 : K) : MvPolynomial σ K) := by
      rw [smul_monomial, smul_eq_mul, mul_one]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨d, hF (mem_support_iff.1 hd), rfl⟩)
  haveI := FiniteDimensional.span_of_finite K
    (hfin.image (fun d => (monomial d (1 : K) : MvPolynomial σ K)))
  exact Submodule.finiteDimensional_of_le hle
end GlobalTheory.MultiHilbert
