-- Prove2me | solution 1 for GlobalTheory.exists_graded_surjection
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:37:45.479581+00:00
-- url     : https://prove2.me/submissions/930bf126-7d9c-49d6-afb7-9b8e19062040

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_XSmulMemWeightedHomogeneousSubmodule
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_WeightAddLeOfMemSupportDividedContraction
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsGradedMapLinearCombination
import Theorems.Thm_GlobalTheory_isGradedMap_linearCombination
import Theorems.Thm_GlobalTheory_Wick_dividedContraction_one
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Wick.dividedContraction_one



set_option autoImplicit false
open DirectSum MvPolynomial
noncomputable section
open GlobalTheory
open GradedHilbert
variable {ι : Type*} {R : Type*} [CommRing R] {κ : Type*}
  {M : κ → Type*} [∀ k, AddCommGroup (M k)] [∀ k, Module R (M k)]
  [∀ k, Module (MvPolynomial ι R) (M k)]
  {N : Type*} [AddCommGroup N] [Module R N] [Module (MvPolynomial ι R) N]
namespace GlobalTheory
theorem _root_.solution (𝒩 : ℤ → Submodule R N) [Decomposition 𝒩] [PolyGradedSMul ι 𝒩]
    [Module.Finite (MvPolynomial ι R) N] :
    ∃ (r : ℕ) (d : Fin r → ℤ) (f : (Fin r → MvPolynomial ι R) →ₗ[MvPolynomial ι R] N),
      IsGradedMap (grFree ι R d) 𝒩 f ∧ Function.Surjective f := by
  classical
  obtain ⟨G, hG⟩ := Module.Finite.fg_top (R := MvPolynomial ι R) (M := N)
  choose T hT using exists_sum_grProj 𝒩
  let U : Finset (N × ℤ) := G ×ˢ G.biUnion T
  let e := U.equivFin.symm
  refine ⟨U.card, fun k => (e k).1.2, Fintype.linearCombination _
    fun k => proj 𝒩 (e k).1.2 (e k).1.1,
    isGradedMap_linearCombination 𝒩 fun k => proj_mem _ _ _, ?_⟩
  rw [← LinearMap.range_eq_top, Fintype.range_linearCombination, eq_top_iff, ← hG,
    Submodule.span_le]
  intro g hg
  rw [← hT g]
  refine Submodule.sum_mem _ fun j hj => Submodule.subset_span
    ⟨e.symm ⟨(g, j), Finset.mem_product.2 ⟨hg, Finset.mem_biUnion.2 ⟨g, hg, hj⟩⟩⟩, by simp⟩
end GlobalTheory
