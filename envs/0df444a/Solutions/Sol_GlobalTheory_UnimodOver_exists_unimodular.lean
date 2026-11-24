-- Prove2me | solution 1 for GlobalTheory.UnimodOver.exists_unimodular
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:02:56.768053+00:00
-- url     : https://prove2.me/submissions/b129635e-e987-4df7-9277-058007232093

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsPolarizedSuperlatticeOfRiemannForm
import Theorems.Thm_GlobalTheory_UnimodOver_discrete_dual
import Theorems.Thm_GlobalTheory_UnimodOver_discrete_of_le
import Theorems.Thm_GlobalTheory_UnimodOver_span_of_le
import Theorems.Thm_GlobalTheory_UnimodOver_exists_nsmul_mem
import Theorems.Thm_GlobalTheory_UnimodOver_exists_selfDual
import Theorems.Thm_GlobalTheory_UnimodOver_dualSubmoduleToDual_surjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.UnimodOver
open Module
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
namespace GlobalTheory.UnimodOver
theorem _root_.solution (B : LinearMap.BilinForm ℝ V) (hB : B.Nondegenerate) (hA : B.IsAlt)
    (Λ : Submodule ℤ V) [DiscreteTopology Λ] (hs : Submodule.span ℝ (Λ : Set V) = ⊤)
    (hint : Λ ≤ B.dualSubmodule Λ) :
    ∃ (M : Submodule ℤ V) (N : ℕ) (Ef : LinearMap.BilinForm ℤ M),
      Λ ≤ M ∧ 0 < N ∧ (∀ x ∈ M, N • x ∈ Λ) ∧ DiscreteTopology M ∧
      Submodule.span ℝ (M : Set V) = ⊤ ∧ (∀ a b : M, (Ef a b : ℝ) = B a b) ∧
      Function.Bijective Ef := by
  obtain ⟨M, h1, h2, h3⟩ := exists_selfDual B hB hA Λ hs hint
  haveI := discrete_dual B hB Λ hs
  haveI : DiscreteTopology M := discrete_of_le h2
  have hsM := span_of_le hs h1
  obtain ⟨N, hN, hNM⟩ := exists_nsmul_mem hs h1
  let e := LinearEquiv.ofEq _ _ h3.symm
  refine ⟨M, N, (B.dualSubmoduleToDual M).comp e.toLinearMap, h1, hN, hNM, this, hsM, ?_, ?_⟩
  · intro a b
    exact B.dualSubmoduleParing_spec (e a) b
  · exact Function.Bijective.comp (g := B.dualSubmoduleToDual M) (f := e)
      ⟨B.dualSubmoduleToDual_injective hB M hsM, dualSubmoduleToDual_surjective B hB M hsM⟩
      e.bijective
end GlobalTheory.UnimodOver
