-- Prove2me | solution 1 for GlobalTheory.two_mul_card_of_cmType_finset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:38:50.549727+00:00
-- url     : https://prove2.me/submissions/c7c95ce9-5bfa-4684-b159-aecce222bbff

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_UnivFrame
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_NormConst
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CuspFree
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RdOrbIntOfLatZ
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Landherr__ExistsNormTensor_9eff20d6b37353d0
import Definitions.Def_Development_AbelianVarietyTheory_Statements_HyperbolicHypotheses_HypothesesInhabitedHyperbolic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FinrankRatSkewHermitianMatricesCmField

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (E : Type) [Field E] [NumberField E]
    (Ψ : Finset (E →+* ℂ)) (hΨ : ∀ τ : E →+* ℂ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ) :
    2 * Ψ.card = Module.finrank ℚ E := by
  classical
  have hcc : ∀ τ : E →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate τ) = τ :=
    fun τ => star_star τ
  rw [← NumberField.Embeddings.card E ℂ]
  have h1 : (Ψᶜ).card = Ψ.card := by
    refine Finset.card_bij (fun τ _ => ComplexEmbedding.conjugate τ) ?_ ?_ ?_
    · intro τ hτ
      rw [Finset.mem_compl] at hτ
      exact (hΨ _).mpr (by rw [hcc]; exact hτ)
    · intro a _ b _ h
      have := congrArg ComplexEmbedding.conjugate h
      rwa [hcc, hcc] at this
    · intro τ hτ
      refine ⟨ComplexEmbedding.conjugate τ, ?_, hcc τ⟩
      rw [Finset.mem_compl]
      exact (hΨ τ).mp hτ
  have h2 := Finset.card_add_card_compl Ψ
  omega
end GlobalTheory
