-- Prove2me | solution 1 for GlobalTheory.embedding_eq_or_eq_conjugate
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:15:01.488828+00:00
-- url     : https://prove2.me/submissions/9c351e4e-49e9-43b8-b860-28510ce2762f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SumLogNormEmbeddingEqFinrankMulLogAbsNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_LatticeCmEqIdealAndCovolume
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_LatticeDeterminedByInvariants
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_MeanLogCovolumeEqMeanClassGroup

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex NumberField
open scoped nonZeroDivisors Real UpperHalfPlane
noncomputable section
open GlobalTheory
variable {K : Type} [Field K] [NumberField K]
namespace GlobalTheory
theorem _root_.solution (hK : Module.finrank ℚ K = 2) {σ₀ : K →+* ℂ}
    (h₀ : ¬ ComplexEmbedding.IsReal σ₀) (σ : K →+* ℂ) :
    σ = σ₀ ∨ σ = ComplexEmbedding.conjugate σ₀ := by
  classical
  have hne : σ₀ ≠ ComplexEmbedding.conjugate σ₀ := fun h =>
    h₀ (ComplexEmbedding.isReal_iff.2 h.symm)
  have : ({σ₀, ComplexEmbedding.conjugate σ₀} : Finset (K →+* ℂ)) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_pair hne, Embeddings.card, hK]
  have hm := this ▸ Finset.mem_univ σ
  simpa using hm
end GlobalTheory
