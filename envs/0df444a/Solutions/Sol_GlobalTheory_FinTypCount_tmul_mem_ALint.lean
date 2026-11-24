-- Prove2me | solution 1 for GlobalTheory.FinTypCount.tmul_mem_ALint
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:26:38.928998+00:00
-- url     : https://prove2.me/submissions/a88a4c46-18e7-48f1-a0fb-d7e9d6bc02e0

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GaloisLevelStructure_DefsFinTyp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FiniteAdeleStrongApproximationModNat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RankLeAleph0SmoothIrreducibleUnitaryAdelic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2.NG
open scoped TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.FinTypCount
variable {L : Type} [Field L] [NumberField L] [IsCMField L]
local notation3 "L⁺" => NumberField.maximalRealSubfield L
namespace GlobalTheory.FinTypCount
theorem _root_.solution (o : 𝓞 L) {a : AFplus L} (ha : ∀ v, a v ∈ v.adicCompletionIntegers L⁺) :
    ((o : L) ⊗ₜ[L⁺] a : AL L) ∈ ALint L := by
  have h1 : ((o : L) ⊗ₜ[L⁺] (1 : AFplus L) : AL L) ∈ ALint L :=
    Subring.subset_closure (Or.inl ⟨o, rfl⟩)
  have h2 : ((1 : L) ⊗ₜ[L⁺] a : AL L) ∈ ALint L :=
    Subring.subset_closure (Or.inr ⟨a, ha, rfl⟩)
  have := Subring.mul_mem _ h1 h2
  rwa [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul] at this
end GlobalTheory.FinTypCount
