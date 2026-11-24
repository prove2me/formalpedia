-- Prove2me | solution 1 for GlobalTheory.WirtChain.ExpSum.sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:17:51.566427+00:00
-- url     : https://prove2.me/submissions/c28a8305-9413-4d56-9a62-457cca670ddf

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DifferentiableRisingS
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DifferentiableOnWirtWordMulExpComp
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
import Theorems.Thm_GlobalTheory_WeightTwoSum_dz_apply
import Theorems.Thm_GlobalTheory_WeightTwoSum_dzbar_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub
attribute [local simp] GlobalTheory.WeightTwoSum.dz_apply
attribute [local simp] GlobalTheory.WeightTwoSum.dzbar_apply



set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.WeightTwoSum
open scoped ContDiff nonZeroDivisors
noncomputable section
open GlobalTheory GlobalTheory.WirtChain
open Complex
variable {Φ I : Type} [Fintype Φ] [Fintype I]
variable (U : Set (I → ℂ)) (G : ℂ → (Φ → ℂ) → ℂ) (t : (I → ℂ) → Φ → ℂ) (l : (I → ℂ) → ℂ)
variable {U G t l}
namespace GlobalTheory.WirtChain
namespace ExpSum
theorem _root_.solution {α : Type} (s : Finset α) (F : α → ℂ → (I → ℂ) → ℂ) (hF : ∀ a ∈ s, ExpSum U G t l (F a)) :
    ExpSum U G t l fun σ z => ∑ a ∈ s, F a σ z := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using ExpSum.zero (U := U) (G := G) (t := t) (l := l)
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact ExpSum.add (hF a (Finset.mem_insert_self a s)) (ih fun b hb => hF b (Finset.mem_insert_of_mem hb))
end ExpSum
end GlobalTheory.WirtChain
