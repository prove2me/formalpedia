-- Prove2me | solution 1 for GlobalTheory.WirtChain.ExpSum.const_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:09:21.676878+00:00
-- url     : https://prove2.me/submissions/dd5ca169-011a-4eaf-bee9-dc576376bc94

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
theorem _root_.solution {F : ℂ → (I → ℂ) → ℂ} (hF : ExpSum U G t l F) (c : ℂ) :
    ExpSum U G t l fun σ z => c * F σ z := by
  induction hF with
  | zero => simpa using ExpSum.zero (U := U) (G := G) (t := t) (l := l)
  | term n β w hβ =>
    have h := ExpSum.term (U := U) (G := G) (t := t) (l := l) n (fun z => c * β z) w (contDiffOn_const.mul hβ)
    convert h using 2
    ring_nf
  | add _ _ h₁ h₂ =>
    have h := ExpSum.add h₁ h₂
    convert h using 2
    ring_nf
end ExpSum
end GlobalTheory.WirtChain
