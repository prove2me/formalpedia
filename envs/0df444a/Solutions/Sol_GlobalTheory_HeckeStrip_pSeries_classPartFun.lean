-- Prove2me | solution 1 for GlobalTheory.HeckeStrip.pSeries_classPartFun
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:35:06.495262+00:00
-- url     : https://prove2.me/submissions/ca5f9e77-4ed0-47d4-8e79-0b8547b69bf1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_CompletedLStripBounds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormWt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_TsumIdealEqSumClassGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ClassGroupCoprimeRepresentative
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RayLSeriesEulerProduct
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeLSeriesEqSumPrincipalPartialSeries
import Theorems.Thm_GlobalTheory_HeckeStrip_pval_classPartFun
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub



set_option autoImplicit false
noncomputable section
open NumberField
open scoped nonZeroDivisors
open GlobalTheory GlobalTheory.HeckeStrip
variable {K : Type} [Field K] [NumberField K] {I : Type} [Fintype I]
variable {φ : I → K →+* ℂ} {n : I → ℤ} {m : Ideal (𝓞 K)} {X : Ideal (𝓞 K) → ℂ}
namespace GlobalTheory.HeckeStrip
theorem _root_.solution
    (hβ : ∀ β : 𝓞 K, β ≠ 0 → β - 1 ∈ m → X (Ideal.span {β}) = wt φ n (β : K))
    (b : Ideal (𝓞 K)) (s : ℂ) :
    pSeries (classPartFun φ n m X b) φ n s =
      ∑' J : {J : Ideal (𝓞 K) // J ≠ ⊥ ∧ J.IsPrincipal ∧ J ≤ b}, X J.1 * ((Ideal.absNorm J.1 : ℕ) : ℂ) ^ (-s) := by
  classical
  let f : Ideal (𝓞 K) → ℂ := fun J => (if J ≤ b then X J else 0) * ((Ideal.absNorm J : ℕ) : ℂ) ^ (-s)
  let g : Ideal (𝓞 K) → ℂ := fun J => X J * ((Ideal.absNorm J : ℕ) : ℂ) ^ (-s)
  have h1 : ∀ J : {J : Ideal (𝓞 K) // J ≠ ⊥ ∧ J.IsPrincipal},
      (haveI := J.2.2; pval (classPartFun φ n m X b) φ n J.1) * ((Ideal.absNorm J.1 : ℕ) : ℂ) ^ (-s) = f J.1 := by
    rintro ⟨J, hJ, hP⟩
    simp only [f]
    rw [pval_classPartFun hβ b J hJ]
  unfold pSeries
  rw [tsum_congr h1]
  have e1 := tsum_subtype {J : Ideal (𝓞 K) | J ≠ ⊥ ∧ J.IsPrincipal} f
  have e2 := tsum_subtype {J : Ideal (𝓞 K) | J ≠ ⊥ ∧ J.IsPrincipal ∧ J ≤ b} g
  refine e1.trans (Eq.trans ?_ e2.symm)
  refine tsum_congr fun J => ?_
  by_cases hJ : J ≠ ⊥ ∧ J.IsPrincipal
  · by_cases h : J ≤ b
    · rw [Set.indicator_of_mem (show J ∈ {J : Ideal (𝓞 K) | J ≠ ⊥ ∧ J.IsPrincipal} from hJ),
        Set.indicator_of_mem (show J ∈ {J : Ideal (𝓞 K) | J ≠ ⊥ ∧ J.IsPrincipal ∧ J ≤ b} from ⟨hJ.1, hJ.2, h⟩)]
      simp only [f, g, if_pos h]
    · rw [Set.indicator_of_mem (show J ∈ {J : Ideal (𝓞 K) | J ≠ ⊥ ∧ J.IsPrincipal} from hJ),
        Set.indicator_of_notMem (show J ∉ {J : Ideal (𝓞 K) | J ≠ ⊥ ∧ J.IsPrincipal ∧ J ≤ b} from fun h' => h h'.2.2)]
      simp only [f, if_neg h, zero_mul]
  · rw [Set.indicator_of_notMem (show J ∉ {J : Ideal (𝓞 K) | J ≠ ⊥ ∧ J.IsPrincipal} from hJ),
      Set.indicator_of_notMem (show J ∉ {J : Ideal (𝓞 K) | J ≠ ⊥ ∧ J.IsPrincipal ∧ J ≤ b} from
        fun h' => hJ ⟨h'.1, h'.2.1⟩)]
end GlobalTheory.HeckeStrip
