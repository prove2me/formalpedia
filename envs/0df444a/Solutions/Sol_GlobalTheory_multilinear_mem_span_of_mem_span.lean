-- Prove2me | solution 1 for GlobalTheory.multilinear_mem_span_of_mem_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:23:21.957901+00:00
-- url     : https://prove2.me/submissions/9e3eb782-db9b-4ba0-beb4-d24e87347473

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoefMod
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WeylTensorCoefSpaceLeSpanPureTensors
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPolynomial Formalism.BasicNotions Formalism.L2.DIV
open scoped Matrix
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {K ι M N : Type} [Field K] [Fintype ι]
    [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
    (m : MultilinearMap K (fun _ : ι => M) N) (S : ι → Set M) (f : ι → M)
    (hf : ∀ τ, f τ ∈ Submodule.span K (S τ)) :
    m f ∈ Submodule.span K {P | ∃ g : ι → M, (∀ τ, g τ ∈ S τ) ∧ P = m g} := by
  classical
  have key : ∀ (s : Finset ι) (f : ι → M), (∀ τ, f τ ∈ Submodule.span K (S τ)) →
      (∀ τ, τ ∉ s → f τ ∈ S τ) →
      m f ∈ Submodule.span K {P | ∃ g : ι → M, (∀ τ, g τ ∈ S τ) ∧ P = m g} := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro f _ h
      exact Submodule.subset_span ⟨f, fun τ => h τ (Finset.notMem_empty τ), rfl⟩
    | insert a s ha ih =>
      intro f h1 h2
      have hle : Submodule.span K (S a) ≤
          (Submodule.span K {P | ∃ g : ι → M, (∀ τ, g τ ∈ S τ) ∧ P = m g}).comap
            (m.toLinearMap f a) := by
        rw [Submodule.span_le]
        intro x hx
        rw [SetLike.mem_coe, Submodule.mem_comap, MultilinearMap.toLinearMap_apply]
        apply ih
        · intro τ
          by_cases hτ : τ = a
          · subst hτ
            rw [Function.update_self]
            exact Submodule.subset_span hx
          · rw [Function.update_of_ne hτ]
            exact h1 τ
        · intro τ hτs
          by_cases hτ : τ = a
          · subst hτ
            rw [Function.update_self]
            exact hx
          · rw [Function.update_of_ne hτ]
            exact h2 τ (by simp [hτ, hτs])
      have h := hle (h1 a)
      rw [Submodule.mem_comap, MultilinearMap.toLinearMap_apply, Function.update_eq_self] at h
      exact h
  exact key Finset.univ f hf (fun τ h => absurd (Finset.mem_univ τ) h)
end GlobalTheory
