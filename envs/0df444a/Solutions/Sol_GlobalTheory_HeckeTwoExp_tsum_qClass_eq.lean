-- Prove2me | solution 1 for GlobalTheory.HeckeTwoExp.tsum_qClass_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:24:59.486145+00:00
-- url     : https://prove2.me/submissions/c10cc0ec-8c9d-4d7b-8073-86bebb79712d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AbsNormEqProd
import Theorems.Thm_GlobalTheory_HeckeTwoExp_toQ_injective
import Theorems.Thm_GlobalTheory_HeckeTwoExp_toQ_surjective
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_OmegaFactorization_qClass_mk


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
noncomputable section
open GlobalTheory GlobalTheory.HeckeTwoExp
variable {F : Type} [Field F] [NumberField F]
namespace GlobalTheory.HeckeTwoExp
theorem _root_.solution [IsTotallyReal F] (𝔞 𝔟 : Frac F) (z : Emb F → ℂ) (hS : Summable (qClass 𝔞 𝔟 2 z)) :
    ∑' c, qClass 𝔞 𝔟 2 z c = ∑' c : Quotient (unitRel (𝔟 : FractionalIdeal (𝓞 F)⁰ F)),
      ∑' ν : NZ (𝔞 : FractionalIdeal (𝓞 F)⁰ F),
        if ∀ τ : Emb F, 0 < τ (ν.1 * c.out.1) then qTerm 𝔞 2 z (ν.1, c.out.1) else 0 := by
  set e := Equiv.ofBijective (toQ 𝔞 𝔟) ⟨toQ_injective 𝔞 𝔟, toQ_surjective 𝔞 𝔟⟩ with he
  have hS' : Summable (qClass 𝔞 𝔟 2 z ∘ e) := e.summable_iff.2 hS
  have h1 : ∑' c, qClass 𝔞 𝔟 2 z c = ∑' p, qClass 𝔞 𝔟 2 z (e p) := (e.tsum_eq _).symm
  have h2 : ∑' p, qClass 𝔞 𝔟 2 z (e p) = ∑' c, ∑' ν, qClass 𝔞 𝔟 2 z (e ⟨c, ν⟩) := hS'.tsum_sigma
  rw [h1, h2]
  refine tsum_congr fun c => ?_
  have h3 := tsum_subtype {ν : NZ (𝔞 : FractionalIdeal (𝓞 F)⁰ F) | ∀ τ : Emb F, 0 < τ (ν.1 * c.out.1)}
    (fun ν => qTerm 𝔞 2 z (ν.1, c.out.1))
  have h4 : ∀ ν : {ν : NZ (𝔞 : FractionalIdeal (𝓞 F)⁰ F) // ∀ τ : Emb F, 0 < τ (ν.1 * c.out.1)},
      qClass 𝔞 𝔟 2 z (e ⟨c, ν⟩) = qTerm 𝔞 2 z (ν.1.1, c.out.1) := fun ν => by
    rw [he]; exact qClass_mk 𝔞 𝔟 2 z _
  rw [tsum_congr h4]
  refine h3.trans (tsum_congr fun ν => ?_)
  rw [Set.indicator_apply]
  rfl
end GlobalTheory.HeckeTwoExp
