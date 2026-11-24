-- Prove2me | solution 1 for GlobalTheory.finrank_quotPiece_sup_add_colon
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:57:34.164535+00:00
-- url     : https://prove2.me/submissions/8e423129-b221-4d86-819b-bdbad03d7978

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsRingKrullDimQuotientMvPolynomialEqNat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_LeadingCoeffNonnegOfEventuallyEvalNat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_RingKrullDimQuotientAddOneOfMemMinimalPrimesSup
import Theorems.Thm_GlobalTheory_finrank_quotPiece_add


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Filter Module
open GlobalTheory
attribute [local instance] MvPolynomial.gradedAlgebra
open MvPolynomial DirectSum
variable {ι k : Type*} [Field k]
variable [Finite ι]
namespace GlobalTheory
theorem _root_.solution {I : Ideal (MvPolynomial ι k)}
    (hI : I.IsHomogeneous (homogeneousSubmodule ι k)) {f : MvPolynomial ι k} {d : ℕ}
    (hf : f.IsHomogeneous d) (n : ℕ) :
    finrank k (quotPiece (I ⊔ Ideal.span {f}) (n + d : ℕ)) +
      finrank k (quotPiece (Submodule.colon I {f}) n) = finrank k (quotPiece I (n + d : ℕ)) := by
  have h1 := finrank_quotPiece_add (I ⊔ Ideal.span {f}) (n + d)
  have h2 := finrank_quotPiece_add (Submodule.colon I {f}) n
  have h3 := finrank_quotPiece_add I (n + d)
  have e := GradedHilbert.finrank_sup_map_add_finrank_inf_comap (LinearMap.mulRight k f)
    (homogeneousSubmodule ι k n) (I.restrictScalars k ⊓ homogeneousSubmodule ι k (n + d))
  have a₁ : (I ⊔ Ideal.span {f}).restrictScalars k ⊓ homogeneousSubmodule ι k (n + d) =
      (I.restrictScalars k ⊓ homogeneousSubmodule ι k (n + d)) ⊔
        (homogeneousSubmodule ι k n).map (LinearMap.mulRight k f) := by
    apply le_antisymm
    · rintro m ⟨hm, hmn⟩
      obtain ⟨a, ha, _, hb, rfl⟩ := Submodule.mem_sup.1 hm
      obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 hb
      rw [← decompose_of_mem_same (homogeneousSubmodule ι k) hmn, decompose_add, DirectSum.add_apply,
        Submodule.coe_add, coe_decompose_mul_add_of_right_mem _ (j := d) hf]
      exact Submodule.add_mem_sup ⟨hI _ ha, SetLike.coe_mem _⟩ ⟨_, SetLike.coe_mem _, rfl⟩
    · refine sup_le (inf_le_inf_right _ fun m hm => Submodule.mem_sup_left hm) ?_
      rintro _ ⟨m, hm, rfl⟩
      exact ⟨Ideal.mem_sup_right (Ideal.mem_span_singleton'.2 ⟨m, rfl⟩),
        IsHomogeneous.mul hm hf⟩
  have a₂ : (Submodule.colon I {f}).restrictScalars k ⊓ homogeneousSubmodule ι k n =
      homogeneousSubmodule ι k n ⊓ (I.restrictScalars k ⊓
        homogeneousSubmodule ι k (n + d)).comap (LinearMap.mulRight k f) := by
    apply le_antisymm
    · rintro m ⟨hm, hmn⟩
      exact ⟨hmn, Submodule.mem_colon_singleton.1 hm, IsHomogeneous.mul hmn hf⟩
    · rintro m ⟨hm, hm', -⟩
      exact ⟨Submodule.mem_colon_singleton.2 hm', hm⟩
  rw [a₁] at h1
  rw [a₂] at h2
  omega
end GlobalTheory
