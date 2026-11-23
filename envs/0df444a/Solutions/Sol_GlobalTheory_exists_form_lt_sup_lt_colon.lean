-- Prove2me | solution 1 for GlobalTheory.exists_form_lt_sup_lt_colon
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:17:58.723141+00:00
-- url     : https://prove2.me/submissions/cbe2fae9-a4c3-4ba8-9861-1417a75cd60f

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsRingKrullDimQuotientMvPolynomialEqNat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_LeadingCoeffNonnegOfEventuallyEvalNat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_RingKrullDimQuotientAddOneOfMemMinimalPrimesSup

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
omit [Finite ι]
namespace GlobalTheory
theorem _root_.solution {I : Ideal (MvPolynomial ι k)}
    (hI : I.IsHomogeneous (homogeneousSubmodule ι k)) (h : I ≠ ⊤) (hp : ¬ I.IsPrime) :
    ∃ (d : ℕ) (f : MvPolynomial ι k), f.IsHomogeneous d ∧ I < I ⊔ Ideal.span {f} ∧
      I < Submodule.colon I {f} := by
  rw [hI.isPrime_iff] at hp
  push Not at hp
  obtain ⟨g, f, -, ⟨d, hf⟩, hgf, hg, hfI⟩ := hp h
  refine ⟨d, f, hf, lt_of_le_of_ne le_sup_left fun e => hfI ?_, lt_of_le_of_ne
    (fun x hx => Submodule.mem_colon_singleton.2 (I.mul_mem_right _ hx)) fun e => hg ?_⟩
  · rw [e]; exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self f)
  · rw [e]; exact Submodule.mem_colon_singleton.2 hgf
end GlobalTheory
