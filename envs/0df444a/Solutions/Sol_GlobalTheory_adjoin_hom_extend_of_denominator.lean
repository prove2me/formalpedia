-- Prove2me | solution 1 for GlobalTheory.adjoin_hom_extend_of_denominator
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:21:11.847294+00:00
-- url     : https://prove2.me/submissions/5c43783b-4aa5-4c51-b4a8-b72a06349488

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NonemptyAlgHomAdjoin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AdjoinHomExtendOfDenominator
import Theorems.Thm_GlobalTheory_AdjoinAlgebraHomNonempty_nonempty_algHom_adjoin


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (k F Ω : Type) [Field k] [Field F] [Algebra k F] [Field Ω]
    [Algebra k Ω] (S : Subalgebra k F) (ψ : S →ₐ[k] Ω) (h : S) (hψ : ψ h ≠ 0) (T : Set F)
    (hT : ∀ x ∈ T, (h : F) * x ∈ S) : Nonempty (Algebra.adjoin k T →ₐ[k] Ω) := by
  first
  | exact @_root_.GlobalTheory.AdjoinAlgebraHomNonempty.nonempty_algHom_adjoin
  | exact _root_.GlobalTheory.AdjoinAlgebraHomNonempty.nonempty_algHom_adjoin
  | (apply _root_.GlobalTheory.AdjoinAlgebraHomNonempty.nonempty_algHom_adjoin <;> assumption)
  | (intros; apply _root_.GlobalTheory.AdjoinAlgebraHomNonempty.nonempty_algHom_adjoin <;> assumption)
  | (intros; apply @_root_.GlobalTheory.AdjoinAlgebraHomNonempty.nonempty_algHom_adjoin <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.AdjoinAlgebraHomNonempty.nonempty_algHom_adjoin ..)
end GlobalTheory
