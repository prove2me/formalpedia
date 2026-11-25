-- Prove2me | solution 1 for GlobalTheory.Avoid.exists_orderEmbedding_minor_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:29:44.502694+00:00
-- url     : https://prove2.me/submissions/0fbd8573-829f-4f8b-ba69-e2dac5b2bc76

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsBasisMapOfLiftBaseChangeSurjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Function
open scoped TensorProduct Pointwise
open GlobalTheory
open GlobalTheory.Avoid
open exteriorPower
open Module Function
open scoped TensorProduct Pointwise
open exteriorPower
namespace GlobalTheory.Avoid
namespace _root_.GlobalTheory.Avoid
theorem _root_.solution {K V ι : Type*} [Field K] [AddCommGroup V]
    [Module K V] [Finite ι] [LinearOrder ι] (c : ι → Dual K V)
    (hc : Submodule.span K (Set.range c) = ⊤) {r : ℕ} (x : ⋀[K]^r V) (hx : x ≠ 0) :
    ∃ J : Fin r ↪o ι, pairingDual K V r (ιMulti K r fun k => c (J k)) x ≠ 0 := by
  classical
  by_contra hne
  push_neg at hne
  have hall : ∀ φ : ⋀[K]^r (Dual K V), pairingDual K V r φ x = 0 := by
    intro φ
    have hφ : φ ∈ Submodule.span K (Set.range (ιMulti_family K r c)) := by
      rw [ιMulti_family_span_of_span K hc]; exact Submodule.mem_top
    induction hφ using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨s, rfl⟩ := hy
      exact hne (Set.powersetCard.ofFinEmbEquiv.symm s)
    | zero => simp
    | add y z _ _ hy hz => simp [hy, hz]
    | smul t y _ hy => simp [hy]
  let b := Basis.ofVectorSpace K V
  letI : LinearOrder (Basis.ofVectorSpaceIndex K V) := IsWellOrder.linearOrder WellOrderingRel
  let B := b.exteriorPower r
  have hcoord : ∀ s, B.coord s = ιMultiDual K r b s := fun s => B.ext fun t => by
    have hBt : B t = ιMulti_family K r b t := by simp [B, Module.Basis.exteriorPower]
    rw [Basis.coord_apply, B.repr_self, hBt]
    by_cases hst : s = t
    · subst hst
      rw [ιMultiDual_apply_diag, Finsupp.single_eq_same]
    · rw [ιMultiDual_apply_nondiag K r b s t hst, Finsupp.single_eq_of_ne hst]
  apply hx
  refine B.ext_elem fun s => ?_
  rw [map_zero, Finsupp.zero_apply, ← B.coord_apply, hcoord]
  exact hall _
end _root_.GlobalTheory.Avoid
end GlobalTheory.Avoid
