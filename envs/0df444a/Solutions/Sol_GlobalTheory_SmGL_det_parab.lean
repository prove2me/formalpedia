-- Prove2me | solution 1 for GlobalTheory.SmGL.det_parab
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:44:41.140241+00:00
-- url     : https://prove2.me/submissions/a11accc3-0376-4f41-9c41-f73303690545

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_LeviEmbMemNormalizerLower
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace GlobalTheory.SmGL
section Blocks
open Matrix
variable (R : Type) [CommRing R] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]
variable {R}
variable (R)
open Matrix in
variable (R : Type) [CommRing R] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] in
variable {R} in
variable (R) in
omit [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] in
private lemma bijective_blockPosition_of_equiv_sigma (e : (Σ a, m a) ≃ n) (a : α) :
    Function.Bijective fun i : m a =>
      (⟨e ⟨a, i⟩, _root_.GlobalTheory.SmGL.blk_apply e a i⟩ :
        {k : n // _root_.GlobalTheory.SmGL.blk e k = a}) := by
  constructor
  · intro i j hij
    have h := e.injective (Subtype.ext_iff.1 hij)
    simpa using h
  · rintro ⟨k, hk⟩
    obtain ⟨⟨b, i⟩, rfl⟩ := e.surjective k
    simp only [_root_.GlobalTheory.SmGL.blk_apply] at hk
    subst hk
    exact ⟨i, rfl⟩
variable {R}
variable (R)
variable {a b : Type}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
end Blocks
end GlobalTheory.SmGL
end
end

set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.SmGL
open Matrix
variable (R : Type) [CommRing R] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]
variable {R}
variable (R)
open Matrix
variable (R : Type) [CommRing R] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]
variable {R}
variable (R)
namespace GlobalTheory.SmGL
namespace _root_.GlobalTheory.SmGL
theorem _root_.solution (e : (Σ a, m a) ≃ n)
    (p : _root_.GlobalTheory.SmGL.parab R e) :
    GeneralLinearGroup.det (p : GL n R) =
      ∏ a, GeneralLinearGroup.det (_root_.GlobalTheory.SmGL.leviProj R e p a) := by
  have hp : ((p : GL n R) : Matrix n n R).BlockTriangular (_root_.GlobalTheory.SmGL.blk e) := p.2
  ext
  rw [GeneralLinearGroup.val_det_apply, Units.coe_prod, hp.det_fintype]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [GeneralLinearGroup.val_det_apply,
    ← Matrix.det_submatrix_equiv_self (Equiv.ofBijective _ (bijective_blockPosition_of_equiv_sigma e a))]
  rfl
end _root_.GlobalTheory.SmGL
end GlobalTheory.SmGL
