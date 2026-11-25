-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.sum_quotient_out_of_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:57:53.761807+00:00
-- url     : https://prove2.me/submissions/940f4b05-e388-4022-8e40-60ef88c33243

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaAverage

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Set
variable {α : Type*} [Group α] {W : Type*} [AddCommGroup W]
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution {s t : Subgroup α} (h : s ≤ t) [Fintype (α ⧸ s)] [Fintype (α ⧸ t)]
    [Fintype (t ⧸ s.subgroupOf t)] (φ : α → W) (hφ : ∀ a, ∀ b ∈ t, φ (a * b) = φ a) :
    ∑ q : α ⧸ s, φ (Quotient.out q) = (s.relIndex t) • ∑ q : α ⧸ t, φ (Quotient.out q) := by
  classical
  set e := Subgroup.quotientEquivProdOfLE h
  have key : ∀ a : α ⧸ s, φ (Quotient.out a) = φ (Quotient.out (e a).1) := by
    intro a
    have h1 : (e a).1 = (QuotientGroup.mk (Quotient.out a) : α ⧸ t) := by
      conv_lhs => rw [← Quotient.out_eq' a]
      rfl
    rw [h1]
    obtain ⟨b, hb⟩ := QuotientGroup.mk_out_eq_mul t (Quotient.out a)
    rw [hb, hφ _ _ b.2]
  rw [Fintype.sum_congr _ _ key, e.sum_comp (fun p => φ (Quotient.out p.1)), Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ]
  rw [Finset.smul_sum, Subgroup.relIndex, Subgroup.index, Nat.card_eq_fintype_card]
end GroundTheory.Automorphic.Parabolic
