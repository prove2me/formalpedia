-- Prove2me | solution 1 for GlobalTheory.TateSeq.exists_div
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:41:21.545557+00:00
-- url     : https://prove2.me/submissions/55f2f1f4-2ab1-4369-9823-7ba21aa2122b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsBasisAdaptedLatticeSubspace
import Theorems.Thm_GlobalTheory_TateSeq_mem_tors

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.TateSeq
variable {M : Type} [AddCommGroup M]
namespace GlobalTheory.TateSeq
theorem _root_.solution (l r : ℕ) [Fact l.Prime]
    (h : ∀ n, Nat.card {x : M // l ^ n • x = 0} = l ^ (r * n)) (n : ℕ) (y : M)
    (hy : l ^ n • y = 0) : ∃ x : M, l • x = y := by
  have hl : 0 < l := (Fact.out : l.Prime).pos
  have hc : ∀ n, Nat.card (tors M (l ^ n)) = l ^ (r * n) := h
  let f : tors M (l ^ (n + 1)) →+ tors M (l ^ n) :=
    { toFun := fun x => ⟨l • x.1, by
        rw [mem_tors, ← mul_smul, ← pow_succ]; exact x.2⟩
      map_zero' := by ext; simp
      map_add' := by intro a b; ext; simp }
  have hker : Nat.card f.ker = l ^ r := by
    have h1 := hc 1
    rw [mul_one, pow_one] at h1
    rw [← h1]
    refine Nat.card_congr
      { toFun := fun x => ⟨x.1.1, by
          exact congrArg Subtype.val x.2⟩
        invFun := fun x => ⟨⟨x.1, by
          have := x.2
          rw [mem_tors] at this
          rw [mem_tors, pow_succ, mul_smul, this, smul_zero]⟩, by
          have := x.2
          rw [mem_tors] at this
          exact Subtype.ext this⟩
        left_inv := fun x => rfl
        right_inv := fun x => rfl }
  have hr : Nat.card f.range = l ^ (r * n) := by
    have h1 := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup f.ker
    rw [Nat.card_congr (QuotientAddGroup.quotientKerEquivRange f).toEquiv, hker, hc,
      mul_add, mul_one, pow_add] at h1
    exact (Nat.eq_of_mul_eq_mul_right (pow_pos hl r) h1).symm
  haveI : Finite (tors M (l ^ n)) :=
    Nat.finite_of_card_ne_zero (by rw [hc]; positivity)
  have htop : f.range = ⊤ := AddSubgroup.eq_top_of_card_eq _ (by rw [hr, hc])
  have : (⟨y, hy⟩ : tors M (l ^ n)) ∈ f.range := by rw [htop]; trivial
  obtain ⟨x, hx⟩ := this
  exact ⟨x.1, congrArg Subtype.val hx⟩
end GlobalTheory.TateSeq
