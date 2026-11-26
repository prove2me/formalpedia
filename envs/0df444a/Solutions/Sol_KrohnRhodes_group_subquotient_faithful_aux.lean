-- Prove2me | solution 1 for KrohnRhodes.group_subquotient_faithful_aux
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:06:59.610203+00:00
-- url     : https://prove2.me/submissions/5315de4d-c169-429a-8802-ae1b45d4a3db

module
public import Definitions.Def_KrohnRhodes_Defs
public import Definitions.Def_KrohnRhodes_Foundations_WreathProduct
public import Definitions.Def_KrohnRhodes_Foundations_LocalDivisor
public import Definitions.Def_KrohnRhodes_Foundations_KrasnerKaloujnine
public import Definitions.Def_KrohnRhodes_Foundations_Division
public import Mathlib
public import Definitions.Def_KrohnRhodes_Foundations_MonoidWreathBridge
public import Definitions.Def_KrohnRhodes_Foundations_Cayley
public import Definitions.Def_KrohnRhodes_Foundations_ConstantMaps
public import Definitions.Def_KrohnRhodes_FactorTower
public import Theorems.Thm_divTowerWreath_nil_of_subsingleton
public import Theorems.Thm_divTowerWreath_ofSimpleGroup
public import Theorems.Thm_divTowerWreath_wreathStep
public import Theorems.Thm_KrohnRhodes_monoidDivides_refl
public import Theorems.Thm_KrohnRhodes_monoidDivides_subgroup
public import Theorems.Thm_KrohnRhodes_quotientGroup_divides
public import Theorems.Thm_KrohnRhodes_subFactorsDivide_nil
public import Theorems.Thm_KrohnRhodes_subFactorsDivide_single
public import Theorems.Thm_KrohnRhodes_subFactorsDivide_of_divides
public import Theorems.Thm_KrohnRhodes_subFactorsDivide_append
public import Theorems.Thm_KrohnRhodes_group_sgdiv_via_normal


set_option autoImplicit true
@[expose] public section
public section
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option linter.style.show false
set_option linter.unusedSectionVars false
universe u
open Green
open KrohnRhodes
open Green
namespace KrohnRhodes
theorem _root_.solution (n : ℕ) :
    ∀ (G : Type u) [Group G] [Finite G], Nat.card G ≤ n →
      Nonempty (KRFactorTowerSub G) := by
  classical
  induction n with
  | zero =>
    intro G _ _ hcard
    have : 0 < Nat.card G := Nat.card_pos
    omega
  | succ k IH =>
    intro G _ _ hcard
    by_cases hss : Subsingleton G
    · exact ⟨⟨[], divTowerWreath_nil_of_subsingleton G, subFactorsDivide_nil G⟩⟩
    have hnontriv : Nontrivial G := not_subsingleton_iff_nontrivial.mp hss
    by_cases hsimple : IsSimpleGroup G
    · refine ⟨⟨[KRFactor.ofSimpleGroup G], divTowerWreath_ofSimpleGroup G, ?_⟩⟩
      exact subFactorsDivide_single _ (monoidDivides_refl (KRFactor.ofSimpleGroup G).carrier)
    · -- `G` not simple: peel a proper nontrivial normal subgroup.
      have hex : ∃ N : Subgroup G, N.Normal ∧ N ≠ ⊥ ∧ N ≠ ⊤ := by
        by_contra hne
        push Not at hne
        apply hsimple
        refine ⟨fun H hH => ?_⟩
        by_cases h1 : H = ⊥
        · exact Or.inl h1
        · exact Or.inr (hne H hH h1)
      obtain ⟨N, hNnormal, hNbot, hNtop⟩ := hex
      have : N.Normal := hNnormal
      obtain ⟨hcardN, hcardQ⟩ :
          Nat.card N < Nat.card G ∧ Nat.card (G ⧸ N) < Nat.card G := by
        have hmul : Nat.card (G ⧸ N) * Nat.card N = Nat.card G := by
          rw [← Subgroup.index_eq_card]; exact N.index_mul_card
        have hN_pos : 0 < Nat.card N := Nat.card_pos
        have hQ_pos : 0 < Nat.card (G ⧸ N) := Nat.card_pos
        have hN_ne_one : Nat.card N ≠ 1 := by
          intro hN; apply hNbot
          have : Subsingleton N := by
            rw [Nat.card_eq_one_iff_unique] at hN; exact hN.1
          exact Subgroup.eq_bot_of_subsingleton (H := N)
        have hQ_ne_one : Nat.card (G ⧸ N) ≠ 1 := by
          intro hQ; apply hNtop
          have hindex : N.index = 1 := by rw [Subgroup.index_eq_card]; exact hQ
          exact Subgroup.index_eq_one.mp hindex
        have hN_ge : 2 ≤ Nat.card N := by omega
        have hQ_ge : 2 ≤ Nat.card (G ⧸ N) := by omega
        exact ⟨by nlinarith [hmul, hN_pos, hQ_pos, hN_ge, hQ_ge],
               by nlinarith [hmul, hN_pos, hQ_pos, hN_ge, hQ_ge]⟩
      have hN_le : Nat.card (N : Type u) ≤ k := by omega
      have hQ_le : Nat.card (G ⧸ N) ≤ k := by omega
      obtain ⟨towN⟩ := IH (N : Type u) hN_le
      obtain ⟨towQ⟩ := IH (G ⧸ N) hQ_le
      have : Fintype (G ⧸ N) := Fintype.ofFinite _
      have hdiv : SgDiv G (WreathProduct (N : Type u) (G ⧸ N) (G ⧸ N)) :=
        KrohnRhodes.group_sgdiv_via_normal N
      refine ⟨⟨towN.factors ++ towQ.factors, ?_, ?_⟩⟩
      · exact divTowerWreath_wreathStep towN.factors hdiv towN.divides towQ.divides
      · apply subFactorsDivide_append
        · exact subFactorsDivide_of_divides (monoidDivides_subgroup N) towN.factorsDivide
        · exact subFactorsDivide_of_divides (quotientGroup_divides N) towQ.factorsDivide
end KrohnRhodes
