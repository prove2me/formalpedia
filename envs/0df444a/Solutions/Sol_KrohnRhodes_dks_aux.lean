-- Prove2me | solution 1 for KrohnRhodes.dks_aux
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:10:24.371006+00:00
-- url     : https://prove2.me/submissions/5be851d5-ce09-4d2a-b8fb-d1a410f4799e

module
public import Definitions.Def_KrohnRhodes_Defs
public import Mathlib
public import Definitions.Def_KrohnRhodes_Foundations_WreathProduct
public import Definitions.Def_KrohnRhodes_Foundations_LocalDivisor
public import Definitions.Def_KrohnRhodes_Foundations_ConstantMaps
public import Definitions.Def_KrohnRhodes_Foundations_Division
public import Definitions.Def_KrohnRhodes_Foundations_MonoidWreathBridge
public import Definitions.Def_KrohnRhodes_Foundations_KrasnerKaloujnine
public import Definitions.Def_KrohnRhodes_FactorTower
public import Definitions.Def_KrohnRhodes_PrimeDecomposition
public import Theorems.Thm_KrohnRhodes_local_divisor_card_lt
public import Theorems.Thm_KrohnRhodes_local_act_injective
public import Theorems.Thm_KrohnRhodes_ext_act_injective
public import Theorems.Thm_KrohnRhodes_main_decomposition
public import Theorems.Thm_KrohnRhodes_submonoid_divides
public import Theorems.Thm_KrohnRhodes_exists_minimal_generating
public import Theorems.Thm_KrohnRhodes_exists_nonunit_generator
public import Theorems.Thm_KrohnRhodes_card_lt_of_proper
public import Theorems.Thm_KrohnRhodes_dks_aux_group
public import Theorems.Thm_KrohnRhodes_LocalDivisor_localDivides
public import Theorems.Thm_KrohnRhodes_MonoidDivides_trans
public import Theorems.Thm_KrohnRhodes_constEnd_mul
public import Theorems.Thm_KrohnRhodes_krasnerKaloujnine_hom_left
public import Theorems.Thm_divTowerWreath_nil_of_subsingleton
public import Theorems.Thm_divTowerWreath_wreathStep
attribute [local simp] KrohnRhodes.constEnd_mul
attribute [local simp] KrohnRhodes.krasnerKaloujnine_hom_left



set_option autoImplicit true
@[expose] public section
public section
set_option linter.unusedFintypeInType false
open KrohnRhodes
open Green
namespace KrohnRhodes
theorem _root_.solution (n : ℕ) :
    ∀ (Q : Type) [Fintype Q] (M : Type) [Monoid M] [Finite M]
      (act : M →* Function.End Q),
      Function.Injective act → Nat.card M ≤ n →
      ∃ factors : List KRFactor.{0}, DivTowerWreath ↥(closureMonoid act) factors ∧
        ∀ F ∈ factors, F.kind = KRFactorKind.simpleGroup →
          KrohnRhodes.MonoidDivides F.carrier M := by
  classical
  induction n with
  | zero =>
    -- `Nat.card M ≤ 0` is impossible: a finite monoid is nonempty, so its card is positive.
    intro Q _ M _ _ act _ hcard
    have : 0 < Nat.card M := Nat.card_pos
    omega
  | succ k IH =>
    intro Q _ M _ _ act hf hcard
    -- DEGENERATE CASE: `Q` subsingleton (covers `Q = ∅` and `|Q| = 1`). Then `End Q` is a
    -- subsingleton, hence so is the closure, and the empty tower works; the divisibility
    -- condition is vacuous.
    by_cases hQ : Subsingleton Q
    · have : Subsingleton (Function.End Q) := inferInstanceAs (Subsingleton (Q → Q))
      have : Subsingleton ↥(closureMonoid act) :=
        ⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩
      exact ⟨[], divTowerWreath_nil_of_subsingleton _, by simp⟩
    -- `Q` nontrivial, hence nonempty.
    have : Nontrivial Q := not_subsingleton_iff_nontrivial.mp hQ
    -- GROUP CASE: every element a unit.
    by_cases hU : ∀ m : M, IsUnit m
    · exact dks_aux_group act hU
    -- NON-GROUP CASE: some non-unit exists.
    push Not at hU
    -- Choose a minimal generating finset `A` and a non-unit `c ∈ A`; set
    -- `N := ⟨A \ {c}⟩`, proper by minimality.
    obtain ⟨A, hA, hmin⟩ := exists_minimal_generating M
    obtain ⟨c, hcA, hc⟩ := exists_nonunit_generator hA hU
    set N : Submonoid M := Submonoid.closure ((A.erase c : Finset M) : Set M) with hNdef
    have hNtop : N ≠ ⊤ := hmin c hcA
    -- Instances for the two recursive calls (`Fintype.ofFinite`).
    have : Finite (cQSet act c) :=
      inferInstanceAs (Finite {q : Q // ∃ x : Q, q = act c x})
    have : Fintype (cQSet act c) := Fintype.ofFinite _
    have : Fintype ↥N := Fintype.ofFinite _
    -- First recursive call, at `(cQ, M_c, localActHom)`: the decoration tower, with
    -- simple-group factors dividing `M_c`. Decrease: `|M_c| < |M| ≤ k + 1`.
    have hcardc : Nat.card (LocalDivisor M c) ≤ k :=
      Nat.lt_succ_iff.mp (lt_of_lt_of_le (local_divisor_card_lt hc) hcard)
    obtain ⟨factorsD, towD, hD⟩ := IH (cQSet act c) (LocalDivisor M c)
      (localActHom act c) (local_act_injective act c hf) hcardc
    -- Second recursive call, at `(Q ⊔ N, N, extAct)`: the base tower, with simple-group
    -- factors dividing `N`. Decrease: `|N| < |M| ≤ k + 1` since `N` is proper.
    have hcardN : Nat.card ↥N ≤ k :=
      Nat.lt_succ_iff.mp (lt_of_lt_of_le (card_lt_of_proper hNtop) hcard)
    obtain ⟨factorsB, towB, hB⟩ := IH (Q ⊕ ↥N) ↥N (extAct act N)
      (ext_act_injective act N) hcardN
    -- The main decomposition: the closure divides the wreath of the two recursive
    -- closures (at the containment `A \ {c} ⊆ N`).
    have hdec := main_decomposition act A hA c N Submonoid.subset_closure
    -- Assemble: factors := decoration tower ++ base tower.
    refine ⟨factorsD ++ factorsB,
      divTowerWreath_wreathStep factorsD hdec towD towB, ?_⟩
    -- Simple-group divisibility into `M`: through `M_c ÷ M` (`LocalDivisor.localDivides`)
    -- on the decoration side, and `N ÷ M` on the base side.
    intro F hF hk
    rcases List.mem_append.mp hF with hFD | hFB
    · exact (hD F hFD hk).trans LocalDivisor.localDivides
    · exact (hB F hFB hk).trans (submonoid_divides N)
end KrohnRhodes
