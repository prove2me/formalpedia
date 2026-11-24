-- Prove2me | solution 1 for GlobalTheory.FinWeil.span_translates_vacua
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T15:47:05.475578+00:00
-- url     : https://prove2.me/submissions/382b5883-3334-4039-a701-ff1f00a35521

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PerfectPairingQuotients
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsHeisTrivial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SumOpTransversal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_HeisenbergIntertwiningSumsCompEqIndex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_NormalizedHeisenbergIntertwinerComp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIntertwinerHeisenbergCocycleOfFixedVector
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsWeilRepresentationHeisenberg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SpanHeisenbergTranslatesVacuumEqTop
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SpanHeisenbergTranslatesOfLatticeVacuaEqTop
import Theorems.Thm_GlobalTheory_FinWeil_IsHeis_comm
import Theorems.Thm_GlobalTheory_FinWeil_IsHeis_comp_of_mem
import Theorems.Thm_GlobalTheory_FinWeil_IsHeis_iso
import Theorems.Thm_GlobalTheory_FinWeil_IsHeis_ne_zero
import Theorems.Thm_GlobalTheory_FinWeil_IsHeis_neg_comp
import Theorems.Thm_GlobalTheory_FinWeil_IsHeis_neg_left
import Theorems.Thm_GlobalTheory_FinWeil_IsHeis_neg_right
import Theorems.Thm_GlobalTheory_FinWeil_IsHeis_swap
import Theorems.Thm_GlobalTheory_FinWeil_IsHeis_swap_eq_one
import Theorems.Thm_GlobalTheory_FinWeil_IsHeis_zero_left
import Theorems.Thm_GlobalTheory_FinWeil_perfect_pairing_quotients

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Classical GlobalTheory.FinWeil
open scoped BigOperators
namespace GlobalTheory.FinWeil
open Classical in
open scoped BigOperators in
private theorem sum_over_quotient_fixed_of_fixed {R X M : Type} [CommRing R] [AddCommGroup X]
    [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R} {γ : X → X → ℂ}
    {W : X → M →ₗ[ℂ] M} (hW : _root_.GlobalTheory.FinWeil.IsHeis σ w γ W) {A : Submodule R X}
    (hA : _root_.GlobalTheory.FinWeil.SelfDual γ A) (S : AddSubgroup X)
    [Fintype (↥A.toAddSubgroup ⧸ S.addSubgroupOf A.toAddSubgroup)]
    (hSA : ∀ s ∈ S, s ∈ A) (y : M) (hy : ∀ s ∈ S, W s y = y) :
    ∀ b ∈ A, W b (∑ q : ↥A.toAddSubgroup ⧸ S.addSubgroupOf A.toAddSubgroup,
      W ((Quotient.out q : ↥A.toAddSubgroup) : X) y) =
      ∑ q : ↥A.toAddSubgroup ⧸ S.addSubgroupOf A.toAddSubgroup,
        W ((Quotient.out q : ↥A.toAddSubgroup) : X) y := by
  intro b hb
  have hstep : ∀ x s : X, x ∈ A → s ∈ S → W (x + s) y = W x y := fun x s hx hs => by
    rw [← hW.comp_of_mem hA hx (hSA s hs), hy s hs]
  rw [map_sum]
  let b' : ↥A.toAddSubgroup := ⟨b, hb⟩
  refine Fintype.sum_equiv
    (Equiv.addLeft (QuotientAddGroup.mk b' : ↥A.toAddSubgroup ⧸ S.addSubgroupOf A.toAddSubgroup))
    _ _ (fun q => ?_)
  rw [hW.comp_of_mem hA hb (Quotient.out q).2 y]
  have hmem : -(b' + Quotient.out q) + Quotient.out ((QuotientAddGroup.mk b' :
      ↥A.toAddSubgroup ⧸ S.addSubgroupOf A.toAddSubgroup) + q) ∈ S.addSubgroupOf A.toAddSubgroup := by
    rw [← QuotientAddGroup.eq]
    simp [QuotientAddGroup.out_eq']
  simp only [Equiv.coe_addLeft]
  have hdec : ((Quotient.out ((QuotientAddGroup.mk b' :
      ↥A.toAddSubgroup ⧸ S.addSubgroupOf A.toAddSubgroup) + q) : ↥A.toAddSubgroup) : X) =
      (b + ((Quotient.out q : ↥A.toAddSubgroup) : X)) +
        ((-(b' + Quotient.out q) + Quotient.out ((QuotientAddGroup.mk b' :
          ↥A.toAddSubgroup ⧸ S.addSubgroupOf A.toAddSubgroup) + q) : ↥A.toAddSubgroup) : X) := by
    push_cast
    abel
  rw [hdec, hstep _ _ (A.add_mem hb (Quotient.out q).2) (AddSubgroup.mem_addSubgroupOf.mp hmem)]
end GlobalTheory.FinWeil
end

set_option autoImplicit false
open Classical GlobalTheory.FinWeil
open scoped BigOperators
open GlobalTheory GlobalTheory.FinWeil
open Classical
open scoped BigOperators
namespace GlobalTheory.FinWeil
namespace _root_.GlobalTheory.FinWeil
theorem _root_.solution : ∀ {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}, _root_.GlobalTheory.FinWeil.IsHeis σ w γ W → ∀ A : Submodule R X, _root_.GlobalTheory.FinWeil.SelfDual γ A → (∀ v : M, ∃ T : Submodule R X, _root_.GlobalTheory.FinWeil.idx A T ≠ 0 ∧ ∀ a ∈ A, (∀ t ∈ T, γ a t = 1) → W a v = v) → Submodule.span ℂ {m : M | ∃ x e, _root_.GlobalTheory.FinWeil.Fixes W A e ∧ m = W x e} = ⊤ := by
  intro R X M _ _ _ _ _ σ w γ W hW A hA hloc
  rw [eq_top_iff]
  rintro v -
  obtain ⟨T, hT, hfix⟩ := hloc v
  have hAdual : ∀ x, x ∈ A ↔ ∀ a ∈ A, γ x a = 1 := by
    unfold _root_.GlobalTheory.FinWeil.SelfDual at hA
    exact hA
  unfold _root_.GlobalTheory.FinWeil.idx at hT
  let S : AddSubgroup X :=
    { carrier := {a | a ∈ A ∧ ∀ t ∈ T, γ a t = 1}
      add_mem' := fun {a b} ha hb => ⟨A.add_mem ha.1 hb.1, fun t ht => by
        rw [hW.add_left, ha.2 t ht, hb.2 t ht, one_mul]⟩
      zero_mem' := ⟨A.zero_mem, fun t _ => hW.zero_left t⟩
      neg_mem' := fun {a} ha => ⟨A.neg_mem ha.1, fun t ht => by
        rw [hW.neg_left, ha.2 t ht, inv_one]⟩ }
  have hSmem : ∀ a, a ∈ S ↔ a ∈ A ∧ ∀ t ∈ T, γ a t = 1 := fun a => Iff.rfl
  let T₀ : AddSubgroup X := A.toAddSubgroup ⊓ T.toAddSubgroup
  have hS : ∀ a ∈ A.toAddSubgroup, a ∈ S ↔ ∀ t ∈ T.toAddSubgroup, γ a t = 1 :=
    fun a ha => ⟨fun h => h.2, fun h => ⟨ha, h⟩⟩
  have hT₀ : ∀ t ∈ T.toAddSubgroup, t ∈ T₀ ↔ ∀ a ∈ A.toAddSubgroup, γ a t = 1 := by
    intro t ht
    constructor
    · rintro ⟨htA, -⟩ a ha
      exact hW.iso hA ha htA
    · intro h
      exact ⟨(hAdual t).2 fun a ha => hW.swap_eq_one (h a ha), ht⟩
  have hidx : T₀.relIndex T.toAddSubgroup ≠ 0 := by
    rwa [AddSubgroup.inf_relIndex_right]
  obtain ⟨hKN, -, -⟩ := _root_.GlobalTheory.FinWeil.perfect_pairing_quotients hW S A.toAddSubgroup T₀ T.toAddSubgroup hS hT₀ hidx
  have hK : S.relIndex A.toAddSubgroup ≠ 0 := hKN ▸ hidx
  obtain ⟨-, -, horth⟩ := _root_.GlobalTheory.FinWeil.perfect_pairing_quotients hW T₀ T.toAddSubgroup S A.toAddSubgroup
    (fun t ht => by
      rw [hT₀ t ht]
      exact ⟨fun h a ha => hW.swap_eq_one (h a ha),
        fun h a ha => hW.swap_eq_one (h a ha)⟩)
    (fun a ha => by
      rw [hS a ha]
      exact ⟨fun h t ht => hW.swap_eq_one (h t ht),
        fun h t ht => hW.swap_eq_one (h t ht)⟩) hK
  haveI : (S.addSubgroupOf A.toAddSubgroup).FiniteIndex := ⟨hK⟩
  haveI : (T₀.addSubgroupOf T.toAddSubgroup).FiniteIndex := ⟨hidx⟩
  letI := Fintype.ofFinite (↥A.toAddSubgroup ⧸ S.addSubgroupOf A.toAddSubgroup)
  letI := Fintype.ofFinite (↥T.toAddSubgroup ⧸ T₀.addSubgroupOf T.toAddSubgroup)
  have hz : ∀ t ∈ T, (∑ q : ↥A.toAddSubgroup ⧸ S.addSubgroupOf A.toAddSubgroup,
      γ ((Quotient.out q : ↥A.toAddSubgroup) : X) t • W ((Quotient.out q : ↥A.toAddSubgroup) : X) v)
      ∈ Submodule.span ℂ {m : M | ∃ x e, _root_.GlobalTheory.FinWeil.Fixes W A e ∧ m = W x e} := by
    intro t ht
    have hy : ∀ s ∈ S, W s (W t v) = W t v := by
      intro s hs
      rw [hW.comm, hs.2 t ht, one_smul, hfix s hs.1 hs.2]
    have hu := sum_over_quotient_fixed_of_fixed hW hA S (fun s hs => hs.1) (W t v) hy
    set c := γ (w • -t) t with hc_def
    have hc : c ≠ 0 := hW.ne_zero _ _
    have key : (∑ q : ↥A.toAddSubgroup ⧸ S.addSubgroupOf A.toAddSubgroup,
        γ ((Quotient.out q : ↥A.toAddSubgroup) : X) t •
          W ((Quotient.out q : ↥A.toAddSubgroup) : X) v) =
        W (-t) (c⁻¹ • ∑ q : ↥A.toAddSubgroup ⧸ S.addSubgroupOf A.toAddSubgroup,
          W ((Quotient.out q : ↥A.toAddSubgroup) : X) (W t v)) := by
      symm
      rw [map_smul, map_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [hW.comm _ t v, map_smul, hW.neg_comp,
        ← hc_def, smul_smul, smul_smul, mul_comm c⁻¹, mul_assoc, inv_mul_cancel₀ hc, mul_one]
    rw [key]
    refine Submodule.subset_span ⟨-t, c⁻¹ • ∑ q : ↥A.toAddSubgroup ⧸ S.addSubgroupOf A.toAddSubgroup,
          W ((Quotient.out q : ↥A.toAddSubgroup) : X) (W t v), ?_, rfl⟩
    unfold _root_.GlobalTheory.FinWeil.Fixes
    intro a ha
    rw [map_smul, hu a ha]
  have horth' : ∀ q : ↥A.toAddSubgroup ⧸ S.addSubgroupOf A.toAddSubgroup,
      ∑ p : ↥T.toAddSubgroup ⧸ T₀.addSubgroupOf T.toAddSubgroup,
        γ ((Quotient.out p : ↥T.toAddSubgroup) : X) ((Quotient.out q : ↥A.toAddSubgroup) : X) =
      if ((Quotient.out q : ↥A.toAddSubgroup) : X) ∈ S then
        ((T₀.relIndex T.toAddSubgroup : ℕ) : ℂ) else 0 := fun q => by
    rw [← finsum_eq_sum_of_fintype]
    exact horth _ (Quotient.out q).2
  have hsum : (∑ p : ↥T.toAddSubgroup ⧸ T₀.addSubgroupOf T.toAddSubgroup,
      ∑ q : ↥A.toAddSubgroup ⧸ S.addSubgroupOf A.toAddSubgroup,
        γ ((Quotient.out q : ↥A.toAddSubgroup) : X) (-((Quotient.out p : ↥T.toAddSubgroup) : X)) •
          W ((Quotient.out q : ↥A.toAddSubgroup) : X) v) =
      ((T₀.relIndex T.toAddSubgroup : ℕ) : ℂ) • v := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_smul, hW.neg_right, ← hW.swap, horth']
    rw [Finset.sum_eq_single 0]
    · have h0 : ((Quotient.out (0 : ↥A.toAddSubgroup ⧸ S.addSubgroupOf A.toAddSubgroup) :
          ↥A.toAddSubgroup) : X) ∈ S :=
        AddSubgroup.mem_addSubgroupOf.mp
          ((QuotientAddGroup.eq_zero_iff _).mp (QuotientAddGroup.out_eq' 0))
      rw [if_pos h0, hfix _ h0.1 h0.2]
    · intro q _ hq
      have hqS : ¬ (((Quotient.out q : ↥A.toAddSubgroup) : X) ∈ S) := fun h => hq (by
        rw [← QuotientAddGroup.out_eq' q, QuotientAddGroup.eq_zero_iff]
        exact AddSubgroup.mem_addSubgroupOf.mpr h)
      rw [if_neg hqS, zero_smul]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hNne : ((T₀.relIndex T.toAddSubgroup : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hidx
  have hv : v = (((T₀.relIndex T.toAddSubgroup : ℕ) : ℂ))⁻¹ •
      ∑ p : ↥T.toAddSubgroup ⧸ T₀.addSubgroupOf T.toAddSubgroup,
        ∑ q : ↥A.toAddSubgroup ⧸ S.addSubgroupOf A.toAddSubgroup,
          γ ((Quotient.out q : ↥A.toAddSubgroup) : X) (-((Quotient.out p : ↥T.toAddSubgroup) : X)) •
            W ((Quotient.out q : ↥A.toAddSubgroup) : X) v := by
    rw [hsum, smul_smul, inv_mul_cancel₀ hNne, one_smul]
  rw [hv]
  exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun p _ =>
    hz _ (T.neg_mem (Quotient.out p).2))
end _root_.GlobalTheory.FinWeil
end GlobalTheory.FinWeil
