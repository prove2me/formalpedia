-- Prove2me | solution 1 for GlobalTheory.FinWeil.adjacent_selfDual_simple
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T15:47:13.250989+00:00
-- url     : https://prove2.me/submissions/765d1d8f-bc1b-43fb-97ba-2f4f893071f3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsHeisTrivial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PerfectPairingQuotients
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SumOpTransversal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_AdjacentSelfDualLatticesIndexSimple
import Theorems.Thm_GlobalTheory_FinWeil_IsHeis_iso
import Theorems.Thm_GlobalTheory_FinWeil_IsHeis_swap_eq_one
import Theorems.Thm_GlobalTheory_FinWeil_IsHeis_zero_right
import Theorems.Thm_GlobalTheory_FinWeil_perfect_pairing_quotients
import Theorems.Thm_GlobalTheory_FinWeil_sumOp_eq_sum_transversal

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
private lemma existsUnique_quotient_sub_smul_mem {R X : Type} [CommRing R] [AddCommGroup X]
    [Module R X] (A B : Submodule R X) (x : X) (P : Ideal R)
    (hxP : ∀ r : R, r • x ∈ A ↔ r ∈ P) (hBle : B ≤ (A ⊓ B) ⊔ Submodule.span R {x}) :
    ∀ b ∈ B, ∃! q : R ⧸ P, b - (Quotient.out q : R) • x ∈ A := by
  intro b hb
  obtain ⟨c, hc, y, hy, rfl⟩ := Submodule.mem_sup.1 (hBle hb)
  obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.1 hy
  refine ⟨Ideal.Quotient.mk P r, ?_, ?_⟩
  · have h1 : (r - Quotient.out (Ideal.Quotient.mk P r)) • x ∈ A := by
      rw [hxP, ← Ideal.Quotient.eq, Ideal.Quotient.mk_out]
    have h2 : c + r • x - Quotient.out (Ideal.Quotient.mk P r) • x =
        c + (r - Quotient.out (Ideal.Quotient.mk P r)) • x := by
      rw [sub_smul]; abel
    show c + r • x - Quotient.out (Ideal.Quotient.mk P r) • x ∈ A
    rw [h2]
    exact A.add_mem (Submodule.mem_inf.1 hc).1 h1
  · intro q hq
    have h2 : (r - Quotient.out q) • x ∈ A := by
      have h3 : (r - Quotient.out q) • x = (c + r • x - Quotient.out q • x) - c := by
        rw [sub_smul]; abel
      rw [h3]
      exact A.sub_mem hq (Submodule.mem_inf.1 hc).1
    rw [hxP, ← Ideal.Quotient.eq, Ideal.Quotient.mk_out] at h2
    exact h2.symm
open Classical in
open scoped BigOperators in
private lemma le_or_eq_of_inf_le_of_le_of_isMaximal {R X : Type} [CommRing R] [AddCommGroup X]
    [Module R X] (A B : Submodule R X) (x : X) (hx : x ∈ B) (P : Ideal R) (hP : P.IsMaximal)
    (hxP : ∀ r : R, r • x ∈ A ↔ r ∈ P) (hBle : B ≤ (A ⊓ B) ⊔ Submodule.span R {x})
    (T : Submodule R X) (h1 : A ⊓ B ≤ T) (h2 : T ≤ B) : T ≤ A ∨ T = B := by
  by_cases hTA : T ≤ A
  · exact Or.inl hTA
  right
  obtain ⟨t, htT, htA⟩ := Set.not_subset.1 hTA
  obtain ⟨c, hc, y, hy, rfl⟩ := Submodule.mem_sup.1 (hBle (h2 htT))
  obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.1 hy
  have hr : r ∉ P := fun hr => htA (A.add_mem (Submodule.mem_inf.1 hc).1 ((hxP r).2 hr))
  obtain ⟨s, i, hi, hsi⟩ := hP.exists_inv hr
  have hrx : r • x ∈ T := by
    have h3 := T.sub_mem htT (h1 hc)
    rwa [add_sub_cancel_left] at h3
  have hix : i • x ∈ T := h1 (Submodule.mem_inf.2 ⟨(hxP i).2 hi, B.smul_mem i hx⟩)
  have hxT : x ∈ T := by
    have h4 : x = s • r • x + i • x := by rw [smul_smul, ← add_smul, hsi, one_smul]
    rw [h4]
    exact T.add_mem (T.smul_mem s hrx) hix
  refine le_antisymm h2 (hBle.trans (sup_le h1 ?_))
  rw [Submodule.span_singleton_le_iff_mem]
  exact hxT
open Classical in
open scoped BigOperators in
private lemma toAddSubgroup_inf {R X : Type} [CommRing R] [AddCommGroup X] [Module R X]
    (A B : Submodule R X) : (A ⊓ B).toAddSubgroup = A.toAddSubgroup ⊓ B.toAddSubgroup := by
  ext; simp
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
theorem _root_.solution : ∀ {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}, _root_.GlobalTheory.FinWeil.IsHeis σ w γ W → ∀ (A B : Submodule R X), _root_.GlobalTheory.FinWeil.SelfDual γ A → _root_.GlobalTheory.FinWeil.SelfDual γ B → ∀ x ∈ B, ∀ P : Ideal R, P.IsMaximal → Finite (R ⧸ P) → (∀ r : R, r • x ∈ A ↔ r ∈ P) → B ≤ (A ⊓ B) ⊔ Submodule.span R {x} → _root_.GlobalTheory.FinWeil.idx A B = Nat.card (R ⧸ P) ∧ _root_.GlobalTheory.FinWeil.idx B A = Nat.card (R ⧸ P) ∧ (∀ b ∈ B, ∃! q : R ⧸ P, b - (Quotient.out q : R) • x ∈ A) ∧ (∀ T : Submodule R X, A ⊓ B ≤ T → T ≤ B → T ≤ A ∨ T = B) ∧ (∀ T : Submodule R X, A ⊓ B ≤ T → T ≤ A → T ≤ B ∨ T = A) := by
  intro R X M _ _ _ _ _ σ w γ W hW A B hA hB x hx P hP hfin hxP hBle
  have hA' : ∀ y, y ∈ A ↔ ∀ a ∈ A, γ y a = 1 := hA
  have hB' : ∀ y, y ∈ B ↔ ∀ b ∈ B, γ y b = 1 := hB
  have hrep := existsUnique_quotient_sub_smul_mem A B x P hxP hBle
  have hN : Nat.card (R ⧸ P) ≠ 0 := Nat.card_pos.ne'
  have hAB : _root_.GlobalTheory.FinWeil.idx A B = Nat.card (R ⧸ P) := by
    haveI := Fintype.ofFinite (R ⧸ P)
    rw [Nat.card_eq_fintype_card]
    exact (_root_.GlobalTheory.FinWeil.sumOp_eq_sum_transversal hW A B hB (0 : M) (fun a _ => map_zero (W a)) (R ⧸ P)
      (fun q => Quotient.out q • x) (fun q => B.smul_mem _ hx) hrep).2
  have hAB' : A.toAddSubgroup.relIndex B.toAddSubgroup = Nat.card (R ⧸ P) := hAB
  have hBA : B.toAddSubgroup.relIndex A.toAddSubgroup = Nat.card (R ⧸ P) := by
    have key := (_root_.GlobalTheory.FinWeil.perfect_pairing_quotients hW B.toAddSubgroup A.toAddSubgroup A.toAddSubgroup
      B.toAddSubgroup (fun a _ => by simpa only [Submodule.mem_toAddSubgroup] using hB' a)
      (fun t ht => by
        simp only [Submodule.mem_toAddSubgroup] at ht ⊢
        rw [hA' t]
        exact ⟨fun h a ha => hW.swap_eq_one (h a ha),
          fun h a ha => hW.swap_eq_one (h a ha)⟩)
      (by rw [hAB']; exact hN)).1
    rw [key, hAB']
  have hdich := le_or_eq_of_inf_le_of_le_of_isMaximal A B x hx P hP hxP hBle
  refine ⟨hAB, hBA, hrep, hdich, ?_⟩
  intro T h1 h2
  by_cases hTB : T ≤ B
  · exact Or.inl hTB
  right
  let T' : Submodule R X :=
    { carrier := {b | b ∈ B ∧ ∀ t ∈ T, γ t b = 1}
      add_mem' := fun {b b'} hb hb' => ⟨B.add_mem hb.1 hb'.1, fun t ht => by
        rw [hW.add_right, hb.2 t ht, hb'.2 t ht, one_mul]⟩
      zero_mem' := ⟨B.zero_mem, fun t _ => hW.zero_right t⟩
      smul_mem' := fun r b hb => ⟨B.smul_mem r hb.1, fun t ht => by
        have h3 := hW.adj (σ r) t b
        rw [hW.sg_sg] at h3
        rw [← h3]
        exact hb.2 _ (T.smul_mem _ ht)⟩ }
  have hmemT' : ∀ b, b ∈ T' ↔ b ∈ B ∧ ∀ t ∈ T, γ t b = 1 := fun b => Iff.rfl
  have hT'1 : A ⊓ B ≤ T' := fun c hc => (hmemT' c).2
    ⟨(Submodule.mem_inf.1 hc).2, fun t ht =>
      hW.iso hA (h2 ht) (Submodule.mem_inf.1 hc).1⟩
  have hT'2 : T' ≤ B := fun b hb => ((hmemT' b).1 hb).1
  rcases hdich T' hT'1 hT'2 with hle | heq
  · have hT'eq : T' = A ⊓ B := le_antisymm (le_inf hle hT'2) hT'1
    have hprod : (A ⊓ B).toAddSubgroup.relIndex T.toAddSubgroup *
        T.toAddSubgroup.relIndex A.toAddSubgroup = Nat.card (R ⧸ P) := by
      rw [AddSubgroup.relIndex_mul_relIndex (A ⊓ B).toAddSubgroup T.toAddSubgroup
        A.toAddSubgroup (fun y hy => h1 hy) (fun y hy => h2 hy),
        toAddSubgroup_inf, AddSubgroup.inf_relIndex_left, hBA]
    have hne : (A ⊓ B).toAddSubgroup.relIndex T.toAddSubgroup ≠ 0 := by
      intro h0; rw [h0, zero_mul] at hprod; exact hN hprod.symm
    have key := (_root_.GlobalTheory.FinWeil.perfect_pairing_quotients hW T'.toAddSubgroup B.toAddSubgroup
      (A ⊓ B).toAddSubgroup T.toAddSubgroup
      (fun b hb => by
        simp only [Submodule.mem_toAddSubgroup] at hb ⊢
        rw [hmemT']
        exact ⟨fun h t ht => hW.swap_eq_one (h.2 t ht),
          fun h => ⟨hb, fun t ht => hW.swap_eq_one (h t ht)⟩⟩)
      (fun t ht => by
        simp only [Submodule.mem_toAddSubgroup, Submodule.mem_inf] at ht ⊢
        rw [hB' t]
        exact ⟨fun h b hb => hW.swap_eq_one (h.2 b hb),
          fun h => ⟨h2 ht, fun b hb => hW.swap_eq_one (h b hb)⟩⟩)
      hne).1
    rw [hT'eq, toAddSubgroup_inf, AddSubgroup.inf_relIndex_right, hAB',
      ← toAddSubgroup_inf] at key
    rw [← key] at hprod
    have hone : T.toAddSubgroup.relIndex A.toAddSubgroup = 1 := by
      have h5 : Nat.card (R ⧸ P) * T.toAddSubgroup.relIndex A.toAddSubgroup =
          Nat.card (R ⧸ P) * 1 := by rw [hprod, mul_one]
      exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hN) h5
    have hAT := AddSubgroup.relIndex_eq_one.1 hone
    exact le_antisymm h2 (fun a ha => hAT ha)
  · exfalso
    apply hTB
    intro t ht
    rw [hB' t]
    intro b hb
    rw [← heq] at hb
    exact ((hmemT' b).1 hb).2 t ht
end _root_.GlobalTheory.FinWeil
end GlobalTheory.FinWeil
