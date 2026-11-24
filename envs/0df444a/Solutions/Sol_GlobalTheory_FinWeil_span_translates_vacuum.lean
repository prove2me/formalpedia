-- Prove2me | solution 1 for GlobalTheory.FinWeil.span_translates_vacuum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T15:47:07.268699+00:00
-- url     : https://prove2.me/submissions/bd73808b-cbff-40d9-862a-b7a0c6f69dda

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsHeisTrivial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PerfectPairingQuotients
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SumOpTransversal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SpanHeisenbergTranslatesVacuumEqTop
import Theorems.Thm_GlobalTheory_FinWeil_IsHeis_comm
import Theorems.Thm_GlobalTheory_FinWeil_IsHeis_iso
import Theorems.Thm_GlobalTheory_FinWeil_IsHeis_ne_zero
import Theorems.Thm_GlobalTheory_FinWeil_IsHeis_swap_eq_one
import Theorems.Thm_GlobalTheory_FinWeil_IsHeis_zero_left
import Theorems.Thm_GlobalTheory_FinWeil_perfect_pairing_quotients
import Theorems.Thm_GlobalTheory_FinWeil_sumOp_transversal


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Classical GlobalTheory.FinWeil
open scoped BigOperators
open GlobalTheory GlobalTheory.FinWeil
namespace GlobalTheory.FinWeil
theorem _root_.solution : ∀ {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}, IsHeis σ w γ W → ∀ A : Submodule R X, SelfDual γ A → ∀ e : M, (∀ v, Fixes W A v → ∃ c : ℂ, v = c • e) → (∀ v : M, ∃ T : Submodule R X, idx A T ≠ 0 ∧ ∀ a ∈ A, (∀ t ∈ T, γ a t = 1) → W a v = v) → Submodule.span ℂ (Set.range fun x => W x e) = ⊤ := by
  intro R X M _ _ _ _ _ σ w γ W h A hA e he hsm
  rw [eq_top_iff]
  intro v _
  obtain ⟨T, hT, hv⟩ := hsm v
  let S : Submodule R X :=
    { carrier := {a | a ∈ A ∧ ∀ t ∈ T, γ a t = 1}
      add_mem' := fun {a b} ha hb => ⟨A.add_mem ha.1 hb.1, fun t ht => by
        rw [h.add_left, ha.2 t ht, hb.2 t ht, mul_one]⟩
      zero_mem' := ⟨A.zero_mem, fun t _ => h.zero_left t⟩
      smul_mem' := fun r a ha => ⟨A.smul_mem r ha.1, fun t ht => by
        rw [h.adj]; exact ha.2 _ (T.smul_mem _ ht)⟩ }
  have hSm : ∀ a, a ∈ S ↔ a ∈ A ∧ ∀ t ∈ T, γ a t = 1 := fun a => Iff.rfl
  have hSv : Fixes W S v := fun a ha => hv a ha.1 ha.2
  have hSt : ∀ t ∈ T, Fixes W S (W (-t) v) := by
    intro t ht a ha
    rw [h.comm, ha.2 _ (T.neg_mem ht), one_smul, hSv a ha]
  obtain ⟨h1, -, -⟩ := perfect_pairing_quotients h S.toAddSubgroup A.toAddSubgroup
    A.toAddSubgroup T.toAddSubgroup
    (fun a ha => ⟨fun hs => hs.2, fun hs => ⟨ha, hs⟩⟩)
    (fun t _ => ⟨fun ht a ha => h.iso hA ha ht,
      fun ht => (hA t).2 fun a ha => h.swap_eq_one (ht a ha)⟩) hT
  have hn : idx S A ≠ 0 := by
    unfold idx
    rw [h1]
    exact hT
  obtain ⟨-, -, h2⟩ := perfect_pairing_quotients h A.toAddSubgroup T.toAddSubgroup
    S.toAddSubgroup A.toAddSubgroup
    (fun t _ => hA t)
    (fun a ha => ⟨fun hs t ht => h.swap_eq_one (hs.2 t ht),
      fun hs => ⟨ha, fun t ht => h.swap_eq_one (hs t ht)⟩⟩) hn
  obtain ⟨t1, t2, -⟩ := sumOp_transversal h S A hA
  obtain ⟨⟨m, f, hf, hu⟩, hfix, -⟩ := t2 hn
  have hg : ∀ t ∈ T, ∑ i, γ t (f i) • W (f i) v ∈ Submodule.span ℂ (Set.range fun x => W x e) := by
    intro t ht
    obtain ⟨c, hc⟩ := he _ (hfix _ (hSt t ht))
    rw [(t1 _ (hSt t ht) _ f hf hu).1] at hc
    have h3 := congrArg (W t) hc
    rw [map_sum, map_smul] at h3
    have h4 : ∀ i, W t (W (f i) (W (-t) v)) = γ (w • t) (-t) • (γ t (f i) • W (f i) v) := by
      intro i
      rw [h.comm, h.comp t (-t), add_neg_cancel, h.zero, map_smul, smul_comm]
    rw [Finset.sum_congr rfl fun i _ => h4 i, ← Finset.smul_sum] at h3
    rw [← Submodule.smul_mem_iff _ (h.ne_zero (w • t) (-t)), h3]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t, rfl⟩)
  haveI : Finite (T.toAddSubgroup ⧸ A.toAddSubgroup.addSubgroupOf T.toAddSubgroup) :=
    Nat.finite_of_card_ne_zero hT
  letI := Fintype.ofFinite (T.toAddSubgroup ⧸ A.toAddSubgroup.addSubgroupOf T.toAddSubgroup)
  have h5 := Submodule.sum_mem (Submodule.span ℂ (Set.range fun x => W x e))
    (t := (Finset.univ : Finset
      (T.toAddSubgroup ⧸ A.toAddSubgroup.addSubgroupOf T.toAddSubgroup)))
    (fun q _ => hg _ (Quotient.out q : T.toAddSubgroup).2)
  rw [Finset.sum_comm] at h5
  obtain ⟨i₀, hi₀, hi⟩ := hu 0 A.zero_mem
  simp only [zero_sub, neg_mem_iff] at hi₀ hi
  have h6 : ∀ i, ∑ q : T.toAddSubgroup ⧸ A.toAddSubgroup.addSubgroupOf T.toAddSubgroup,
      γ ((Quotient.out q : T.toAddSubgroup) : X) (f i) • W (f i) v
      = if i = i₀ then (idx A T : ℂ) • v else 0 := by
    intro i
    rw [← Finset.sum_smul, ← finsum_eq_sum_of_fintype, h2 _ (hf i)]
    by_cases hii : i = i₀
    · subst hii
      rw [if_pos rfl, if_pos (show f i ∈ S.toAddSubgroup from hi₀), hSv _ hi₀]
      rfl
    · rw [if_neg hii, if_neg (fun hh : f i ∈ S.toAddSubgroup => hii (hi i hh)), zero_smul]
  rw [Finset.sum_congr rfl fun i _ => h6 i, Finset.sum_ite_eq', if_pos (Finset.mem_univ _)] at h5
  exact (Submodule.smul_mem_iff _ (Nat.cast_ne_zero.2 hT)).1 h5
end GlobalTheory.FinWeil
