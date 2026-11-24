-- Prove2me | solution 1 for GlobalTheory.TripleIntertwiner.sum_refine
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:38:56.449068+00:00
-- url     : https://prove2.me/submissions/ccee6348-968b-49d1-a038-9133e985621b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GaussPowFourHom
import Theorems.Thm_GlobalTheory_TripleIntertwiner_rep_mem
import Theorems.Thm_GlobalTheory_TripleIntertwiner_rep_mk

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.TripleIntertwiner
open Classical
variable {V : Type*} [AddCommGroup V]
namespace GlobalTheory.TripleIntertwiner
theorem _root_.solution {F : Type} [AddCommMonoid F] {A₀ A B : AddSubgroup V} (hB : A₀ ≤ B)
    [Fintype (A ⧸ A₀.addSubgroupOf A)] [Fintype (A ⧸ B.addSubgroupOf A)] (g : V → F)
    (hg : ∀ x ∈ A, ∀ l ∈ A, l ∈ B → g (x + l) = g x) :
    ∃ k : ℕ, k * B.relIndex A = A₀.relIndex A ∧
      ∑ q : A ⧸ A₀.addSubgroupOf A, g (rep q) = k • ∑ q : A ⧸ B.addSubgroupOf A, g (rep q) := by
  have hle : A₀.addSubgroupOf A ≤ B.addSubgroupOf A := AddSubgroup.comap_mono hB
  let π : A ⧸ A₀.addSubgroupOf A →+ A ⧸ B.addSubgroupOf A :=
    QuotientAddGroup.map _ _ (AddMonoidHom.id A) hle
  have hπ : ∀ a : A, π (QuotientAddGroup.mk a) = QuotientAddGroup.mk a := fun a => rfl
  have hsurj : Function.Surjective π := by
    intro q
    exact ⟨QuotientAddGroup.mk (Quotient.out q), by rw [hπ, QuotientAddGroup.out_eq']⟩
  have hfib : ∀ q, (Finset.univ.filter fun x => π x = q).card = (Finset.univ.filter fun x => π x = 0).card :=
    fun q => AddMonoidHom.card_fiber_eq_of_mem_range π (hsurj q) ⟨0, map_zero _⟩
  have main : ∀ {G : Type} [AddCommMonoid G] (u : A ⧸ B.addSubgroupOf A → G),
      ∑ q, u (π q) = (Finset.univ.filter fun x => π x = 0).card • ∑ q, u q := by
    intro G _ u
    rw [← Finset.sum_fiberwise Finset.univ π, Finset.smul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Finset.sum_congr rfl (g := fun _ => u q) (fun x hx => by rw [(Finset.mem_filter.mp hx).2]),
      Finset.sum_const, hfib]
  refine ⟨(Finset.univ.filter fun x => π x = 0).card, ?_, ?_⟩
  · have := main (G := ℕ) (fun _ => 1)
    simp only [Finset.sum_const, smul_eq_mul, mul_one, Finset.card_univ] at this
    unfold AddSubgroup.relIndex AddSubgroup.index
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, this]
  · rw [← main (fun q => g (rep q))]
    refine Finset.sum_congr rfl fun q _ => ?_
    obtain ⟨l, h1, h2, h3⟩ := rep_mk (B := B) (Quotient.out q : A)
    rw [← hπ, QuotientAddGroup.out_eq'] at h3
    rw [h3, hg _ (rep_mem q) _ h1 h2]
end GlobalTheory.TripleIntertwiner
