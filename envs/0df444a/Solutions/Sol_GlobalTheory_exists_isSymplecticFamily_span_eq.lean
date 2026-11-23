-- Prove2me | solution 1 for GlobalTheory.exists_isSymplecticFamily_span_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:35:34.950188+00:00
-- url     : https://prove2.me/submissions/defd5205-aac7-490c-9e31-6c5de01cf879

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DualRestrictSurjectiveOfIsTorsionFreeQuotient
import Theorems.Thm_GlobalTheory_exists_pair_dvd_of_bilinForm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Function
open GlobalTheory
variable {R M : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [AddCommGroup M]
  [Module R M]
namespace GlobalTheory
theorem _root_.solution [Module.Free R M] [Module.Finite R M]
    {B : LinearMap.BilinForm R M} (hB : B.IsAlt) (N : Submodule R M)
    (hN : ∀ x ∈ N, (∀ y ∈ N, B x y = 0) → x = 0) :
    ∃ (g : ℕ) (e f : Fin g → M) (d : Fin g → R), IsSymplecticFamily B e f d ∧ (∀ i, d i ≠ 0) ∧
      (∀ i j, i ≤ j → d i ∣ d j) ∧ Submodule.span R (Set.range (Sum.elim e f)) = N := by
  revert hN
  refine Submodule.inductionOnRank (Module.Free.chooseBasis R M) (fun N => (∀ x ∈ N, (∀ y ∈ N, B x y = 0) → x = 0) →
    ∃ (g : ℕ) (e f : Fin g → M) (d : Fin g → R), IsSymplecticFamily B e f d ∧ (∀ i, d i ≠ 0) ∧
      (∀ i j, i ≤ j → d i ∣ d j) ∧ Submodule.span R (Set.range (Sum.elim e f)) = N) ?_ N
  intro N ih hN
  by_cases hbot : N = ⊥
  · refine ⟨0, Fin.elim0, Fin.elim0, Fin.elim0, ⟨fun i => i.elim0, fun i => i.elim0,
      fun i => i.elim0, fun i => i.elim0⟩, fun i => i.elim0, fun i => i.elim0, ?_⟩
    rw [hbot, Submodule.span_eq_bot]
    rintro _ ⟨i | i, rfl⟩ <;> exact i.elim0
  obtain ⟨e, he, f, hf, h₁, h₂, h₃⟩ := exists_pair_dvd_of_bilinForm B N
  have hd : B e f ≠ 0 := by
    intro h0
    apply hbot
    rw [Submodule.eq_bot_iff]
    intro x hx
    refine hN x hx fun y hy => ?_
    rw [h0] at h₁ h₂ h₃
    exact zero_dvd_iff.1 (h₃ x hx y hy (zero_dvd_iff.1 (h₁ y hy)) (zero_dvd_iff.1 (h₂ x hx)))
  let N' : Submodule R M := N ⊓ (LinearMap.ker (B e) ⊓ LinearMap.ker (B f))
  have hmem : ∀ y, y ∈ N' ↔ y ∈ N ∧ B e y = 0 ∧ B f y = 0 := fun y => Iff.rfl
  have hdec : ∀ y ∈ N, ∃ a b : R, ∃ y' ∈ N', y = a • e + b • f + y' := by
    intro y hy
    obtain ⟨b, hb⟩ := h₁ y hy
    obtain ⟨a, ha⟩ := h₂ y hy
    refine ⟨a, b, y - a • e - b • f, (hmem _).2 ⟨N.sub_mem (N.sub_mem hy (N.smul_mem _ he))
      (N.smul_mem _ hf), ?_, ?_⟩, by abel⟩
    · simp [hb, hB.self_eq_zero, mul_comm]
    · simp [← hB.neg_eq y f, ← hB.neg_eq e f, ha, hB.self_eq_zero, mul_comm]
  obtain ⟨g, e', f', d', hs, hd', hdvd, hspan⟩ := ih N' inf_le_left f hf (by
    intro c y hy hc
    have := congrArg (B e) hc
    simpa [((hmem y).1 hy).2.1, hd] using this) (by
    intro x hx hx0
    refine hN x hx.1 fun y hy => ?_
    obtain ⟨a, b, y', hy', rfl⟩ := hdec y hy
    simp [hx0 y' hy', hB.eq_iff.1 ((hmem x).1 hx).2.1, hB.eq_iff.1 ((hmem x).1 hx).2.2])
  have he' : ∀ i, e' i ∈ N' := fun i => hspan ▸ Submodule.subset_span ⟨Sum.inl i, rfl⟩
  have hf' : ∀ i, f' i ∈ N' := fun i => hspan ▸ Submodule.subset_span ⟨Sum.inr i, rfl⟩
  refine ⟨g + 1, Fin.cons e e', Fin.cons f f', Fin.cons (B e f) d', ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro i j
    cases i using Fin.cases <;> cases j using Fin.cases
    · simp [hB.self_eq_zero]
    · simp [((hmem _).1 (he' _)).2.1]
    · simp [hB.eq_iff.1 ((hmem _).1 (he' _)).2.1]
    · simp [hs.left_left]
  · intro i j
    cases i using Fin.cases <;> cases j using Fin.cases
    · simp [hB.self_eq_zero]
    · simp [((hmem _).1 (hf' _)).2.2]
    · simp [hB.eq_iff.1 ((hmem _).1 (hf' _)).2.2]
    · simp [hs.right_right]
  · intro i
    cases i using Fin.cases
    · simp
    · simp [hs.left_right_self]
  · intro i j hij
    cases i using Fin.cases <;> cases j using Fin.cases
    · exact absurd rfl hij
    · simp [((hmem _).1 (hf' _)).2.1]
    · simp [hB.eq_iff.1 ((hmem _).1 (he' _)).2.2]
    · simpa using hs.left_right_ne _ _ fun a => hij (congrArg _ a)
  · intro i
    cases i using Fin.cases
    · simpa using hd
    · simpa using hd' _
  · intro i j hij
    cases i using Fin.cases <;> cases j using Fin.cases
    · exact dvd_rfl
    · simp only [Fin.cons_zero, Fin.cons_succ]
      rw [← hs.left_right_self]
      exact h₃ _ (he' _).1 _ (hf' _).1 ((hmem _).1 (hf' _)).2.1
        (hB.eq_iff.1 ((hmem _).1 (he' _)).2.2)
    · exact absurd hij (by simp)
    · simpa using hdvd _ _ (by simpa using hij)
  · apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨i | i, rfl⟩ <;> cases i using Fin.cases
      · exact he
      · exact (he' _).1
      · exact hf
      · exact (hf' _).1
    · intro y hy
      obtain ⟨a, b, y', hy', rfl⟩ := hdec y hy
      refine Submodule.add_mem _ (Submodule.add_mem _ (Submodule.smul_mem _ _ ?_)
        (Submodule.smul_mem _ _ ?_)) ?_
      · exact Submodule.subset_span ⟨Sum.inl 0, rfl⟩
      · exact Submodule.subset_span ⟨Sum.inr 0, rfl⟩
      · rw [← hspan] at hy'
        refine Submodule.span_mono ?_ hy'
        rintro _ ⟨i | i, rfl⟩
        · exact ⟨Sum.inl i.succ, rfl⟩
        · exact ⟨Sum.inr i.succ, rfl⟩
end GlobalTheory
