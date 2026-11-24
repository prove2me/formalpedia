-- Prove2me | solution 1 for GlobalTheory.LevelExist.exists_isSymplecticFamily_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:43:57.494029+00:00
-- url     : https://prove2.me/submissions/2c747932-8a02-4db3-aa64-54eaf6a014d6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DualRestrictSurjectiveOfIsTorsionFreeQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsAlternatingSkewNatural
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_ExistsIsSymplecticFamilySpan
import Theorems.Thm_GlobalTheory_IsSymplecticBasis_left_left
import Theorems.Thm_GlobalTheory_IsSymplecticBasis_right_right
import Theorems.Thm_GlobalTheory_orthogonalQuotientForm_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.orthogonalQuotientForm_mk



set_option autoImplicit false
set_option autoImplicit false
open GlobalTheory GlobalTheory.LevelExist
namespace GlobalTheory.LevelExist
theorem _root_.solution {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V] [IsArtinian R V]
    {B : LinearMap.BilinForm R V} (hB : B.IsAlt) (t : R) (ht : ∀ r, t * r ≠ 0 → IsUnit r) (N : Submodule R V) :
    (∀ x ∈ N, (∀ y ∈ N, B x y = 0) → x = 0) →
    (∀ x ∈ N, x ≠ 0 → ∃ a : R, ∃ y ∈ N, a • x = t • y ∧ t • y ≠ 0) →
    ∃ (g : ℕ) (e f : Fin g → V), IsSymplecticFamily B e f (fun _ => 1) ∧
      Submodule.span R (Set.range (Sum.elim e f)) = N := by
  induction N using WellFoundedLT.induction with
  | ind N ih =>
  intro hN hF
  by_cases hbot : N = ⊥
  · refine ⟨0, Fin.elim0, Fin.elim0, ⟨fun i => i.elim0, fun i => i.elim0,
      fun i => i.elim0, fun i => i.elim0⟩, ?_⟩
    rw [hbot, Submodule.span_eq_bot]
    rintro _ ⟨i | i, rfl⟩ <;> exact i.elim0
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  obtain ⟨-, e, he, -, he0⟩ := hF x hx hx0
  obtain ⟨z, hz, hz0⟩ : ∃ z ∈ N, B (t • e) z ≠ 0 := by
    by_contra! h
    exact he0 (hN _ (N.smul_mem _ he) h)
  have : Nontrivial R := ⟨_, _, hz0⟩
  obtain ⟨u, hu⟩ := (ht (B e z) (by simpa using hz0)).exists_left_inv
  obtain ⟨f, hf, hd⟩ : ∃ f ∈ N, B e f = 1 := ⟨u • z, N.smul_mem _ hz, by simpa using hu⟩
  have hd' : B f e = -1 := by rw [← hB.neg_eq, hd]
  let N' : Submodule R V := N ⊓ (LinearMap.ker (B e) ⊓ LinearMap.ker (B f))
  have hmem : ∀ y, y ∈ N' ↔ y ∈ N ∧ B e y = 0 ∧ B f y = 0 := fun y => Iff.rfl
  have hpr : ∀ y ∈ N, y - B y f • e - B e y • f ∈ N' := fun y hy =>
    (hmem _).2 ⟨N.sub_mem (N.sub_mem hy (N.smul_mem _ he)) (N.smul_mem _ hf),
      by simp [hd, hB.self_eq_zero], by simp [← hB.neg_eq y f, hd', hB.self_eq_zero]⟩
  have hdec : ∀ y ∈ N, ∃ a b : R, ∃ y' ∈ N', y = a • e + b • f + y' := fun y hy =>
    ⟨B y f, B e y, _, hpr y hy, by abel⟩
  obtain ⟨g, e', f', hs, hspan⟩ := ih N' (lt_of_le_of_ne inf_le_left fun h => by
      have := ((hmem f).1 (h ▸ hf)).2.1
      simp [hd] at this) (by
    intro x hx hx0
    refine hN x hx.1 fun y hy => ?_
    obtain ⟨a, b, y', hy', rfl⟩ := hdec y hy
    simp [hx0 y' hy', hB.eq_iff.1 ((hmem x).1 hx).2.1, hB.eq_iff.1 ((hmem x).1 hx).2.2]) (by
    intro x hx hx0
    obtain ⟨a, y, hy, h₁, h₂⟩ := hF x hx.1 hx0
    have h₃ : t • (y - B y f • e - B e y • f) = t • y := by
      have h₄ : t * B y f = 0 := by
        simpa [hB.eq_iff.1 ((hmem x).1 hx).2.2] using (congrArg (B · f) h₁).symm
      have h₅ : t * B e y = 0 := by
        simpa [((hmem x).1 hx).2.1] using (congrArg (B e) h₁).symm
      simp [smul_sub, smul_smul, h₄, h₅]
    exact ⟨a, _, hpr y hy, h₃ ▸ h₁, h₃ ▸ h₂⟩)
  have he' : ∀ i, e' i ∈ N' := fun i => hspan ▸ Submodule.subset_span ⟨Sum.inl i, rfl⟩
  have hf' : ∀ i, f' i ∈ N' := fun i => hspan ▸ Submodule.subset_span ⟨Sum.inr i, rfl⟩
  refine ⟨g + 1, Fin.cons e e', Fin.cons f f', ⟨?_, ?_, ?_, ?_⟩, ?_⟩
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
    · simp [hd]
    · simp [hs.left_right_self]
  · intro i j hij
    cases i using Fin.cases <;> cases j using Fin.cases
    · exact absurd rfl hij
    · simp [((hmem _).1 (hf' _)).2.1]
    · simp [hB.eq_iff.1 ((hmem _).1 (he' _)).2.2]
    · simpa using hs.left_right_ne _ _ fun a => hij (congrArg _ a)
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
end GlobalTheory.LevelExist
