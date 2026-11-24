-- Prove2me | solution 1 for GlobalTheory.exists_isSymplecticBasis_extend
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:16:11.968596+00:00
-- url     : https://prove2.me/submissions/148eff57-b7b7-42c9-b00d-5b1530e880b6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DualRestrictSurjectiveOfIsTorsionFreeQuotient
import Theorems.Thm_GlobalTheory_IsSymplecticFamily_left_right
import Theorems.Thm_GlobalTheory_IsSymplecticFamily_right_left
import Theorems.Thm_GlobalTheory_IsSymplecticFamily_sum
import Theorems.Thm_GlobalTheory_exists_isSymplecticFamily_span_eq
import Theorems.Thm_GlobalTheory_IsSymplecticBasis_left_left
import Theorems.Thm_GlobalTheory_IsSymplecticBasis_right_right
import Theorems.Thm_GlobalTheory_IsSymplecticBasis_left_right
import Theorems.Thm_GlobalTheory_IsSymplecticBasis_right_left
import Theorems.Thm_GlobalTheory_IsSymplecticFamily_exists_isSymplecticBasis
import Theorems.Thm_GlobalTheory_exists_isSymplecticBasis
import Theorems.Thm_GlobalTheory_orthogonalQuotientForm_mk
import Theorems.Thm_GlobalTheory_exists_isSymplecticFamily_of_isotropic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.orthogonalQuotientForm_mk

set_option autoImplicit false
open Module Function
open GlobalTheory
variable {R M : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [AddCommGroup M]
  [Module R M] [Module.Finite R M] {B : LinearMap.BilinForm R M} {I : Submodule R M}
namespace GlobalTheory
theorem _root_.solution [Module.Free R M] {ι : Type*} [Finite ι] (hB : B.IsAlt)
    (hp : Bijective B) (hI : IsTorsionFree R (M ⧸ I)) (hiso : I ≤ B.orthogonal I)
    (v : Basis ι R I) :
    ∃ (g : ℕ) (b : Basis ((ι ⊕ Fin g) ⊕ (ι ⊕ Fin g)) R M), IsSymplecticBasis B b ∧
      ∀ i, b (Sum.inl (Sum.inl i)) = v i := by
  classical
  have := Fintype.ofFinite ι
  obtain ⟨f, hf⟩ := exists_isSymplecticFamily_of_isotropic hB hp.2 hI hiso v
  let N : Submodule R M := (⨅ i, LinearMap.ker (B (v i))) ⊓ ⨅ i, LinearMap.ker (B (f i))
  have hmem : ∀ y, y ∈ N ↔ (∀ i, B (v i) y = 0) ∧ ∀ i, B (f i) y = 0 := fun y => by
    simp [N, Submodule.mem_iInf]
  have hdec : ∀ y, ∃ a b : ι → R, ∃ y' ∈ N, y = ∑ i, a i • (v i : M) + ∑ i, b i • f i + y' := by
    intro y
    refine ⟨fun i => B y (f i), fun i => B (v i) y,
      y - ∑ i, B y (f i) • (v i : M) - ∑ i, B (v i) y • f i, (hmem _).2 ⟨fun k => ?_, fun k => ?_⟩,
      by abel⟩
    · simp [hf.left_left, hf.left_right]
    · simp [hf.right_right, hf.right_left hB, ← hB.neg_eq y]
  obtain ⟨g, e', f', d, h', hd, -, hspan⟩ := exists_isSymplecticFamily_span_eq hB N (by
    intro x hx hx0
    refine (injective_iff_map_eq_zero B).1 hp.1 x (LinearMap.ext fun y => ?_)
    obtain ⟨a, b, y', hy', rfl⟩ := hdec y
    simp [hx0 y' hy', fun i => hB.eq_iff.1 (((hmem x).1 hx).1 i),
      fun i => hB.eq_iff.1 (((hmem x).1 hx).2 i)])
  have he' : ∀ i, e' i ∈ N := fun i => hspan ▸ Submodule.subset_span ⟨Sum.inl i, rfl⟩
  have hf' : ∀ i, f' i ∈ N := fun i => hspan ▸ Submodule.subset_span ⟨Sum.inr i, rfl⟩
  have hs := IsSymplecticFamily.sum hB hf h' (fun i j => ((hmem _).1 (he' j)).1 i)
    (fun i j => ((hmem _).1 (hf' j)).1 i) (fun i j => ((hmem _).1 (he' j)).2 i)
    (fun i j => ((hmem _).1 (hf' j)).2 i)
  obtain ⟨b, hb, hbe⟩ := hs.exists_isSymplecticBasis (by
    rintro (i | i)
    · exact one_ne_zero
    · exact hd i) (by
    rw [eq_top_iff]
    intro y _
    obtain ⟨a, b, y', hy', rfl⟩ := hdec y
    refine Submodule.add_mem _ (Submodule.add_mem _
      (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_)
      (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_)) ?_
    · exact Submodule.subset_span ⟨Sum.inl (Sum.inl i), rfl⟩
    · exact Submodule.subset_span ⟨Sum.inr (Sum.inl i), rfl⟩
    · rw [← hspan] at hy'
      refine Submodule.span_mono ?_ hy'
      rintro _ ⟨i | i, rfl⟩
      · exact ⟨Sum.inl (Sum.inr i), rfl⟩
      · exact ⟨Sum.inr (Sum.inr i), rfl⟩) hp.2
  exact ⟨g, b, hb, fun i => hbe _⟩
end GlobalTheory
