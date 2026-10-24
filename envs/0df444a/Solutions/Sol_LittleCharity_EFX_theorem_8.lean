-- Prove2me | solution 1 for LittleCharity.EFX.theorem_8
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-24T05:40:52.740716+00:00
-- url     : https://prove2.me/submissions/9459294c-f6ad-40c9-aa8a-39939d47e145

import Mathlib
import Definitions.Def_LittleCharity_EFX_Setting


open LittleCharity.EFX
namespace CharityProof

variable {n m : ℕ} {v : Fin n → Finset (Fin m) → ℝ}

@[simp] theorem mem_pool_iff (X : Fin n → Finset (Fin m)) (g : Fin m) :
    g ∈ pool X ↔ ∀ i, g ∉ X i := by
  classical
  simp [pool]

theorem pool_disjoint (X : Fin n → Finset (Fin m)) (i : Fin n) :
    Disjoint (pool X) (X i) := by
  classical
  exact Finset.disjoint_left.mpr fun g hg hi => (mem_pool_iff X g).mp hg i hi

theorem efx_of_erased_bound (X Y : Fin n → Finset (Fin m))
    (hown : ∀ i, v i (X i) ≤ v i (Y i))
    (hb : ∀ i j, ∀ g ∈ Y j, v i ((Y j).erase g) ≤ v i (X i)) : IsEFX v Y :=
  fun i j g hg => (hb i j g hg).trans (hown i)

theorem update_pool_feasible (X : Fin n → Finset (Fin m))
    (hX : IsPartialAllocation X) (i : Fin n) (Z : Finset (Fin m))
    (hZ : Z ⊆ pool X) : IsPartialAllocation (Function.update X i Z) := by
  classical
  intro a b hab
  by_cases ha : a = i
  · subst a
    rw [Function.update_self, Function.update_of_ne hab.symm]
    exact (pool_disjoint X b).mono_left hZ
  · rw [Function.update_of_ne ha]
    by_cases hb : b = i
    · subst b
      rw [Function.update_self]
      exact ((pool_disjoint X a).mono_left hZ).symm
    · rw [Function.update_of_ne hb]
      exact hX hab

theorem minimal_pool_improvement (X : Fin n → Finset (Fin m))
    (hX : IsPartialAllocation X) (hE : IsEFX v X)
    (i : Fin n) (Z : Finset (Fin m))
    (hZ : IsMinimalEnviedSubset v X (pool X) Z)
    (hi : v i (X i) < v i Z) :
    IsPartialAllocation (Function.update X i Z) ∧
      IsEFX v (Function.update X i Z) ∧
      welfare v X < welfare v (Function.update X i Z) := by
  classical
  have ho : ∀ a, v a (X a) ≤ v a (Function.update X i Z a) := by
    intro a
    by_cases h : a = i
    · subst a; simpa using hi.le
    · simp [Function.update_of_ne h]
  refine ⟨update_pool_feasible X hX i Z hZ.1, ?_, ?_⟩
  · apply efx_of_erased_bound X _ ho
    intro a b g hg
    by_cases hb : b = i
    · subst b
      simp only [Function.update_self] at hg ⊢
      exact hZ.2.2 _ (Finset.erase_ssubset hg) a
    · simpa [Function.update_of_ne hb] using hE a b g (by simpa [Function.update_of_ne hb] using hg)
  · apply Finset.sum_lt_sum (fun a _ => ho a)
    exact ⟨i, Finset.mem_univ _, by simpa using hi⟩

theorem add_pool_feasible (X : Fin n → Finset (Fin m))
    (hX : IsPartialAllocation X) (i : Fin n) (g : Fin m) (hg : g ∈ pool X) :
    IsPartialAllocation (Function.update X i (insert g (X i))) := by
  classical
  have hn := (mem_pool_iff X g).mp hg
  intro a b hab
  by_cases ha : a = i
  · subst a
    rw [Function.update_self, Function.update_of_ne hab.symm]
    exact Finset.disjoint_insert_left.mpr ⟨hn b, hX hab⟩
  · rw [Function.update_of_ne ha]
    by_cases hb : b = i
    · subst b
      rw [Function.update_self]
      exact (Finset.disjoint_insert_left.mpr ⟨hn a, hX (Ne.symm ha)⟩).symm
    · rw [Function.update_of_ne hb]
      exact hX hab

theorem add_pool_eq (X : Fin n → Finset (Fin m)) (i : Fin n) (g : Fin m) :
    pool (Function.update X i (insert g (X i))) = (pool X).erase g := by
  classical
  ext a
  simp only [mem_pool_iff, Finset.mem_erase]
  constructor
  · intro h
    have hi := h i
    simp only [Function.update_self, Finset.mem_insert, not_or] at hi
    refine ⟨hi.1, ?_⟩
    intro j hj
    by_cases he : j = i
    · subst j; exact hi.2 hj
    · exact h j (by simpa [Function.update_of_ne he] using hj)
  · rintro ⟨hag, h⟩ j
    by_cases he : j = i
    · subst j; simpa using And.intro hag (h i)
    · simpa [Function.update_of_ne he] using h j

theorem add_pool_own_le (X : Fin n → Finset (Fin m))
    (hmono : IsMonotoneVal v) (i : Fin n) (g : Fin m) :
    ∀ a, v a (X a) ≤ v a (Function.update X i (insert g (X i)) a) := by
  classical
  intro a
  by_cases h : a = i
  · subst a; simpa using hmono i _ _ (Finset.subset_insert g (X i))
  · simp [Function.update_of_ne h]

theorem add_unenvied_efx (X : Fin n → Finset (Fin m))
    (hE : IsEFX v X) (hmono : IsMonotoneVal v) (i : Fin n) (g : Fin m)
    (hnot : ¬ IsEnvied v X (insert g (X i))) :
    IsEFX v (Function.update X i (insert g (X i))) := by
  classical
  apply efx_of_erased_bound X _ (add_pool_own_le X hmono i g)
  intro a b z hz
  by_cases hb : b = i
  · subst b
    simp only [Function.update_self] at hz ⊢
    exact (hmono a _ _ (Finset.erase_subset _ _)).trans (le_of_not_gt fun h => hnot ⟨a, h⟩)
  · simpa [Function.update_of_ne hb] using hE a b z (by simpa [Function.update_of_ne hb] using hz)

end CharityProof

open LittleCharity.EFX
namespace CharityProof
variable {n m : ℕ} {v : Fin n → Finset (Fin m) → ℝ}

def Extremal (v : Fin n → Finset (Fin m) → ℝ) (X : Fin n → Finset (Fin m)) : Prop :=
  IsPartialAllocation X ∧ IsEFX v X ∧
    (∀ Y, IsPartialAllocation Y → IsEFX v Y → welfare v Y ≤ welfare v X) ∧
    (∀ Y, IsPartialAllocation Y → IsEFX v Y → welfare v Y = welfare v X →
      (pool X).card ≤ (pool Y).card)

theorem exists_extremal (v : Fin n → Finset (Fin m) → ℝ)
    (hnorm : IsNormalized v) (hmono : IsMonotoneVal v) : ∃ X, Extremal v X := by
  classical
  let F := Finset.univ.filter (fun X : Fin n → Finset (Fin m) => IsPartialAllocation X ∧ IsEFX v X)
  have he : IsPartialAllocation (fun _ : Fin n => (∅ : Finset (Fin m))) ∧
      IsEFX v (fun _ : Fin n => (∅ : Finset (Fin m))) := by
    constructor
    · intro i j _; exact Finset.disjoint_empty_left _
    · intro i j g _
      calc
        v i (Finset.erase ∅ g) ≤ v i ∅ := hmono i _ _ (Finset.erase_subset g ∅)
        _ = 0 := hnorm i
        _ ≤ v i ∅ := by rw [hnorm i]
  have hF : F.Nonempty := ⟨_, by simp only [F, Finset.mem_filter, Finset.mem_univ, true_and]; exact he⟩
  obtain ⟨A, hA, hmax⟩ := F.exists_max_image (welfare v) hF
  let G := F.filter (fun X => welfare v X = welfare v A)
  have hG : G.Nonempty := ⟨A, by simp [G, hA]⟩
  obtain ⟨X, hX, hmin⟩ := G.exists_min_image (fun Y => (pool Y).card) hG
  have hXF : X ∈ F := (Finset.mem_filter.mp hX).1
  have hval : welfare v X = welfare v A := (Finset.mem_filter.mp hX).2
  have hx := (Finset.mem_filter.mp hXF).2
  refine ⟨X, hx.1, hx.2, ?_, ?_⟩
  · intro Y hp hefx
    rw [hval]
    exact hmax Y (by simp [F, hp, hefx])
  · intro Y hp hefx hy
    exact hmin Y (by simp [G, F, hp, hefx, hy, hval])

theorem minimal_envied_exists (X : Fin n → Finset (Fin m)) (S : Finset (Fin m))
    (hS : IsEnvied v X S) : ∃ Z, IsMinimalEnviedSubset v X S Z := by
  classical
  let F := S.powerset.filter (IsEnvied v X)
  have hF : F.Nonempty := ⟨S, by simp [F, hS]⟩
  obtain ⟨Z, hZ, hmin⟩ := F.exists_min_image Finset.card hF
  have hz := Finset.mem_filter.mp hZ
  have hsub : Z ⊆ S := Finset.mem_powerset.mp hz.1
  refine ⟨Z, hsub, hz.2, ?_⟩
  intro T hT j
  apply le_of_not_gt
  intro hj
  have hTF : T ∈ F := by
    simp only [F, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨hT.1.trans hsub, j, hj⟩
  exact (Finset.card_lt_card hT).not_ge (hmin T hTF)

theorem extremal_pool_unenvied (X : Fin n → Finset (Fin m)) (hX : Extremal v X) :
    ∀ i, v i (pool X) ≤ v i (X i) := by
  intro i
  apply le_of_not_gt
  intro hi
  obtain ⟨Z, hZ⟩ := minimal_envied_exists X (pool X) ⟨i, hi⟩
  obtain ⟨j, hj⟩ := hZ.2.1
  have himp := minimal_pool_improvement X hX.1 hX.2.1 j Z hZ hj
  exact himp.2.2.not_ge (hX.2.2.1 _ himp.1 himp.2.1)

theorem extremal_no_u0 (X : Fin n → Finset (Fin m))
    (hmono : IsMonotoneVal v) (hX : Extremal v X) : ¬ U0Applicable v X := by
  classical
  rintro ⟨g, hg, i, he⟩
  have hp := add_pool_feasible X hX.1 i g hg
  have hl : welfare v X ≤ welfare v (Function.update X i (insert g (X i))) :=
    Finset.sum_le_sum (fun a _ => add_pool_own_le X hmono i g a)
  have hu := hX.2.2.1 _ hp he
  have hm := hX.2.2.2 _ hp he (le_antisymm hu hl)
  rw [add_pool_eq] at hm
  exact (Finset.card_erase_lt_of_mem hg).not_ge hm

end CharityProof

set_option autoImplicit false
namespace CharityProof

theorem closed_permutation {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    (p : α → α) :
    ∃ T : Finset α, T.Nonempty ∧ ∃ e : T ≃ T, ∀ j : T, (e j : α) = p j := by
  classical
  let C : Finset (Finset α) := Finset.univ.filter fun T => T.Nonempty ∧ T.image p ⊆ T
  have hu : (Finset.univ : Finset α) ∈ C := by simp [C]
  obtain ⟨T, hT, hmin⟩ := Finset.exists_min_image C Finset.card ⟨_, hu⟩
  have hprop : T.Nonempty ∧ T.image p ⊆ T := (Finset.mem_filter.mp hT).2
  have himage : T.image p ∈ C := by
    simp only [C, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hprop.1.image p, Finset.image_subset_image hprop.2⟩
  have heq : T.image p = T := Finset.eq_of_subset_of_card_le hprop.2 (hmin _ himage)
  let f : T → T := fun j => ⟨p j, hprop.2 (Finset.mem_image.mpr ⟨j, j.property, rfl⟩)⟩
  have hs : Function.Surjective f := by
    intro j
    have hj : (j : α) ∈ T.image p := heq.symm ▸ j.property
    obtain ⟨a, ha, hp⟩ := Finset.mem_image.mp hj
    exact ⟨⟨a, ha⟩, Subtype.ext hp⟩
  let e : T ≃ T := Equiv.ofBijective f ((Fintype.bijective_iff_surjective_and_card f).mpr ⟨hs, rfl⟩)
  exact ⟨T, hprop.1, e, fun _ => rfl⟩

end CharityProof

set_option autoImplicit false
open LittleCharity.EFX
namespace CharityProof

theorem container_improvement {n m : ℕ} (hn : 0 < n)
    (v : Fin n → Finset (Fin m) → ℝ) (X B : Fin n → Finset (Fin m))
    (p : Fin n → Fin n) (hX : IsPartialAllocation X) (hEFX : IsEFX v X)
    (hB : Pairwise fun j l => Disjoint (B j) (B l))
    (hcross : ∀ j l, j ≠ l → Disjoint (B j) (X l))
    (hdelete : ∀ i j, ∀ g ∈ B j, v i ((B j).erase g) ≤ v i (X i))
    (hadmire : ∀ j, v (p j) (X (p j)) < v (p j) (B j)) :
    ∃ Y, IsPartialAllocation Y ∧ IsEFX v Y ∧
      (∀ i, v i (X i) ≤ v i (Y i)) ∧ welfare v X < welfare v Y := by
  classical
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨T, hT, e, he⟩ := closed_permutation p
  let Y : Fin n → Finset (Fin m) := fun i => if hi : i ∈ T then B (e.symm ⟨i, hi⟩) else X i
  have hinside (i : Fin n) (hi : i ∈ T) : v i (X i) < v i (Y i) := by
    have hp : p (e.symm ⟨i, hi⟩) = i := by
      rw [← he]
      exact congrArg Subtype.val (e.apply_symm_apply ⟨i, hi⟩)
    simpa only [Y, dif_pos hi, hp] using hadmire (e.symm ⟨i, hi⟩)
  have hweak (i : Fin n) : v i (X i) ≤ v i (Y i) := by
    by_cases hi : i ∈ T
    · exact (hinside i hi).le
    · simp [Y, hi]
  have hpartial : IsPartialAllocation Y := by
    intro i j hij
    by_cases hi : i ∈ T <;> by_cases hj : j ∈ T
    · simp only [Y, dif_pos hi, dif_pos hj]
      apply hB
      intro h
      apply hij
      have hs : e.symm ⟨i, hi⟩ = e.symm ⟨j, hj⟩ := Subtype.ext h
      exact congrArg Subtype.val (e.symm.injective hs)
    · simp only [Y, dif_pos hi, dif_neg hj]
      apply hcross
      intro h
      exact hj (h ▸ (e.symm ⟨i, hi⟩).property)
    · simp only [Y, dif_neg hi, dif_pos hj]
      apply Disjoint.symm
      apply hcross
      intro h
      exact hi (h ▸ (e.symm ⟨j, hj⟩).property)
    · simpa only [Y, dif_neg hi, dif_neg hj] using hX hij
  have hefx : IsEFX v Y := by
    intro i j g hg
    by_cases hj : j ∈ T
    · have hg' : g ∈ B (e.symm ⟨j, hj⟩) := by simpa only [Y, dif_pos hj] using hg
      simpa only [Y, dif_pos hj] using (hdelete i _ g hg').trans (hweak i)
    · have hg' : g ∈ X j := by simpa only [Y, dif_neg hj] using hg
      simpa only [Y, dif_neg hj] using (hEFX i j g hg').trans (hweak i)
  refine ⟨Y, hpartial, hefx, hweak, ?_⟩
  apply Finset.sum_lt_sum (fun i _ => hweak i)
  obtain ⟨i, hi⟩ := hT
  exact ⟨i, Finset.mem_univ _, hinside i hi⟩

end CharityProof

open LittleCharity.EFX
namespace CharityProof
variable {n m : ℕ} {v : Fin n → Finset (Fin m) → ℝ}

theorem extremal_sources_bound (X : Fin n → Finset (Fin m)) (hn : 0 < n)
    (hmono : IsMonotoneVal v) (hX : Extremal v X) :
    (pool X).card < (sources v X).card := by
  classical
  by_contra hlt
  have hP : (sources v X).card ≤ (pool X).card := Nat.le_of_not_gt hlt
  obtain ⟨g, hg⟩ := Function.Embedding.exists_of_card_le_finset
    (α := ↥(sources v X)) (s := pool X) (by simpa using hP)
  have hgP (s : ↥(sources v X)) : g s ∈ pool X := hg ⟨s, rfl⟩
  have hgX (s : ↥(sources v X)) (i : Fin n) : g s ∉ X i :=
    (mem_pool_iff X (g s)).mp (hgP s) i
  have henv (s : ↥(sources v X)) : IsEnvied v X (insert (g s) (X s)) := by
    by_contra h
    exact extremal_no_u0 X hmono hX
      ⟨g s, hgP s, s, add_unenvied_efx X hX.2.1 hmono s (g s) h⟩
  choose Z hZ using fun s : ↥(sources v X) =>
    minimal_envied_exists X (insert (g s) (X s)) (henv s)
  let B : Fin n → Finset (Fin m) := fun j =>
    if hj : j ∈ sources v X then Z ⟨j, hj⟩ else X j
  have hcross : ∀ j l, j ≠ l → Disjoint (B j) (X l) := by
    intro j l hne
    by_cases hj : j ∈ sources v X
    · simp only [B, dif_pos hj]
      exact (Finset.disjoint_insert_left.mpr ⟨hgX ⟨j, hj⟩ l, hX.1 hne⟩).mono_left (hZ ⟨j, hj⟩).1
    · simpa only [B, dif_neg hj] using hX.1 hne
  have hgood (s : ↥(sources v X)) (l : Fin n) (hne : (s : Fin n) ≠ l) :
      g s ∉ B l := by
    by_cases hl : l ∈ sources v X
    · simp only [B, dif_pos hl]
      intro h
      rcases Finset.mem_insert.mp ((hZ ⟨l, hl⟩).1 h) with he | ho
      · exact hne (congrArg Subtype.val (g.injective he))
      · exact hgX s l ho
    · simpa only [B, dif_neg hl] using hgX s l
  have hpair : Pairwise fun j l => Disjoint (B j) (B l) := by
    intro j l hne
    by_cases hj : j ∈ sources v X
    · simp only [B, dif_pos hj]
      exact (Finset.disjoint_insert_left.mpr
        ⟨hgood ⟨j, hj⟩ l hne, (hcross l j hne.symm).symm⟩).mono_left (hZ ⟨j, hj⟩).1
    · simpa only [B, dif_neg hj] using (hcross l j hne.symm).symm
  have hdelete : ∀ i j, ∀ a ∈ B j, v i ((B j).erase a) ≤ v i (X i) := by
    intro i j a ha
    by_cases hj : j ∈ sources v X
    · simp only [B, dif_pos hj] at ha ⊢
      exact (hZ ⟨j, hj⟩).2.2 _ (Finset.erase_ssubset ha) i
    · simpa only [B, dif_neg hj] using hX.2.1 i j a (by simpa only [B, dif_neg hj] using ha)
  have hadm : ∀ j, ∃ i, v i (X i) < v i (B j) := by
    intro j
    by_cases hj : j ∈ sources v X
    · simpa only [B, dif_pos hj, IsEnvied] using (hZ ⟨j, hj⟩).2.1
    · have hs : ¬ IsSource v X j := by simpa [sources] using hj
      simp only [IsSource, Envies, not_forall, not_not] at hs
      simpa only [B, dif_neg hj] using hs
  choose p hp using hadm
  obtain ⟨Y, hY, hEY, _, hlt⟩ := container_improvement hn v X B p hX.1 hX.2.1 hpair hcross hdelete hp
  exact hlt.not_ge (hX.2.2.1 Y hY hEY)

end CharityProof

namespace LittleCharity.EFX

theorem theorem_8 {n m : ℕ} (hn : 0 < n)
    (v : Fin n → Finset (Fin m) → ℝ)
    (hnorm : IsNormalized v) (hmono : IsMonotoneVal v) :
    ∃ X : Fin n → Finset (Fin m),
      IsPartialAllocation X ∧ IsEFX v X ∧
      (∀ i, v i (pool X) ≤ v i (X i)) ∧
      (pool X).card < (sources v X).card ∧
      (pool X).card < n := by
  obtain ⟨X, hX⟩ := CharityProof.exists_extremal v hnorm hmono
  have hs := CharityProof.extremal_sources_bound X hn hmono hX
  refine ⟨X, hX.1, hX.2.1, CharityProof.extremal_pool_unenvied X hX, hs, ?_⟩
  exact hs.trans_le (by simpa using (sources v X).card_le_univ)
end LittleCharity.EFX

theorem solution {n m : ℕ} (hn : 0 < n)
    (v : Fin n → Finset (Fin m) → ℝ)
    (hnorm : LittleCharity.EFX.IsNormalized v) (hmono : LittleCharity.EFX.IsMonotoneVal v) :
    ∃ X : Fin n → Finset (Fin m),
      LittleCharity.EFX.IsPartialAllocation X ∧ LittleCharity.EFX.IsEFX v X ∧
      (∀ i, v i (LittleCharity.EFX.pool X) ≤ v i (X i)) ∧
      (LittleCharity.EFX.pool X).card < (LittleCharity.EFX.sources v X).card ∧
      (LittleCharity.EFX.pool X).card < n := by
  exact LittleCharity.EFX.theorem_8 hn v hnorm hmono
