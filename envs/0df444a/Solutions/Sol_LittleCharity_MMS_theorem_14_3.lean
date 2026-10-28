-- Prove2me | solution 3 for LittleCharity.MMS.theorem_14
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T14:54:51.531639+00:00
-- url     : https://prove2.me/submissions/a87e1ca5-e067-48c4-b372-d07d907b8746

import Mathlib
import Definitions.Def_LittleCharity_MMS_Setting
import Theorems.Thm_LittleCharity_MMS_sum_1_to_3

-- carved verbatim out of submission f6b0a743-f93d-41ba-ae74-9e531ddfd142, lines 142-209

section
set_option autoImplicit false
open scoped BigOperators
open LittleCharity.MMS

lemma value_mono {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ) (hadd : IsAdditive v)
    (i : Fin n) {S T : Finset (Fin m)} (h : S ⊆ T) : v i S ≤ v i T := by
  rw [hadd.1 i S, hadd.1 i T]
  exact Finset.sum_le_sum_of_subset_of_nonneg h (fun g _ _ => hadd.2 i {g})

lemma mms_reduced_average {n m r : ℕ} (v : Fin n → Finset (Fin m) → ℝ)
    (hadd : IsAdditive v) (i : Fin n) (S : Finset (Fin m))
    (hr : 0 < r) (hremoved : (Finset.univ \ S).card + r ≤ n) :
    mms (v i) n Finset.univ ≤ v i S / (r : ℝ) := by
  classical
  have : Nonempty (Fin n) := ⟨i⟩
  unfold mms
  apply ciSup_le
  intro f
  let B := fun j : Fin n => Finset.univ.filter (fun g : Fin m => f g = j)
  let A := Finset.univ \ (Finset.univ \ S).image f
  let z := ⨅ j : Fin n, v i (B j)
  have hz : 0 ≤ z := le_ciInf (fun j => hadd.2 i (B j))
  have hcard : r ≤ A.card := by
    have hi := Finset.card_image_le (s := Finset.univ \ S) (f := f)
    have hc := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ ((Finset.univ \ S).image f))
    simp only [Finset.card_univ, Fintype.card_fin] at hc
    dsimp [A]
    omega
  have hsub : A.biUnion B ⊆ S := by
    intro g hg
    obtain ⟨j, hj, hgj⟩ := Finset.mem_biUnion.mp hg
    have he : f g = j := (Finset.mem_filter.mp hgj).2
    by_contra hgS
    apply (Finset.mem_sdiff.mp hj).2
    exact Finset.mem_image.mpr ⟨g, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hgS⟩, he⟩
  have hdis : (A : Set (Fin n)).PairwiseDisjoint B := by
    intro j hj k hk hjk
    apply Finset.disjoint_left.mpr
    intro g hgj hgk
    exact hjk ((Finset.mem_filter.mp hgj).2.symm.trans (Finset.mem_filter.mp hgk).2)
  have hsum : (∑ j ∈ A, v i (B j)) = v i (A.biUnion B) := by
    rw [hadd.1 i (A.biUnion B), Finset.sum_biUnion hdis]
    exact Finset.sum_congr rfl (fun j _ => hadd.1 i (B j))
  have hbound : (A.card : ℝ) * z ≤ v i S := by
    calc
      _ = ∑ j ∈ A, z := by simp
      _ ≤ ∑ j ∈ A, v i (B j) := Finset.sum_le_sum (fun j _ => ciInf_le (Finite.bddBelow_range _) j)
      _ = v i (A.biUnion B) := hsum
      _ ≤ v i S := value_mono v hadd i hsub
  apply (le_div_iff₀ (by exact_mod_cast hr)).mpr
  change z * (r : ℝ) ≤ v i S
  have hc : (r : ℝ) ≤ A.card := by exact_mod_cast hcard
  nlinarith

theorem solution {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ) (hadd : IsAdditive v)
    (X : Fin n → Finset (Fin m)) (hX : LittleCharity.EFX.IsPartialAllocation X) (hEFX : IsEFX v X)
    (hpool : ∀ i, v i (LittleCharity.EFX.pool X) ≤ v i (X i))
    (hsrc : (LittleCharity.EFX.pool X).card < (LittleCharity.EFX.sources v X).card) (i : Fin n) :
    mms (v i) n Finset.univ /
      (2 - ((LittleCharity.EFX.pool X).card : ℝ) / (n : ℝ)) ≤ v i (X i) := by
  classical
  let N' := LittleCharity.EFX.sources v X ∪ {i} ∪ Finset.univ.filter (fun j => 2 ≤ (X j).card)
  let S := N'.biUnion X ∪ LittleCharity.EFX.pool X
  have hi : i ∈ N' := by simp [N']
  have hr : 0 < N'.card := Finset.card_pos.mpr ⟨i, hi⟩
  have hrn : N'.card ≤ n := by simpa using Finset.card_le_card (Finset.subset_univ N')
  have hsmall (j : Fin n) (hj : j ∈ Finset.univ \ N') : (X j).card ≤ 1 := by
    have hnot := (Finset.mem_sdiff.mp hj).2
    have htwo : ¬ 2 ≤ (X j).card := by
      intro h
      apply hnot
      simp [N', h]
    omega
  have hsub : Finset.univ \ S ⊆ (Finset.univ \ N').biUnion X := by
    intro g hg
    have hgS := (Finset.mem_sdiff.mp hg).2
    have hpool' : g ∉ LittleCharity.EFX.pool X := fun h => hgS (Finset.mem_union_right _ h)
    have halloc : g ∈ Finset.univ.biUnion X := by
      simpa [LittleCharity.EFX.pool] using hpool'
    obtain ⟨j, hj, hgj⟩ := Finset.mem_biUnion.mp halloc
    have hjnot : j ∉ N' := by
      intro hjN
      exact hgS (Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨j, hjN, hgj⟩))
    exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_sdiff.mpr ⟨hj, hjnot⟩, hgj⟩
  have hcard : (Finset.univ \ S).card ≤ (Finset.univ \ N').card := by
    calc
      _ ≤ ((Finset.univ \ N').biUnion X).card := Finset.card_le_card hsub
      _ ≤ ∑ j ∈ Finset.univ \ N', (X j).card := Finset.card_biUnion_le
      _ ≤ ∑ j ∈ Finset.univ \ N', 1 := Finset.sum_le_sum hsmall
      _ = _ := by simp
  have hremoved : (Finset.univ \ S).card + N'.card ≤ n := by
    have hc := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ N')
    simp only [Finset.card_univ, Fintype.card_fin] at hc
    omega
  have hmms := mms_reduced_average v hadd i S hr hremoved
  have hsum := LittleCharity.MMS.sum_1_to_3 v hadd X hX hEFX hpool hsrc i N' rfl
  have hrpos : (0 : ℝ) < N'.card := by exact_mod_cast hr
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt i.isLt)
  have hrn' : (N'.card : ℝ) ≤ n := by exact_mod_cast hrn
  have hk : ((LittleCharity.EFX.pool X).card : ℝ) < n := by
    have ha : (LittleCharity.EFX.sources v X).card ≤ n := by
      simpa using Finset.card_le_card (Finset.subset_univ (LittleCharity.EFX.sources v X))
    exact_mod_cast hsrc.trans_le ha
  have hden : 0 < 2 - ((LittleCharity.EFX.pool X).card : ℝ) / (n : ℝ) := by
    have hlt := (div_lt_one hnpos).mpr hk
    linarith
  apply (div_le_iff₀ hden).mpr
  have hred : v i S / (N'.card : ℝ) ≤
      (2 - ((LittleCharity.EFX.pool X).card : ℝ) / (N'.card : ℝ)) * v i (X i) := by
    apply (div_le_iff₀ hrpos).mpr
    calc
      v i S ≤ (2 * (N'.card : ℝ) - ((LittleCharity.EFX.pool X).card : ℝ)) * v i (X i) := hsum
      _ = _ := by field_simp <;> ring
  have hratio : ((LittleCharity.EFX.pool X).card : ℝ) / (n : ℝ) ≤
      ((LittleCharity.EFX.pool X).card : ℝ) / (N'.card : ℝ) :=
    div_le_div_of_nonneg_left (Nat.cast_nonneg _) hrpos hrn'
  calc
    _ ≤ v i S / (N'.card : ℝ) := hmms
    _ ≤ _ := hred
    _ ≤ _ := by nlinarith [hadd.2 i (X i), mul_nonneg (sub_nonneg.mpr hratio) (hadd.2 i (X i))]

end
