-- Prove2me | solution 1 for LittleCharity.MMS.theorem_14
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-20T09:09:30.78599+00:00
-- url     : https://prove2.me/submissions/f6b0a743-f93d-41ba-ae74-9e531ddfd142

-- Research direction: Alexander Richard Towell (queelius); formalization: OpenAI Codex.
-- Argument: Bhaskar Ray Chaudhury, Telikepalli Kavitha, Kurt Mehlhorn, Alkmini Sgouritsa, arXiv:1907.04596v3.
-- Platform formulation: mikedeng1; review: Shuze Chen.
import Mathlib
import Definitions.Def_LittleCharity_MMS_Setting
set_option autoImplicit false
open scoped BigOperators
open LittleCharity.MMS

theorem efx_bound {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ) (hadd : IsAdditive v)
    (X : Fin n → Finset (Fin m)) (hEFX : IsEFX v X) (i j : Fin n)
    (hj : 2 ≤ (X j).card) :
    (1 - 1 / ((X j).card : ℝ)) * v i (X j) ≤ v i (X i) ∧
      (1 / 2 : ℝ) * v i (X j) ≤ v i (X i) := by
  classical
  have hsum (g : Fin m) (hg : g ∈ X j) :
      v i (X j) - v i {g} ≤ v i (X i) := by
    have h := hEFX i j g hg
    rw [hadd.1 i ((X j).erase g)] at h
    have he := Finset.sum_erase_add (X j) (fun g => v i {g}) hg
    rw [← hadd.1 i (X j)] at he
    linarith
  have h := Finset.sum_le_sum hsum
  simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul] at h
  rw [← hadd.1 i (X j)] at h
  have hc : (2 : ℝ) ≤ (X j).card := by exact_mod_cast hj
  have hp : (0 : ℝ) < (X j).card := by linarith
  have hfirst : (1 - 1 / ((X j).card : ℝ)) * v i (X j) ≤ v i (X i) := by
    apply (mul_le_mul_iff_right₀ hp).mp
    field_simp
    nlinarith
  refine ⟨hfirst, ?_⟩
  have hfrac : 1 / ((X j).card : ℝ) ≤ (1 / 2 : ℝ) := by
    exact one_div_le_one_div_of_le (by norm_num) hc
  have hn := hadd.2 i (X j)
  nlinarith



theorem source_sum_bound {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ) (hadd : IsAdditive v)
    (X : Fin n → Finset (Fin m)) (hX : LittleCharity.EFX.IsPartialAllocation X) (hEFX : IsEFX v X)
    (hpool : ∀ i, v i (LittleCharity.EFX.pool X) ≤ v i (X i))
    (hsrc : (LittleCharity.EFX.pool X).card < (LittleCharity.EFX.sources v X).card) (i : Fin n)
    (N' : Finset (Fin n))
    (hN' : N' = LittleCharity.EFX.sources v X ∪ {i} ∪ Finset.univ.filter (fun j => 2 ≤ (X j).card)) :
    v i (N'.biUnion X ∪ LittleCharity.EFX.pool X) ≤
      (2 * (N'.card : ℝ) - ((LittleCharity.EFX.pool X).card : ℝ)) * v i (X i) := by
  classical
  let A := LittleCharity.EFX.sources v X
  have hAs : A ⊆ N' := by rw [hN']; exact Finset.subset_union_left.trans Finset.subset_union_left
  have hA (j : Fin n) (hj : j ∈ A) : v i (X j) ≤ v i (X i) := by
    have h : LittleCharity.EFX.IsSource v X j := (Finset.mem_filter.mp hj).2
    exact le_of_not_gt (h i)
  have hother (j : Fin n) (hj : j ∈ N' \ A) : v i (X j) ≤ 2 * v i (X i) := by
    have hjN := (Finset.mem_sdiff.mp hj).1
    rw [hN'] at hjN
    simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_filter, Finset.mem_univ, true_and] at hjN
    rcases hjN with ((hs | rfl) | htwo)
    · exact False.elim ((Finset.mem_sdiff.mp hj).2 hs)
    · nlinarith [hadd.2 j (X j)]
    · nlinarith [(efx_bound v hadd X hEFX i j htwo).2]
  have hdis : Disjoint (N'.biUnion X) (LittleCharity.EFX.pool X) := by
    apply Finset.disjoint_left.mpr
    intro g hg hp
    obtain ⟨j, hj, hgj⟩ := Finset.mem_biUnion.mp hg
    have hg' : g ∈ Finset.univ.biUnion X := Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j, hgj⟩
    exact (Finset.mem_sdiff.mp hp).2 hg'
  have hvalue : v i (N'.biUnion X ∪ LittleCharity.EFX.pool X) =
      (∑ j ∈ N', v i (X j)) + v i (LittleCharity.EFX.pool X) := by
    rw [hadd.1 i (_ ∪ _), Finset.sum_union hdis, ← hadd.1 i (LittleCharity.EFX.pool X)]
    congr 1
    rw [Finset.sum_biUnion]
    · exact Finset.sum_congr rfl (fun j _ => (hadd.1 i (X j)).symm)
    · intro a ha b hb hab
      exact hX hab
  have hsumA : (∑ j ∈ A, v i (X j)) ≤ (A.card : ℝ) * v i (X i) := by
    simpa using Finset.sum_le_sum hA
  have hsumC : (∑ j ∈ N' \ A, v i (X j)) ≤ ((N' \ A).card : ℝ) * (2 * v i (X i)) := by
    simpa using Finset.sum_le_sum hother
  have hsum := Finset.sum_sdiff hAs (f := fun j => v i (X j))
  have hcard : ((N' \ A).card : ℝ) + (A.card : ℝ) = (N'.card : ℝ) := by
    exact_mod_cast Finset.card_sdiff_add_card_eq_card hAs
  have hcount : ((LittleCharity.EFX.pool X).card : ℝ) + 1 ≤ (A.card : ℝ) := by
    exact_mod_cast hsrc
  have hcardmul := congrArg (fun t : ℝ => t * v i (X i)) hcard
  rw [hvalue]
  nlinarith [hpool i, mul_nonneg (sub_nonneg.mpr hcount) (hadd.2 i (X i))]



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
  have hsum := source_sum_bound v hadd X hX hEFX hpool hsrc i N' rfl
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

