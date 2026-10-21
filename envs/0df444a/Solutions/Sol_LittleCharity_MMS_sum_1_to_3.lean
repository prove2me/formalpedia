-- Prove2me | solution 1 for LittleCharity.MMS.sum_1_to_3
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-20T09:07:03.183034+00:00
-- url     : https://prove2.me/submissions/ab8a8c20-dc72-4357-bb2a-8da127bc6fb7

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



theorem solution {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ) (hadd : IsAdditive v)
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

