-- Prove2me | solution 1 for MulticlassDS.NatGap.pseudo_cube_natarajan_one
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @CGTMoyano
-- created : 2026-11-24T13:14:29.799923+00:00
-- url     : https://prove2.me/submissions/8245535d-778d-49c7-918c-5b72d99a99fe
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_MulticlassDS_NatGap_Dimensions
import Definitions.Def_MulticlassDS_NatGap_Complexes
import Theorems.Thm_MulticlassDS_NatGap_theorem45_coset_complex
import Theorems.Thm_MulticlassDS_NatGap_prop46_coset_complex_good
import Theorems.Thm_MulticlassDS_NatGap_prop42_good_complex_pseudo_cube
import Theorems.Thm_MulticlassDS_NatGap_cor44_no_empty_square_natarajan_le_one

open MulticlassDS.NatGap

theorem P2M_nshatter_inj {X Y : Type} {n : ℕ} (H : Set (X → Y)) (S : Fin n → X)
    (hS : NShatters H S) : Function.Injective S := by
  obtain ⟨f, g, hfg, hc⟩ := hS
  intro i j hij
  by_contra hne
  obtain ⟨h1, -, e1⟩ := hc (fun _ => true)
  obtain ⟨h2, -, e2⟩ := hc (fun k => decide (k = i))
  have a1 : h1 (S i) = f i := by simpa using congrFun e1 i
  have a2 : h1 (S j) = f j := by simpa using congrFun e1 j
  have b1 : h2 (S i) = f i := by simpa using congrFun e2 i
  have b2 : h2 (S j) = g j := by simpa [Ne.symm hne] using congrFun e2 j
  exact hfg j (a2.symm.trans ((congrArg h1 hij.symm).trans
    (a1.trans (b1.symm.trans ((congrArg h2 hij).trans b2)))))

theorem P2M_one_le_natarajan {X Y : Type} (H : Set (X → Y)) (h g : X → Y) (hh : h ∈ H)
    (hg : g ∈ H) (x : X) (hne : g x ≠ h x) : (1 : ℕ∞) ≤ natarajanDim H := by
  have hS : NShatters H (fun _ : Fin 1 => x) := by
    refine ⟨fun _ => g x, fun _ => h x, fun _ => hne, fun c => ?_⟩
    by_cases hc : c 0
    · refine ⟨g, hg, ?_⟩
      funext i
      have hi : i = 0 := Subsingleton.elim _ _
      subst hi
      simp [hc]
    · refine ⟨h, hh, ?_⟩
      funext i
      have hi : i = 0 := Subsingleton.elim _ _
      subst hi
      simp [hc]
  unfold natarajanDim
  exact le_trans (by simp) (le_iSup_of_le 1 (le_iSup_of_le _ (le_iSup_of_le hS le_rfl)))

theorem solution (d : ℕ) (hd : 1 ≤ d) :
    ∃ (Y : Type) (B : Set (Fin d → Y)), IsPseudoCube B ∧ natarajanDim B = 1 := by
  by_cases hd1 : d = 1
  · subst hd1
    have hP : IsPseudoCube (Set.univ : Set (Fin 1 → Bool)) := by
      refine ⟨⟨fun _ => true, trivial⟩, Set.toFinite _, ?_⟩
      intro h _ i
      refine ⟨fun _ => !h i, trivial, by simp, ?_⟩
      intro j hj
      exact absurd (Subsingleton.elim j i) hj
    refine ⟨Bool, Set.univ, hP, le_antisymm ?_ ?_⟩
    · unfold natarajanDim
      refine iSup_le fun n => iSup_le fun S => iSup_le fun hS => ?_
      have := Fintype.card_le_of_injective S (P2M_nshatter_inj _ S hS)
      simp at this
      exact_mod_cast this
    · exact P2M_one_le_natarajan _ (fun _ => true) (fun _ => false) trivial trivial 0 (by simp)
  · obtain ⟨k, rfl⟩ : ∃ k, d = k + 1 := ⟨d - 1, by omega⟩
    obtain ⟨F, instF, hfin, Hs, h1, h2⟩ := theorem45_coset_complex (k + 1) (by omega)
    haveI := hfin
    have hg := (prop46_coset_complex_good (k + 1) (by omega) Hs h1 h2).1
    simp only [Nat.add_sub_cancel] at hg
    obtain ⟨r, hr⟩ := hg.2.2.2.2.1
    have hB := prop42_good_complex_pseudo_cube _ k hg r hr
    refine ⟨Set F, pseudoCubeOf (cosetComplex Hs) k r, hB,
      le_antisymm (cor44_no_empty_square_natarajan_le_one _ k hg h2 r hr) ?_⟩
    obtain ⟨⟨w, hw⟩, -, hn⟩ := hB
    obtain ⟨g, hg', hne, -⟩ := hn w hw 0
    exact P2M_one_le_natarajan _ w g hw hg' 0 hne
