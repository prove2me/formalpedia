-- Prove2me | solution 1 for MulticlassDS.NatGap.prop42_good_complex_pseudo_cube
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-23T20:46:09.143813+00:00
-- url     : https://prove2.me/submissions/671d3e51-1a28-4d6f-a732-ce29ef4132b6

import Init
import Mathlib
import Definitions.Def_MulticlassDS_NatGap_Dimensions
import Definitions.Def_MulticlassDS_NatGap_Complexes

open Set Function Classical
noncomputable section
namespace GoodBridge
open MulticlassDS.NatGap
variable {V : Type*} {C : Set (Finset V)} {d : ℕ} {r : V → Fin (d+1)}

lemma color_injective (hc : IsComplex C) (hr : IsProperColoring C d r)
    {f : Finset V} (hf : f ∈ C) : Set.InjOn r (f : Set V) := by
  classical
  intro u hu v hv he
  by_contra hne
  exact hr u v hne (hc f hf {u,v} (by simp only [Finset.insert_subset_iff,Finset.singleton_subset_iff];exact ⟨hu,hv⟩)) he

lemma word_injective {w : Fin (d+1) → V} (hw : ∀ i, r (w i) = i) : Injective w := by
  intro i j he
  simpa only [hw] using congrArg r he

lemma face_word (hc : IsComplex C) (hr : IsProperColoring C d r)
    {f : Finset V} (hf : f ∈ C) (hcard : f.card = d+1) :
    ∃ w : Fin (d+1) → V, Finset.univ.image w = f ∧ ∀ i,r (w i) = i := by
  classical
  have himg : f.image r = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_image_of_injOn (color_injective hc hr hf),hcard,Fintype.card_fin]
  have hall : ∀ i : Fin (d+1), ∃ v ∈ f,r v=i := by
    intro i
    have hi : i ∈ f.image r := by rw [himg];exact Finset.mem_univ i
    exact Finset.mem_image.mp hi
  choose w hw hrw using hall
  refine ⟨w,?_,hrw⟩
  apply Finset.eq_of_subset_of_card_le
  · intro v hv
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hv
    exact hw i
  · rw [Finset.card_image_of_injective _ (word_injective hrw),Finset.card_univ,Fintype.card_fin,hcard]

lemma word_finite (hf : C.Finite) : (pseudoCubeOf C d r).Finite := by
  classical
  apply Set.Finite.of_injOn (f := fun w : Fin (d+1) → V => Finset.univ.image w)
    (t := C) (fun w hw => hw.1) ?_ hf
  intro w hw v hv he
  change Finset.univ.image w = Finset.univ.image v at he
  funext i
  have hi : w i ∈ Finset.univ.image v := by
    rw [← he]
    exact Finset.mem_image.mpr ⟨i,Finset.mem_univ i,rfl⟩
  obtain ⟨j,_,hji⟩ := Finset.mem_image.mp hi
  have hidx : j=i := by simpa [hw.2,hv.2] using congrArg r hji
  simpa [hidx] using hji.symm

lemma update_face (w : Fin (d+1) → V) (hw : Injective w) (i : Fin (d+1)) (u : V) :
    Finset.univ.image (Function.update w i u) = insert u ((Finset.univ.image w).erase (w i)) := by
  classical
  ext v
  constructor
  · intro hv
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hv
    by_cases hj : j=i
    · subst j;simp
    · simp only [Function.update_of_ne hj]
      exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨fun he => hj (hw he),Finset.mem_image.mpr ⟨j,Finset.mem_univ j,rfl⟩⟩)
  · intro hv
    rcases Finset.mem_insert.mp hv with rfl|hv
    · exact Finset.mem_image.mpr ⟨i,Finset.mem_univ i,by simp⟩
    · obtain ⟨hne,hv⟩ := Finset.mem_erase.mp hv
      obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hv
      have hj : j≠i := fun h => hne (congrArg w h)
      exact Finset.mem_image.mpr ⟨j,Finset.mem_univ j,by simp [hj]⟩

theorem good_pseudo (hC : IsGood C d) (hr : IsProperColoring C d r) :
    IsPseudoCube (pseudoCubeOf C d r) := by
  classical
  obtain ⟨hc,hfinite,hdim,hpure,hcolor,hrep⟩ := hC
  refine ⟨?_,word_finite hfinite,?_⟩
  · obtain ⟨f,hf,hcard⟩ := hdim.2
    obtain ⟨w,hw,hrw⟩ := face_word hc hr hf hcard
    exact ⟨w,by simpa [pseudoCubeOf,hw] using And.intro hf hrw⟩
  · intro w hw i
    obtain ⟨u,hu,hnew⟩ := hrep _ hw.1 (w i) (Finset.mem_image.mpr ⟨i,Finset.mem_univ i,rfl⟩)
    have hu_ne (j : Fin (d+1)) : u≠w j := by
      intro he
      apply hu
      rw [he]
      exact Finset.mem_image.mpr ⟨j,Finset.mem_univ j,rfl⟩
    have hru : r u=i := by
      by_contra hne
      have hj : w (r u) ∈ (Finset.univ.image w).erase (w i) :=
        Finset.mem_erase.mpr ⟨fun he => hne (word_injective hw.2 he),Finset.mem_image.mpr ⟨r u,Finset.mem_univ _,rfl⟩⟩
      have hedge : ({u,w (r u)} : Finset V) ∈ C := hc _ hnew _ (by
        simp only [Finset.insert_subset_iff,Finset.singleton_subset_iff]
        exact ⟨Finset.mem_insert_self _ _,Finset.mem_insert_of_mem hj⟩)
      exact hr u (w (r u)) (hu_ne _) hedge (hw.2 _).symm
    refine ⟨Function.update w i u,?_,by simpa using hu_ne i,?_⟩
    · constructor
      · rw [update_face w (word_injective hw.2) i u]
        exact hnew
      · intro j
        by_cases hj : j=i
        · subst j;simpa using hru
        · simpa [hj] using hw.2 j
    · intro j hj
      simp [hj]
end GoodBridge

theorem solution {V : Type*} (C : Set (Finset V)) (d : ℕ)
    (hC : MulticlassDS.NatGap.IsGood C d) (r : V → Fin (d+1))
    (hr : MulticlassDS.NatGap.IsProperColoring C d r) :
    MulticlassDS.NatGap.IsPseudoCube (MulticlassDS.NatGap.pseudoCubeOf C d r) :=
  GoodBridge.good_pseudo hC hr
#print axioms solution
