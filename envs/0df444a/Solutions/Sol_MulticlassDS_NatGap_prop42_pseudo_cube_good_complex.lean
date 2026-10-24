-- Prove2me | solution 1 for MulticlassDS.NatGap.prop42_pseudo_cube_good_complex
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-23T20:49:21.095502+00:00
-- url     : https://prove2.me/submissions/94bffcb6-d8a6-4640-b522-9aa86a9c6493

import Init
import Mathlib
import Definitions.Def_MulticlassDS_NatGap_Dimensions
import Definitions.Def_MulticlassDS_NatGap_Complexes

open Set Function Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace ConverseBridge
open MulticlassDS.NatGap
variable {Y : Type*} {d : ℕ}
def face (w : Fin (d+1) → Y) : Finset (Y × Fin (d+1)) :=
  Finset.univ.image (fun i => (w i,i))
lemma face_card (w : Fin (d+1) → Y) : (face w).card = d+1 := by
  rw [face,Finset.card_image_of_injective _ (fun i j h => congrArg Prod.snd h),Finset.card_univ,Fintype.card_fin]
lemma mem_face (w : Fin (d+1) → Y) (p : Y × Fin (d+1)) : p ∈ face w ↔ p.1=w p.2 := by
  constructor
  · intro hp
    obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hp
    exact (congrArg Prod.fst hi).symm.trans (congrArg w (congrArg Prod.snd hi))
  · intro h
    exact Finset.mem_image.mpr ⟨p.2,Finset.mem_univ _,Prod.ext h.symm rfl⟩

theorem pseudo_good (B : Set (Fin (d+1) → Y)) (hB : IsPseudoCube B) :
    IsGood (complexOf B) d := by
  classical
  letI : DecidableEq (Y × Fin (d+1)) := Classical.decEq _
  have hc : IsComplex (complexOf B) := by
    rintro f ⟨w,hw,hf⟩ g hg
    exact ⟨w,hw,hg.trans hf⟩
  have hfinite : (complexOf B).Finite := by
    have hf : (⋃ w ∈ B, (↑(face w).powerset : Set (Finset (Y × Fin (d+1))))).Finite :=
      hB.2.1.biUnion fun w hw => (face w).powerset.finite_toSet
    apply hf.subset
    rintro f ⟨w,hw,hf⟩
    exact Set.mem_iUnion.mpr ⟨w,Set.mem_iUnion.mpr ⟨hw,Finset.mem_powerset.mpr hf⟩⟩
  have hd : HasDim (complexOf B) d := by
    constructor
    · rintro f ⟨w,hw,hf⟩
      exact (Finset.card_le_card hf).trans_eq (face_card w)
    · obtain ⟨w,hw⟩ := hB.1
      exact ⟨face w,⟨w,hw,Finset.Subset.refl _⟩,face_card w⟩
  have hp : IsPure (complexOf B) d := by
    intro f hf hmax
    obtain ⟨w,hw,hf⟩ := hf
    rw [← hmax (face w) ⟨w,hw,Finset.Subset.refl _⟩ hf]
    exact face_card w
  have hr : IsProperColoring (complexOf B) d (fun p => p.2) := by
    intro u v hne hedge hcol
    change u.2=v.2 at hcol
    obtain ⟨w,hw,hsub⟩ := hedge
    have hu := (mem_face w u).mp (hsub (Finset.mem_insert_self _ _))
    have hv := (mem_face w v).mp (hsub (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))
    apply hne
    exact Prod.ext (by rw [hu,hv,hcol]) hcol
  refine ⟨hc,hfinite,hd,hp,⟨fun p => p.2,hr⟩,?_⟩
  rintro f ⟨w,hw,hf⟩ v hv
  obtain ⟨g,hg,hne,hagree⟩ := hB.2.2 w hw v.2
  have hvw := (mem_face w v).mp (hf hv)
  refine ⟨(g v.2,v.2),?_,g,hg,?_⟩
  · intro hmem
    have hh := (mem_face w (g v.2,v.2)).mp (hf hmem)
    exact hne hh
  · intro p hp
    rcases Finset.mem_insert.mp hp with rfl|hp
    · exact (mem_face g _).mpr rfl
    · obtain ⟨hpv,hpf⟩ := Finset.mem_erase.mp hp
      have hpw := (mem_face w p).mp (hf hpf)
      have hpi : p.2≠v.2 := by
        intro he
        apply hpv
        exact Prod.ext (by rw [hpw,hvw,he]) he
      exact (mem_face g p).mpr (hpw.trans (hagree p.2 hpi).symm)
end ConverseBridge

theorem solution {Y : Type*} (d : ℕ) (B : Set (Fin (d+1) → Y))
    (hB : MulticlassDS.NatGap.IsPseudoCube B) :
    MulticlassDS.NatGap.IsGood (MulticlassDS.NatGap.complexOf B) d :=
  ConverseBridge.pseudo_good B hB
#print axioms solution
