-- Prove2me | solution 1 for MulticlassDS.NatGap.prop43_natarajan_square
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-23T20:53:28.373292+00:00
-- url     : https://prove2.me/submissions/d5b28f2b-c365-46e4-b837-e03397dab292

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

theorem prior_good {V : Type*} (C : Set (Finset V)) (d : ℕ)
    (hC : MulticlassDS.NatGap.IsGood C d) (r : V → Fin (d+1))
    (hr : MulticlassDS.NatGap.IsProperColoring C d r) :
    MulticlassDS.NatGap.IsPseudoCube (MulticlassDS.NatGap.pseudoCubeOf C d r) :=
  GoodBridge.good_pseudo hC hr
#print axioms prior_good

open Set Function Classical
open scoped ENNReal
noncomputable section
namespace SquareBound
open MulticlassDS.NatGap
variable {V : Type*} {C : Set (Finset V)} {d : ℕ} {r : V → Fin (d+1)}

lemma pair_edge (hc : IsComplex C) {w : Fin (d+1) → V} (hw : w ∈ pseudoCubeOf C d r)
    (i j : Fin (d+1)) : ({w i,w j} : Finset V) ∈ C := by
  apply hc _ hw.1
  simp only [Finset.insert_subset_iff,Finset.singleton_subset_iff]
  exact ⟨Finset.mem_image.mpr ⟨i,Finset.mem_univ i,rfl⟩,Finset.mem_image.mpr ⟨j,Finset.mem_univ j,rfl⟩⟩

lemma two_patterns {n : ℕ} {B : Set (Fin (d+1) → V)} {S : Fin n → Fin (d+1)}
    {f g : Fin n → V} (h : ∀ c : Fin n → Bool,(fun i => if c i then f i else g i) ∈ proj B S)
    (i j : Fin n) (hne : i≠j) (a b : Bool) :
    ∃ w ∈ B, w (S i) = (if a then f i else g i) ∧ w (S j) = (if b then f j else g j) := by
  obtain ⟨w,hw,he⟩ := h (Function.update (fun _ => b) i a)
  refine ⟨w,hw,?_,?_⟩
  · simpa [Function.comp_apply] using congrFun he i
  · simpa [Function.comp_apply,Function.update_of_ne hne.symm] using congrFun he j

lemma shattered_square (hc : IsComplex C) (hr : IsProperColoring C d r)
    {n : ℕ} (hn : 2 ≤ n) (S : Fin n → Fin (d+1))
    (hS : NShatters (pseudoCubeOf C d r) S) :
    ∃ a b c e : V, IsEmptySquare C a b c e ∧ r a = r c ∧ r b = r e := by
  obtain ⟨f,g,hfg,hpat⟩ := hS
  let i : Fin n := ⟨0,by omega⟩
  let j : Fin n := ⟨1,by omega⟩
  have hij : i≠j := by intro he;have := congrArg Fin.val he;dsimp [i,j] at this;omega
  obtain ⟨w0,hw0,h0i,h0j⟩ := two_patterns hpat i j hij true true
  obtain ⟨w1,hw1,h1i,h1j⟩ := two_patterns hpat i j hij false true
  obtain ⟨w2,hw2,h2i,h2j⟩ := two_patterns hpat i j hij false false
  obtain ⟨w3,hw3,h3i,h3j⟩ := two_patterns hpat i j hij true false
  simp only [Bool.false_eq_true,ite_false,ite_true] at h0i h0j h1i h1j h2i h2j h3i h3j
  have hSi : S i≠S j := by
    intro he
    have h0 : f i=f j := by rw [← h0i,← h0j,he]
    have h1 : g i=f j := by rw [← h1i,← h1j,he]
    exact hfg i (h0.trans h1.symm)
  have hfci : r (f i)=S i := by rw [← h0i];exact hw0.2 _
  have hfcj : r (f j)=S j := by rw [← h0j];exact hw0.2 _
  have hgci : r (g i)=S i := by rw [← h2i];exact hw2.2 _
  have hgcj : r (g j)=S j := by rw [← h2j];exact hw2.2 _
  have hab : f i≠f j := fun he => hSi (hfci.symm.trans ((congrArg r he).trans hfcj))
  have had : f i≠g j := fun he => hSi (hfci.symm.trans ((congrArg r he).trans hgcj))
  have hbc : f j≠g i := fun he => hSi ((hgci.symm.trans ((congrArg r he).symm.trans hfcj)))
  have hcd : g i≠g j := fun he => hSi (hgci.symm.trans ((congrArg r he).trans hgcj))
  refine ⟨f i,f j,g i,g j,?_,hfci.trans hgci.symm,hfcj.trans hgcj.symm⟩
  refine ⟨⟨?_,?_,?_,?_,?_⟩,?_,?_⟩
  · simp [List.nodup_cons,hab,hfg i,had,hbc,hfg j,hcd]
  · simpa only [h0i,h0j] using pair_edge hc hw0 (S i) (S j)
  · simpa only [h1i,h1j] using pair_edge hc hw1 (S j) (S i)
  · simpa only [h2i,h2j] using pair_edge hc hw2 (S i) (S j)
  · simpa only [h3i,h3j] using pair_edge hc hw3 (S j) (S i)
  · intro hedge
    exact hr _ _ (hfg i) hedge (hfci.trans hgci.symm)
  · intro hedge
    exact hr _ _ (hfg j) hedge (hfcj.trans hgcj.symm)

theorem bound (hC : IsGood C d) (hsq : NoEmptySquares C)
    (hr : IsProperColoring C d r) : natarajanDim (pseudoCubeOf C d r) ≤ 1 := by
  apply iSup_le
  intro n
  apply iSup_le
  intro S
  apply iSup_le
  intro hS
  have hn : n ≤ 1 := by
    by_contra h
    have hn : 2 ≤ n := by omega
    obtain ⟨a,b,c,e,hce,_,_⟩ := shattered_square hC.1 hr hn S hS
    exact hsq a b c e hce
  exact_mod_cast hn
end SquareBound

theorem prior_nosquare {V : Type*} (C : Set (Finset V)) (d : ℕ)
    (hC : MulticlassDS.NatGap.IsGood C d) (hsq : MulticlassDS.NatGap.NoEmptySquares C) :
    ∀ r : V → Fin (d+1), MulticlassDS.NatGap.IsProperColoring C d r →
      MulticlassDS.NatGap.natarajanDim (MulticlassDS.NatGap.pseudoCubeOf C d r) ≤ 1 := by
  intro r hr
  exact SquareBound.bound hC hsq hr
#print axioms prior_nosquare

open Set Function Classical
noncomputable section
namespace SquareBridge
open MulticlassDS.NatGap
variable {V : Type*} {C : Set (Finset V)} {d : ℕ} {r : V → Fin (d+1)}

lemma extend_face (hC : IsGood C d) {f : Finset V} (hf : f ∈ C) :
    ∃ g ∈ C, f ⊆ g ∧ g.card=d+1 := by
  let T : Set (Finset V) := {g | g ∈ C ∧ f ⊆ g}
  have hT : T.Finite := hC.2.1.subset (fun g hg => hg.1)
  obtain ⟨g,hg,hmax⟩ := Set.exists_max_image T Finset.card hT ⟨f,hf,Finset.Subset.refl _⟩
  refine ⟨g,hg.1,hg.2,hC.2.2.2.1 g hg.1 ?_⟩
  intro k hk hgk
  exact (Finset.eq_of_subset_of_card_le hgk (hmax k ⟨hk,hg.2.trans hgk⟩)).symm

lemma edge_word (hC : IsGood C d) (hr : IsProperColoring C d r)
    (a b : V) (he : ({a,b} : Finset V) ∈ C) :
    ∃ w ∈ pseudoCubeOf C d r, w (r a)=a ∧ w (r b)=b := by
  obtain ⟨f,hf,hsub,hcard⟩ := extend_face hC he
  obtain ⟨w,hw,hcolor⟩ := GoodBridge.face_word hC.1 hr hf hcard
  have hget : ∀ v ∈ f, w (r v)=v := by
    intro v hv
    rw [← hw] at hv
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hv
    rw [hcolor]
  refine ⟨w,⟨by rw [hw];exact hf,hcolor⟩,hget a (hsub (Finset.mem_insert_self _ _)),
    hget b (hsub (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))⟩

theorem square_shatters (hC : IsGood C d) (hr : IsProperColoring C d r)
    {a b c e : V} (hsq : IsSquare C a b c e) (hac : r a=r c) (hbe : r b=r e) :
    2 ≤ natarajanDim (pseudoCubeOf C d r) := by
  obtain ⟨hnd,hab,hbc,hce,hea⟩ := hsq
  have hneac : a≠c := by intro he;subst c;simpa using hnd
  have hnebe : b≠e := by intro he;subst e;simpa using hnd
  obtain ⟨w0,hw0,h0i,h0j⟩ := edge_word hC hr a b hab
  obtain ⟨w1,hw1,h1i,h1j⟩ := edge_word hC hr c b (by simpa [Finset.pair_comm] using hbc)
  obtain ⟨w2,hw2,h2i,h2j⟩ := edge_word hC hr c e hce
  obtain ⟨w3,hw3,h3i,h3j⟩ := edge_word hC hr a e (by simpa [Finset.pair_comm] using hea)
  rw [← hac] at h1i h2i
  rw [← hbe] at h2j h3j
  let S : Fin 2 → Fin (d+1) := ![r a,r b]
  let f : Fin 2 → V := ![a,b]
  let g : Fin 2 → V := ![c,e]
  have hsh : NShatters (pseudoCubeOf C d r) S := by
    refine ⟨f,g,?_,?_⟩
    · intro k
      fin_cases k
      · exact hneac
      · exact hnebe
    · intro z
      cases hz0 : z 0 <;> cases hz1 : z 1
      · exact ⟨w2,hw2,by funext k;fin_cases k <;> simp [S,f,g,Function.comp_apply,hz0,hz1,h2i,h2j]⟩
      · exact ⟨w1,hw1,by funext k;fin_cases k <;> simp [S,f,g,Function.comp_apply,hz0,hz1,h1i,h1j]⟩
      · exact ⟨w3,hw3,by funext k;fin_cases k <;> simp [S,f,g,Function.comp_apply,hz0,hz1,h3i,h3j]⟩
      · exact ⟨w0,hw0,by funext k;fin_cases k <;> simp [S,f,g,Function.comp_apply,hz0,hz1,h0i,h0j]⟩
  exact le_iSup_of_le 2 (le_iSup_of_le S (le_iSup_of_le hsh le_rfl))

theorem equivalence (hC : IsGood C d) (hr : IsProperColoring C d r) :
    (∃ a b c e : V, IsSquare C a b c e ∧ r a=r c ∧ r b=r e) ↔
      2 ≤ natarajanDim (pseudoCubeOf C d r) := by
  constructor
  · rintro ⟨a,b,c,e,hsq,hac,hbe⟩
    exact square_shatters hC hr hsq hac hbe
  · intro hd
    by_contra hnone
    have hu : natarajanDim (pseudoCubeOf C d r) ≤ 1 := by
      apply iSup_le
      intro n
      apply iSup_le
      intro S
      apply iSup_le
      intro hS
      have hn : n≤1 := by
        by_contra hh
        obtain ⟨a,b,c,e,hce,hac,hbe⟩ := SquareBound.shattered_square hC.1 hr (by omega) S hS
        exact hnone ⟨a,b,c,e,hce.1,hac,hbe⟩
      exact_mod_cast hn
    have hh : (2 : ℕ∞) ≤ 1 := hd.trans hu
    norm_num at hh
end SquareBridge

theorem solution {V : Type*} (C : Set (Finset V)) (d : ℕ)
    (hC : MulticlassDS.NatGap.IsGood C d) (r : V → Fin (d+1))
    (hr : MulticlassDS.NatGap.IsProperColoring C d r) :
    (∃ a b c e : V, MulticlassDS.NatGap.IsSquare C a b c e ∧ r a=r c ∧ r b=r e) ↔
      2 ≤ MulticlassDS.NatGap.natarajanDim (MulticlassDS.NatGap.pseudoCubeOf C d r) :=
  SquareBridge.equivalence hC hr
#print axioms solution
