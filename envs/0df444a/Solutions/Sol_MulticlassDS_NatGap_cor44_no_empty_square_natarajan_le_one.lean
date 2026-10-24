-- Prove2me | solution 1 for MulticlassDS.NatGap.cor44_no_empty_square_natarajan_le_one
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-23T20:52:10.835464+00:00
-- url     : https://prove2.me/submissions/d8fa4ed9-07e4-4153-91f5-4f351c3cddbb

import Init
import Mathlib
import Definitions.Def_MulticlassDS_NatGap_Dimensions
import Definitions.Def_MulticlassDS_NatGap_Complexes

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

theorem solution {V : Type*} (C : Set (Finset V)) (d : ℕ)
    (hC : MulticlassDS.NatGap.IsGood C d) (hsq : MulticlassDS.NatGap.NoEmptySquares C) :
    ∀ r : V → Fin (d+1), MulticlassDS.NatGap.IsProperColoring C d r →
      MulticlassDS.NatGap.natarajanDim (MulticlassDS.NatGap.pseudoCubeOf C d r) ≤ 1 := by
  intro r hr
  exact SquareBound.bound hC hsq hr
#print axioms solution
