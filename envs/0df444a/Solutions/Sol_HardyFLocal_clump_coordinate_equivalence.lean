-- Prove2me | solution 1 for HardyFLocal.clump_coordinate_equivalence
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-22T01:01:39.941917+00:00
-- url     : https://prove2.me/submissions/58564b97-9f95-4476-b7c2-178e2e464680

import Mathlib
import Definitions.Def_HardyFLocal_ClumpCausaloid
import Theorems.Thm_HardyFLocal_eq20_two_qubit_expansion
open HardyCausaloid
namespace HardyFLocal
open HardyCausaloid

variable {m n : ℕ}
private theorem label_basis_coordinates (S : FiducialFamily)
    (L : ∀ x : X m n, Ω × Ω → Label (Setting m n) (Outcome m n) x) (hL : IsFiducialLabels S L)
    (x : X m n) (p : Ω × Ω) :
    elemCoeff S (labelOp (L x p)) = Pi.single p 1 := by
  classical
  have h := (eq20_two_qubit_expansion S).1 _ ((L x p).1.cp (L x p).2)
  symm
  apply ((eq20_two_qubit_expansion S).2 _ h).2
  simp [Pi.single_apply]
  exact hL x p

private theorem labels_injective (S : FiducialFamily)
    (L : ∀ x : X m n, Ω × Ω → Label (Setting m n) (Outcome m n) x) (hL : IsFiducialLabels S L)
    (x : X m n) : Function.Injective (L x) := by
  intro p p' h
  have hv := (label_basis_coordinates S L hL x p).symm.trans
    ((congrArg (fun α => elemCoeff S (labelOp α)) h).trans (label_basis_coordinates S L hL x p'))
  by_contra hp
  simpa [Pi.single_apply, hp, Ne.symm hp] using congrFun hv p

open Classical in
private noncomputable def labelEquiv (S : FiducialFamily)
    (L : ∀ x : X m n, Ω × Ω → Label (Setting m n) (Outcome m n) x) (hL : IsFiducialLabels S L)
    (x : X m n) : Ω × Ω ≃ omegaOne L x :=
  Equiv.ofBijective (fun p => ⟨L x p, Finset.mem_image.mpr ⟨p,Finset.mem_univ _,rfl⟩⟩) ⟨
    fun _ _ h => labels_injective S L hL x (congrArg Subtype.val h), by
      rintro ⟨l,hl⟩
      obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp hl
      exact ⟨p,rfl⟩⟩


end HardyFLocal

open HardyFLocal

open Classical in
theorem solution {m n : ℕ} (S : FiducialFamily)
    (L : ∀ x : X m n, Ω × Ω → Label (Setting m n) (Outcome m n) x) (hL : IsFiducialLabels S L)
    (O : Finset (X m n)) :
    ∃ e : omegaC L O ≃ ({i : O × Bool // IsClumpStart O
      (if i.2 then Sum.inl i.1.val.1 else Sum.inr i.1.val.2) i.1.val} → Ω),
      ∀ k i, e k i = (if i.val.2 then (famPairs L O k.val i.val.1.val).1
        else (famPairs L O k.val i.val.1.val).2) := by
  classical
  let I := {i : O × Bool // IsClumpStart O (if i.2 then Sum.inl i.1.val.1 else Sum.inr i.1.val.2) i.1.val}
  let read (k : omegaC L O) (i : I) : Ω := if i.val.2 then (famPairs L O k.val i.val.1.val).1 else
    (famPairs L O k.val i.val.1.val).2
  let p (a : I → Ω) (x : O) : Ω × Ω :=
    (if h : IsClumpStart O (.inl x.val.1) x.val then a ⟨(x,true),h⟩ else 0,
     if h : IsClumpStart O (.inr x.val.2) x.val then a ⟨(x,false),h⟩ else 0)
  let labels (a : I → Ω) (x : O) := labelEquiv S L hL x.val (p a x)
  have decodeLabels (a : I → Ω) (x : O) : famPairs L O (labels a) x.val = p a x := by
    simp only [famPairs,x.property,↓reduceDIte]
    exact Function.leftInverse_invFun (labels_injective S L hL x.val) _
  let build (a : I → Ω) : omegaC L O := ⟨labels a,Finset.mem_filter.mpr ⟨Finset.mem_univ _,by
    intro x hx
    rw [decodeLabels a ⟨x,hx⟩]
    exact ⟨fun hh => dif_neg hh,fun hh => dif_neg hh⟩⟩⟩
  refine ⟨⟨read,build,?_,?_⟩,fun _ _ => rfl⟩
  · intro k
    apply Subtype.ext
    funext x
    have cond := (Finset.mem_filter.mp k.property).2 x.val x.property
    have hp : p (read k) x = famPairs L O k.val x.val := by
      apply Prod.ext
      · by_cases hh : IsClumpStart O (.inl x.val.1) x.val
        · simp [p,hh,read]
        · simpa [p,hh] using (cond.1 hh).symm
      · by_cases hh : IsClumpStart O (.inr x.val.2) x.val
        · simp [p,hh,read]
        · simpa [p,hh] using (cond.2 hh).symm
    change labelEquiv S L hL x.val (p (read k) x) = k.val x
    rw [hp]
    obtain ⟨b,hb⟩ := (labelEquiv S L hL x.val).surjective (k.val x)
    simp only [famPairs,x.property,↓reduceDIte,← hb]
    have hi : decode L x.val ((labelEquiv S L hL x.val b).val) = b :=
      Function.leftInverse_invFun (labels_injective S L hL x.val) b
    simp [hi]
  · intro a
    funext i
    obtain ⟨⟨x,b⟩,hi⟩ := i
    cases b <;> simp_all [read,build,p] <;> exact dif_pos hi

