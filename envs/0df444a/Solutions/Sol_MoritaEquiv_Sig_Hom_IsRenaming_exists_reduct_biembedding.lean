-- Prove2me | solution 1 for MoritaEquiv.Sig.Hom.IsRenaming.exists_reduct_biembedding
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-10-13T20:05:36.567519+00:00
-- url     : https://prove2.me/submissions/10e82f2c-5875-46ae-ae20-8c0fd9190715

import Mathlib
import Definitions.Def_MoritaEquiv_defs
import Theorems.Thm_MoritaEquiv_ElemEmb_exists_of_sortwise_equiv

open CategoryTheory

namespace MoritaEquiv
namespace RNE

variable {L L' : Sig} {F : L.Hom L'}

/-- the pushforward structure along a renaming -/
noncomputable def push (hF : F.IsRenaming) (N : Str L) : Str L' where
  carrier s := N.carrier ((Equiv.ofBijective _ hF.srt).symm s)
  funMap {m dom s} f xs :=
    N.funMap ((Equiv.ofBijective _ (hF.func (dom := (Equiv.ofBijective _ hF.srt).symm ∘ dom)
      (s := (Equiv.ofBijective _ hF.srt).symm s))).symm
      (cast (by
        have h1 : F.onSrt ∘ ((Equiv.ofBijective _ hF.srt).symm ∘ dom) = dom :=
          funext fun j => (Equiv.ofBijective _ hF.srt).apply_symm_apply (dom j)
        have h2 : F.onSrt ((Equiv.ofBijective _ hF.srt).symm s) = s :=
          (Equiv.ofBijective _ hF.srt).apply_symm_apply s
        rw [h1, h2]) f)) xs
  relMap {m dom} r xs :=
    N.relMap ((Equiv.ofBijective _ (hF.rel (dom := (Equiv.ofBijective _ hF.srt).symm ∘ dom))).symm
      (cast (by
        have h1 : F.onSrt ∘ ((Equiv.ofBijective _ hF.srt).symm ∘ dom) = dom :=
          funext fun j => (Equiv.ofBijective _ hF.srt).apply_symm_apply (dom j)
        rw [h1]) r)) xs
  nonempty _ := N.nonempty _

theorem funMap_cast (hF : F.IsRenaming) (N : Str L) {m : ℕ} :
    ∀ {dom₁ dom : Fin m → L.Srt} {s₁ s : L.Srt} (hd : dom₁ = dom) (hs : s₁ = s)
      (f₁ : L.Func m dom₁ s₁) (f : L.Func m dom s)
      (H : L'.Func m (F.onSrt ∘ dom) (F.onSrt s) = L'.Func m (F.onSrt ∘ dom₁) (F.onSrt s₁)),
      F.onFunc f₁ = cast H (F.onFunc f) →
      ∀ (xs : (j : Fin m) → N.carrier (dom₁ j)),
      cast (congrArg N.carrier hs) (N.funMap f₁ xs) =
        N.funMap f (fun j => cast (congrArg N.carrier (congrFun hd j)) (xs j)) := by
  intro dom₁ dom s₁ s hd hs f₁ f H hf xs
  subst hd hs
  have : f₁ = f := (hF.func).1 hf
  subst this
  rfl

theorem relMap_cast (hF : F.IsRenaming) (N : Str L) {m : ℕ} :
    ∀ {dom₁ dom : Fin m → L.Srt} (hd : dom₁ = dom)
      (r₁ : L.Rel m dom₁) (r : L.Rel m dom)
      (H : L'.Rel m (F.onSrt ∘ dom) = L'.Rel m (F.onSrt ∘ dom₁)),
      F.onRel r₁ = cast H (F.onRel r) →
      ∀ (xs : (j : Fin m) → N.carrier (dom₁ j)),
      N.relMap r₁ xs ↔ N.relMap r (fun j => cast (congrArg N.carrier (congrFun hd j)) (xs j)) := by
  intro dom₁ dom hd r₁ r H hr xs
  subst hd
  have : r₁ = r := (hF.rel).1 hr
  subst this
  rfl

theorem rne_main {L L' : Sig} {F : L.Hom L'} (hF : F.IsRenaming) (N : Str L) :
    ∃ M : Str L', Nonempty (ElemEmb (M.reduct F) N) ∧ Nonempty (ElemEmb N (M.reduct F)) := by
  let e := Equiv.ofBijective _ hF.srt
  have hsa : ∀ s, e.symm (F.onSrt s) = s := fun s => e.symm_apply_apply s
  let E : ∀ s, ((push hF N).reduct F).carrier s ≃ N.carrier s :=
    fun s => Equiv.cast (congrArg N.carrier (hsa s))
  have hf : ∀ {m : ℕ} {dom : Fin m → L.Srt} {s : L.Srt} (f : L.Func m dom s)
      (xs : (j : Fin m) → ((push hF N).reduct F).carrier (dom j)),
      E s (((push hF N).reduct F).funMap f xs) = N.funMap f (fun j => E _ (xs j)) := by
    intro m dom s f xs
    exact funMap_cast hF N (funext fun j => hsa (dom j)) (hsa s) _ f _
      ((Equiv.ofBijective_apply_symm_apply _ _ _).trans rfl) xs
  have hr : ∀ {m : ℕ} {dom : Fin m → L.Srt} (r : L.Rel m dom)
      (xs : (j : Fin m) → ((push hF N).reduct F).carrier (dom j)),
      N.relMap r (fun j => E _ (xs j)) ↔ ((push hF N).reduct F).relMap r xs := by
    intro m dom r xs
    exact (relMap_cast hF N (funext fun j => hsa (dom j)) _ r _
      ((Equiv.ofBijective_apply_symm_apply _ _ _).trans rfl) xs).symm
  obtain ⟨h, -⟩ := ElemEmb.exists_of_sortwise_equiv E hf hr
  obtain ⟨h', -⟩ := ElemEmb.exists_of_sortwise_equiv (A := N) (B := (push hF N).reduct F)
    (fun s => (E s).symm)
    (fun {m dom s} f xs => by
      apply (E s).injective
      rw [Equiv.apply_symm_apply, hf]
      congr 1; funext j; simp)
    (fun {m dom} r xs => by
      rw [← hr]; congr!; simp)
  exact ⟨push hF N, ⟨h⟩, ⟨h'⟩⟩

end RNE
end MoritaEquiv

open MoritaEquiv in
theorem solution {L L' : Sig} {F : L.Hom L'}
    (hF : F.IsRenaming) (N : Str L) :
    ∃ M : Str L', Nonempty (ElemEmb (M.reduct F) N) ∧ Nonempty (ElemEmb N (M.reduct F)) :=
  MoritaEquiv.RNE.rne_main hF N
