-- Prove2me | solution 1 for OAI.Higman.benign_iff_centralExtension_embeds
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T19:48:47.348293+00:00
-- url     : https://prove2.me/submissions/b3c6ef0e-f850-4aa5-917b-365a5b319a4d

import Mathlib
import Definitions.Def_OAIQWUFI004

section
-- module Solutions.OAIQW_UniversalFInfinity.CentralHNN
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section UniversalFinitelyPresentedProof
universe u v w x

namespace Higman
open HNNExtension

namespace CentralExtension
variable {G : Type u} [Group G] {K : Type v} [Group K]
variable {A : Subgroup G} {B : Subgroup K}

open Monoid Coprod Multiplicative

theorem con_finitelyNormallyGenerated (hA : A.FG) :
    (HNNExtension.con G A A (MulEquiv.refl A)).subgroup.IsFinitelyNormallyGenerated := by
  classical
  obtain ⟨S, hS⟩ := hA
  let C := HNNExtension.con G A A (MulEquiv.refl A)
  let N : Subgroup (G ∗ Multiplicative ℤ) :=
    Subgroup.normalClosure (relation '' (S : Set G))
  let Q := (G ∗ Multiplicative ℤ) ⧸ N
  let q : G ∗ Multiplicative ℤ →* Q := QuotientGroup.mk' N
  let f : G →* Q := q.comp inl
  let t : Q := q (inr (ofAdd 1))
  let e : G →* Q := (MulAut.conj t).toMonoidHom.comp f
  have hgen : (S : Set G) ⊆ f.eqLocus e := by
    intro g hg
    have hh : q (relation g) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.subset_normalClosure ⟨g, hg, rfl⟩)
    have he : t * f g = f g * t := by
      apply mul_inv_eq_one.mp
      exact hh
    change f g = t * f g * t⁻¹
    rw [he, mul_inv_cancel_right]
  have hAeq : A ≤ f.eqLocus e := by
    rw [← hS]
    exact (Subgroup.closure_le _).mpr hgen
  have hC : C ≤ Con.ker q := by
    apply Con.conGen_le.mpr
    rintro _ _ ⟨a, rfl, rfl⟩
    change t * f a = f a * t
    have ha : f a = t * f a * t⁻¹ := hAeq a.2
    nth_rw 2 [ha]
    simp only [inv_mul_cancel_right]
  refine ⟨relation '' (S : Set G), S.finite_toSet.image _, ?_⟩
  change N = C.subgroup
  apply le_antisymm
  · apply Subgroup.normalClosure_le_normal
    rintro _ ⟨g, hg, rfl⟩
    have hgA : g ∈ A := by rw [← hS]; exact Subgroup.subset_closure hg
    have hr : C (inr (ofAdd 1) * inl g) (inl g * inr (ofAdd 1)) :=
      ConGen.Rel.of _ _ ⟨⟨g, hgA⟩, rfl, rfl⟩
    change C (relation g) 1
    have hh := C.mul hr (C.refl (inl g * inr (ofAdd 1))⁻¹)
    have hcancel : (inl g * inr (ofAdd 1) : G ∗ Multiplicative ℤ) *
        (inl g * inr (ofAdd 1))⁻¹ = 1 := mul_inv_cancel _
    rw [hcancel] at hh
    exact hh
  · intro x hx
    apply (QuotientGroup.eq_one_iff _).mp
    exact (hC hx).trans (map_one q)

theorem finitelyPresented [Group.IsFinitelyPresented G] (hA : A.FG) :
    Group.IsFinitelyPresented (CentralExtension G A) := by
  let C := HNNExtension.con G A A (MulEquiv.refl A)
  have hC := con_finitelyNormallyGenerated hA
  have hfp := Group.IsFinitelyPresented.quotient C.subgroup hC
  change Group.IsFinitelyPresented C.Quotient
  rw [← QuotientGroup.con_subgroup C]
  exact hfp

end CentralExtension
end Higman

end UniversalFinitelyPresentedProof

end OAI
end

section
-- module Solutions.OAIQW_UniversalFInfinity.Benign
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section UniversalFinitelyPresentedProof
universe u v w x

namespace Higman.HNN
open HNNExtension
variable {G : Type*} [Group G] {A B : Subgroup G} (φ : A ≃* B)

theorem conj_mem_range_iff (g : G) :
    (t * of g * t⁻¹ : HNNExtension G A B φ) ∈ of.range ↔ g ∈ A := by
  constructor
  · intro h
    by_contra hg
    let w : NormalWord.ReducedWord G A B :=
      { head := 1
        toList := [(1,g),(-1,1)]
        chain := by simp [hg] }
    have hp : w.prod φ = t * of g * t⁻¹ := by
      simp [NormalWord.ReducedWord.prod,w]
    have hn := HNNExtension.ReducedWord.toList_eq_nil_of_mem_of_range φ w (hp ▸ h)
    simp [w] at hn
  · intro hg
    rw [← equiv_eq_conj (φ := φ) ⟨g,hg⟩]
    exact ⟨_,rfl⟩

theorem commute_t_iff (g : G) :
    Commute (t : HNNExtension G A A (MulEquiv.refl A)) (of g) ↔ g ∈ A := by
  constructor
  · intro h
    apply (conj_mem_range_iff (MulEquiv.refl A) g).mp
    rw [h.eq,mul_inv_cancel_right]
    exact ⟨g,rfl⟩
  · intro hg
    exact t_mul_of (φ := MulEquiv.refl A) ⟨g,hg⟩

end Higman.HNN

namespace Higman
variable {G : Type u} [Group G] {A : Subgroup G}

theorem benign_iff_centralExtension_embeds_oai : IsBenign A ↔
    ∃ (K : Type u) (_ : Group K) (_ : Group.IsFinitelyPresented K)
      (j : CentralExtension G A →* K), Function.Injective j := by
  constructor
  · rintro ⟨K,_,_,i,hi,B,hB,hBi⟩
    exact ⟨CentralExtension K B,inferInstance,CentralExtension.finitelyPresented hB,
      CentralExtension.map i (le_of_eq hBi.symm),
      CentralExtension.map_injective i hi hBi⟩
  · rintro ⟨K,_,_,j,hj⟩
    obtain ⟨n,p,hp,_⟩ := Group.IsFinitelyPresented.out (G := K)
    have : Group.FG K := Group.fg_of_surjective hp
    let i : G →* K := j.comp HNNExtension.of
    let t : K := j HNNExtension.t
    let k : G →* K × K := i.prod ((MulAut.conj t).toMonoidHom.comp i)
    let d : K →* K × K := (MonoidHom.id K).prod (MonoidHom.id K)
    have hd : d.range.FG := by
      rw [MonoidHom.range_eq_map]
      obtain ⟨S,hS⟩ := (Group.FG.out : (⊤ : Subgroup K).FG)
      refine (Subgroup.fg_iff _).mpr ⟨d '' (S : Set K),?_,S.finite_toSet.image d⟩
      rw [← MonoidHom.map_closure,hS]
    refine ⟨K × K,inferInstance,finitelyPresented_prod,k,?_,d.range,hd,?_⟩
    · intro x y he
      exact HNNExtension.of_injective (φ := MulEquiv.refl A)
        (hj (congrArg Prod.fst he))
    · ext g
      change (∃ z, d z = k g) ↔ g ∈ A
      constructor
      · rintro ⟨z,hz⟩
        have h₀ : z = i g := congrArg Prod.fst hz
        have h₁ : z = t * i g * t⁻¹ := congrArg Prod.snd hz
        have he : (HNNExtension.t : CentralExtension G A) * HNNExtension.of g *
            HNNExtension.t⁻¹ = HNNExtension.of g := by
          apply hj
          simpa only [i,t,MonoidHom.comp_apply,map_mul,map_inv] using h₁.symm.trans h₀
        apply (HNN.commute_t_iff g).mp
        change HNNExtension.t * HNNExtension.of g = HNNExtension.of g * HNNExtension.t
        calc
          HNNExtension.t * HNNExtension.of g =
              ((HNNExtension.t * HNNExtension.of g) * HNNExtension.t⁻¹) *
                (HNNExtension.t : CentralExtension G A) := (inv_mul_cancel_right _ _).symm
          _ = HNNExtension.of g * HNNExtension.t := congrArg (fun x : CentralExtension G A ↦
            x * HNNExtension.t) he
      · intro hg
        refine ⟨i g,?_⟩
        apply Prod.ext
        · rfl
        · change i g = t * i g * t⁻¹
          have he := HNNExtension.equiv_eq_conj (φ := MulEquiv.refl A) ⟨g,hg⟩
          simpa only [i,t,MonoidHom.comp_apply,map_mul,map_inv,MulEquiv.refl_apply] using
            congrArg j he

end Higman

end UniversalFinitelyPresentedProof

end OAI
end

theorem solution.{u} : type_of% @OAI.Higman.benign_iff_centralExtension_embeds_oai.{u} := @OAI.Higman.benign_iff_centralExtension_embeds_oai.{u}
