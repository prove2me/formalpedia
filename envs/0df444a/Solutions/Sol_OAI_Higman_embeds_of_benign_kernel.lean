-- Prove2me | solution 1 for OAI.Higman.embeds_of_benign_kernel
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T19:50:14.17676+00:00
-- url     : https://prove2.me/submissions/4c8a14fd-0fd8-4dba-8139-4a3c7934eecd

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
-- module Solutions.OAIQW_UniversalFInfinity.RopeTrick
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u v w x

namespace Higman.RopeTrick

section
open Monoid Coprod Multiplicative

section Container
variable {ι : Type u} {K : Type v} [Group K]

theorem finitelyPresented [Finite ι] [Group.IsFinitelyPresented K]
    (α β : FreeGroup ι →* K) : Group.IsFinitelyPresented (Container α β) := by
  let := Higman.finitelyPresented_prod (G := K) (H := FreeGroup ι)
  exact Group.IsFinitelyPresented.quotient _ ⟨Set.range (relation α β),Set.finite_range _,rfl⟩

lemma relation_zero (α β : FreeGroup ι →* K) (j : ι ⊕ ι) :
    proj α β (relation α β j) = 1 :=
  (QuotientGroup.eq_one_iff _).mpr (Subgroup.subset_normalClosure ⟨j,rfl⟩)

lemma generator_zero (α β : FreeGroup ι →* K) (j : ι) :
    stable α β * kMap α β (α (FreeGroup.of j)) =
      kMap α β (α (FreeGroup.of j)) * stable α β := by
  apply mul_inv_eq_one.mp
  simpa only [proj,relation,map_mul,map_inv,kMap,stable,MonoidHom.comp_apply] using
    relation_zero α β (.inl j)

lemma generator_one (α β : FreeGroup ι →* K) (j : ι) :
    stable α β * kMap α β (β (FreeGroup.of j)) =
      kMap α β (β (FreeGroup.of j)) * fMap α β (FreeGroup.of j) * stable α β := by
  apply mul_inv_eq_one.mp
  simpa only [proj,relation,map_mul,map_inv,kMap,fMap,stable,MonoidHom.comp_apply] using
    relation_zero α β (.inr j)

lemma conjugate_zero (α β : FreeGroup ι →* K) (w : FreeGroup ι) :
    stable α β * kMap α β (α w) * (stable α β)⁻¹ = kMap α β (α w) := by
  have hh : (MulAut.conj (stable α β)).toMonoidHom.comp ((kMap α β).comp α) =
      (kMap α β).comp α := by
    apply FreeGroup.ext_hom
    intro j
    change stable α β * kMap α β (α (FreeGroup.of j)) * (stable α β)⁻¹ = _
    rw [generator_zero,mul_inv_cancel_right]
    rfl
  exact DFunLike.congr_fun hh w

lemma pair_eq (α β : FreeGroup ι →* K) (k : K) (w : FreeGroup ι) :
    proj α β (Coprod.inl (k,w)) = kMap α β k * fMap α β w := by
  change proj α β (Coprod.inl (k,w)) =
    proj α β (Coprod.inl (k,1)) * proj α β (Coprod.inl (1,w))
  rw [← map_mul,← map_mul]
  simp

lemma conjugate_one (α β : FreeGroup ι →* K) (w : FreeGroup ι) :
    stable α β * kMap α β (β w) * (stable α β)⁻¹ =
      kMap α β (β w) * fMap α β w := by
  let p : FreeGroup ι →* Container α β :=
    ((proj α β).comp Coprod.inl).comp (β.prod (MonoidHom.id _))
  have hh : (MulAut.conj (stable α β)).toMonoidHom.comp ((kMap α β).comp β) = p := by
    apply FreeGroup.ext_hom
    intro j
    change stable α β * kMap α β (β (FreeGroup.of j)) * (stable α β)⁻¹ =
      proj α β (Coprod.inl (β (FreeGroup.of j),FreeGroup.of j))
    rw [generator_one,mul_inv_cancel_right,pair_eq]
  have h := DFunLike.congr_fun hh w
  change stable α β * kMap α β (β w) * (stable α β)⁻¹ =
    proj α β (Coprod.inl (β w,w)) at h
  rwa [pair_eq] at h

lemma kills_relation (α β : FreeGroup ι →* K) (w : FreeGroup ι) (hw : α w = β w) :
    fMap α β w = 1 := by
  have h0 := conjugate_zero α β w
  rw [hw,conjugate_one] at h0
  exact mul_left_cancel (h0.trans (mul_one _).symm)

end Container

end

open Monoid Coprod Multiplicative
noncomputable section
variable {ι : Type u} {A : Type v} {K : Type w} {G : Type x}
variable [Group A] [Group K] [Group G]
variable (i : A →* K) (hi : Function.Injective i) (r : A →* G)
variable (q : FreeGroup ι →* G)

variable (p₀ p₁ : FreeGroup ι →* A)
variable (h₀ : ∀ w, r (p₀ w) = 1) (h₁ : ∀ w, r (p₁ w) = q w)

include hi h₀ h₁ in

theorem embeds_quotient [Finite ι] [Group.IsFinitelyPresented K]
    (hq : Function.Surjective q)
    (hident : ∀ w ∈ q.ker, i (p₀ w) = i (p₁ w)) :
    ∃ (Q : Type (max u w)) (_ : Group Q) (_ : Group.IsFinitelyPresented Q),
      ∃ j : G →* Q, Function.Injective j := by
  let α := i.comp p₀
  let β := i.comp p₁
  have hk : q.ker ≤ (fMap α β).ker := by
    intro w hw
    exact kills_relation α β w (hident w hw)
  let j : G →* Container α β := q.liftOfSurjective hq ⟨fMap α β,hk⟩
  have hj (w : FreeGroup ι) : j (q w) = fMap α β w := by
    exact MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _
  let d := detect i hi r q p₀ p₁ h₀ h₁
  have hd (g : G) : d (j g) = HNNExtension.of (1,g) := by
    obtain ⟨w,rfl⟩ := hq g
    rw [hj]
    exact detect_fMap i hi r q p₀ p₁ h₀ h₁ w
  refine ⟨Container α β,inferInstance,finitelyPresented α β,j,?_⟩
  intro g h he
  have hh := congrArg d he
  rw [hd,hd] at hh
  exact congrArg Prod.snd (HNNExtension.of_injective (φ := associated i hi r) hh)

end
end Higman.RopeTrick

namespace Higman
variable {G : Type u} [Group G]

namespace Double
lemma firstIn_eq_secondIn {A : Subgroup G} {g : G} (hg : g ∈ A) :
    firstIn A g = secondIn A g := by
  apply Subtype.ext
  exact HNNExtension.equiv_eq_conj (φ := MulEquiv.refl A) ⟨g,hg⟩
end Double

theorem embeds_of_benign_kernel_oai {ι : Type u} [Finite ι]
    {D : Type v} [Group D] (q : FreeGroup ι →* D) (hq : Function.Surjective q)
    (hben : IsBenign q.ker) :
    ∃ (K : Type u) (_ : Group K) (_ : Group.IsFinitelyPresented K)
      (i : D →* K), Function.Injective i := by
  obtain ⟨K,_,_,i,hi,B,hB,hBi⟩ := hben
  let E := CentralExtension K B
  have : Group.IsFinitelyPresented E := CentralExtension.finitelyPresented hB
  let j := CentralExtension.map i (le_of_eq hBi.symm)
  have hj : Function.Injective j := CentralExtension.map_injective i hi hBi
  let A := Double.subgroup q.ker
  let jA : A →* E := j.comp A.subtype
  have hjA : Function.Injective jA := hj.comp Subtype.val_injective
  let r := Double.read q (le_refl q.ker)
  exact RopeTrick.embeds_quotient jA hjA r q
    (Double.firstIn q.ker) (Double.secondIn q.ker)
    (Double.read_first q (le_refl q.ker))
    (Double.read_second q (le_refl q.ker)) hq
    (fun w hw ↦ congrArg jA (Double.firstIn_eq_secondIn hw))

end Higman

end OAI
end

theorem solution.{u, v} : type_of% @OAI.Higman.embeds_of_benign_kernel_oai.{u, v} := @OAI.Higman.embeds_of_benign_kernel_oai.{u, v}
