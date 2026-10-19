-- Prove2me | solution 1 for OAI.Higman.NormalWords.benign_normalClosure
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T19:48:03.866746+00:00
-- url     : https://prove2.me/submissions/dceb3da1-3ce5-4ce9-901f-c1414a607e8f

import Mathlib
import Definitions.Def_OAIQWUFI004
import Theorems.Thm_OAI_Higman_benign_iff_centralExtension_embeds
import Theorems.Thm_OAI_Higman_embeds_of_benign_kernel

section
-- module Solutions.OAIQW_UniversalFInfinity.Benign
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section UniversalFinitelyPresentedProof
universe u v w x

namespace Higman
variable {G : Type u} [Group G] {A : Subgroup G}

theorem embeds_of_benign_kernel_fp {D : Type v} [Group D]
    [Group.IsFinitelyPresented G] (q : G →* D) (hq : Function.Surjective q)
    (hben : IsBenign q.ker) :
    ∃ (K : Type u) (_ : Group K) (_ : Group.IsFinitelyPresented K)
      (i : D →* K), Function.Injective i := by
  obtain ⟨n,p,hp,_⟩ := Group.IsFinitelyPresented.out (G := G)
  let p' : FreeGroup (ULift.{u} (Fin n)) →* G := p.comp (FreeGroup.map ULift.down)
  have hp' : Function.Surjective p' := hp.comp
    (FreeGroup.map_surjective (fun a ↦ ⟨ULift.up a,rfl⟩))
  apply embeds_of_benign_kernel (q.comp p') (hq.comp hp')
  exact hben.comap p'

end Higman

namespace Higman.CentralExtension
open Monoid Coprod Multiplicative
variable {G : Type u} [Group G] (A : Subgroup G)

theorem rawProjection_ker : (rawProjection A).ker =
    Subgroup.normalClosure (relation '' (A : Set G)) := by
  let C := HNNExtension.con G A A (MulEquiv.refl A)
  let N := Subgroup.normalClosure (relation '' (A : Set G))
  let q := QuotientGroup.mk' N
  have hC : C ≤ Con.ker q := by
    apply Con.conGen_le.mpr
    rintro _ _ ⟨a,rfl,rfl⟩
    apply mul_inv_eq_one.mp
    have hh : q (relation (a : G)) = 1 := (QuotientGroup.eq_one_iff (relation (a : G))).mpr
      (Subgroup.subset_normalClosure (show relation (a : G) ∈ relation '' (A : Set G) from
        ⟨a,a.2,rfl⟩))
    simpa only [relation,map_mul,map_inv,MulEquiv.refl_apply] using hh
  apply le_antisymm
  · intro x hx
    apply (QuotientGroup.eq_one_iff _).mp
    apply (hC ?_).trans (map_one q)
    apply (Con.eq C).mp
    exact hx.trans (map_one C.mk').symm
  · apply Subgroup.normalClosure_le_normal
    rintro _ ⟨g,hg,rfl⟩
    change rawProjection A (relation g) = 1
    change (HNNExtension.t * HNNExtension.of g) *
      (HNNExtension.of g * (HNNExtension.t : CentralExtension G A))⁻¹ = 1
    rw [HNNExtension.t_mul_of (φ := MulEquiv.refl A) ⟨g,hg⟩]
    exact mul_inv_cancel _

variable {H : Type u} [Group H]

theorem rawMap_surjective (f : G →* H) (hf : Function.Surjective f) :
    Function.Surjective (Coprod.map f (MonoidHom.id (Multiplicative ℤ))) := by
  apply MonoidHom.range_eq_top.mp
  rw [Coprod.range_eq]
  have h₀ : ((Coprod.map f (MonoidHom.id (Multiplicative ℤ))).comp inl).range =
      (inl : H →* H ∗ Multiplicative ℤ).range := by
    change ((inl : H →* H ∗ Multiplicative ℤ).comp f).range = _
    rw [MonoidHom.range_comp,MonoidHom.range_eq_top.mpr hf,← MonoidHom.range_eq_map]
  rw [h₀]
  exact Coprod.range_inl_sup_range_inr

theorem rawProjection_ker_map (f : G →* H) (hf : Function.Surjective f) :
    (rawProjection A).ker.map (Coprod.map f (MonoidHom.id (Multiplicative ℤ))) =
      (rawProjection (A.map f)).ker := by
  rw [rawProjection_ker,rawProjection_ker,
    Subgroup.map_normalClosure _ _ (rawMap_surjective f hf)]
  congr 1
  ext x
  constructor
  · rintro ⟨_,⟨g,hg,rfl⟩,rfl⟩
    refine ⟨f g,⟨g,hg,rfl⟩,?_⟩
    simp [relation]
  · rintro ⟨_,⟨g,hg,rfl⟩,rfl⟩
    refine ⟨relation g,⟨g,hg,rfl⟩,?_⟩
    simp [relation]

end Higman.CentralExtension

namespace Higman.IsBenign
open Monoid Coprod Multiplicative
variable {G H : Type u} [Group G] [Group H]
  [Group.IsFinitelyPresented G] [Group.IsFinitelyPresented H]
  {A : Subgroup G}

theorem map_surjective (hA : IsBenign A) (f : G →* H) (hf : Function.Surjective f) :
    IsBenign (A.map f) := by
  obtain ⟨K,_,_,j,hj⟩ := benign_iff_centralExtension_embeds.mp hA
  let π := CentralExtension.rawProjection A
  let F := Coprod.map f (MonoidHom.id (Multiplicative ℤ))
  let k : G ∗ Multiplicative ℤ →* K × (H ∗ Multiplicative ℤ) := (j.comp π).prod F
  let i : H ∗ Multiplicative ℤ →* K × (H ∗ Multiplicative ℤ) :=
    (1 : H ∗ Multiplicative ℤ →* K).prod (MonoidHom.id _)
  have hi : Function.Injective i := by
    intro x y he
    exact congrArg Prod.snd he
  have hk : k.range.FG := by
    obtain ⟨n,p,hp,_⟩ := Group.IsFinitelyPresented.out (G := G ∗ Multiplicative ℤ)
    have : Group.FG (G ∗ Multiplicative ℤ) := Group.fg_of_surjective hp
    obtain ⟨S,hS⟩ := (Group.FG.out : (⊤ : Subgroup (G ∗ Multiplicative ℤ)).FG)
    refine (Subgroup.fg_iff _).mpr ⟨k '' (S : Set (G ∗ Multiplicative ℤ)),?_,
      S.finite_toSet.image k⟩
    rw [← MonoidHom.map_closure,hS,← MonoidHom.range_eq_map]
  have hker : k.range.comap i = (CentralExtension.rawProjection (A.map f)).ker := by
    rw [← CentralExtension.rawProjection_ker_map A f hf]
    ext x
    change (∃ y, k y = i x) ↔ ∃ y, π y = 1 ∧ F y = x
    constructor
    · rintro ⟨y,hy⟩
      refine ⟨y,?_,congrArg Prod.snd hy⟩
      apply hj
      exact (congrArg Prod.fst hy).trans (map_one j).symm
    · rintro ⟨y,hy,hxy⟩
      refine ⟨y,Prod.ext ?_ hxy⟩
      change j (π y) = 1
      rw [hy,map_one]
  have hben : IsBenign (CentralExtension.rawProjection (A.map f)).ker :=
    ⟨K × (H ∗ Multiplicative ℤ),inferInstance,finitelyPresented_prod,i,hi,k.range,hk,hker⟩
  apply benign_iff_centralExtension_embeds.mpr
  exact embeds_of_benign_kernel_fp (CentralExtension.rawProjection (A.map f))
    Con.mk'_surjective hben

end Higman.IsBenign

namespace Higman.HNNTransport
open HNNExtension
variable {G : Type u} [Group G] {K : Type v} [Group K]
  {A B : Subgroup G} {C D : Subgroup K} (φ : A ≃* B) (ψ : C ≃* D)
  (i : G →* K) (hA : C.comap i = A) (hB : D.comap i = B)
  (hφ : ∀ a : A, i (φ a) = ψ ⟨i a,show i a ∈ C from hA.symm ▸ a.2⟩)

include hB

theorem range_comap_of : (map φ ψ i hA hφ).range.comap HNNExtension.of = i.range := by
  ext k
  constructor
  · rintro ⟨x,hx⟩
    have hm : map φ ψ i hA hφ x ∈ HNNExtension.of.range := ⟨k,hx.symm⟩
    obtain ⟨g,rfl⟩ := mem_base_of_map_mem_base φ ψ i hA hB hφ x hm
    refine ⟨g,?_⟩
    apply HNNExtension.of_injective (φ := ψ)
    simpa using hx
  · rintro ⟨g,rfl⟩
    exact ⟨HNNExtension.of g,map_of φ ψ i hA hφ g⟩

end Higman.HNNTransport

namespace Higman.HNNSubgroup
open HNNExtension
variable {G : Type u} [Group G] {A B : Subgroup G} (φ : A ≃* B)
  (S : Subgroup G) (hS : ∀ a : A, (φ a : G) ∈ S ↔ (a : G) ∈ S)

theorem range_comap_of : (inclusion φ S hS).range.comap HNNExtension.of = S := by
  exact (HNNTransport.range_comap_of (restricted φ S hS) φ S.subtype rfl rfl
    (fun _ ↦ rfl)).trans (Subgroup.range_subtype S)

include hS

theorem closure_comap_of :
    (Subgroup.closure (HNNExtension.of '' (S : Set G) ∪
      {(HNNExtension.t : HNNExtension G A B φ)})).comap HNNExtension.of = S := by
  apply le_antisymm
  · have hle : Subgroup.closure (HNNExtension.of '' (S : Set G) ∪
        {(HNNExtension.t : HNNExtension G A B φ)}) ≤ (inclusion φ S hS).range := by
      apply (Subgroup.closure_le _).mpr
      rintro _ (⟨s,hs,rfl⟩ | ht)
      · exact ⟨HNNExtension.of ⟨s,hs⟩,inclusion_of φ S hS ⟨s,hs⟩⟩
      · obtain rfl := Set.mem_singleton_iff.mp ht
        exact ⟨HNNExtension.t,inclusion_t φ S hS⟩
    exact (Subgroup.comap_mono hle).trans_eq (range_comap_of φ S hS)
  · intro s hs
    exact Subgroup.subset_closure (Or.inl ⟨s,hs,rfl⟩)

end Higman.HNNSubgroup

end UniversalFinitelyPresentedProof

end OAI
end

section
-- module Solutions.OAIQW_UniversalFInfinity.FiniteHNN
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u v w x

namespace Higman.HNN
open Monoid Coprod Multiplicative
variable {G : Type u} [Group G] {A B : Subgroup G} (φ : A ≃* B)

theorem con_finitelyNormallyGenerated (hA : A.FG) :
    (HNNExtension.con G A B φ).subgroup.IsFinitelyNormallyGenerated := by
  classical
  have : Group.FG A := (Group.fg_iff_subgroup_fg A).mpr hA
  obtain ⟨S,hS⟩ := (Group.FG.out : (⊤ : Subgroup A).FG)
  let C := HNNExtension.con G A B φ
  let N : Subgroup (G ∗ Multiplicative ℤ) :=
    Subgroup.normalClosure (relation φ '' (S : Set A))
  let Q := (G ∗ Multiplicative ℤ) ⧸ N
  let q : G ∗ Multiplicative ℤ →* Q := QuotientGroup.mk' N
  let f : G →* Q := q.comp inl
  let t : Q := q (inr (ofAdd 1))
  let f₀ : A →* Q := (MulAut.conj t).toMonoidHom.comp (f.comp A.subtype)
  let f₁ : A →* Q := f.comp (B.subtype.comp φ.toMonoidHom)
  have hgen : (S : Set A) ⊆ f₀.eqLocus f₁ := by
    intro a ha
    have hr : q (relation φ a) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.subset_normalClosure ⟨a,ha,rfl⟩)
    have he : t * f a = f (φ a) * t := mul_inv_eq_one.mp hr
    change t * f a * t⁻¹ = f (φ a)
    rw [he,mul_inv_cancel_right]
  have heq : f₀ = f₁ := by
    apply MonoidHom.ext
    intro a
    have hh : (⊤ : Subgroup A) ≤ f₀.eqLocus f₁ := by
      rw [← hS]
      exact (Subgroup.closure_le _).mpr hgen
    exact hh (Subgroup.mem_top a)
  have hC : C ≤ Con.ker q := by
    apply Con.conGen_le.mpr
    rintro _ _ ⟨a,rfl,rfl⟩
    change t * f a = f (φ a) * t
    have he : t * f a * t⁻¹ = f (φ a) := DFunLike.congr_fun heq a
    rw [← he, inv_mul_cancel_right]
  refine ⟨relation φ '' (S : Set A), S.finite_toSet.image _, ?_⟩
  change N = C.subgroup
  apply le_antisymm
  · apply Subgroup.normalClosure_le_normal
    rintro _ ⟨a,_,rfl⟩
    have hr : C (inr (ofAdd 1) * inl (a : G))
        (inl (φ a : G) * inr (ofAdd 1)) := ConGen.Rel.of _ _ ⟨a,rfl,rfl⟩
    change C (relation φ a) 1
    have hh := C.mul hr (C.refl (inl (φ a : G) * inr (ofAdd 1))⁻¹)
    simpa only [relation, mul_inv_cancel] using hh
  · intro x hx
    apply (QuotientGroup.eq_one_iff _).mp
    exact (hC hx).trans (map_one q)

theorem finitelyPresented [Group.IsFinitelyPresented G] (hA : A.FG) :
    Group.IsFinitelyPresented (HNNExtension G A B φ) := by
  let C := HNNExtension.con G A B φ
  have hfp := Group.IsFinitelyPresented.quotient C.subgroup
    (con_finitelyNormallyGenerated φ hA)
  change Group.IsFinitelyPresented C.Quotient
  rw [← QuotientGroup.con_subgroup C]
  exact hfp

end Higman.HNN

namespace Higman

namespace PartialIso
variable {G : Type u} [Group G] {K : Type u} [Group K]

theorem invariant_map (p : PartialIso G) (i : G →* K) (hi : Function.Injective i)
    (R : Subgroup G) (S : Subgroup K) (he : S.comap i = R) (h : p.Invariant R) :
    (p.map i hi).Invariant S := by
  intro a
  obtain ⟨b,rfl⟩ := (p.source.equivMapOfInjective i hi).surjective a
  rw [map_equiv]
  change (p.equiv b : G) ∈ S.comap i ↔ (b : G) ∈ S.comap i
  rw [he]
  exact h b

end PartialIso
namespace FiniteHNN
variable {G : Type u} [Group G] [Group.IsFinitelyPresented G]

theorem realization (ps : List (PartialIso G))
    (hfg : ∀ p ∈ ps, p.source.FG) (R : Subgroup G)
    (hinv : ∀ p ∈ ps, p.Invariant R) :
    ∃ (K : Type u) (_ : Group K) (_ : Group.IsFinitelyPresented K)
      (i : G →* K), Function.Injective i ∧
      ∃ T : Set K, T.Finite ∧
        (Subgroup.closure (i '' (R : Set G) ∪ T)).comap i = R ∧
        ∀ p ∈ ps, ∃ t ∈ T, ∀ a : p.source,
          i (p.equiv a) = t * i a * t⁻¹ := by
  induction ps with
  | nil =>
    refine ⟨G,inferInstance,inferInstance,MonoidHom.id G,Function.injective_id,
      ∅,Set.finite_empty,?_,?_⟩
    · simp
    · simp
  | cons p ps ih =>
    obtain ⟨K,_,_,i,hi,T,hT,hR,hrel⟩ := ih
      (fun q hq ↦ hfg q (List.mem_cons_of_mem p hq))
      (fun q hq ↦ hinv q (List.mem_cons_of_mem p hq))
    let q := p.map i hi
    let E := HNNExtension K q.source q.target q.equiv
    let j : K →* E := HNNExtension.of
    let i' := j.comp i
    let C := Subgroup.closure (i '' (R : Set G) ∪ T)
    let T' : Set E := j '' T ∪ {HNNExtension.t}
    have hqfg : q.source.FG := by
      obtain ⟨S,hS⟩ := hfg p (List.mem_cons_self)
      refine (Subgroup.fg_iff _).mpr ⟨i '' (S : Set G),?_,S.finite_toSet.image i⟩
      rw [← MonoidHom.map_closure,hS]
      rfl
    have hCinv : q.Invariant C :=
      p.invariant_map i hi R C hR (hinv p (List.mem_cons_self))
    have hC : (Subgroup.closure (j '' (C : Set K) ∪ {HNNExtension.t})).comap j = C :=
      HNNSubgroup.closure_comap_of q.equiv C hCinv
    have hclosure : Subgroup.closure (i' '' (R : Set G) ∪ T') =
        Subgroup.closure (j '' (C : Set K) ∪ {HNNExtension.t}) := by
      conv_rhs => rw [Subgroup.closure_union,← MonoidHom.map_closure j (C : Set K),Subgroup.closure_eq]
      change Subgroup.closure (i' '' (R : Set G) ∪ T') =
        C.map j ⊔ Subgroup.closure {HNNExtension.t}
      rw [show C.map j = Subgroup.closure (j '' (i '' (R : Set G) ∪ T)) from
        MonoidHom.map_closure j _]
      rw [← Subgroup.closure_union]
      congr 1
      simp only [T',Set.image_union,Set.image_image,Set.union_assoc,i',MonoidHom.coe_comp]
      rfl
    refine ⟨E,inferInstance,HNN.finitelyPresented q.equiv hqfg,i',
      (HNNExtension.of_injective (φ := q.equiv)).comp hi,T',
      (hT.image j).union (Set.finite_singleton _),?_,?_⟩
    · rw [hclosure]
      change ((Subgroup.closure (j '' (C : Set K) ∪ {HNNExtension.t})).comap j).comap i = R
      rw [hC]
      exact hR
    · intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · refine ⟨HNNExtension.t,Or.inr rfl,?_⟩
        intro b
        have he := HNNExtension.equiv_eq_conj (φ := q.equiv)
          (a.source.equivMapOfInjective i hi b)
        simpa only [q,PartialIso.map_equiv,i',j,MonoidHom.comp_apply,
          Subgroup.coe_equivMapOfInjective_apply] using he
      · obtain ⟨t,ht,he⟩ := hrel a ha
        refine ⟨j t,Or.inl ⟨t,ht,rfl⟩,?_⟩
        intro b
        simpa only [i',MonoidHom.comp_apply,map_mul,map_inv] using congrArg j (he b)

end FiniteHNN

namespace PartialIso
variable {G : Type u} [Group G]

theorem invariant_sInf (p : PartialIso G) (C : Set (Subgroup G))
    (hC : ∀ S ∈ C, p.Invariant S) : p.Invariant (sInf C) := by
  intro a
  simp only [Subgroup.mem_sInf]
  exact forall₂_congr fun S hS ↦ hC S hS a

end PartialIso
namespace Orbit
variable {G : Type u} [Group G]

theorem subset (ps : List (PartialIso G)) (S : Set G) :
    S ⊆ subgroup ps S := by
  intro x hx
  exact Subgroup.mem_sInf.mpr (fun R hR ↦ hR.1 hx)

theorem invariant (ps : List (PartialIso G)) (S : Set G) (p : PartialIso G)
    (hp : p ∈ ps) : p.Invariant (subgroup ps S) :=
  p.invariant_sInf _ (fun _ hR ↦ hR.2 p hp)

theorem minimal (ps : List (PartialIso G)) (S : Set G) (R : Subgroup G)
    (hS : S ⊆ R) (hR : ∀ p ∈ ps, p.Invariant R) : subgroup ps S ≤ R :=
  sInf_le ⟨hS,hR⟩

theorem benign [Group.IsFinitelyPresented G] (ps : List (PartialIso G))
    (hfg : ∀ p ∈ ps, p.source.FG) (S : Set G) (hS : S.Finite) :
    IsBenign (subgroup ps S) := by
  let R := subgroup ps S
  obtain ⟨K,_,_,i,hi,T,hT,hR,hrel⟩ := FiniteHNN.realization ps hfg R
    (fun p hp ↦ invariant ps S p hp)
  let B := Subgroup.closure (i '' S ∪ T)
  have hB : B.FG := (Subgroup.fg_iff _).mpr ⟨i '' S ∪ T, rfl, (hS.image i).union hT⟩
  refine ⟨K,inferInstance,inferInstance,i,hi,B,hB,?_⟩
  apply le_antisymm
  · calc
      B.comap i ≤ (Subgroup.closure (i '' (R : Set G) ∪ T)).comap i :=
        Subgroup.comap_mono (Subgroup.closure_mono
          (Set.union_subset_union_left _ (Set.image_mono (subset ps S))))
      _ = R := hR
  · apply minimal ps S (B.comap i)
    · intro x hx
      exact Subgroup.subset_closure (Or.inl ⟨x,hx,rfl⟩)
    · intro p hp a
      obtain ⟨t,ht,he⟩ := hrel p hp
      have htB : t ∈ B := Subgroup.subset_closure (Or.inr ht)
      change i (p.equiv a) ∈ B ↔ i a ∈ B
      rw [he a]
      constructor
      · intro ha
        have hh := B.mul_mem (B.mul_mem (B.inv_mem htB) ha) htB
        simpa only [inv_mul_cancel_left,mul_assoc,inv_mul_cancel,mul_one] using hh
      · intro ha
        exact B.mul_mem (B.mul_mem htB ha) (B.inv_mem htB)

end Orbit
end Higman

end OAI
end

section
-- module Solutions.OAIQW_UniversalFInfinity.Markers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section UniversalFinitelyPresentedProof
universe u v w x

namespace Higman.DecoratedMarker
open Monoid Coprod
variable {G : Type u} [Group G] {T : Type v} [Group T] {Q : Type w}

theorem inclusion_injective : Function.Injective (inclusion (G := G) (T := T) (Q := Q)) := by
  apply Function.Injective.of_comp (f := test)
  rw [← MonoidHom.coe_comp,test_comp]
  exact SemidirectProduct.inl_injective

end Higman.DecoratedMarker

end UniversalFinitelyPresentedProof

end OAI
end

section
-- module Solutions.OAIQW_UniversalFInfinity.MarkerMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u v w x

namespace Higman.FreeBasis

section
variable {X : Type*}

theorem erase_eq_self_iff (S : Set X) (g : FreeGroup X) : erase S g = g ↔ g ∈ span S := by
  classical
  constructor
  · intro hg
    have hle : (erase S).range ≤ span S := by
      rw [erase,FreeGroup.range_lift_eq_closure]
      apply (Subgroup.closure_le _).mpr
      rintro _ ⟨x,rfl⟩
      by_cases hx : x ∈ S
      · simp only [hx,ite_true]
        exact Subgroup.subset_closure ⟨x,hx,rfl⟩
      · simp only [hx,ite_false]
        exact Subgroup.one_mem _
    exact hle ⟨g,hg⟩
  · have hle : span S ≤ (erase S).eqLocus (MonoidHom.id _) := by
      apply (Subgroup.closure_le _).mpr
      rintro _ ⟨x,hx,rfl⟩
      change erase S (FreeGroup.of x) = FreeGroup.of x
      simp [hx]
    exact fun hg ↦ hle hg

theorem erase_comp (S T : Set X) : (erase S).comp (erase T) = erase (S ∩ T) := by
  classical
  apply FreeGroup.ext_hom
  intro x
  by_cases hxS : x ∈ S <;> by_cases hxT : x ∈ T <;> simp [hxS,hxT]

theorem span_inter (S T : Set X) : span S ⊓ span T = span (S ∩ T) := by
  apply le_antisymm
  · intro g hg
    apply (erase_eq_self_iff _ _).mp
    rw [← erase_comp]
    change erase S (erase T g) = g
    rw [(erase_eq_self_iff T g).mpr hg.2,(erase_eq_self_iff S g).mpr hg.1]
  · exact le_inf (Subgroup.closure_mono (Set.image_mono Set.inter_subset_left))
      (Subgroup.closure_mono (Set.image_mono Set.inter_subset_right))

end

variable {X : Type*} {G : Type*} [Group G]

theorem map_span_inf (d : FreeGroup X →* G) (r : G →* FreeGroup X)
    (hr : r.comp d = MonoidHom.id _) (U V : Set X) (A : Subgroup G)
    (hsupport : A.map r ≤ span U)
    (hletters : ∀ x ∈ U, d (FreeGroup.of x) ∈ A) :
    (span V).map d ⊓ A = (span (V ∩ U)).map d := by
  apply le_antisymm
  · rintro g ⟨⟨w,hw,rfl⟩,hA⟩
    refine ⟨w,?_,rfl⟩
    rw [← span_inter]
    refine ⟨hw,?_⟩
    have hh := hsupport (Subgroup.mem_map.mpr ⟨d w,hA,rfl⟩)
    change w ∈ span U
    simpa only [← MonoidHom.comp_apply,hr,MonoidHom.id_apply] using hh
  · apply le_inf
    · exact Subgroup.map_mono (Subgroup.closure_mono (Set.image_mono Set.inter_subset_left))
    · rw [span,MonoidHom.map_closure]
      apply (Subgroup.closure_le _).mpr
      rintro _ ⟨_,⟨x,hx,rfl⟩,rfl⟩
      exact hletters x hx.2

end Higman.FreeBasis

namespace Higman.DecoratedMarker
open Monoid Coprod
variable {G : Type u} [Group G] {T : Type v} [Group T] {Q : Type w}

theorem eq_inclusion_of_right_eq_one (x : Base G T Q) (hx : (test x).right = 1) :
    x = inclusion (test x).left := by
  apply (decomposition (G := G) (T := T) (Q := Q)).injective
  change test x = test (inclusion (test x).left)
  rw [← MonoidHom.comp_apply,test_comp]
  apply SemidirectProduct.ext
  · rfl
  · exact hx

end Higman.DecoratedMarker

namespace Higman.MarkerEmbedding

section
open Monoid Coprod DecoratedMarker
variable {G : Type u} [Group G] {D : Type v} [Group D]
    {T : Type w} [Group T] {P Q : Type*}

theorem kernel_intersection (f : D →* T) (hf : Function.Injective f)
    (o : P → T) (q : P → Q) (w : P → G) (R : Subgroup (Kernel G T Q)) :
    R.map inclusion ⊓ (embedding f o q w).range =
      (R ⊓ (kernelMap f o q w).range).map inclusion := by
  apply le_antisymm
  · rintro _ ⟨⟨a,ha,rfl⟩,⟨x,hx⟩⟩
    have hxright : (test x).right = 1 := by
      apply hf
      have he := congrArg (fun y : Base G T Q ↦ (test y).right) hx
      simp only [test_embedding,SemidirectProduct.map_right] at he
      rw [← MonoidHom.comp_apply,test_comp] at he
      simpa only [SemidirectProduct.right_inl,map_one] using he
    have hx' := eq_inclusion_of_right_eq_one x hxright
    refine ⟨a,⟨ha,?_⟩,rfl⟩
    refine ⟨(test x).left,?_⟩
    apply inclusion_injective
    rw [← embedding_inclusion,← hx']
    exact hx
  · rintro _ ⟨a,⟨ha,⟨x,hx⟩⟩,rfl⟩
    refine ⟨⟨a,ha,rfl⟩,inclusion x,?_⟩
    rw [embedding_inclusion,hx]

lemma projection_kernelMap (f : D →* T) (o : P → T) (q : P → Q) (w : P → G) :
    (Coprod.snd : Kernel G T Q →* FreeGroup (T × Q)).comp (kernelMap f o q w) =
      (FreeGroup.map (index f o q)).comp (Coprod.snd : Kernel G D P →* _) := by
  apply Coprod.hom_ext
  · apply MonoidHom.ext
    intro g
    simp
  · apply FreeGroup.ext_hom
    intro x
    simp

lemma range_projection_support (f : D →* T) (o : P → T) (q : P → Q) (w : P → G) :
    (kernelMap f o q w).range.map Coprod.snd ≤ FreeBasis.span (Set.range (index f o q)) := by
  rintro _ ⟨_,⟨x,rfl⟩,rfl⟩
  have he := DFunLike.congr_fun (projection_kernelMap f o q w) x
  change Coprod.snd (kernelMap f o q w x) ∈ FreeBasis.span (Set.range (index f o q))
  rw [show Coprod.snd (kernelMap f o q w x) = FreeGroup.map (index f o q) (Coprod.snd x) from he]
  have hm : FreeGroup.map (index f o q) (Coprod.snd x) ∈ (FreeGroup.map (index f o q)).range :=
    ⟨Coprod.snd x,rfl⟩
  simpa only [FreeGroup.range_map,FreeBasis.span] using hm

lemma decorated_letter_mem_range (f : D →* T) (o : P → T) (q : P → Q) (w : P → G)
    (v : T × Q → G) (x : T × Q) (hx : x ∈ Set.range (index f o q)) :
    DecoratedFreeBasis.inclusion v (FreeGroup.of x) ∈ (kernelMap f o q w).range := by
  obtain ⟨⟨d,p⟩,rfl⟩ := hx
  refine ⟨inl (v (index f o q (d,p)) * (w p)⁻¹) * inr (FreeGroup.of (d,p)),?_⟩
  simp [mul_assoc]

theorem decorated_kernel_intersection (f : D →* T) (o : P → T) (q : P → Q)
    (w : P → G) (v : T × Q → G) (V : Set (T × Q)) :
    (FreeBasis.span V).map (DecoratedFreeBasis.inclusion v) ⊓ (kernelMap f o q w).range =
      (FreeBasis.span (V ∩ Set.range (index f o q))).map (DecoratedFreeBasis.inclusion v) :=
  FreeBasis.map_span_inf (DecoratedFreeBasis.inclusion v) Coprod.snd
    (DecoratedFreeBasis.projection_comp v) (Set.range (index f o q)) V _
    (range_projection_support f o q w) (decorated_letter_mem_range f o q w v)

theorem decorated_intersection (f : D →* T) (hf : Function.Injective f)
    (o : P → T) (q : P → Q) (w : P → G) (v : T × Q → G) (V : Set (T × Q)) :
    decoratedSubgroup v V ⊓ (embedding f o q w).range =
      decoratedSubgroup v (V ∩ Set.range (index f o q)) := by
  rw [decoratedSubgroup,← Subgroup.map_map,kernel_intersection f hf o q w,
    decorated_kernel_intersection,Subgroup.map_map]
  rfl

theorem decoratedSubgroup_eq_closure (v : T × Q → G) (V : Set (T × Q)) :
    decoratedSubgroup v V =
      Subgroup.closure ((fun x : T × Q ↦ coefficient (v x) * marker x.1 x.2) '' V) := by
  rw [decoratedSubgroup,FreeBasis.span,MonoidHom.map_closure,Set.image_image]
  congr 1

end

open DecoratedMarker
variable {G : Type u} [Group G] {T : Type v} [Group T] {Q : Type w}
  {D : Type*} [Group D] {P : Type*}

lemma map_decoratedSubgroup (f : D →* T) (o : P → T) (q : P → Q) (w : P → G)
    (v : T × Q → G) (W : Set (D × P)) :
    (decoratedSubgroup (pullDecoration f o q w v) W).map (embedding f o q w) =
      decoratedSubgroup v (index f o q '' W) := by
  rw [decoratedSubgroup_eq_closure,MonoidHom.map_closure,decoratedSubgroup_eq_closure]
  simp only [Set.image_image,embedding_decorated]

theorem comap_decoratedSubgroup [Nonempty P] (f : D →* T) (hf : Function.Injective f)
    (o : P → T) (q : P → Q) (w : P → G) (hi : Function.Injective (index f o q))
    (v : T × Q → G) (V : Set (T × Q)) :
    (decoratedSubgroup v V).comap (embedding f o q w) =
      decoratedSubgroup (pullDecoration f o q w v) (index f o q ⁻¹' V) := by
  apply Subgroup.map_injective (embedding_injective f hf o q w hi)
  rw [Subgroup.map_comap_eq,inf_comm,decorated_intersection f hf,
    map_decoratedSubgroup,Set.image_preimage_eq_inter_range]

end Higman.MarkerEmbedding

namespace Higman.PartialIso
variable {H : Type u} [Group H] {G : Type u} [Group G]

lemma ofEmbeddings_invariant_iff (i j : H →* G) (hi : Function.Injective i)
    (hj : Function.Injective j) (R : Subgroup G) :
    (ofEmbeddings i j hi hj).Invariant R ↔ R.comap i = R.comap j := by
  constructor
  · intro h
    ext x
    simpa only [ofEmbeddings_apply,MonoidHom.ofInjective_apply,Subgroup.mem_comap] using
      (h (MonoidHom.ofInjective hi x)).symm
  · intro h a
    obtain ⟨x,rfl⟩ := (MonoidHom.ofInjective hi).surjective a
    rw [ofEmbeddings_apply]
    change x ∈ R.comap j ↔ x ∈ R.comap i
    rw [h]

end Higman.PartialIso
namespace Higman.MarkerMachine
open DecoratedMarker MarkerEmbedding

attribute [instance] Edge.domainGroup
variable {G T Q : Type u} [Group G] [Group T]

namespace Edge
variable (e : Edge G T Q)

lemma inputMap_decorated (v : G) (d : e.Domain) :
    e.inputMap (coefficient v * marker d ()) =
      coefficient v * marker (e.input d).1 (e.input d).2 := by
  simp [inputMap,input]

lemma outputMap_decorated (v : G) (d : e.Domain) :
    e.outputMap (coefficient v * marker d ()) =
      coefficient (v * e.weight) * marker (e.output d).1 (e.output d).2 := by
  simp [outputMap,output,map_mul,mul_assoc]

end Edge
end Higman.MarkerMachine

namespace Higman.MarkerEmbedding
open DecoratedMarker
variable {G : Type u} [Group G] {T : Type v} [Group T] {Q : Type w}

lemma decoratedSubgroup_congr {v w : T × Q → G} {V : Set (T × Q)}
    (h : ∀ x ∈ V, v x = w x) : decoratedSubgroup v V = decoratedSubgroup w V := by
  rw [decoratedSubgroup_eq_closure,decoratedSubgroup_eq_closure]
  congr 1
  apply Set.image_congr
  intro x hx
  rw [h x hx]

end Higman.MarkerEmbedding
namespace Higman.MarkerMachine.Edge
open DecoratedMarker MarkerEmbedding
variable {G T Q : Type u} [Group G] [Group T] (e : Edge G T Q)

theorem invariant (v : T × Q → G) (V : Set (T × Q))
    (hV : ∀ d, e.input d ∈ V ↔ e.output d ∈ V)
    (hv : ∀ d, e.input d ∈ V → v (e.output d) = v (e.input d) * e.weight) :
    e.partialIso.Invariant (decoratedSubgroup v V) := by
  rw [partialIso,PartialIso.ofEmbeddings_invariant_iff]
  unfold inputMap outputMap
  rw [comap_decoratedSubgroup e.inputLinear e.input_injective _ _ _ e.input_index_injective,
    comap_decoratedSubgroup e.outputLinear e.output_injective _ _ _ e.output_index_injective]
  have he : index e.inputLinear (fun _ : Unit ↦ e.inputOffset) (fun _ ↦ e.inputState) ⁻¹' V =
      index e.outputLinear (fun _ : Unit ↦ e.outputOffset) (fun _ ↦ e.outputState) ⁻¹' V := by
    ext x
    exact hV x.1
  rw [← he]
  apply decoratedSubgroup_congr
  rintro ⟨d,p⟩ hd
  change v (e.input d) * (1 : G)⁻¹ = v (e.output d) * e.weight⁻¹
  change e.input d ∈ V at hd
  rw [hv d hd]
  simp

lemma invariant_decorated_iff (R : Subgroup (Base G T Q)) (hR : e.partialIso.Invariant R)
    (a : G) (d : e.Domain) :
    coefficient (a * e.weight) * marker (e.output d).1 (e.output d).2 ∈ R ↔
      coefficient a * marker (e.input d).1 (e.input d).2 ∈ R := by
  have hh := hR (MonoidHom.ofInjective e.inputMap_injective (coefficient a * marker d ()))
  change ((PartialIso.ofEmbeddings e.inputMap e.outputMap _ _).equiv
    (MonoidHom.ofInjective e.inputMap_injective (coefficient a * marker d ())) :
    Base G T Q) ∈ R ↔ _ at hh
  simpa only [PartialIso.ofEmbeddings_apply,MonoidHom.ofInjective_apply,
    inputMap_decorated,outputMap_decorated] using hh

lemma source_fg [Group.IsFinitelyPresented G] [Group.IsFinitelyPresented e.Domain] :
    e.partialIso.source.FG := by
  have : Group.IsFinitelyPresented (G × e.Domain) := finitelyPresented_prod
  obtain ⟨n,p,hp,_⟩ := Group.IsFinitelyPresented.out (G := Base G e.Domain Unit)
  have : Group.FG (Base G e.Domain Unit) := Group.fg_of_surjective hp
  exact (Group.fg_iff_subgroup_fg e.inputMap.range).mp inferInstance

end Higman.MarkerMachine.Edge

namespace Higman.MarkerMachine
open DecoratedMarker MarkerEmbedding
variable {G T Q : Type u} [Group G] [Group T]

lemma reach_iff (es : List (Edge G T Q)) (seed : T × Q) (e : Edge G T Q) (he : e ∈ es)
    (d : e.Domain) : Reach es seed (e.input d) ↔ Reach es seed (e.output d) :=
  ⟨Reach.forward e he d,Reach.backward e he d⟩

theorem orbit_eq (es : List (Edge G T Q)) (seed : T × Q) (v : T × Q → G)
    (hv : ∀ e ∈ es, ∀ d, Reach es seed (e.input d) →
      v (e.output d) = v (e.input d) * e.weight) :
    Orbit.subgroup (es.map Edge.partialIso) {word v seed} =
      decoratedSubgroup v {c | Reach es seed c} := by
  apply le_antisymm
  · apply Orbit.minimal
    · rintro x (rfl : x = word v seed)
      rw [decoratedSubgroup_eq_closure]
      exact Subgroup.subset_closure ⟨seed,Reach.start,rfl⟩
    · intro p hp
      obtain ⟨e,he,rfl⟩ := List.mem_map.mp hp
      exact e.invariant v _ (reach_iff es seed e he) (hv e he)
  · rw [decoratedSubgroup_eq_closure]
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨c,hc,rfl⟩
    change word v c ∈ Orbit.subgroup (es.map Edge.partialIso) {word v seed}
    induction hc with
    | start => exact Orbit.subset _ _ (Set.mem_singleton _)
    | forward e he d hr ih =>
      have hinv := Orbit.invariant (es.map Edge.partialIso) {word v seed} e.partialIso
        (List.mem_map.mpr ⟨e,he,rfl⟩)
      change coefficient (v (e.output d)) * marker (e.output d).1 (e.output d).2 ∈ _
      rw [hv e he d hr]
      exact (e.invariant_decorated_iff _ hinv (v (e.input d)) d).mpr ih
    | backward e he d hr ih =>
      have hinv := Orbit.invariant (es.map Edge.partialIso) {word v seed} e.partialIso
        (List.mem_map.mpr ⟨e,he,rfl⟩)
      apply (e.invariant_decorated_iff _ hinv (v (e.input d)) d).mp
      rw [← hv e he d (Reach.backward e he d hr)]
      exact ih

theorem benign [Group.IsFinitelyPresented G] [Group.IsFinitelyPresented T] [Finite Q]
    (es : List (Edge G T Q)) (hD : ∀ e ∈ es, Group.IsFinitelyPresented e.Domain)
    (seed : T × Q) (v : T × Q → G)
    (hv : ∀ e ∈ es, ∀ d, Reach es seed (e.input d) →
      v (e.output d) = v (e.input d) * e.weight) :
    IsBenign (decoratedSubgroup v {c | Reach es seed c}) := by
  have : Group.IsFinitelyPresented (G × T) := finitelyPresented_prod
  rw [← orbit_eq es seed v hv]
  apply Orbit.benign _ _ _ (Set.finite_singleton _)
  intro p hp
  obtain ⟨e,he,rfl⟩ := List.mem_map.mp hp
  have := hD e he
  exact e.source_fg

end Higman.MarkerMachine

end OAI
end

section
-- module Solutions.OAIQW_UniversalFInfinity.StackMachines
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u v w x

namespace Higman.IntegerStack
variable {E : Type*}

variable (b : ℤ) (d : E → ℤ) (hb : 2 ≤ b)
  (hd : ∀ e, 2 ≤ d e ∧ d e < b)

include hd

lemma push_mod (e : E) (z : ℤ) : (b * z + d e) % b = d e := by
  rw [Int.add_emod,Int.mul_emod_right,zero_add,Int.emod_emod,
    Int.emod_eq_of_lt (by have := (hd e).1; omega) (hd e).2]

include hb

lemma push_ne_empty (e : E) (z : ℤ) : b * z + d e ≠ 1 := by
  intro h
  have he := congrArg (fun x : ℤ ↦ x % b) h
  rw [push_mod b d hd,Int.emod_eq_of_lt (by omega) (by omega)] at he
  have := (hd e).1
  omega

lemma push_injective (hdinj : Function.Injective d) {e f : E} {z w : ℤ}
    (h : b * z + d e = b * w + d f) : e = f ∧ z = w := by
  have he := congrArg (fun x : ℤ ↦ x % b) h
  rw [push_mod b d hd,push_mod b d hd] at he
  have hef := hdinj he
  subst f
  refine ⟨rfl,?_⟩
  have hm : b * z = b * w := by omega
  exact mul_left_cancel₀ (by omega : b ≠ 0) hm

theorem decode_push (hdinj : Function.Injective d) (e : E) (z : ℤ) (s : List E) :
    b * z + d e = code b d s ↔ ∃ t, s = e :: t ∧ z = code b d t := by
  cases s with
  | nil => simp [push_ne_empty b d hb hd e z]
  | cons f t =>
    constructor
    · intro h
      obtain ⟨hef,hzt⟩ := push_injective b d hb hd hdinj h
      subst f
      exact ⟨t,rfl,hzt⟩
    · rintro ⟨u,hu,hz⟩
      cases hu
      simp [hz]

theorem code_injective (hdinj : Function.Injective d) : Function.Injective (code b d) := by
  intro s
  induction s with
  | nil =>
    intro t h
    cases t with
    | nil => rfl
    | cons e t => exact False.elim (push_ne_empty b d hb hd e (code b d t) h.symm)
  | cons e s ih =>
    intro t h
    obtain ⟨u,rfl,hu⟩ := (decode_push b d hb hd hdinj e (code b d s) t).mp h
    exact congrArg (List.cons e) (ih hu)

end Higman.IntegerStack

namespace Higman.HistoryMachine
variable {E : Type*} {C : Type*} {D : E → Type*}

variable (input output : (e : E) → D e → C) (initial : C)

variable (b : ℤ) (digit : E → ℤ) (hb : 2 ≤ b)
  (hd : ∀ e, 2 ≤ digit e ∧ digit e < b) (hinj : Function.Injective digit)

lemma reach_start : Reach input output initial b digit initial 1 := ⟨[],Run.start,rfl⟩

include hb hd hinj in

theorem reach_step_iff (hout : ∀ e, Function.Injective (output e)) (e : E) (z : D e)
    (h : ℤ) :
    Reach input output initial b digit (output e z) (b * h + digit e) ↔
      Reach input output initial b digit (input e z) h := by
  constructor
  · rintro ⟨s,hs,he⟩
    obtain ⟨t,rfl,ht⟩ := (IntegerStack.decode_push b digit hb hd hinj e h s).mp he
    obtain ⟨y,hy,hr⟩ := (run_cons input output initial e t (output e z)).mp hs
    have hzy : z = y := hout e hy
    subst y
    exact ⟨t,hr,ht⟩
  · rintro ⟨s,hs,rfl⟩
    exact ⟨e :: s,Run.step e z hs,rfl⟩

variable {G : Type*} [Group G]

include hb hd hinj in
@[simp] theorem decoration_code (weight : E → G) (s : List E) :
    decoration b digit weight (IntegerStack.code b digit s) = value weight s := by
  classical
  unfold decoration
  split_ifs with h
  · have he : h.choose = s :=
      IntegerStack.code_injective b digit hb hd hinj h.choose_spec.symm
    rw [he]
  · exact False.elim (h ⟨s,rfl⟩)

include hb hd hinj in
lemma decoration_step (weight : E → G) (e : E) (z : D e) (h : ℤ)
    (hr : Reach input output initial b digit (input e z) h) :
    decoration b digit weight (b * h + digit e) = decoration b digit weight h * weight e := by
  obtain ⟨s,_,rfl⟩ := hr
  rw [← IntegerStack.code_cons,decoration_code b digit hb hd hinj,
    decoration_code b digit hb hd hinj]
  rfl

end Higman.HistoryMachine

namespace Higman.RecordedMachine

section
open MarkerMachine

variable {G T Q : Type u} [Group G]

variable [Group T]

variable {E : Type u} [Fintype E] (edges : E → Edge G T Q)
  (b : ℤ) (digit : E → ℤ) (hb : 2 ≤ b)

lemma mem_edgeList (e : E) : edge (edges e) b (digit e) (by omega) ∈ edgeList edges b digit hb := by
  classical
  exact List.mem_map.mpr ⟨e,Finset.mem_toList.mpr (Finset.mem_univ _),rfl⟩

lemma of_mem_edgeList (a : Edge G (T × Counter) Q) (ha : a ∈ edgeList edges b digit hb) :
    ∃ e, a = edge (edges e) b (digit e) (by omega) := by
  obtain ⟨e,_,rfl⟩ := List.mem_map.mp ha
  exact ⟨e,rfl⟩

variable (seed : T × Q)

omit [Fintype E] in
lemma forward_start : Forward edges b digit seed (augment seed 1) :=
  HistoryMachine.reach_start _ _ _ _ _

variable (hd : ∀ e, 2 ≤ digit e ∧ digit e < b) (hinj : Function.Injective digit)

include hb hd hinj in
omit [Fintype E] in
lemma forward_edge (e : E) (d : (edges e).Domain) (h : ℤ) :
    Forward edges b digit seed (augment ((edges e).output d) (b*h + digit e)) ↔
      Forward edges b digit seed (augment ((edges e).input d) h) :=
  HistoryMachine.reach_step_iff _ _ _ b digit hb hd hinj
    (fun e ↦ output_injective (edges e)) e d h

include hd hinj in
lemma reach_implies_forward (c : (T × Counter) × Q)
    (hc : MarkerMachine.Reach (edgeList edges b digit hb) (augment seed 1) c) :
    Forward edges b digit seed c := by
  induction hc with
  | start => exact forward_start edges b digit seed
  | forward a ha d _ ih =>
    obtain ⟨e,rfl⟩ := of_mem_edgeList edges b digit hb a ha
    obtain ⟨d,h⟩ := d
    change Counter at h
    simpa only [edge_output] using
      (forward_edge edges b digit hb seed hd hinj e d h.toAdd).mpr
        (by simpa only [edge_input] using ih)
  | backward a ha d _ ih =>
    obtain ⟨e,rfl⟩ := of_mem_edgeList edges b digit hb a ha
    obtain ⟨d,h⟩ := d
    change Counter at h
    simpa only [edge_input] using
      (forward_edge edges b digit hb seed hd hinj e d h.toAdd).mp
        (by simpa only [edge_output] using ih)

lemma run_implies_reach {s : List E} {c : T × Q}
    (hc : HistoryMachine.Run (fun e ↦ (edges e).input) (fun e ↦ (edges e).output) seed s c) :
    MarkerMachine.Reach (edgeList edges b digit hb) (augment seed 1)
      (augment c (IntegerStack.code b digit s)) := by
  induction hc with
  | start => exact MarkerMachine.Reach.start
  | @step s e d hr ih =>
    have hh := MarkerMachine.Reach.forward (seed := augment seed 1)
      (edge (edges e) b (digit e) (by omega)) (mem_edgeList edges b digit hb e)
      (d,Multiplicative.ofAdd (IntegerStack.code b digit s))
    rw [edge_input,edge_output] at hh
    exact hh ih

lemma forward_implies_reach (c : (T × Counter) × Q) (hc : Forward edges b digit seed c) :
    MarkerMachine.Reach (edgeList edges b digit hb) (augment seed 1) c := by
  obtain ⟨s,hs,hh⟩ := hc
  have hr := run_implies_reach edges b digit hb seed hs
  rw [← hh,augment_forget] at hr
  exact hr

include hd hinj in

theorem reach_iff_forward (c : (T × Counter) × Q) :
    MarkerMachine.Reach (edgeList edges b digit hb) (augment seed 1) c ↔
      Forward edges b digit seed c :=
  ⟨reach_implies_forward edges b digit hb seed hd hinj c,
    forward_implies_reach edges b digit hb seed c⟩

end

open MarkerMachine DecoratedMarker MarkerEmbedding
variable {G T Q E : Type u} [Group G] [Group T] [Fintype E]
  (edges : E → Edge G T Q) (b : ℤ) (digit : E → ℤ) (hb : 2 ≤ b)
  (seed : T × Q) (hd : ∀ e, 2 ≤ digit e ∧ digit e < b) (hinj : Function.Injective digit)

include hd hinj in
lemma decoration_edge (a : Edge G (T × Counter) Q) (ha : a ∈ edgeList edges b digit hb)
    (d : a.Domain) (hr : MarkerMachine.Reach (edgeList edges b digit hb) (augment seed 1) (a.input d)) :
    decoration edges b digit (a.output d) = decoration edges b digit (a.input d) * a.weight := by
  obtain ⟨e,rfl⟩ := of_mem_edgeList edges b digit hb a ha
  obtain ⟨d,h⟩ := d
  have hf := reach_implies_forward edges b digit hb seed hd hinj _ hr
  rw [edge_input] at hf ⊢
  rw [edge_output]
  exact HistoryMachine.decoration_step (fun e ↦ (edges e).input) (fun e ↦ (edges e).output)
    seed b digit hb hd hinj
    (fun e ↦ (edges e).weight) e d h.toAdd hf

include hb hd hinj in

theorem benign_forward [Group.IsFinitelyPresented G] [Group.IsFinitelyPresented T] [Finite Q]
    (hD : ∀ e, Group.IsFinitelyPresented (edges e).Domain) :
    IsBenign (decoratedSubgroup (decoration edges b digit) {c | Forward edges b digit seed c}) := by
  have : Group.IsFinitelyPresented (T × Counter) := finitelyPresented_prod
  have he : {c | MarkerMachine.Reach (edgeList edges b digit hb) (augment seed 1) c} =
      {c | Forward edges b digit seed c} := by
    ext c
    exact reach_iff_forward edges b digit hb seed hd hinj c
  rw [← he]
  apply MarkerMachine.benign _ _ _ _ (decoration_edge edges b digit hb seed hd hinj)
  intro a ha
  obtain ⟨e,rfl⟩ := of_mem_edgeList edges b digit hb a ha
  have := hD e
  exact finitelyPresented_prod

end Higman.RecordedMachine

namespace Higman.MarkerEmbedding
open Monoid Coprod DecoratedMarker
variable {G T : Type u} {Q : Type*} [Group G] [Group T]

lemma projection_surjective : Function.Surjective (coefficientProjection : Base G T Q →* G) :=
  fun g ↦ ⟨coefficient g,projection_coefficient g⟩

variable {Q : Type u}

theorem benign_output [Group.IsFinitelyPresented G] [Group.IsFinitelyPresented T]
    (v : T × Q → G) (V : Set (T × Q)) (hR : IsBenign (decoratedSubgroup v V)) (q : Q) :
    IsBenign (Subgroup.closure (v '' {c | c ∈ V ∧ c.2 = q})) := by
  have : Group.IsFinitelyPresented (G × T) := finitelyPresented_prod
  let f : Base G T Unit →* Base G T Q := embedding (MonoidHom.id T) (fun _ ↦ 1)
    (fun _ ↦ q) (fun _ ↦ 1)
  have hi : Function.Injective (index (MonoidHom.id T) (fun _ : Unit ↦ 1) (fun _ ↦ q)) :=
    index_injective _ Function.injective_id _ _ (Function.injective_of_subsingleton _)
  have hB := (hR.comap f).map_surjective
    (coefficientProjection : Base G T Unit →* G)
      (projection_surjective (G := G) (T := T) (Q := Unit))
  dsimp only [f] at hB
  rw [comap_decoratedSubgroup _ Function.injective_id _ _ _ hi,
    decoratedSubgroup_eq_closure,MonoidHom.map_closure] at hB
  have he : (coefficientProjection : Base G T Unit →* G) ''
      ((fun x : T × Unit ↦ coefficient
        (pullDecoration (MonoidHom.id T) (fun _ ↦ 1) (fun _ ↦ q) (fun _ ↦ 1) v x) *
          marker x.1 x.2) ''
        (index (MonoidHom.id T) (fun _ : Unit ↦ 1) (fun _ ↦ q) ⁻¹' V)) =
      v '' {c | c ∈ V ∧ c.2 = q} := by
    rw [Set.image_image]
    ext g
    constructor
    · rintro ⟨⟨t,p⟩,ht,rfl⟩
      refine ⟨(t,q),⟨?_,rfl⟩,?_⟩
      · simpa [index] using ht
      · simp [pullDecoration,index]
    · rintro ⟨⟨t,r⟩,⟨hc,hq⟩,rfl⟩
      change r = q at hq
      subst r
      refine ⟨(t,()),?_,?_⟩
      · simpa [index] using hc
      · simp [pullDecoration,index]
  rw [he] at hB
  exact hB

end Higman.MarkerEmbedding

namespace Higman.RecordedMachine
open MarkerMachine
variable {G T Q E : Type u} [Group G] [Group T]
  (edges : E → Edge G T Q) (seed : T × Q) (halt : Q)

variable [Fintype E] [Finite Q] [Group.IsFinitelyPresented G] [Group.IsFinitelyPresented T]

theorem benign_accepted (hD : ∀ e, Group.IsFinitelyPresented (edges e).Domain) :
    IsBenign (Subgroup.closure (acceptedOutputs edges seed halt)) := by
  classical
  let b : ℤ := Fintype.card E + 2
  let digit : E → ℤ := fun e ↦ ((Fintype.equivFin E e).val : ℤ) + 2
  have hb : 2 ≤ b := by dsimp [b]; omega
  have hd : ∀ e, 2 ≤ digit e ∧ digit e < b := by
    intro e
    have hh := (Fintype.equivFin E e).isLt
    dsimp [digit,b]
    constructor <;> omega
  have hi : Function.Injective digit := by
    intro e f h
    apply (Fintype.equivFin E).injective
    apply Fin.ext
    dsimp [digit] at h
    omega
  have : Group.IsFinitelyPresented (T × Counter) := finitelyPresented_prod
  have hp := MarkerEmbedding.benign_output (decoration edges b digit)
    {c | Forward edges b digit seed c}
    (benign_forward edges b digit hb seed hd hi hD) halt
  have he : decoration edges b digit ''
      {c | c ∈ {c | Forward edges b digit seed c} ∧ c.2 = halt} =
      acceptedOutputs edges seed halt := by
    ext g
    constructor
    · rintro ⟨c,⟨⟨s,hs,hh⟩,hc⟩,rfl⟩
      refine ⟨s,forget c,hs,hc,?_⟩
      dsimp [decoration]
      rw [hh,HistoryMachine.decoration_code b digit hb hd hi]
    · rintro ⟨s,c,hs,hc,rfl⟩
      refine ⟨augment c (IntegerStack.code b digit s),⟨?_,hc⟩,?_⟩
      · exact ⟨s,hs,rfl⟩
      · exact HistoryMachine.decoration_code b digit hb hd hi _ s
  rwa [he] at hp

end Higman.RecordedMachine

namespace Higman

theorem finitelyPresented_pi (I : Type u) [Finite I] (G : Type v) [Group G]
    [Group.IsFinitelyPresented G] : Group.IsFinitelyPresented (I → G) := by
  apply Finite.induction_empty_option _ _ _ I
  · intro A B e ih
    have := ih
    exact Group.IsFinitelyPresented.equiv (MulEquiv.arrowCongr e (MulEquiv.refl G))
  · infer_instance
  · intro A _ ih
    have := ih
    have : Group.IsFinitelyPresented (G × (A → G)) := finitelyPresented_prod
    let e : (Option A → G) ≃* G × (A → G) :=
      { Equiv.piOptionEquivProd with map_mul' := fun _ _ ↦ rfl }
    exact Group.IsFinitelyPresented.equiv e.symm

end Higman

end OAI
end

section
-- module Solutions.OAIQW_UniversalFInfinity.StackPrograms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u v w x

namespace Higman.AffineStack

section
open MarkerMachine

variable {Γ G Q : Type} [Group G]

variable (b : ℤ) (digit : Γ → ℤ) (hb : 2 ≤ b)
  (hd : ∀ a, 2 ≤ digit a ∧ digit a < b) (hi : Function.Injective digit)

include hb hd hi in
lemma encode_injective : Function.Injective (encode b digit) :=
  fun _ _ h ↦ IntegerStack.code_injective b digit hb hd hi (congrArg Multiplicative.toAdd h)

include hb hd hi in

theorem local_sound (p q : Q) (w : G) (o : Op Γ)
    (x : (localEdge b digit (by omega) p q w o).Domain) (s : List Γ)
    (h : (localEdge b digit (by omega) p q w o).inputLinear x *
      (localEdge b digit (by omega) p q w o).inputOffset = encode b digit s) :
    ∃ t, (localEdge b digit (by omega) p q w o).outputLinear x *
      (localEdge b digit (by omega) p q w o).outputOffset = encode b digit t ∧ o.Rel s t := by
  cases o with
  | push a =>
    change x * 1 = encode b digit s at h
    simp only [mul_one] at h
    subst x
    exact ⟨a::s,rfl,rfl⟩
  | pop a =>
    change Counter at x
    have hh : b*x.toAdd + digit a = IntegerStack.code b digit s :=
      congrArg Multiplicative.toAdd h
    obtain ⟨t,rfl,ht⟩ := (IntegerStack.decode_push b digit hb hd hi a x.toAdd s).mp hh
    refine ⟨t,?_,rfl⟩
    change x * 1 = encode b digit t
    rw [mul_one]
    exact Multiplicative.toAdd.injective ht
  | peek a =>
    change Counter at x
    have hh : b*x.toAdd + digit a = IntegerStack.code b digit s :=
      congrArg Multiplicative.toAdd h
    obtain ⟨t,ht,_⟩ := (IntegerStack.decode_push b digit hb hd hi a x.toAdd s).mp hh
    exact ⟨s,h,rfl,t,ht⟩
  | empty =>
    have hh : encode b digit [] = encode b digit s := by
      change (1 : Counter) * encode b digit [] = encode b digit s at h
      simpa only [one_mul] using h
    have hs : s = [] := (encode_injective b digit hb hd hi hh).symm
    exact ⟨[],rfl,hs,rfl⟩
  | idle => exact ⟨s,h,rfl⟩

include hb in

theorem local_complete (p q : Q) (w : G) (o : Op Γ) (s t : List Γ) (h : o.Rel s t) :
    ∃ x : (localEdge b digit (by omega) p q w o).Domain,
      (localEdge b digit (by omega) p q w o).inputLinear x *
        (localEdge b digit (by omega) p q w o).inputOffset = encode b digit s ∧
      (localEdge b digit (by omega) p q w o).outputLinear x *
        (localEdge b digit (by omega) p q w o).outputOffset = encode b digit t := by
  cases o with
  | push a => exact ⟨encode b digit s, mul_one _, by cases h; rfl⟩
  | pop a => exact ⟨encode b digit t, by cases h; rfl, mul_one _⟩
  | peek a =>
    obtain ⟨rfl,r,rfl⟩ := h
    exact ⟨encode b digit r,rfl,rfl⟩
  | empty =>
    obtain ⟨rfl,rfl⟩ := h
    exact ⟨PUnit.unit,rfl,rfl⟩
  | idle => exact ⟨encode b digit s,mul_one _,by cases h; exact mul_one _⟩

end

section
open MarkerMachine
variable {K Γ G Q : Type} [DecidableEq K] [Group G]

lemma liftEdge_finitelyPresented [Finite K] (k : K) (e : Edge G Counter Q)
    [Group.IsFinitelyPresented e.Domain] : Group.IsFinitelyPresented (liftEdge k e).Domain := by
  have : Group.IsFinitelyPresented (Rest k) := finitelyPresented_pi _ _
  exact finitelyPresented_prod

variable (b : ℤ) (digit : Γ → ℤ) (hb : 2 ≤ b)
  (hd : ∀ a, 2 ≤ digit a ∧ digit a < b) (hi : Function.Injective digit)

lemma action_finitelyPresented [Finite K] (p q : Q) (w : G) (a : Action K Γ) :
    Group.IsFinitelyPresented (actionEdge b digit hb p q w a).Domain := by
  cases a with
  | onStack k o => exact liftEdge_finitelyPresented _ _
  | idle => exact finitelyPresented_pi _ _

include hd hi in
theorem action_sound (p q : Q) (w : G) (a : Action K Γ)
    (x : (actionEdge b digit hb p q w a).Domain) (S : K → List Γ)
    (h : (actionEdge b digit hb p q w a).inputLinear x *
      (actionEdge b digit hb p q w a).inputOffset = encodeStores b digit S) :
    ∃ T, (actionEdge b digit hb p q w a).outputLinear x *
      (actionEdge b digit hb p q w a).outputOffset = encodeStores b digit T ∧ a.Rel S T := by
  cases a with
  | onStack k o =>
    change (localEdge b digit (by omega) p q w o).Domain × Rest k at x
    have input_eq (j : K) :
        (if hj : j = k then (localEdge b digit (by omega) p q w o).inputLinear x.1
          else x.2 ⟨j,hj⟩) *
        (if j = k then (localEdge b digit (by omega) p q w o).inputOffset else 1) =
          encode b digit (S j) := congrFun h j
    have hk : (localEdge b digit (by omega) p q w o).inputLinear x.1 *
        (localEdge b digit (by omega) p q w o).inputOffset = encode b digit (S k) := by
      simpa using input_eq k
    obtain ⟨t,ht,hr⟩ := local_sound b digit hb hd hi p q w o x.1 (S k) hk
    refine ⟨Function.update S k t,?_,t,hr,rfl⟩
    funext j
    change (if hj : j = k then (localEdge b digit (by omega) p q w o).outputLinear x.1
        else x.2 ⟨j,hj⟩) *
      (if j = k then (localEdge b digit (by omega) p q w o).outputOffset else 1) =
        encode b digit (Function.update S k t j)
    by_cases hj : j = k
    · subst j
      simpa using ht
    · simpa [hj] using input_eq j
  | idle => exact ⟨S,h,rfl⟩

theorem action_complete (p q : Q) (w : G) (a : Action K Γ) (S T : K → List Γ) (h : a.Rel S T) :
    ∃ x : (actionEdge b digit hb p q w a).Domain,
      (actionEdge b digit hb p q w a).inputLinear x *
        (actionEdge b digit hb p q w a).inputOffset = encodeStores b digit S ∧
      (actionEdge b digit hb p q w a).outputLinear x *
        (actionEdge b digit hb p q w a).outputOffset = encodeStores b digit T := by
  cases a with
  | onStack k o =>
    obtain ⟨t,hr,rfl⟩ := h
    obtain ⟨x,hs,ht⟩ := local_complete b digit hb p q w o (S k) t hr
    refine ⟨(x,fun j ↦ encode b digit (S j.val)),?_,?_⟩
    · funext j
      change (if j = k then (localEdge b digit (by omega) p q w o).inputLinear x
          else encode b digit (S j)) *
        (if j = k then (localEdge b digit (by omega) p q w o).inputOffset else 1) =
          encode b digit (S j)
      by_cases hj : j = k
      · subst j
        simpa using hs
      · simp [hj]
    · funext j
      change (if j = k then (localEdge b digit (by omega) p q w o).outputLinear x
          else encode b digit (S j)) *
        (if j = k then (localEdge b digit (by omega) p q w o).outputOffset else 1) =
          encode b digit (Function.update S k t j)
      by_cases hj : j = k
      · subst j
        simpa using ht
      · simp [hj]
  | idle => exact ⟨encodeStores b digit S,mul_one _,by cases h; exact mul_one _⟩

end

open MarkerMachine

end Higman.AffineStack

namespace Higman.StackProgram

section
open AffineStack MarkerMachine
variable {K Γ G Q E : Type} [DecidableEq K] [Group G]

variable (prog : E → Instruction K Γ G Q) (seed : (K → List Γ) × Q)
  (b : ℤ) (digit : Γ → ℤ) (hb : 2 ≤ b)
  (hd : ∀ a, 2 ≤ digit a ∧ digit a < b) (hi : Function.Injective digit)

include hd hi in

theorem run_sound {s : List E} {c : Stores K × Q}
    (h : HistoryMachine.Run (fun e ↦ ((prog e).edge b digit hb).input)
      (fun e ↦ ((prog e).edge b digit hb).output) (encodeStores b digit seed.1,seed.2) s c) :
    ∃ S, encodeStores b digit S = c.1 ∧ Run prog seed s (S,c.2) := by
  induction h with
  | start => exact ⟨seed.1,rfl,Run.start⟩
  | @step s e x h ih =>
    obtain ⟨S,hS,hR⟩ := ih
    obtain ⟨T,hT,hr⟩ := action_sound b digit hb hd hi (prog e).source (prog e).target
      (prog e).weight (prog e).action x S hS.symm
    refine ⟨T,hT.symm,?_⟩
    simp only [Edge.input,Instruction.edge,actionEdge_inputState] at hR
    simpa only [Edge.output,Instruction.edge,actionEdge_outputState] using Run.step e S T hr hR

theorem run_complete {s : List E} {c : (K → List Γ) × Q} (h : Run prog seed s c) :
    HistoryMachine.Run (fun e ↦ ((prog e).edge b digit hb).input)
      (fun e ↦ ((prog e).edge b digit hb).output) (encodeStores b digit seed.1,seed.2)
      s (encodeStores b digit c.1,c.2) := by
  induction h with
  | start => exact HistoryMachine.Run.start
  | @step s e S T hr h ih =>
    obtain ⟨x,hS,hT⟩ := action_complete b digit hb (prog e).source (prog e).target
      (prog e).weight (prog e).action S T hr
    have hin : ((prog e).edge b digit hb).input x = (encodeStores b digit S,(prog e).source) := by
      apply Prod.ext hS
      exact actionEdge_inputState _ _ _ _ _ _ _
    have hout : ((prog e).edge b digit hb).output x = (encodeStores b digit T,(prog e).target) := by
      apply Prod.ext hT
      exact actionEdge_outputState _ _ _ _ _ _ _
    rw [← hout]
    apply HistoryMachine.Run.step (input := fun e ↦ ((prog e).edge b digit hb).input)
      (output := fun e ↦ ((prog e).edge b digit hb).output) e x
    rwa [hin]

end

open AffineStack MarkerMachine
variable {K Γ G Q E : Type} [DecidableEq K] [Group G]
  [Finite K] [Fintype Γ] [Finite Q] [Fintype E] [Group.IsFinitelyPresented G]
  (prog : E → Instruction K Γ G Q) (seed : (K → List Γ) × Q) (halt : Q)

theorem benign_outputs : IsBenign (Subgroup.closure (outputs prog seed halt)) := by
  classical
  let b : ℤ := Fintype.card Γ + 2
  let digit : Γ → ℤ := fun a ↦ ((Fintype.equivFin Γ a).val : ℤ) + 2
  have hb : 2 ≤ b := by dsimp [b]; omega
  have hd : ∀ a, 2 ≤ digit a ∧ digit a < b := by
    intro a
    have hh := (Fintype.equivFin Γ a).isLt
    dsimp [digit,b]
    constructor <;> omega
  have hi : Function.Injective digit := by
    intro a c h
    apply (Fintype.equivFin Γ).injective
    apply Fin.ext
    dsimp [digit] at h
    omega
  have : Group.IsFinitelyPresented (Stores K) := finitelyPresented_pi _ _
  have hp := RecordedMachine.benign_accepted (fun e ↦ (prog e).edge b digit hb)
    (encodeStores b digit seed.1,seed.2) halt
    (fun e ↦ action_finitelyPresented b digit hb (prog e).source (prog e).target
      (prog e).weight (prog e).action)
  have he : RecordedMachine.acceptedOutputs (fun e ↦ (prog e).edge b digit hb)
      (encodeStores b digit seed.1,seed.2) halt = outputs prog seed halt := by
    ext g
    constructor
    · rintro ⟨s,c,hs,hc,hg⟩
      obtain ⟨S,_,hR⟩ := run_sound prog seed b digit hb hd hi hs
      refine ⟨s,S,?_,?_⟩
      · rwa [hc] at hR
      · simpa only [Instruction.edge,actionEdge_weight] using hg
    · rintro ⟨s,S,hs,hg⟩
      refine ⟨s,(encodeStores b digit S,halt),run_complete prog seed b digit hb hs,rfl,?_⟩
      simpa only [Instruction.edge,actionEdge_weight] using hg
  rwa [he] at hp

end Higman.StackProgram

end OAI
end

section
-- module Solutions.OAIQW_UniversalFInfinity.TuringMachines
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section UniversalFinitelyPresentedProof
universe u v w x

namespace Higman.MicroTM2
open Turing Function Relation
variable {K Γ Λ σ : Type} [DecidableEq K]

variable (M : Λ → Stmt K Γ Λ σ)

theorem reaches_stepAux (q : Stmt K Γ Λ σ) (v : σ) (S : K → List Γ) :
    StateTransition.Reaches (step M) (S,some q,v) (translate M (TM2.stepAux q v S)) := by
  induction q generalizing v S with
  | push k f r ih =>
    exact ReflTransGen.head rfl (ih v (update S k (f v :: S k)))
  | peek k f r ih => exact ReflTransGen.head rfl (ih (f v (S k).head?) S)
  | pop k f r ih =>
    exact ReflTransGen.head rfl (ih (f v (S k).head?) (update S k (S k).tail))
  | load f r ih => exact ReflTransGen.head rfl (ih (f v) S)
  | branch f r t ihr iht =>
    cases h : f v
    · simp only [TM2.stepAux,h,Bool.cond_false]
      exact ReflTransGen.head
        (show (S,some t,v) ∈ step M (S,some (.branch f r t),v) by simp [step,h]) (iht v S)
    · simp only [TM2.stepAux,h,Bool.cond_true]
      exact ReflTransGen.head
        (show (S,some r,v) ∈ step M (S,some (.branch f r t),v) by simp [step,h]) (ihr v S)
  | goto f => exact ReflTransGen.single rfl
  | halt => exact ReflTransGen.single rfl

theorem translate_step {c d : TM2.Cfg (fun _ : K ↦ Γ) Λ σ} (h : d ∈ TM2.step M c) :
    StateTransition.Reaches (step M) (translate M c) (translate M d) := by
  rcases c with ⟨_ | l,v,S⟩
  · simp [TM2.step] at h
  · have hh : d = TM2.stepAux (M l) v S := by simpa [TM2.step] using h.symm
    subst d
    exact reaches_stepAux M (M l) v S

theorem translate_reaches {c d : TM2.Cfg (fun _ : K ↦ Γ) Λ σ}
    (h : TM2.Reaches M c d) : StateTransition.Reaches (step M) (translate M c) (translate M d) := by
  induction h with
  | refl => exact ReflTransGen.refl
  | tail h hd ih => exact ih.trans (translate_step M hd)

theorem project_step {c d : Cfg K Γ Λ σ} (h : d ∈ step M c) :
    TM2.Reaches M (project c) (project d) := by
  rcases c with ⟨S,_ | q,v⟩
  · simp [step] at h
  · cases q with
    | push k f r =>
      have hd : d = (update S k (f v :: S k),some r,v) := by simpa [step] using h.symm
      subst d
      exact ReflTransGen.refl
    | peek k f r =>
      have hd : d = (S,some r,f v (S k).head?) := by simpa [step] using h.symm
      subst d
      exact ReflTransGen.refl
    | pop k f r =>
      have hd : d = (update S k (S k).tail,some r,f v (S k).head?) := by simpa [step] using h.symm
      subst d
      exact ReflTransGen.refl
    | load f r =>
      have hd : d = (S,some r,f v) := by simpa [step] using h.symm
      subst d
      exact ReflTransGen.refl
    | branch f r t =>
      have hd : d = (S,some (if f v then r else t),v) := by simpa [step] using h.symm
      subst d
      cases h : f v <;> simp [project,TM2.stepAux,h,TM2.Reaches] <;> exact ReflTransGen.refl
    | goto f =>
      have hd : d = (S,some (M (f v)),v) := by simpa [step] using h.symm
      subst d
      exact ReflTransGen.single rfl
    | halt =>
      have hd : d = (S,none,v) := by simpa [step] using h.symm
      subst d
      exact ReflTransGen.refl

theorem project_reaches {c d : Cfg K Γ Λ σ} (h : StateTransition.Reaches (step M) c d) :
    TM2.Reaches M (project c) (project d) := by
  induction h with
  | refl => exact ReflTransGen.refl
  | tail h hd ih => exact ih.trans (project_step M hd)

theorem reaches_project_translate (c : TM2.Cfg (fun _ : K ↦ Γ) Λ σ) :
    TM2.Reaches M c (project (translate M c)) := by
  rcases c with ⟨_ | l,v,S⟩
  · exact ReflTransGen.refl
  · exact ReflTransGen.single rfl

theorem reaches_halt_iff (c : TM2.Cfg (fun _ : K ↦ Γ) Λ σ) (S : K → List Γ) (v : σ) :
    TM2.Reaches M c ⟨none,v,S⟩ ↔
      StateTransition.Reaches (step M) (translate M c) (S,none,v) := by
  constructor
  · exact translate_reaches M
  · intro h
    exact (reaches_project_translate M c).trans (project_reaches M h)

end Higman.MicroTM2

namespace Higman.TM2StackCompiler
open Turing Function AffineStack StackProgram MicroTM2 Relation
variable {K Γ Λ σ G : Type} [DecidableEq K] [Group G]

lemma readOp_rel (pop : Bool) (a : Option Γ) (s t : List Γ) :
    (readOp pop a).Rel s t ↔ a = s.head? ∧ t = (if pop then s.tail else s) := by
  cases pop <;> cases a <;> cases s <;> simp [readOp,Op.Rel] <;> aesop

lemma readAction_rel (pop : Bool) (a : Option Γ) (k : K) (S T : K → List Γ) :
    (Action.onStack k (readOp pop a)).Rel S T ↔
      a = (S k).head? ∧ T = (if pop then update S k (S k).tail else S) := by
  simp only [Action.Rel,readOp_rel]
  constructor
  · rintro ⟨t,⟨h,rfl⟩,rfl⟩
    refine ⟨h,?_⟩
    cases pop <;> simp
  · rintro ⟨h,rfl⟩
    refine ⟨if pop then (S k).tail else S k,⟨h,rfl⟩,?_⟩
    cases pop <;> simp

variable (M : Λ → Stmt K Γ Λ σ)

lemma raw_sound (q : Stmt K Γ Λ σ) (v : σ) (a : Option Γ) (S T : K → List Γ)
    (h : (rawAction q v a).Rel S T) :
    (T,rawTarget M q v a) ∈ MicroTM2.step M (S,some q,v) := by
  cases q with
  | push k f r =>
    obtain ⟨t,ht,rfl⟩ := h
    cases ht
    rfl
  | peek k f r =>
    obtain ⟨ha,rfl⟩ := (readAction_rel false a k S T).mp h
    simp [rawTarget,MicroTM2.step,ha]
  | pop k f r =>
    obtain ⟨ha,rfl⟩ := (readAction_rel true a k S T).mp h
    simp [rawTarget,MicroTM2.step,ha]
  | load f r | branch f r t | goto f | halt =>
    cases h
    rfl

lemma raw_complete (q : Stmt K Γ Λ σ) (v : σ) (S : K → List Γ) (d : Cfg K Γ Λ σ)
    (h : d ∈ MicroTM2.step M (S,some q,v)) :
    ∃ a, (rawAction q v a).Rel S d.1 ∧ d.2 = rawTarget M q v a := by
  cases q with
  | push k f r =>
    have hd : d = (update S k (f v :: S k),some r,v) := by simpa [MicroTM2.step] using h.symm
    subst d
    exact ⟨none,⟨f v :: S k,rfl,rfl⟩,rfl⟩
  | peek k f r =>
    have hd : d = (S,some r,f v (S k).head?) := by simpa [MicroTM2.step] using h.symm
    subst d
    exact ⟨(S k).head?,(readAction_rel false _ k S S).mpr ⟨rfl,rfl⟩,rfl⟩
  | pop k f r =>
    have hd : d = (update S k (S k).tail,some r,f v (S k).head?) := by
      simpa [MicroTM2.step] using h.symm
    subst d
    exact ⟨(S k).head?,(readAction_rel true _ k S _).mpr ⟨rfl,rfl⟩,rfl⟩
  | load f r =>
    have hd : d = (S,some r,f v) := by simpa [MicroTM2.step] using h.symm
    subst d
    exact ⟨none,rfl,rfl⟩
  | branch f r t =>
    have hd : d = (S,some (if f v then r else t),v) := by simpa [MicroTM2.step] using h.symm
    subst d
    exact ⟨none,rfl,rfl⟩
  | goto f =>
    have hd : d = (S,some (M (f v)),v) := by simpa [MicroTM2.step] using h.symm
    subst d
    exact ⟨none,rfl,rfl⟩
  | halt =>
    have hd : d = (S,none,v) := by simpa [MicroTM2.step] using h.symm
    subst d
    exact ⟨none,rfl,rfl⟩

variable (L : Finset Λ) (hL : ∀ l ∈ L, TM2.SupportsStmt L (M l))

lemma compile_sound (e : Edge M L) (S T : K → List Γ)
    (h : (compile (G := G) M L hL e).action.Rel S T) :
    forget M L (T,(compile (G := G) M L hL e).target) ∈
      MicroTM2.step M (forget M L (S,(compile (G := G) M L hL e).source)) :=
  raw_sound M e.1.val e.2.1 e.2.2 S T h

lemma compile_complete (c : (K → List Γ) × State M L) (d : Cfg K Γ Λ σ)
    (h : d ∈ MicroTM2.step M (forget M L c)) :
    ∃ e : Edge M L, c.2 = (compile (G := G) M L hL e).source ∧
      (compile (G := G) M L hL e).action.Rel c.1 d.1 ∧
      forget M L (d.1,(compile (G := G) M L hL e).target) = d := by
  rcases c with ⟨S,⟨_ | q,hq⟩,v⟩
  · simp [forget,MicroTM2.step] at h
  · obtain ⟨a,ha,hd⟩ := raw_complete M q v S d h
    refine ⟨(⟨q,hq⟩,v,a),rfl,ha,?_⟩
    change (d.1,rawTarget M q v a) = d
    rw [← hd]

lemma reaches_complete {seed : (K → List Γ) × State M L} {d : Cfg K Γ Λ σ}
    (h : StateTransition.Reaches (MicroTM2.step M) (forget M L seed) d) :
    ∃ s c, Run (compile (G := G) M L hL) seed s c ∧ forget M L c = d := by
  induction h with
  | refl => exact ⟨[],seed,Run.start,rfl⟩
  | @tail d f hr hd ih =>
    obtain ⟨s,c,hc,rfl⟩ := ih
    obtain ⟨e,he,ha,hf⟩ := compile_complete (G := G) M L hL c f hd
    refine ⟨e::s,(f.1,(compile (G := G) M L hL e).target),?_,hf⟩
    apply Run.step e c.1 f.1 ha
    simpa only [← he] using hc

end Higman.TM2StackCompiler

end UniversalFinitelyPresentedProof

end OAI
end

section
-- module Solutions.OAIQW_UniversalFInfinity.HigmanEmbedding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u v w x

namespace Higman.WordBinary
open Turing.PartrecToTM2

lemma push_ge (a : Letter) (n : ℕ) : 8*n ≤ push a n := by
  rcases a with ⟨b,c,d⟩
  cases b <;> cases c <;> cases d <;> simp [push,Nat.bit] <;> omega

lemma code_pos (w : List Letter) : 0 < code w := by
  induction w with
  | nil => decide
  | cons a w ih => have := push_ge a (code w); change 0 < push a (code w); omega

lemma push_inj {a b : Letter} {m n : ℕ} (h : push a m = push b n) : a = b ∧ m = n := by
  have h₁ := congrArg Nat.bodd h
  have ht := congrArg Nat.div2 h
  simp only [push,Nat.bodd_bit,Nat.div2_bit] at h₁ ht
  have h₂ := congrArg Nat.bodd ht
  have hu := congrArg Nat.div2 ht
  simp only [Nat.bodd_bit,Nat.div2_bit] at h₂ hu
  have h₃ := congrArg Nat.bodd hu
  have hm := congrArg Nat.div2 hu
  simp only [Nat.bodd_bit,Nat.div2_bit] at h₃ hm
  exact ⟨Prod.ext h₁ (Prod.ext h₂ h₃),hm⟩

lemma code_injective : Function.Injective code := by
  intro v
  induction v with
  | nil =>
    intro w h
    cases w with
    | nil => rfl
    | cons a w =>
      have hp := code_pos w
      have hg := push_ge a (code w)
      change 1 = push a (code w) at h
      omega
  | cons a v ih =>
    intro w h
    cases w with
    | nil =>
      have hp := code_pos v
      have hg := push_ge a (code v)
      change push a (code v) = 1 at h
      omega
    | cons b w =>
      obtain ⟨rfl,he⟩ := push_inj h
      exact congrArg (List.cons a) (ih he)

lemma trNat_bit (b : Bool) (n : ℕ) (hn : 0 < n) :
    trNat (Nat.bit b n) = symbol b :: trNat n := by
  have hcast : (n : Num) ≠ 0 := by
    intro h
    have := congrArg (fun m : Num ↦ (m : ℕ)) h
    simp only [Num.to_of_nat,Num.cast_zero] at this
    omega
  unfold trNat
  rw [← Num.ofNat'_eq,Num.ofNat'_bit,Num.ofNat'_eq]
  cases h : (n : Num) with
  | zero => exact False.elim (hcast h)
  | pos p => cases b <;> rfl

lemma trNat_code (w : List Letter) : trNat (code w) = spelling w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    have hp := code_pos w
    have hbit (b : Bool) (n : ℕ) (hn : 0 < n) : 0 < Nat.bit b n := by
      cases b <;> simp [Nat.bit]; omega
    simp only [code,push,trNat_bit _ _ (hbit _ _ (hbit _ _ hp)),
      trNat_bit _ _ (hbit _ _ hp),trNat_bit _ _ hp,ih,spelling]

lemma push_primrec : Primrec₂ push := by
  let digit : Letter → ℕ := fun a ↦ push a 0
  have h : Primrec (fun p : Letter × ℕ ↦ 8*p.2+digit p.1) :=
    Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 8) Primrec.snd)
      ((Primrec.dom_finite digit).comp Primrec.fst)
  apply h.of_eq
  rintro ⟨⟨b,c,d⟩,n⟩
  cases b <;> cases c <;> cases d <;> simp [digit,push,Nat.bit] <;> omega

lemma code_primrec : Primrec code := by
  have h := Primrec.list_foldr (α := List Letter) Primrec.id (Primrec.const 1)
    (push_primrec.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂
  apply h.of_eq
  intro w
  induction w with
  | nil => rfl
  | cons a w ih => simpa only [id_eq,List.foldr_cons,code] using congrArg (push a) ih

end Higman.WordBinary

namespace Higman.RangeRecognizer
open Turing ToPartrec PartrecToTM2

lemma search_dom (r : ℕ → ℕ) (n : ℕ) : (search r n).Dom ↔ n ∈ Set.range r := by
  exact (Nat.rfind_dom (p := fun k ↦ Part.some (decide (r k = n)))).trans
    (by simp [Set.mem_range])

lemma search_partrec (r : ℕ → ℕ) (hr : Computable r) : Partrec (search r) := by
  apply Partrec.rfind
  exact ((Primrec.eq.decide.to_comp).comp (hr.comp Computable.snd) Computable.fst).partrec.to₂

theorem exists_code (r : ℕ → ℕ) (hr : Computable r) :
    ∃ c : Code, ∀ n, (c.eval [n]).Dom ↔ n ∈ Set.range r := by
  obtain ⟨c,hc⟩ := Code.exists_code (Nat.Partrec'.part_iff₁.mpr (search_partrec r hr))
  refine ⟨c,fun n ↦ ?_⟩
  have he := hc ⟨[n],rfl⟩
  change c.eval [n] = _ at he
  rw [he]
  exact search_dom r n

lemma halt_iff_dom (c : Code) (v : List ℕ) :
    (∃ S x, TM2.Reaches tr (init c v) ⟨none,x,S⟩) ↔ (c.eval v).Dom := by
  constructor
  · rintro ⟨S,x,h⟩
    have hm : (⟨none,x,S⟩ : Cfg') ∈ StateTransition.eval (TM2.step tr) (init c v) :=
      StateTransition.mem_eval.mpr ⟨h,rfl⟩
    rw [tr_eval] at hm
    obtain ⟨w,hw,_⟩ := (Part.mem_map_iff _).mp hm
    exact hw.1
  · intro h
    let w := (c.eval v).get h
    have hw : halt w ∈ StateTransition.eval (TM2.step tr) (init c v) := by
      rw [tr_eval]
      exact (Part.mem_map_iff _).mpr ⟨w,Part.get_mem h,rfl⟩
    exact ⟨(halt w).stk,(halt w).var,(StateTransition.mem_eval.mp hw).1⟩

end Higman.RangeRecognizer

noncomputable section
namespace Higman.RecognizingStack
open Turing ToPartrec PartrecToTM2 WordBinary AffineStack StackProgram Function Relation
variable {G : Type} [Group G]

attribute [local instance] OAI.Higman.RecognizingStack.instFintypeMEdge
lemma store_push (s : List Γ') (a : Γ') :
    update (store s) .main (a :: store s .main) = store (a::s) := by
  funext k
  cases k <;> simp [store]

lemma initial_forget (c : Code) (w : List Letter) :
    TM2StackCompiler.forget tr (support c) (store (encoded w),initialState c) =
      MicroTM2.translate tr (init c [code w]) := by
  simp [TM2StackCompiler.forget,initialState,MicroTM2.translate,init,store,encoded,trNat_code]
  rfl

lemma correct_seed (c : Code) (weight : Letter → G) : Correct c weight 1 (seed c) :=
  ⟨[],rfl,rfl⟩

lemma correct_step (c : Code) (weight : Letter → G) (e : Edge c)
    (S T : K' → List Γ') (g : G) (hr : (prog c weight e).action.Rel S T)
    (hc : Correct c weight g (S,(prog c weight e).source)) :
    Correct c weight (g * (prog c weight e).weight) (T,(prog c weight e).target) := by
  cases e with
  | first a =>
    obtain ⟨w,rfl,hg⟩ := hc
    obtain ⟨t,ht,rfl⟩ := hr
    cases ht
    exact ⟨w,store_push _ _,by simpa [prog] using hg⟩
  | second a =>
    obtain ⟨w,rfl,hg⟩ := hc
    obtain ⟨t,ht,rfl⟩ := hr
    cases ht
    exact ⟨w,store_push _ _,by simpa [prog] using hg⟩
  | third a =>
    obtain ⟨w,rfl,rfl⟩ := hc
    obtain ⟨t,ht,rfl⟩ := hr
    cases ht
    refine ⟨a::w,?_,rfl⟩
    exact store_push _ _
  | enter =>
    obtain ⟨w,rfl,hg⟩ := hc
    cases hr
    refine ⟨w,by simpa [prog] using hg,?_⟩
    rw [initial_forget]
    exact .refl
  | machine e =>
    obtain ⟨w,hg,hh⟩ := hc
    refine ⟨w,by simpa [prog] using hg,hh.tail ?_⟩
    exact TM2StackCompiler.compile_sound tr (support c) (tr_supports c Cont'.halt).2 e S T hr
  | exit v =>
    obtain ⟨w,hg,hh⟩ := hc
    cases hr
    refine ⟨w,by simpa [prog] using hg,?_⟩
    apply (RangeRecognizer.halt_iff_dom c [code w]).mp
    exact ⟨S,v,(MicroTM2.reaches_halt_iff tr _ S v).mpr hh⟩

lemma run_correct (c : Code) (weight : Letter → G) {s : List (Edge c)}
    {d : (K' → List Γ') × State c} (h : Run (prog c weight) (seed c) s d) :
    Correct c weight (HistoryMachine.value (fun e ↦ (prog c weight e).weight) s) d := by
  induction h with
  | start => exact correct_seed c weight
  | step e S T hr h ih => exact correct_step c weight e S T _ hr ih

lemma build_word (c : Code) (weight : Letter → G) (w : List Letter) :
    ∃ s, Run (prog c weight) (seed c) s (store (encoded w),.ready) ∧
      HistoryMachine.value (fun e ↦ (prog c weight e).weight) s = HistoryMachine.value weight w := by
  induction w with
  | nil => exact ⟨[],Run.start,rfl⟩
  | cons a w ih =>
    obtain ⟨s,hs,hv⟩ := ih
    refine ⟨.third a :: .second a :: .first a :: s,?_,?_⟩
    · apply Run.step (prog := prog c weight) (Edge.third a) (store (symbol a.2.1 :: symbol a.2.2 :: encoded w)) _
      · exact ⟨_,rfl,(store_push _ _).symm⟩
      apply Run.step (prog := prog c weight) (Edge.second a) (store (symbol a.2.2 :: encoded w)) _
      · exact ⟨_,rfl,(store_push _ _).symm⟩
      apply Run.step (prog := prog c weight) (Edge.first a) (store (encoded w)) _
      · exact ⟨_,rfl,(store_push _ _).symm⟩
      exact hs
    · simpa only [HistoryMachine.value,prog,mul_one] using congrArg (fun g ↦ g * weight a) hv

lemma enter_word (c : Code) (weight : Letter → G) (w : List Letter) :
    ∃ s, Run (prog c weight) (seed c) s (store (encoded w),.machine (initialState c)) ∧
      HistoryMachine.value (fun e ↦ (prog c weight e).weight) s = HistoryMachine.value weight w := by
  obtain ⟨s,hs,hv⟩ := build_word c weight w
  exact ⟨.enter::s,Run.step (prog := prog c weight) Edge.enter _ _ rfl hs,by simpa only [HistoryMachine.value,prog,mul_one] using hv⟩

lemma run_machine (c : Code) (weight : Letter → G) (w : List Letter) {s : List (MEdge c)}
    {d : (K' → List Γ') × MState c}
    (h : Run (mprog (G := G) c) (store (encoded w),initialState c) s d) :
    ∃ t, Run (prog c weight) (seed c) t (d.1,.machine d.2) ∧
      HistoryMachine.value (fun e ↦ (prog c weight e).weight) t = HistoryMachine.value weight w := by
  induction h with
  | start => exact enter_word c weight w
  | step e S T hr h ih =>
    obtain ⟨t,ht,hv⟩ := ih
    exact ⟨.machine e::t,Run.step (prog := prog c weight) (Edge.machine e) S T hr ht,
      by simpa only [HistoryMachine.value,prog,mul_one] using hv⟩

lemma halt_word (c : Code) (weight : Letter → G) (w : List Letter) (h : (c.eval [code w]).Dom) :
    HistoryMachine.value weight w ∈ outputs (prog c weight) (seed c) .done := by
  obtain ⟨S,v,hm⟩ := (RangeRecognizer.halt_iff_dom c [code w]).mpr h
  have hh := (MicroTM2.reaches_halt_iff tr _ S v).mp hm
  rw [← initial_forget c w] at hh
  obtain ⟨s,d,hr,hd⟩ := TM2StackCompiler.reaches_complete (G := G) tr (support c)
    (tr_supports c Cont'.halt).2 hh
  have hq : d.2 = finalState c v := by
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg (fun x ↦ x.2.1) hd
    · exact congrArg (fun x ↦ x.2.2) hd
  obtain ⟨t,ht,hv⟩ := run_machine c weight w hr
  have ht' : Run (prog c weight) (seed c) t (d.1,.machine (finalState c v)) := by
    simpa only [hq] using ht
  refine ⟨.exit v::t,d.1,Run.step (prog := prog c weight) (Edge.exit v) _ _ rfl ht',?_⟩
  simpa only [HistoryMachine.value,prog,mul_one] using hv.symm

theorem outputs_eq (c : Code) (weight : Letter → G) :
    outputs (prog c weight) (seed c) .done =
      {g | ∃ w, (c.eval [code w]).Dom ∧ g = HistoryMachine.value weight w} := by
  ext g
  constructor
  · rintro ⟨s,S,hs,rfl⟩
    obtain ⟨w,hw,hd⟩ := run_correct c weight hs
    exact ⟨w,hd,hw⟩
  · rintro ⟨w,hd,rfl⟩
    exact halt_word c weight w hd

end Higman.RecognizingStack

namespace Higman
open WordBinary
variable {G : Type} [Group G] [Group.IsFinitelyPresented G]

theorem benign_enumerated_words (enumerate : ℕ → List Letter)
    (he : Computable enumerate) (weight : Letter → G) :
    IsBenign (Subgroup.closure (Set.range (fun n ↦ HistoryMachine.value weight (enumerate n)))) := by
  obtain ⟨c,hc⟩ := RangeRecognizer.exists_code (fun n ↦ code (enumerate n))
    (code_primrec.to_comp.comp he)
  have hh := StackProgram.benign_outputs (RecognizingStack.prog c weight)
    (RecognizingStack.seed c) RecognizingStack.State.done
  rw [RecognizingStack.outputs_eq] at hh
  have hs : {g | ∃ w, (c.eval [code w]).Dom ∧ g = HistoryMachine.value weight w} =
      Set.range (fun n ↦ HistoryMachine.value weight (enumerate n)) := by
    ext g
    constructor
    · rintro ⟨w,hw,rfl⟩
      obtain ⟨n,hn⟩ := (hc (code w)).mp hw
      exact ⟨n,congrArg (HistoryMachine.value weight) (code_injective hn)⟩
    · rintro ⟨n,rfl⟩
      exact ⟨enumerate n,(hc _).mpr ⟨n,rfl⟩,rfl⟩
  rwa [hs] at hh

end Higman

namespace Higman.HistoryMachine
variable {E G : Type*} [Group G]
lemma value_append (weight : E → G) (v w : List E) :
    value weight (v ++ w) = value weight w * value weight v := by
  induction v with
  | nil => simp [value]
  | cons a v ih => simp only [List.cons_append,value,ih,mul_assoc]
end Higman.HistoryMachine

namespace Higman.NormalWords

section
open WordBinary

lemma encoded_value (w : Raw) : HistoryMachine.value weight (encodeWord w) = FreeGroup.mk w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    simp only [encodeWord,List.reverse_cons,List.map_append,List.map_cons,List.map_nil,
      HistoryMachine.value_append,HistoryMachine.value,one_mul] at *
    rw [ih]
    rcases a with ⟨a,b⟩
    cases a <;> cases b <;> rfl

lemma encodeWord_primrec : Primrec encodeWord :=
  Primrec.list_map Primrec.list_reverse ((Primrec.dom_finite encodeLetter).comp Primrec.snd)

lemma conjugator_primrec : Primrec conjugator :=
  Primrec.option_getD.comp Primrec.decode (Primrec.const [])

lemma invRev_primrec : Primrec (@FreeGroup.invRev Alphabet) := by
  unfold FreeGroup.invRev
  apply Primrec.list_reverse.comp
  apply Primrec.list_map Primrec.id
  exact (Primrec.fst.comp Primrec.snd).pair
    ((Primrec.dom_bool Bool.not).comp (Primrec.snd.comp Primrec.snd))

lemma enumerate_computable (r : ℕ → Raw) (hr : Computable r) : Computable (enumerate r) := by
  apply encodeWord_primrec.to_comp.comp
  have hc : Computable (fun n : ℕ ↦ conjugator n.unpair.1) :=
    conjugator_primrec.to_comp.comp (Primrec.fst.comp Primrec.unpair).to_comp
  exact Primrec.list_append.to_comp.comp
    (Primrec.list_append.to_comp.comp hc (hr.comp (Primrec.snd.comp Primrec.unpair).to_comp))
    (invRev_primrec.to_comp.comp hc)

lemma conjugator_encode (w : Raw) : conjugator (Encodable.encode w) = w := by
  simp only [conjugator,Encodable.encodek,Option.getD_some]

lemma mk_conjugated (r : ℕ → Raw) (n : ℕ) :
    FreeGroup.mk (conjugated r n) = FreeGroup.mk (conjugator n.unpair.1) *
      FreeGroup.mk (r n.unpair.2) * (FreeGroup.mk (conjugator n.unpair.1))⁻¹ := by
  simp only [conjugated,← FreeGroup.mul_mk,← FreeGroup.inv_mk]

theorem range_values (r : ℕ → Raw) :
    Set.range (fun n ↦ HistoryMachine.value weight (enumerate r n)) =
      Group.conjugatesOfSet (Set.range (fun n ↦ FreeGroup.mk (r n))) := by
  ext g
  constructor
  · rintro ⟨n,rfl⟩
    change HistoryMachine.value weight (encodeWord (conjugated r n)) ∈ _
    rw [encoded_value,mk_conjugated]
    exact Group.mem_conjugatesOfSet_iff.mpr
      ⟨_,⟨n.unpair.2,rfl⟩,isConj_iff.mpr ⟨_,rfl⟩⟩
  · intro h
    obtain ⟨x,⟨k,rfl⟩,hx⟩ := Group.mem_conjugatesOfSet_iff.mp h
    obtain ⟨a,ha⟩ := isConj_iff.mp hx
    obtain ⟨w,rfl⟩ := Quot.exists_rep a
    refine ⟨Nat.pair (Encodable.encode w) k,?_⟩
    simp only [enumerate,encoded_value,mk_conjugated,Nat.unpair_pair,conjugator_encode]
    exact ha

end

theorem benign_normalClosure_oai (r : ℕ → Raw) (hr : Computable r) :
    IsBenign (Subgroup.normalClosure (Set.range (fun n ↦ FreeGroup.mk (r n)))) := by
  have h := benign_enumerated_words (enumerate r) (enumerate_computable r hr) weight
  rw [range_values] at h
  exact h

end Higman.NormalWords

end

end OAI
end

theorem solution : type_of% @OAI.Higman.NormalWords.benign_normalClosure_oai := @OAI.Higman.NormalWords.benign_normalClosure_oai
