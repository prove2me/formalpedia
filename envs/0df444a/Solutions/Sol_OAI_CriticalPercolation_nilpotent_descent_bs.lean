-- Prove2me | solution 1 for OAI.CriticalPercolation.nilpotent_descent_bs
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T14:04:28.179764+00:00
-- url     : https://prove2.me/submissions/0f4b72c9-d4b5-49da-8bd4-f49cb20a6401

import Mathlib
import Definitions.Def_OAIQ078B000
import Definitions.Def_OAIQ078B001

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Nilpotent_CentralCommutatorGeneration
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function
open scoped Classical commutatorElement

namespace CriticalPercolation
variable {G : Type*} [Group G]

private lemma central_conjugation {z : G} (hz : z∈Subgroup.center G) (a : G) :
    a*z*a⁻¹=z := by
  rw [Subgroup.mem_center_iff.mp hz a,mul_assoc,mul_inv_cancel,mul_one]

private lemma central_comm_inv_left {a b : G} (h : ⁅a,b⁆∈Subgroup.center G) :
    ⁅a⁻¹,b⁆=⁅a,b⁆⁻¹ := by
  rw [commutatorElement_inv_left,←commutatorElement_inv]
  simpa using central_conjugation ((Subgroup.center G).inv_mem h) a⁻¹

private lemma central_comm_inv_right {a b : G} (h : ⁅a,b⁆∈Subgroup.center G) :
    ⁅a,b⁻¹⁆=⁅a,b⁆⁻¹ := by
  rw [commutatorElement_inv_right,←commutatorElement_inv]
  simpa using central_conjugation ((Subgroup.center G).inv_mem h) b⁻¹

theorem central_commutator_generated (S T : Set G)
    (hc : ⁅Subgroup.closure S,Subgroup.closure T⁆≤Subgroup.center G) :
    ⁅Subgroup.closure S,Subgroup.closure T⁆=
      Subgroup.closure (Set.image2 (fun a b : G => ⁅a,b⁆) S T) := by
  let K := Subgroup.closure (Set.image2 (fun a b : G => ⁅a,b⁆) S T)
  have hz {a b : G} (ha : a∈Subgroup.closure S) (hb : b∈Subgroup.closure T) :
      ⁅a,b⁆∈Subgroup.center G := hc (Subgroup.commutator_mem_commutator ha hb)
  apply le_antisymm
  · apply Subgroup.commutator_le.mpr
    intro a ha
    induction ha using Subgroup.closure_induction with
    | mem a ha =>
      intro b hb
      induction hb using Subgroup.closure_induction with
      | mem b hb => exact Subgroup.subset_closure (Set.mem_image2.mpr ⟨a,ha,b,hb,rfl⟩)
      | one => simp
      | mul b c hb hc' ihb ihc =>
        rw [commutatorElement_mul_right_eq_mul_conj]
        have he : ⁅a,b⁆*b*⁅a,c⁆*b⁻¹=⁅a,b⁆*(b*⁅a,c⁆*b⁻¹) := by group
        rw [he,central_conjugation (hz (Subgroup.subset_closure ha) hc') b]
        exact K.mul_mem ihb ihc
      | inv b hb ih =>
        rw [central_comm_inv_right (hz (Subgroup.subset_closure ha) hb)]
        exact K.inv_mem ih
    | one => intro b _; simp
    | mul a c ha hc' iha ihc =>
      intro b hb
      rw [commutatorElement_mul_left_eq_conj_mul,
        central_conjugation (hz hc' hb) a]
      exact K.mul_mem (ihc b hb) (iha b hb)
    | inv a ha ih =>
      intro b hb
      rw [central_comm_inv_left (hz ha hb)]
      exact K.inv_mem (ih b hb)
  · apply (Subgroup.closure_le _).mpr
    rintro z ⟨a,ha,b,hb,rfl⟩
    exact Subgroup.commutator_mem_commutator (Subgroup.subset_closure ha)
      (Subgroup.subset_closure hb)

theorem central_commutator_fg (H J : Subgroup G) (hH : H.FG) (hJ : J.FG)
    (hc : ⁅H,J⁆≤Subgroup.center G) : ⁅H,J⁆.FG := by
  obtain ⟨S,hS,hfinS⟩ := Subgroup.fg_iff H |>.mp hH
  obtain ⟨T,hT,hfinT⟩ := Subgroup.fg_iff J |>.mp hJ
  apply (Subgroup.fg_iff _).mpr
  refine ⟨Set.image2 (fun a b : G => ⁅a,b⁆) S T,?_,hfinS.image2 _ hfinT⟩
  rw [←central_commutator_generated S T (by rwa [hS,hT]),hS,hT]

theorem class_two_commutator_fg [Group.FG G]
    (hc : commutator G≤Subgroup.center G) : Group.FG (commutator G) := by
  apply (Group.fg_iff_subgroup_fg _).mpr
  exact central_commutator_fg ⊤ ⊤ (Group.fg_def.mp inferInstance)
    (Group.fg_def.mp inferInstance) hc

end CriticalPercolation
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Criticality_ClassTwoRankOne
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function
open scoped Classical commutatorElement

namespace CriticalPercolation
variable {G A : Type*} [Group G] [Group A]

theorem class_two_commutator_finite_of_cyclic_mod_torsion [Group.FG G]
    (hc : commutator G≤Subgroup.center G) (ρ : G →* A)
    (hker : ρ.ker≤Subgroup.center G) (g : G)
    (hcyc : ∀ a : G, ∃ k : ℤ, IsOfFinOrder (ρ (a*g^(-k)))) :
    (commutator G : Set G).Finite := by
  let C := commutator G
  let _ : CommGroup C := {
    (inferInstance : Group C) with
    mul_comm := fun a b => Subtype.ext (Subgroup.mem_center_iff.mp (hc b.property) a.val) }
  let _ : Group.FG C := class_two_commutator_fg hc
  let t := centralCommHom hc
  have ht (a b : G) (hb : IsOfFinOrder (ρ b)) : IsOfFinOrder (t a b) := by
    obtain ⟨m,hm,he⟩ := hb.exists_pow_eq_one
    have hpow : b^m∈ρ.ker := by change ρ (b^m)=1; rwa [map_pow]
    have hz := hker hpow
    apply isOfFinOrder_iff_pow_eq_one.mpr
    refine ⟨m,hm,?_⟩
    rw [←map_pow]
    apply Subtype.ext
    exact commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_center_iff.mp hz a)
  have hself : t g g=1 := by apply Subtype.ext; simp [t,centralCommHom,commutatorElement_def]
  have hga (a : G) : IsOfFinOrder (t g a) := by
    obtain ⟨k,hk⟩ := hcyc a
    have h := ht g (a*g^(-k)) hk
    simpa only [map_mul,map_zpow,hself,one_zpow,mul_one] using h
  have hag (a : G) : IsOfFinOrder (t a g) := by
    have he : t a g=(t g a)⁻¹ := by
      apply Subtype.ext
      exact (commutatorElement_inv g a).symm
    rw [he]
    exact (hga a).inv
  have hab (a b : G) : IsOfFinOrder (t a b) := by
    obtain ⟨k,hk⟩ := hcyc b
    have hw := ht a (b*g^(-k)) hk
    have hg : (t a g)^k∈CommGroup.torsion C :=
      (CommGroup.torsion C).zpow_mem (hag a) k
    have hh := (CommGroup.torsion C).mul_mem hw hg
    have he : t a (b*g^(-k))*(t a g)^k=t a b := by
      rw [map_mul,map_zpow,zpow_neg]
      group
    rw [he] at hh
    exact hh
  have hsub : C≤(CommGroup.torsion C).map C.subtype := by
    apply Subgroup.commutator_le.mpr
    intro a _ b _
    exact ⟨t a b,hab a b,rfl⟩
  let _ : Finite C := CommGroup.finite_of_fg_isMulTorsion C (fun c => by
    obtain ⟨d,hd,he⟩ := hsub c.property
    change IsOfFinOrder d at hd
    exact (show d=c from Subtype.ext he) ▸ hd)
  exact Set.toFinite _

end CriticalPercolation
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Criticality_SubgroupFiniteIndexExtension
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function
open scoped Classical Pointwise

namespace CriticalPercolation

theorem subgroup_finiteIndex_of_image_and_kernel {G Q : Type*} [Group G] [Group Q]
    (f : G →* Q) (hf : Surjective f) (J : Subgroup G)
    [(J.map f).FiniteIndex] [(J.subgroupOf f.ker).FiniteIndex] : J.FiniteIndex := by
  let S := J ⊔ f.ker
  have hS : S.FiniteIndex := by
    constructor
    have hn := (inferInstance : (J.map f).FiniteIndex).index_ne_zero
    rw [Subgroup.index_map,f.range_eq_top_of_surjective hf,Subgroup.index_top,mul_one] at hn
    exact hn
  let _ := hS
  let inc : f.ker →* S := {
    toFun := fun x => ⟨x.val,(le_sup_right : f.ker≤J⊔f.ker) x.property⟩
    map_one' := rfl
    map_mul' := by intros; rfl }
  let F : (f.ker ⧸ J.subgroupOf f.ker) → (S ⧸ J.subgroupOf S) :=
    Quotient.map inc (by
      intro a b hab
      apply (QuotientGroup.leftRel_apply (s := J.subgroupOf S)).mpr
      exact (QuotientGroup.leftRel_apply (s := J.subgroupOf f.ker)).mp hab)
  have hF : Surjective F := by
    intro y
    obtain ⟨x,rfl⟩ := QuotientGroup.mk_surjective y
    have hx : x.val∈(f.ker : Set G)*(J : Set G) := by
      rw [←Subgroup.normal_mul, sup_comm]
      exact x.property
    obtain ⟨a,ha,b,hb,he⟩ := hx
    refine ⟨QuotientGroup.mk ⟨a,ha⟩,?_⟩
    apply Quotient.sound
    apply (QuotientGroup.leftRel_apply (s := J.subgroupOf S)).mpr
    change a⁻¹*x.val∈J
    rw [←he,inv_mul_cancel_left]
    exact hb
  let _ : Finite (S ⧸ J.subgroupOf S) := Finite.of_surjective F hF
  apply Subgroup.finiteIndex_iff_finite_quotient.mpr
  exact Finite.of_equiv _ (Subgroup.quotientEquivProdOfLE (le_sup_left : J≤S)).symm

end CriticalPercolation
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_FiniteKernelDescent
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function
open scoped Classical

namespace CriticalPercolation

universe u v

lemma hom_finite_preimage_of_finite_kernel {G H : Type*} [Group G] [Group H]
    (f : G →* H) (hk : (f.ker : Set G).Finite) (S : Set H) (hS : S.Finite) :
    (f ⁻¹' S).Finite := by
  let _ := hk.to_subtype
  have hfib : ∀ a : H, (f ⁻¹' {a}).Finite := by
    intro a
    by_cases ha : (f ⁻¹' {a}).Nonempty
    · obtain ⟨x,hx⟩ := ha
      change f x=a at hx
      rw [←hx]
      let _ := Finite.of_equiv _ (f.fiberEquivKer x).symm
      exact Set.toFinite _
    · rw [Set.not_nonempty_iff_eq_empty.mp ha]
      exact Set.finite_empty
  apply (hS.biUnion (fun a _ => hfib a)).subset
  exact fun x hx => Set.mem_iUnion₂.mpr ⟨f x,hx,rfl⟩

lemma hom_finite_composite_kernel {G H K : Type*} [Group G] [Group H] [Group K]
    (f : G →* H) (g : H →* K)
    (hf : (f.ker : Set G).Finite) (hg : (g.ker : Set H).Finite) :
    ((g.comp f).ker : Set G).Finite :=
  hom_finite_preimage_of_finite_kernel f hf g.ker hg

end CriticalPercolation
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Nilpotent_AbelianAlternatives
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function
open scoped Classical DirectSum

namespace CriticalPercolation

theorem additive_abelian_alternatives (A : Type*) [AddCommGroup A] [AddGroup.FG A] :
    Finite A ∨
      (∃ φ : A →+ ℤ, Surjective φ ∧ (φ.ker : Set A).Finite) ∨
      (∃ φ : A →+ (ℤ×ℤ), Surjective φ) := by
  obtain ⟨n,ι,hι,p,hp,e,⟨f⟩⟩ := AddCommGroup.equiv_free_prod_directSum_zmod A
  let _ := hι
  let _ : ∀ i : ι, NeZero (p i ^ e i) := fun i => ⟨pow_ne_zero _ (hp i).ne_zero⟩
  let T := ⨁ i : ι, ZMod (p i ^ e i)
  let _ : Finite T := Finite.of_equiv _ DFinsupp.equivFunOnFintype.symm
  cases n with
  | zero =>
    exact Or.inl (Finite.of_equiv _ f.symm.toEquiv)
  | succ n =>
    cases n with
    | zero =>
      let φ := (Finsupp.applyAddHom (0 : Fin 1)).comp
        ((AddMonoidHom.fst (Fin 1 →₀ ℤ) T).comp f.toAddMonoidHom)
      have hs : Surjective φ := by
        intro z
        refine ⟨f.symm (Finsupp.single 0 z,0),?_⟩
        simp [φ]
      have hk : (φ.ker : Set A).Finite := by
        apply (Set.finite_singleton (0 : Fin 1 →₀ ℤ)).prod (Set.toFinite (Set.univ : Set T)) |>.preimage f.injective.injOn |>.subset
        intro x hx
        change (f x).1∈({0} : Set (Fin 1 →₀ ℤ)) ∧ (f x).2∈(Set.univ : Set T)
        refine ⟨?_,Set.mem_univ _⟩
        apply Finsupp.ext
        intro i
        have hi : i=(0 : Fin 1) := Fin.ext (by omega)
        subst i
        exact hx
      exact Or.inr (Or.inl ⟨φ,hs,hk⟩)
    | succ n =>
      let ev : (Fin (n+2) →₀ ℤ) →+ (ℤ×ℤ) :=
        (Finsupp.applyAddHom ⟨0,by omega⟩).prod (Finsupp.applyAddHom ⟨1,by omega⟩)
      let φ := ev.comp ((AddMonoidHom.fst (Fin (n+2) →₀ ℤ) T).comp f.toAddMonoidHom)
      refine Or.inr (Or.inr ⟨φ,?_⟩)
      intro z
      refine ⟨f.symm (Finsupp.single ⟨0,by omega⟩ z.1 +
        Finsupp.single ⟨1,by omega⟩ z.2,0),?_⟩
      simp [φ,ev]

theorem abelian_alternatives (A : Type*) [CommGroup A] [Group.FG A] :
    Finite A ∨
      (∃ φ : A →* Multiplicative ℤ, Surjective φ ∧ (φ.ker : Set A).Finite) ∨
      (∃ φ : A →* Multiplicative (ℤ×ℤ), Surjective φ) := by
  rcases additive_abelian_alternatives (Additive A) with h | ⟨φ,hs,hk⟩ | ⟨φ,hs⟩
  · let _ := h
    exact Or.inl (Finite.of_equiv _ Additive.toMul)
  · refine Or.inr (Or.inl ⟨φ.toMultiplicativeRight,?_,?_⟩)
    · exact fun z => hs z.toAdd
    · exact hk
  · refine Or.inr (Or.inr ⟨φ.toMultiplicativeRight,?_⟩)
    exact fun z => hs z.toAdd

end CriticalPercolation
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Nilpotent_CentralCommutatorQuotient
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function
open scoped Classical commutatorElement

namespace CriticalPercolation
variable {G Q : Type*} [Group G] [Group Q]

lemma finite_generating_lifts [Group.FG Q] {H : Type*} [Group H]
    (f : H →* Q) (hf : Surjective f) :
    ∃ S : Set H, S.Finite ∧ (Subgroup.closure S).map f=⊤ := by
  obtain ⟨T,hT,hfin⟩ := Group.fg_iff.mp (inferInstance : Group.FG Q)
  choose s hs using hf
  refine ⟨s '' T,hfin.image s,?_⟩
  rw [MonoidHom.map_closure,Set.image_image]
  have he : (fun x => f (s x))=id := funext hs
  rw [he,Set.image_id,hT]

theorem central_commutator_fg_of_quotient [Group.FG G] [Group.FG Q]
    (H : Subgroup G) (f : H →* Q) (hf : Surjective f)
    (hker : f.ker.map H.subtype≤Subgroup.center G)
    (hcentral : ⁅(⊤ : Subgroup G),H⁆≤Subgroup.center G) :
    ⁅(⊤ : Subgroup G),H⁆.FG := by
  obtain ⟨S,hS,himage⟩ := finite_generating_lifts f hf
  let L := Subgroup.closure S
  let M := L.map H.subtype
  have hM : M.FG := by
    apply (Subgroup.fg_iff M).mpr
    refine ⟨H.subtype '' S,?_,hS.image H.subtype⟩
    exact (MonoidHom.map_closure H.subtype S).symm
  have hMH : M≤H := by
    rintro x ⟨y,_,rfl⟩
    exact y.property
  suffices he : ⁅(⊤ : Subgroup G),H⁆=⁅(⊤ : Subgroup G),M⁆ by
    rw [he]
    exact central_commutator_fg ⊤ M (Group.fg_def.mp inferInstance) hM
      ((Subgroup.commutator_mono le_rfl hMH).trans hcentral)
  apply le_antisymm
  · apply Subgroup.commutator_le.mpr
    intro g _ h hh
    have him : f ⟨h,hh⟩∈L.map f := by rw [himage]; trivial
    obtain ⟨l,hl,he⟩ := him
    let z : H := l⁻¹*⟨h,hh⟩
    have hzker : z∈f.ker := by
      change f (l⁻¹*⟨h,hh⟩)=1
      rw [map_mul,map_inv,he,inv_mul_cancel]
    have hz : (z:G)∈Subgroup.center G := hker ⟨z,hzker,rfl⟩
    have hgz : ⁅g,(z:G)⁆=1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_center_iff.mp hz g)
    have hdecomp : h=(l:G)*(z:G) := by simp [z]
    rw [hdecomp,commutatorElement_mul_right_eq_mul_conj,hgz]
    simpa using (Subgroup.commutator_mem_commutator (H₁ := (⊤ : Subgroup G))
      (H₂ := M) (by trivial) (show (l:G)∈M from ⟨l,hl,rfl⟩) : ⁅g,(l:G)⁆∈⁅⊤,M⁆)
  · exact Subgroup.commutator_mono le_rfl hMH

end CriticalPercolation
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Nilpotent_CentralCommutatorFinite
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function
open scoped Classical commutatorElement

namespace CriticalPercolation
variable {G Q : Type*} [Group G] [Group Q]

theorem central_commutator_finite_of_quotient [Group.FG G] [Finite Q]
    (H : Subgroup G) (f : H →* Q) (hf : Surjective f)
    (hker : f.ker.map H.subtype≤Subgroup.center G)
    (hc : ⁅(⊤ : Subgroup G),H⁆≤Subgroup.center G) :
    ((⁅(⊤ : Subgroup G),H⁆ : Subgroup G) : Set G).Finite := by
  let C := ⁅(⊤ : Subgroup G),H⁆
  let _ : CommGroup C := {
    (inferInstance : Group C) with
    mul_comm := fun a b => Subtype.ext (Subgroup.mem_center_iff.mp (hc b.property) a.val) }
  let _ : Group.FG C := (Group.fg_iff_subgroup_fg C).mpr
    (central_commutator_fg_of_quotient H f hf hker hc)
  have hpair (a : G) (b : H) : IsOfFinOrder (⁅a,(b:G)⁆) := by
    let t : H →* G := {
      toFun := fun b => ⁅a,(b:G)⁆
      map_one' := by simp
      map_mul' := by
        intro b d
        change ⁅a,(b:G)*(d:G)⁆=⁅a,(b:G)⁆*⁅a,(d:G)⁆
        rw [commutatorElement_mul_right_eq_mul_conj]
        have hd := hc (Subgroup.commutator_mem_commutator (H₁ := (⊤ : Subgroup G))
          (by trivial) d.property : ⁅a,(d:G)⁆∈C)
        calc
          ⁅a,(b:G)⁆*(b:G)*⁅a,(d:G)⁆*(b:G)⁻¹ =
            ⁅a,(b:G)⁆*((b:G)*⁅a,(d:G)⁆)*(b:G)⁻¹ := by group
          _ = ⁅a,(b:G)⁆*(⁅a,(d:G)⁆*(b:G))*(b:G)⁻¹ := by
            rw [Subgroup.mem_center_iff.mp hd (b:G)]
          _ = _ := by group }
    obtain ⟨m,hm,he⟩ := (isOfFinOrder_of_finite (f b)).exists_pow_eq_one
    have hb : b^m∈f.ker := by change f (b^m)=1; rwa [map_pow]
    have hz : ((b^m:H):G)∈Subgroup.center G := hker ⟨b^m,hb,rfl⟩
    have heq : t (b^m)=1 := commutatorElement_eq_one_iff_mul_comm.mpr
      (Subgroup.mem_center_iff.mp hz a)
    rw [map_pow] at heq
    exact isOfFinOrder_iff_pow_eq_one.mpr ⟨m,hm,heq⟩
  have ht : C≤(CommGroup.torsion C).map C.subtype := by
    apply Subgroup.commutator_le.mpr
    intro a _ b hb
    let c : C := ⟨⁅a,b⁆,Subgroup.commutator_mem_commutator (by trivial) hb⟩
    refine ⟨c,?_,rfl⟩
    change IsOfFinOrder c
    obtain ⟨m,hm,he⟩ := (hpair a ⟨b,hb⟩).exists_pow_eq_one
    exact isOfFinOrder_iff_pow_eq_one.mpr ⟨m,hm,Subtype.ext he⟩
  let _ : Finite C := CommGroup.finite_of_fg_isMulTorsion C (fun c => by
    obtain ⟨d,hd,he⟩ := ht c.property
    have hcd : d=c := Subtype.ext he
    change IsOfFinOrder d at hd
    exact hcd ▸ hd)
  exact Set.toFinite _

end CriticalPercolation
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Nilpotent_CyclicModTorsion
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function
open scoped Classical

namespace CriticalPercolation

lemma cyclic_mod_torsion_of_finite_kernel {G A : Type*} [Group G] [Group A]
    (ρ : G →* A) (hρ : Surjective ρ) (φ : A →* Multiplicative ℤ)
    (hφ : Surjective φ) (hk : (φ.ker : Set A).Finite) :
    ∃ g : G, ∀ a : G, ∃ k : ℤ, IsOfFinOrder (ρ (a*g^(-k))) := by
  obtain ⟨g,hg⟩ := hφ.comp hρ (Multiplicative.ofAdd (1 : ℤ))
  change φ (ρ g)=Multiplicative.ofAdd (1 : ℤ) at hg
  let _ := hk.to_subtype
  refine ⟨g,fun a => ?_⟩
  let k := (φ (ρ a)).toAdd
  refine ⟨k,?_⟩
  have he : ρ (a*g^(-k))∈φ.ker := by
    change φ (ρ (a*g^(-k)))=1
    rw [map_mul,map_zpow,map_mul,map_zpow,hg]
    change (φ (ρ a)).toAdd+(-k) • (1 : ℤ)=0
    simp [k]
  obtain ⟨m,hm,heq⟩ :=
    (isOfFinOrder_of_finite (⟨ρ (a*g^(-k)),he⟩ : φ.ker)).exists_pow_eq_one
  exact isOfFinOrder_iff_pow_eq_one.mpr ⟨m,hm,congrArg Subtype.val heq⟩

end CriticalPercolation
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Nilpotent_CyclicSubgroupIndex
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function
open scoped Classical

namespace CriticalPercolation

theorem cyclic_infinite_subgroup_finiteIndex {G : Type*} [Group G]
    (e : G ≃* Multiplicative ℤ) (J : Subgroup G) [Infinite J] : J.FiniteIndex := by
  let a : Additive G ≃+ ℤ := e.toAdditive.trans (AddEquiv.additiveMultiplicative ℤ)
  let K := J.toAddSubgroup.map a.toAddMonoidHom
  obtain ⟨j,hj⟩ := exists_ne (1 : J)
  let z := a (Additive.ofMul j.val)
  have hz : z≠0 := by
    intro h
    have he : Additive.ofMul j.val=0 := a.injective (h.trans a.map_zero.symm)
    apply hj
    exact Subtype.ext he
  have hmem : z∈K := ⟨Additive.ofMul j.val,j.property,rfl⟩
  have hZ : (AddSubgroup.zmultiples z).FiniteIndex := by
    constructor
    rw [Int.index_zmultiples]
    exact Int.natAbs_ne_zero.mpr hz
  let _ := hZ
  have hK : K.FiniteIndex := AddSubgroup.finiteIndex_of_le (AddSubgroup.zmultiples_le.mpr hmem)
  constructor
  have hn := hK.index_ne_zero
  have he : K.index=J.index := by
    exact (AddSubgroup.index_map_equiv J.toAddSubgroup a).trans J.index_toAddSubgroup
  rwa [he] at hn

end CriticalPercolation
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Nilpotent_FGExtensions
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function
open scoped Classical

namespace CriticalPercolation

theorem fg_of_kernel_quotient {G Q : Type*} [Group G] [Group Q] [Group.FG Q]
    (f : G →* Q) (hf : Surjective f) [Group.FG f.ker] : Group.FG G := by
  obtain ⟨S,hS,himage⟩ := finite_generating_lifts f hf
  obtain ⟨T,hT,hfinT⟩ := Group.fg_iff.mp (inferInstance : Group.FG f.ker)
  let U := S ∪ f.ker.subtype '' T
  let L := Subgroup.closure U
  have hSle : Subgroup.closure S≤L := Subgroup.closure_mono Set.subset_union_left
  have hker : f.ker≤L := by
    have he : (Subgroup.closure T).map f.ker.subtype=f.ker := by
      rw [hT,←MonoidHom.range_eq_map,Subgroup.subtype_range]
    rw [←he,MonoidHom.map_closure]
    exact Subgroup.closure_mono Set.subset_union_right
  have htop : L=⊤ := by
    apply top_unique
    intro g _
    have hg : f g∈(Subgroup.closure S).map f := by rw [himage]; trivial
    obtain ⟨a,ha,he⟩ := hg
    have hz : a⁻¹*g∈f.ker := by
      change f (a⁻¹*g)=1
      rw [map_mul,map_inv,he,inv_mul_cancel]
    simpa using L.mul_mem (hSle ha) (hker hz)
  exact Group.fg_iff.mpr ⟨U,htop,hS.union (hfinT.image _)⟩

theorem abelian_subgroup_fg {A : Type*} [CommGroup A] [Group.FG A]
    (H : Subgroup A) : Group.FG H := by
  let K := H.toAddSubgroup.toIntSubmodule
  let _ : Module.Finite ℤ (Additive A) := Module.Finite.iff_addGroup_fg.mpr inferInstance
  let _ : AddGroup.FG K := Module.Finite.iff_addGroup_fg.mp inferInstance
  let e : Multiplicative K ≃* H := {
    toFun := fun a => ⟨a.toAdd.val.toMul,a.toAdd.property⟩
    invFun := fun h => Multiplicative.ofAdd ⟨Additive.ofMul h.val,h.property⟩
    left_inv := by intro a; rfl
    right_inv := by intro h; rfl
    map_mul' := by intros; rfl }
  exact Group.fg_of_surjective (f := e.toMonoidHom) e.surjective

end CriticalPercolation
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Nilpotent_FiniteCyclicConstruction
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u

section
section
noncomputable section
open Set Function
open scoped Classical DirectSum

namespace CriticalPercolation

lemma FiniteCyclicConstruction.of_finite_kernel {G Q : Type u} [Group G] [Group Q]
    {n : ℕ} (hQ : FiniteCyclicConstruction Q n) (f : G →* Q)
    (hf : Surjective f) [Finite f.ker] : FiniteCyclicConstruction G n := by
  simpa using FiniteCyclicConstruction.extension f hf (.finite f.ker) hQ

lemma FiniteCyclicConstruction.of_equiv {G Q : Type u} [Group G] [Group Q]
    {n : ℕ} (hQ : FiniteCyclicConstruction Q n) (e : G ≃* Q) :
    FiniteCyclicConstruction G n := by
  have he : e.toMonoidHom.ker=⊥ := e.toMonoidHom.ker_eq_bot e.injective
  let _ : Finite e.toMonoidHom.ker := he.symm ▸ (inferInstance : Finite (⊥ : Subgroup G))
  exact hQ.of_finite_kernel e.toMonoidHom e.surjective

private lemma free_finite_cyclic_construction_rank (n : ℕ) :
    ∀ (A : Type u) [AddCommGroup A] [Module.Free ℤ A] [Module.Finite ℤ A],
      Module.finrank ℤ A=n → ∃ k≤n, FiniteCyclicConstruction (Multiplicative A) k := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro A _ _ _ hrank
    let b : Module.Basis (Fin n) ℤ A := hrank ▸ Module.finBasis ℤ A
    let e := b.equivFun
    cases n with
    | zero =>
      let _ : Subsingleton A := ⟨fun x y => e.injective (funext fun i => Fin.elim0 i)⟩
      exact ⟨0,le_rfl,.finite _⟩
    | succ n =>
      let f : A →+ ULift.{u} ℤ := {
        toFun := fun a => ⟨e a 0⟩
        map_zero' := by apply ULift.ext; simp
        map_add' := by intros; apply ULift.ext; simp }
      have hf : Surjective f := by
        intro z
        exact ⟨e.symm (fun _ => z.down),by apply ULift.ext; simp [f]⟩
      let K := f.ker.toIntSubmodule
      have hzero (a : K) : e a.val 0=0 := congrArg ULift.down a.property
      let d : K →ₗ[ℤ] (Fin n → ℤ) := {
        toFun := fun a i => e a.val i.succ
        map_add' := by intros; ext i; simp
        map_smul' := by intros; ext i; simp }
      have hd : Injective d := by
        intro a a' haa
        apply Subtype.ext
        apply e.injective
        funext i
        exact Fin.cases ((hzero a).trans (hzero a').symm) (fun j => congrFun haa j) i
      have hr : Module.finrank ℤ K≤n := by
        simpa using d.finrank_le_finrank_of_injective hd
      obtain ⟨k,hk,hC⟩ := ih (Module.finrank ℤ K) (by omega) K rfl
      let ek : f.toMultiplicative.ker ≃* Multiplicative K := {
        toFun := fun a => Multiplicative.ofAdd ⟨a.val.toAdd,a.property⟩
        invFun := fun a => ⟨Multiplicative.ofAdd a.toAdd.val,a.toAdd.property⟩
        left_inv := by intro a; rfl
        right_inv := by intro a; rfl
        map_mul' := by intros; rfl }
      refine ⟨k+1,by omega,?_⟩
      exact FiniteCyclicConstruction.extension f.toMultiplicative (fun z => hf z.toAdd)
        (hC.of_equiv ek) (.cyclic _ AddEquiv.ulift.toMultiplicative)

theorem free_finite_cyclic_construction (A : Type u) [AddCommGroup A]
    [Module.Free ℤ A] [Module.Finite ℤ A] :
    ∃ n, FiniteCyclicConstruction (Multiplicative A) n := by
  obtain ⟨n,_,hn⟩ := free_finite_cyclic_construction_rank (Module.finrank ℤ A) A rfl
  exact ⟨n,hn⟩

theorem abelian_finite_cyclic_construction (A : Type u) [CommGroup A] [Group.FG A] :
    ∃ n, FiniteCyclicConstruction A n := by
  obtain ⟨n,ι,hι,p,hp,e,⟨f⟩⟩ := AddCommGroup.equiv_free_prod_directSum_zmod (Additive A)
  let _ := hι
  let _ : ∀ i : ι, NeZero (p i ^ e i) := fun i => ⟨pow_ne_zero _ (hp i).ne_zero⟩
  let T := ⨁ i : ι, ZMod (p i ^ e i)
  let _ : Finite T := Finite.of_equiv _ DFinsupp.equivFunOnFintype.symm
  let φ₀ := (AddMonoidHom.fst (Fin n →₀ ℤ) T).comp f.toAddMonoidHom
  let φ : Additive A →+ ULift.{u} (Fin n →₀ ℤ) := AddEquiv.ulift.symm.toAddMonoidHom.comp φ₀
  have hs : Surjective φ := by
    intro z
    refine ⟨f.symm (z.down,0),?_⟩
    change ULift.up (φ₀ (f.symm (z.down,0)))=z
    apply ULift.ext
    change φ₀ (f.symm (z.down,0))=z.down
    simp [φ₀]
  have hk : (φ.toMultiplicativeRight.ker : Set A).Finite := by
    apply ((Set.finite_singleton (0 : Fin n →₀ ℤ)).prod
      (Set.toFinite (Set.univ : Set T))).preimage f.injective.injOn |>.subset
    intro x hx
    exact ⟨congrArg (fun z : Multiplicative (ULift (Fin n →₀ ℤ)) => z.toAdd.down) hx,
      Set.mem_univ _⟩
  let _ := hk.to_subtype
  obtain ⟨k,hk⟩ := free_finite_cyclic_construction (ULift.{u} (Fin n →₀ ℤ))
  exact ⟨k,hk.of_finite_kernel φ.toMultiplicativeRight (fun z => hs z.toAdd)⟩

end CriticalPercolation
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Nilpotent_FiniteCyclicInheritance
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe groupUniverse

section
section
noncomputable section
open Set Function
open scoped Classical

namespace CriticalPercolation

theorem FiniteCyclicConstruction.subgroup {G : Type groupUniverse} [Group G] {n : ℕ}
    (hG : FiniteCyclicConstruction G n) :
    ∀ J : Subgroup G, ∃ m≤n, FiniteCyclicConstruction J m ∧ (m=n → J.FiniteIndex) := by
  induction hG with
  | @finite G _ _ =>
    intro J
    exact ⟨0,le_rfl,.finite _,fun _ => inferInstance⟩
  | @cyclic G _ e =>
    intro J
    cases finite_or_infinite J with
    | inl h =>
      let _ := h
      exact ⟨0,by omega,.finite _,by omega⟩
    | inr h =>
      let _ := h
      let _ : IsCyclic G := isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective
      exact ⟨1,le_rfl,.cyclic _ (intCyclicMulEquiv.symm),
        fun _ => cyclic_infinite_subgroup_finiteIndex e J⟩
  | @extension G Q _ _ f hf n m hker hquot ihker ihquot =>
    intro J
    obtain ⟨k,hk,hK,hki⟩ := ihker (J.subgroupOf f.ker)
    obtain ⟨l,hl,hL,hli⟩ := ihquot (J.map f)
    let g : J →* J.map f := {
      toFun := fun j => ⟨f j.val,⟨j.val,j.property,rfl⟩⟩
      map_one' := by apply Subtype.ext; exact f.map_one
      map_mul' := by intros; apply Subtype.ext; exact f.map_mul _ _ }
    have hg : Surjective g := by
      rintro ⟨q,x,hx,rfl⟩
      exact ⟨⟨x,hx⟩,rfl⟩
    let e : g.ker ≃* J.subgroupOf f.ker := {
      toFun := fun a => ⟨⟨a.val.val,congrArg Subtype.val a.property⟩,a.val.property⟩
      invFun := fun a => ⟨⟨a.val.val,a.property⟩,Subtype.ext a.val.property⟩
      left_inv := by intro a; rfl
      right_inv := by intro a; rfl
      map_mul' := by intros; rfl }
    refine ⟨k+l,by omega,FiniteCyclicConstruction.extension g hg (hK.of_equiv e) hL,?_⟩
    intro he
    let _ := hki (by omega)
    let _ := hli (by omega)
    exact subgroup_finiteIndex_of_image_and_kernel f hf J

end CriticalPercolation
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Nilpotent_LowerCentralFG
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function
open scoped Classical commutatorElement

namespace CriticalPercolation
variable (G : Type*) [Group G]

lemma lowerFactor_central (n : ℕ) : lowerFactor G n≤
    Subgroup.center (G ⧸ (⊤ : Subgroup G).lowerCentralSeries (n+1)) := by
  apply Subgroup.commutator_top_right_eq_bot_iff_le_center.mp
  let f := QuotientGroup.mk' ((⊤ : Subgroup G).lowerCentralSeries (n+1))
  have hf : (⊤ : Subgroup G).map f=⊤ :=
    Subgroup.map_top_of_surjective f QuotientGroup.mk_surjective
  change ⁅((⊤ : Subgroup G).lowerCentralSeries n).map f,⊤⁆=⊥
  rw [←hf,←Subgroup.map_commutator,←Subgroup.lowerCentralSeries_succ]
  apply (Subgroup.map_eq_bot_iff _).mpr
  rw [QuotientGroup.ker_mk']

theorem lowerFactor_fg [Group.FG G] (n : ℕ) : Group.FG (lowerFactor G n) := by
  induction n with
  | zero =>
    unfold lowerFactor
    rw [Subgroup.lowerCentralSeries_zero,←MonoidHom.range_eq_map]
    infer_instance
  | succ n ih =>
    let N := (⊤ : Subgroup G).lowerCentralSeries (n+1)
    let M := (⊤ : Subgroup G).lowerCentralSeries (n+2)
    let π := QuotientGroup.mk' M
    let σ := QuotientGroup.mk' N
    have hMN : M≤N := (⊤ : Subgroup G).lowerCentralSeries_antitone (by omega)
    let q : (G ⧸ M) →* (G ⧸ N) := QuotientGroup.lift M σ (by
      rw [QuotientGroup.ker_mk']; exact hMN)
    have hq (g : G) : q (π g)=σ g := rfl
    let H := ((⊤ : Subgroup G).lowerCentralSeries n).map π
    let f : H →* lowerFactor G n := {
      toFun := fun h => ⟨q h.val,by
        obtain ⟨g,hg,he⟩ := h.property
        exact ⟨g,hg,by change σ g=q h.val; rw [←he,hq]⟩⟩
      map_one' := by apply Subtype.ext; exact q.map_one
      map_mul' := by intros; apply Subtype.ext; exact q.map_mul _ _ }
    have hf : Surjective f := by
      rintro ⟨x,g,hg,rfl⟩
      exact ⟨⟨π g,⟨g,hg,rfl⟩⟩,rfl⟩
    have hker : f.ker.map H.subtype≤Subgroup.center (G ⧸ M) := by
      rintro x ⟨h,hh,rfl⟩
      obtain ⟨g,hg,he⟩ := h.property
      apply lowerFactor_central G (n+1)
      refine ⟨g,?_,he⟩
      have heq : σ g=1 := by
        rw [←hq,he]
        exact congrArg Subtype.val hh
      change g∈N
      rw [←QuotientGroup.ker_mk' N]
      exact heq
    have hcomm : ⁅(⊤ : Subgroup (G ⧸ M)),H⁆=lowerFactor G (n+1) := by
      have hπ : (⊤ : Subgroup G).map π=⊤ :=
        Subgroup.map_top_of_surjective π QuotientGroup.mk_surjective
      change ⁅⊤,((⊤ : Subgroup G).lowerCentralSeries n).map π⁆=
        ((⊤ : Subgroup G).lowerCentralSeries (n+1)).map π
      rw [←hπ,←Subgroup.map_commutator,Subgroup.commutator_comm,
        ←Subgroup.lowerCentralSeries_succ]
    let _ := ih
    have hfg := central_commutator_fg_of_quotient H f hf hker
      (hcomm ▸ lowerFactor_central G (n+1))
    apply (Group.fg_iff_subgroup_fg _).mpr
    rwa [hcomm] at hfg

end CriticalPercolation
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Nilpotent_LowerCentralFinite
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function
open scoped Classical commutatorElement

namespace CriticalPercolation
variable (G : Type*) [Group G]

theorem lowerFactor_finite [Group.FG G] [Finite (lowerFactor G 0)] (n : ℕ) :
    Finite (lowerFactor G n) := by
  induction n with
  | zero => infer_instance
  | succ n ih =>
    let N := (⊤ : Subgroup G).lowerCentralSeries (n+1)
    let M := (⊤ : Subgroup G).lowerCentralSeries (n+2)
    let π := QuotientGroup.mk' M
    let σ := QuotientGroup.mk' N
    have hMN : M≤N := (⊤ : Subgroup G).lowerCentralSeries_antitone (by omega)
    let q : (G ⧸ M) →* (G ⧸ N) := QuotientGroup.lift M σ (by
      rw [QuotientGroup.ker_mk']; exact hMN)
    have hq (g : G) : q (π g)=σ g := rfl
    let H := ((⊤ : Subgroup G).lowerCentralSeries n).map π
    let f : H →* lowerFactor G n := {
      toFun := fun h => ⟨q h.val,by
        obtain ⟨g,hg,he⟩ := h.property
        exact ⟨g,hg,by change σ g=q h.val; rw [←he,hq]⟩⟩
      map_one' := by apply Subtype.ext; exact q.map_one
      map_mul' := by intros; apply Subtype.ext; exact q.map_mul _ _ }
    have hf : Surjective f := by
      rintro ⟨x,g,hg,rfl⟩
      exact ⟨⟨π g,⟨g,hg,rfl⟩⟩,rfl⟩
    have hker : f.ker.map H.subtype≤Subgroup.center (G ⧸ M) := by
      rintro x ⟨h,hh,rfl⟩
      obtain ⟨g,hg,he⟩ := h.property
      apply lowerFactor_central G (n+1)
      refine ⟨g,?_,he⟩
      have heq : σ g=1 := by
        rw [←hq,he]
        exact congrArg Subtype.val hh
      change g∈N
      rw [←QuotientGroup.ker_mk' N]
      exact heq
    have hcomm : ⁅(⊤ : Subgroup (G ⧸ M)),H⁆=lowerFactor G (n+1) := by
      have hπ : (⊤ : Subgroup G).map π=⊤ :=
        Subgroup.map_top_of_surjective π QuotientGroup.mk_surjective
      change ⁅⊤,((⊤ : Subgroup G).lowerCentralSeries n).map π⁆=
        ((⊤ : Subgroup G).lowerCentralSeries (n+1)).map π
      rw [←hπ,←Subgroup.map_commutator,Subgroup.commutator_comm,
        ←Subgroup.lowerCentralSeries_succ]
    let _ := ih
    have hfin := central_commutator_finite_of_quotient H f hf hker
      (hcomm ▸ lowerFactor_central G (n+1))
    rw [hcomm] at hfin
    exact hfin.to_subtype

end CriticalPercolation
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Nilpotent_LowerCentralTailFinite
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function
open scoped Classical commutatorElement

namespace CriticalPercolation

lemma lowerFactor_finite_step (G : Type*) [Group G] [Group.FG G] (n : ℕ)
    [Finite (lowerFactor G n)] : Finite (lowerFactor G (n+1)) := by
  let N := (⊤ : Subgroup G).lowerCentralSeries (n+1)
  let M := (⊤ : Subgroup G).lowerCentralSeries (n+2)
  let π := QuotientGroup.mk' M
  let σ := QuotientGroup.mk' N
  have hMN : M≤N := (⊤ : Subgroup G).lowerCentralSeries_antitone (by omega)
  let q : (G ⧸ M) →* (G ⧸ N) := QuotientGroup.lift M σ (by
    rw [QuotientGroup.ker_mk']; exact hMN)
  have hq (g : G) : q (π g)=σ g := rfl
  let H := ((⊤ : Subgroup G).lowerCentralSeries n).map π
  let f : H →* lowerFactor G n := {
    toFun := fun h => ⟨q h.val,by
      obtain ⟨g,hg,he⟩ := h.property
      exact ⟨g,hg,by change σ g=q h.val; rw [←he,hq]⟩⟩
    map_one' := by apply Subtype.ext; exact q.map_one
    map_mul' := by intros; apply Subtype.ext; exact q.map_mul _ _ }
  have hf : Surjective f := by
    rintro ⟨x,g,hg,rfl⟩
    exact ⟨⟨π g,⟨g,hg,rfl⟩⟩,rfl⟩
  have hker : f.ker.map H.subtype≤Subgroup.center (G ⧸ M) := by
    rintro x ⟨h,hh,rfl⟩
    obtain ⟨g,hg,he⟩ := h.property
    apply lowerFactor_central G (n+1)
    refine ⟨g,?_,he⟩
    have heq : σ g=1 := by
      rw [←hq,he]
      exact congrArg Subtype.val hh
    change g∈N
    rw [←QuotientGroup.ker_mk' N]
    exact heq
  have hcomm : ⁅(⊤ : Subgroup (G ⧸ M)),H⁆=lowerFactor G (n+1) := by
    have hπ : (⊤ : Subgroup G).map π=⊤ :=
      Subgroup.map_top_of_surjective π QuotientGroup.mk_surjective
    change ⁅⊤,((⊤ : Subgroup G).lowerCentralSeries n).map π⁆=
      ((⊤ : Subgroup G).lowerCentralSeries (n+1)).map π
    rw [←hπ,←Subgroup.map_commutator,Subgroup.commutator_comm,
      ←Subgroup.lowerCentralSeries_succ]
  have hfin := central_commutator_finite_of_quotient H f hf hker
    (hcomm ▸ lowerFactor_central G (n+1))
  rw [hcomm] at hfin
  exact hfin.to_subtype

theorem nilpotent_lower_finite_of_tail (G : Type*) [Group G]
    [Group.IsNilpotent G] (start : ℕ)
    (hfin : ∀ n, start≤n → Finite (lowerFactor G n)) :
    Finite ((⊤ : Subgroup G).lowerCentralSeries start) := by
  obtain ⟨c,hc⟩ := Subgroup.nilpotent_iff_lowerCentralSeries.mp
    (inferInstance : Group.IsNilpotent G)
  let L := fun n => (⊤ : Subgroup G).lowerCentralSeries n
  have step (n : ℕ) (hsn : start≤n) (hn : Finite (L (n+1))) : Finite (L n) := by
    let F := lowerFactor G n
    let _ : Finite F := hfin n hsn
    let q := QuotientGroup.mk' (L (n+1))
    let f : L n →* F := {
      toFun := fun x => ⟨q x.val,⟨x.val,x.property,rfl⟩⟩
      map_one' := by apply Subtype.ext; exact q.map_one
      map_mul' := by intros; apply Subtype.ext; exact q.map_mul _ _ }
    have hemem (x : L n) : x∈f.ker ↔ x.val∈L (n+1) := by
      change f x=1 ↔ _
      rw [Subtype.ext_iff]
      change q x.val=1 ↔ _
      exact QuotientGroup.eq_one_iff _
    let e : L (n+1) ≃ f.ker := {
      toFun := fun x => ⟨⟨x.val,
        (⊤ : Subgroup G).lowerCentralSeries_antitone (Nat.le_succ n) x.property⟩,
        (hemem _).mpr x.property⟩
      invFun := fun x => ⟨x.val.val,(hemem _).mp x.property⟩
      left_inv := by intro x; rfl
      right_inv := by intro x; rfl }
    let _ : Finite f.ker := Finite.of_equiv _ e
    exact f.finite_iff_finite_ker_range.mpr ⟨inferInstance,inferInstance⟩

  have hall : ∀ k n, c≤n+k → start≤n → Finite (L n) := by
    intro k
    induction k with
    | zero =>
      intro n hcn _
      have hn : L n=⊥ := by
        apply le_antisymm ?_ bot_le
        calc
          L n ≤ L c := (⊤ : Subgroup G).lowerCentralSeries_antitone (by omega)
          _ = ⊥ := hc
      rw [hn]
      infer_instance
    | succ k ih =>
      intro n hcn hsn
      exact step n hsn (ih (n+1) (by omega) (by omega))
  exact hall c start (by omega) le_rfl

end CriticalPercolation
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Nilpotent_NilpotentFinite
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function
open scoped Classical

namespace CriticalPercolation

theorem nilpotent_finite_of_finite_factors (G : Type*) [Group G]
    [Group.IsNilpotent G] (hfin : ∀ n, Finite (lowerFactor G n)) : Finite G := by
  obtain ⟨c,hc⟩ := Subgroup.nilpotent_iff_lowerCentralSeries.mp
    (inferInstance : Group.IsNilpotent G)
  let L := fun n => (⊤ : Subgroup G).lowerCentralSeries n
  have step (n : ℕ) (hn : Finite (L (n+1))) : Finite (L n) := by
    let F := lowerFactor G n
    let _ : Finite F := hfin n
    let q := QuotientGroup.mk' (L (n+1))
    let f : L n →* F := {
      toFun := fun x => ⟨q x.val,⟨x.val,x.property,rfl⟩⟩
      map_one' := by apply Subtype.ext; exact q.map_one
      map_mul' := by intros; apply Subtype.ext; exact q.map_mul _ _ }
    have hemem (x : L n) : x∈f.ker ↔ x.val∈L (n+1) := by
      change f x=1 ↔ _
      rw [Subtype.ext_iff]
      change q x.val=1 ↔ _
      exact QuotientGroup.eq_one_iff _
    let e : L (n+1) ≃ f.ker := {
      toFun := fun x => ⟨⟨x.val,
        (⊤ : Subgroup G).lowerCentralSeries_antitone (Nat.le_succ n) x.property⟩,
        (hemem _).mpr x.property⟩
      invFun := fun x => ⟨x.val.val,(hemem _).mp x.property⟩
      left_inv := by intro x; rfl
      right_inv := by intro x; rfl }
    let _ : Finite f.ker := Finite.of_equiv _ e
    exact f.finite_iff_finite_ker_range.mpr ⟨inferInstance,inferInstance⟩
  have base : Finite (L c) := by
    change Finite ((⊤ : Subgroup G).lowerCentralSeries c)
    rw [hc]
    infer_instance
  have hall : ∀ k, Finite (L (c-k)) := by
    intro k
    induction k with
    | zero => simpa using base
    | succ k ih =>
      by_cases hk : k < c
      · have he : c-k=(c-(k+1))+1 := by omega
        rw [he] at ih
        exact step _ ih
      · simpa [Nat.sub_eq_zero_of_le (by omega : c≤k),
          Nat.sub_eq_zero_of_le (by omega : c≤k+1)] using ih
  have h : Finite (⊤ : Subgroup G) := by simpa [L] using hall c
  let _ := h
  exact Finite.of_equiv _ (Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G).toEquiv

theorem nilpotent_finite_of_finite_abelianization (G : Type*) [Group G]
    [Group.FG G] [Group.IsNilpotent G] [Finite (Abelianization G)] : Finite G := by
  have he : (⊤ : Subgroup G).lowerCentralSeries 1=commutator G :=
    Subgroup.top_lowerCentralSeries_one
  let _ : Finite (G ⧸ (⊤ : Subgroup G).lowerCentralSeries 1) := by
    rw [he]
    exact (inferInstance : Finite (Abelianization G))
  let _ : Finite (lowerFactor G 0) := inferInstance
  exact nilpotent_finite_of_finite_factors G (lowerFactor_finite G)

end CriticalPercolation
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Nilpotent_NilpotentRankOne
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function
open scoped Classical commutatorElement

namespace CriticalPercolation

theorem first_commutator_factor_finite (G : Type*) [Group G] [Group.FG G]
    (φ : Abelianization G →* Multiplicative ℤ) (hφ : Surjective φ)
    (hk : (φ.ker : Set (Abelianization G)).Finite) : Finite (lowerFactor G 1) := by
  let M := (⊤ : Subgroup G).lowerCentralSeries 2
  let p := QuotientGroup.mk' M
  have hM : M ≤ commutator G := by
    rw [←Subgroup.top_lowerCentralSeries_one]
    exact (⊤ : Subgroup G).lowerCentralSeries_antitone (by omega)
  let ρ : (G ⧸ M) →* Abelianization G := QuotientGroup.lift M (Abelianization.of : G →* Abelianization G) (by
    rw [Abelianization.ker_of]; exact hM)
  have hρ : Surjective ρ := by
    intro a
    obtain ⟨g,rfl⟩ := (QuotientGroup.mk_surjective (s := commutator G)) a
    exact ⟨p g,rfl⟩
  have hcomm : commutator (G ⧸ M)=lowerFactor G 1 := by
    have hp : (⊤ : Subgroup G).map p=⊤ :=
      Subgroup.map_top_of_surjective p QuotientGroup.mk_surjective
    change ⁅⊤,⊤⁆=((⊤ : Subgroup G).lowerCentralSeries 1).map p
    rw [Subgroup.top_lowerCentralSeries_one,commutator,Subgroup.map_commutator,hp]
  have hc : commutator (G ⧸ M)≤Subgroup.center (G ⧸ M) := by
    rw [hcomm]
    exact lowerFactor_central G 1
  have hker : ρ.ker≤Subgroup.center (G ⧸ M) := by
    intro x hx
    obtain ⟨g,rfl⟩ := QuotientGroup.mk_surjective x
    have hg : g∈commutator G := by
      change Abelianization.of g=1 at hx
      exact (QuotientGroup.eq_one_iff g).mp hx
    apply lowerFactor_central G 1
    exact ⟨g,hg,rfl⟩
  obtain ⟨g,hg⟩ := cyclic_mod_torsion_of_finite_kernel ρ hρ φ hφ hk
  have hf := class_two_commutator_finite_of_cyclic_mod_torsion hc ρ hker g hg
  rw [hcomm] at hf
  exact hf.to_subtype

theorem nilpotent_commutator_finite_of_cyclic_abelianization (G : Type*)
    [Group G] [Group.FG G] [Group.IsNilpotent G]
    (φ : Abelianization G →* Multiplicative ℤ) (hφ : Surjective φ)
    (hk : (φ.ker : Set (Abelianization G)).Finite) :
    (commutator G : Set G).Finite := by
  have hfirst := first_commutator_factor_finite G φ hφ hk
  have htail : ∀ n, 1≤n → Finite (lowerFactor G n) := by
    intro n hn
    induction n,hn using Nat.le_induction with
    | base => exact hfirst
    | succ n hn ih =>
      let _ := ih
      exact lowerFactor_finite_step G n
  have hf := nilpotent_lower_finite_of_tail G 1 htail
  rw [Subgroup.top_lowerCentralSeries_one] at hf
  let _ := hf
  exact Set.toFinite _

end CriticalPercolation
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Nilpotent_NilpotentAlternatives
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function
open scoped Classical

namespace CriticalPercolation

theorem nilpotent_alternatives (G : Type*) [Group G] [Group.FG G]
    [Group.IsNilpotent G] :
    Finite G ∨
      (∃ φ : G →* Multiplicative ℤ, Surjective φ ∧ (φ.ker : Set G).Finite) ∨
      (∃ φ : G →* Multiplicative (ℤ×ℤ), Surjective φ) := by
  let q : G →* Abelianization G := Abelianization.of
  have hq : Surjective q := QuotientGroup.mk_surjective
  let _ : Group.FG (Abelianization G) := Group.fg_of_surjective hq
  rcases abelian_alternatives (Abelianization G) with h | ⟨φ,hφ,hk⟩ | ⟨φ,hφ⟩
  · let _ := h
    exact Or.inl (nilpotent_finite_of_finite_abelianization G)
  · refine Or.inr (Or.inl ⟨φ.comp q,hφ.comp hq,?_⟩)
    apply hom_finite_composite_kernel q φ ?_ hk
    have hf := nilpotent_commutator_finite_of_cyclic_abelianization G φ hφ hk
    simpa only [q,Abelianization.ker_of] using hf
  · exact Or.inr (Or.inr ⟨φ.comp q,hφ.comp hq⟩)

end CriticalPercolation
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Nilpotent_NilpotentCyclicConstruction
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function
open scoped Classical

namespace CriticalPercolation

theorem nilpotent_subgroup_finite_cyclic_construction (G : Type*) [Group G] [Group.FG G]
    [Group.IsNilpotent G] (J : Subgroup G) : ∃ k, FiniteCyclicConstruction J k := by
  obtain ⟨c,hc⟩ := Subgroup.nilpotent_iff_lowerCentralSeries.mp
    (inferInstance : Group.IsNilpotent G)
  let L := fun n => J ⊓ (⊤ : Subgroup G).lowerCentralSeries n
  have step (n : ℕ) (hn : ∃ k, FiniteCyclicConstruction (L (n+1)) k) :
      ∃ k, FiniteCyclicConstruction (L n) k := by
    let F := lowerFactor G n
    let _ : CommGroup F := {
      (inferInstance : Group F) with
      mul_comm := fun a b => Subtype.ext
        (Subgroup.mem_center_iff.mp (lowerFactor_central G n b.property) a.val) }
    let _ : Group.FG F := lowerFactor_fg G n
    let q := QuotientGroup.mk' ((⊤ : Subgroup G).lowerCentralSeries (n+1))
    let f : L n →* F := {
      toFun := fun x => ⟨q x.val,⟨x.val,x.property.2,rfl⟩⟩
      map_one' := by apply Subtype.ext; exact q.map_one
      map_mul' := by intros; apply Subtype.ext; exact q.map_mul _ _ }
    let _ : Group.FG f.range := abelian_subgroup_fg f.range
    obtain ⟨k,hk⟩ := hn
    have hemem (x : L n) : x∈f.ker ↔ x.val∈(⊤ : Subgroup G).lowerCentralSeries (n+1) := by
      change f x=1 ↔ _
      rw [Subtype.ext_iff]
      change q x.val=1 ↔ _
      exact QuotientGroup.eq_one_iff _
    let e : L (n+1) ≃* f.ker := {
      toFun := fun x => ⟨⟨x.val,⟨x.property.1,
        (⊤ : Subgroup G).lowerCentralSeries_antitone (Nat.le_succ n) x.property.2⟩⟩,
        (hemem _).mpr x.property.2⟩
      invFun := fun x => ⟨x.val.val,⟨x.val.property.1,(hemem _).mp x.property⟩⟩
      left_inv := by intro x; rfl
      right_inv := by intro x; rfl
      map_mul' := by intros; rfl }
    have hker := hk.of_equiv e.symm
    have he : f.rangeRestrict.ker=f.ker := by
      ext x
      change f.rangeRestrict x=1 ↔ f x=1
      exact Subtype.ext_iff
    have hker' : FiniteCyclicConstruction f.rangeRestrict.ker k := he.symm ▸ hker
    obtain ⟨m,hm⟩ := abelian_finite_cyclic_construction f.range
    exact ⟨k+m,FiniteCyclicConstruction.extension f.rangeRestrict
      f.rangeRestrict_surjective hker' hm⟩
  have base : ∃ k, FiniteCyclicConstruction (L c) k := by
    have he : L c=⊥ := by simp [L,hc]
    rw [he]
    exact ⟨0,.finite _⟩
  have hall : ∀ k, ∃ m, FiniteCyclicConstruction (L (c-k)) m := by
    intro k
    induction k with
    | zero => simpa using base
    | succ k ih =>
      by_cases hk : k < c
      · have he : c-k=(c-(k+1))+1 := by omega
        rw [he] at ih
        exact step _ ih
      · have he : c-k=c-(k+1) := by omega
        exact he ▸ ih
  have h := hall c
  have he : L (c-c)=J := by simp [L]
  exact he ▸ h

theorem nilpotent_finite_cyclic_construction (G : Type*) [Group G] [Group.FG G]
    [Group.IsNilpotent G] : ∃ k, FiniteCyclicConstruction G k := by
  obtain ⟨k,hk⟩ := nilpotent_subgroup_finite_cyclic_construction G ⊤
  exact ⟨k,hk.of_equiv Subgroup.topEquiv.symm⟩

end CriticalPercolation
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Nilpotent_NilpotentSubgroupFG
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function
open scoped Classical

namespace CriticalPercolation

theorem nilpotent_subgroup_fg (G : Type*) [Group G] [Group.FG G]
    [Group.IsNilpotent G] (J : Subgroup G) : Group.FG J := by
  obtain ⟨c,hc⟩ := Subgroup.nilpotent_iff_lowerCentralSeries.mp
    (inferInstance : Group.IsNilpotent G)
  let L := fun n => J ⊓ (⊤ : Subgroup G).lowerCentralSeries n
  have step (n : ℕ) (hn : Group.FG (L (n+1))) : Group.FG (L n) := by
    let F := lowerFactor G n
    let _ : CommGroup F := {
      (inferInstance : Group F) with
      mul_comm := fun a b => Subtype.ext
        (Subgroup.mem_center_iff.mp (lowerFactor_central G n b.property) a.val) }
    let _ : Group.FG F := lowerFactor_fg G n
    let q := QuotientGroup.mk' ((⊤ : Subgroup G).lowerCentralSeries (n+1))
    let f : L n →* F := {
      toFun := fun x => ⟨q x.val,⟨x.val,x.property.2,rfl⟩⟩
      map_one' := by apply Subtype.ext; exact q.map_one
      map_mul' := by intros; apply Subtype.ext; exact q.map_mul _ _ }
    let _ : Group.FG f.range := abelian_subgroup_fg f.range
    let _ : Group.FG (L (n+1)) := hn
    have hemem (x : L n) : x∈f.ker ↔ x.val∈(⊤ : Subgroup G).lowerCentralSeries (n+1) := by
      change f x=1 ↔ _
      rw [Subtype.ext_iff]
      change q x.val=1 ↔ _
      exact QuotientGroup.eq_one_iff _
    let e : L (n+1) ≃* f.ker := {
      toFun := fun x => ⟨⟨x.val,⟨x.property.1,
        (⊤ : Subgroup G).lowerCentralSeries_antitone (Nat.le_succ n) x.property.2⟩⟩,
        (hemem _).mpr x.property.2⟩
      invFun := fun x => ⟨x.val.val,⟨x.val.property.1,(hemem _).mp x.property⟩⟩
      left_inv := by intro x; rfl
      right_inv := by intro x; rfl
      map_mul' := by intros; rfl }
    let _ : Group.FG f.ker := Group.fg_of_surjective (f := e.toMonoidHom) e.surjective
    have he : f.rangeRestrict.ker=f.ker := by
      ext x
      change f.rangeRestrict x=1 ↔ f x=1
      exact Subtype.ext_iff
    let _ : Group.FG f.rangeRestrict.ker := he.symm ▸ (inferInstance : Group.FG f.ker)
    exact fg_of_kernel_quotient f.rangeRestrict f.rangeRestrict_surjective
  have base : Group.FG (L c) := by
    have he : L c=⊥ := by simp [L,hc]
    rw [he]
    infer_instance
  have hall : ∀ k, Group.FG (L (c-k)) := by
    intro k
    induction k with
    | zero => simpa using base
    | succ k ih =>
      by_cases hk : k < c
      · have he : c-k=(c-(k+1))+1 := by omega
        rw [he] at ih
        exact step _ ih
      · simpa [Nat.sub_eq_zero_of_le (by omega : c≤k),
          Nat.sub_eq_zero_of_le (by omega : c≤k+1)] using ih
  have h := hall c
  simpa [L] using h

end CriticalPercolation
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Nilpotent_NilpotentDescent
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function
open scoped Classical

namespace CriticalPercolation

private theorem nilpotent_descent_by_construction (n : ℕ) :
    ∀ (G : Type*) [Group G] [Group.FG G] [Group.IsNilpotent G],
      FiniteCyclicConstruction G n → AlgebraicDescent G := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro G _ _ _ hG
    rcases nilpotent_alternatives G with h | ⟨φ,hφ,hk⟩ | ⟨φ,hφ⟩
    · let _ := h
      exact .finite G
    · exact .cyclic G φ hφ hk
    · apply AlgebraicDescent.plane G φ hφ
      intro J hJ
      obtain ⟨m,hm,hC,hi⟩ := hG.subgroup J
      have hlt : m<n := by
        by_contra! hge
        have he : m=n := by omega
        let _ := hi he
        have hker : φ.ker.FiniteIndex := Subgroup.finiteIndex_of_le hJ
        apply hker.index_ne_zero
        rw [Subgroup.index_ker,φ.range_eq_top_of_surjective hφ]
        rw [Nat.card_congr (Subgroup.topEquiv :
          (⊤ : Subgroup (Multiplicative (ℤ×ℤ))) ≃* Multiplicative (ℤ×ℤ)).toEquiv]
        exact Nat.card_eq_zero_of_infinite
      let _ : Group.FG J := nilpotent_subgroup_fg G J
      exact ih m hlt J hC

theorem nilpotent_descent_bs_oai (G : Type*) [Group G] [Group.FG G] [Group.IsNilpotent G] :
    AlgebraicDescent G := by
  obtain ⟨n,hn⟩ := nilpotent_finite_cyclic_construction G
  exact nilpotent_descent_by_construction n G hn

end CriticalPercolation
end
end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.CriticalPercolation.nilpotent_descent_bs_oai.{u_1} := @OAI.CriticalPercolation.nilpotent_descent_bs_oai.{u_1}
