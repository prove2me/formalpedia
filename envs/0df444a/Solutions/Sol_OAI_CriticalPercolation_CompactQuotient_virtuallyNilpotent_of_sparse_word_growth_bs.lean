-- Prove2me | solution 1 for OAI.CriticalPercolation.CompactQuotient.virtuallyNilpotent_of_sparse_word_growth_bs
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T14:00:59.025108+00:00
-- url     : https://prove2.me/submissions/4c119666-82ae-4761-b826-71e432045896

import Mathlib
import Definitions.Def_OAIQ078B001
import Theorems.Thm_OAI_CriticalPercolation_HarmonicAnalysis_WordGeometry_exists_infinite_finiteDimensional_linear_image_bs
import Theorems.Thm_OAI_CriticalPercolation_LinearGrowth_StrongFullSpan_virtually_comm_range_bs

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
-- module Solutions.OAIQ078_BS.CriticalPercolation_Nilpotent_FiniteKernelNilpotent
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function

namespace CriticalPercolation.CompactQuotient
variable {A B : Type*} [Group A] [Group B]

theorem virtuallyNilpotent_of_finite_kernel (f : A →* B)
    (hfin : (f.ker : Set A).Finite) (hB : Group.IsVirtuallyNilpotent B) :
    Group.IsVirtuallyNilpotent A := by
  let _ : Finite f.ker := hfin.to_subtype
  obtain ⟨N,hN,hNi⟩ := hB
  let _ := hN
  let _ := hNi
  let c : A →* MulAut f.ker := MulAut.conjNormal
  let P := N.comap f ⊓ c.ker
  let _ : c.ker.FiniteIndex := inferInstance
  let _ : (N.comap f).FiniteIndex := by
    constructor
    rw [N.index_comap]
    exact (inferInstance : (N.subgroupOf f.range).FiniteIndex).index_ne_zero
  let _ : P.FiniteIndex := inferInstance
  let j : P →* N :=
    { toFun := fun a => ⟨f a.val,a.property.1⟩
      map_one' := Subtype.ext (map_one f)
      map_mul' := fun a b => Subtype.ext (map_mul f a.val b.val) }
  have hker : j.ker≤Subgroup.center P := by
    intro a ha
    have haf : (a : A)∈f.ker := by
      exact congrArg Subtype.val ha
    rw [Subgroup.mem_center_iff]
    intro b
    apply Subtype.ext
    have hb : c b.val=1 := b.property.2
    have he := congrArg (fun e : MulAut f.ker => (e ⟨a.val,haf⟩).val) hb
    change b.val*a.val*b.val⁻¹=a.val at he
    exact (mul_inv_eq_iff_eq_mul).mp he
  exact ⟨P,Subgroup.isNilpotent_of_ker_le_center j hker,inferInstance⟩

end CriticalPercolation.CompactQuotient
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Growth_PolynomialGrowthDescent
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical Pointwise

namespace CriticalPercolation.SparseGrowth
variable {A B : Type*} [Group A] [Group B] [DecidableEq A] [DecidableEq B]

lemma cyclic_inter_lower_bound (S : Finset A) (h1 : (1 : A) ∈ S)
    (H : Subgroup A) (a : A) (ha : a ∈ H) (ha0 : orderOf a = 0)
    (L : ℕ) (haL : a ∈ S ^ L) (n : ℕ) :
    n + 1 ≤ ((S ^ (L*n)).filter (fun x => x ∈ H)).card := by
  have hinj : Injective (fun i : ℕ => a^i) := fun _ _ h =>
    (pow_inj_iff_of_orderOf_eq_zero ha0).mp h
  calc
    n+1 = ((Finset.range (n+1)).image (fun i => a^i)).card := by
      rw [Finset.card_image_of_injective _ hinj, Finset.card_range]
    _ ≤ ((S ^ (L*n)).filter (fun x => x ∈ H)).card := by
      apply Finset.card_le_card
      intro x hx
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
      have hi' : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      refine Finset.mem_filter.mpr ⟨?_,H.pow_mem ha i⟩
      apply Finset.pow_subset_pow_right h1 (Nat.mul_le_mul_left L hi')
      simpa only [pow_mul] using Finset.pow_mem_pow (n := i) haL

lemma quotient_linear_packing (S : Finset A) (h1 : (1 : A) ∈ S)
    (H : Subgroup A) [H.Normal] (a : A) (ha : a ∈ H) (ha0 : orderOf a = 0)
    (L : ℕ) (haL : a ∈ S ^ L) (n : ℕ) :
    ((S.image (QuotientGroup.mk' H)) ^ n).card * (n+1) ≤
      (S ^ ((L+1)*n)).card := by
  calc
    _ ≤ ((S^n).image (QuotientGroup.mk' H)).card *
        ((S ^ (L*n)).filter (fun x => x ∈ H)).card := by
      rw [Finset.image_pow]
      exact Nat.mul_le_mul_left _ (cyclic_inter_lower_bound S h1 H a ha ha0 L haL n)
    _ ≤ (S ^ (n + L*n)).card := Finset.card_pow_quotient_mul_pow_inter_subgroup_le
    _ = (S ^ ((L+1)*n)).card := by congr 2; ring

theorem quotient_degree_descent (S : Finset A) (h1 : (1 : A) ∈ S)
    (H : Subgroup A) [H.Normal] (a : A) (ha : a ∈ H) (ha0 : orderOf a = 0)
    (L : ℕ) (haL : a ∈ S ^ L) (d : ℕ) (hg : HasDegree S (d+1)) :
    HasDegree (S.image (QuotientGroup.mk' H)) d := by
  obtain ⟨C,hC⟩ := hg
  refine ⟨C * (2*(L+1))^(d+1),?_⟩
  intro R
  obtain ⟨r,hr,hbound⟩ := hC ((L+1)*max R 1)
  let n := r/(L+1)
  have hL : 0 < L+1 := by omega
  have hnr : (L+1)*n ≤ r := by
    simpa only [n, Nat.mul_comm] using Nat.div_mul_le_self r (L+1)
  have hn : max R 1 ≤ n := (Nat.le_div_iff_mul_le hL).mpr (by simpa [Nat.mul_comm] using hr)
  have hn1 : 1 ≤ n := (le_max_right R 1).trans hn
  have hrn : r ≤ (2*(L+1))*n := by
    have hlt := Nat.lt_mul_div_succ r hL
    change r < (L+1)*(n+1) at hlt
    have hh : (L+1)*(n+1) ≤ (2*(L+1))*n := by nlinarith
    exact hlt.le.trans hh
  refine ⟨n,(le_max_left R 1).trans hn,?_⟩
  have hb : ((S.image (QuotientGroup.mk' H))^n).card * n ≤
      (C*(2*(L+1))^(d+1)*n^d)*n := by
    calc
      _ ≤ ((S.image (QuotientGroup.mk' H))^n).card * (n+1) :=
        Nat.mul_le_mul_left _ (Nat.le_succ n)
      _ ≤ (S ^ ((L+1)*n)).card := quotient_linear_packing S h1 H a ha ha0 L haL n
      _ ≤ (S ^ r).card := Finset.card_le_card (Finset.pow_subset_pow_right h1 hnr)
      _ ≤ C*r^(d+1) := hbound
      _ ≤ C*((2*(L+1))*n)^(d+1) := Nat.mul_le_mul_left C (Nat.pow_le_pow_left hrn (d+1))
      _ = (C*(2*(L+1))^(d+1)*n^d)*n := by rw [mul_pow,pow_succ n]; ac_rfl
  exact Nat.le_of_mul_le_mul_right hb (by omega : 0<n)

theorem finite_of_degree_zero (S : Finset A) (h1 : (1 : A) ∈ S)
    (hgen : Subgroup.closure (S : Set A) = ⊤) (hg : HasDegree S 0) : Finite A := by
  rcases finite_or_infinite A with hA | hA
  · exact hA
  let _ := hA
  obtain ⟨C,hC⟩ := hg
  obtain ⟨n,hn,hbound⟩ := hC C
  have hinf : (Subgroup.closure (S : Set A) : Set A).Infinite := by
    simpa only [hgen, Subgroup.coe_top] using (Set.infinite_univ : (Set.univ : Set A).Infinite)
  have hlow := Finset.add_one_le_card_pow h1 hinf n
  simp only [pow_zero,mul_one] at hbound
  omega

omit [DecidableEq A] [DecidableEq B] in

theorem virtuallyNilpotent_of_central_kernel (f : A →* B)
    (hc : f.ker ≤ Subgroup.center A) (hB : Group.IsVirtuallyNilpotent B) :
    Group.IsVirtuallyNilpotent A := by
  obtain ⟨N,hN,hNi⟩ := hB
  let _ := hN
  let _ := hNi
  let P := N.comap f
  let _ : P.FiniteIndex := by
    constructor
    rw [N.index_comap]
    exact (inferInstance : (N.subgroupOf f.range).FiniteIndex).index_ne_zero
  let j : P →* N :=
    { toFun := fun a => ⟨f a.val,a.property⟩
      map_one' := Subtype.ext (map_one f)
      map_mul' := fun a b => Subtype.ext (map_mul f a.val b.val) }
  have hker : j.ker ≤ Subgroup.center P := by
    intro a ha
    have haf : (a : A) ∈ f.ker := congrArg Subtype.val ha
    rw [Subgroup.mem_center_iff]
    intro b
    exact Subtype.ext ((Subgroup.mem_center_iff.mp (hc haf)) b.val)
  exact ⟨P,Subgroup.isNilpotent_of_ker_le_center j hker,inferInstance⟩

omit [DecidableEq A] in

theorem virtuallyNilpotent_of_finiteIndex (H : Subgroup A) [H.FiniteIndex]
    (hH : Group.IsVirtuallyNilpotent H) : Group.IsVirtuallyNilpotent A := by
  obtain ⟨N,hN,hNi⟩ := hH
  let _ := hN
  refine ⟨N.map H.subtype,Group.nilpotent_of_surjective
    (H.subtype.subgroupMap N) (H.subtype.subgroupMap_surjective N),?_⟩
  constructor
  rw [Subgroup.index_map_subtype]
  exact mul_ne_zero hNi.index_ne_zero (inferInstance : H.FiniteIndex).index_ne_zero

lemma finite_subset_word_ball (S : Finset A) (h1 : (1 : A) ∈ S) (hsym : S⁻¹=S)
    (hgen : Subgroup.closure (S : Set A)=⊤) (T : Finset A) :
    ∃ L : ℕ, T ⊆ S^L := by
  have hword : ∀ a : A, ∃ n : ℕ, a ∈ S^n := fun a =>
    exists_mem_pow S hsym (by rw [hgen]; trivial)
  choose l hl using hword
  refine ⟨T.sup l,fun a ha => ?_⟩
  exact Finset.pow_subset_pow_right h1 (Finset.le_sup ha) (hl a)

theorem degree_of_injective (S : Finset A) (h1 : (1 : A) ∈ S) (hsym : S⁻¹=S)
    (hgen : Subgroup.closure (S : Set A)=⊤) (f : B →* A) (hf : Injective f)
    (T : Finset B) (d : ℕ) (hg : HasDegree S d) : HasDegree T d := by
  obtain ⟨L,hL⟩ := finite_subset_word_ball S h1 hsym hgen (T.image f)
  obtain ⟨C,hC⟩ := hg
  refine ⟨C*(2*(L+1))^d,?_⟩
  intro R
  obtain ⟨r,hr,hbound⟩ := hC ((L+1)*max R 1)
  let n := r/(L+1)
  have hLpos : 0 < L+1 := by omega
  have hnr : (L+1)*n ≤ r := by
    simpa only [n,Nat.mul_comm] using Nat.div_mul_le_self r (L+1)
  have hn : max R 1 ≤ n := (Nat.le_div_iff_mul_le hLpos).mpr (by simpa [Nat.mul_comm] using hr)
  have hn1 : 1 ≤ n := (le_max_right R 1).trans hn
  have hrn : r ≤ (2*(L+1))*n := by
    have hlt := Nat.lt_mul_div_succ r hLpos
    change r < (L+1)*(n+1) at hlt
    have hh : (L+1)*(n+1) ≤ (2*(L+1))*n := by nlinarith
    exact hlt.le.trans hh
  refine ⟨n,(le_max_left R 1).trans hn,?_⟩
  calc
    (T^n).card = ((T^n).image f).card := (Finset.card_image_of_injective _ hf).symm
    _ = ((T.image f)^n).card := by rw [Finset.image_pow]
    _ ≤ ((S^L)^n).card := Finset.card_le_card (Finset.pow_subset_pow_left hL)
    _ = (S^(L*n)).card := by rw [pow_mul]
    _ ≤ (S^r).card := Finset.card_le_card (Finset.pow_subset_pow_right h1 (by nlinarith))
    _ ≤ C*r^d := hbound
    _ ≤ C*((2*(L+1))*n)^d := Nat.mul_le_mul_left C (Nat.pow_le_pow_left hrn d)
    _ = C*(2*(L+1))^d*n^d := by rw [mul_pow,mul_assoc]

lemma hasPolynomialDegree_iff (d : ℕ) : HasPolynomialDegree A d ↔
    ∃ S : Finset A, (1 : A)∈S ∧ S⁻¹=S ∧
      Subgroup.closure (S : Set A)=⊤ ∧ HasDegree S d := by
  constructor
  · rintro ⟨S,hSf,h1,hsym,hgen,C,hC⟩
    refine ⟨hSf.toFinset,by simpa using h1,?_,by simpa using hgen,C,?_⟩
    · apply Finset.coe_injective
      simpa only [Finset.coe_inv,Set.Finite.coe_toFinset] using hsym
    · intro R
      obtain ⟨n,hn,hb⟩ := hC R
      refine ⟨n,hn,?_⟩
      have hb' : ((hSf.toFinset : Set A)^n).ncard ≤ C*n^d := by
        simpa only [Set.Finite.coe_toFinset] using hb
      simpa only [← Finset.coe_pow,Set.ncard_coe_finset] using hb'
  · rintro ⟨S,h1,hsym,hgen,C,hC⟩
    refine ⟨S,S.finite_toSet,h1,?_,hgen,C,?_⟩
    · simpa only [Finset.coe_inv] using congrArg (fun T : Finset A => (T : Set A)) hsym
    · intro R
      obtain ⟨n,hn,hb⟩ := hC R
      exact ⟨n,hn,by simpa only [← Finset.coe_pow,Set.ncard_coe_finset] using hb⟩

omit [DecidableEq A] in
lemma HasPolynomialDegree.fg {d : ℕ} (h : HasPolynomialDegree A d) : Group.FG A := by
  obtain ⟨S,hS,_,_,hgen,_⟩ := h
  exact Group.fg_iff.mpr ⟨S,hgen,hS⟩

lemma exists_symmetric_generators [Group.FG A] :
    ∃ S : Finset A, (1 : A)∈S ∧ S⁻¹=S ∧ Subgroup.closure (S : Set A)=⊤ := by
  obtain ⟨F,hF⟩ := Group.FG.out (G := A)
  let S := insert 1 (F ∪ F⁻¹)
  refine ⟨S,by simp [S],?_,?_⟩
  · ext a
    simp only [S,Finset.mem_inv',Finset.mem_insert,Finset.mem_union,inv_eq_one,inv_inv]
    tauto
  · apply top_unique
    rw [← hF]
    apply Subgroup.closure_mono
    intro a ha
    exact Finset.mem_insert_of_mem (Finset.mem_union_left _ ha)

theorem HasPolynomialDegree.of_injective {d : ℕ} (h : HasPolynomialDegree A d)
    (f : B →* A) (hf : Injective f) [Group.FG B] : HasPolynomialDegree B d := by
  obtain ⟨S,h1,hs,hgen,hg⟩ := (hasPolynomialDegree_iff d).mp h
  obtain ⟨T,hT1,hTs,hTgen⟩ := exists_symmetric_generators (A := B)
  exact (hasPolynomialDegree_iff d).mpr ⟨T,hT1,hTs,hTgen,
    degree_of_injective S h1 hs hgen f hf T d hg⟩

theorem HasPolynomialDegree.finiteIndex_subgroup {d : ℕ} (h : HasPolynomialDegree A d)
    (H : Subgroup A) [H.FiniteIndex] : HasPolynomialDegree H d := by
  let _ := h.fg
  exact h.of_injective H.subtype H.subtype_injective

theorem HasPolynomialDegree.finite (h : HasPolynomialDegree A 0) : Finite A := by
  obtain ⟨S,h1,_,hgen,hg⟩ := (hasPolynomialDegree_iff 0).mp h
  exact finite_of_degree_zero S h1 hgen hg

theorem HasPolynomialDegree.quotient_descent {d : ℕ} (h : HasPolynomialDegree A (d+1))
    (H : Subgroup A) [H.Normal] (a : A) (ha : a ∈ H) (ha0 : orderOf a=0) :
    HasPolynomialDegree (A ⧸ H) d := by
  obtain ⟨S,h1,hs,hgen,hg⟩ := (hasPolynomialDegree_iff (d+1)).mp h
  obtain ⟨L,haL⟩ := exists_mem_pow S hs (a := a) (by rw [hgen]; trivial)
  apply (hasPolynomialDegree_iff d).mpr
  refine ⟨S.image (QuotientGroup.mk' H),?_,?_,?_,
    quotient_degree_descent S h1 H a ha ha0 L haL d hg⟩
  · exact Finset.mem_image.mpr ⟨1,h1,map_one _⟩
  · rw [← Finset.image_inv,hs]
  · rw [Finset.coe_image,← MonoidHom.map_closure,hgen]
    exact Subgroup.map_top_of_surjective _ QuotientGroup.mk_surjective

omit [DecidableEq A] in
lemma virtuallyNilpotent_of_finite [Finite A] : Group.IsVirtuallyNilpotent A :=
  ⟨⊥,inferInstance,inferInstance⟩

universe u

end CriticalPercolation.SparseGrowth
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Criticality_NormalClosureGrowth
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function Filter Topology
open scoped Classical Pointwise

namespace CriticalPercolation.SparseGrowth
variable {A : Type*} [Group A] [DecidableEq A]

lemma eventually_exponential_dominates (C k : ℕ) :
    ∃ N : ℕ, ∀ n ≥ N, C*n^k < 2^n := by
  have ht := (tendsto_pow_const_div_const_pow_of_one_lt k
    (by norm_num : (1:ℝ)<2)).const_mul (C:ℝ)
  have he : ∀ᶠ n : ℕ in atTop, (C:ℝ)*((n:ℝ)^k / 2^n) < 1 :=
    ht.eventually (Iio_mem_nhds (by simp : (C:ℝ)*0 < 1))
  obtain ⟨N,hN⟩ := eventually_atTop.mp he
  refine ⟨N,fun n hn => ?_⟩
  have hx := hN n hn
  rw [← mul_div_assoc] at hx
  have hx' := (div_lt_one (pow_pos (by norm_num : (0:ℝ)<2) n)).mp hx
  exact_mod_cast hx'

lemma not_quadratic_exponential_lower (S : Finset A) (h1 : (1:A)∈S)
    (d : ℕ) (hg : HasDegree S d) (L : ℕ) (hL : 0<L)
    (hlo : ∀ n : ℕ, 2^n ≤ (S^(L*n^2)).card) : False := by
  obtain ⟨C,hC⟩ := hg
  obtain ⟨N,hN⟩ := eventually_exponential_dominates (C*(4*L)^d) (2*d)
  obtain ⟨r,hr,hbound⟩ := hC (L*(max N 1)^2)
  let n := Nat.sqrt (r/L)
  have hn : max N 1 ≤ n := Nat.le_sqrt'.mpr ((Nat.le_div_iff_mul_le hL).mpr (by
    simpa only [Nat.mul_comm] using hr))
  have hn1 : 1 ≤ n := (le_max_right N 1).trans hn
  have hnr : L*n^2 ≤ r := by
    calc
      _ ≤ L*(r/L) := Nat.mul_le_mul_left L (Nat.sqrt_le' (r/L))
      _ ≤ r := by simpa only [Nat.mul_comm] using Nat.div_mul_le_self r L
  have hrn : r ≤ (4*L)*n^2 := by
    have ht := Nat.lt_mul_div_succ r hL
    have hs : r/L+1 ≤ (n+1)^2 := Nat.succ_le_of_lt (Nat.lt_succ_sqrt' (r/L))
    have hs' : (n+1)^2 ≤ 4*n^2 := by nlinarith
    have hj := (Nat.mul_le_mul_left L hs).trans (Nat.mul_le_mul_left L hs')
    nlinarith
  have hu : 2^n ≤ (C*(4*L)^d)*n^(2*d) := by
    calc
      _ ≤ (S^(L*n^2)).card := hlo n
      _ ≤ (S^r).card := Finset.card_le_card (Finset.pow_subset_pow_right h1 hnr)
      _ ≤ C*r^d := hbound
      _ ≤ C*((4*L)*n^2)^d := Nat.mul_le_mul_left C (Nat.pow_le_pow_left hrn d)
      _ = (C*(4*L)^d)*n^(2*d) := by rw [mul_pow,pow_mul]; ring
  exact (not_le_of_gt (hN n ((le_max_left N 1).trans hn))) hu

lemma binaryProducts_mem (K : ℕ → Subgroup A) (hK : Monotone K)
    (g : ℕ → A) (hg : ∀ n, g n∈K (n+1)) :
    ∀ n, ∀ x ∈ binaryProducts g n, x∈K n := by
  intro n
  induction n with
  | zero =>
    intro x hx
    have he : x=1 := by simpa [binaryProducts] using hx
    exact he ▸ (K 0).one_mem
  | succ n ih =>
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact hK (Nat.le_succ n) (ih x hx)
    · obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
      exact (K (n+1)).mul_mem (hg n) (hK (Nat.le_succ n) (ih y hy))

lemma binaryProducts_card (K : ℕ → Subgroup A) (hK : Monotone K)
    (g : ℕ → A) (hg : ∀ n, g n∈K (n+1)) (hout : ∀ n, g n∉K n) :
    ∀ n, (binaryProducts g n).card=2^n := by
  intro n
  induction n with
  | zero => simp [binaryProducts]
  | succ n ih =>
    have hd : Disjoint (binaryProducts g n)
        ((binaryProducts g n).image (fun x => g n*x)) := by
      apply Finset.disjoint_left.mpr
      intro x hx hy
      obtain ⟨y,hy,he⟩ := Finset.mem_image.mp hy
      have hxK := binaryProducts_mem K hK g hg n x hx
      have hyK := binaryProducts_mem K hK g hg n y hy
      apply hout n
      rw [←he] at hxK
      simpa only [mul_assoc,mul_inv_cancel,mul_one] using
        (K n).mul_mem hxK ((K n).inv_mem hyK)
    rw [binaryProducts,Finset.card_union_of_disjoint hd,
      Finset.card_image_of_injective _ (mul_right_injective (g n)),ih,pow_succ]
    omega

lemma binaryProducts_subset_pow (S : Finset A) (h1 : (1:A)∈S)
    (g : ℕ → A) (L : ℕ) (hg : ∀ n, g n∈S^(L*(n+1))) :
    ∀ n, binaryProducts g n ⊆ S^(L*n^2) := by
  intro n
  induction n with
  | zero => simp [binaryProducts]
  | succ n ih =>
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact Finset.pow_subset_pow_right h1 (Nat.mul_le_mul_left L (Nat.pow_le_pow_left (Nat.le_succ n) 2)) (ih hx)
    · obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
      have hlen : L*(n+1)+L*n^2 ≤ L*(n+1)^2 := by
        calc
          _ = L*(n+1+n^2) := by ring
          _ ≤ L*(n+1)^2 := Nat.mul_le_mul_left L (by nlinarith)
      apply Finset.pow_subset_pow_right h1 hlen
      rw [pow_add]
      exact Finset.mul_mem_mul (hg n) (ih hy)

theorem no_linear_word_strict_chain (S : Finset A) (h1 : (1:A)∈S)
    (d : ℕ) (hg : HasDegree S d) (K : ℕ → Subgroup A) (hK : Monotone K)
    (g : ℕ → A) (hgin : ∀ n, g n∈K (n+1)) (hgout : ∀ n, g n∉K n)
    (L : ℕ) (hL : 0<L) (hword : ∀ n, g n∈S^(L*(n+1))) : False := by
  apply not_quadratic_exponential_lower S h1 d hg L hL
  intro n
  rw [←binaryProducts_card K hK g hgin hgout n]
  exact Finset.card_le_card (binaryProducts_subset_pow S h1 g L hword n)

lemma mem_boundedConjugates (S F : Finset A) (n : ℕ) {x : A} :
    x∈boundedConjugates S F n ↔ ∃ g∈S^n, ∃ f∈F, g*f*g⁻¹=x := by
  simp [boundedConjugates, MulAut.conj_apply]

lemma boundedConjugates_mono (S F : Finset A) (h1 : (1:A)∈S) :
    Monotone (boundedConjugates S F) := by
  intro m n h x hx
  obtain ⟨g,hg,f,hf,rfl⟩ := (mem_boundedConjugates S F m).mp hx
  exact (mem_boundedConjugates S F n).mpr
    ⟨g,Finset.pow_subset_pow_right h1 h hg,f,hf,rfl⟩

lemma conjugateStage_mono (S F : Finset A) (h1 : (1:A)∈S) :
    Monotone (conjugateStage S F) := by
  intro m n h
  exact Subgroup.closure_mono (boundedConjugates_mono S F h1 h)

lemma boundedConjugates_subset_pow (S F : Finset A) (hsym : S⁻¹=S)
    (L : ℕ) (hF : F⊆S^L) (n : ℕ) :
    boundedConjugates S F n ⊆ S^(2*n+L) := by
  intro x hx
  obtain ⟨g,hg,f,hf,rfl⟩ := (mem_boundedConjugates S F n).mp hx
  have hgi : g⁻¹∈S^n := by
    rw [←hsym,inv_pow]
    exact Finset.inv_mem_inv hg
  have he : 2*n+L=n+L+n := by omega
  rw [he,pow_add,pow_add]
  exact Finset.mul_mem_mul (Finset.mul_mem_mul hg (hF hf)) hgi

lemma conjugateStage_le_normalClosure (S F : Finset A) (n : ℕ) :
    conjugateStage S F n ≤ Subgroup.normalClosure (F : Set A) := by
  apply (Subgroup.closure_le _).mpr
  intro x hx
  obtain ⟨g,hg,f,hf,rfl⟩ := (mem_boundedConjugates S F n).mp hx
  exact Subgroup.normalClosure_normal.conj_mem f (Subgroup.subset_normalClosure hf) g

lemma conjugateStage_conj_generator (S F : Finset A) (n : ℕ)
    (s : A) (hs : s∈S) {x : A} (hx : x∈conjugateStage S F n) :
    s*x*s⁻¹∈conjugateStage S F (n+1) := by
  change x∈Subgroup.closure _ at hx
  have hmap : conjugateStage S F n ≤
      (conjugateStage S F (n+1)).comap (MulAut.conj s) := by
    apply (Subgroup.closure_le _).mpr
    intro y hy
    obtain ⟨g,hg,f,hf,rfl⟩ := (mem_boundedConjugates S F n).mp hy
    apply Subgroup.subset_closure
    apply (mem_boundedConjugates S F (n+1)).mpr
    refine ⟨s*g,?_,f,hf,?_⟩
    · rw [pow_succ']
      exact Finset.mul_mem_mul hs hg
    · simp [MulAut.conj_apply,mul_assoc]
  exact hmap hx

lemma conjugateStage_normal_of_stationary (S F : Finset A) (hsym : S⁻¹=S)
    (hgen : Subgroup.closure (S : Set A)=⊤) (n : ℕ)
    (he : conjugateStage S F (n+1)=conjugateStage S F n) :
    (conjugateStage S F n).Normal := by
  rw [←Subgroup.normalizer_eq_top_iff]
  apply top_unique
  rw [←hgen]
  apply (Subgroup.closure_le _).mpr
  intro s hs
  change ∀ x, x∈conjugateStage S F n ↔ s*x*s⁻¹∈conjugateStage S F n
  intro x
  constructor
  · intro hx
    rw [←he]
    exact conjugateStage_conj_generator S F n s hs hx
  · intro hx
    have hsi : s⁻¹∈S := by rw [←hsym]; exact Finset.inv_mem_inv hs
    have hy := conjugateStage_conj_generator S F n s⁻¹ hsi hx
    rw [he] at hy
    simpa only [inv_inv, mul_assoc, inv_mul_cancel_left, mul_inv_cancel_right, inv_mul_cancel, mul_one] using hy

lemma normalClosure_eq_conjugateStage_of_stationary (S F : Finset A)
    (h1 : (1:A)∈S) (hsym : S⁻¹=S) (hgen : Subgroup.closure (S : Set A)=⊤)
    (n : ℕ) (he : conjugateStage S F (n+1)=conjugateStage S F n) :
    Subgroup.normalClosure (F : Set A)=conjugateStage S F n := by
  let _ := conjugateStage_normal_of_stationary S F hsym hgen n he
  apply le_antisymm
  · apply Subgroup.normalClosure_le_normal
    intro f hf
    apply Subgroup.subset_closure
    exact (mem_boundedConjugates S F n).mpr
      ⟨1,Finset.one_mem_pow h1,f,hf,by simp⟩
  · exact conjugateStage_le_normalClosure S F n

theorem exists_conjugateStage_stationary (S F : Finset A)
    (h1 : (1:A)∈S) (hsym : S⁻¹=S) (d : ℕ) (hg : HasDegree S d)
    (L : ℕ) (hF : F⊆S^L) :
    ∃ n : ℕ, conjugateStage S F (n+1)=conjugateStage S F n := by
  by_contra! hn
  have hw : ∀ n : ℕ, ∃ x∈boundedConjugates S F (n+1), x∉conjugateStage S F n := by
    intro n
    by_contra! h
    apply hn n
    apply le_antisymm ((Subgroup.closure_le _).mpr h)
    exact conjugateStage_mono S F h1 (Nat.le_succ n)
  choose g hgin hgout using hw
  apply no_linear_word_strict_chain S h1 d hg (conjugateStage S F)
    (conjugateStage_mono S F h1) g (fun n => Subgroup.subset_closure (hgin n))
    hgout (L+2) (by omega)
  intro n
  apply Finset.pow_subset_pow_right h1 (show 2*(n+1)+L≤(L+2)*(n+1) by nlinarith)
  exact boundedConjugates_subset_pow S F hsym L hF (n+1) (hgin n)

theorem normalClosure_fg_of_sparse_growth (S F : Finset A)
    (h1 : (1:A)∈S) (hsym : S⁻¹=S) (hgen : Subgroup.closure (S : Set A)=⊤)
    (d : ℕ) (hg : HasDegree S d) : (Subgroup.normalClosure (F : Set A)).FG := by
  obtain ⟨L,hF⟩ := finite_subset_word_ball S h1 hsym hgen F
  obtain ⟨n,hn⟩ := exists_conjugateStage_stationary S F h1 hsym d hg L hF
  rw [normalClosure_eq_conjugateStage_of_stationary S F h1 hsym hgen n hn]
  exact (Subgroup.fg_iff _).mpr ⟨(boundedConjugates S F n : Set A),rfl,Finset.finite_toSet _⟩

end CriticalPercolation.SparseGrowth
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_IntegerKernelGeneration
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical Pointwise

namespace CriticalPercolation.SparseGrowth
variable {A : Type*} [Group A] [DecidableEq A]

lemma integer_kernel_normalClosure (S : Finset A)
    (hgen : Subgroup.closure (S : Set A)=⊤)
    (f : A →* Multiplicative ℤ) (a : A) (ha : f a=Multiplicative.ofAdd 1) :
    f.ker=Subgroup.normalClosure
      ((S.image (fun s => s*a^(-Multiplicative.toAdd (f s)))) : Set A) := by
  let F := S.image (fun s => s*a^(-Multiplicative.toAdd (f s)))
  let N := Subgroup.normalClosure (F : Set A)
  have hN : N≤f.ker := by
    apply Subgroup.normalClosure_le_normal
    intro y hy
    obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp hy
    change f (s*a^(-Multiplicative.toAdd (f s)))=1
    rw [map_mul,map_zpow,ha]
    apply Multiplicative.toAdd.injective
    simp
  let q := QuotientGroup.mk' N
  have hqa : ∀ x : A, q x=(q a)^Multiplicative.toAdd (f x) := by
    intro x
    have hx : x∈Subgroup.closure (S : Set A) := hgen.symm ▸ Subgroup.mem_top x
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      have hm : x*a^(-Multiplicative.toAdd (f x))∈N :=
        Subgroup.subset_normalClosure (Finset.mem_image.mpr ⟨x,hx,rfl⟩)
      have he := (QuotientGroup.eq_one_iff _).mpr hm
      change q (x*a^(-Multiplicative.toAdd (f x)))=1 at he
      rw [map_mul,map_zpow,zpow_neg] at he
      exact mul_inv_eq_one.mp he
    | one => simp
    | mul x y _ _ hx hy =>
      rw [map_mul,hx,hy,←zpow_add,map_mul,toAdd_mul]
    | inv x _ hx =>
      rw [map_inv,hx,map_inv,toAdd_inv,zpow_neg]
  apply le_antisymm _ hN
  intro x hx
  apply (QuotientGroup.eq_one_iff _).mp
  change q x=1
  rw [hqa,MonoidHom.mem_ker.mp hx]
  simp

theorem HasPolynomialDegree.integer_kernel_fg {d : ℕ}
    (hg : HasPolynomialDegree A d) (f : A →* Multiplicative ℤ) (hf : Surjective f) :
    Group.FG f.ker := by
  obtain ⟨S,h1,hs,hgen,hS⟩ := (hasPolynomialDegree_iff d).mp hg
  obtain ⟨a,ha⟩ := hf (Multiplicative.ofAdd 1)
  rw [integer_kernel_normalClosure S hgen f a ha]
  exact (Group.fg_iff_subgroup_fg _).mpr
    (normalClosure_fg_of_sparse_growth S _ h1 hs hgen d hS)

end CriticalPercolation.SparseGrowth
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Growth_KernelGrowthDescent
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical Pointwise

namespace CriticalPercolation.SparseGrowth
variable {A : Type*} [Group A] [DecidableEq A]

lemma quotient_word_lower (S : Finset A) (h1 : (1:A)∈S)
    (hgen : Subgroup.closure (S : Set A)=⊤)
    (H : Subgroup A) [H.Normal] [Infinite (A ⧸ H)] (n : ℕ) :
    n+1 ≤ ((S^n).image (QuotientGroup.mk' H)).card := by
  let q := QuotientGroup.mk' H
  have hq1 : (1:A ⧸ H)∈S.image q := Finset.mem_image.mpr ⟨1,h1,map_one q⟩
  have hqgen : Subgroup.closure (S.image q : Set (A ⧸ H))=⊤ := by
    rw [Finset.coe_image,←MonoidHom.map_closure,hgen]
    exact Subgroup.map_top_of_surjective q (QuotientGroup.mk'_surjective H)
  have hinf : (Subgroup.closure (S.image q : Set (A ⧸ H)) : Set (A ⧸ H)).Infinite := by
    rw [hqgen,Subgroup.coe_top]
    exact Set.infinite_univ
  rw [Finset.image_pow]
  exact Finset.add_one_le_card_pow hq1 hinf n

lemma subgroup_linear_packing (S : Finset A) (h1 : (1:A)∈S)
    (hgen : Subgroup.closure (S : Set A)=⊤)
    (H : Subgroup A) [H.Normal] [Infinite (A ⧸ H)]
    (T : Finset H) (L : ℕ) (hT : T.image H.subtype ⊆ S^L) (n : ℕ) :
    (T^n).card*(n+1) ≤ (S^((L+1)*n)).card := by
  have hTin : (T^n).image H.subtype ⊆ (S^(L*n)).filter (fun a => a∈H) := by
    intro a ha
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp ha
    refine Finset.mem_filter.mpr ⟨?_,b.property⟩
    have he : (b : A)∈(T.image H.subtype)^n := by
      rw [←Finset.image_pow]
      exact Finset.mem_image.mpr ⟨b,hb,rfl⟩
    rw [pow_mul]
    exact Finset.pow_subset_pow_left hT he
  calc
    _ = (n+1)*((T^n).image H.subtype).card := by
      rw [Finset.card_image_of_injective _ H.subtype_injective,Nat.mul_comm]
    _ ≤ ((S^n).image (QuotientGroup.mk' H)).card *
        ((S^(L*n)).filter (fun a => a∈H)).card :=
      Nat.mul_le_mul (quotient_word_lower S h1 hgen H n) (Finset.card_le_card hTin)
    _ ≤ (S^(n+L*n)).card := Finset.card_pow_quotient_mul_pow_inter_subgroup_le
    _ = (S^((L+1)*n)).card := by congr 2; ring

theorem subgroup_degree_descent (S : Finset A) (h1 : (1:A)∈S)
    (hgen : Subgroup.closure (S : Set A)=⊤)
    (H : Subgroup A) [H.Normal] [Infinite (A ⧸ H)]
    (T : Finset H) (L : ℕ) (hT : T.image H.subtype ⊆ S^L)
    (d : ℕ) (hg : HasDegree S (d+1)) : HasDegree T d := by
  obtain ⟨C,hC⟩ := hg
  refine ⟨C*(2*(L+1))^(d+1),?_⟩
  intro R
  obtain ⟨r,hr,hbound⟩ := hC ((L+1)*max R 1)
  let n := r/(L+1)
  have hL : 0<L+1 := by omega
  have hnr : (L+1)*n ≤ r := by
    simpa only [n,Nat.mul_comm] using Nat.div_mul_le_self r (L+1)
  have hn : max R 1≤n := (Nat.le_div_iff_mul_le hL).mpr (by simpa [Nat.mul_comm] using hr)
  have hn1 : 1≤n := (le_max_right R 1).trans hn
  have hrn : r≤(2*(L+1))*n := by
    have hlt := Nat.lt_mul_div_succ r hL
    change r<(L+1)*(n+1) at hlt
    have hh : (L+1)*(n+1)≤(2*(L+1))*n := by nlinarith
    exact hlt.le.trans hh
  refine ⟨n,(le_max_left R 1).trans hn,?_⟩
  have hb : (T^n).card*n ≤ (C*(2*(L+1))^(d+1)*n^d)*n := by
    calc
      _ ≤ (T^n).card*(n+1) := Nat.mul_le_mul_left _ (Nat.le_succ n)
      _ ≤ (S^((L+1)*n)).card := subgroup_linear_packing S h1 hgen H T L hT n
      _ ≤ (S^r).card := Finset.card_le_card (Finset.pow_subset_pow_right h1 hnr)
      _ ≤ C*r^(d+1) := hbound
      _ ≤ C*((2*(L+1))*n)^(d+1) := Nat.mul_le_mul_left C (Nat.pow_le_pow_left hrn (d+1))
      _ = (C*(2*(L+1))^(d+1)*n^d)*n := by rw [mul_pow,pow_succ n]; ac_rfl
  exact Nat.le_of_mul_le_mul_right hb (by omega : 0<n)

theorem HasPolynomialDegree.normal_subgroup_descent {d : ℕ}
    (h : HasPolynomialDegree A (d+1)) (H : Subgroup A) [H.Normal]
    [Infinite (A ⧸ H)] [Group.FG H] : HasPolynomialDegree H d := by
  obtain ⟨S,h1,hs,hgen,hg⟩ := (hasPolynomialDegree_iff (d+1)).mp h
  obtain ⟨T,hT1,hTs,hTgen⟩ := exists_symmetric_generators (A := H)
  obtain ⟨L,hL⟩ := finite_subset_word_ball S h1 hs hgen (T.image H.subtype)
  exact (hasPolynomialDegree_iff d).mpr ⟨T,hT1,hTs,hTgen,
    subgroup_degree_descent S h1 hgen H T L hL d hg⟩

end CriticalPercolation.SparseGrowth
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Criticality_ExpandingCharacterGrowth
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical Pointwise

namespace CriticalPercolation.SparseGrowth
variable {A B : Type*} [Group A] [Group B] [DecidableEq A] [DecidableEq B]

lemma binaryProducts_map (f : B →* A) (g : ℕ → B) (n : ℕ) :
    (binaryProducts g n).image f = binaryProducts (fun i => f (g i)) n := by
  induction n with
  | zero => simp [binaryProducts]
  | succ n ih =>
    simp only [binaryProducts, Finset.image_union]
    rw [←ih]
    congr 1
    simp only [Finset.image_image]
    apply Finset.image_congr
    intro x _
    exact map_mul f (g n) x

lemma binaryProducts_card_norm_bound
    (φ : A →* Multiplicative ℂ) (g : ℕ → A) (b q : ℝ)
    (hb : 0 < b) (hq : 3 ≤ q)
    (he : ∀ n, ‖Multiplicative.toAdd (φ (g n))‖ = b*q^n) :
    ∀ n, (binaryProducts g n).card=2^n ∧
      ∀ a∈binaryProducts g n,
        2*‖Multiplicative.toAdd (φ a)‖ ≤ b*(q^n-1) := by
  intro n
  induction n with
  | zero =>
    constructor
    · simp [binaryProducts]
    · intro a ha
      have ha1 : a=1 := by simpa [binaryProducts] using ha
      simp [ha1]
  | succ n ih =>
    have hdis : Disjoint (binaryProducts g n)
        ((binaryProducts g n).image (fun x => g n*x)) := by
      apply Finset.disjoint_left.mpr
      intro a ha ha'
      obtain ⟨c,hc,hca⟩ := Finset.mem_image.mp ha'
      have heq : Multiplicative.toAdd (φ (g n)) =
          Multiplicative.toAdd (φ a)-Multiplicative.toAdd (φ c) := by
        rw [←hca,map_mul]
        change Multiplicative.toAdd (φ (g n)) =
          (Multiplicative.toAdd (φ (g n))+Multiplicative.toAdd (φ c))-
            Multiplicative.toAdd (φ c)
        abel
      have hn := norm_sub_le (Multiplicative.toAdd (φ a)) (Multiplicative.toAdd (φ c))
      rw [←heq,he n] at hn
      have haB := ih.2 a ha
      have hcB := ih.2 c hc
      nlinarith
    constructor
    · simp only [binaryProducts,Finset.card_union_of_disjoint hdis,
        Finset.card_image_of_injective _ (mul_right_injective (g n)),ih.1,pow_succ]
      omega
    · intro a ha
      obtain ha|ha := Finset.mem_union.mp ha
      · have haB := ih.2 a ha
        have hpow : q^n ≤ q^(n+1) := by
          rw [pow_succ]
          nlinarith [pow_nonneg (by linarith : 0≤q) n]
        exact haB.trans (mul_le_mul_of_nonneg_left (sub_le_sub_right hpow 1) hb.le)
      · obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp ha
        have hn := norm_add_le (Multiplicative.toAdd (φ (g n))) (Multiplicative.toAdd (φ c))
        have hcB := ih.2 c hc
        rw [he n] at hn
        rw [map_mul]
        change 2*‖Multiplicative.toAdd (φ (g n))+Multiplicative.toAdd (φ c)‖≤_
        rw [pow_succ]
        have hqn : 0≤q^n := pow_nonneg (by linarith) n
        have hprod : 3*(b*q^n) ≤ (b*q^n)*q := by
          calc
            3*(b*q^n) = (b*q^n)*3 := mul_comm _ _
            _ ≤ (b*q^n)*q := mul_le_mul_of_nonneg_left hq (mul_nonneg hb.le hqn)
        nlinarith

theorem no_expanding_short_character (S : Finset A) (h1 : (1:A)∈S)
    (d : ℕ) (hg : HasDegree S d) (f : B →* A) (hf : Injective f)
    (φ : B →* Multiplicative ℂ) (g : ℕ → B) (b q : ℝ)
    (hb : 0<b) (hq : 3≤q)
    (he : ∀ n, ‖Multiplicative.toAdd (φ (g n))‖=b*q^n)
    (L : ℕ) (hL : 0<L) (hw : ∀ n, f (g n)∈S^(L*(n+1))) : False := by
  apply not_quadratic_exponential_lower S h1 d hg L hL
  intro n
  have hc := (binaryProducts_card_norm_bound φ g b q hb hq he n).1
  calc
    2^n = ((binaryProducts g n).image f).card := by
      rw [Finset.card_image_of_injective _ hf,hc]
    _ = (binaryProducts (fun i => f (g i)) n).card := by rw [binaryProducts_map]
    _ ≤ (S^(L*n^2)).card :=
      Finset.card_le_card (binaryProducts_subset_pow S h1 (fun i => f (g i)) L hw n)

theorem HasPolynomialDegree.norm_conj_eigencharacter_le_one {d : ℕ}
    (hg : HasPolynomialDegree A d) (H : Subgroup A) [H.Normal]
    (a : A) (φ : H →* Multiplicative ℂ) (ζ : ℂ)
    (heigen : ∀ x : H, Multiplicative.toAdd (φ ((MulAut.conjNormal a) x)) =
      ζ * Multiplicative.toAdd (φ x))
    (b : H) (hb : Multiplicative.toAdd (φ b) ≠ 0) : ‖ζ‖≤1 := by
  by_contra! hl
  obtain ⟨k,hk⟩ := pow_unbounded_of_one_lt (3:ℝ) hl
  obtain ⟨S,h1,hs,hgen,hgrowth⟩ := (hasPolynomialDegree_iff d).mp hg
  obtain ⟨L,hL⟩ := finite_subset_word_ball S h1 hs hgen {a,a⁻¹,(b:A)}
  have haL : a∈S^L := hL (by simp)
  have haiL : a⁻¹∈S^L := hL (by simp)
  have hbL : (b:A)∈S^L := hL (by simp)
  have hepow : ∀ m : ℕ, ∀ x : H,
      Multiplicative.toAdd (φ ((MulAut.conjNormal (a^m)) x)) =
        ζ^m * Multiplicative.toAdd (φ x) := by
    intro m
    induction m with
    | zero => intro x; simp
    | succ m ih =>
      intro x
      rw [pow_succ',map_mul,MulAut.mul_apply,heigen,ih,pow_succ']
      ring
  let g : ℕ → H := fun n => (MulAut.conjNormal (a^(k*n))) b
  apply no_expanding_short_character S h1 d hgrowth H.subtype H.subtype_injective
    φ g ‖Multiplicative.toAdd (φ b)‖ (‖ζ‖^k) (norm_pos_iff.mpr hb) hk.le
    (fun n => ?_) (2*L*k+L+1) (by omega) (fun n => ?_)
  · dsimp only [g]
    rw [hepow,norm_mul,norm_pow,pow_mul,mul_comm]
  · change ((MulAut.conjNormal (a^(k*n))) b : A)∈_
    rw [MulAut.conjNormal_apply]
    have haP : a^(k*n)∈S^(L*(k*n)) := by
      rw [pow_mul]
      exact Finset.pow_mem_pow haL
    have haiP : (a^(k*n))⁻¹∈S^(L*(k*n)) := by
      rw [←inv_pow,pow_mul]
      exact Finset.pow_mem_pow haiL
    apply Finset.pow_subset_pow_right h1
      (show L*(k*n)+L+L*(k*n)≤(2*L*k+L+1)*(n+1) by nlinarith)
    rw [pow_add,pow_add]
    exact Finset.mul_mem_mul (Finset.mul_mem_mul haP hbL) haiP

end CriticalPercolation.SparseGrowth
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_LinearGroups_ConjugationMatrixGrowth
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical Matrix

namespace CriticalPercolation.SparseGrowth
variable {A : Type*} [Group A] [DecidableEq A]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma latticeCharacter_mulVec (w : ι → ℂ) (M : Matrix ι ι ℤ) (v : ι → ℤ) :
    Multiplicative.toAdd (latticeCharacter w (Multiplicative.ofAdd (M.mulVec v))) =
      (Matrix.vecMul w (M.map (Int.castRingHom ℂ))) ⬝ᵥ (fun i => (v i : ℂ)) := by
  change (w ⬝ᵥ fun i => ((M.mulVec v i : ℤ) : ℂ)) = _
  have he : (fun i => ((M.mulVec v i : ℤ) : ℂ)) =
      (M.map (Int.castRingHom ℂ)).mulVec (fun i => (v i : ℂ)) := by
    funext i
    exact (Int.castRingHom ℂ).map_mulVec M v i
  rw [he,Matrix.dotProduct_mulVec]

lemma latticeCharacter_single (w : ι → ℂ) (i : ι) :
    Multiplicative.toAdd (latticeCharacter w (Multiplicative.ofAdd (Pi.single i 1)))=w i := by
  change (w ⬝ᵥ fun j => (((Pi.single i (1:ℤ) : ι → ℤ) j : ℤ) : ℂ))=w i
  have he : (fun j => (((Pi.single i (1:ℤ) : ι → ℤ) j : ℤ) : ℂ)) = Pi.single i (1:ℂ) := by
    funext j
    by_cases h : i=j
    · subst j; simp
    · simp [Ne.symm h]
  rw [he,dotProduct_single,mul_one]

theorem HasPolynomialDegree.conjugationMatrix_roots_norm_le_one {d : ℕ}
    (hg : HasPolynomialDegree A d) (H : Subgroup A) [H.Normal] (a : A)
    (p : H →* Multiplicative (ι → ℤ)) (hp : Surjective p)
    (M : Matrix ι ι ℤ)
    (hM : ∀ x : H, Multiplicative.toAdd (p ((MulAut.conjNormal a) x)) =
      M.mulVec (Multiplicative.toAdd (p x))) :
    ∀ z∈(M.map (Int.castRingHom ℂ)).charpoly.roots, ‖z‖≤1 := by
  intro z hz
  let C := M.map (Int.castRingHom ℂ)
  have hroot : (C.transpose.mulVecLin.charpoly).IsRoot z := by
    rw [Matrix.charpoly_mulVecLin,Matrix.charpoly_transpose]
    exact (Polynomial.mem_roots (Matrix.charpoly_monic C).ne_zero).mp hz
  have heig := (Module.End.hasEigenvalue_iff_isRoot_charpoly C.transpose.mulVecLin z).mpr hroot
  obtain ⟨w,hw⟩ := heig.exists_hasUnifEigenvector
  have hweq : Matrix.vecMul w C = z • w := by
    simpa only [Matrix.mulVecLin_apply,Matrix.mulVec_transpose] using hw.apply_eq_smul
  have hwn := hw.2
  have hex : ∃ i, w i ≠ 0 := by
    by_contra! h
    exact hwn (funext h)
  obtain ⟨i,hi⟩ := hex
  obtain ⟨b,hb⟩ := hp (Multiplicative.ofAdd (Pi.single i 1))
  let φ := (latticeCharacter w).comp p
  have hφ : ∀ x : H, Multiplicative.toAdd (φ ((MulAut.conjNormal a) x)) =
      z * Multiplicative.toAdd (φ x) := by
    intro x
    change Multiplicative.toAdd (latticeCharacter w (p ((MulAut.conjNormal a) x))) =
      z * Multiplicative.toAdd (latticeCharacter w (p x))
    have hpx : p ((MulAut.conjNormal a) x) =
      Multiplicative.ofAdd (M.mulVec (Multiplicative.toAdd (p x))) := by
      exact congrArg Multiplicative.ofAdd (hM x)
    rw [hpx,latticeCharacter_mulVec]
    change (Matrix.vecMul w C) ⬝ᵥ (fun i => ((Multiplicative.toAdd (p x) i : ℤ) : ℂ)) = _
    rw [hweq,smul_dotProduct]
    rfl
  have hφb : Multiplicative.toAdd (φ b) ≠ 0 := by
    change Multiplicative.toAdd (latticeCharacter w (p b)) ≠ 0
    rw [hb,latticeCharacter_single]
    exact hi
  exact hg.norm_conj_eigencharacter_le_one H a φ z hφ b hφb

end CriticalPercolation.SparseGrowth
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_LinearGroups_MatrixPeriodicDirection
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical Matrix

namespace CriticalPercolation.SparseGrowth
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma intMatrix_mahlerMeasure_eq_one (M : Matrix ι ι ℤ)
    (hroots : ∀ z∈(M.map (Int.castRingHom ℂ)).charpoly.roots, ‖z‖≤1) :
    (M.charpoly.map (Int.castRingHom ℂ)).mahlerMeasure=1 := by
  rw [←Matrix.charpoly_map,Polynomial.mahlerMeasure_eq_leadingCoeff_mul_prod_roots,
    (Matrix.charpoly_monic _).leadingCoeff,norm_one,one_mul]
  apply Multiset.prod_eq_one
  intro x hx
  obtain ⟨z,hz,rfl⟩ := Multiset.mem_map.mp hx
  exact max_eq_left (hroots z hz)

lemma intMatrix_root_is_rootOfUnity (M : Matrix ι ι ℤ)
    (hroots : ∀ z∈(M.map (Int.castRingHom ℂ)).charpoly.roots, ‖z‖≤1)
    (z : ℂ) (hz : z∈(M.map (Int.castRingHom ℂ)).charpoly.roots) (hz0 : z≠0) :
    ∃ m : ℕ, 0 < m ∧ z ^ m = 1 := by
  apply Polynomial.pow_eq_one_of_mahlerMeasure_eq_one
    (intMatrix_mahlerMeasure_eq_one M hroots) hz0
  have he : Int.castRingHom ℂ = algebraMap ℤ ℂ := by ext; simp
  simpa only [Polynomial.aroots_def,Matrix.charpoly_map,he] using hz

theorem intMatrix_exists_periodic_vector [Nonempty ι] (M : Matrix ι ι ℤ)
    (hunit : IsUnit M)
    (hroots : ∀ z∈(M.map (Int.castRingHom ℂ)).charpoly.roots, ‖z‖≤1) :
    ∃ m : ℕ, 0 < m ∧ ∃ v : ι → ℤ, v≠0 ∧ (M^m).mulVec v=v := by
  let C := M.map (Int.castRingHom ℂ)
  have hcunit : IsUnit C := hunit.map (Int.castRingHom ℂ).mapMatrix
  have hdeg : C.charpoly.degree ≠ 0 := by
    apply ne_of_gt
    apply Polynomial.natDegree_pos_iff_degree_pos.mp
    rw [Matrix.charpoly_natDegree_eq_dim]
    exact Fintype.card_pos
  obtain ⟨z,hz⟩ := IsAlgClosed.exists_root C.charpoly hdeg
  have heig : Module.End.HasEigenvalue C.mulVecLin z := by
    apply (Module.End.hasEigenvalue_iff_isRoot_charpoly _ _).mpr
    rwa [Matrix.charpoly_mulVecLin]
  have hz0 : z≠0 := by
    intro hz0
    obtain ⟨w,hw⟩ := heig.exists_hasEigenvector
    apply hw.2
    apply Matrix.mulVec_injective_iff_isUnit.mpr hcunit
    have he := hw.apply_eq_smul
    simpa [hz0] using he
  have hzmem := (Polynomial.mem_roots (Matrix.charpoly_monic C).ne_zero).mpr hz
  obtain ⟨m,hm,hmz⟩ := intMatrix_root_is_rootOfUnity M hroots z hzmem hz0
  have heigpow := heig.pow m
  rw [hmz] at heigpow
  have hroot : (C^m).charpoly.IsRoot 1 := by
    have he : (C^m).mulVecLin = C.mulVecLin^m := Matrix.toLin'_pow C m
    rw [←Matrix.charpoly_mulVecLin,he]
    exact (Module.End.hasEigenvalue_iff_isRoot_charpoly _ _).mp heigpow
  have hrootZ : (M^m).charpoly.IsRoot 1 := by
    apply Polynomial.IsRoot.of_map (f := Int.castRingHom ℂ) ?_ (Int.castRingHom ℂ).injective_int
    simpa only [map_one,←Matrix.charpoly_map,Matrix.map_pow] using hroot
  have heigZ : Module.End.HasEigenvalue (M^m).mulVecLin 1 := by
    apply (Module.End.hasEigenvalue_iff_isRoot_charpoly _ _).mpr
    rwa [Matrix.charpoly_mulVecLin]
  obtain ⟨v,hv⟩ := heigZ.exists_hasEigenvector
  refine ⟨m,hm,v,hv.2,?_⟩
  simpa only [Matrix.mulVecLin_apply,one_smul] using hv.apply_eq_smul

end CriticalPercolation.SparseGrowth
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Nilpotent_AbelianConjugationGrowth
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical Matrix IsMulCommutative

namespace CriticalPercolation.SparseGrowth

variable {B : Type*} [CommGroup B]

lemma periodic_lift_of_torsion_coset (f : B ≃* B) (x : B)
    (hx : ¬IsOfFinOrder x) (hfix : f x * x⁻¹ ∈ CommGroup.torsion B) :
    ∃ y : B, ¬IsOfFinOrder y ∧ f y=y := by
  obtain ⟨k,hk,he⟩ := (CommGroup.mem_torsion _).mp hfix |>.exists_pow_eq_one
  refine ⟨x^k,fun hy => hx (hy.of_pow (Nat.ne_of_gt hk)),?_⟩
  rw [map_pow]
  rw [mul_pow,inv_pow,mul_inv_eq_one] at he
  exact he

lemma infinite_fg_commgroup_quotient_torsion_nontrivial [Group.FG B] [Infinite B] :
    Nontrivial (B ⧸ CommGroup.torsion B) := by
  by_contra h
  have hs : Subsingleton (B ⧸ CommGroup.torsion B) := not_nontrivial_iff_subsingleton.mp h
  have ht : IsMulTorsion B := by
    intro x
    exact (QuotientGroup.eq_one_iff (N := CommGroup.torsion B) x).mp (Subsingleton.elim _ _)
  let _ := CommGroup.finite_of_fg_isMulTorsion B ht
  exact not_finite B

variable {A : Type*} [Group A] [DecidableEq A]

theorem HasPolynomialDegree.abelian_normal_periodic_direction {d : ℕ}
    (hg : HasPolynomialDegree A d) (H : Subgroup A) [H.Normal]
    [IsMulCommutative H] [Group.FG H] [Infinite H] (a : A) :
    ∃ m : ℕ, 0 < m ∧ ∃ x : H, ¬IsOfFinOrder x ∧ (MulAut.conjNormal (a^m)) x=x := by
  let T := CommGroup.torsion H
  let Q := H ⧸ T
  let _ : Nontrivial Q := infinite_fg_commgroup_quotient_torsion_nontrivial
  let V := Additive Q
  let _ : Module.Finite ℤ V := Module.Finite.iff_addGroup_fg.mpr inferInstance
  let _ : Module.Free ℤ V := Module.free_of_finite_type_torsion_free'
  let ι := Module.Free.ChooseBasisIndex ℤ V
  let b := Module.Free.chooseBasis ℤ V
  let _ : Fintype ι := Module.Free.ChooseBasisIndex.fintype ℤ V
  let _ : Nonempty ι := b.index_nonempty
  let e := b.equivFun
  let c : Q ≃* Multiplicative (ι → ℤ) :=
    { toFun := fun q => Multiplicative.ofAdd (e (Additive.ofMul q))
      invFun := fun v => Additive.toMul (e.symm (Multiplicative.toAdd v))
      left_inv := by intro q; exact congrArg Additive.toMul (e.symm_apply_apply _)
      right_inv := by intro v; exact congrArg Multiplicative.ofAdd (e.apply_symm_apply _)
      map_mul' := by intro x y; exact congrArg Multiplicative.ofAdd (e.map_add _ _) }
  let f := MulAut.conjNormal a (H := H)
  let fQ := QuotientGroup.congr T T f f.map_torsion
  let fV : V ≃ₗ[ℤ] V := fQ.toAdditive.toIntLinearEquiv
  let M := LinearMap.toMatrix b b fV.toLinearMap
  have hfunit : IsUnit fV.toLinearMap := by
    refine ⟨⟨fV.toLinearMap,fV.symm.toLinearMap,?_,?_⟩,rfl⟩ <;> ext x <;> simp
  have hMunit : IsUnit M := hfunit.map (LinearMap.toMatrixAlgEquiv b)
  let p := c.toMonoidHom.comp (QuotientGroup.mk' T)
  have hp : Surjective p := c.surjective.comp (QuotientGroup.mk'_surjective T)
  have hM : ∀ x : H, Multiplicative.toAdd (p (f x))=M.mulVec (Multiplicative.toAdd (p x)) := by
    intro x
    change e (Additive.ofMul ((QuotientGroup.mk' T) (f x))) =
      M.mulVec (e (Additive.ofMul ((QuotientGroup.mk' T) x)))
    have he := (LinearMap.toMatrix_mulVec_repr b b fV.toLinearMap
      (Additive.ofMul ((QuotientGroup.mk' T) x))).symm
    simpa [←Module.Basis.equivFun_apply, fV, fQ, e, M, MulEquiv.toAdditive] using he
  have hroots := hg.conjugationMatrix_roots_norm_le_one H a p hp M hM
  obtain ⟨m,hm,v,hv,hMv⟩ := intMatrix_exists_periodic_vector M hMunit hroots
  let q := c.symm (Multiplicative.ofAdd v)
  obtain ⟨x,hxq⟩ := QuotientGroup.mk'_surjective T q
  have hqne : q≠1 := by
    intro h
    apply hv
    have hh := congrArg c h
    simpa [q] using hh
  have hx : ¬IsOfFinOrder x := by
    intro hx
    have hqfin : IsOfFinOrder q := hxq ▸ (QuotientGroup.mk' T).isOfFinOrder hx
    exact isMulTorsionFree_iff_not_isOfFinOrder.mp (inferInstance : IsMulTorsionFree Q) hqne hqfin
  have hMp (n : ℕ) (y : H) :
      Multiplicative.toAdd (p ((MulAut.conjNormal (a^n)) y))=
        (M^n).mulVec (Multiplicative.toAdd (p y)) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ',map_mul,MulAut.mul_apply,hM,ih,Matrix.mulVec_mulVec,←pow_succ']
  have hpx : Multiplicative.toAdd (p x)=v := by
    change Multiplicative.toAdd (c ((QuotientGroup.mk' T) x))=v
    rw [hxq]
    exact congrArg Multiplicative.toAdd (c.apply_symm_apply _)
  have hT : (MulAut.conjNormal (a^m)) x*x⁻¹ ∈ T := by
    apply (QuotientGroup.eq_one_iff _).mp
    change (QuotientGroup.mk' T) (_*_)=1
    rw [map_mul,map_inv,mul_inv_eq_one]
    apply c.injective
    apply Multiplicative.toAdd.injective
    change Multiplicative.toAdd (p ((MulAut.conjNormal (a^m)) x))=
      Multiplicative.toAdd (p x)
    rw [hMp,hpx,hMv]
  obtain ⟨y,hy,hyfix⟩ := periodic_lift_of_torsion_coset (MulAut.conjNormal (a^m)) x hx hT
  exact ⟨m,hm,y,hy,hyfix⟩

end CriticalPercolation.SparseGrowth
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_LinearGroups_SolvableGrowth
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical Pointwise IsMulCommutative commutatorElement

namespace CriticalPercolation.SparseGrowth
variable {A B : Type*} [Group A] [Group B] [DecidableEq A]

omit [DecidableEq A] in
lemma isMulCommutative_of_generators (S : Set A) (hgen : Subgroup.closure S=⊤)
    (hcomm : ∀ x∈S, ∀ y∈S, x*y=y*x) : IsMulCommutative A := by
  have hc := Subgroup.isMulCommutative_closure
    (fun left hleft right hright => hcomm left hleft right hright)
  rw [hgen] at hc
  let _ := hc
  exact ⟨⟨fun x y => congrArg Subtype.val
    (mul_comm' (⟨x,Subgroup.mem_top x⟩ : (⊤ : Subgroup A))
      (⟨y,Subgroup.mem_top y⟩ : (⊤ : Subgroup A)))⟩⟩

lemma commutator_eq_normalClosure_generators (S : Finset A)
    (hgen : Subgroup.closure (S : Set A)=⊤) :
    commutator A = Subgroup.normalClosure
      (((S.product S).image (fun p : A×A => ⁅p.1,p.2⁆)) : Set A) := by
  let F := (S.product S).image (fun p : A×A => ⁅p.1,p.2⁆)
  let N := Subgroup.normalClosure (F : Set A)
  change commutator A=N
  apply le_antisymm
  · apply Subgroup.Normal.quotient_commutative_iff_commutator_le.mp
    let q := QuotientGroup.mk' N
    apply isMulCommutative_of_generators (q '' (S : Set A))
    · rw [←MonoidHom.map_closure,hgen,←MonoidHom.range_eq_map]
      exact MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective N)
    · rintro _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩
      apply commutatorElement_eq_one_iff_mul_comm.mp
      rw [←map_commutatorElement]
      apply (QuotientGroup.eq_one_iff ⁅x,y⁆).mpr
      apply Subgroup.subset_normalClosure
      exact Finset.mem_image.mpr ⟨(x,y),Finset.mem_product.mpr ⟨hx,hy⟩,rfl⟩
  · apply Subgroup.normalClosure_le_normal
    intro x hx
    obtain ⟨⟨u,v⟩,huv,rfl⟩ := Finset.mem_image.mp hx
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top u) (Subgroup.mem_top v)

theorem HasPolynomialDegree.commutator_fg {d : ℕ} (h : HasPolynomialDegree A d) :
    (commutator A).FG := by
  obtain ⟨S,h1,hsym,hgen,hg⟩ := (hasPolynomialDegree_iff d).mp h
  rw [commutator_eq_normalClosure_generators S hgen]
  exact normalClosure_fg_of_sparse_growth S _ h1 hsym hgen d hg

omit [DecidableEq A] in
lemma finite_of_fg_torsion_finite_commutator [Group.FG A]
    (ht : IsMulTorsion A) [Finite (commutator A)] : Finite A := by
  let N := commutator A
  let _ : IsMulCommutative (A ⧸ N) :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr le_rfl
  let _ : Finite (A ⧸ N) := CommGroup.finite_of_fg_isMulTorsion _
    (IsMulTorsion.of_surjective (QuotientGroup.mk'_surjective N) ht)
  exact Finite.of_subgroup_quotient N

omit [DecidableEq A] in
lemma map_derivedSeries_commutator (n : ℕ) :
    (derivedSeries (commutator A) n).map (commutator A).subtype =
      derivedSeries A (n+1) := by
  induction n with
  | zero =>
    change (⊤ : Subgroup (commutator A)).map (commutator A).subtype=commutator A
    rw [←MonoidHom.range_eq_map,Subgroup.range_subtype]
  | succ n ih =>
    change (⁅derivedSeries (commutator A) n,derivedSeries (commutator A) n⁆).map _=_
    rw [Subgroup.map_commutator,ih]
    rfl

theorem finite_of_torsion_derivedSeries_eq_bot (n : ℕ) :
    ∀ (A : Type*) [Group A] [DecidableEq A], ∀ d : ℕ,
      HasPolynomialDegree A d → IsMulTorsion A → derivedSeries A n=⊥ → Finite A := by
  induction n with
  | zero =>
    intro A _ _ d hg ht hz
    have hsub : Subsingleton A := by
      constructor
      intro x y
      have hx : x=1 := by
        have hm : x∈derivedSeries A 0 := Subgroup.mem_top x
        simpa only [hz,Subgroup.mem_bot] using hm
      have hy : y=1 := by
        have hm : y∈derivedSeries A 0 := Subgroup.mem_top y
        simpa only [hz,Subgroup.mem_bot] using hm
      exact hx.trans hy.symm
    exact Finite.of_subsingleton
  | succ n ih =>
    intro A _ _ d hg ht hz
    let _ := hg.fg
    let H := commutator A
    let _ : Group.FG H := (Group.fg_iff_subgroup_fg H).mpr hg.commutator_fg
    have hH : HasPolynomialDegree H d := hg.of_injective H.subtype Subtype.val_injective
    have htH := ht.subgroup H
    have hzH : derivedSeries H n=⊥ := by
      apply Subgroup.map_injective (f := H.subtype) Subtype.val_injective
      rw [Subgroup.map_bot,map_derivedSeries_commutator,hz]
    let _ : Finite H := ih H d hH htH hzH
    exact finite_of_fg_torsion_finite_commutator ht

omit [DecidableEq A] in
theorem finite_of_torsion_solvable_sparse_growth {d : ℕ} (hg : HasPolynomialDegree A d)
    (ht : IsMulTorsion A) [Group.IsSolvable A] : Finite A := by
  classical
  obtain ⟨n,hn⟩ := Group.IsSolvable.solvable (G := A)
  exact finite_of_torsion_derivedSeries_eq_bot n A d hg ht hn

end CriticalPercolation.SparseGrowth
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Nilpotent_CharacteristicNilpotentCore
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical Pointwise IsMulCommutative

namespace CriticalPercolation.SparseGrowth
variable {A B : Type*} [Group A] [Group B] [DecidableEq A] [DecidableEq B]

lemma HasPolynomialDegree.of_surjective {d : ℕ} (hg : HasPolynomialDegree A d)
    (f : A →* B) (hf : Surjective f) : HasPolynomialDegree B d := by
  obtain ⟨S,h1,hs,hgen,C,hC⟩ := (hasPolynomialDegree_iff d).mp hg
  apply (hasPolynomialDegree_iff d).mpr
  refine ⟨S.image f,Finset.mem_image.mpr ⟨1,h1,map_one f⟩,?_,?_,C,?_⟩
  · rw [←Finset.image_inv,hs]
  · rw [Finset.coe_image,←MonoidHom.map_closure,hgen]
    exact Subgroup.map_top_of_surjective f hf
  · intro R
    obtain ⟨n,hn,hb⟩ := hC R
    refine ⟨n,hn,le_trans ?_ hb⟩
    rw [←Finset.image_pow]
    exact Finset.card_image_le

omit [DecidableEq A] [DecidableEq B] in
lemma powerSubgroup_le_finiteIndex (L : Subgroup A) [L.Normal] [L.FiniteIndex] :
    powerSubgroup A (Nat.card (A ⧸ L)) ≤ L := by
  apply (Subgroup.closure_le L).mpr
  rintro _ ⟨x,rfl⟩
  apply (QuotientGroup.eq_one_iff _).mp
  change (QuotientGroup.mk' L) (x^_)=1
  rw [map_pow]
  let _ := Fintype.ofFinite (A ⧸ L)
  simpa only [Nat.card_eq_fintype_card] using
    (pow_card_eq_one (x := (QuotientGroup.mk' L) x))

omit [DecidableEq A] [DecidableEq B] in
lemma characteristic_map_normal (N : Subgroup A) [N.Normal]
    (P : Subgroup N) [P.Characteristic] : (P.map N.subtype).Normal := by
  constructor
  rintro _ ⟨x,hx,rfl⟩ a
  refine ⟨(MulAut.conjNormal a) x,?_,rfl⟩
  exact Subgroup.characteristic_iff_le_comap.mp inferInstance (MulAut.conjNormal a) hx

end CriticalPercolation.SparseGrowth
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Nilpotent_FiniteCyclicExtensionIndex
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical

namespace CriticalPercolation.SparseGrowth
variable {A : Type*} [Group A]

lemma finiteIndex_of_finite_kernel_int (f : A →* Multiplicative ℤ)
    [Finite f.ker] (a : A) (ha : f a=Multiplicative.ofAdd 1)
    (H : Subgroup A) (m : ℕ) (hm : 0 < m) (haH : a^m ∈ H) : H.FiniteIndex := by
  let F : f.ker × Fin m → A ⧸ H := fun p => QuotientGroup.mk (p.1.val*a^p.2.val)
  have hF : Surjective F := by
    intro q
    obtain ⟨x,rfl⟩ := QuotientGroup.mk_surjective q
    let n : ℤ := (f x).toAdd
    let k : A := x*a^(-n)
    have hk : k∈f.ker := by
      change f k=1
      apply Multiplicative.toAdd.injective
      simp [k,map_zpow,ha,n]
    let r : Fin m := ⟨(n % (m:ℤ)).toNat,by
      have hr0 := Int.emod_nonneg n (by omega : (m:ℤ)≠0)
      have hr := Int.emod_lt_of_pos n (by omega : 0<(m:ℤ))
      omega⟩
    refine ⟨(⟨k,hk⟩,r),?_⟩
    apply QuotientGroup.eq.mpr
    change (k*a^r.val)⁻¹*x∈H
    have hr : (r.val:ℤ)=n%(m:ℤ) := Int.toNat_of_nonneg
      (Int.emod_nonneg n (by omega : (m:ℤ)≠0))
    have he : (k*a^r.val)⁻¹*x=(a^m)^(n/(m:ℤ)) := by
      calc
        (k*a^r.val)⁻¹*x = a^(-(r.val:ℤ))*a^n := by simp only [k,mul_inv_rev,zpow_neg,←zpow_natCast]; group
        _ = a^((m:ℤ)*(n/(m:ℤ))) := by
          rw [←zpow_add,hr]
          congr 1
          have hh := Int.emod_add_mul_ediv n (m:ℤ)
          omega
        _ = (a^m)^(n/(m:ℤ)) := by rw [zpow_mul,zpow_natCast]
    rw [he]
    exact H.zpow_mem haH _
  let _ : Finite (A ⧸ H) := Finite.of_surjective F hF
  exact Subgroup.finiteIndex_of_finite_quotient

lemma finite_lift_kernel (f : A →* Multiplicative ℤ) (L : Subgroup A) [L.Normal]
    (hL : L ≤ f.ker) [(L.subgroupOf f.ker).FiniteIndex] :
    Finite (QuotientGroup.lift L f hL).ker := by
  let q := QuotientGroup.mk' L
  let p := q.comp f.ker.subtype
  have hpker : p.ker=L.subgroupOf f.ker := by
    ext x
    exact QuotientGroup.eq_one_iff (N := L) x.val
  let _ : p.ker.FiniteIndex := hpker.symm ▸ (inferInstance : (L.subgroupOf f.ker).FiniteIndex)
  let _ : Finite p.range := Finite.of_equiv (f.ker ⧸ p.ker)
    (QuotientGroup.quotientKerEquivRange p).toEquiv
  have he : p.range=(QuotientGroup.lift L f hL).ker := by
    ext x
    constructor
    · rintro ⟨y,rfl⟩
      exact y.property
    · intro hx
      obtain ⟨y,rfl⟩ := QuotientGroup.mk'_surjective L x
      exact ⟨⟨y,hx⟩,rfl⟩
  exact he ▸ (inferInstance : Finite p.range)

lemma finiteIndex_of_normal_kernel_subgroup (f : A →* Multiplicative ℤ)
    (L : Subgroup A) [L.Normal] (hL : L ≤ f.ker) [(L.subgroupOf f.ker).FiniteIndex]
    (a : A) (ha : f a=Multiplicative.ofAdd 1)
    (H : Subgroup A) (hLH : L ≤ H) (m : ℕ) (hm : 0 < m) (haH : a^m ∈ H) :
    H.FiniteIndex := by
  let q := QuotientGroup.mk' L
  let g := QuotientGroup.lift L f hL
  let _ : Finite g.ker := finite_lift_kernel f L hL
  have hi : (H.map q).FiniteIndex := finiteIndex_of_finite_kernel_int g (q a) ha
    (H.map q) m hm (by rw [←map_pow]; exact ⟨a^m,haH,rfl⟩)
  constructor
  rw [←Subgroup.index_map_eq H (QuotientGroup.mk'_surjective L)
    (by simpa only [QuotientGroup.ker_mk'] using hLH)]
  exact hi.index_ne_zero

end CriticalPercolation.SparseGrowth
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Nilpotent_NilpotentInfiniteCenter
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical commutatorElement

namespace CriticalPercolation.SparseGrowth
variable {A : Type*} [Group A]

lemma finite_upperCentralSeriesStep [Group.FG A] [Finite (Subgroup.center A)]
    (N : Subgroup A) [N.Normal] [Finite N] :
    Finite (Subgroup.upperCentralSeriesStep N) := by
  obtain ⟨S,hS⟩ := Group.fg_def.mp (inferInstance : Group.FG A)
  let U := Subgroup.upperCentralSeriesStep N
  let f : U → (S → N) := fun u s => ⟨⁅u.val,s.val⁆,u.property s.val⟩
  have hdiff (u v : U) (h : f u=f v) : v.val⁻¹*u.val ∈ Subgroup.center A := by
    rw [←Subgroup.centralizer_univ,←Subgroup.coe_top,←hS,Subgroup.centralizer_closure]
    intro s hs
    have he := congrArg (fun g : S → N => (g ⟨s,hs⟩).val) h
    change ⁅u.val,s⁆=⁅v.val,s⁆ at he
    simp only [commutatorElement_def] at he
    calc
      s*(v.val⁻¹*u.val) = v.val⁻¹*(v.val*s*v.val⁻¹*s⁻¹)*s*u.val := by group
      _ = v.val⁻¹*(u.val*s*u.val⁻¹*s⁻¹)*s*u.val := by rw [he]
      _ = v.val⁻¹*u.val*s := by group
  have hf (b : S → N) : Finite {u : U // f u=b} := by
    by_cases hb : Nonempty {u : U // f u=b}
    · obtain ⟨v,hv⟩ := hb
      let e : {u : U // f u=b} → Subgroup.center A := fun u =>
        ⟨v.val⁻¹*u.val.val,hdiff u.val v (u.property.trans hv.symm)⟩
      apply Finite.of_injective e
      intro u w he
      apply Subtype.ext
      apply Subtype.ext
      have he' := congrArg Subtype.val he
      exact mul_left_cancel he'
    · let _ : IsEmpty {u : U // f u=b} := not_nonempty_iff.mp hb
      infer_instance
  let _ : ∀ b : S → N, Finite {u : U // f u=b} := hf
  apply Finite.of_injective (fun u : U => (⟨f u,⟨u,rfl⟩⟩ : Σ b : S → N, {u : U // f u=b}))
  intro u v h
  exact congrArg (fun x : Σ b : S → N, {u : U // f u=b} => x.2.val) h

theorem finite_of_finite_center [Group.FG A] [Group.IsNilpotent A]
    [Finite (Subgroup.center A)] : Finite A := by
  have hf (n : ℕ) : Finite (Subgroup.upperCentralSeries A n) := by
    induction n with
    | zero => simpa only [Subgroup.upperCentralSeries_zero] using
        (inferInstance : Finite (⊥ : Subgroup A))
    | succ n ih =>
      let _ := ih
      exact finite_upperCentralSeriesStep (Subgroup.upperCentralSeries A n)
  obtain ⟨n,hn⟩ := Group.IsNilpotent.nilpotent A
  let _ : Finite (⊤ : Subgroup A) := hn ▸ hf n
  exact Finite.of_surjective (⊤ : Subgroup A).subtype (by intro x; exact ⟨⟨x,Subgroup.mem_top x⟩,rfl⟩)

theorem infinite_center_of_nilpotent [Group.FG A] [Group.IsNilpotent A]
    [Infinite A] : Infinite (Subgroup.center A) := by
  rcases finite_or_infinite (Subgroup.center A) with hf | hi
  · let _ := hf
    let _ : Finite A := finite_of_finite_center
    exact False.elim (_root_.not_finite A)
  · exact hi

end CriticalPercolation.SparseGrowth
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_LinearGroups_GeneralPeriodicCenter
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical IsMulCommutative

namespace CriticalPercolation.SparseGrowth
variable {A : Type*} [Group A] [DecidableEq A]

lemma HasPolynomialDegree.periodic_center_of_fg_nilpotent_kernel {d : ℕ}
    (hg : HasPolynomialDegree A d)
    (f : A →* Multiplicative ℤ) (hf : Surjective f)
    (L : Subgroup A) [L.Normal] [Group.IsNilpotent L] [Group.FG L] [Infinite L]
    (hLK : L ≤ f.ker) [(L.subgroupOf f.ker).FiniteIndex] :
    ∃ H : Subgroup A, H.FiniteIndex ∧ ∃ x : H,
      x∈Subgroup.center H ∧ ¬IsOfFinOrder x := by
  let Z := Subgroup.center L
  let _ : Infinite Z := infinite_center_of_nilpotent
  let C := Z.map L.subtype
  let e : Z ≃* C := Z.equivMapOfInjective L.subtype Subtype.val_injective
  let _ : C.Normal := characteristic_map_normal L Z
  let _ : IsMulCommutative C := ⟨⟨fun x y => e.symm.injective (by
    simp only [map_mul]; exact mul_comm _ _)⟩⟩
  let _ : Infinite C := Infinite.of_injective e e.injective
  let _ : Group.FG Z := nilpotent_subgroup_fg L Z
  let _ : Group.FG C := Group.fg_of_surjective (f := e.toMonoidHom) e.surjective
  obtain ⟨a,ha⟩ := hf (Multiplicative.ofAdd 1)
  obtain ⟨m,hm,x,hx,hfix⟩ := hg.abelian_normal_periodic_direction C a
  let H := Subgroup.centralizer ({x.val} : Set A)
  have hLH : L≤H := by
    intro l hl
    obtain ⟨z,hz,hzx⟩ := x.property
    rw [Subgroup.mem_centralizer_singleton_iff,←hzx]
    exact congrArg Subtype.val ((Subgroup.mem_center_iff.mp hz) ⟨l,hl⟩)
  have haH : a^m∈H := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have he := congrArg Subtype.val hfix
    change a^m*x.val*(a^m)⁻¹=x.val at he
    exact mul_inv_eq_iff_eq_mul.mp he
  have hHi : H.FiniteIndex := finiteIndex_of_normal_kernel_subgroup f L hLK a ha H hLH m hm haH
  let y : H := ⟨x.val,by rw [Subgroup.mem_centralizer_singleton_iff]⟩
  refine ⟨H,hHi,y,?_,?_⟩
  · rw [Subgroup.mem_center_iff]
    intro w
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp w.property
  · intro hy
    obtain ⟨k,hk,he⟩ := hy.exists_pow_eq_one
    apply hx
    apply isOfFinOrder_iff_pow_eq_one.mpr
    exact ⟨k,hk,Subtype.ext (congrArg (fun z : H => z.val) he)⟩

end CriticalPercolation.SparseGrowth
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Nilpotent_GeneralNilpotentCore
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical IsMulCommutative

namespace CriticalPercolation.SparseGrowth
variable {A B : Type*} [Group A] [Group B] [DecidableEq A] [DecidableEq B]

omit [DecidableEq A] [DecidableEq B] in
lemma virtuallyNilpotent_of_surjective (f : A →* B) (hf : Surjective f)
    (hv : Group.IsVirtuallyNilpotent A) : Group.IsVirtuallyNilpotent B := by
  obtain ⟨N,hN,hNi⟩ := hv
  let _ := hN
  let _ := hNi
  refine ⟨N.map f,?_,⟨fun he => hNi.index_ne_zero (by have hh := N.index_map_dvd hf; simpa [he] using hh)⟩⟩
  let g : N →* N.map f := {
    toFun := fun x => ⟨f x,⟨x,x.property,rfl⟩⟩
    map_one' := Subtype.ext (map_one f)
    map_mul' := fun x y => Subtype.ext (map_mul f x.val y.val) }
  apply Group.nilpotent_of_surjective g
  rintro ⟨y,x,hx,rfl⟩
  exact ⟨⟨x,hx⟩,rfl⟩

omit [DecidableEq B] in
lemma finite_of_torsion_virtuallyNilpotent_growth {d : ℕ}
    (hg : HasPolynomialDegree A d) (ht : IsMulTorsion A)
    (hv : Group.IsVirtuallyNilpotent A) : Finite A := by
  obtain ⟨N,hN,hNi⟩ := hv
  let _ := hN
  let _ := hNi
  let _ : Finite N := finite_of_torsion_solvable_sparse_growth
    (hg.finiteIndex_subgroup N) (ht.subgroup N)
  exact N.finite_iff_finite_and_finiteIndex.mpr ⟨inferInstance,hNi⟩

omit [DecidableEq B] in
lemma HasPolynomialDegree.powerSubgroup_finiteIndex {d : ℕ}
    (hg : HasPolynomialDegree A d) (hv : Group.IsVirtuallyNilpotent A)
    (k : ℕ) (hk : 0<k) : (powerSubgroup A k).FiniteIndex := by
  let P := powerSubgroup A k
  have ht : IsMulTorsion (A ⧸ P) := by
    intro q
    obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective P q
    apply isOfFinOrder_iff_pow_eq_one.mpr
    refine ⟨k,hk,?_⟩
    rw [←map_pow]
    apply (QuotientGroup.eq_one_iff _).mpr
    exact Subgroup.subset_closure ⟨x,rfl⟩
  have hq := hg.of_surjective (QuotientGroup.mk' P) (QuotientGroup.mk'_surjective P)
  have hvq := virtuallyNilpotent_of_surjective (QuotientGroup.mk' P)
    (QuotientGroup.mk'_surjective P) hv
  let _ : Finite (A ⧸ P) := finite_of_torsion_virtuallyNilpotent_growth hq ht hvq
  exact Subgroup.finiteIndex_of_finite_quotient

omit [DecidableEq B] in
lemma HasPolynomialDegree.characteristic_nilpotent_core_general {d : ℕ}
    (hg : HasPolynomialDegree A d) (hv : Group.IsVirtuallyNilpotent A) :
    ∃ P : Subgroup A, P.Characteristic ∧ P.FiniteIndex ∧ Group.IsNilpotent P := by
  obtain ⟨L,hL,hLi⟩ := hv
  let _ := hL
  let _ := hLi
  let N := L.normalCore
  let k := Nat.card (A ⧸ N)
  have hk : 0 < k := Nat.card_pos
  let P := powerSubgroup A k
  have hPL : P≤L := (powerSubgroup_le_finiteIndex N).trans L.normalCore_le
  refine ⟨P,inferInstance,hg.powerSubgroup_finiteIndex ⟨L,hL,hLi⟩ k hk,?_⟩
  let f : P →* L := Subgroup.inclusion hPL
  apply Subgroup.isNilpotent_of_ker_le_center f
  rw [(MonoidHom.ker_eq_bot_iff f).mpr (Subgroup.inclusion_injective hPL)]
  exact bot_le

end CriticalPercolation.SparseGrowth
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Criticality_IndicableDegreeStep
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical IsMulCommutative

namespace CriticalPercolation.SparseGrowth
universe u

theorem virtuallyNilpotent_of_indicability_degree_step
    (d : ℕ)
    (ih : ∀ (B : Type u) [Group B] [DecidableEq B],
      HasPolynomialDegree B d → Group.IsVirtuallyNilpotent B)
    (A : Type u) [Group A] [DecidableEq A]
    (hg : HasPolynomialDegree A (d+1))
    (hind : ∃ H : Subgroup A, H.FiniteIndex ∧
      ∃ f : H →* Multiplicative ℤ, Surjective f) :
    Group.IsVirtuallyNilpotent A := by
    rcases finite_or_infinite A with hfin | hinf
    · let _ := hfin
      exact virtuallyNilpotent_of_finite
    let _ := hinf
    obtain ⟨H,hHi,f,hf⟩ := hind
    let _ := hHi
    apply virtuallyNilpotent_of_finiteIndex H
    have hgH := hg.finiteIndex_subgroup H
    let _ : Group.FG H := hgH.fg
    let K := f.ker
    let _ : Group.FG K := hgH.integer_kernel_fg f hf
    let _ : Infinite (H ⧸ K) :=
      (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv.infinite_iff.mpr inferInstance
    have hgK := hgH.normal_subgroup_descent K
    have hvK := ih K hgK
    obtain ⟨P,hP,hPi,hPn⟩ := hgK.characteristic_nilpotent_core_general hvK
    let _ := hP
    let _ := hPi
    let _ := hPn
    let L := P.map K.subtype
    let e : P ≃* L := P.equivMapOfInjective K.subtype Subtype.val_injective
    let _ : L.Normal := characteristic_map_normal K P
    let _ : Group.IsNilpotent L := Group.nilpotent_of_surjective e.toMonoidHom e.surjective
    have hLK : L≤K := Subgroup.map_subtype_le P
    have he : L.subgroupOf K=P := by
      exact Subgroup.comap_map_eq_self_of_injective K.subtype_injective P
    let _ : (L.subgroupOf K).FiniteIndex := he.symm ▸ hPi
    rcases finite_or_infinite L with hLf | hLi
    · let _ := hLf
      let _ : Finite P := Finite.of_equiv L e.symm.toEquiv
      let _ : Finite K := P.finite_iff_finite_and_finiteIndex.mpr ⟨inferInstance,hPi⟩
      exact CompactQuotient.virtuallyNilpotent_of_finite_kernel f (Set.toFinite _)
        (Group.IsNilpotent.isVirtuallyNilpotent inferInstance)
    · let _ := hLi
      let _ : Group.FG P := inferInstance
      let _ : Group.FG L := Group.fg_of_surjective (f := e.toMonoidHom) e.surjective
      obtain ⟨J,hJi,x,hx,hxinf⟩ := hgH.periodic_center_of_fg_nilpotent_kernel f hf L hLK
      let _ := hJi
      apply virtuallyNilpotent_of_finiteIndex J
      have hgJ := hgH.finiteIndex_subgroup J
      have hgQ := hgJ.quotient_descent (Subgroup.center J) x hx (orderOf_eq_zero hxinf)
      have hvQ := ih (J ⧸ Subgroup.center J) hgQ
      exact virtuallyNilpotent_of_central_kernel (QuotientGroup.mk' (Subgroup.center J))
        (by rw [QuotientGroup.ker_mk']) hvQ

end CriticalPercolation.SparseGrowth
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Criticality_VirtualIndicability
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical IsMulCommutative

namespace CriticalPercolation.SparseGrowth

lemma infinite_fg_abelian_surjects_int (B : Type*) [CommGroup B] [Group.FG B]
    [Infinite B] : ∃ f : B →* Multiplicative ℤ, Surjective f := by
  rcases abelian_alternatives B with hf | ⟨f,hf,_⟩ | ⟨f,hf⟩
  · let _ := hf
    exact False.elim (_root_.not_finite B)
  · exact ⟨f,hf⟩
  · let p : Multiplicative (ℤ×ℤ) →* Multiplicative ℤ :=
      (AddMonoidHom.fst ℤ ℤ).toMultiplicative
    have hp : Surjective p := fun z => ⟨Multiplicative.ofAdd (z.toAdd,0),rfl⟩
    exact ⟨p.comp f,hp.comp hf⟩

lemma virtually_indicable_of_derivedSeries_eq_bot (n : ℕ) :
    ∀ (A : Type*) [Group A] [DecidableEq A], ∀ d : ℕ,
      HasPolynomialDegree A d → derivedSeries A n=⊥ → Infinite A →
      ∃ H : Subgroup A, H.FiniteIndex ∧
        ∃ f : H →* Multiplicative ℤ, Surjective f := by
  induction n with
  | zero =>
    intro A _ _ d hg hz hi
    have hs : Subsingleton A := by
      constructor
      intro x y
      have hx : x=1 := by simpa only [hz,Subgroup.mem_bot] using
        (show x∈derivedSeries A 0 from Subgroup.mem_top x)
      have hy : y=1 := by simpa only [hz,Subgroup.mem_bot] using
        (show y∈derivedSeries A 0 from Subgroup.mem_top y)
      exact hx.trans hy.symm
    exact False.elim (_root_.not_finite A)
  | succ n ih =>
    intro A _ _ d hg hz hi
    let _ := hg.fg
    let C := commutator A
    let _ : Group.FG C := (Group.fg_iff_subgroup_fg C).mpr hg.commutator_fg
    let Q := A ⧸ C
    let _ : IsMulCommutative Q :=
      Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr le_rfl
    rcases finite_or_infinite Q with hq | hq
    · let _ := hq
      let _ : C.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
      have hc : Infinite C := by
        rcases finite_or_infinite C with hfin | hinf
        · let _ := hfin
          let _ : Finite A := (C.finite_iff_finite_and_finiteIndex).mpr ⟨hfin,inferInstance⟩
          exact False.elim (_root_.not_finite A)
        · exact hinf
      have hgC := hg.of_injective C.subtype Subtype.val_injective
      have hzC : derivedSeries C n=⊥ := by
        apply Subgroup.map_injective (f := C.subtype) Subtype.val_injective
        rw [Subgroup.map_bot,map_derivedSeries_commutator,hz]
      obtain ⟨H,hHi,f,hf⟩ := ih C d hgC hzC hc
      let _ := hHi
      let J := H.map C.subtype
      let e : H ≃* J := H.equivMapOfInjective C.subtype Subtype.val_injective
      have hJi : J.FiniteIndex := by
        constructor
        rw [Subgroup.index_map_subtype]
        exact mul_ne_zero hHi.index_ne_zero (inferInstance : C.FiniteIndex).index_ne_zero
      exact ⟨J,hJi,f.comp e.symm.toMonoidHom,hf.comp e.symm.surjective⟩
    · let _ := hq
      obtain ⟨f,hf⟩ := infinite_fg_abelian_surjects_int Q
      let e : (⊤ : Subgroup A) ≃* A := Subgroup.topEquiv
      exact ⟨⊤,inferInstance,(f.comp (QuotientGroup.mk' C)).comp e.toMonoidHom,
        hf.comp ((QuotientGroup.mk'_surjective C).comp e.surjective)⟩

theorem HasPolynomialDegree.virtually_indicable {A : Type*} [Group A] [DecidableEq A]
    {d : ℕ} (hg : HasPolynomialDegree A d) [Group.IsSolvable A] [Infinite A] :
    ∃ H : Subgroup A, H.FiniteIndex ∧ ∃ f : H →* Multiplicative ℤ, Surjective f := by
  obtain ⟨n,hn⟩ := Group.IsSolvable.solvable (G := A)
  exact virtually_indicable_of_derivedSeries_eq_bot n A d hg hn inferInstance

end CriticalPercolation.SparseGrowth
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_LinearGroups_InvariantBlockSolvability
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Module Function

namespace CriticalPercolation.LinearGrowth
variable {K V G : Type*} [Field K] [AddCommGroup V] [Module K V] [Group G]

lemma commute_of_identity_on_subspace_quotient (W : Submodule K V) (e f : V ≃ₗ[K] V)
    (heW : ∀ w∈W, e w=w) (hfW : ∀ w∈W, f w=w)
    (heQ : ∀ v, e v-v∈W) (hfQ : ∀ v, f v-v∈W) : e*f=f*e := by
  ext v
  have he := heW (f v-v) (hfQ v)
  have hf := hfW (e v-v) (heQ v)
  rw [map_sub] at he hf
  change e (f v)=f (e v)
  have h1 : e (f v)=f v-v+e v := (sub_eq_iff_eq_add).mp he
  have h2 : f (e v)=e v-v+f v := (sub_eq_iff_eq_add).mp hf
  rw [h1,h2]
  abel

lemma solvable_of_subspace_quotient (ρ : G →* (V ≃ₗ[K] V)) (hρ : Injective ρ)
    (W : Submodule K V) (hW : ∀ g, W.map (ρ g).toLinearMap=W)
    [Group.IsSolvable (subspaceRepresentation ρ W hW).range]
    [Group.IsSolvable (quotientRepresentation ρ W hW).range] : Group.IsSolvable G := by
  let σ := subspaceRepresentation ρ W hW
  let τ := quotientRepresentation ρ W hW
  let ψ := σ.rangeRestrict.prod τ.rangeRestrict
  have hker : Group.IsSolvable ψ.ker := by
    apply Group.isSolvable_of_comm
    intro x y
    apply Subtype.ext
    apply hρ
    change ρ (x.val*y.val)=ρ (y.val*x.val)
    rw [map_mul,map_mul]
    have hs (g : ψ.ker) : σ g.val=1 := by
      have he := congrArg (fun z : σ.range × τ.range => (z.1 : W ≃ₗ[K] W)) g.property
      exact he
    have ht (g : ψ.ker) : τ g.val=1 := by
      have he := congrArg (fun z : σ.range × τ.range => (z.2 : (V ⧸ W) ≃ₗ[K] (V ⧸ W))) g.property
      exact he
    have hsub (g : ψ.ker) (w : V) (hw : w∈W) : ρ g.val w=w :=
      congrArg (fun e : W ≃ₗ[K] W => (e ⟨w,hw⟩ : V)) (hs g)
    have hquot (g : ψ.ker) (v : V) : ρ g.val v-v∈W := by
      apply (Submodule.Quotient.eq W).mp
      exact congrArg (fun e : (V ⧸ W) ≃ₗ[K] (V ⧸ W) => e (Submodule.Quotient.mk v)) (ht g)
    exact commute_of_identity_on_subspace_quotient W (ρ x.val) (ρ y.val)
      (hsub x) (hsub y) (hquot x) (hquot y)
  let := hker
  exact Group.isSolvable_of_ker_le_range ψ.ker.subtype ψ (by simp)

end CriticalPercolation.LinearGrowth
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_LinearGroups_BurnsideDensity
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Function Module
open scoped Classical

namespace CriticalPercolation.LinearGrowth

lemma toModuleEnd_surjective_of_simple {K A V : Type*} [Field K] [IsAlgClosed K]
    [Ring A] [Algebra K A] [AddCommGroup V] [Module K V] [Module A V]
    [IsScalarTower K A V] [IsSimpleModule A V] [FiniteDimensional K V] :
    Surjective (Module.toModuleEnd K (S:=A) V) := by
  let E := Module.End A V
  have he : Surjective (algebraMap K E) :=
    (IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed K).2
  let : Module.Finite E V := Module.Finite.of_restrictScalars_finite K E V
  intro T
  let T' : Module.End E V := {
    toFun := T
    map_add' := T.map_add
    map_smul' := by
      intro e x
      obtain ⟨c,rfl⟩ := he e
      change T (c • x)=c • T x
      exact T.map_smul c x }
  obtain ⟨a,ha⟩ := Module.Finite.toModuleEnd_moduleEnd_surjective (R:=A) (M:=V) T'
  refine ⟨a,?_⟩
  ext x
  exact congrArg (fun f : Module.End E V => f x) ha

lemma subalgebra_eq_top_of_simple {K V : Type*} [Field K] [IsAlgClosed K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (A : Subalgebra K (Module.End K V))
    [IsSimpleModule A V] : A=⊤ := by
  apply top_unique
  intro T _
  obtain ⟨a,ha⟩ := toModuleEnd_surjective_of_simple (K:=K) (A:=A) (V:=V) T
  have he : (a : Module.End K V)=T := by
    ext v
    exact congrArg (fun f : Module.End K V => f v) ha
  exact he ▸ a.property

end CriticalPercolation.LinearGrowth
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_LinearGroups_InvariantSubspaceDensity
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function Module
open scoped Classical

namespace CriticalPercolation.LinearGrowth
variable {K V G : Type*} [Field K] [IsAlgClosed K] [AddCommGroup V] [Module K V]
variable [FiniteDimensional K V] [Nontrivial V] [Group G]

lemma invariant_subspace_of_not_fullSpan (ρ : G →* (V ≃ₗ[K] V)) (hρ : ¬FullSpan ρ) :
    ∃ W : Submodule K V, W≠⊥ ∧ W≠⊤ ∧ ∀ g, W.map (ρ g).toLinearMap=W := by
  let σ : G →* End K V := LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp ρ
  let A := Algebra.adjoin K ((MonoidHom.mrange σ) : Set (End K V))
  have hAspan : A.toSubmodule=Submodule.span K (Set.range (fun g => (ρ g).toLinearMap)) := by
    rw [Algebra.adjoin_eq_span,Submonoid.closure_eq]
    rfl
  have hA : A≠⊤ := by
    intro he
    apply hρ
    change Submodule.span K (Set.range (fun g => (ρ g).toLinearMap))=⊤
    rw [←hAspan,he]
    rfl
  have hns : ¬IsSimpleModule A V := by
    intro h
    exact hA (subalgebra_eq_top_of_simple A)
  have he : ∃ P : Submodule A V, P≠⊥ ∧ P≠⊤ := by
    by_contra hn
    push Not at hn
    have : IsSimpleOrder (Submodule A V) := IsSimpleOrder.of_forall_eq_top hn
    exact hns ⟨⟩
  obtain ⟨P,hP0,hP1⟩ := he
  let W := P.restrictScalars K
  have hρmem (g : G) : (ρ g).toLinearMap∈A :=
    Algebra.subset_adjoin (show σ g∈(MonoidHom.mrange σ) from ⟨g,rfl⟩)
  have hstable (g : G) {v : V} (hv : v∈W) : ρ g v∈W :=
    P.smul_mem ⟨(ρ g).toLinearMap,hρmem g⟩ hv
  refine ⟨W,?_,?_,?_⟩
  · intro hw
    apply hP0
    apply Submodule.restrictScalars_injective K A V
    simpa only [Submodule.restrictScalars_bot] using hw
  · intro hw
    apply hP1
    apply Submodule.restrictScalars_injective K A V
    simpa only [Submodule.restrictScalars_top] using hw
  · intro g
    ext v
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact hstable g hx
    · intro hv
      refine ⟨ρ g⁻¹ v,hstable g⁻¹ hv,?_⟩
      simp only [map_inv,LinearEquiv.coe_coe,LinearEquiv.coe_inv,
        LinearEquiv.apply_symm_apply]

end CriticalPercolation.LinearGrowth
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_LinearGroups_FgMatrixRing
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical Pointwise BigOperators

namespace CriticalPercolation.LinearGrowth
variable {G R : Type*} [Group G] [CommRing R]
variable {n : Type*} [Fintype n] [DecidableEq n]

lemma exists_finiteType_matrix_ring [Group.FG G] (ρ : G →* GL n R) :
    ∃ D : Subalgebra ℤ R, Algebra.FiniteType ℤ D ∧ ∀ g i j, ρ g i j∈D := by
  obtain ⟨S,hS,hSf⟩ := Group.fg_iff.mp (inferInstance : Group.FG G)
  let T := hSf.toFinset ∪ hSf.toFinset⁻¹
  let E := T.biUnion (fun g => Finset.univ.biUnion (fun i => Finset.univ.image (fun j => ρ g i j)))
  let D := Algebra.adjoin ℤ (E : Set R)
  have hD : Algebra.FiniteType ℤ D := (Subalgebra.fg_iff_finiteType _).mp (Subalgebra.fg_adjoin_finset E)
  have hgen (g : G) (hg : g∈T) (i j : n) : ρ g i j∈D := by
    apply Algebra.subset_adjoin
    exact Finset.mem_biUnion.mpr ⟨g,hg,Finset.mem_biUnion.mpr
      ⟨i,Finset.mem_univ _,Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩⟩⟩
  refine ⟨D,hD,?_⟩
  intro g
  have hg : g∈Subgroup.closure S := by rw [hS]; trivial
  induction hg using Subgroup.closure_induction'' with
  | mem a ha => exact hgen a (Finset.mem_union_left _ (hSf.mem_toFinset.mpr ha))
  | inv_mem a ha =>
    apply hgen a⁻¹
    apply Finset.mem_union_right
    simpa using hSf.mem_toFinset.mpr ha
  | one =>
    intro i j
    rw [map_one]
    by_cases h : i=j <;> simp [h,D.zero_mem,D.one_mem]
  | mul a b ha hb iha ihb =>
    intro i j
    rw [map_mul]
    change (∑ l, ρ a i l*ρ b l j)∈D
    exact D.sum_mem (fun l _ => D.mul_mem (iha i l) (ihb l j))

variable (ρ : G →* GL n R) (D : Subalgebra ℤ R) (hD : ∀ g i j, ρ g i j∈D)

lemma liftMatrixGroup_injective (hρ : Injective ρ) : Injective (liftMatrixGroup ρ D hD) := by
  intro x y he
  apply hρ
  apply Units.ext
  ext i j
  exact congrArg (fun M : GL n D => ((M i j : D) : R)) he

end CriticalPercolation.LinearGrowth
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_LinearGroups_AlgebraicVirtualSolvability
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function Module
open scoped Classical

namespace CriticalPercolation.LinearGrowth

lemma finiteIndex_comap_surjective {A B : Type*} [Group A] [Group B]
    (f : A →* B) (hf : Surjective f) (P : Subgroup B) [P.FiniteIndex] :
    (P.comap f).FiniteIndex := by
  constructor
  rw [Subgroup.index_comap,f.range_eq_top_of_surjective hf,Subgroup.relIndex_top_right]
  exact Subgroup.FiniteIndex.index_ne_zero

lemma solvable_range_of_mem {A B : Type*} [Group A] [Group B]
    (f : A →* B) (P : Subgroup B) [Group.IsSolvable P] (hp : ∀ a, f a∈P) :
    Group.IsSolvable f.range := by
  have hh : f.range≤P := by rintro _ ⟨a,rfl⟩; exact hp a
  exact Group.isSolvable_of_isSolvable_injective (f:=Subgroup.inclusion hh)
    (Subgroup.inclusion_injective hh)

lemma solvable_restricted_range {A B : Type*} [Group A] [Group B]
    (f : A →* B) (P : Subgroup f.range) [Group.IsSolvable P]
    (J : Subgroup A) (hJ : J≤P.comap f.rangeRestrict) :
    Group.IsSolvable (f.comp J.subtype).range := by
  let Q := P.map f.range.subtype
  let e := P.equivMapOfInjective f.range.subtype Subtype.val_injective
  let : Group.IsSolvable Q := Group.isSolvable_of_surjective (f:=e.toMonoidHom) e.surjective
  apply solvable_range_of_mem (f.comp J.subtype) Q
  intro j
  exact ⟨f.rangeRestrict j.val,hJ j.property,rfl⟩

lemma virtually_solvable_linear_of_rank (K : Type) [Field K] [CharZero K]
    [Countable K] [IsAlgClosed K] (r : ℕ) :
    ∀ (V G : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V]
      [Group G] [DecidableEq G], finrank K V=r →
      ∀ (ρ : G →* (V ≃ₗ[K] V)), Injective ρ →
      ∀ d, SparseGrowth.HasPolynomialDegree G d →
      ∃ H : Subgroup G, H.FiniteIndex ∧ Group.IsSolvable H := by
  induction r using Nat.strong_induction_on with
  | h r ih =>
    intro V G _ _ _ _ _ hr ρ hρ d hg
    rcases subsingleton_or_nontrivial V with hv | hv
    · let := hv
      have hc : ∀ g h : G, g*h=h*g := by
        intro g h
        apply hρ
        exact Subsingleton.elim _ _
      let : Group.IsSolvable G := Group.isSolvable_of_comm hc
      exact ⟨⊤,inferInstance,inferInstance⟩
    let := hv
    by_cases hd : StrongFullSpan ρ
    · obtain ⟨H,hHi,hH⟩ := hd.virtually_comm_range_bs ρ hg
      let : Group.IsSolvable (ρ.comp H.subtype).range := Group.isSolvable_of_comm hH
      have hinj : Injective (ρ.comp H.subtype).rangeRestrict := by
        intro x y he
        apply Subtype.ext
        apply hρ
        exact congrArg Subtype.val he
      exact ⟨H,hHi,Group.isSolvable_of_isSolvable_injective hinj⟩
    obtain ⟨H,hHi,hH⟩ : ∃ H : Subgroup G, H.FiniteIndex ∧ ¬FullSpan (ρ.comp H.subtype) := by
      simp only [StrongFullSpan,not_forall] at hd
      obtain ⟨H,hHi,hH⟩ := hd
      exact ⟨H,hHi,hH⟩
    let := hHi
    let ρH := ρ.comp H.subtype
    have hgH := hg.finiteIndex_subgroup H
    obtain ⟨W,hW0,hW1,hW⟩ := invariant_subspace_of_not_fullSpan ρH hH
    let σ := subspaceRepresentation ρH W hW
    let τ := quotientRepresentation ρH W hW
    have hWrank : finrank K W < r := hr ▸ Submodule.finrank_lt hW1
    have hQrank : finrank K (V ⧸ W) < r := by
      have he := W.finrank_quotient_add_finrank
      have hp : 0 < finrank K W := by
        let : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hW0
        exact Module.finrank_pos (R:=K) (M:=W)
      omega
    have hgσ := hgH.of_surjective σ.rangeRestrict σ.rangeRestrict_surjective
    have hgτ := hgH.of_surjective τ.rangeRestrict τ.rangeRestrict_surjective
    obtain ⟨P,hPi,hPs⟩ := ih _ hWrank W σ.range rfl σ.range.subtype Subtype.val_injective d hgσ
    obtain ⟨Q,hQi,hQs⟩ := ih _ hQrank (V ⧸ W) τ.range rfl τ.range.subtype Subtype.val_injective d hgτ
    let := hPi
    let := hQi
    let := hPs
    let := hQs
    let J := P.comap σ.rangeRestrict ⊓ Q.comap τ.rangeRestrict
    let : (P.comap σ.rangeRestrict).FiniteIndex :=
      finiteIndex_comap_surjective σ.rangeRestrict σ.rangeRestrict_surjective P
    let : (Q.comap τ.rangeRestrict).FiniteIndex :=
      finiteIndex_comap_surjective τ.rangeRestrict τ.rangeRestrict_surjective Q
    let : J.FiniteIndex := inferInstance
    have hWJ (j : J) : W.map (ρH j.val).toLinearMap=W := hW j.val
    have hsJ : subspaceRepresentation (ρH.comp J.subtype) W hWJ=σ.comp J.subtype := by
      ext j w; rfl
    have htJ : quotientRepresentation (ρH.comp J.subtype) W hWJ=τ.comp J.subtype := by
      ext j v
      induction v using Submodule.Quotient.induction_on
      rfl
    let : Group.IsSolvable (subspaceRepresentation (ρH.comp J.subtype) W hWJ).range :=
      hsJ.symm ▸ solvable_restricted_range σ P J inf_le_left
    let : Group.IsSolvable (quotientRepresentation (ρH.comp J.subtype) W hWJ).range :=
      htJ.symm ▸ solvable_restricted_range τ Q J inf_le_right
    let : Group.IsSolvable J := solvable_of_subspace_quotient (ρH.comp J.subtype)
      ((hρ.comp Subtype.val_injective).comp Subtype.val_injective) W hWJ
    let L := J.map H.subtype
    let e := J.equivMapOfInjective H.subtype Subtype.val_injective
    have hLi : L.FiniteIndex := by
      constructor
      rw [Subgroup.index_map_subtype]
      exact mul_ne_zero (inferInstance : J.FiniteIndex).index_ne_zero hHi.index_ne_zero
    exact ⟨L,hLi,Group.isSolvable_of_surjective (f:=e.toMonoidHom) e.surjective⟩

lemma virtually_solvable_linear (K V G : Type) [Field K] [CharZero K]
    [Countable K] [IsAlgClosed K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [Group G] [DecidableEq G] (ρ : G →* (V ≃ₗ[K] V)) (hρ : Injective ρ)
    {degree : ℕ} (hg : SparseGrowth.HasPolynomialDegree G degree) :
    ∃ H : Subgroup G, H.FiniteIndex ∧ Group.IsSolvable H :=
  virtually_solvable_linear_of_rank K (finrank K V) V G rfl ρ hρ degree hg

end CriticalPercolation.LinearGrowth
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_LinearGroups_RealVirtualSolvability
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function Module
open scoped Classical Cardinal

namespace CriticalPercolation.LinearGrowth

lemma countable_finiteType_int (D : Type) [CommRing D] [Algebra ℤ D]
    [Algebra.FiniteType ℤ D] : Countable D := by
  obtain ⟨n,f,hf⟩ := (Algebra.FiniteType.iff_quotient_mvPolynomial).mp
    (inferInstance : Algebra.FiniteType ℤ D)
  let : Countable (MvPolynomial n ℤ) := by
    apply Function.Injective.countable (f := AddMonoidAlgebra.coeff)
    intro x y h
    cases x; cases y; cases h; rfl
  exact Function.Surjective.countable hf

lemma countable_fraction (D : Type) [CommRing D] [Countable D] : Countable (FractionRing D) := by
  apply Cardinal.mk_le_aleph0_iff.mp
  rw [Cardinal.mk_fractionRing]
  exact Cardinal.mk_le_aleph0

lemma countable_algebraicClosure (F : Type) [Field F] [Countable F] :
    Countable (AlgebraicClosure F) := by
  have h := Algebraic.countable F (AlgebraicClosure F)
  have he : {x : AlgebraicClosure F | IsAlgebraic F x}=Set.univ :=
    Set.eq_univ_of_forall (fun _ => Algebra.IsAlgebraic.isAlgebraic _)
  rw [he] at h
  exact Set.countable_univ_iff.mp h

lemma matrixRepresentation_injective {K G n : Type} [Field K] [Group G]
    [Fintype n] [DecidableEq n] (ρ : G →* GL n K) (hρ : Injective ρ) :
    Injective (matrixRepresentation ρ) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv K (n → K)).injective.comp
    (Matrix.GeneralLinearGroup.toLin.injective.comp hρ)

lemma virtually_solvable_real_matrix {G n : Type} [Group G] [DecidableEq G]
    [Fintype n] [DecidableEq n] (ρ : G →* GL n ℝ) (hρ : Injective ρ)
    {degree : ℕ} (hg : SparseGrowth.HasPolynomialDegree G degree) :
    ∃ H : Subgroup G, H.FiniteIndex ∧ Group.IsSolvable H := by
  let := hg.fg
  obtain ⟨D,hD,hm⟩ := exists_finiteType_matrix_ring ρ
  let := hD
  let : Countable D := countable_finiteType_int D
  let F := FractionRing D
  let K := AlgebraicClosure F
  let : Countable F := countable_fraction D
  let : Countable K := countable_algebraicClosure F
  let f : D →+* K := (algebraMap F K).comp (algebraMap D F)
  have hf : Injective f := (algebraMap F K).injective.comp (IsFractionRing.injective D F)
  let σ := liftMatrixGroup ρ D hm
  let τ := (Matrix.GeneralLinearGroup.map f).comp σ
  have hσ : Injective σ := liftMatrixGroup_injective ρ D hm hρ
  have hτ : Injective τ := by
    intro x y h
    apply hσ
    apply Units.ext
    apply Matrix.ext
    intro i j
    apply hf
    exact congrArg (fun M : GL n K => M i j) h
  exact virtually_solvable_linear K (n → K) G (matrixRepresentation τ)
    (matrixRepresentation_injective τ hτ) hg

end CriticalPercolation.LinearGrowth

namespace CriticalPercolation.LinearGrowth
lemma virtually_solvable_real_linear_general {G V : Type*} [Group G] [DecidableEq G]
    [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (ρ : G →* (V ≃ₗ[ℝ] V)) (hρ : Injective ρ)
    {degree : ℕ} (hg : SparseGrowth.HasPolynomialDegree G degree) :
    ∃ H : Subgroup G, H.FiniteIndex ∧ Group.IsSolvable H := by
  let τ := (linearMatrixEquiv (K:=ℝ) (V:=V)).toMonoidHom.comp ρ
  have hτ : Injective τ := linearMatrixEquiv.injective.comp hρ
  have hgτ := hg.of_surjective τ.rangeRestrict τ.rangeRestrict_surjective
  obtain ⟨P,hPi,hPs⟩ := virtually_solvable_real_matrix τ.range.subtype Subtype.val_injective hgτ
  let := hPi
  let := hPs
  let H := P.comap τ.rangeRestrict
  have hHi : H.FiniteIndex := finiteIndex_comap_surjective τ.rangeRestrict τ.rangeRestrict_surjective P
  let ψ : H →* P := (τ.rangeRestrict.comp H.subtype).codRestrict P (fun h => h.property)
  have hψ : Injective ψ := by
    intro x y he
    apply Subtype.ext
    apply hτ
    exact congrArg (fun z : P => (z.val : GL (Fin (finrank ℝ V)) ℝ)) he
  exact ⟨H,hHi,Group.isSolvable_of_isSolvable_injective hψ⟩
end CriticalPercolation.LinearGrowth
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Harmonic_WeakGromovHarmonic
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical

namespace CriticalPercolation.SparseGrowth

lemma infinite_finiteIndex_subgroup {A : Type*} [Group A] [Infinite A]
    (H : Subgroup A) [H.FiniteIndex] : Infinite H := by
  rcases finite_or_infinite H with hf | hi
  · let := hf
    let : Finite A := H.finite_iff_finite_and_finiteIndex.mpr ⟨hf,inferInstance⟩
    exact False.elim (_root_.not_finite A)
  · exact hi

lemma indicability_of_finiteIndex {A : Type*} [Group A] (P : Subgroup A) [P.FiniteIndex]
    (hp : ∃ Q : Subgroup P, Q.FiniteIndex ∧ ∃ f : Q →* Multiplicative ℤ, Surjective f) :
    ∃ H : Subgroup A, H.FiniteIndex ∧ ∃ f : H →* Multiplicative ℤ, Surjective f := by
  obtain ⟨Q,hQi,f,hf⟩ := hp
  let H := Q.map P.subtype
  let e := Q.equivMapOfInjective P.subtype Subtype.val_injective
  have hHi : H.FiniteIndex := by
    constructor
    rw [Subgroup.index_map_subtype]
    exact mul_ne_zero hQi.index_ne_zero (inferInstance : P.FiniteIndex).index_ne_zero
  exact ⟨H,hHi,f.comp e.symm.toMonoidHom,hf.comp e.symm.surjective⟩

lemma indicability_of_surjective {A B : Type*} [Group A] [Group B]
    (f : A →* B) (hf : Surjective f)
    (hb : ∃ P : Subgroup B, P.FiniteIndex ∧ ∃ q : P →* Multiplicative ℤ, Surjective q) :
    ∃ H : Subgroup A, H.FiniteIndex ∧ ∃ q : H →* Multiplicative ℤ, Surjective q := by
  obtain ⟨P,hPi,q,hq⟩ := hb
  let := hPi
  let H := P.comap f
  let ψ : H →* P := (f.comp H.subtype).codRestrict P (fun h => h.property)
  have hψ : Surjective ψ := by
    intro p
    obtain ⟨a,ha⟩ := hf p.val
    refine ⟨⟨a,?_⟩,Subtype.ext ha⟩
    change f a∈P
    rw [ha]
    exact p.property
  exact ⟨H,LinearGrowth.finiteIndex_comap_surjective f hf P,q.comp ψ,hq.comp hψ⟩

lemma HasPolynomialDegree.linear_virtually_indicable {A : Type*} [Group A] [DecidableEq A]
    {d : ℕ} (hg : HasPolynomialDegree A d) [Infinite A] :
    ∃ H : Subgroup A, H.FiniteIndex ∧ ∃ f : H →* Multiplicative ℤ, Surjective f := by
  let : DecidableEq A := Classical.decEq A
  obtain ⟨S,h1,hi,hgen,hgS⟩ := (hasPolynomialDegree_iff d).mp hg
  let W : HarmonicAnalysis.WordGeometry A := ⟨S,h1,hi,hgen⟩
  obtain ⟨V,hV,hM,hfd,ρ,hρ⟩ := W.exists_infinite_finiteDimensional_linear_image_bs d hgS
  let := hV
  let := hM
  let := hfd
  have hgR := hg.of_surjective ρ.rangeRestrict ρ.rangeRestrict_surjective
  let : Infinite ρ.range := hρ.to_subtype
  obtain ⟨P,hPi,hPs⟩ := LinearGrowth.virtually_solvable_real_linear_general
    ρ.range.subtype Subtype.val_injective hgR
  let := hPi
  let := hPs
  let : Infinite P := infinite_finiteIndex_subgroup P
  apply indicability_of_surjective ρ.rangeRestrict ρ.rangeRestrict_surjective
  apply indicability_of_finiteIndex P
  exact (hgR.finiteIndex_subgroup P).virtually_indicable

universe u

theorem sparse_polynomial_virtuallyNilpotent (d : ℕ) :
    ∀ (A : Type u) [Group A] [DecidableEq A],
      HasPolynomialDegree A d → Group.IsVirtuallyNilpotent A := by
  induction d with
  | zero =>
    intro A _ _ hg
    let : Finite A := hg.finite
    exact virtuallyNilpotent_of_finite
  | succ d ih =>
    intro A _ _ hg
    rcases finite_or_infinite A with hf | hi
    · let := hf
      exact virtuallyNilpotent_of_finite
    let := hi
    exact virtuallyNilpotent_of_indicability_degree_step d ih A hg hg.linear_virtually_indicable

end CriticalPercolation.SparseGrowth
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Classification_DiscreteWeakGromovBridge
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function Topology
open scoped Classical Pointwise

namespace CriticalPercolation.CompactQuotient
lemma virtuallyNilpotent_of_sparse_word_growth_bs_oai {A : Type*} [Group A]
    (hg : HasSparsePolynomialWordGrowth A) : Group.IsVirtuallyNilpotent A := by
  obtain ⟨S,hSf,h1,hi,hgen,d,hg⟩ := hg
  exact SparseGrowth.sparse_polynomial_virtuallyNilpotent d A
    ⟨S,hSf,h1,hi,hgen,1,by simpa only [one_mul] using hg⟩
end CriticalPercolation.CompactQuotient

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.CriticalPercolation.CompactQuotient.virtuallyNilpotent_of_sparse_word_growth_bs_oai.{u_1} := @OAI.CriticalPercolation.CompactQuotient.virtuallyNilpotent_of_sparse_word_growth_bs_oai.{u_1}
