-- Prove2me | solution 1 for OAI.PolycyclicRecognition.dekimpeLatticeRealizationInput
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-02T23:57:42.350731+00:00
-- url     : https://prove2.me/submissions/e30bb856-d705-461c-ac4d-9104dde1eb6a

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_PolycyclicRecognition
import Definitions.Def_OAIQ093D017
import Theorems.Thm_OAI_PolycyclicRecognition_nilpotent_by_abelian_uniform_lattice

section
-- module Solutions.OAIQ093_PR.CriticalPercolation_Nilpotent_CentralCommutatorGeneration
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
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
-- module Solutions.OAIQ093_PR.CriticalPercolation_Nilpotent_CentralCommutatorQuotient
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
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
-- module Solutions.OAIQ093_PR.CriticalPercolation_Nilpotent_FGExtensions
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
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
-- module Solutions.OAIQ093_PR.CriticalPercolation_Nilpotent_LowerCentralFG
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
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
-- module Solutions.OAIQ093_PR.CriticalPercolation_Nilpotent_NilpotentSubgroupFG
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
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
-- module Solutions.OAIQ093_PR.CyclicSeries_Length
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cyclic subnormal series and their minimum lengths in finite p-groups. -/

namespace ChromaticCyclic

namespace CyclicStep
variable {G : Type*} [Group G]

protected theorem bot (K : Subgroup G) [IsCyclic K] : CyclicStep ⊥ K := by
  refine ⟨bot_le, Subgroup.normal_subgroupOf, ?_⟩
  exact isCyclic_of_surjective (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)

end CyclicStep

end ChromaticCyclic

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_Polycyclic
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Compatibility with OpenAI's Mathlib (d13f23b): its instance that `comap` keeps a finite index
(`GroupTheory/Index.lean`). -/

theorem Subgroup.FiniteIndex.map_of_surjective {G G' : Type*} [Group G] [Group G'] {f : G →* G'}
    (H : Subgroup G) [H.FiniteIndex] (hf : Function.Surjective f) : (H.map f).FiniteIndex where
  index_ne_zero := ne_zero_of_dvd_ne_zero Subgroup.FiniteIndex.index_ne_zero (H.index_map_dvd hf)

namespace OAI

/-!
# Polycyclic and virtually polycyclic groups

We use the existing concrete cyclic subnormal series, including normality and
cyclicity of each quotient. Neither polycyclicity nor virtual polycyclicity is
an unspecified property parameter.
-/

namespace PolycyclicRecognition

open ChromaticCyclic

variable (G : Type*) [Group G]

variable {G} {H : Type*} [Group H]

/-- The length-zero series proves polycyclicity of the trivial group. -/
theorem isPolycyclic_of_subsingleton [Subsingleton G] : IsPolycyclic G := by
  refine ⟨0, ?_⟩
  have htop : (⊥ : Subgroup G) = ⊤ := Subsingleton.elim _ _
  simpa only [htop] using (⟨CyclicSeries.refl (⊥ : Subgroup G)⟩ :
    Nonempty (CyclicSeries (⊥ : Subgroup G) ⊥ 0))

/-- Polycyclicity descends to a surjective image by mapping a cyclic series. -/
theorem IsPolycyclic.of_surjective (hG : IsPolycyclic G)
    (f : G →* H) (hf : Function.Surjective f) : IsPolycyclic H := by
  obtain ⟨n, ⟨c⟩⟩ := hG
  refine ⟨n, ?_⟩
  have hc := c.map f
  rw [Subgroup.map_bot, Subgroup.map_top_of_surjective f hf] at hc
  exact ⟨hc⟩

/-- Subgroups of polycyclic groups are polycyclic, by pulling back the cyclic series. -/
theorem IsPolycyclic.of_injective (hG : IsPolycyclic G)
    (f : H →* G) (hf : Function.Injective f) : IsPolycyclic H := by
  obtain ⟨n, ⟨c⟩⟩ := hG
  refine ⟨n, ?_⟩
  have hc := c.comap f
  rw [MonoidHom.comap_bot, (MonoidHom.ker_eq_bot_iff f).mpr hf,
    Subgroup.comap_top] at hc
  exact ⟨hc⟩

/-- A polycyclic group is virtually polycyclic, using the whole group. -/
theorem IsPolycyclic.isVirtuallyPolycyclic (hG : IsPolycyclic G) :
    IsVirtuallyPolycyclic G := by
  refine ⟨⊤, inferInstance, ?_⟩
  exact hG.of_injective (⊤ : Subgroup G).subtype Subtype.val_injective

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_Extensions
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Cyclic factors and extensions of polycyclic groups

These are elementary consequences of concrete cyclic subnormal series. They
are used in the nilpotent branch of the recognition argument.
-/

namespace PolycyclicRecognition

open ChromaticCyclic

variable {G : Type*} [Group G]

/-- Polycyclic groups are closed under group extensions, by concatenating the
series in the kernel with the lifted series in the quotient. -/
theorem isPolycyclic_of_normal_subgroup (N : Subgroup G) [N.Normal]
    (hN : IsPolycyclic N) (hQ : IsPolycyclic (G ⧸ N)) : IsPolycyclic G := by
  obtain ⟨n, ⟨c⟩⟩ := hN
  obtain ⟨m, ⟨d⟩⟩ := hQ
  have cG := c.map N.subtype
  rw [Subgroup.map_bot, ← MonoidHom.range_eq_map, N.range_subtype] at cG
  have dG := d.comap (QuotientGroup.mk' N)
  rw [MonoidHom.comap_bot, QuotientGroup.ker_mk', Subgroup.comap_top] at dG
  exact ⟨n + m, ⟨cG.append dG⟩⟩

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_Abelian
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finitely generated abelian groups are polycyclic

Adjoining one generator to a subgroup of an abelian group gives a cyclic
quotient. Iterating this observation constructs an actual finite cyclic
subnormal series.
-/

namespace PolycyclicRecognition

open ChromaticCyclic

variable {G : Type*} [CommGroup G]

/-- The quotient obtained by adjoining one generator to an abelian subgroup
is cyclic. -/
theorem cyclicStep_closure_insert (S : Set G) (a : G) :
    CyclicStep (Subgroup.closure S) (Subgroup.closure (insert a S)) := by
  let H := Subgroup.closure S
  let K := Subgroup.closure (insert a S)
  have hHK : H ≤ K := Subgroup.closure_mono (Set.subset_insert a S)
  refine ⟨hHK, inferInstance, ?_⟩
  let q := QuotientGroup.mk' (H.subgroupOf K)
  let aK : K := ⟨a, Subgroup.subset_closure (Set.mem_insert a S)⟩
  apply isCyclic_iff_exists_zpowers_eq_top.mpr
  refine ⟨q aK, top_unique ?_⟩
  intro y _
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (H.subgroupOf K) y
  change q x ∈ Subgroup.zpowers (q aK)
  have hx : ∀ (g : G) (hg : g ∈ K), q ⟨g, hg⟩ ∈ Subgroup.zpowers (q aK) := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem g hg =>
      rcases Set.mem_insert_iff.mp hg with rfl | hg
      · exact Subgroup.mem_zpowers (q aK)
      · have hq : q ⟨g, Subgroup.subset_closure (Set.mem_insert_of_mem a hg)⟩ = 1 := by
          apply (QuotientGroup.eq_one_iff _).mpr
          exact Subgroup.subset_closure hg
        rw [hq]
        exact (Subgroup.zpowers (q aK)).one_mem
    | one =>
      change q 1 ∈ _
      rw [map_one]
      exact (Subgroup.zpowers (q aK)).one_mem
    | mul g h hg hh ihg ihh =>
      change q (⟨g, hg⟩ * ⟨h, hh⟩) ∈ _
      rw [map_mul]
      exact (Subgroup.zpowers (q aK)).mul_mem ihg ihh
    | inv g hg ih =>
      change q (⟨g, hg⟩⁻¹) ∈ _
      rw [map_inv]
      exact (Subgroup.zpowers (q aK)).inv_mem ih
  exact hx x x.property

/-- A finite generating set in an abelian group explicitly yields a finite
cyclic series from the trivial subgroup to its closure. -/
theorem exists_cyclicSeries_closure_finset (S : Finset G) :
    ∃ n : ℕ, Nonempty (CyclicSeries (⊥ : Subgroup G) (Subgroup.closure (S : Set G)) n) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨0, ?_⟩
    simpa using (⟨CyclicSeries.refl (⊥ : Subgroup G)⟩ :
      Nonempty (CyclicSeries (⊥ : Subgroup G) ⊥ 0))
  | @insert a S ha ih =>
    obtain ⟨n, ⟨c⟩⟩ := ih
    refine ⟨n + 1, ?_⟩
    have d := CyclicSeries.cons (cyclicStep_closure_insert (S : Set G) a)
      (CyclicSeries.refl (Subgroup.closure (insert a (S : Set G))))
    simpa using (⟨c.append d⟩ : Nonempty (CyclicSeries (⊥ : Subgroup G)
      (Subgroup.closure (insert a (S : Set G))) (n + 1)))

/-- Every finitely generated abelian group is polycyclic. -/
theorem isPolycyclic_of_finitelyGenerated_commGroup (G : Type*) [CommGroup G]
    [Group.FG G] : IsPolycyclic G := by
  obtain ⟨S, hS⟩ := Group.fg_def.mp (inferInstance : Group.FG G)
  obtain ⟨n, h⟩ := exists_cyclicSeries_closure_finset S
  exact ⟨n, hS ▸ h⟩

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_Solvable
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

namespace OAI

/-!
# Solvable groups with finitely generated subgroups

Induction on the derived series proves that a solvable group whose subgroups
are all finitely generated has a finite cyclic subnormal series. This is the
algebraic step used for finitely generated nilpotent groups.
-/

namespace PolycyclicRecognition

open scoped IsMulCommutative

variable {G : Type*} [Group G]

/-- Restricting to a subgroup preserves finite generation of all subgroups. -/
theorem subgroups_fg_of_subgroups_fg (hfg : ∀ J : Subgroup G, Group.FG J)
    (H : Subgroup G) : ∀ J : Subgroup H, Group.FG J := by
  intro J
  let e := J.equivMapOfInjective H.subtype Subtype.val_injective
  let := hfg (J.map H.subtype)
  exact Group.fg_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective

/-- The derived series of the commutator subgroup maps to the shifted
derived series of the ambient group. -/
theorem map_derivedSeries_commutator (n : ℕ) :
    (derivedSeries (commutator G) n).map (commutator G).subtype =
      derivedSeries G (n + 1) := by
  induction n with
  | zero =>
    change (⊤ : Subgroup (commutator G)).map (commutator G).subtype = commutator G
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  | succ n ih =>
    rw [derivedSeries_succ, Subgroup.map_commutator, ih]
    rfl

/-- A trivial term in the derived series and finite generation of every
subgroup suffice to construct a finite cyclic series. -/
theorem isPolycyclic_of_derivedSeries_eq_bot (n : ℕ) :
    ∀ (G : Type*) [Group G], derivedSeries G n = ⊥ →
      (∀ J : Subgroup G, Group.FG J) → IsPolycyclic G := by
  induction n with
  | zero =>
    intro G _ hn _
    have hsub : Subsingleton G := by
      constructor
      intro x y
      have hx : x = 1 := by
        have h : x ∈ derivedSeries G 0 := Subgroup.mem_top x
        simpa only [hn, Subgroup.mem_bot] using h
      have hy : y = 1 := by
        have h : y ∈ derivedSeries G 0 := Subgroup.mem_top y
        simpa only [hn, Subgroup.mem_bot] using h
      exact hx.trans hy.symm
    exact isPolycyclic_of_subsingleton
  | succ n ih =>
    intro G _ hn hfg
    let N := commutator G
    have hnN : derivedSeries N n = ⊥ := by
      apply Subgroup.map_injective (f := N.subtype) Subtype.val_injective
      rw [Subgroup.map_bot, map_derivedSeries_commutator, hn]
    have hN : IsPolycyclic N := ih N hnN (subgroups_fg_of_subgroups_fg hfg N)
    let : Group.FG G := Group.fg_def.mpr
      ((Group.fg_iff_subgroup_fg (⊤ : Subgroup G)).mp (hfg ⊤))
    have hQ : IsPolycyclic (G ⧸ N) := by
      have hFG : Group.FG (G ⧸ N) := inferInstance
      -- `G ⧸ commutator G` is `Abelianization G` by definition; ours has its `CommGroup` only there
      exact @isPolycyclic_of_finitelyGenerated_commGroup (G ⧸ N)
        (inferInstanceAs (CommGroup (Abelianization G))) hFG
    exact isPolycyclic_of_normal_subgroup N hN hQ

/-- A solvable group with all subgroups finitely generated is polycyclic. -/
theorem isPolycyclic_of_solvable_subgroups_fg [Group.IsSolvable G]
    (hfg : ∀ J : Subgroup G, Group.FG J) : IsPolycyclic G := by
  obtain ⟨n, hn⟩ := Group.IsSolvable.solvable (G := G)
  exact isPolycyclic_of_derivedSeries_eq_bot n G hn hfg

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_Nilpotent
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The nilpotent conclusion in recognition

Finitely generated nilpotent groups are polycyclic. Consequently a finitely
generated virtually nilpotent group is virtually polycyclic, by finite
generation of the finite-index nilpotent subgroup.
-/

namespace PolycyclicRecognition

variable (G : Type*) [Group G] [Group.FG G]

/-- Finite generation and nilpotence yield an actual finite cyclic subnormal series. -/
theorem isPolycyclic_of_finitelyGenerated_nilpotent [Group.IsNilpotent G] :
    IsPolycyclic G := by
  apply isPolycyclic_of_solvable_subgroups_fg
  exact CriticalPercolation.nilpotent_subgroup_fg G

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_CohomologicalFiniteness
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.cyclicTopHomologyInjection_mono _root_.OAI.PolycyclicRecognition.finiteResolution_single_supported _root_.OAI.PolycyclicRecognition.finiteTruncationAugmentation_quasiIso _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The finiteness and duality properties used in recognition

These are concrete properties of the trivial integral representation and its
projective resolutions. A finite classifying space supplies a finite resolution
of this kind, but no predicate for an unspecified classifying space is used.
The cohomology condition includes the possibly nontrivial orientation action:
only the underlying integral module in top degree is required to be `ℤ`.
-/

namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits
open scoped MonoidAlgebra

variable (G : Type) [Group G]

theorem HasFiniteProjectiveResolution.typeFPInfinity
    (h : HasFiniteProjectiveResolution G) : TypeFPInfinity G := by
  obtain ⟨P, d, hfg, _⟩ := h
  exact fun n => ⟨P, fun i _ => hfg i⟩

theorem IsIntegralPoincareDualityGroup.typeFPInfinity {n : ℕ}
    (h : IsIntegralPoincareDualityGroup G n) : TypeFPInfinity G :=
  h.1.typeFPInfinity G

/-- The bounded resolution in the definition really implies finite
cohomological dimension: every higher Ext cocycle has zero source. -/
theorem HasFiniteProjectiveResolution.finiteCohomologicalDimension
    (h : HasFiniteProjectiveResolution G) :
    HasFiniteIntegralCohomologicalDimension G := by
  obtain ⟨P, d, _, hz⟩ := h
  let := HasExt.standard (Rep ℤ G)
  refine ⟨d, HasProjectiveDimensionLT.mk ?_⟩
  intro i hi Y e
  obtain ⟨f, hf, rfl⟩ := P.extMk_surjective e (i + 1) rfl
  have hzero : f = 0 := (hz i (Nat.lt_of_succ_le hi)).eq_of_src f 0
  subst f
  exact P.extMk_zero (i + 1) rfl

theorem IsIntegralPoincareDualityGroup.finiteCohomologicalDimension {n : ℕ}
    (h : IsIntegralPoincareDualityGroup G n) :
    HasFiniteIntegralCohomologicalDimension G :=
  h.1.finiteCohomologicalDimension G

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_FiniteIntegralRepresentations
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite generation in the concrete integral resolutions -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits
open scoped MonoidAlgebra

variable (G : Type) [Group G]

theorem integralRepresentationFinite_of_finite (A : Rep ℤ G)
    (hA : letI : Module ℤ A := A.hV2; Module.Finite ℤ A) :
    IntegralRepresentationFinite G A := by
  let module : Module ℤ A := A.hV2
  let finite : Module.Finite ℤ A := hA
  let moduleZ : Module ℤ A.ρ.asModule := A.ρ.instModuleAsModule
  let finiteModule : Module.Finite ℤ A.ρ.asModule :=
    Module.Finite.equiv A.ρ.asModuleEquiv.symm
  exact Module.Finite.of_restrictScalars_finite ℤ ℤ[G] A.ρ.asModule

theorem integralRepresentationFinite_of_isZero (A : Rep ℤ G) (hA : IsZero A) :
    IntegralRepresentationFinite G A := by
  have ha (a : A) : a = 0 := by
    have hh : (𝟙 A : A ⟶ A) = 0 := hA.eq_of_src _ _
    exact congrArg (fun f : A ⟶ A => f.hom a) hh
  let sub : Subsingleton A := ⟨fun a b => (ha a).trans (ha b).symm⟩
  exact integralRepresentationFinite_of_finite G A (by
    let module : Module ℤ A := A.hV2
    infer_instance)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_FiniteRepresentationQuotients
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite generation of quotient representations

The top term in a truncated projective resolution is a quotient of its old
term. This bridge transfers finite generation through the actual group-ring map.
-/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
open scoped MonoidAlgebra
variable {G : Type} [Group G] {A B : Rep ℤ G}

theorem IntegralRepresentationFinite.of_epi (f : A ⟶ B) [Epi f]
    (hA : IntegralRepresentationFinite G A) : IntegralRepresentationFinite G B := by
  let : Module ℤ A := A.hV2
  let : Module ℤ B := B.hV2
  let fM : A.ρ.asModule →ₗ[ℤ[G]] B.ρ.asModule :=
    Representation.IntertwiningMap.equivLinearMapAsModule A.ρ B.ρ f.hom
  have hs : Function.Surjective fM := by
    intro b
    obtain ⟨a, ha⟩ := (Rep.epi_iff_surjective f).mp inferInstance (B.ρ.asModuleEquiv b)
    refine ⟨A.ρ.asModuleEquiv.symm a, ?_⟩
    apply B.ρ.asModuleEquiv.injective
    exact ha
  let : Module.Finite ℤ[G] A.ρ.asModule := hA
  exact Module.Finite.of_surjective fM hs

theorem IntegralRepresentationFinite.of_iso (e : A ≅ B)
    (hA : IntegralRepresentationFinite G A) : IntegralRepresentationFinite G B :=
  hA.of_epi e.hom

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_ProjectiveResolutionSyzygies
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.cyclicTopHomologyInjection_mono _root_.OAI.PolycyclicRecognition.finiteResolution_single_supported _root_.OAI.PolycyclicRecognition.finiteTruncationAugmentation_quasiIso _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Projectivity of the top syzygy

Successive quotient terms of a projective resolution fit into short exact
sequences. Finite projective dimension therefore makes the corresponding
top quotient projective; it remains finitely generated when the old term is.
-/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
variable {G : Type} [Group G] (P : ProjectiveResolution (trivialIntegral G))

theorem resolutionOpcycles_finite (d : ℕ)
    (h : IntegralRepresentationFinite G (P.complex.X d)) :
    IntegralRepresentationFinite G (P.complex.opcycles d) :=
  h.of_epi (P.complex.pOpcycles d)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_FiniteResolutionTruncation
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.cyclicTopHomologyInjection_mono _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A finite resolution from finite dimension and finite generation

Canonical truncation replaces the last term by its quotient syzygy. The
projectivity of that syzygy follows from finite projective dimension, while
finite generation passes to the quotient.
-/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits

variable {G : Type} [Group G] (P : ProjectiveResolution (trivialIntegral G)) (d : ℕ)

theorem finiteTruncation_finite
    (hfin : ∀ i, i ≤ d → IntegralRepresentationFinite G (P.complex.X i)) (i : ℕ) :
    IntegralRepresentationFinite G ((finiteTruncation P d).X i) := by
  rcases lt_trichotomy i d with hi | hi | hi
  · exact (hfin i (by omega)).of_iso (finiteTruncationIso P d i hi).symm
  · subst i
    exact (resolutionOpcycles_finite P d (hfin d le_rfl)).of_iso
      (finiteTruncationTopIso P d).symm
  · exact integralRepresentationFinite_of_isZero G _ (finiteTruncation_isZero P d i hi)

theorem finiteProjectiveResolution_of_finiteDimension_typeFP
    (hdim : HasFiniteIntegralCohomologicalDimension G) (hfp : TypeFPInfinity G) :
    HasFiniteProjectiveResolution G := by
  obtain ⟨d, hd⟩ := hdim
  obtain ⟨P, hP⟩ := hfp d
  have := hd
  exact ⟨finiteProjectiveResolution P d, d, finiteTruncation_finite P d hP,
    finiteTruncation_isZero P d⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_CyclicQuotientSequence
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.cyclicTopHomologyInjection_mono _root_.OAI.PolycyclicRecognition.finiteResolution_single_supported _root_.OAI.PolycyclicRecognition.finiteTruncationAugmentation_quasiIso _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The coefficient sequence for an infinite cyclic quotient

Inflating the cyclic augmentation sequence gives the two copies of the
quotient permutation module used in the cyclic-extension argument.
-/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits
open scoped MonoidAlgebra
attribute [local instance 2000] Rep.hV2

variable (Q : Type) [CommGroup Q]

variable {G : Type} [Group G]

theorem cohomologicalDimension_bound_of_cyclicQuotientModule [Infinite Q]
    (q : G →* Q) (z : Q) (hz : ∀ x, x ∈ Subgroup.zpowers z) (d : ℕ)
    [HasProjectiveDimensionLE (Rep.res q (Rep.leftRegular ℤ Q)) d] :
    HasProjectiveDimensionLE (trivialIntegral G) (d + 1) := by
  apply (cyclicQuotientSequence_shortExact Q q z hz).hasProjectiveDimensionLT_X₃ (d + 1)
  · change HasProjectiveDimensionLE (Rep.res q (Rep.leftRegular ℤ Q)) d
    infer_instance
  · change HasProjectiveDimensionLT (Rep.res q (Rep.leftRegular ℤ Q)) (d + 1 + 1)
    exact hasProjectiveDimensionLT_of_ge _ (d + 1) (d + 1 + 1) (by omega)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_NormalInductionDimension
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.cyclicTopHomologyInjection_mono _root_.OAI.PolycyclicRecognition.finiteResolution_single_supported _root_.OAI.PolycyclicRecognition.finiteTruncationAugmentation_quasiIso _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The cohomological dimension bound in an infinite cyclic extension -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2

variable {G : Type} [Group G]

theorem projectiveDimension_of_boundedResolution {A : Rep ℤ G}
    (P : ProjectiveResolution A) (d : ℕ)
    (hz : ∀ i, d < i → IsZero (P.complex.X i)) :
    HasProjectiveDimensionLE A d := by
  let := HasExt.standard (Rep ℤ G)
  refine HasProjectiveDimensionLT.mk ?_
  intro i hi Y e
  obtain ⟨f, hf, rfl⟩ := P.extMk_surjective e (i + 1) rfl
  have hzero : f = 0 := (hz i (Nat.lt_of_succ_le hi)).eq_of_src f 0
  subst f
  exact P.extMk_zero (i + 1) rfl

theorem normalInducedResolution_bounded (N : Subgroup G) [N.Normal]
    {A : Rep ℤ N} (P : ProjectiveResolution A) (d : ℕ)
    (hz : ∀ i, d < i → IsZero (P.complex.X i)) :
    ∀ i, d < i → IsZero ((normalInducedResolution ℤ N P).complex.X i) := by
  intro i hi
  exact (Rep.indFunctor ℤ N.subtype).map_isZero (hz i hi)

theorem quotientRegular_projectiveDimension (N : Subgroup G) [N.Normal]
    (P : ProjectiveResolution (trivialIntegral N)) (d : ℕ)
    (hz : ∀ i, d < i → IsZero (P.complex.X i)) :
    HasProjectiveDimensionLE (Rep.res (QuotientGroup.mk' N)
      (Rep.leftRegular ℤ (G ⧸ N))) d := by
  let := projectiveDimension_of_boundedResolution (normalInducedResolution ℤ N P) d
    (normalInducedResolution_bounded N P d hz)
  exact hasProjectiveDimensionLT_of_iso (inductionTrivialIso ℤ N) (d + 1)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_SubgroupResolution
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.cyclicTopHomologyInjection_mono _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Restricting integral resolutions to subgroups

Restriction is exact and preserves projectives. Truncating at a projective
syzygy before restriction gives the cohomological-dimension bound for every
subgroup, without a finite-generation hypothesis.
-/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits

variable {G : Type} [Group G] (H : Subgroup G)

/-- Integral cohomological dimension cannot increase on passing to a subgroup. -/
theorem subgroup_cohomologicalDimension_le (d : ℕ)
    [HasProjectiveDimensionLE (trivialIntegral G) d] :
    HasProjectiveDimensionLE (trivialIntegral H) d := by
  let P := finiteProjectiveResolution (Rep.standardResolution ℤ G) d
  apply projectiveDimension_of_boundedResolution (subgroupResolution H P) d
  intro i hi
  exact (Rep.resFunctor H.subtype).map_isZero
    (finiteTruncation_isZero (Rep.standardResolution ℤ G) d i hi)

theorem HasFiniteIntegralCohomologicalDimension.subgroup
    (hG : HasFiniteIntegralCohomologicalDimension G) :
    HasFiniteIntegralCohomologicalDimension H := by
  obtain ⟨d, hd⟩ := hG
  let := hd
  exact ⟨d, subgroup_cohomologicalDimension_le H d⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_FiniteDimensionCohomology
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.cyclicTopHomologyInjection_mono _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalizedGroupIdentityClass_comparison _root_.OAI.PolycyclicRecognition.rationalCoefficientInclusion_apply _root_.OAI.PolycyclicRecognition.resolutionStableSyzygyTransition_class _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Cohomology above the integral dimension bound

The bound applies to every coefficient representation. In particular the
periodic cohomology of a nontrivial finite cyclic group rules out finite
integral cohomological dimension.
-/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2100] Linear.homModule

variable {G : Type}

theorem groupCohomology_isZero_above_dimension [Group G] (d : ℕ)
    [HasProjectiveDimensionLE (trivialIntegral G) d]
    (A : Rep ℤ G) (i : ℕ) (hi : d < i) :
    IsZero (groupCohomology A i) := by
  let P := finiteProjectiveResolution (Rep.standardResolution ℤ G) d
  have hP : IsZero (P.complex.X i) :=
    finiteTruncation_isZero (Rep.standardResolution ℤ G) d i hi
  have hX : IsZero ((P.complex.linearYonedaObj ℤ A).X i) := by
    apply ModuleCat.isZero_iff_subsingleton.mpr
    exact ⟨fun f g => hP.eq_of_src f g⟩
  refine IsZero.of_iso ?_ (groupCohomologyIso A i P)
  apply HomologicalComplex.ExactAt.isZero_homology
  apply ShortComplex.exact_of_isZero_X₂
  simpa only [HomologicalComplex.shortComplexFunctor_obj_X₂] using hX

/-- A nonzero dualizing module cannot occur above the cohomological dimension. -/
theorem IsIntegralPoincareDualityGroup.dimension_le [Group G] {n d : ℕ}
    (hG : IsIntegralPoincareDualityGroup G n)
    [HasProjectiveDimensionLE (trivialIntegral G) d] : n ≤ d := by
  by_contra hnd
  have hz := groupCohomology_isZero_above_dimension d (Rep.leftRegular ℤ G) n
    (Nat.lt_of_not_ge hnd)
  obtain ⟨e⟩ := hG.2.2
  have hzero : IsZero (ModuleCat.of ℤ ℤ) := IsZero.of_iso hz e.symm
  have h01 : (0 : ℤ) = 1 := ModuleCat.isZero_iff_subsingleton.mp hzero |>.elim _ _
  exact zero_ne_one h01

section FiniteCyclic
variable [CommGroup G] [Fintype G] (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g)

include g hg in
/-- The class of one in positive even integral cohomology is nonzero whenever
there is more than one group element. -/
theorem finiteCyclic_even_cohomology_not_isZero (hG : 1 < Fintype.card G)
    (i : ℕ) [NeZero i] (hi : Even i) :
    ¬ IsZero (groupCohomology (trivialIntegral G) i) := by
  intro hz
  let x : LinearMap.ker (Rep.applyAsHom (trivialIntegral G) g -
      𝟙 (trivialIntegral G)).hom.toLinearMap := ⟨1, by change (1 : ℤ) - 1 = 0; omega⟩
  have hx : Rep.FiniteCyclicGroup.groupCohomologyπEven
      (trivialIntegral G) g hg i hi x = 0 := by
    exact ModuleCat.isZero_iff_subsingleton.mp hz |>.elim _ _
  obtain ⟨z, hz⟩ := (Rep.FiniteCyclicGroup.groupCohomologyπEven_eq_zero_iff
    (trivialIntegral G) g hg i hi x).mp hx
  have heq : (Fintype.card G : ℤ) * z = 1 := by
    simpa [Rep.norm, Representation.norm, trivialIntegral, x] using hz
  have hdvd : (Fintype.card G : ℤ) ∣ 1 := ⟨z, heq.symm⟩
  have hc : (Fintype.card G : ℤ) = 1 := (Int.eq_one_of_dvd_one (by omega) hdvd)
  omega

end FiniteCyclic
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_FiniteRestriction
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Restriction through a surjective group homomorphism preserves finite generation -/

noncomputable section
namespace PolycyclicRecognition

open Representation
open scoped MonoidAlgebra
attribute [local instance 2000] Rep.hV2

variable (k : Type) [CommRing k] {G J : Type} [Group G] [Group J]
  (f : J →* G) (A : Rep k G)

theorem restriction_span_of_span (hf : Function.Surjective f) (s : Set A.ρ.asModule)
    (hs : Submodule.span k[G] s = ⊤) :
    Submodule.span k[J] (restrictionModuleEquiv k f A '' s) = ⊤ := by
  let p := Submodule.span k[J] (restrictionModuleEquiv k f A '' s)
  let pR := Subrepresentation.ofSubmodule' p
  let q : Subrepresentation A.ρ :=
    { toSubmodule := pR.toSubmodule
      apply_mem_toSubmodule g a ha := by
        obtain ⟨j, rfl⟩ := hf g
        exact pR.apply_mem_toSubmodule j ha }
  have hsq : s ⊆ q.asSubmodule := by
    intro a ha
    change restrictionModuleEquiv k f A a ∈ p
    exact Submodule.subset_span ⟨a, ha, rfl⟩
  have hq : q.asSubmodule = ⊤ := by
    apply top_unique
    rw [← hs]
    exact Submodule.span_le.mpr hsq
  apply top_unique
  intro a _
  have ha : A.ρ.asModuleEquiv.symm ((Rep.res f A).ρ.asModuleEquiv a) ∈ q.asSubmodule := by
    rw [hq]
    trivial
  exact ha

theorem finite_restriction_of_surjective (hf : Function.Surjective f)
    [Module.Finite k[G] A.ρ.asModule] :
    Module.Finite k[J] (Rep.res f A).ρ.asModule := by
  classical
  obtain ⟨s, hsf, hs⟩ := Submodule.fg_def.mp (Module.Finite.fg_top :
    (⊤ : Submodule k[G] A.ρ.asModule).FG)
  exact Module.Finite.of_fg_top (Submodule.fg_def.mpr
    ⟨restrictionModuleEquiv k f A '' s, hsf.image _, restriction_span_of_span k f A hf s hs⟩)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_FiniteInduction
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite generation is preserved by subgroup induction -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory Representation
open scoped MonoidAlgebra
attribute [local instance 2000] Rep.hV2

variable (k : Type) [CommRing k] {G : Type} [Group G]
  (N : Subgroup G) (A : Rep k N)

theorem induction_span_of_span (s : Set A.ρ.asModule)
    (hs : Submodule.span k[N] s = ⊤) :
    Submodule.span k[G] (inductionAtOne k N A '' s) = ⊤ := by
  let p := Submodule.span k[G] (inductionAtOne k N A '' s)
  let pR := Subrepresentation.ofSubmodule' p
  let u : A ⟶ Rep.res N.subtype (Rep.ind N.subtype A) :=
    Rep.indResHomEquiv N.subtype A (Rep.ind N.subtype A) (𝟙 _)
  have hu (a : A) : u.hom a = IndV.mk N.subtype A.ρ 1 a := rfl
  let q : Subrepresentation A.ρ :=
    { toSubmodule := pR.toSubmodule.comap u.hom.toLinearMap
      apply_mem_toSubmodule n a ha := by
        change u.hom (A.ρ n a) ∈ pR.toSubmodule
        rw [Rep.hom_comm_apply]
        exact pR.apply_mem_toSubmodule (n : G) ha }
  have hsq : s ⊆ q.asSubmodule := by
    intro a ha
    change u.hom (A.ρ.asModuleEquiv a) ∈ pR.toSubmodule
    rw [hu]
    change inductionAtOne k N A a ∈ p
    exact Submodule.subset_span ⟨a, ha, rfl⟩
  have hq : q.asSubmodule = ⊤ := by
    apply top_unique
    rw [← hs]
    exact Submodule.span_le.mpr hsq
  have hone (a : A) : IndV.mk N.subtype A.ρ 1 a ∈ pR.toSubmodule := by
    have ha : A.ρ.asModuleEquiv.symm a ∈ q.asSubmodule := by rw [hq]; trivial
    change u.hom a ∈ pR.toSubmodule at ha
    rwa [hu] at ha
  have hmk (g : G) (a : A) : IndV.mk N.subtype A.ρ g a ∈ pR.toSubmodule := by
    simpa only [Rep.ind, Representation.ind_mk, inv_inv, one_mul] using
      pR.apply_mem_toSubmodule g⁻¹ (hone a)
  have hzero : pR.toSubmodule.mkQ = 0 := by
    apply IndV.hom_ext
    intro g
    apply LinearMap.ext
    intro a
    exact (Submodule.Quotient.mk_eq_zero _).mpr (hmk g a)
  apply top_unique
  intro a _
  have ha := LinearMap.congr_fun hzero ((Rep.ind N.subtype A).ρ.asModuleEquiv a)
  exact (Submodule.Quotient.mk_eq_zero _).mp ha

theorem finite_induction [Module.Finite k[N] A.ρ.asModule] :
    Module.Finite k[G] (Rep.ind N.subtype A).ρ.asModule := by
  classical
  obtain ⟨s, hsfin, hs⟩ := Submodule.fg_def.mp (Module.Finite.fg_top :
    (⊤ : Submodule k[N] A.ρ.asModule).FG)
  exact Module.Finite.of_fg_top (Submodule.fg_def.mpr
    ⟨inductionAtOne k N A '' s, hsfin.image _, induction_span_of_span k N A s hs⟩)

theorem integralRepresentationFinite_induction
    (A : Rep ℤ N) (hA : IntegralRepresentationFinite N A) :
    IntegralRepresentationFinite G (Rep.ind N.subtype A) := by
  let : Module.Finite ℤ[N] A.ρ.asModule := hA
  exact finite_induction ℤ N A

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_FiniteCofiber
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Projectivity and finiteness of the cyclic-extension mapping cone -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped MonoidAlgebra
attribute [local instance 2000] Rep.hV2

variable {G : Type} [Group G]

theorem integralRepresentationFinite_of_iso {A B : Rep ℤ G}
    (e : A ≅ B) (hA : IntegralRepresentationFinite G A) :
    IntegralRepresentationFinite G B := by
  let : Module.Finite ℤ[G] A.ρ.asModule := hA
  let e' : A.ρ.asModule ≃ₗ[ℤ[G]] B.ρ.asModule :=
    (Rep.toModuleMonoidAlgebra.mapIso e).toLinearEquiv
  exact Module.Finite.equiv e'

theorem integralRepresentationFinite_biprod (A B : Rep ℤ G)
    (hA : IntegralRepresentationFinite G A) (hB : IntegralRepresentationFinite G B) :
    IntegralRepresentationFinite G (A ⊞ B) := by
  let : Module.Finite ℤ[G] A.ρ.asModule := hA
  let : Module.Finite ℤ[G] B.ρ.asModule := hB
  let := preservesBinaryBiproduct_of_preservesBinaryProduct
    (Rep.toModuleMonoidAlgebra (k := ℤ) (G := G)) (X := A) (Y := B)
  have : Module.Finite ℤ[G] ((Rep.toModuleMonoidAlgebra.obj A) ×
      (Rep.toModuleMonoidAlgebra.obj B)) := by
    change Module.Finite ℤ[G] (A.ρ.asModule × B.ρ.asModule)
    infer_instance
  let e := Rep.toModuleMonoidAlgebra.mapBiprod A B ≪≫ ModuleCat.biprodIsoProd _ _
  exact Module.Finite.equiv e.symm.toLinearEquiv

variable {A B : Rep ℤ G} (P : ProjectiveResolution A) (Q : ProjectiveResolution B)
  (φ : P.complex ⟶ Q.complex)

theorem repCofiber_finite
    (hP : ∀ i, IntegralRepresentationFinite G (P.complex.X i))
    (hQ : ∀ i, IntegralRepresentationFinite G (Q.complex.X i)) (i : ℕ) :
    IntegralRepresentationFinite G ((repCofiber φ).X i) := by
  cases i with
  | zero =>
      exact integralRepresentationFinite_of_iso
        (homotopyCofiber.XIso φ 0 (by simp)).symm (hQ 0)
  | succ i =>
      exact integralRepresentationFinite_of_iso
        (homotopyCofiber.XIsoBiprod φ (i + 1) i (by rfl)).symm
        (integralRepresentationFinite_biprod _ _ (hP i) (hQ (i + 1)))

theorem repCofiber_bounded (d : ℕ)
    (hP : ∀ i, d < i → IsZero (P.complex.X i))
    (hQ : ∀ i, d < i → IsZero (Q.complex.X i)) :
    ∀ i, d + 1 < i → IsZero ((repCofiber φ).X i) := by
  intro i hi
  apply homotopyCofiber.isZero_X φ i (hQ i (by omega))
  intro j hj
  have : j + 1 = i := hj
  exact hP j (by omega)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_CyclicExtensionFiniteness
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.cyclicTopHomologyInjection_mono _root_.OAI.PolycyclicRecognition.finiteResolution_single_supported _root_.OAI.PolycyclicRecognition.finiteTruncationAugmentation_quasiIso _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite projective resolutions through infinite cyclic extensions -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2

variable {G : Type} [Group G]

theorem finiteProjectiveResolution_of_infiniteCyclicQuotient
    (N : Subgroup G) [N.Normal] [IsCyclic (G ⧸ N)] [Infinite (G ⧸ N)]
    (hN : HasFiniteProjectiveResolution N) : HasFiniteProjectiveResolution G := by
  let : CommGroup (G ⧸ N) := IsCyclic.commGroup
  obtain ⟨z, hz⟩ := IsCyclic.exists_generator (α := G ⧸ N)
  obtain ⟨P, d, hP, hd⟩ := hN
  let IP := normalInducedResolution ℤ N P
  let R := projectiveResolutionAlongIso IP (inductionTrivialIso ℤ N)
  have hR (i : ℕ) : IntegralRepresentationFinite G (R.complex.X i) :=
    integralRepresentationFinite_induction N (P.complex.X i) (hP i)
  have hRd (i : ℕ) (hi : d < i) : IsZero (R.complex.X i) :=
    normalInducedResolution_bounded N P d hd i hi
  let S := cyclicQuotientSequence (G ⧸ N) (QuotientGroup.mk' N) z
  have hS : S.ShortExact :=
    cyclicQuotientSequence_shortExact (G ⧸ N) (QuotientGroup.mk' N) z hz
  refine ⟨cokernelProjectiveResolution S R R hS, d + 1, ?_, ?_⟩
  · exact repCofiber_finite R R (cokernelResolutionMap S R R) hR hR
  · exact repCofiber_bounded R R (cokernelResolutionMap S R R) d hRd hRd

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_GroupIsoFiniteness
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.cyclicTopHomologyInjection_mono _root_.OAI.PolycyclicRecognition.finiteResolution_single_supported _root_.OAI.PolycyclicRecognition.finiteTruncationAugmentation_quasiIso _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite projective resolutions transported through a group isomorphism -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits
open scoped MonoidAlgebra
attribute [local instance 2000] Rep.hV2

variable {G J : Type} [Group G] [Group J]

theorem HasFiniteProjectiveResolution.of_equiv
    (hG : HasFiniteProjectiveResolution G) (e : G ≃* J) :
    HasFiniteProjectiveResolution J := by
  obtain ⟨P, d, hP, hd⟩ := hG
  let F : Rep ℤ G ⥤ Rep ℤ J := Rep.resFunctor e.symm.toMonoidHom
  let : F.IsEquivalence := (restrictionEquivalence ℤ e.symm).isEquivalence_functor
  let Q := F.mapProjectiveResolution P
  refine ⟨Q, d, ?_, ?_⟩
  · intro i
    let : Module.Finite ℤ[G] (P.complex.X i).ρ.asModule := hP i
    exact finite_restriction_of_surjective ℤ e.symm.toMonoidHom (P.complex.X i) e.symm.surjective
  · intro i hi
    exact F.map_isZero (hd i hi)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_GroupIsoDuality
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Transport of regular-module cohomology and duality through group isomorphisms -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits
open scoped MonoidAlgebra
attribute [local instance 2000] Rep.hV2

variable (k : Type) [CommRing k] {G J : Type} [Group G] [Group J]

theorem IsIntegralPoincareDualityGroup.of_equiv {n : ℕ}
    (hG : IsIntegralPoincareDualityGroup G n) (e : G ≃* J) :
    IsIntegralPoincareDualityGroup J n := by
  refine ⟨hG.1.of_equiv e, ?_, ?_⟩
  · intro i hi
    exact IsZero.of_iso (hG.2.1 i hi) (regularCohomologyGroupIso ℤ e i).symm
  · obtain ⟨u⟩ := hG.2.2
    exact ⟨(regularCohomologyGroupIso ℤ e n).symm ≪≫ u⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_CochainSuccessor
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The successor shift of a nonnegative cochain complex -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits HomologicalComplex

variable {k : Type} [CommRing k]

theorem cochainSuccessor_homology_zero (C : CochainComplex (ModuleCat k) ℕ) :
    IsZero ((cochainSuccessor C).homology 0) :=
  (negativeCochainComplex C).extend_exactAt cochainSuccessorEmbedding 0 (by
    intro i
    simp [cochainSuccessorEmbedding]) |>.isZero_homology

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_CofiberCohomology
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.repCofiber_projective _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Cohomology of a cone whose induced map is injective -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits HomologicalComplex
attribute [local instance 2000] Rep.hV2
attribute [local instance 2000] Rep.instLinear
attribute [local instance 2100] Linear.homModule

variable {k G : Type} [CommRing k] [Group G]
  {P Q : ChainComplex (Rep k G) ℕ} (φ : P ⟶ Q) (A : Rep k G)

theorem cofiberCochain_homology_zero
    [Mono (HomologicalComplex.homologyMap (repCochainPrecomp k φ A) 0)] :
    IsZero ((ChainComplex.linearYonedaObj (repCofiber φ) k A).homology 0) := by
  let := cofiberCochain_homologyInclusion_epi φ A 0
  let := ModuleCat.subsingleton_of_isZero
    (cochainSuccessor_homology_zero (P.linearYonedaObj k A))
  apply ModuleCat.isZero_of_iff_subsingleton.mpr
  apply subsingleton_of_forall_eq (0 : (ChainComplex.linearYonedaObj (repCofiber φ) k A).homology 0)
  intro y
  obtain ⟨x, rfl⟩ := (ModuleCat.epi_iff_surjective
    (HomologicalComplex.homologyMap (cofiberCochainInclusion φ A) 0)).mp inferInstance y
  have hx : x = 0 := Subsingleton.elim _ _
  rw [hx, map_zero]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_IntegerExtensionDuality
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.cyclicTopHomologyInjection_mono _root_.OAI.PolycyclicRecognition.finiteResolution_single_supported _root_.OAI.PolycyclicRecognition.finiteTruncationAugmentation_quasiIso _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The cohomological dimension shift for an infinite cyclic extension -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped MonoidAlgebra
attribute [local instance 2000] Rep.hV2

variable {G : Type} [Group G] (q : G →* Multiplicative ℤ)
  (t : G) (ht : q t = Multiplicative.ofAdd 1)

section Cyclic
variable [IsCyclic (G ⧸ q.ker)] [Infinite (G ⧸ q.ker)]

variable (P : ProjectiveResolution (Rep.trivial ℤ q.ker ℤ))

variable (hP : ∀ i, Module.Finite ℤ[q.ker] (P.complex.X i).ρ.asModule)

attribute [local instance] OAI.PolycyclicRecognition.instCommGroupQuotientSubgroupKerMultiplicativeInt_solutions
include q t ht P hP in
theorem integerExtensionCohomology_zero :
    IsZero (groupCohomology (Rep.leftRegular ℤ G) 0) := by
  let := integerExtensionMap_homology_mono q t ht P hP 0
  exact IsZero.of_iso (cofiberCochain_homology_zero (integerExtensionMap q t P)
    (Rep.leftRegular ℤ G))
      (groupCohomologyIso (Rep.leftRegular ℤ G) 0 (integerExtensionResolution q t ht P))

end Cyclic

include ht in
theorem poincareDuality_of_integerQuotient {n : ℕ}
    (hN : IsIntegralPoincareDualityGroup q.ker n) :
    IsIntegralPoincareDualityGroup G (n + 1) := by
  let := integerQuotient_isCyclic q t ht
  let := integerQuotient_infinite q t ht
  obtain ⟨P, d, hP, hd⟩ := hN.1
  refine ⟨finiteProjectiveResolution_of_infiniteCyclicQuotient q.ker hN.1, ?_, ?_⟩
  · intro i hi
    cases i with
    | zero => exact integerExtensionCohomology_zero q t ht P hP
    | succ j =>
      exact IsZero.of_iso (hN.2.1 j (by omega))
        (integerExtensionCohomologyIso q t ht P hP j)
  · obtain ⟨e⟩ := hN.2.2
    exact ⟨integerExtensionCohomologyIso q t ht P hP n ≪≫ e⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_TrivialGroupDuality
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.booleanPartitionStage_projective _root_.OAI.PolycyclicRecognition.cyclicTopHomologyInjection_mono _root_.OAI.PolycyclicRecognition.finiteResolution_single_supported _root_.OAI.PolycyclicRecognition.finiteTruncationAugmentation_quasiIso _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.horseshoeCover_projective _root_.OAI.PolycyclicRecognition.integralRepresentationSum_projective _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.normalizedSyzygy_projective _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The dimension-zero base of integral Poincaré duality -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits

variable (G : Type) [Group G] [Subsingleton G]

theorem finiteProjectiveResolution_of_subsingleton : HasFiniteProjectiveResolution G := by
  let P := ProjectiveResolution.self (trivialIntegral G)
  have hz (i : ℕ) (hi : 0 < i) : IsZero (P.complex.X i) := by
    apply HomologicalComplex.isZero_single_obj_X
    omega
  refine ⟨P, 0, ?_, hz⟩
  intro i
  cases i with
  | zero =>
      change IntegralRepresentationFinite G (trivialIntegral G)
      exact integralRepresentationFinite_of_finite G _ (by infer_instance)
  | succ i => exact integralRepresentationFinite_of_isZero G _ (hz (i + 1) (by omega))

theorem poincareDuality_zero_of_subsingleton : IsIntegralPoincareDualityGroup G 0 := by
  refine ⟨finiteProjectiveResolution_of_subsingleton G, ?_, ?_⟩
  · intro i hi
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi
    exact isZero_groupCohomology_succ_of_subsingleton (Rep.leftRegular ℤ G) j
  · let e : Rep.leftRegular ℤ G ≅ Rep.trivial ℤ G ℤ :=
      Rep.ofMulActionSubsingletonIsoTrivial ℤ G G
    exact ⟨(groupCohomology.functor ℤ G 0).mapIso e ≪≫
      groupCohomology.H0IsoOfIsTrivial (Rep.trivial ℤ G ℤ)⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_FreeAbelianDuality
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.cyclicTopHomologyInjection_mono _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.latticeNormalFlag_normal _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Free abelian rank bounds from integral cohomological dimension

The coordinate homomorphism splits off one infinite cyclic quotient at a time.
The resulting duality calculation bounds the rank of every embedded integral
lattice in a group of finite integral cohomological dimension.
-/

noncomputable section
namespace PolycyclicRecognition

theorem integralLattice_poincareDuality (n : ℕ) :
    IsIntegralPoincareDualityGroup (IntegralLatticeGroup n) n := by
  induction n with
  | zero => exact poincareDuality_zero_of_subsingleton _
  | succ n ih =>
    have hkernel := ih.of_equiv (latticeCoordinateKernel n).symm
    exact poincareDuality_of_integerQuotient (latticeCoordinate n)
      (latticeCoordinateSection n) (latticeCoordinate_section n) hkernel

theorem lattice_rank_le_cohomologicalDimension {G : Type} [Group G] (d : ℕ)
    [CategoryTheory.HasProjectiveDimensionLE (trivialIntegral G) d]
    (n : ℕ) (f : IntegralLatticeGroup n →* G) (hf : Function.Injective f) : n ≤ d := by
  let e := MonoidHom.ofInjective hf
  have hpd := (integralLattice_poincareDuality n).of_equiv e
  let := subgroup_cohomologicalDimension_le f.range d
  exact hpd.dimension_le

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_AbelianSubgroupRank
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.cyclicTopHomologyInjection_mono _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.latticeNormalFlag_normal _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

namespace OAI

/-! # Every abelian subgroup has bounded integral rank

An independent finite family defines an embedded integral lattice. The
cohomological-dimension bound on those lattices bounds the full module rank,
without assuming that the abelian subgroup is finitely generated.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped IsMulCommutative

variable {A : Type} [CommGroup A] {n : ℕ}

theorem independentLatticeHom_injective {b : Fin n → Additive A}
    (hb : LinearIndependent ℤ b) : Function.Injective (independentLatticeHom b) := by
  intro x y hxy
  apply Multiplicative.toAdd.injective
  apply hb.fintypeLinearCombination_injective
  exact congrArg Additive.ofMul hxy

theorem abelian_subgroup_integral_rank_le {G : Type} [Group G] (d : ℕ)
    [CategoryTheory.HasProjectiveDimensionLE (trivialIntegral G) d]
    (H : Subgroup G) [IsMulCommutative H] : Module.rank ℤ (Additive H) ≤ d := by
  by_contra hd
  have hlt : (d : Cardinal) < Module.rank ℤ (Additive H) := lt_of_not_ge hd
  have hle : ((d + 1 : ℕ) : Cardinal) ≤ Module.rank ℤ (Additive H) := by
    rw [Nat.cast_add, Nat.cast_one]
    exact Cardinal.natCast_add_one_le_iff.mpr hlt
  obtain ⟨b, hb⟩ := exists_linearIndependent_of_le_rank hle
  have hbound := lattice_rank_le_cohomologicalDimension d (d + 1)
    (H.subtype.comp (independentLatticeHom b))
    (Subtype.val_injective.comp (independentLatticeHom_injective hb))
  omega

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_LinearActionFiltration
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The dimension bound for an eventually vanishing action filtration

Take successive spans of the images of a family of operators. If this
descending filtration ever vanishes, it vanishes by the dimension of the
space: an equality at one stage propagates to all later stages, so every
nonzero stage must strictly lower dimension.
-/

noncomputable section
namespace PolycyclicRecognition

variable {K V I : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem linearActionStep_mono (D : I → Module.End K V) : Monotone (linearActionStep D) := by
  intro U W h
  exact iSup_mono fun _ => Submodule.map_mono h

theorem linearActionFiltration_antitone (D : I → Module.End K V) :
    Antitone (linearActionFiltration D) := by
  apply antitone_nat_of_succ_le
  intro n
  induction n with
  | zero => exact le_top
  | succ n ih => exact linearActionStep_mono D ih

theorem linearActionFiltration_constant (D : I → Module.End K V) {n : ℕ}
    (h : linearActionFiltration D (n + 1) = linearActionFiltration D n) (k : ℕ) :
    linearActionFiltration D (n + k) = linearActionFiltration D n := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change linearActionStep D (linearActionFiltration D (n + k)) = _
    rw [ih]
    exact h

theorem linearActionFiltration_strict_of_nonzero
    (D : I → Module.End K V) (hnil : ∃ c, linearActionFiltration D c = ⊥)
    {n : ℕ} (hn : linearActionFiltration D n ≠ ⊥) :
    linearActionFiltration D (n + 1) < linearActionFiltration D n := by
  apply lt_of_le_of_ne (linearActionFiltration_antitone D (Nat.le_succ n))
  intro he
  obtain ⟨c, hc⟩ := hnil
  have hnc : linearActionFiltration D (n + c) = ⊥ :=
    eq_bot_iff.mpr ((linearActionFiltration_antitone D (Nat.le_add_left c n)).trans_eq hc)
  exact hn ((linearActionFiltration_constant D he c).symm.trans hnc)

theorem linearActionFiltration_finrank_eq_bot [Module.Finite K V]
    (D : I → Module.End K V) (hnil : ∃ c, linearActionFiltration D c = ⊥) :
    linearActionFiltration D (Module.finrank K V) = ⊥ := by
  by_contra hnonzero
  let d := Module.finrank K V
  have hn (n : ℕ) (hnd : n ≤ d) : linearActionFiltration D n ≠ ⊥ := by
    intro hn
    exact hnonzero (eq_bot_iff.mpr
      ((linearActionFiltration_antitone D hnd).trans_eq hn))
  have hr (n : ℕ) (hnd : n ≤ d) :
      Module.finrank K (linearActionFiltration D n) + n ≤ d := by
    induction n with
    | zero => simpa only [Nat.add_zero] using
        (Submodule.finrank_le (linearActionFiltration D 0))
    | succ n ih =>
      have hi := ih (Nat.le_of_succ_le hnd)
      have hs := Submodule.finrank_lt_finrank_of_lt
        (linearActionFiltration_strict_of_nonzero D hnil (hn n (by omega)))
      omega
  have hzero : Module.finrank K (linearActionFiltration D d) = 0 := by
    have hbound := hr d le_rfl
    omega
  exact hnonzero (Submodule.finrank_eq_zero.mp hzero)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_ActionDepth
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Commutators advance an operator filtration

If every action difference raises a descending filtration by one step, its
commutators raise it further. This controls the lower central series using
the length at which the action filtration vanishes.
-/

namespace PolycyclicRecognition

open scoped commutatorElement

variable {K V I : Type*} [Field K] [AddCommGroup V] [Module K V]

namespace ActionDepth

variable {D : I → Module.End K V} {k l : ℕ} {f g : Module.End K V}

theorem zero (k : ℕ) : ActionDepth D k 0 := fun _ _ _ => Submodule.zero_mem _

theorem mono (hf : ActionDepth D k f) (hl : l ≤ k) : ActionDepth D l f := by
  intro n v hv
  exact linearActionFiltration_antitone D (Nat.add_le_add_left hl n) (hf n v hv)

theorem add (hf : ActionDepth D k f) (hg : ActionDepth D k g) :
    ActionDepth D k (f + g) := fun n v hv =>
  Submodule.add_mem _ (hf n v hv) (hg n v hv)

theorem neg (hf : ActionDepth D k f) : ActionDepth D k (-f) := fun n v hv =>
  Submodule.neg_mem _ (hf n v hv)

theorem sub (hf : ActionDepth D k f) (hg : ActionDepth D k g) :
    ActionDepth D k (f - g) := by simpa only [sub_eq_add_neg] using hf.add hg.neg

theorem mul (hf : ActionDepth D k f) (hg : ActionDepth D l g) :
    ActionDepth D (k + l) (f * g) := by
  intro n v hv
  simpa only [Module.End.mul_apply, Nat.add_assoc, Nat.add_comm l k] using hf (n + l) (g v) (hg n v hv)

theorem one : ActionDepth D 0 1 := by
  intro n v hv
  simpa using hv

theorem generator (i : I) : ActionDepth D 1 (D i) := by
  intro n v hv
  exact (le_iSup (fun j => (linearActionFiltration D n).map (D j)) i) ⟨v, hv, rfl⟩

theorem eq_zero {c : ℕ} (hf : ActionDepth D c f)
    (hc : linearActionFiltration D c = ⊥) : f = 0 := by
  apply LinearMap.ext
  intro v
  have hv := hf 0 v (Submodule.mem_top)
  simpa only [Nat.zero_add, hc, Submodule.mem_bot, LinearMap.zero_apply] using hv

end ActionDepth

variable {G : Type*} [Group G]

theorem lowerCentralSeries_le_ker_of_actionFiltration
    (ρ : G →* Module.End K V) (c : ℕ)
    (hc : linearActionFiltration (fun g => ρ g - 1) c = ⊥) :
    (⊤ : Subgroup G).lowerCentralSeries c ≤ ρ.ker := by
  let D := fun g => ρ g - 1
  have h1 (g : G) : ActionDepth D 1 (ρ g - 1) := ActionDepth.generator g
  have h0 (g : G) : ActionDepth D 0 (ρ g) := by
    have hh := ((h1 g).mono (Nat.zero_le 1)).add ActionDepth.one
    simpa only [sub_add_cancel] using hh
  have hmul (g h : G) :
      ρ (g * h) - 1 = (ρ g - 1) + (ρ h - 1) + (ρ g - 1) * (ρ h - 1) := by
    rw [ρ.map_mul]
    noncomm_ring
  have hinv (g : G) : ρ g⁻¹ - 1 = -(ρ g⁻¹ * (ρ g - 1)) := by
    have he : ρ g⁻¹ * ρ g = 1 := by rw [← ρ.map_mul, inv_mul_cancel, ρ.map_one]
    rw [mul_sub, he]
    noncomm_ring
  let S (k : ℕ) : Subgroup G :=
    { carrier := {g | ActionDepth D k (ρ g - 1)}
      one_mem' := by
        change ActionDepth D k (ρ 1 - 1)
        rw [ρ.map_one, sub_self]
        exact ActionDepth.zero k
      mul_mem' := by
        intro g h hg hh
        change ActionDepth D k (ρ (g * h) - 1)
        rw [hmul]
        exact (hg.add hh).add ((hg.mul hh).mono (by omega))
      inv_mem' := by
        intro g hg
        change ActionDepth D k (ρ g⁻¹ - 1)
        rw [hinv]
        simpa only [Nat.zero_add] using ((h0 g⁻¹).mul hg).neg }
  have hcomm (k : ℕ) (x y : G) (hx : x ∈ S k) : ⁅x, y⁆ ∈ S (k + 1) := by
    have hxy : ActionDepth D (k + 1)
        ((ρ x - 1) * (ρ y - 1) - (ρ y - 1) * (ρ x - 1)) :=
      (hx.mul (h1 y)).sub (by simpa only [Nat.add_comm] using (h1 y).mul hx)
    have hxi : ρ x * ρ x⁻¹ = 1 := by rw [← ρ.map_mul, mul_inv_cancel, ρ.map_one]
    have hyi : ρ y * ρ y⁻¹ = 1 := by rw [← ρ.map_mul, mul_inv_cancel, ρ.map_one]
    have he : ρ ⁅x, y⁆ - 1 =
        ((ρ x - 1) * (ρ y - 1) - (ρ y - 1) * (ρ x - 1)) * ρ x⁻¹ * ρ y⁻¹ := by
      simp only [commutatorElement_def, ρ.map_mul]
      calc
        _ = ρ x * ρ y * ρ x⁻¹ * ρ y⁻¹ - (ρ y * (ρ x * ρ x⁻¹)) * ρ y⁻¹ := by
          rw [hxi, mul_one, hyi]
        _ = _ := by noncomm_ring
    change ActionDepth D (k + 1) (ρ ⁅x, y⁆ - 1)
    rw [he]
    simpa only [Nat.add_zero] using (hxy.mul (h0 x⁻¹)).mul (h0 y⁻¹)
  have hs (k : ℕ) : (⊤ : Subgroup G).lowerCentralSeries k ≤ S (k + 1) := by
    induction k with
    | zero => exact fun g _ => h1 g
    | succ k ih =>
      rw [Subgroup.lowerCentralSeries_succ]
      exact Subgroup.commutator_le.mpr (fun x hx y _ => hcomm (k + 1) x y (ih hx))
  intro g hg
  change ρ g = 1
  exact sub_eq_zero.mp (((hs c hg).mono (Nat.le_succ c)).eq_zero hc)

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_ActionWordFiltration
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Operator words and the action filtration

The image-span filtration is controlled by products of the operators. This
turns any uniform vanishing length into the dimension bound proved for that
filtration.
-/

noncomputable section
namespace PolycyclicRecognition

variable {K V I : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem linearActionFiltration_le_ker (D : I → Module.End K V) (n : ℕ)
    (f : Module.End K V)
    (h : ∀ w : List I, w.length = n → f * actionOperatorWord D w = 0) :
    linearActionFiltration D n ≤ LinearMap.ker f := by
  induction n generalizing f with
  | zero =>
    have hf : f = 0 := by simpa [actionOperatorWord] using h [] rfl
    simp [hf]
  | succ n ih =>
    change (⨆ i, (linearActionFiltration D n).map (D i)) ≤ LinearMap.ker f
    apply iSup_le
    intro i
    rintro y ⟨x, hx, rfl⟩
    have hk := ih (f * D i) (by
      intro w hw
      have he := h (i :: w) (by simp [hw])
      simpa only [actionOperatorWord, List.map_cons, List.prod_cons, mul_assoc] using he)
    exact hk hx

theorem linearActionFiltration_eq_bot_of_word_zero
    (D : I → Module.End K V) (n : ℕ)
    (h : ∀ w : List I, w.length = n → actionOperatorWord D w = 0) :
    linearActionFiltration D n = ⊥ := by
  apply eq_bot_iff.mpr
  have he := linearActionFiltration_le_ker D n 1 (by simpa using h)
  simpa only [Module.End.one_eq_id, LinearMap.ker_id] using he

theorem actionOperatorWord_apply_mem (D : I → Module.End K V)
    (w : List I) (v : V) :
    actionOperatorWord D w v ∈ linearActionFiltration D w.length := by
  induction w with
  | nil => exact Submodule.mem_top
  | cons i w ih =>
    change D i (actionOperatorWord D w v) ∈
      ⨆ j, (linearActionFiltration D w.length).map (D j)
    exact (le_iSup (fun j => (linearActionFiltration D w.length).map (D j)) i)
      ⟨actionOperatorWord D w v, ih, rfl⟩

theorem actionOperatorWord_zero_of_filtration_eq_bot
    (D : I → Module.End K V) {n : ℕ} (h : linearActionFiltration D n = ⊥)
    (w : List I) (hw : w.length = n) : actionOperatorWord D w = 0 := by
  apply LinearMap.ext
  intro v
  have hv := actionOperatorWord_apply_mem D w v
  rw [hw, h] at hv
  exact hv

theorem actionOperatorWord_zero_at_finrank [Module.Finite K V]
    (D : I → Module.End K V)
    (h : ∃ c, ∀ w : List I, w.length = c → actionOperatorWord D w = 0) :
    ∀ w : List I, w.length = Module.finrank K V → actionOperatorWord D w = 0 := by
  apply actionOperatorWord_zero_of_filtration_eq_bot
  apply linearActionFiltration_finrank_eq_bot
  obtain ⟨c, hc⟩ := h
  exact ⟨c, linearActionFiltration_eq_bot_of_word_zero D c hc⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_MaximalAbelianNormal
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

theorem Subgroup.normal_of_le_center {G : Type*} [Group G] {H : Subgroup G}
    (hH : H ≤ Subgroup.center G) : H.Normal :=
  ⟨fun a ha b ↦ by simpa [Subgroup.mem_center_iff.mp (hH ha) b]⟩

/-! Compatibility with OpenAI's Mathlib (d13f23b): a lemma it has and ours lacks. -/

theorem Group.IsNilpotent.inf_center_ne_bot_of_normal {G : Type*} [Group G] [Group.IsNilpotent G]
    {H : Subgroup G} [H.Normal] (hH : H ≠ ⊥) : H ⊓ Subgroup.center G ≠ ⊥ := by
  classical
  have hk : ∃ n, H ⊓ (⊤ : Subgroup G).lowerCentralSeries n ≠ ⊥ ∧
      H ⊓ (⊤ : Subgroup G).lowerCentralSeries (n + 1) = ⊥ := by
    have : H ⊓ (⊤ : Subgroup G).lowerCentralSeries 0 ≠ ⊥ := by
      simpa [Subgroup.lowerCentralSeries_zero] using hH
    have key : ∃ k, H ⊓ (⊤ : Subgroup G).lowerCentralSeries k = ⊥ :=
      ⟨Group.nilpotencyClass G, by simp [Subgroup.lowerCentralSeries_nilpotencyClass]⟩
    exact ⟨Nat.find key - 1, by grind [Nat.find_min key]⟩
  obtain ⟨k, k_min, k_spec⟩ := hk
  refine ne_bot_of_le_ne_bot k_min (le_inf inf_le_left ?_)
  rw [← Subgroup.commutator_top_right_eq_bot_iff_le_center, eq_bot_iff, ← k_spec,
    Subgroup.lowerCentralSeries_succ]
  exact le_inf ((Subgroup.commutator_le_left _ _).trans inf_le_left)
    (Subgroup.commutator_mono inf_le_right le_rfl)
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

namespace OAI

/-! # Maximal abelian normal subgroups for nilpotent lattice finiteness -/

noncomputable section
namespace PolycyclicRecognition

open Set Subgroup

variable (G : Type*) [Group G]

theorem exists_maximal_abelian_normal_subgroup :
    ∃ A : Subgroup G, A.Normal ∧ IsMulCommutative A ∧
      ∀ B : Subgroup G, B.Normal → IsMulCommutative B → A ≤ B → B = A := by
  let P : Set (Subgroup G) := {A | A.Normal ∧ IsMulCommutative A}
  obtain ⟨A, hA, hmax⟩ := zorn_le₀ P (by
    intro c hc hchain
    rcases c.eq_empty_or_nonempty with rfl | hne
    · exact ⟨⊥, ⟨inferInstance, inferInstance⟩, by simp⟩
    · have hdir : DirectedOn (· ≤ ·) c := hchain.directedOn
      have hn : (sSup c).Normal := Subgroup.sSup_normal c (fun B hB => (hc hB).1)
      have ha : IsMulCommutative (sSup c : Subgroup G) := by
        apply IsMulCommutative.of_setLike_mul_comm
        intro x hx y hy
        obtain ⟨B, hB, hx⟩ := (Subgroup.mem_sSup_of_directedOn hne hdir).mp hx
        obtain ⟨C, hC, hy⟩ := (Subgroup.mem_sSup_of_directedOn hne hdir).mp hy
        obtain ⟨D, hD, hBD, hCD⟩ := hdir B hB C hC
        let : IsMulCommutative D := (hc hD).2
        exact setLike_mul_comm (hBD hx) (hCD hy)
      exact ⟨sSup c, ⟨hn, ha⟩, fun B hB => le_sSup hB⟩)
  refine ⟨A, hA.1, hA.2, ?_⟩
  intro B hn ha hAB
  exact le_antisymm (hmax ⟨hn, ha⟩ hAB) hAB

/-- In a nilpotent group, a maximal abelian normal subgroup is its own
centralizer. This permits a faithful action of the quotient on that subgroup. -/
theorem centralizer_eq_of_maximal_abelian_normal [Group.IsNilpotent G]
    (A : Subgroup G) [A.Normal] [IsMulCommutative A]
    (hmax : ∀ B : Subgroup G, B.Normal → IsMulCommutative B → A ≤ B → B = A) :
    Subgroup.centralizer (A : Set G) = A := by
  classical
  let C := Subgroup.centralizer (A : Set G)
  have hAC : A ≤ C := Subgroup.le_centralizer A
  apply le_antisymm _ hAC
  by_contra hCA
  let q := QuotientGroup.mk' A
  let D := C.map q
  have hD : D ≠ ⊥ := by
    intro hD
    apply hCA
    intro x hx
    have hqx : q x ∈ D := ⟨x, hx, rfl⟩
    rw [hD] at hqx
    exact (QuotientGroup.eq_one_iff _).mp hqx
  let : D.Normal := inferInstance
  have hDC := Group.IsNilpotent.inf_center_ne_bot_of_normal hD
  let : Nontrivial ↥(D ⊓ Subgroup.center (G ⧸ A)) :=
    (Subgroup.nontrivial_iff_ne_bot _).mpr hDC
  obtain ⟨u, hu, hune⟩ := (D ⊓ Subgroup.center (G ⧸ A)).exists_ne_one_of_nontrivial
  obtain ⟨x, hxC, hxu⟩ := hu.1
  let S := Subgroup.zpowers u
  let : S.Normal := Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr hu.2)
  let B := C ⊓ S.comap q
  have hAB : A ≤ B := by
    intro a ha
    refine ⟨hAC ha, ?_⟩
    change q a ∈ S
    have hqa : q a = 1 := (QuotientGroup.eq_one_iff _).mpr ha
    rw [hqa]
    exact S.one_mem
  let f : B →* S := (q.comp B.subtype).codRestrict S (fun b => b.property.2)
  have hf : f.ker ≤ Subgroup.center B := by
    intro b hb
    have hbA : (b : G) ∈ A := by
      apply (QuotientGroup.eq_one_iff _).mp
      exact congrArg Subtype.val hb
    rw [Subgroup.mem_center_iff]
    intro c
    apply Subtype.ext
    exact (c.property.1 b hbA).symm
  have hbcomm : IsMulCommutative B := f.isMulCommutative_of_isCyclic_of_ker_le_center hf
  have hBA : B = A := hmax B inferInstance hbcomm hAB
  have hxB : x ∈ B := ⟨hxC, by
    change q x ∈ S
    rw [hxu]
    exact Subgroup.mem_zpowers u⟩
  have hxA : x ∈ A := hBA ▸ hxB
  exact hune (hxu.symm.trans ((QuotientGroup.eq_one_iff _).mpr hxA))

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_FiniteDimensionTorsionFree
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.cyclicTopHomologyInjection_mono _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite integral cohomological dimension excludes torsion

Restriction gives a dimension bound on every cyclic subgroup. Its periodic
integral cohomology contradicts that bound if the subgroup is nontrivial finite.
-/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits

variable {G : Type} [Group G]

theorem HasFiniteIntegralCohomologicalDimension.torsionFree
    (hG : HasFiniteIntegralCohomologicalDimension G) : HasNoNontrivialTorsion G := by
  classical
  intro g n hn hgn
  by_contra hg
  have hfin : IsOfFinOrder g := isOfFinOrder_iff_pow_eq_one.mpr ⟨n, Nat.pos_of_ne_zero hn, hgn⟩
  let H := Subgroup.zpowers g
  let : Fintype H := Fintype.ofEquiv (Fin (orderOf g)) (finEquivZPowers hfin)
  let : CommGroup H := IsCyclic.commGroup
  let : Nontrivial H := ⟨⟨⟨g, Subgroup.mem_zpowers g⟩, 1, fun h => hg (congrArg Subtype.val h)⟩⟩
  obtain ⟨z, hz⟩ := IsCyclic.exists_generator (α := H)
  obtain ⟨d, hd⟩ := hG.subgroup H
  let := hd
  let : NeZero (2 * (d + 1)) := ⟨by omega⟩
  exact finiteCyclic_even_cohomology_not_isZero z hz Fintype.one_lt_card
    (2 * (d + 1)) (even_two_mul _) <|
      groupCohomology_isZero_above_dimension d (trivialIntegral H) _ (by omega)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_RationalAbelianRank
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.cyclicTopHomologyInjection_mono _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

namespace OAI

/-! # Rationalizing the bounded-rank abelian subgroups

The integral dimension bound applies even to abelian subgroups which are not
finitely generated. Their rationalizations have the same rank, and the
canonical map is injective because integral cohomological dimension excludes
torsion. Thus these subgroups embed in finite-dimensional rational spaces.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped IsMulCommutative TensorProduct

variable {A : Type} [CommGroup A]

theorem rationalAbelianMap_injective (hA : HasNoNontrivialTorsion A) :
    Function.Injective (rationalAbelianMap (A := A)) := by
  let : IsMulTorsionFree A := isMulTorsionFree_iff_not_isOfFinOrder.mpr (by
    intro a ha hf
    exact ha (hA a (orderOf a) (ne_of_gt hf.orderOf_pos) (pow_orderOf_eq_one a)))
  let : IsAddTorsionFree (Additive A) := inferInstance
  let : Module.IsTorsionFree ℤ (Additive A) := inferInstance
  exact Module.Flat.tensorProduct_mk_injective ℤ (Additive A) ℚ

theorem rationalAbelianSpace_rank :
    Module.rank ℚ (RationalAbelianSpace A) = Module.rank ℤ (Additive A) := by
  exact (TensorProduct.isBaseChange ℤ (Additive A) ℚ).rank_eq

theorem abelian_subgroup_rational_rank_le {G : Type} [Group G] (d : ℕ)
    [CategoryTheory.HasProjectiveDimensionLE (trivialIntegral G) d]
    (H : Subgroup G) [IsMulCommutative H] :
    Module.rank ℚ (RationalAbelianSpace H) ≤ d := by
  rw [rationalAbelianSpace_rank]
  exact abelian_subgroup_integral_rank_le d H

theorem abelian_subgroup_rational_finite {G : Type} [Group G] (d : ℕ)
    [CategoryTheory.HasProjectiveDimensionLE (trivialIntegral G) d]
    (H : Subgroup G) [IsMulCommutative H] :
    Module.Finite ℚ (RationalAbelianSpace H) :=
  Module.rank_lt_aleph0_iff.mp <|
    (abelian_subgroup_rational_rank_le d H).trans_lt Cardinal.natCast_lt_aleph0

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_RationalConjugation
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

namespace OAI

/-! # Rational conjugation on an abelian normal subgroup

Conjugation extends to the rationalization. When the subgroup is torsion free,
the extended action has exactly the same kernel, namely its centralizer.
Together with the rank bound this is a finite-dimensional representation of
the centralizer quotient, without a finite-generation assumption on the
abelian subgroup.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped IsMulCommutative TensorProduct

variable {A : Type} [CommGroup A]

theorem rationalAbelianAut_injective (hA : HasNoNontrivialTorsion A) :
    Function.Injective (rationalAbelianAut (A := A)) := by
  intro e f hef
  ext a
  apply Additive.ofMul.injective
  apply rationalAbelianMap_injective hA
  exact congrArg (fun u => u (rationalAbelianMap (Additive.ofMul a))) hef

variable {G : Type} [Group G] (H : Subgroup G) [H.Normal] [IsMulCommutative H]

theorem rationalConjugation_ker (hH : HasNoNontrivialTorsion H) :
    (rationalConjugation H).ker = Subgroup.centralizer (H : Set G) := by
  ext g
  change rationalAbelianAut (A := H) (MulAut.conjNormal (H := H) g) =
    (1 : RationalAbelianSpace H ≃ₗ[ℚ] RationalAbelianSpace H) ↔ _
  rw [← (rationalAbelianAut (A := H)).map_one,
    (rationalAbelianAut_injective hH).eq_iff]
  constructor
  · intro hg a ha
    have he := congrArg (fun e : MulAut H => ((e ⟨a, ha⟩ : H) : G)) hg
    change g * a * g⁻¹ = a at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  · intro hg
    ext a
    change g * (a : G) * g⁻¹ = a
    rw [← hg a a.property, mul_inv_cancel_right]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_NilpotentRationalConjugation
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

namespace OAI

/-! # Nilpotent conjugation has a dimension-bounded unipotence exponent

On an abelian normal subgroup, conjugation minus the identity is the
commutator map. Its successive powers lie in successive lower-central terms.
Rationalization therefore gives a nilpotent operator, whose exponent is
bounded by the rational rank rather than by a chosen group nilpotency class.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped IsMulCommutative TensorProduct commutatorElement

variable {G : Type} [Group G] (H : Subgroup G) [H.Normal] [IsMulCommutative H]

theorem integralConjugationDifference_apply (g : G) (a : Additive H) :
    ((integralConjugationDifference H g a).toMul : G) = ⁅g, (a.toMul : G)⁆ := by
  simp only [integralConjugationDifference, LinearMap.sub_apply, Module.End.one_apply,
    commutatorElement_def]
  change (((MulAut.conjNormal (H := H) g) a.toMul / a.toMul : H) : G) = _
  rw [Subgroup.coe_div]
  change (g * (a.toMul : G) * g⁻¹) / (a.toMul : G) = _
  rw [div_eq_mul_inv]

theorem integralConjugationDifference_pow_mem (g : G) (k : ℕ) (a : Additive H) :
    (((integralConjugationDifference H g ^ k) a).toMul : G) ∈
      (⊤ : Subgroup G).lowerCentralSeries k := by
  induction k with
  | zero => exact Subgroup.mem_top _
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, integralConjugationDifference_apply,
      Subgroup.lowerCentralSeries_succ, Subgroup.commutator_comm]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top g) ih

theorem integralConjugationDifference_nilpotent [Group.IsNilpotent G] (g : G) :
    IsNilpotent (integralConjugationDifference H g) := by
  refine ⟨Group.nilpotencyClass G, ?_⟩
  apply LinearMap.ext
  intro a
  have h := integralConjugationDifference_pow_mem H g (Group.nilpotencyClass G) a
  rw [Subgroup.lowerCentralSeries_nilpotencyClass, Subgroup.mem_bot] at h
  apply Additive.toMul.injective
  apply Subtype.val_injective
  exact h

theorem rationalConjugationDifference_baseChange (g : G) :
    (rationalConjugation H g).toLinearMap - 1 =
      (integralConjugationDifference H g).baseChange ℚ := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro q a
  simp only [integralConjugationDifference, LinearMap.baseChange_sub,
    LinearMap.baseChange_one]
  rfl

theorem rationalConjugationDifference_nilpotent [Group.IsNilpotent G] (g : G) :
    IsNilpotent ((rationalConjugation H g).toLinearMap - 1) := by
  obtain ⟨k, hk⟩ := integralConjugationDifference_nilpotent H g
  refine ⟨k, ?_⟩
  rw [rationalConjugationDifference_baseChange, ← LinearMap.baseChange_pow,
    hk, LinearMap.baseChange_zero]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_NilpotentConjugationWords
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

namespace OAI

/-! # A common dimension bound for mixed conjugation differences

Nilpotence of the group annihilates sufficiently long products even when
successive conjugating elements differ. The action filtration improves this
bound to the rational rank of the abelian normal subgroup.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped IsMulCommutative TensorProduct commutatorElement

variable {G : Type} [Group G] (H : Subgroup G) [H.Normal] [IsMulCommutative H]

theorem integralConjugationWord_mem (w : List G) (a : Additive H) :
    ((((w.map (integralConjugationDifference H)).prod) a).toMul : G) ∈
      (⊤ : Subgroup G).lowerCentralSeries w.length := by
  induction w with
  | nil => exact Subgroup.mem_top _
  | cons g w ih =>
    rw [List.map_cons, List.prod_cons, Module.End.mul_apply,
      integralConjugationDifference_apply, List.length_cons,
      Subgroup.lowerCentralSeries_succ, Subgroup.commutator_comm]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top g) ih

theorem integralConjugationWord_zero [Group.IsNilpotent G]
    (w : List G) (hw : w.length = Group.nilpotencyClass G) :
    (w.map (integralConjugationDifference H)).prod = 0 := by
  apply LinearMap.ext
  intro a
  have h := integralConjugationWord_mem H w a
  rw [hw, Subgroup.lowerCentralSeries_nilpotencyClass, Subgroup.mem_bot] at h
  apply Additive.toMul.injective
  apply Subtype.val_injective
  exact h

theorem rationalConjugationWord_baseChange (w : List G) :
    actionOperatorWord (fun g => (rationalConjugation H g).toLinearMap - 1) w =
      ((w.map (integralConjugationDifference H)).prod).baseChange ℚ := by
  induction w with
  | nil => simp [actionOperatorWord]
  | cons g w ih =>
    change ((rationalConjugation H g).toLinearMap - 1) *
      actionOperatorWord (fun g => (rationalConjugation H g).toLinearMap - 1) w = _
    rw [ih, rationalConjugationDifference_baseChange, ← LinearMap.baseChange_mul]
    rfl

theorem rationalConjugationWord_zero_at_rank [Group.IsNilpotent G]
    [Module.Finite ℚ (RationalAbelianSpace H)] :
    ∀ w : List G, w.length = Module.finrank ℚ (RationalAbelianSpace H) →
      actionOperatorWord (fun g => (rationalConjugation H g).toLinearMap - 1) w = 0 := by
  apply actionOperatorWord_zero_at_finrank
  refine ⟨Group.nilpotencyClass G, fun w hw => ?_⟩
  rw [rationalConjugationWord_baseChange, integralConjugationWord_zero H w hw,
    LinearMap.baseChange_zero]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_RationalSubgroupFiltration
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

namespace OAI

/-! # Pulling the rational action filtration back to the group

The rational filtration on an abelian normal subgroup gives actual ambient
subgroups. Commuting with the ambient group advances the filtration. Its last
term is trivial when the abelian subgroup is torsion free.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G] (H : Subgroup G) [H.Normal] [IsMulCommutative H]

theorem rationalSubgroupFiltration_zero : rationalSubgroupFiltration H 0 = H := by
  have htop : rationalPreimageSubgroup H ⊤ = ⊤ := by ext; simp [rationalPreimageSubgroup]
  simp only [rationalSubgroupFiltration, linearActionFiltration, htop,
    ← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem rationalAbelianMap_conjugationDifference (g : G) (a : Additive H) :
    rationalAbelianMap (integralConjugationDifference H g a) =
      ((rationalConjugation H g).toLinearMap - 1) (rationalAbelianMap a) := by
  rw [rationalConjugationDifference_baseChange]
  rfl

theorem rationalSubgroupFiltration_commutator (n : ℕ) :
    ⁅rationalSubgroupFiltration H n, (⊤ : Subgroup G)⁆ ≤ rationalSubgroupFiltration H (n + 1) := by
  apply Subgroup.commutator_le.mpr
  rintro x ⟨a, ha, rfl⟩ y _
  let b := (integralConjugationDifference H y (Additive.ofMul a)).toMul
  have hD : rationalAbelianMap (integralConjugationDifference H y (Additive.ofMul a)) ∈
      linearActionFiltration (fun g => (rationalConjugation H g).toLinearMap - 1) (n + 1) := by
    rw [rationalAbelianMap_conjugationDifference]
    exact ActionDepth.generator y n _ ha
  refine ⟨b⁻¹, ?_, ?_⟩
  · change rationalAbelianMap (-integralConjugationDifference H y (Additive.ofMul a)) ∈
      linearActionFiltration (fun g => (rationalConjugation H g).toLinearMap - 1) (n + 1)
    rw [map_neg]
    exact Submodule.neg_mem _ hD
  · change (b : G)⁻¹ = ⁅(a : G), y⁆
    rw [show (b : G) = ⁅y, (a : G)⁆ from integralConjugationDifference_apply H y _]
    exact commutatorElement_inv y (a : G)

theorem rationalSubgroupFiltration_eq_bot (hH : HasNoNontrivialTorsion H) {n : ℕ}
    (hn : linearActionFiltration (fun g => (rationalConjugation H g).toLinearMap - 1) n = ⊥) :
    rationalSubgroupFiltration H n = ⊥ := by
  apply eq_bot_iff.mpr
  rintro g ⟨a, ha, rfl⟩
  change rationalAbelianMap (Additive.ofMul a) ∈
    linearActionFiltration (fun g => (rationalConjugation H g).toLinearMap - 1) n at ha
  rw [hn, Submodule.mem_bot] at ha
  have ha0 : Additive.ofMul a = 0 := rationalAbelianMap_injective hH (by simpa using ha)
  exact congrArg (fun x : Additive H => ((x.toMul : H) : G)) ha0

theorem lowerCentralSeries_le_rationalSubgroupFiltration (r : ℕ)
    (hr : (⊤ : Subgroup G).lowerCentralSeries r ≤ H) (n : ℕ) :
    (⊤ : Subgroup G).lowerCentralSeries (r + n) ≤ rationalSubgroupFiltration H n := by
  induction n with
  | zero => simpa only [Nat.add_zero, rationalSubgroupFiltration_zero] using hr
  | succ n ih =>
    rw [Nat.add_succ, Subgroup.lowerCentralSeries_succ]
    exact (Subgroup.commutator_mono ih le_rfl).trans (rationalSubgroupFiltration_commutator H n)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_NilpotentClassBound
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.cyclicTopHomologyInjection_mono _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

namespace OAI

/-! # A uniform nilpotency-class bound from integral dimension

A maximal abelian normal subgroup of a nilpotent group is self-centralizing.
The faithful rational conjugation action bounds the lower central series
modulo that subgroup. Its pulled-back rational filtration bounds the remaining
series inside it. Each part has length at most the rational rank.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped IsMulCommutative

variable {G : Type} [Group G]

theorem rationalConjugationLinear_ker (H : Subgroup G) [H.Normal] [IsMulCommutative H]
    (hH : HasNoNontrivialTorsion H) :
    (rationalConjugationLinear H).ker = Subgroup.centralizer (H : Set G) := by
  rw [← rationalConjugation_ker H hH]
  ext g
  change (rationalConjugation H g).toLinearMap = 1 ↔ rationalConjugation H g = 1
  exact ⟨fun h => LinearEquiv.toLinearMap_injective h, fun h => congrArg LinearEquiv.toLinearMap h⟩

theorem nilpotencyClass_le_twice_rationalRank [Group.IsNilpotent G]
    (H : Subgroup G) [H.Normal] [IsMulCommutative H]
    [Module.Finite ℚ (RationalAbelianSpace H)] (hH : HasNoNontrivialTorsion H)
    (hC : Subgroup.centralizer (H : Set G) = H) :
    Group.nilpotencyClass G ≤ 2 * Module.finrank ℚ (RationalAbelianSpace H) := by
  let r := Module.finrank ℚ (RationalAbelianSpace H)
  have hF : linearActionFiltration
      (fun g => (rationalConjugation H g).toLinearMap - 1) r = ⊥ :=
    linearActionFiltration_eq_bot_of_word_zero _ r (rationalConjugationWord_zero_at_rank H)
  have hL : (⊤ : Subgroup G).lowerCentralSeries r ≤ H := by
    rw [← hC, ← rationalConjugationLinear_ker H hH]
    exact lowerCentralSeries_le_ker_of_actionFiltration (rationalConjugationLinear H) r hF
  have hlast : (⊤ : Subgroup G).lowerCentralSeries (r + r) = ⊥ := by
    apply eq_bot_iff.mpr
    exact (lowerCentralSeries_le_rationalSubgroupFiltration H r hL r).trans
      (le_of_eq (rationalSubgroupFiltration_eq_bot H hH hF))
  rw [two_mul]
  exact Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mp hlast

theorem nilpotencyClass_le_twice_cohomologicalDimension [Group.IsNilpotent G]
    (d : ℕ) [CategoryTheory.HasProjectiveDimensionLE (trivialIntegral G) d] :
    Group.nilpotencyClass G ≤ 2 * d := by
  obtain ⟨A, hAn, hAa, hmax⟩ := exists_maximal_abelian_normal_subgroup G
  let := hAn
  let := hAa
  let := abelian_subgroup_rational_finite d A
  have hA : HasFiniteIntegralCohomologicalDimension A :=
    ⟨d, subgroup_cohomologicalDimension_le A d⟩
  have hr : Module.finrank ℚ (RationalAbelianSpace A) ≤ d :=
    FiniteDimensional.finrank_le_iff_rank_le.mpr (abelian_subgroup_rational_rank_le d A)
  exact (nilpotencyClass_le_twice_rationalRank A hA.torsionFree
    (centralizer_eq_of_maximal_abelian_normal G A hmax)).trans (Nat.mul_le_mul_left 2 hr)

theorem nilpotent_subgroup_class_le (d : ℕ)
    [CategoryTheory.HasProjectiveDimensionLE (trivialIntegral G) d]
    (N : Subgroup G) [Group.IsNilpotent N] : Group.nilpotencyClass N ≤ 2 * d := by
  let := subgroup_cohomologicalDimension_le N d
  exact nilpotencyClass_le_twice_cohomologicalDimension d

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_CentralFiltrationAction
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Compatibility with OpenAI's Mathlib (d13f23b): one-sided `commutator_mono`. -/

private theorem Subgroup.commutator_mono_left_p0 {G : Type*} [Group G] {H₁ H₂ K : Subgroup G} (h : H₁ ≤ H₂) :
    ⁅H₁, K⁆ ≤ ⁅H₂, K⁆ :=
  Subgroup.commutator_mono h le_rfl

private theorem Subgroup.commutator_mono_right_p0 {G : Type*} [Group G] {H K₁ K₂ : Subgroup G} (h : K₁ ≤ K₂) :
    ⁅H, K₁⁆ ≤ ⁅H, K₂⁆ :=
  Subgroup.commutator_mono le_rfl h

namespace OAI

/-! # Nilpotence detected by an action on a central filtration

The three subgroups lemma increases the depth of a commutator action. Once
the lower central series centralizes the last filtration term, a centralizer
bound puts it inside that term; the action then lowers it to the identity.
-/

namespace PolycyclicRecognition

open scoped commutatorElement
variable {G : Type} [Group G]

theorem commutator_commutator_le_of_rotate (H₁ H₂ H₃ N : Subgroup G) [N.Normal]
    (h₁ : ⁅⁅H₂, H₃⁆, H₁⁆ ≤ N) (h₂ : ⁅⁅H₃, H₁⁆, H₂⁆ ≤ N) :
    ⁅⁅H₁, H₂⁆, H₃⁆ ≤ N := by
  let q := QuotientGroup.mk' N
  have hm (S : Subgroup G) : S ≤ N ↔ S.map q = ⊥ := by
    rw [eq_bot_iff, Subgroup.map_le_iff_le_comap, MonoidHom.comap_bot, QuotientGroup.ker_mk']
  apply (hm _).mpr
  rw [Subgroup.map_commutator, Subgroup.map_commutator]
  apply Subgroup.commutator_commutator_eq_bot_of_rotate
  · simpa only [Subgroup.map_commutator] using (hm _).mp h₁
  · simpa only [Subgroup.map_commutator] using (hm _).mp h₂

theorem lowerCentralSeries_action_depth (K : Subgroup G) (U : ℕ → Subgroup G)
    [∀ i, (U i).Normal]
    (hstep : ∀ i, ⁅K, U (i + 1)⁆ ≤ U i) (n i : ℕ) :
    ⁅K.lowerCentralSeries n, U (i + n + 1)⁆ ≤ U i := by
  induction n generalizing i with
  | zero => simpa only [Subgroup.lowerCentralSeries_zero, Nat.add_zero] using hstep i
  | succ n ih =>
    rw [Subgroup.lowerCentralSeries_succ]
    apply commutator_commutator_le_of_rotate
    · have hs : ⁅K, U (i + (n + 1) + 1)⁆ ≤ U (i + n + 1) := by
        exact hstep (i + n + 1)
      calc
        ⁅⁅K, U (i + (n + 1) + 1)⁆, K.lowerCentralSeries n⁆ ≤
            ⁅U (i + n + 1), K.lowerCentralSeries n⁆ := Subgroup.commutator_mono_left_p0 hs
        _ = ⁅K.lowerCentralSeries n, U (i + n + 1)⁆ := Subgroup.commutator_comm _ _
        _ ≤ U i := ih i
    · have hs : ⁅U (i + (n + 1) + 1), K.lowerCentralSeries n⁆ ≤ U (i + 1) := by
        rw [Subgroup.commutator_comm]
        simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (i + 1)
      exact (Subgroup.commutator_mono_left_p0 hs).trans (by
        rw [Subgroup.commutator_comm]
        exact hstep i)

theorem nilpotent_of_central_filtration_action (K : Subgroup G) (U : ℕ → Subgroup G)
    [∀ i, (U i).Normal] (hmono : Monotone U) (hzero : U 0 = ⊥)
    (hstep : ∀ i, ⁅K, U (i + 1)⁆ ≤ U i) (c : ℕ)
    (hcent : Subgroup.centralizer (U c : Set G) ≤ U c) : Group.IsNilpotent K := by
  have hz : ⁅K.lowerCentralSeries c, U c⁆ = ⊥ := by
    apply eq_bot_iff.mpr
    calc
      ⁅K.lowerCentralSeries c, U c⁆ ≤ ⁅K.lowerCentralSeries c, U (c + 1)⁆ :=
        Subgroup.commutator_mono_right_p0 (hmono (Nat.le_succ c))
      _ ≤ U 0 := by simpa only [Nat.zero_add] using lowerCentralSeries_action_depth K U hstep c 0
      _ = ⊥ := hzero
  have hdeep : K.lowerCentralSeries c ≤ U c :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hz).trans hcent
  have hdown : ∀ j, j ≤ c → K.lowerCentralSeries (c + j) ≤ U (c - j) := by
    intro j
    induction j with
    | zero => simpa only [Nat.add_zero, Nat.sub_zero] using fun _ : 0 ≤ c => hdeep
    | succ j ih =>
      intro hj
      have he : c - j = (c - (j + 1)) + 1 := by omega
      calc
        K.lowerCentralSeries (c + (j + 1)) = ⁅K.lowerCentralSeries (c + j), K⁆ := by
          rw [← Nat.add_assoc, Subgroup.lowerCentralSeries_succ]
        _ ≤ ⁅U (c - j), K⁆ := Subgroup.commutator_mono_left_p0 (ih (by omega))
        _ = ⁅K, U ((c - (j + 1)) + 1)⁆ := by rw [he, Subgroup.commutator_comm]
        _ ≤ U (c - (j + 1)) := hstep _
  apply (Subgroup.isNilpotent_iff_lowerCentralSeries K).mpr
  refine ⟨c + c, eq_bot_iff.mpr ?_⟩
  simpa only [Nat.sub_self, hzero] using hdown c le_rfl

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_RelativeCommutatorSeries
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Compatibility with OpenAI's Mathlib (d13f23b): one-sided `commutator_mono`. -/

private theorem Subgroup.commutator_mono_right_p1 {G : Type*} [Group G] {H K₁ K₂ : Subgroup G} (h : K₁ ≤ K₂) :
    ⁅H, K₁⁆ ≤ ⁅H, K₂⁆ :=
  Subgroup.commutator_mono le_rfl h

namespace OAI

/-! # Iterated action commutators and a centralizer criterion -/

namespace PolycyclicRecognition

open scoped commutatorElement
variable {G : Type} [Group G]

theorem relativeCommutatorSeries_mono (K : Subgroup G) {N M : Subgroup G}
    (h : N ≤ M) (n : ℕ) : relativeCommutatorSeries K N n ≤ relativeCommutatorSeries K M n := by
  induction n with
  | zero => exact h
  | succ n ih => exact Subgroup.commutator_mono_right_p1 ih

theorem relativeCommutatorSeries_antitone (K N : Subgroup G) [N.Normal] :
    Antitone (relativeCommutatorSeries K N) := by
  apply antitone_nat_of_succ_le
  intro n
  induction n with
  | zero => exact Subgroup.commutator_le_right K N
  | succ n ih => exact Subgroup.commutator_mono_right_p1 ih

theorem relativeCommutatorSeries_add (K N : Subgroup G) (i j : ℕ) :
    relativeCommutatorSeries K N (i + j) =
      relativeCommutatorSeries K (relativeCommutatorSeries K N i) j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    change ⁅K, relativeCommutatorSeries K N (i + j)⁆ =
      ⁅K, relativeCommutatorSeries K (relativeCommutatorSeries K N i) j⁆
    rw [ih]

theorem nilpotent_of_relativeCommutatorSeries (K N : Subgroup G) [K.Normal] [N.Normal]
    (c : ℕ) (hc : relativeCommutatorSeries K N c = ⊥)
    (hcent : Subgroup.centralizer (N : Set G) ≤ N) : Group.IsNilpotent K := by
  let U (i : ℕ) := relativeCommutatorSeries K N (c - i)
  refine nilpotent_of_central_filtration_action K U ?_ ?_ ?_ c ?_
  · intro i j hij
    exact relativeCommutatorSeries_antitone K N (Nat.sub_le_sub_left hij c)
  · simpa only [U, Nat.sub_zero] using hc
  · intro i
    by_cases hi : i < c
    · have he : c - i = (c - (i + 1)) + 1 := by omega
      change ⁅K, relativeCommutatorSeries K N (c - (i + 1))⁆ ≤
        relativeCommutatorSeries K N (c - i)
      rw [he]
      exact le_rfl
    · have hi' : c - i = 0 := Nat.sub_eq_zero_of_le (by omega)
      have hi'' : c - (i + 1) = 0 := Nat.sub_eq_zero_of_le (by omega)
      simpa only [U, hi', hi'', relativeCommutatorSeries] using
        Subgroup.commutator_le_right K N
  · simpa only [U, Nat.sub_self, relativeCommutatorSeries] using hcent

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_EquivariantCommutatorFiltration
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Linear control of iterated commutators in a normal subgroup

An equivariant homomorphism from a normal subgroup into an additive vector
space sends action commutators to action differences. Vanishing of the
linear action filtration therefore puts the relative commutator series in
the kernel of that homomorphism.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped commutatorElement
variable {G k V : Type} [Group G] [Field k] [AddCommGroup V] [Module k V]

theorem relativeCommutatorSeries_le_linearFiltration
    (K N : Subgroup G) [N.Normal] (ρ : G →* (V ≃ₗ[k] V))
    (π : N →* Multiplicative V)
    (heq : ∀ g : G, ∀ a : N,
      (π (MulAut.conjNormal (H := N) g a)).toAdd = ρ g (π a).toAdd) (n : ℕ) :
    relativeCommutatorSeries K N n ≤
      (linearPreimageSubgroup π (linearActionFiltration
        (fun g : K => (ρ g).toLinearMap - 1) n)).map N.subtype := by
  let D := fun g : K => (ρ g).toLinearMap - 1
  induction n with
  | zero =>
    intro a ha
    refine ⟨⟨a, ha⟩, ?_, rfl⟩
    change (π ⟨a, ha⟩).toAdd ∈ (⊤ : Submodule k V)
    trivial
  | succ n ih =>
    apply Subgroup.commutator_le.mpr
    intro g hg a ha
    obtain ⟨a, hav, rfl⟩ := ih ha
    let b : N := MulAut.conjNormal (H := N) g a * a⁻¹
    have hb : (π b).toAdd = D ⟨g, hg⟩ (π a).toAdd := by
      simp only [b, map_mul, map_inv, toAdd_mul, toAdd_inv, heq]
      change ρ g (π a).toAdd + -(π a).toAdd = ρ g (π a).toAdd - (π a).toAdd
      exact (sub_eq_add_neg _ _).symm
    refine ⟨b, ?_, rfl⟩
    change (π b).toAdd ∈ linearActionFiltration D (n + 1)
    rw [hb]
    exact ActionDepth.generator (D := D) (⟨g, hg⟩ : K) n _ hav

theorem relativeCommutatorSeries_le_kernel_of_linearFiltration
    (K N : Subgroup G) [N.Normal] (ρ : G →* (V ≃ₗ[k] V))
    (π : N →* Multiplicative V)
    (heq : ∀ g : G, ∀ a : N,
      (π (MulAut.conjNormal (H := N) g a)).toAdd = ρ g (π a).toAdd)
    (c : ℕ) (hc : linearActionFiltration (fun g : K => (ρ g).toLinearMap - 1) c = ⊥) :
    relativeCommutatorSeries K N c ≤ π.ker.map N.subtype := by
  intro g hg
  obtain ⟨a, ha, rfl⟩ := relativeCommutatorSeries_le_linearFiltration K N ρ π heq c hg
  refine ⟨a, ?_, rfl⟩
  change (π a).toAdd ∈ linearActionFiltration (fun g : K => (ρ g).toLinearMap - 1) c at ha
  rw [hc, Submodule.mem_bot] at ha
  change π a = 1
  exact Multiplicative.toAdd.injective ha

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_FiniteProjectivePresentations
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite projective covers of finitely generated representations -/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
open scoped MonoidAlgebra
variable {G : Type} [Group G]

theorem chosenIntegralPresentation_finite (A : Rep.{0} ℤ G)
    (hA : IntegralRepresentationFinite G A) :
    IntegralRepresentationFinite G (chosenIntegralPresentation A).p := by
  simp only [chosenIntegralPresentation, dite_eq_left hA]
  exact (finiteIntegralProjectivePresentation_exists A hA).some.finite

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_ChosenIntegralResolution
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A resolution with finitely generated covers whenever available

The initial free term is the regular module. Every subsequent term covers the
kernel of the preceding differential. The chosen presentation retains finite
generation whenever that kernel is finitely generated.
-/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
variable {G : Type} [Group G]

theorem chosenIntegralResolution_step_finite (n : ℕ)
    (h : IntegralRepresentationFinite G
      (kernel ((chosenIntegralResolutionComplex G).d (n + 1) n))) :
    IntegralRepresentationFinite G ((chosenIntegralResolutionComplex G).X (n + 2)) :=
  (chosenIntegralPresentation_finite _ h).of_iso (chosenIntegralResolutionSuccessorIso n).symm

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_InfiniteCyclicFiniteness
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finiteness of the two-term infinite cyclic resolution -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits ZeroObject
open scoped MonoidAlgebra

theorem integralRepresentationFinite_leftRegular (G : Type) [Group G] :
    IntegralRepresentationFinite G (Rep.leftRegular ℤ G) := by
  exact Module.Finite.equiv
    (Representation.ofMulActionSelfAsModuleEquiv (k := ℤ) (G := G)).symm

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_FiniteAugmentationFromFP
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.cyclicTopHomologyInjection_mono _root_.OAI.PolycyclicRecognition.finiteResolution_single_supported _root_.OAI.PolycyclicRecognition.finiteTruncationAugmentation_quasiIso _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalizedGroupIdentityClass_comparison _root_.OAI.PolycyclicRecognition.rationalCoefficientInclusion_apply _root_.OAI.PolycyclicRecognition.resolutionStableSyzygyTransition_class _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # FP one gives a finitely generated augmentation kernel

A resolution comparison expresses the kernel as a sum of two finite images.
The argument does not assume that the group is finitely generated.
-/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits
open scoped MonoidAlgebra
attribute [local instance 2000] Rep.hV2

variable {G : Type} [Group G]

theorem TypeFP.augmentationKernel_fg (hG : TypeFP G 1) :
    (LinearMap.ker (integralRepresentationMap
      (Rep.leftRegularHom (Rep.trivial ℤ G ℤ) 1))).FG := by
  obtain ⟨P, hP⟩ := hG
  let Q := chosenIntegralResolution G
  let e := ProjectiveResolution.homotopyEquiv Q P
  let h := e.homotopyHomInvId.symm
  let F := integralRepresentationMap (e.inv.f 1 ≫ Q.complex.d 1 0)
  let H := integralRepresentationMap (h.hom 0 1 ≫ Q.complex.d 1 0)
  let N := LinearMap.range F ⊔ LinearMap.range H
  have hN : N.FG := by
    apply Submodule.FG.sup
    · have : Module.Finite ℤ[G] (P.complex.X 1).ρ.asModule := hP 1 le_rfl
      simpa only [Submodule.map_top] using
        (Module.Finite.fg_top (R := ℤ[G]) (M := (P.complex.X 1).ρ.asModule)).map F
    · have : Module.Finite ℤ[G] (Q.complex.X 0).ρ.asModule :=
        integralRepresentationFinite_leftRegular G
      simpa only [Submodule.map_top] using
        (Module.Finite.fg_top (R := ℤ[G]) (M := (Q.complex.X 0).ρ.asModule)).map H
  have hπ : Q.π.f 0 = Rep.leftRegularHom (Rep.trivial ℤ G ℤ) 1 := rfl
  change (LinearMap.ker (integralRepresentationMap (Q.π.f 0))).FG
  have hNK : N ≤ LinearMap.ker (integralRepresentationMap (Q.π.f 0)) := by
    apply sup_le <;> rintro _ ⟨a, rfl⟩
    · change integralRepresentationMap (e.inv.f 1 ≫ Q.complex.d 1 0 ≫ Q.π.f 0) a = 0
      rw [Q.complex_d_comp_π_f_zero, comp_zero, integralRepresentationMap_zero]
      rfl
    · change integralRepresentationMap (h.hom 0 1 ≫ Q.complex.d 1 0 ≫ Q.π.f 0) a = 0
      rw [Q.complex_d_comp_π_f_zero, comp_zero, integralRepresentationMap_zero]
      rfl
  have hKN : LinearMap.ker (integralRepresentationMap (Q.π.f 0)) ≤ N := by
    intro z hz
    let z0 : Q.complex.X 0 := (Q.complex.X 0).ρ.asModuleEquiv z
    have hz' : (Q.π.f 0).hom z0 = 0 := hz
    have hcycle : (P.π.f 0).hom ((e.hom.f 0).hom z0) = 0 := by
      have hc := congrArg (fun f => f.hom z0)
        (ProjectiveResolution.lift_commutes_zero (𝟙 (trivialIntegral G)) Q P)
      change (P.π.f 0).hom ((e.hom.f 0).hom z0) = (Q.π.f 0).hom z0 at hc
      exact hc.trans hz'
    obtain ⟨b, hb⟩ := (rep_shortComplex_exact_iff _).mp P.exact₀ _ hcycle
    have hm := h.comm 0
    rw [Homotopy.dNext_zero_chainComplex, prevD_eq _ (by simp : (ComplexShape.down ℕ).Rel 1 0)] at hm
    have hm' := congrArg (fun f => f.hom z0) hm
    change z0 = 0 + (Q.complex.d 1 0).hom ((h.hom 0 1).hom z0) +
      (e.inv.f 0).hom ((e.hom.f 0).hom z0) at hm'
    rw [zero_add] at hm'
    have hmap := congrArg (fun f => f.hom b) (e.inv.comm 1 0)
    change (Q.complex.d 1 0).hom ((e.inv.f 1).hom b) =
      (e.inv.f 0).hom ((P.complex.d 1 0).hom b) at hmap
    rw [hb] at hmap
    apply Submodule.mem_sup.mpr
    refine ⟨F b, ⟨b, rfl⟩, H z, ⟨z, rfl⟩, ?_⟩
    change (Q.complex.d 1 0).hom ((e.inv.f 1).hom b) +
      (Q.complex.d 1 0).hom ((h.hom 0 1).hom z0) = z0
    rw [hmap]
    exact (add_comm _ _).trans hm'.symm
  rw [le_antisymm hKN hNK]
  exact hN

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_FiniteAugmentationKernel
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The augmentation kernel for a finitely generated group

Differences corresponding to a finite group generating set generate the
integral augmentation kernel as a left group-ring module.
-/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
open scoped MonoidAlgebra
variable {G : Type} [Group G]

theorem augmentationDifference_mul (g h : G) :
    augmentationDifference (g * h) = MonoidAlgebra.single g (1 : ℤ) • augmentationDifference h +
      augmentationDifference g := by
  apply (Representation.leftRegular ℤ G).asModuleEquiv.injective
  simp only [map_add, Representation.asModuleEquiv_map_smul,
    Representation.asAlgebraHom_single, one_smul, augmentationDifference,
    LinearEquiv.apply_symm_apply, map_sub, Representation.ofMulAction_single, smul_eq_mul, mul_one]
  abel

theorem augmentationDifference_inv (g : G) :
    augmentationDifference g⁻¹ = -(MonoidAlgebra.single g⁻¹ (1 : ℤ) • augmentationDifference g) := by
  apply (Representation.leftRegular ℤ G).asModuleEquiv.injective
  simp only [map_neg, Representation.asModuleEquiv_map_smul,
    Representation.asAlgebraHom_single, one_smul, augmentationDifference,
    LinearEquiv.apply_symm_apply, map_sub, Representation.ofMulAction_single, smul_eq_mul,
    inv_mul_cancel, mul_one, neg_sub]

theorem augmentationDifference_mem_span {S : Set G} (hS : Subgroup.closure S = ⊤)
    (g : G) :
    augmentationDifference g ∈ Submodule.span ℤ[G] (augmentationDifference '' S) := by
  have hg : g ∈ Subgroup.closure S := by rw [hS]; trivial
  induction hg using Subgroup.closure_induction with
  | mem g hg => exact Submodule.subset_span ⟨g, hg, rfl⟩
  | one => simp [augmentationDifference]
  | mul g h _ _ hg hh =>
    rw [augmentationDifference_mul]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ hh) hg
  | inv g _ hg =>
    rw [augmentationDifference_inv]
    exact Submodule.neg_mem _ (Submodule.smul_mem _ _ hg)

theorem integralAugmentationKernel_fg [Group.FG G] :
    (LinearMap.ker (integralRepresentationMap
      (Rep.leftRegularHom (Rep.trivial ℤ G ℤ) 1))).FG := by
  obtain ⟨S, hS, hfin⟩ := Group.fg_iff.mp (inferInstance : Group.FG G)
  let N := Submodule.span ℤ[G] (augmentationDifference '' S)
  have hsub (x : ℤ[G]) : (Representation.leftRegular ℤ G).asModuleEquiv.symm
      (x - MonoidAlgebra.single 1 (integralAugmentation G x)) ∈ N := by
    induction x using MonoidAlgebra.induction_linear with
    | zero => simp
    | add x y hx hy =>
      simpa only [map_add, MonoidAlgebra.single_add, add_sub_add_comm] using N.add_mem hx hy
    | single g r =>
      have hg := N.smul_mem (MonoidAlgebra.single 1 r) (augmentationDifference_mem_span hS g)
      convert hg using 1
      all_goals try with_reducible_and_instances rfl
      apply (Representation.leftRegular ℤ G).asModuleEquiv.injective
      simp [augmentationDifference,
        integralAugmentation_single, smul_sub]
      rfl
  have hNK : N ≤ LinearMap.ker (integralRepresentationMap
      (Rep.leftRegularHom (Rep.trivial ℤ G ℤ) 1)) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨g, _, rfl⟩
    change integralAugmentation G (MonoidAlgebra.single g (1 : ℤ) - MonoidAlgebra.single 1 (1 : ℤ)) = 0
    simp
  have hKN : LinearMap.ker (integralRepresentationMap
      (Rep.leftRegularHom (Rep.trivial ℤ G ℤ) 1)) ≤ N := by
    intro x hx
    have hx' : integralAugmentation G ((Representation.leftRegular ℤ G).asModuleEquiv x) = 0 := hx
    simpa only [hx', MonoidAlgebra.single_zero, sub_zero,
      LinearEquiv.symm_apply_apply] using hsub ((Representation.leftRegular ℤ G).asModuleEquiv x)
  rw [le_antisymm hKN hNK]
  exact Submodule.fg_span (hfin.image _)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_GroupFiniteGenerationFromFP
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # FP one implies finite generation

The finite supports of augmentation-kernel generators generate the group.
Projection to the permutation module on their left cosets proves this directly.
-/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory
open scoped MonoidAlgebra
attribute [local instance 2000] Rep.hV2

variable {G : Type} [Group G]

theorem integralCosetProjection_support (K : Subgroup G) (c : ℤ[G])
    (hc : ∀ g ∈ c.coeff.support, g ∈ K) :
    (integralCosetProjection K).hom c =
      MonoidAlgebra.single (QuotientGroup.mk 1) (integralAugmentation G c) := by
  classical
  let L := (integralCosetProjection K).hom.toLinearMap -
    (MonoidAlgebra.lsingle (QuotientGroup.mk (1 : G) : G ⧸ K)).comp (integralAugmentation G)
  have hL : L c = 0 := by
    conv_lhs => rw [← MonoidAlgebra.sum_coeff_single c, map_finsuppSum]
    apply Finset.sum_eq_zero
    intro g hg
    have hcoset : (QuotientGroup.mk g : G ⧸ K) = QuotientGroup.mk 1 :=
      QuotientGroup.eq.mpr (by simpa using K.inv_mem (hc g hg))
    change (integralCosetProjection K).hom (MonoidAlgebra.single g (c.coeff g)) -
      MonoidAlgebra.single (QuotientGroup.mk 1)
        (integralAugmentation G (MonoidAlgebra.single g (c.coeff g))) = 0
    rw [integralCosetProjection_single, integralAugmentation_single, hcoset, sub_self]
  exact sub_eq_zero.mp hL

theorem mem_subgroup_of_coset_difference_zero (K : Subgroup G) (g : G)
    (hp : (integralCosetProjection K).hom
      (MonoidAlgebra.single g (1 : ℤ) - MonoidAlgebra.single 1 (1 : ℤ)) = 0) : g ∈ K := by
  classical
  have hsub : MonoidAlgebra.single (QuotientGroup.mk g : G ⧸ K) (1 : ℤ) -
      MonoidAlgebra.single (QuotientGroup.mk 1 : G ⧸ K) (1 : ℤ) = 0 := by
    calc
      _ = (integralCosetProjection K).hom
          (MonoidAlgebra.single g (1 : ℤ) - MonoidAlgebra.single 1 (1 : ℤ)) := by
        rw [map_sub, integralCosetProjection_single, integralCosetProjection_single]
      _ = 0 := hp
  have heq : (QuotientGroup.mk g : G ⧸ K) = QuotientGroup.mk 1 := by
    by_contra hne
    have he := congrArg (fun c : ℤ[G ⧸ K] => c.coeff (QuotientGroup.mk g))
      (sub_eq_zero.mp hsub)
    simp [hne] at he
  have hmem := QuotientGroup.eq.mp heq
  simpa using K.inv_mem hmem

theorem mem_subgroup_of_module_difference_zero (K : Subgroup G) (g : G)
    (hp : augmentationDifference g ∈
      LinearMap.ker (integralRepresentationMap (integralCosetProjection K))) : g ∈ K := by
  apply mem_subgroup_of_coset_difference_zero K g
  exact hp

theorem augmentationDifference_mem_kernel (g : G) :
    augmentationDifference g ∈ LinearMap.ker (integralRepresentationMap
      (Rep.leftRegularHom (Rep.trivial ℤ G ℤ) 1)) := by
  change integralAugmentation G
    (MonoidAlgebra.single g (1 : ℤ) - MonoidAlgebra.single 1 (1 : ℤ)) = 0
  simp

theorem group_fg_of_augmentationKernel_fg
    (hfg : (LinearMap.ker (integralRepresentationMap
      (Rep.leftRegularHom (Rep.trivial ℤ G ℤ) 1))).FG) : Group.FG G := by
  classical
  let A := Rep.leftRegular ℤ G
  obtain ⟨s, hs, hspan⟩ := Submodule.fg_def.mp hfg
  let S : Set G := ⋃ a ∈ s, ((A.ρ.asModuleEquiv a).coeff.support : Set G)
  have hS : S.Finite := hs.biUnion fun a _ => (A.ρ.asModuleEquiv a).coeff.support.finite_toSet
  let K := Subgroup.closure S
  have hgen (a) (ha : a ∈ s) :
      integralRepresentationMap (integralCosetProjection K) a = 0 := by
    have haker : a ∈ LinearMap.ker (integralRepresentationMap
        (Rep.leftRegularHom (Rep.trivial ℤ G ℤ) 1)) := by
      rw [← hspan]
      exact Submodule.subset_span ha
    have hau : integralAugmentation G (A.ρ.asModuleEquiv a) = 0 := haker
    change (integralCosetProjection K).hom (A.ρ.asModuleEquiv a) = 0
    rw [integralCosetProjection_support K _ (fun g hg =>
      Subgroup.subset_closure (Set.mem_iUnion.mpr ⟨a, Set.mem_iUnion.mpr ⟨ha, hg⟩⟩)),
      hau, MonoidAlgebra.single_zero]
  have hker : LinearMap.ker (integralRepresentationMap
      (Rep.leftRegularHom (Rep.trivial ℤ G ℤ) 1)) ≤
      LinearMap.ker (integralRepresentationMap (integralCosetProjection K)) := by
    rw [← hspan]
    exact Submodule.span_le.mpr hgen
  have hK : K = ⊤ := by
    apply top_unique
    intro g _
    exact mem_subgroup_of_module_difference_zero K g
      (hker (augmentationDifference_mem_kernel g))
  exact (Group.fg_iff).mpr ⟨S, hK, hS⟩

theorem TypeFP.fg (hG : TypeFP G 1) : Group.FG G :=
  group_fg_of_augmentationKernel_fg hG.augmentationKernel_fg

theorem TypeFPInfinity.fg (hG : TypeFPInfinity G) : Group.FG G := (hG 1).fg

theorem HasFiniteProjectiveResolution.fg (hG : HasFiniteProjectiveResolution G) :
    Group.FG G := (hG.typeFPInfinity G).fg

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_CyclicDuality
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The cyclic base cases of polycyclic finiteness and duality -/

noncomputable section
namespace PolycyclicRecognition

variable (G : Type) [Group G]

theorem subsingleton_of_finite_torsionFree [Finite G]
    (ht : HasNoNontrivialTorsion G) : Subsingleton G := by
  have hone (g : G) : g = 1 :=
    ht g (orderOf g) (ne_of_gt (orderOf_pos g)) (pow_orderOf_eq_one g)
  exact ⟨fun g h => (hone g).trans (hone h).symm⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_DirectedLowerCentral
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.cyclicTopHomologyInjection_mono _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.normalizedGroupIdentityClass_comparison _root_.OAI.PolycyclicRecognition.rationalCoefficientInclusion_apply _root_.OAI.PolycyclicRecognition.resolutionStableSyzygyTransition_class _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Directed unions with a uniform lower-central bound

The lower-central terms of a directed union are witnessed in its constituent
subgroups. The uniform bound from integral cohomological dimension therefore
allows Zorn's lemma to produce a maximal nilpotent normal subgroup.
-/

namespace PolycyclicRecognition

variable {G : Type} [Group G]

theorem sSup_lowerCentralSeries_le_directedLowerCentral
    (C : Set (Subgroup G)) (hC : C.Nonempty) (hdir : DirectedOn (· ≤ ·) C) (n : ℕ) :
    (sSup C).lowerCentralSeries n ≤ directedLowerCentral C hC hdir n := by
  induction n with
  | zero =>
    intro g hg
    exact (Subgroup.mem_sSup_of_directedOn hC hdir).mp hg
  | succ n ih =>
    rw [Subgroup.lowerCentralSeries_succ]
    apply Subgroup.commutator_le.mpr
    intro x hx y hy
    obtain ⟨H, hH, hxH⟩ := ih hx
    obtain ⟨K, hK, hyK⟩ := (Subgroup.mem_sSup_of_directedOn hC hdir).mp hy
    obtain ⟨L, hL, hHL, hKL⟩ := hdir H hH K hK
    exact ⟨L, hL, Subgroup.commutator_mem_commutator
      (Subgroup.lowerCentralSeries_mono n hHL hxH) (hKL hyK)⟩

theorem sSup_lowerCentralSeries_eq_bot
    (C : Set (Subgroup G)) (hC : C.Nonempty) (hdir : DirectedOn (· ≤ ·) C)
    (n : ℕ) (hn : ∀ H ∈ C, H.lowerCentralSeries n = ⊥) :
    (sSup C).lowerCentralSeries n = ⊥ := by
  apply eq_bot_iff.mpr
  intro g hg
  obtain ⟨H, hH, hgH⟩ := sSup_lowerCentralSeries_le_directedLowerCentral C hC hdir n hg
  simpa only [hn H hH] using hgH

theorem exists_maximal_nilpotent_normal_subgroup
    (hG : HasFiniteIntegralCohomologicalDimension G) :
    ∃ F : Subgroup G, F.Normal ∧ Group.IsNilpotent F ∧
      ∀ N : Subgroup G, N.Normal → Group.IsNilpotent N → F ≤ N → N = F := by
  obtain ⟨d, hd⟩ := hG
  let := hd
  let P : Set (Subgroup G) := {N | N.Normal ∧ Group.IsNilpotent N}
  obtain ⟨F, hF, hmax⟩ := zorn_le₀ P (by
    intro C hC hchain
    rcases C.eq_empty_or_nonempty with rfl | hne
    · exact ⟨⊥, ⟨inferInstance, inferInstance⟩, by simp⟩
    · have hnormal : (sSup C).Normal := Subgroup.sSup_normal C (fun N hN => (hC hN).1)
      have hnil : Group.IsNilpotent (sSup C : Subgroup G) := by
        apply (Subgroup.isNilpotent_iff_lowerCentralSeries (sSup C)).mpr
        refine ⟨2 * d, sSup_lowerCentralSeries_eq_bot C hne hchain.directedOn _ ?_⟩
        intro N hN
        let := (hC hN).2
        exact Subgroup.lowerCentralSeries_eq_bot_of_nilpotencyClass_le
          (nilpotent_subgroup_class_le d N)
      exact ⟨sSup C, ⟨hnormal, hnil⟩, fun N hN => le_sSup hN⟩)
  exact ⟨F, hF.1, hF.2, fun N hn hnil hFN => le_antisymm (hmax ⟨hn, hnil⟩ hFN) hFN⟩

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_CommutingSubgroupProduct
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Products of commuting nilpotent subgroups

Multiplication is a surjective homomorphism from the direct product onto the
join when the two subgroups centralize each other. Nilpotence passes through
this explicit homomorphism.
-/

namespace PolycyclicRecognition

variable {G : Type} [Group G] (H K : Subgroup G)
  (hcomm : ∀ h : H, ∀ k : K, (h : G) * k = (k : G) * h)

theorem commutingProductHom_range : (commutingProductHom H K hcomm).range = H ⊔ K := by
  apply le_antisymm
  · rintro g ⟨⟨h, k⟩, rfl⟩
    exact Subgroup.mul_mem _
      ((show H ≤ H ⊔ K from le_sup_left) h.property)
      ((show K ≤ H ⊔ K from le_sup_right) k.property)
  · apply sup_le
    · intro h hh
      exact ⟨(⟨h, hh⟩, 1), by simp [commutingProductHom]⟩
    · intro k hk
      exact ⟨(1, ⟨k, hk⟩), by simp [commutingProductHom]⟩

include hcomm in
theorem nilpotent_sup_of_commute [Group.IsNilpotent H] [Group.IsNilpotent K] :
    Group.IsNilpotent (H ⊔ K : Subgroup G) := by
  have h := Group.nilpotent_of_surjective (commutingProductHom H K hcomm).rangeRestrict
    (commutingProductHom H K hcomm).rangeRestrict_surjective
  rwa [commutingProductHom_range] at h

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_MaximalNilpotentNormal
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The centralizer of a maximal nilpotent normal subgroup

In a solvable group, a maximal nilpotent normal subgroup contains its own
centralizer. Descend the derived series of that centralizer: if the next term
lies in the maximal subgroup, the current term has class at most two and
centralizes it, so their product contradicts maximality unless it was already
contained. Finite integral cohomological dimension supplies the maximal
subgroup by the uniform nilpotence bound.
-/

namespace PolycyclicRecognition

open scoped commutatorElement

variable {G : Type} [Group G] [Group.IsSolvable G]

theorem centralizer_le_maximal_nilpotent_normal
    (F : Subgroup G) [F.Normal] [Group.IsNilpotent F]
    (hmax : ∀ N : Subgroup G, N.Normal → Group.IsNilpotent N → F ≤ N → N = F) :
    Subgroup.centralizer (F : Set G) ≤ F := by
  let C := Subgroup.centralizer (F : Set G)
  let D (i : ℕ) := (derivedSeries C i).map C.subtype
  have hDC (i : ℕ) : D i ≤ C := by
    rintro g ⟨a, _, rfl⟩
    exact a.property
  have hnormal (i : ℕ) : (D i).Normal := by
    dsimp [D]
    infer_instance
  have hstep (i : ℕ) (hnext : D (i + 1) ≤ F) : D i ≤ F := by
    have hDD : ⁅D i, D i⁆ ≤ F := by
      simpa only [D, derivedSeries_succ, Subgroup.map_commutator] using hnext
    have hcomm : ⁅F, D i⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
        (Subgroup.le_centralizer_iff.mpr (hDC i))
    have hnilD : Group.IsNilpotent (D i) := by
      apply (Subgroup.isNilpotent_iff_lowerCentralSeries (D i)).mpr
      refine ⟨2, eq_bot_iff.mpr ?_⟩
      change ⁅⁅D i, D i⁆, D i⁆ ≤ ⊥
      exact (Subgroup.commutator_mono hDD le_rfl).trans (le_of_eq hcomm)
    let := hnilD
    let := hnormal i
    have hnil : Group.IsNilpotent (F ⊔ D i : Subgroup G) :=
      nilpotent_sup_of_commute F (D i) (fun f d => hDC i d.property f f.property)
    have heq : F ⊔ D i = F := hmax (F ⊔ D i) inferInstance hnil le_sup_left
    exact heq ▸ (show D i ≤ F ⊔ D i from le_sup_right)
  have hback : ∀ k i, D (i + k) ≤ F → D i ≤ F := by
    intro k
    induction k with
    | zero => intro i hi; exact hi
    | succ k ih =>
      intro i hi
      apply hstep
      apply ih (i + 1)
      simpa only [Nat.add_assoc, Nat.add_comm 1 k] using hi
  obtain ⟨m, hm⟩ := Group.IsSolvable.solvable (G := C)
  have hterminal : D (0 + m) ≤ F := by simp only [D, Nat.zero_add, hm, Subgroup.map_bot, bot_le]
  have hzero := hback m 0 hterminal
  simpa only [D, derivedSeries_zero, ← MonoidHom.range_eq_map, Subgroup.range_subtype] using hzero

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_MaximalNilpotentCentralAction
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Detecting the maximal nilpotent normal subgroup by its central factors -/

namespace PolycyclicRecognition

open scoped commutatorElement
variable {G : Type} [Group G]

theorem ambientUpperCentralSeries_mono (F : Subgroup G) :
    Monotone (ambientUpperCentralSeries F) := by
  intro i j hij
  exact Subgroup.map_mono (Subgroup.upperCentralSeries_mono F hij)

theorem ambientUpperCentralSeries_zero (F : Subgroup G) :
    ambientUpperCentralSeries F 0 = ⊥ := by
  simp only [ambientUpperCentralSeries, Subgroup.upperCentralSeries_zero, Subgroup.map_bot]

theorem ambientUpperCentralSeries_top (F : Subgroup G) [Group.IsNilpotent F] :
    ambientUpperCentralSeries F (Group.nilpotencyClass F) = F := by
  simp only [ambientUpperCentralSeries, Subgroup.upperCentralSeries_nilpotencyClass,
    ← MonoidHom.range_eq_map, Subgroup.range_subtype]

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_FinitelyGeneratedLift
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite generation lifts through a surjection

Only finitely many chosen lifts are needed. This does not assert that the
whole inverse image of a finitely generated subgroup is finitely generated.
-/

noncomputable section
namespace PolycyclicRecognition

theorem exists_fg_subgroup_surjective {G A : Type*} [Group G] [Group A]
    [Group.FG A] (q : G →* A) (hq : Function.Surjective q) :
    ∃ H : Subgroup G, H.FG ∧ Function.Surjective (q.comp H.subtype) := by
  obtain ⟨S, hS, hfin⟩ := Group.fg_iff.mp (inferInstance : Group.FG A)
  choose s hs using hq
  let H := Subgroup.closure (s '' S)
  have himage : q '' (s '' S) = S := by
    ext a
    constructor
    · rintro ⟨_, ⟨b, hb, rfl⟩, rfl⟩
      simpa only [hs] using hb
    · intro ha
      exact ⟨s a, ⟨a, ha, rfl⟩, hs a⟩
  have hmap : H.map q = ⊤ := by
    change (Subgroup.closure (s '' S)).map q = ⊤
    rw [MonoidHom.map_closure, himage, hS]
  refine ⟨H, (Subgroup.fg_iff H).mpr ⟨s '' S, rfl, hfin.image s⟩, ?_⟩
  intro a
  have ha : a ∈ H.map q := by rw [hmap]; trivial
  obtain ⟨g, hg, hga⟩ := ha
  exact ⟨⟨g, hg⟩, hga⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_IntegralKernelRepresentation
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The categorical kernel and its concrete group-ring module -/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
open scoped MonoidAlgebra
attribute [local instance 2000] Rep.hV2
attribute [local instance 3000] Submodule.module
variable {G : Type} [Group G] {A B C : Rep.{0} ℤ G}

theorem integralKernel_finite (f : A ⟶ B)
    (h : (LinearMap.ker (integralRepresentationMap f)).FG) :
    IntegralRepresentationFinite G (kernel f) := by
  have : Module.Finite ℤ[G] (LinearMap.ker (integralRepresentationMap f)) := Module.Finite.of_fg h
  have hf : IntegralRepresentationFinite G (integralKernelObject f) :=
    Module.Finite.equiv (integralKernelModuleEquiv f).symm
  exact hf.of_iso (integralKernelIso f)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_ControlledFiniteChains
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite chains at a controlled scale

These submodules retain a finite set of allowed relative positions. They
provide the chain-level control needed for the remaining FP transfer argument.
-/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
variable {R G H : Type} [CommRing R] [Group G] [Group H] {n m : ℕ}

theorem controlledChainSpan_mono {S T : Set G} (h : S ⊆ T) :
    controlledChainSpan R G n S ≤ controlledChainSpan R G n T := by
  apply Submodule.span_mono
  rintro c ⟨x, hx, rfl⟩
  exact ⟨x, fun i j => h (hx i j), rfl⟩

theorem exists_controlledChainScale (c : MonoidAlgebra R (Fin (n + 1) → G)) :
    ∃ S : Set G, S.Finite ∧ c ∈ controlledChainSpan R G n S := by
  induction c using MonoidAlgebra.induction_on with
  | of x =>
    let S := Set.range (fun p : Fin (n + 1) × Fin (n + 1) => (x p.1)⁻¹ * x p.2)
    exact ⟨S, Set.finite_range _, controlledChainSpan_single (fun i j => ⟨(i, j), rfl⟩)⟩
  | add c c' hc hc' =>
    obtain ⟨S, hS, hc⟩ := hc
    obtain ⟨T, hT, hc'⟩ := hc'
    exact ⟨S ∪ T, hS.union hT, Submodule.add_mem _
      (controlledChainSpan_mono Set.subset_union_left hc)
      (controlledChainSpan_mono Set.subset_union_right hc')⟩
  | smul r c hc =>
    obtain ⟨S, hS, hc⟩ := hc
    exact ⟨S, hS, Submodule.smul_mem _ r hc⟩

theorem controlledChainSpan_pushforward (f : G → H) (hf : GroupBornologous f)
    (S : Set G) (hS : S.Finite) :
    ∃ T : Set H, T.Finite ∧ ∀ c ∈ controlledChainSpan R G n S,
      (tupleChainMap (R := R) f).f n c ∈ controlledChainSpan R H n T := by
  obtain ⟨T, hT, hbound⟩ := hf S hS
  refine ⟨T, hT, fun c hc => controlledChainSpan_map ((tupleChainMap f).f n).hom ?_ hc⟩
  intro x hx
  change (tupleChainMap (R := R) f).f n (MonoidAlgebra.single x 1) ∈
    controlledChainSpan R H n T
  rw [tupleChainMap_single]
  exact controlledChainSpan_single (fun i j => hbound _ _ (hx i j))

theorem controlledChainSpan_prism (e e' : GroupCoarseEquivalence G H)
    (hc : (Set.range fun x => (e.toFun x)⁻¹ * e'.toFun x).Finite)
    (S : Set G) (hS : S.Finite) :
    ∃ T : Set H, T.Finite ∧ ∀ c ∈ controlledChainSpan R G n S,
      (tupleChainPrism (R := R) e.toFun e'.toFun).hom n (n + 1) c ∈
        controlledChainSpan R H (n + 1) T := by
  obtain ⟨T, hT, hbound⟩ := controlled_tuplePrism (n := n) e e' hc S hS
  refine ⟨T, hT, fun c hc' =>
    controlledChainSpan_map ((tupleChainPrism e.toFun e'.toFun).hom n (n + 1)).hom ?_ hc'⟩
  intro x hx
  change (tupleChainPrism (R := R) e.toFun e'.toFun).hom n (n + 1)
    (MonoidAlgebra.single x 1) ∈ controlledChainSpan R H (n + 1) T
  rw [tupleChainPrism_single]
  apply Submodule.neg_mem
  apply Submodule.sum_mem
  intro i _
  exact Submodule.smul_mem _ _ (controlledChainSpan_single (hbound x hx i))

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_ControlledCycleFillings
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Coarse invariance of uniformly controlled cycle fillings

Only finite chains occur here. A fixed input scale must admit a fixed filling
scale for every cycle. This quantitative condition is stronger than ordinary
acyclicity of the standard resolution and is the condition needed in the
remaining finiteness argument.
-/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory HomologicalComplex
variable {R G H J : Type} [CommRing R] [Group G] [Group H] [Group J] {n : ℕ}

omit [Group G] in
theorem tupleChainMap_id : tupleChainMap (R := R) (id : G → G) = 𝟙 _ := by
  let F : SimplicialObject Type ⥤ ChainComplex (ModuleCat R) ℕ :=
    (SimplicialObject.whiskering Type (ModuleCat R)).obj (ModuleCat.monoidAlgebraFree R) ⋙
      AlgebraicTopology.alternatingFaceMapComplex (ModuleCat R)
  have h : tupleSimplicialMap (id : G → G) = 𝟙 (tupleSimplicial G) := rfl
  change F.map (tupleSimplicialMap id) = 𝟙 _
  exact (congrArg F.map h).trans (F.map_id _)

omit [Group G] [Group H] [Group J] in
theorem tupleChainMap_comp (f : G → H) (g : H → J) :
    tupleChainMap (R := R) (g ∘ f) = tupleChainMap f ≫ tupleChainMap g := by
  let F : SimplicialObject Type ⥤ ChainComplex (ModuleCat R) ℕ :=
    (SimplicialObject.whiskering Type (ModuleCat R)).obj (ModuleCat.monoidAlgebraFree R) ⋙
      AlgebraicTopology.alternatingFaceMapComplex (ModuleCat R)
  have h : tupleSimplicialMap (g ∘ f) = tupleSimplicialMap f ≫ tupleSimplicialMap g := rfl
  change F.map (tupleSimplicialMap (g ∘ f)) =
    F.map (tupleSimplicialMap f) ≫ F.map (tupleSimplicialMap g)
  exact (congrArg F.map h).trans (F.map_comp _ _)

omit [Group G] [Group H] in
theorem tupleChainMap_cycle (f : G → H) (c : MonoidAlgebra R (Fin (n + 2) → G))
    (hc : (tupleChainComplex R G).d (n + 1) n c = 0) :
    (tupleChainComplex R H).d (n + 1) n ((tupleChainMap f).f (n + 1) c) = 0 := by
  have h := congrArg (fun f => f.hom c) ((tupleChainMap (R := R) f).comm (n + 1) n).symm
  change (tupleChainMap f).f n ((tupleChainComplex R G).d (n + 1) n c) =
    (tupleChainComplex R H).d (n + 1) n ((tupleChainMap f).f (n + 1) c) at h
  rw [hc, map_zero] at h
  exact h.symm

omit [Group G] [Group H] in
theorem tupleChainPrism_cycle (f g : G → H) (c : MonoidAlgebra R (Fin (n + 2) → G))
    (hc : (tupleChainComplex R G).d (n + 1) n c = 0) :
    (tupleChainMap f).f (n + 1) c =
      (tupleChainComplex R H).d (n + 2) (n + 1)
        ((tupleChainPrism f g).hom (n + 1) (n + 2) c) +
      (tupleChainMap g).f (n + 1) c := by
  have h := (tupleChainPrism (R := R) f g).comm (n + 1)
  rw [dNext_eq _ (by simp : (ComplexShape.down ℕ).Rel (n + 1) n),
    prevD_eq _ (by simp : (ComplexShape.down ℕ).Rel (n + 2) (n + 1))] at h
  have hh := congrArg (fun f => f.hom c) h
  change (tupleChainMap f).f (n + 1) c =
    (tupleChainPrism f g).hom n (n + 1) ((tupleChainComplex R G).d (n + 1) n c) +
      (tupleChainComplex R H).d (n + 2) (n + 1)
        ((tupleChainPrism f g).hom (n + 1) (n + 2) c) +
      (tupleChainMap g).f (n + 1) c at hh
  simpa only [hc, map_zero, zero_add] using hh

theorem HasControlledCycleFillings.of_coarse (e : GroupCoarseEquivalence G H)
    (hG : HasControlledCycleFillings R G n) : HasControlledCycleFillings R H n := by
  intro S hS
  obtain ⟨SG, hSG, hback⟩ := controlledChainSpan_pushforward (R := R) (n := n + 1)
    e.invFun e.bornologous_invFun S hS
  obtain ⟨TG, hTG, hfill⟩ := hG SG hSG
  obtain ⟨TH, hTH, hforward⟩ := controlledChainSpan_pushforward (R := R) (n := n + 2)
    e.toFun e.bornologous_toFun TG hTG
  obtain ⟨U, hU, hprism⟩ := controlledChainSpan_prism (R := R) (n := n + 1)
    (GroupCoarseEquivalence.refl H) (e.symm.trans e) e.right_error S hS
  refine ⟨TH ∪ U, hTH.union hU, ?_⟩
  intro c hc hcycle
  obtain ⟨b, hb, hdb⟩ := hfill _ (hback c hc) (tupleChainMap_cycle e.invFun c hcycle)
  let p := (tupleChainPrism (R := R) id (e.toFun ∘ e.invFun)).hom (n + 1) (n + 2) c
  refine ⟨(tupleChainMap e.toFun).f (n + 2) b + p, ?_, ?_⟩
  · exact Submodule.add_mem _
      (controlledChainSpan_mono Set.subset_union_left (hforward b hb))
      (controlledChainSpan_mono Set.subset_union_right (hprism c hc))
  · have hmap := congrArg (fun f => f.hom b)
      ((tupleChainMap (R := R) e.toFun).comm (n + 2) (n + 1)).symm
    change (tupleChainMap e.toFun).f (n + 1)
        ((tupleChainComplex R G).d (n + 2) (n + 1) b) =
      (tupleChainComplex R H).d (n + 2) (n + 1)
        ((tupleChainMap e.toFun).f (n + 2) b) at hmap
    rw [hdb] at hmap
    have hp := tupleChainPrism_cycle (R := R) id (e.toFun ∘ e.invFun) c hcycle
    simp only [tupleChainMap_id, tupleChainMap_comp] at hp
    change c = (tupleChainComplex R H).d (n + 2) (n + 1) p +
      (tupleChainMap e.toFun).f (n + 1) ((tupleChainMap e.invFun).f (n + 1) c) at hp
    rw [map_add, ← hmap]
    exact (add_comm _ _).trans hp.symm

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_ControlledChainRepresentation
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Equivariant control of finite chains

Left translation preserves every relative-position bound. Consequently an
equivariant image of a finitely generated representation lies at one finite
scale in the homogeneous standard chains.
-/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
open scoped MonoidAlgebra
variable {R G : Type} [CommRing R] [Group G] {n : ℕ}

theorem exists_common_controlledChainScale
    {C : Set (MonoidAlgebra R (Fin (n + 1) → G))} (hC : C.Finite) :
    ∃ S : Set G, S.Finite ∧ ∀ c ∈ C, c ∈ controlledChainSpan R G n S := by
  induction C, hC using Set.Finite.induction_on with
  | empty => exact ⟨∅, Set.finite_empty, by simp⟩
  | @insert c C hc hC ih =>
    obtain ⟨S, hS, hc⟩ := exists_controlledChainScale c
    obtain ⟨T, hT, hCT⟩ := ih
    refine ⟨S ∪ T, hS.union hT, ?_⟩
    intro x hx
    rcases hx with rfl | hx
    · exact controlledChainSpan_mono Set.subset_union_left hc
    · exact controlledChainSpan_mono Set.subset_union_right (hCT x hx)

theorem finiteRepresentation_range_controlled (A : Rep ℤ G)
    (hA : IntegralRepresentationFinite G A)
    (f : A ⟶ Rep.ofMulAction ℤ G (Fin (n + 1) → G)) :
    ∃ S : Set G, S.Finite ∧ ∀ a : A, f.hom a ∈ controlledChainSpan ℤ G n S := by
  let : Module ℤ A := A.hV2
  let : Module.Finite ℤ[G] A.ρ.asModule := hA
  obtain ⟨s, hsfin, hs⟩ := Submodule.fg_def.mp (Module.Finite.fg_top (R := ℤ[G])
    (M := A.ρ.asModule))
  obtain ⟨S, hS, hgen⟩ := exists_common_controlledChainScale
    (hsfin.image (fun a => f.hom (A.ρ.asModuleEquiv a)))
  let fM := Representation.IntertwiningMap.equivLinearMapAsModule A.ρ
    (Representation.ofMulAction ℤ G (Fin (n + 1) → G)) f.hom
  let Q := (controlledChainSubrepresentation (R := ℤ) (n := n) S).asSubmodule
  have hle : (⊤ : Submodule ℤ[G] A.ρ.asModule) ≤ Q.comap fM := by
    rw [← hs]
    apply Submodule.span_le.mpr
    intro a ha
    exact hgen _ ⟨a, ha, rfl⟩
  refine ⟨S, hS, fun a => ?_⟩
  exact hle (show A.ρ.asModuleEquiv.symm a ∈ (⊤ : Submodule ℤ[G] A.ρ.asModule)
    from Submodule.mem_top)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_ControlledChainGenerators
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite group-ring generators at a fixed scale

Normalizing the first vertex to the identity leaves only finitely many tuples.
Their translates generate all chains at the chosen scale.
-/

noncomputable section
namespace PolycyclicRecognition
open scoped MonoidAlgebra
variable {R G : Type} [CommRing R] [Group G] {n : ℕ}

theorem finite_normalizedControlledTuples (S : Set G) (hS : S.Finite) :
    {x : Fin (n + 1) → G | IsControlledTuple S x ∧ x 0 = 1}.Finite := by
  apply (Set.Finite.pi' (fun _ : Fin (n + 1) => hS)).subset
  intro x hx i
  simpa only [hx.2, inv_one, one_mul] using hx.1 0 i

theorem controlledChainSubrepresentation_fg (S : Set G) (hS : S.Finite) :
    ((controlledChainSubrepresentation (R := R) (n := n) S).asSubmodule).FG := by
  let ρ := Representation.ofMulAction R G (Fin (n + 1) → G)
  let A := {x : Fin (n + 1) → G | IsControlledTuple S x ∧ x 0 = 1}
  let B : Set ρ.asModule := (fun x => ρ.asModuleEquiv.symm
    (MonoidAlgebra.single x 1)) '' A
  let N : Submodule R[G] ρ.asModule := Submodule.span R[G] B
  have hB : B.Finite := (finite_normalizedControlledTuples S hS).image _
  have hNQ : N ≤ (controlledChainSubrepresentation (R := R) (n := n) S).asSubmodule := by
    apply Submodule.span_le.mpr
    rintro _ ⟨x, hx, rfl⟩
    exact controlledChainSpan_single hx.1
  have hscalar : controlledChainSpan R G n S ≤
      (Subrepresentation.ofSubmodule' N).toSubmodule := by
    apply Submodule.span_le.mpr
    rintro _ ⟨x, hx, rfl⟩
    let y := (x 0)⁻¹ • x
    have hy : y ∈ A := by
      refine ⟨hx.left_translate _, ?_⟩
      simp [y]
    have hmem : ρ.asModuleEquiv.symm (MonoidAlgebra.single y 1) ∈ N :=
      Submodule.subset_span ⟨y, hy, rfl⟩
    have hxy : ρ (x 0) (MonoidAlgebra.single y 1) = MonoidAlgebra.single x 1 := by
      rw [Representation.ofMulAction_single]
      congr 1
      funext i
      simp [y]
    have hm := N.smul_mem (MonoidAlgebra.of R G (x 0)) hmem
    rw [← Representation.asModuleEquiv_symm_map_rho, hxy] at hm
    exact hm
  have hQN : (controlledChainSubrepresentation (R := R) (n := n) S).asSubmodule ≤ N :=
    fun _ hx => hscalar hx
  rw [le_antisymm hQN hNQ]
  exact Submodule.fg_span hB

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_ControlledEquivariantMaps
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Equivariant maps have uniform control on each finite scale -/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
open scoped MonoidAlgebra
variable {G : Type} [Group G] {n m : ℕ}

theorem equivariant_controlledChainImage
    (f : Rep.ofMulAction ℤ G (Fin (n + 1) → G) ⟶
      Rep.ofMulAction ℤ G (Fin (m + 1) → G))
    (S : Set G) (hS : S.Finite) :
    ∃ T : Set G, T.Finite ∧ ∀ c ∈ controlledChainSpan ℤ G n S,
      f.hom c ∈ controlledChainSpan ℤ G m T := by
  let ρ := Representation.ofMulAction ℤ G (Fin (n + 1) → G)
  let σ := Representation.ofMulAction ℤ G (Fin (m + 1) → G)
  let Q := (controlledChainSubrepresentation (R := ℤ) (n := n) S).asSubmodule
  obtain ⟨s, hsfin, hs⟩ := Submodule.fg_def.mp (controlledChainSubrepresentation_fg
    (R := ℤ) (n := n) S hS)
  obtain ⟨T, hT, hgen⟩ := exists_common_controlledChainScale
    (hsfin.image (fun a => f.hom (ρ.asModuleEquiv a)))
  let fM := Representation.IntertwiningMap.equivLinearMapAsModule ρ σ f.hom
  let Q' := (controlledChainSubrepresentation (R := ℤ) (n := m) T).asSubmodule
  have hle : Q ≤ Q'.comap fM := by
    rw [show Q = Submodule.span ℤ[G] s from hs.symm]
    apply Submodule.span_le.mpr
    intro a ha
    exact hgen _ ⟨a, ha, rfl⟩
  exact ⟨T, hT, fun c hc => hle (show ρ.asModuleEquiv.symm c ∈ Q from hc)⟩

theorem standardComplex_boundary_apply
    (c : MonoidAlgebra ℤ (Fin (n + 2) → G)) :
    ((Rep.standardComplex ℤ G).d (n + 1) n).hom c =
      (tupleChainComplex ℤ G).d (n + 1) n c := by
  change ((Rep.standardComplex ℤ G).d (n + 1) n).hom.toLinearMap c = _
  rw [Rep.standardComplex.d_eq, ← tupleChainComplex_boundary_linear]
  rfl

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_ControlledFillingsFromResolution
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.cyclicTopHomologyInjection_mono _root_.OAI.PolycyclicRecognition.finiteResolution_single_supported _root_.OAI.PolycyclicRecognition.finiteTruncationAugmentation_quasiIso _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalizedGroupIdentityClass_comparison _root_.OAI.PolycyclicRecognition.rationalCoefficientInclusion_apply _root_.OAI.PolycyclicRecognition.resolutionStableSyzygyTransition_class _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite resolution terms give uniformly controlled fillings

Comparison with the homogeneous resolution provides the filler. Finite
generation bounds the image of the filling term, and equivariance bounds the
chain homotopy on each input scale.
-/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory HomologicalComplex
variable {G : Type} [Group G] {n : ℕ}

theorem controlledCycleFillings_of_resolution
    (P : ProjectiveResolution (trivialIntegral G))
    (hfin : IntegralRepresentationFinite G (P.complex.X (n + 2))) :
    HasControlledCycleFillings ℤ G n := by
  let Q := Rep.standardResolution ℤ G
  let e := ProjectiveResolution.homotopyEquiv Q P
  let h := e.homotopyHomInvId.symm
  intro S hS
  obtain ⟨T, hT, hα⟩ := finiteRepresentation_range_controlled
    (P.complex.X (n + 2)) hfin (e.inv.f (n + 2))
  obtain ⟨U, hU, hh⟩ := equivariant_controlledChainImage
    (h.hom (n + 1) (n + 2)) S hS
  refine ⟨U ∪ T, hU.union hT, ?_⟩
  intro c hc hcycle
  have hcP : (P.complex.d (n + 1) n).hom ((e.hom.f (n + 1)).hom c) = 0 := by
    have hc' := congrArg (fun f => f.hom c) (e.hom.comm (n + 1) n)
    change (P.complex.d (n + 1) n).hom ((e.hom.f (n + 1)).hom c) =
      (e.hom.f n).hom (((Rep.standardComplex ℤ G).d (n + 1) n).hom c) at hc'
    rw [standardComplex_boundary_apply, hcycle] at hc'
    exact hc'.trans (map_zero (e.hom.f n).hom)
  obtain ⟨b, hb⟩ := (rep_shortComplex_exact_iff _).mp (P.exact_succ n) _ hcP
  refine ⟨(h.hom (n + 1) (n + 2)).hom c + (e.inv.f (n + 2)).hom b, ?_, ?_⟩
  · exact Submodule.add_mem _
      (controlledChainSpan_mono Set.subset_union_left (hh c hc))
      (controlledChainSpan_mono Set.subset_union_right (hα b))
  · have hδ := congrArg (fun f => f.hom b) (e.inv.comm (n + 2) (n + 1))
    change ((Rep.standardComplex ℤ G).d (n + 2) (n + 1)).hom
        ((e.inv.f (n + 2)).hom b) =
      (e.inv.f (n + 1)).hom ((P.complex.d (n + 2) (n + 1)).hom b) at hδ
    rw [hb] at hδ
    have hδ' := (standardComplex_boundary_apply ((e.inv.f (n + 2)).hom b)).symm.trans hδ
    have hm := h.comm (n + 1)
    rw [dNext_eq _ (by simp : (ComplexShape.down ℕ).Rel (n + 1) n),
      prevD_eq _ (by simp : (ComplexShape.down ℕ).Rel (n + 2) (n + 1))] at hm
    have hm' := congrArg (fun f => f.hom c) hm
    change c = (h.hom n (n + 1)).hom
        ((Q.complex.d (n + 1) n).hom c) +
      (Q.complex.d (n + 2) (n + 1)).hom
        ((h.hom (n + 1) (n + 2)).hom c) +
      (e.inv.f (n + 1)).hom ((e.hom.f (n + 1)).hom c) at hm'
    have hz : (Q.complex.d (n + 1) n).hom c = 0 := by
      change ((Rep.standardComplex ℤ G).d (n + 1) n).hom c = 0
      rw [standardComplex_boundary_apply, hcycle]
      rfl
    have hbd : (Q.complex.d (n + 2) (n + 1)).hom
        ((h.hom (n + 1) (n + 2)).hom c) =
        (tupleChainComplex ℤ G).d (n + 2) (n + 1)
          ((h.hom (n + 1) (n + 2)).hom c) :=
      standardComplex_boundary_apply _
    rw [hz, map_zero, zero_add, hbd] at hm'
    let z : MonoidAlgebra ℤ (Fin (n + 3) → G) := (h.hom (n + 1) (n + 2)).hom c
    let w : MonoidAlgebra ℤ (Fin (n + 3) → G) := (e.inv.f (n + 2)).hom b
    let D : MonoidAlgebra ℤ (Fin (n + 3) → G) →ₗ[ℤ]
        MonoidAlgebra ℤ (Fin (n + 2) → G) :=
      ((tupleChainComplex ℤ G).d (n + 2) (n + 1)).hom
    change D (z + w) = c
    rw [D.map_add]
    exact (congrArg (fun t => D z + t)
      hδ').trans hm'.symm

theorem TypeFP.controlledCycleFillings (h : TypeFP G (n + 2)) :
    HasControlledCycleFillings ℤ G n := by
  obtain ⟨P, hP⟩ := h
  exact controlledCycleFillings_of_resolution P (hP (n + 2) le_rfl)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_FiniteKernelsFromFillings
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.cyclicTopHomologyInjection_mono _root_.OAI.PolycyclicRecognition.finiteResolution_single_supported _root_.OAI.PolycyclicRecognition.finiteTruncationAugmentation_quasiIso _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalizedGroupIdentityClass_comparison _root_.OAI.PolycyclicRecognition.rationalCoefficientInclusion_apply _root_.OAI.PolycyclicRecognition.resolutionStableSyzygyTransition_class _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Controlled fillings make the next resolution kernel finite

The kernel is the sum of two finite images: controlled fillers mapped back
from homogeneous chains, and the comparison homotopy applied to the finite
resolution term. This proves finite generation without assuming noetherianity
of the group ring.
-/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
open scoped MonoidAlgebra
attribute [local instance 2000] Rep.hV2
variable {G : Type} [Group G] {n : ℕ}

theorem resolution_comp_range_le_kernel
    (P : ProjectiveResolution (trivialIntegral G)) {A : Rep.{0} ℤ G}
    (f : A ⟶ P.complex.X (n + 2)) :
    LinearMap.range (integralRepresentationMap (f ≫ P.complex.d (n + 2) (n + 1))) ≤
      LinearMap.ker (integralRepresentationMap (P.complex.d (n + 1) n)) := by
  rintro _ ⟨a, rfl⟩
  change integralRepresentationMap (f ≫ P.complex.d (n + 2) (n + 1) ≫
    P.complex.d (n + 1) n) a = 0
  rw [P.complex.d_comp_d, comp_zero, integralRepresentationMap_zero]
  rfl

theorem finite_resolution_kernel_of_controlledFillings
    (P : ProjectiveResolution (trivialIntegral G))
    (hfin : IntegralRepresentationFinite G (P.complex.X (n + 1)))
    (hfill : HasControlledCycleFillings ℤ G n) :
    (LinearMap.ker (integralRepresentationMap (P.complex.d (n + 1) n))).FG := by
  let Q := Rep.standardResolution ℤ G
  let e := ProjectiveResolution.homotopyEquiv P Q
  let h := e.homotopyHomInvId.symm
  obtain ⟨S, hS, hα⟩ := finiteRepresentation_range_controlled
    (P.complex.X (n + 1)) hfin (e.hom.f (n + 1))
  obtain ⟨T, hT, hTfill⟩ := hfill S hS
  let F := integralRepresentationMap
    (e.inv.f (n + 2) ≫ P.complex.d (n + 2) (n + 1))
  let H := integralRepresentationMap
    (h.hom (n + 1) (n + 2) ≫ P.complex.d (n + 2) (n + 1))
  let C := (controlledChainSubrepresentation (R := ℤ) (n := n + 2) T).asSubmodule
  let N := C.map F ⊔ LinearMap.range H
  have hN : N.FG := by
    apply Submodule.FG.sup
    · exact (controlledChainSubrepresentation_fg T hT).map F
    · have : Module.Finite ℤ[G] (P.complex.X (n + 1)).ρ.asModule := hfin
      simpa only [Submodule.map_top] using
        (Module.Finite.fg_top (R := ℤ[G]) (M := (P.complex.X (n + 1)).ρ.asModule)).map H
  have hNK : N ≤ LinearMap.ker (integralRepresentationMap (P.complex.d (n + 1) n)) := by
    apply sup_le
    · exact (Submodule.map_mono le_top).trans
        (by simpa only [Submodule.map_top] using
          resolution_comp_range_le_kernel P (e.inv.f (n + 2)))
    · exact resolution_comp_range_le_kernel P (h.hom (n + 1) (n + 2))
  have hKN : LinearMap.ker (integralRepresentationMap (P.complex.d (n + 1) n)) ≤ N := by
    intro z hz
    have hz' : (P.complex.d (n + 1) n).hom z = 0 := hz
    have hcycle : (tupleChainComplex ℤ G).d (n + 1) n ((e.hom.f (n + 1)).hom z) = 0 := by
      have hc := congrArg (fun f => f.hom z) (e.hom.comm (n + 1) n)
      change (Q.complex.d (n + 1) n).hom ((e.hom.f (n + 1)).hom z) =
        (e.hom.f n).hom ((P.complex.d (n + 1) n).hom z) at hc
      rw [hz', map_zero] at hc
      exact (standardComplex_boundary_apply _).symm.trans hc
    obtain ⟨b, hb, hdb⟩ := hTfill _ (hα z) hcycle
    have hm := h.comm (n + 1)
    rw [dNext_eq _ (by simp : (ComplexShape.down ℕ).Rel (n + 1) n),
      prevD_eq _ (by simp : (ComplexShape.down ℕ).Rel (n + 2) (n + 1))] at hm
    have hm' := congrArg (fun f => f.hom z) hm
    change z = (h.hom n (n + 1)).hom ((P.complex.d (n + 1) n).hom z) +
      (P.complex.d (n + 2) (n + 1)).hom ((h.hom (n + 1) (n + 2)).hom z) +
      (e.inv.f (n + 1)).hom ((e.hom.f (n + 1)).hom z) at hm'
    rw [hz', map_zero, zero_add] at hm'
    have hmap := congrArg (fun f => f.hom b) (e.inv.comm (n + 2) (n + 1))
    change (P.complex.d (n + 2) (n + 1)).hom ((e.inv.f (n + 2)).hom b) =
      (e.inv.f (n + 1)).hom ((Q.complex.d (n + 2) (n + 1)).hom b) at hmap
    have hdb' : (Q.complex.d (n + 2) (n + 1)).hom b = (e.hom.f (n + 1)).hom z :=
      (standardComplex_boundary_apply b).trans hdb
    rw [hdb'] at hmap
    apply Submodule.mem_sup.mpr
    refine ⟨F b, ?_, H z, ⟨z, rfl⟩, ?_⟩
    · exact ⟨b, hb, rfl⟩
    · change (P.complex.d (n + 2) (n + 1)).hom ((e.inv.f (n + 2)).hom b) +
        (P.complex.d (n + 2) (n + 1)).hom ((h.hom (n + 1) (n + 2)).hom z) = z
      rw [hmap]
      exact (add_comm _ _).trans hm'.symm
  rw [le_antisymm hKN hNK]
  exact hN

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_FinitenessFromControlledFillings
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.cyclicTopHomologyInjection_mono _root_.OAI.PolycyclicRecognition.finiteResolution_single_supported _root_.OAI.PolycyclicRecognition.finiteTruncationAugmentation_quasiIso _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finiteness from uniformly controlled fillings

Finite group generation supplies the first augmentation kernel. Each further
kernel is finite by the controlled-filling comparison, so the chosen projective
cover remains finite through the required degree.
-/

noncomputable section
namespace PolycyclicRecognition
variable {G : Type} [Group G] [Group.FG G]

theorem typeFP_of_controlledCycleFillings (m : ℕ)
    (hfill : ∀ n, n + 2 ≤ m → HasControlledCycleFillings ℤ G n) : TypeFP G m := by
  have hfin : ∀ i, i ≤ m →
      IntegralRepresentationFinite G ((chosenIntegralResolution G).complex.X i) := by
    intro i
    induction i using Nat.strong_induction_on with
    | h i ih =>
      intro him
      rcases i with _ | (_ | n)
      · exact integralRepresentationFinite_leftRegular G
      · exact chosenIntegralPresentation_finite _
          (integralKernel_finite (integralFreeAugmentation (G := G)) integralAugmentationKernel_fg)
      · apply chosenIntegralResolution_step_finite
        apply integralKernel_finite
        exact finite_resolution_kernel_of_controlledFillings (chosenIntegralResolution G)
          (ih (n + 1) (by omega) (by omega)) (hfill n (by omega))
  exact ⟨chosenIntegralResolution G, hfin⟩

omit [Group.FG G] in
theorem TypeFP.mono {m n : ℕ} (h : TypeFP G n) (hmn : m ≤ n) : TypeFP G m := by
  obtain ⟨P, hP⟩ := h
  exact ⟨P, fun i hi => hP i (hi.trans hmn)⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_CoarsePoincareDuality
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The cohomological part of Poincare duality transfer

Coarse invariance supplies the vanishing and the integral top class. Existence
of a finite projective resolution is a separate algebraic finiteness obligation.
-/

namespace PolycyclicRecognition
open CategoryTheory
variable {G H : Type} [Group G] [Group H]

theorem poincareDuality_of_coarse_finiteResolution (e : GroupCoarseEquivalence G H)
    (hfin : HasFiniteProjectiveResolution H) {n : ℕ}
    (hG : IsIntegralPoincareDualityGroup G n) : IsIntegralPoincareDualityGroup H n := by
  refine ⟨hfin, ?_, ?_⟩
  · intro i hi
    exact (hG.2.1 i hi).of_iso (coarseGroupRingCohomologyIso (R := ℤ) e i).symm
  · obtain ⟨top⟩ := hG.2.2
    exact ⟨(coarseGroupRingCohomologyIso (R := ℤ) e n).symm ≪≫ top⟩

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_LiDualityFromFiniteness
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Deriving the duality transfer from finiteness transfer

The cohomology comparison is proved by controlled cochains. Canonical
truncation supplies a finite projective resolution once FP infinity and finite
cohomological dimension are known. Thus the application of Li, Corollary 4.48,
requires no independent hypothesis beyond the Corollary 4.47 finiteness transfer.
-/

namespace PolycyclicRecognition

theorem liDualityInput_of_finiteness (liFP : LiFinitenessInput) : LiDualityInput := by
  intro Γ H _ _ _ _ e _ hcd n hPD
  have hfp : TypeFPInfinity H := fun k => liFP Γ H e k (hPD.typeFPInfinity Γ k)
  exact poincareDuality_of_coarse_finiteResolution e
    (finiteProjectiveResolution_of_finiteDimension_typeFP hcd hfp) hPD

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_CoarseFiniteness
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Coarse invariance of integral FP finiteness

The proof transfers uniform fillings and constructs finite projective covers.
It does not assume homology with product coefficients or an FP recognition
criterion.
-/

namespace PolycyclicRecognition

theorem liFinitenessInput : LiFinitenessInput := by
  intro Γ H _ _ _ _ e m hΓ
  apply typeFP_of_controlledCycleFillings m
  intro n hn
  exact ((hΓ.mono hn).controlledCycleFillings).of_coarse e

/-- Integral Poincaré duality transfers once both cohomological dimensions
are finite, using the proved FP transfer and controlled cochain comparison. -/
theorem liDualityInput : LiDualityInput :=
  liDualityInput_of_finiteness liFinitenessInput

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_PolycyclicFiniteGeneration
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finite_templateSymmetryGroup _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteSubtypeLinearEquivRealIdMemSubgroupLinearSupportSymmetryGroup _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite generation of the lattice comparison groups

A cyclic series supplies finite generators at every step. This removes a
separate finite-generation premise when a published lattice theorem gives
polycyclicity.
-/

namespace PolycyclicRecognition

open ChromaticCyclic

variable {G : Type*} [Group G]

/-- A generator of a cyclic group is a finite generating set. -/
theorem finitelyGenerated_of_isCyclic [IsCyclic G] : Group.FG G := by
  obtain ⟨g, hg⟩ := isCyclic_iff_exists_zpowers_eq_top.mp (inferInstance : IsCyclic G)
  exact Group.fg_iff.mpr ⟨{g}, by simpa only [← Subgroup.zpowers_eq_closure] using hg,
    Set.finite_singleton g⟩

/-- Finite generation passes along a concrete cyclic extension. -/
theorem finitelyGenerated_of_cyclicStep {H K : Subgroup G} (s : CyclicStep H K)
    (hH : Group.FG H) : Group.FG K := by
  let := hH
  let := s.normal
  let := s.cyclic
  let e := (Subgroup.subgroupOfEquivOfLe s.le).symm
  let : Group.FG (H.subgroupOf K) :=
    Group.fg_of_surjective (f := e.toMonoidHom) e.surjective
  let : Group.FG (K ⧸ H.subgroupOf K) := finitelyGenerated_of_isCyclic
  let q := QuotientGroup.mk' (H.subgroupOf K)
  let : Group.FG q.ker := by
    change Group.FG (QuotientGroup.mk' (H.subgroupOf K)).ker
    rw [QuotientGroup.ker_mk']
    infer_instance
  exact CriticalPercolation.fg_of_kernel_quotient q (QuotientGroup.mk'_surjective _)

/-- The top group of a cyclic series is finitely generated when its initial
group is finitely generated. -/
theorem finitelyGenerated_of_cyclicSeries {H K : Subgroup G} {n : ℕ}
    (c : CyclicSeries H K n) (hH : Group.FG H) : Group.FG K := by
  have hm : ∀ i, i ≤ n → Group.FG (c.group i) := by
    intro i
    induction i with
    | zero => intro _; rw [c.first]; exact hH
    | succ i ih =>
      intro hi
      exact finitelyGenerated_of_cyclicStep (c.step i (by omega)) (ih (by omega))
  rw [← c.last]
  exact hm n le_rfl

/-- Every polycyclic group is finitely generated. -/
theorem IsPolycyclic.finitelyGenerated (hG : IsPolycyclic G) : Group.FG G := by
  obtain ⟨n, ⟨c⟩⟩ := hG
  let : Group.FG (⊤ : Subgroup G) := finitelyGenerated_of_cyclicSeries c inferInstance
  exact Group.fg_of_surjective (f := (⊤ : Subgroup G).subtype)
    (by intro g; exact ⟨⟨g, trivial⟩, rfl⟩)

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_CharacteristicFiniteIndex
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Characteristic finite-index refinements

A finite-index subgroup of a finitely generated group contains a
characteristic finite-index subgroup. We intersect kernels of maps into the
finite permutation group on its cosets. This is the finite-index refinement
needed in the induction proving virtual torsion freeness.
-/

noncomputable section
namespace PolycyclicRecognition

variable {G F : Type*} [Group G] [Group F]

theorem finite_hom_of_finitelyGenerated [Group.FG G] [Finite F] :
    Finite (G →* F) := by
  obtain ⟨S, hS, hfin⟩ := Group.fg_iff.mp (inferInstance : Group.FG G)
  let : Finite S := hfin
  exact Finite.of_injective (fun f : G →* F => fun s : S => f s) (by
    intro f g h
    apply MonoidHom.eq_of_eqOn_dense hS
    intro s hs
    exact congrFun h ⟨s, hs⟩)

theorem finiteTargetKernel_characteristic : (finiteTargetKernel G F).Characteristic := by
  apply Subgroup.characteristic_iff_le_comap.mpr
  intro e g hg
  change e g ∈ finiteTargetKernel G F
  simp only [finiteTargetKernel, Subgroup.mem_iInf, MonoidHom.mem_ker] at hg ⊢
  intro f
  exact hg (f.comp e.toMonoidHom)

theorem finiteTargetKernel_finiteIndex [Group.FG G] [Finite F] :
    (finiteTargetKernel G F).FiniteIndex := by
  let : Finite (G →* F) := finite_hom_of_finitelyGenerated
  apply Subgroup.finiteIndex_iInf
  intro f
  change ((⊥ : Subgroup F).comap f).FiniteIndex
  infer_instance

theorem exists_characteristic_finiteIndex_le [Group.FG G]
    (H : Subgroup G) [H.FiniteIndex] :
    ∃ K : Subgroup G, K ≤ H ∧ K.Characteristic ∧ K.FiniteIndex := by
  let F := Equiv.Perm (G ⧸ H)
  refine ⟨finiteTargetKernel G F, ?_, finiteTargetKernel_characteristic,
    finiteTargetKernel_finiteIndex⟩
  intro g hg
  have he : MulAction.toPermHom G (G ⧸ H) g = 1 :=
    (Subgroup.mem_iInf.mp hg (MulAction.toPermHom G (G ⧸ H)))
  have hx := congrArg (fun e : Equiv.Perm (G ⧸ H) => e (QuotientGroup.mk g⁻¹)) he
  change QuotientGroup.mk (g * g⁻¹) = QuotientGroup.mk g⁻¹ at hx
  rw [mul_inv_cancel] at hx
  simpa using (QuotientGroup.eq.mp hx.symm)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_TorsionFreeCyclicExtension
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Virtual torsion freeness across a cyclic extension

The finite-index subgroup of the kernel is first made characteristic. For an
infinite cyclic quotient, lift its generator and take the subgroup generated
by that lift and the characteristic subgroup. Its torsion lies in the kernel,
where torsion freeness is already known.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped Pointwise

variable {G : Type} [Group G]

theorem HasNoNontrivialTorsion.of_injective {J : Type} [Group J]
    (h : HasNoNontrivialTorsion G) (f : J →* G) (hf : Function.Injective f) :
    HasNoNontrivialTorsion J := by
  intro g n hn hg
  apply hf
  rw [map_one]
  exact h (f g) n hn (by rw [← map_pow, hg, map_one])

/-- A finite-index subgroup of the kernel gives finitely many cosets whenever
the chosen subgroup surjects onto the quotient. No normality of `H` is needed. -/
theorem finiteIndex_of_kernel_cover (N : Subgroup G) [N.Normal]
    (K : Subgroup N) [K.FiniteIndex] (H : Subgroup G)
    (hKH : K.map N.subtype ≤ H)
    (hcover : ∀ g : G, ∃ h ∈ H, (QuotientGroup.mk' N) h = (QuotientGroup.mk' N) g) :
    H.FiniteIndex := by
  let f : N ⧸ K → G ⧸ H := Quotient.map' (fun n : N => (n : G)) (by
    intro a b hab
    rw [QuotientGroup.leftRel_apply] at hab ⊢
    exact hKH (Subgroup.mem_map.mpr ⟨a⁻¹ * b, hab, rfl⟩))
  have hf : Function.Surjective f := by
    intro x
    obtain ⟨g, rfl⟩ := Quotient.mk''_surjective x
    obtain ⟨h, hh, he⟩ := hcover g
    have hn : g * h⁻¹ ∈ N := by
      apply (QuotientGroup.eq_one_iff _).mp
      change (QuotientGroup.mk' N) (g * h⁻¹) = 1
      rw [map_mul, map_inv, he, mul_inv_cancel]
    refine ⟨QuotientGroup.mk (⟨g * h⁻¹, hn⟩ : N), ?_⟩
    change QuotientGroup.mk (g * h⁻¹) = QuotientGroup.mk g
    apply QuotientGroup.eq.mpr
    simpa [mul_assoc] using hh
  let : Finite (G ⧸ H) := Finite.of_surjective f hf
  exact Subgroup.finiteIndex_of_finite_quotient

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_PolyZ
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Cyclic series with torsion-free factors

Trivial factors are allowed. Removing them gives the usual poly-Z series.
The predicate records an actual series and is stable under subgroups.
-/

noncomputable section
namespace PolycyclicRecognition

open ChromaticCyclic

variable {G J : Type} [Group G] [Group J]

theorem TorsionFreeCyclicFactors.comap {H K : Subgroup G} {n : ℕ}
    {c : CyclicSeries H K n} (hc : TorsionFreeCyclicFactors c) (f : J →* G) :
    TorsionFreeCyclicFactors (c.comap f) := by
  dsimp only [TorsionFreeCyclicFactors, CyclicSeries.comap]
  intro i hi
  let := (c.step i hi).normal
  let := (c.step i hi).normal_comap f
  exact (hc i hi).of_injective ((c.step i hi).factorComap f)
    ((c.step i hi).factorComap_injective f)

theorem IsPolyZ.of_injective (h : IsPolyZ G) (f : J →* G)
    (hf : Function.Injective f) : IsPolyZ J := by
  obtain ⟨n, c, hc⟩ := h
  let d := c.comap f
  let d' : CyclicSeries (⊥ : Subgroup J) ⊤ n :=
    { d with
      first := by
        simpa only [MonoidHom.comap_bot, (MonoidHom.ker_eq_bot_iff f).mpr hf] using d.first
      last := by simpa only [Subgroup.comap_top] using d.last }
  exact ⟨n, d', hc.comap f⟩

theorem IsPolyZ.of_equiv (h : IsPolyZ G) (e : G ≃* J) : IsPolyZ J :=
  h.of_injective e.symm.toMonoidHom e.symm.injective

theorem isPolyZ_of_subsingleton [Subsingleton G] : IsPolyZ G := by
  let c : CyclicSeries (⊥ : Subgroup G) ⊤ 0 :=
    { CyclicSeries.refl (⊥ : Subgroup G) with last := Subsingleton.elim _ _ }
  exact ⟨0, c, by intro i hi; omega⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_PolyZExtension
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Extending a torsion-free cyclic series by one cyclic quotient -/

noncomputable section
namespace PolycyclicRecognition

open ChromaticCyclic
variable {G J : Type} [Group G] [Group J]

theorem cyclicStep_factorMap_injective {H K : Subgroup G} (s : CyclicStep H K)
    (f : G →* J) (hf : Function.Injective f) :
    letI := s.normal
    letI := s.normal_map f
    Function.Injective (s.factorMap f) := by
  let := s.normal
  let := s.normal_map f
  apply (s.factorMap f).ker_eq_bot_iff.mp
  apply le_antisymm ?_ bot_le
  intro x hx
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ x
  change (↑(⟨f x.val, Subgroup.mem_map.mpr ⟨x, x.property, rfl⟩⟩ : K.map f) :
    K.map f ⧸ (H.map f).subgroupOf (K.map f)) = 1 at hx
  have hm := (QuotientGroup.eq_one_iff
    (⟨f x.val, Subgroup.mem_map.mpr ⟨x, x.property, rfl⟩⟩ : K.map f)).mp hx
  obtain ⟨y, hy, he⟩ := hm
  have hxy : y = x.val := hf he
  change (↑x : K ⧸ H.subgroupOf K) = 1
  apply (QuotientGroup.eq_one_iff _).mpr
  change (x : G) ∈ H
  rw [← hxy]
  exact hy

theorem TorsionFreeCyclicFactors.map {H K : Subgroup G} {n : ℕ}
    {c : CyclicSeries H K n} (hc : TorsionFreeCyclicFactors c)
    (f : G →* J) (hf : Function.Injective f) : TorsionFreeCyclicFactors (c.map f) := by
  dsimp only [TorsionFreeCyclicFactors, CyclicSeries.map]
  intro i hi
  let := (c.step i hi).normal
  let := (c.step i hi).normal_map f
  let e := MulEquiv.ofBijective ((c.step i hi).factorMap f)
    ⟨cyclicStep_factorMap_injective (c.step i hi) f hf,
      (c.step i hi).factorMap_surjective f⟩
  exact (hc i hi).of_injective e.symm.toMonoidHom e.symm.injective

theorem cyclicStep_torsionFree_congr {H K H' K' : Subgroup G}
    (s : CyclicStep H K) (t : CyclicStep H' K') (hH : H = H') (hK : K = K') :
    (letI := s.normal; HasNoNontrivialTorsion (K ⧸ H.subgroupOf K)) ↔
      (letI := t.normal; HasNoNontrivialTorsion (K' ⧸ H'.subgroupOf K')) := by
  subst H'
  subst K'
  rfl

theorem TorsionFreeCyclicFactors.snoc {H K L : Subgroup G} {n : ℕ}
    {c : CyclicSeries H K n} (hc : TorsionFreeCyclicFactors c) (s : CyclicStep K L)
    (hs : letI := s.normal; HasNoNontrivialTorsion (L ⧸ K.subgroupOf L)) :
    TorsionFreeCyclicFactors (cyclicSeriesSnoc c s) := by
  intro i hi
  by_cases h : i < n
  · have h₀ : (cyclicSeriesSnoc c s).group i = c.group i :=
      ite_eq_left (by omega)
    have h₁ : (cyclicSeriesSnoc c s).group (i + 1) = c.group (i + 1) :=
      ite_eq_left (by omega)
    exact (cyclicStep_torsionFree_congr ((cyclicSeriesSnoc c s).step i hi)
      (c.step i h) h₀ h₁).mpr (hc i h)
  · have he : i = n := by omega
    subst i
    have h₀ : (cyclicSeriesSnoc c s).group n = K := by
      change (if n ≤ n then c.group n else L) = K
      rw [ite_eq_left le_rfl, c.last]
    have h₁ : (cyclicSeriesSnoc c s).group (n + 1) = L := ite_eq_right (by omega)
    exact (cyclicStep_torsionFree_congr ((cyclicSeriesSnoc c s).step n hi)
      s h₀ h₁).mpr hs

theorem isPolyZ_of_normal_cyclic_quotient (N : Subgroup G) [N.Normal]
    [IsCyclic (G ⧸ N)] (hN : IsPolyZ N)
    (hQ : HasNoNontrivialTorsion (G ⧸ N)) : IsPolyZ G := by
  obtain ⟨n, c, hc⟩ := hN
  let d := c.map N.subtype
  let d' : CyclicSeries (⊥ : Subgroup G) N n :=
    { d with
      first := by simpa only [Subgroup.map_bot] using d.first
      last := by simpa only [← MonoidHom.range_eq_map, N.range_subtype] using d.last }
  let s : CyclicStep N ⊤ := by
    have hbot : (⊥ : Subgroup (G ⧸ N)).comap (QuotientGroup.mk' N) = N := by
      rw [MonoidHom.comap_bot, QuotientGroup.ker_mk']
    simpa only [hbot, Subgroup.comap_top] using
      (CyclicStep.bot (⊤ : Subgroup (G ⧸ N))).comap (QuotientGroup.mk' N)
  let := s.normal
  have hs : HasNoNontrivialTorsion ((⊤ : Subgroup G) ⧸ N.subgroupOf ⊤) := by
    let f : (⊤ : Subgroup G) ⧸ N.subgroupOf ⊤ →* G ⧸ N :=
      QuotientGroup.map _ _ (⊤ : Subgroup G).subtype (by intro x hx; exact hx)
    have hf : Function.Injective f := by
      apply f.ker_eq_bot_iff.mp
      apply le_antisymm ?_ bot_le
      intro x hx
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ x
      change QuotientGroup.mk' N (x : G) = 1 at hx
      exact (QuotientGroup.eq_one_iff x).mpr ((QuotientGroup.eq_one_iff (x : G)).mp hx)
    exact hQ.of_injective f hf
  have hd : TorsionFreeCyclicFactors d' := hc.map N.subtype N.subtype_injective
  exact ⟨n + 1, cyclicSeriesSnoc d' s, hd.snoc s hs⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_PolyZFiniteIndex
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite-index poly-Z subgroups of polycyclic groups -/

noncomputable section
namespace PolycyclicRecognition

open scoped Pointwise
open ChromaticCyclic
variable {G : Type} [Group G]

theorem infiniteCyclic_torsionFree [IsCyclic G] [Infinite G] :
    HasNoNontrivialTorsion G := by
  have ht : HasNoNontrivialTorsion (Multiplicative ℤ) := by
    intro g n hn hg
    apply Multiplicative.toAdd.injective
    change g.toAdd = 0
    have h : (n : ℤ) * g.toAdd = 0 := by
      simpa using congrArg Multiplicative.toAdd hg
    exact (mul_eq_zero.mp h).resolve_left (by exact_mod_cast hn)
  exact ht.of_injective (intCyclicMulEquiv.symm.toMonoidHom) intCyclicMulEquiv.symm.injective

theorem polyZ_finiteIndex_of_cyclic_extension
    (N : Subgroup G) [N.Normal] [Group.FG N] [IsCyclic (G ⧸ N)]
    (hN : ∃ L : Subgroup N, L.FiniteIndex ∧ IsPolyZ L) :
    ∃ H : Subgroup G, H.FiniteIndex ∧ IsPolyZ H := by
  obtain ⟨L, hLi, hLz⟩ := hN
  let := hLi
  obtain ⟨K, hKL, hKc, hKi⟩ := exists_characteristic_finiteIndex_le L
  let := hKc
  let := hKi
  have hKz : IsPolyZ K := hLz.of_injective (Subgroup.inclusion hKL)
    (Subgroup.inclusion_injective hKL)
  let A : Subgroup G := K.map N.subtype
  have hAz : IsPolyZ A := hKz.of_equiv (K.equivMapOfInjective N.subtype N.subtype_injective)
  let q := QuotientGroup.mk' N
  have hAq : A ≤ q.ker := by
    rintro a ⟨k, hk, rfl⟩
    change q k = 1
    exact (QuotientGroup.eq_one_iff (k : G)).mpr k.property
  cases finite_or_infinite (G ⧸ N) with
  | inl hfin =>
    let := hfin
    let : N.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
    have hAi : A.FiniteIndex := ⟨by
      change (K.map N.subtype).index ≠ 0
      rw [Subgroup.index_map_subtype]
      exact mul_ne_zero hKi.index_ne_zero (Subgroup.FiniteIndex.index_ne_zero (H := N))⟩
    exact ⟨A, hAi, hAz⟩
  | inr hinf =>
    let := hinf
    obtain ⟨z, hz⟩ := isCyclic_iff_exists_zpowers_eq_top.mp
      (inferInstance : IsCyclic (G ⧸ N))
    obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective N z
    have hz0 : orderOf z = 0 := orderOf_eq_card_of_zpowers_eq_top hz
      |>.trans (Nat.card_eq_zero_of_infinite)
    have hzinj : Function.Injective (fun k : ℤ => z ^ k) :=
      injective_zpow_iff_not_isOfFinOrder.mpr (orderOf_eq_zero_iff.mp hz0)
    let H : Subgroup G := A ⊔ Subgroup.zpowers g
    have hHi : H.FiniteIndex := finiteIndex_of_kernel_cover N K H le_sup_left (by
      intro x
      have hx : q x ∈ Subgroup.zpowers z := hz.ge (Subgroup.mem_top _)
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hx
      refine ⟨g ^ k, (show Subgroup.zpowers g ≤ H from le_sup_right)
        (Subgroup.zpow_mem_zpowers g k), ?_⟩
      change q (g ^ k) = q x
      rw [map_zpow, hg, hk])
    have hker (x : H) (hx : q (x : G) = 1) : (x : G) ∈ A := by
      have hmem : (x : G) ∈ (A : Set G) * (Subgroup.zpowers g : Set G) := by
        rw [← Subgroup.normal_mul]
        exact x.property
      obtain ⟨a, ha, b, hb, hab⟩ := hmem
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
      have he : z ^ k = z ^ (0 : ℤ) := by
        rw [zpow_zero, ← hx, ← hab, map_mul, hAq ha, one_mul, map_zpow, hg]
      have hk : k = 0 := hzinj he
      have hxa : (x : G) = a := by simpa [hk] using hab.symm
      rwa [hxa]
    let A' : Subgroup H := A.subgroupOf H
    let f : H ⧸ A' →* G ⧸ N :=
      QuotientGroup.lift A' (q.comp H.subtype) (by
        intro x hx
        exact hAq hx)
    have hf : Function.Injective f := by
      apply f.ker_eq_bot_iff.mp
      apply le_antisymm ?_ bot_le
      intro x hx
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective A' x
      exact (QuotientGroup.eq_one_iff x).mpr (hker x hx)
    let : IsCyclic (H ⧸ A') := isCyclic_of_injective f hf
    have hA'z : IsPolyZ A' := hAz.of_equiv
      (Subgroup.subgroupOfEquivOfLe (show A ≤ H from le_sup_left)).symm
    exact ⟨H, hHi, isPolyZ_of_normal_cyclic_quotient A' hA'z
      ((infiniteCyclic_torsionFree (G := G ⧸ N)).of_injective f hf)⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_PolyZComparison
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finite_templateSymmetryGroup _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteSubtypeLinearEquivRealIdMemSubgroupLinearSupportSymmetryGroup _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The virtual poly-Z refinement of a polycyclic series -/

noncomputable section
namespace PolycyclicRecognition

open ChromaticCyclic
variable {G J : Type} [Group G] [Group J]

theorem polyZ_finiteIndex_of_equiv (e : G ≃* J)
    (h : ∃ H : Subgroup G, H.FiniteIndex ∧ IsPolyZ H) :
    ∃ K : Subgroup J, K.FiniteIndex ∧ IsPolyZ K := by
  obtain ⟨H, hHi, hHz⟩ := h
  let := hHi
  let d := H.equivMapOfInjective e.toMonoidHom e.injective
  exact ⟨H.map e.toMonoidHom, Subgroup.FiniteIndex.map_of_surjective H e.surjective,
    hHz.of_equiv d⟩

theorem polyZ_finiteIndex_of_cyclicStep {H K : Subgroup G}
    (s : CyclicStep H K) (hfg : Group.FG H)
    (hH : ∃ L : Subgroup H, L.FiniteIndex ∧ IsPolyZ L) :
    ∃ L : Subgroup K, L.FiniteIndex ∧ IsPolyZ L := by
  let e := (Subgroup.subgroupOfEquivOfLe s.le).symm
  let : Group.FG (H.subgroupOf K) :=
    @Group.fg_of_surjective _ _ _ _ hfg e.toMonoidHom e.surjective
  let := s.normal
  let := s.cyclic
  exact polyZ_finiteIndex_of_cyclic_extension (H.subgroupOf K)
    (polyZ_finiteIndex_of_equiv e hH)

theorem IsPolycyclic.exists_polyZ_finiteIndex (hG : IsPolycyclic G) :
    ∃ H : Subgroup G, H.FiniteIndex ∧ IsPolyZ H := by
  obtain ⟨n, ⟨c⟩⟩ := hG
  have hm : ∀ i, i ≤ n → Group.FG (c.group i) ∧
      ∃ H : Subgroup (c.group i), H.FiniteIndex ∧ IsPolyZ H := by
    intro i
    induction i with
    | zero =>
      intro _
      rw [c.first]
      exact ⟨inferInstance, ⊤, inferInstance, isPolyZ_of_subsingleton⟩
    | succ i ih =>
      intro hi
      obtain ⟨hfg, hz⟩ := ih (by omega)
      exact ⟨finitelyGenerated_of_cyclicStep (c.step i (by omega)) hfg,
        polyZ_finiteIndex_of_cyclicStep (c.step i (by omega)) hfg hz⟩
  have htop := (hm n le_rfl).2
  rw [c.last] at htop
  exact polyZ_finiteIndex_of_equiv Subgroup.topEquiv htop

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_PolyZDuality
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integral duality along a torsion-free cyclic series

The comparison group needed in recognition can be chosen poly-Z.  The
cohomology shift for an infinite cyclic extension proves duality for this
subgroup directly, without assuming the general polycyclic duality theorem.
-/

noncomputable section
namespace PolycyclicRecognition

open ChromaticCyclic
variable {G : Type} [Group G]

theorem poincareDuality_of_infiniteCyclicQuotient
    (N : Subgroup G) [N.Normal] [IsCyclic (G ⧸ N)] [Infinite (G ⧸ N)]
    {n : ℕ} (hN : IsIntegralPoincareDualityGroup N n) :
    IsIntegralPoincareDualityGroup G (n + 1) := by
  let e : Multiplicative ℤ ≃* G ⧸ N := intCyclicMulEquiv
  let q : G →* Multiplicative ℤ := e.symm.toMonoidHom.comp (QuotientGroup.mk' N)
  have hker : q.ker = N := by
    ext g
    change e.symm (QuotientGroup.mk' N g) = 1 ↔ g ∈ N
    rw [← e.symm.map_one, e.symm.injective.eq_iff]
    exact QuotientGroup.eq_one_iff g
  obtain ⟨t, ht⟩ := QuotientGroup.mk'_surjective N (e (Multiplicative.ofAdd 1))
  have hqt : q t = Multiplicative.ofAdd 1 := by
    change e.symm (QuotientGroup.mk' N t) = _
    rw [ht, e.symm_apply_apply]
  exact poincareDuality_of_integerQuotient q t hqt
    (hN.of_equiv (MulEquiv.subgroupCongr hker.symm))

theorem exists_poincareDuality_of_torsionFreeCyclicQuotient
    (N : Subgroup G) [N.Normal] [IsCyclic (G ⧸ N)]
    {n : ℕ} (hN : IsIntegralPoincareDualityGroup N n)
    (hQ : HasNoNontrivialTorsion (G ⧸ N)) :
    ∃ d, IsIntegralPoincareDualityGroup G d := by
  cases finite_or_infinite (G ⧸ N) with
  | inr h =>
    let := h
    exact ⟨n + 1, poincareDuality_of_infiniteCyclicQuotient N hN⟩
  | inl h =>
    let := h
    let := subsingleton_of_finite_torsionFree (G ⧸ N) hQ
    have htop : N = ⊤ := by
      apply top_unique
      intro g _
      exact (QuotientGroup.eq_one_iff g).mp (Subsingleton.elim _ _)
    subst N
    exact ⟨n, hN.of_equiv Subgroup.topEquiv⟩

theorem IsPolyZ.exists_poincareDuality (hG : IsPolyZ G) :
    ∃ n, IsIntegralPoincareDualityGroup G n := by
  obtain ⟨n, c, hc⟩ := hG
  have hm : ∀ i, i ≤ n → ∃ d, IsIntegralPoincareDualityGroup (c.group i) d := by
    intro i
    induction i with
    | zero =>
      intro _
      rw [c.first]
      exact ⟨0, poincareDuality_zero_of_subsingleton _⟩
    | succ i ih =>
      intro hi
      let s := c.step i (by omega)
      let := s.normal
      let := s.cyclic
      let e := (Subgroup.subgroupOfEquivOfLe s.le).symm
      obtain ⟨d, hd⟩ := ih (by omega)
      exact exists_poincareDuality_of_torsionFreeCyclicQuotient
        ((c.group i).subgroupOf (c.group (i + 1)))
        (hd.of_equiv e) (hc i (by omega))
  obtain ⟨d, hd⟩ := hm n le_rfl
  rw [c.last] at hd
  exact ⟨d, hd.of_equiv Subgroup.topEquiv⟩

theorem IsPolycyclic.exists_poincareDuality_finiteIndex (hG : IsPolycyclic G) :
    ∃ H : Subgroup G, H.FiniteIndex ∧ ∃ n, IsIntegralPoincareDualityGroup H n := by
  obtain ⟨H, hi, hz⟩ := hG.exists_polyZ_finiteIndex
  exact ⟨H, hi, hz.exists_poincareDuality⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_PolycyclicQuotientRank
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.cyclicTopHomologyInjection_mono _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.latticeNormalFlag_normal _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.commutingIntegralHom_generator _root_.OAI.PolycyclicRecognition.integralQuotientDrop_insert _root_.OAI.PolycyclicRecognition.integralQuotientLast_insert _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Lattice quotients of polycyclic groups

The already proved finite-index duality transfer gives duality for a
polycyclic group of finite integral cohomological dimension. Splitting off
the coordinates of a lattice quotient then bounds its rank by that dimension.
-/

noncomputable section
namespace PolycyclicRecognition

variable {G : Type} [Group G]

theorem IsPolycyclic.exists_poincareDuality_of_finiteDimension
    (hG : IsPolycyclic G) (hcd : HasFiniteIntegralCohomologicalDimension G) :
    ∃ n, IsIntegralPoincareDualityGroup G n := by
  let : Group.FG G := hG.finitelyGenerated
  obtain ⟨H, hH, n, hn⟩ := hG.exists_poincareDuality_finiteIndex
  let := hH
  let : Group.FG H := hn.1.fg
  exact ⟨n, liDualityInput H G (finiteIndexCoarseEquivalence H)
    (hn.finiteCohomologicalDimension H) hcd n hn⟩

theorem IsPolycyclic.poincareDuality_dimension_ge_lattice_quotient
    (hG : IsPolycyclic G) (hcd : HasFiniteIntegralCohomologicalDimension G)
    (n : ℕ) (q : G →* IntegralLatticeGroup n) (hq : Function.Surjective q) :
    ∃ m, IsIntegralPoincareDualityGroup G (m + n) := by
  induction n generalizing G with
  | zero =>
    obtain ⟨m, hm⟩ := hG.exists_poincareDuality_of_finiteDimension hcd
    exact ⟨m, by simpa using hm⟩
  | succ n ih =>
    let q₁ : G →* Multiplicative ℤ := (latticeCoordinate n).comp q
    let qK : q₁.ker →* (latticeCoordinate n).ker :=
      { toFun := fun x => ⟨q x, x.property⟩
        map_one' := Subtype.ext q.map_one
        map_mul' := fun x y => Subtype.ext (q.map_mul x y) }
    have hqK : Function.Surjective qK := by
      intro y
      obtain ⟨x, hx⟩ := hq y
      have hxK : x ∈ q₁.ker := by
        change latticeCoordinate n (q x) = 1
        rw [hx]
        exact y.property
      exact ⟨⟨x, hxK⟩, Subtype.ext hx⟩
    obtain ⟨m, hm⟩ := ih
      (hG.of_injective q₁.ker.subtype Subtype.val_injective)
      (hcd.subgroup q₁.ker)
      ((latticeCoordinateKernel n).toMonoidHom.comp qK)
      ((latticeCoordinateKernel n).surjective.comp hqK)
    obtain ⟨t, ht⟩ := hq (latticeCoordinateSection n)
    have ht₁ : q₁ t = Multiplicative.ofAdd 1 := by
      change latticeCoordinate n (q t) = _
      rw [ht, latticeCoordinate_section]
    exact ⟨m, by simpa only [Nat.add_assoc] using
      poincareDuality_of_integerQuotient q₁ t ht₁ hm⟩

theorem IsPolycyclic.lattice_quotient_rank_le
    (hG : IsPolycyclic G) (d : ℕ)
    [CategoryTheory.HasProjectiveDimensionLE (trivialIntegral G) d]
    (n : ℕ) (q : G →* IntegralLatticeGroup n) (hq : Function.Surjective q) : n ≤ d := by
  obtain ⟨m, hm⟩ := hG.poincareDuality_dimension_ge_lattice_quotient ⟨d, inferInstance⟩ n q hq
  have hmd : m + n ≤ d := hm.dimension_le
  omega

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_NilpotentAbelianQuotientRank
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.cyclicTopHomologyInjection_mono _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.latticeNormalFlag_normal _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Rank bounds for abelian quotients of nilpotent groups

A finite independent family in a quotient lifts inside a finitely generated
nilpotent subgroup. Its lattice quotient is bounded by the cohomological
dimension of that subgroup. No finite generation of the original kernel or
quotient is required.
-/

noncomputable section
namespace PolycyclicRecognition

variable {G A : Type} [Group G] [Group.IsNilpotent G] [CommGroup A]

theorem nilpotent_abelian_quotient_lattice_rank_le (d : ℕ)
    [CategoryTheory.HasProjectiveDimensionLE (trivialIntegral G) d]
    (q : G →* A) (hq : Function.Surjective q) (n : ℕ)
    (i : IntegralLatticeGroup n →* A) (hi : Function.Injective i) : n ≤ d := by
  let P := i.range.comap q
  let qP : P →* i.range :=
    { toFun := fun x => ⟨q x, x.property⟩
      map_one' := Subtype.ext q.map_one
      map_mul' := fun x y => Subtype.ext (q.map_mul x y) }
  have hqP : Function.Surjective qP := by
    intro a
    obtain ⟨g, hg⟩ := hq a
    have hgP : g ∈ P := by change q g ∈ i.range; rw [hg]; exact a.property
    exact ⟨⟨g, hgP⟩, Subtype.ext hg⟩
  let e := MonoidHom.ofInjective hi
  let : Group.FG (IntegralLatticeGroup n) := inferInstance
  let : Group.FG i.range := Group.fg_of_surjective e.surjective
  obtain ⟨H, hH, hsurj⟩ := exists_fg_subgroup_surjective qP hqP
  let : Group.FG H := (Group.fg_iff_subgroup_fg H).mpr hH
  let := subgroup_cohomologicalDimension_le P d
  let := subgroup_cohomologicalDimension_le H d
  exact (isPolycyclic_of_finitelyGenerated_nilpotent H).lattice_quotient_rank_le d n
    (e.symm.toMonoidHom.comp (qP.comp H.subtype)) (e.symm.surjective.comp hsurj)

theorem nilpotent_abelian_quotient_rank_le (d : ℕ)
    [CategoryTheory.HasProjectiveDimensionLE (trivialIntegral G) d]
    (q : G →* A) (hq : Function.Surjective q) : Module.rank ℤ (Additive A) ≤ d := by
  by_contra hd
  have hlt : (d : Cardinal) < Module.rank ℤ (Additive A) := lt_of_not_ge hd
  have hle : ((d + 1 : ℕ) : Cardinal) ≤ Module.rank ℤ (Additive A) := by
    rw [Nat.cast_add, Nat.cast_one]
    exact Cardinal.natCast_add_one_le_iff.mpr hlt
  obtain ⟨b, hb⟩ := exists_linearIndependent_of_le_rank hle
  have hbound := nilpotent_abelian_quotient_lattice_rank_le d q hq (d + 1)
    (independentLatticeHom b) (independentLatticeHom_injective hb)
  omega

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_FiniteOrderUnipotent
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A rational unipotent operator of finite order is the identity

The polynomial X^n-1 is squarefree in characteristic zero. An operator it
annihilates is semisimple, and its nilpotent difference from the identity must
therefore vanish.
-/

namespace PolycyclicRecognition

open Polynomial

theorem rationalUnipotent_eq_one_of_pow_eq_one {V : Type*}
    [AddCommGroup V] [Module ℚ V] (f : Module.End ℚ V)
    (hf : IsNilpotent (f - 1)) {n : ℕ} (hn : n ≠ 0) (hpow : f ^ n = 1) : f = 1 := by
  have hp : Squarefree (X ^ n - C (1 : ℚ)) :=
    (separable_X_pow_sub_C (1 : ℚ) (Nat.cast_ne_zero.mpr hn) one_ne_zero).squarefree
  have hroot : aeval f (X ^ n - C (1 : ℚ)) = 0 := by simp [hpow]
  have hs := Module.End.isSemisimple_of_squarefree_aeval_eq_zero hp hroot
  have hdiff : (f - 1).IsSemisimple := by
    simpa only [map_one] using
      (Module.End.isSemisimple_sub_algebraMap_iff (f := f) (μ := (1 : ℚ))).mpr hs
  exact sub_eq_zero.mp (Module.End.eq_zero_of_isNilpotent_isSemisimple hf hdiff)

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_NilpotentCentralRoots
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

namespace OAI

/-! # Isolated centers in torsion-free nilpotent groups

If a nonzero power of an element is central, its unipotent action on a maximal
abelian normal subgroup has finite order and is trivial. The element belongs
to that abelian subgroup, where torsion freeness makes roots unique. Thus it
is central, and the quotient by the center is torsion free.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped IsMulCommutative

variable {G : Type} [Group G] [Group.IsNilpotent G]

theorem nilpotent_mem_center_of_pow_mem_center
    (hG : HasNoNontrivialTorsion G) (g : G) {n : ℕ} (hn : n ≠ 0)
    (hgn : g ^ n ∈ Subgroup.center G) : g ∈ Subgroup.center G := by
  obtain ⟨A, hAn, hAa, hmax⟩ := exists_maximal_abelian_normal_subgroup G
  let := hAn
  let := hAa
  have hA : HasNoNontrivialTorsion A := by
    intro a k hk hak
    apply Subtype.ext
    exact hG a k hk (congrArg Subtype.val hak)
  let ρ := rationalConjugationLinear A
  have hcentral : g ^ n ∈ (rationalConjugationLinear A).ker := by
    rw [rationalConjugationLinear_ker A hA]
    exact Subgroup.center_le_centralizer _ hgn
  have hpow : ρ g ^ n = 1 := by
    rw [← map_pow]
    exact hcentral
  have hid : ρ g = 1 := rationalUnipotent_eq_one_of_pow_eq_one (ρ g)
    (rationalConjugationDifference_nilpotent A g) hn hpow
  have hgA : g ∈ A := by
    have hgker : g ∈ (rationalConjugationLinear A).ker := hid
    rw [rationalConjugationLinear_ker A hA,
      centralizer_eq_of_maximal_abelian_normal G A hmax] at hgker
    exact hgker
  let a : A := ⟨g, hgA⟩
  let : IsMulTorsionFree A := isMulTorsionFree_iff_not_isOfFinOrder.mpr (by
    intro b hb hfin
    exact hb (hA b (orderOf b) (ne_of_gt hfin.orderOf_pos) (pow_orderOf_eq_one b)))
  apply Subgroup.mem_center_iff.mpr
  intro x
  have hxpow : (MulAut.conjNormal (H := A) x a) ^ n = a ^ n := by
    rw [← map_pow]
    apply Subtype.ext
    change x * (g ^ n) * x⁻¹ = g ^ n
    rw [Subgroup.mem_center_iff.mp hgn x, mul_inv_cancel_right]
  have hxa : MulAut.conjNormal (H := A) x a = a := pow_left_injective hn hxpow
  exact mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val hxa)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_NilpotentQuotientRank
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.cyclicTopHomologyInjection_mono _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

namespace OAI

/-! # Uniform rank bounds persist in nilpotent quotients

The inverse image of a subgroup need not be finitely generated. For the
generator bound we lift only a finite generating set. The abelian rank bound
uses the full inverse image and needs no finite-generation assumption.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped IsMulCommutative
variable {G Q : Type} [Group G] [Group.IsNilpotent G] [Group Q]

omit [Group.IsNilpotent G] in
theorem quotientSubgroupMap_surjective (q : G →* Q) (hq : Function.Surjective q)
    (K : Subgroup Q) : Function.Surjective (quotientSubgroupMap q K) := by
  intro k
  obtain ⟨g, hg⟩ := hq k
  have hgK : g ∈ K.comap q := by change q g ∈ K; rw [hg]; exact k.property
  exact ⟨⟨g, hgK⟩, Subtype.ext hg⟩

theorem nilpotent_quotient_abelian_subgroup_rank_le (d : ℕ)
    [CategoryTheory.HasProjectiveDimensionLE (trivialIntegral G) d]
    (q : G →* Q) (hq : Function.Surjective q) (K : Subgroup Q) [IsMulCommutative K] :
    Module.rank ℤ (Additive K) ≤ d := by
  let := subgroup_cohomologicalDimension_le (K.comap q) d
  exact nilpotent_abelian_quotient_rank_le d (quotientSubgroupMap q K)
    (quotientSubgroupMap_surjective q hq K)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_NilpotentUpperCentralRoots
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.cyclicTopHomologyInjection_mono _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

namespace OAI

/-! # Torsion-free upper central quotients

Each upper central term is closed under taking roots. The center of every
resulting quotient therefore embeds faithfully into a finite-dimensional
rational space whenever the original group has finite integral dimension.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped IsMulCommutative
variable {G : Type} [Group G]

theorem quotient_torsionFree_of_root_closed (N : Subgroup G) [N.Normal]
    (hN : ∀ (g : G) (n : ℕ), n ≠ 0 → g ^ n ∈ N → g ∈ N) :
    HasNoNontrivialTorsion (G ⧸ N) := by
  intro x n hn hx
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N x
  apply (QuotientGroup.eq_one_iff g).mpr
  apply hN g n hn
  apply (QuotientGroup.eq_one_iff (g ^ n)).mp
  change (QuotientGroup.mk' N) (g ^ n) = 1
  simpa only [map_pow] using hx

theorem nilpotent_upperCentralQuotient_torsionFree [Group.IsNilpotent G]
    (hG : HasNoNontrivialTorsion G) (k : ℕ) :
    HasNoNontrivialTorsion (G ⧸ Subgroup.upperCentralSeries G k) := by
  induction k with
  | zero =>
    apply quotient_torsionFree_of_root_closed
    intro g n hn hgn
    change g ^ n = 1 at hgn
    change g = 1
    exact hG g n hn hgn
  | succ k ih =>
    let U := Subgroup.upperCentralSeries G k
    let q := QuotientGroup.mk' U
    have he : Subgroup.upperCentralSeries G (k + 1) =
        (Subgroup.center (G ⧸ U)).comap q :=
      Subgroup.upperCentralSeriesStep_eq_comap_center U
    apply quotient_torsionFree_of_root_closed
    intro g n hn hgn
    rw [he] at hgn ⊢
    have hp : (q g) ^ n ∈ Subgroup.center (G ⧸ U) := by
      rw [← map_pow]
      exact hgn
    exact nilpotent_mem_center_of_pow_mem_center ih (q g) hn hp

theorem nilpotent_upperCentral_center_rational_finite [Group.IsNilpotent G]
    (d : ℕ) [CategoryTheory.HasProjectiveDimensionLE (trivialIntegral G) d] (k : ℕ) :
    Module.Finite ℚ
      (RationalAbelianSpace (Subgroup.center (G ⧸ Subgroup.upperCentralSeries G k))) := by
  apply Module.rank_lt_aleph0_iff.mp
  rw [rationalAbelianSpace_rank]
  exact (nilpotent_quotient_abelian_subgroup_rank_le d
    (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _) (Subgroup.center _)).trans_lt
      Cardinal.natCast_lt_aleph0

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_RationalCentralLayers
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

namespace OAI

/-! # Rational actions on the upper central layers

Ambient conjugation preserves the characteristic upper central series.
On each central layer it therefore gives a rational linear action. Trivial
rational action implies trivial action on the layer itself, since the
successive quotients are torsion-free.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G] (F : Subgroup G) [F.Normal]

theorem subgroup_le_rationalUpperCentralAction_ker (i : ℕ) :
    F ≤ (rationalUpperCentralAction F i).ker := by
  intro g hg
  let a : F := ⟨g, hg⟩
  let U := Subgroup.upperCentralSeries F i
  let q := QuotientGroup.mk' U
  have he : upperCentralLayerAut F i g = 1 := by
    apply MulEquiv.ext
    intro z
    apply Subtype.ext
    obtain ⟨b, hb⟩ := QuotientGroup.mk'_surjective U (z : F ⧸ U)
    change characteristicQuotientAut U (MulAut.conjNormal (H := F) g) (z : F ⧸ U) = z
    rw [← hb, characteristicQuotientAut_mk]
    change q (a * b * a⁻¹) = q b
    rw [map_mul, map_mul, map_inv]
    have hcomm : q a * q b = q b * q a := by
      rw [hb]
      exact Subgroup.mem_center_iff.mp z.property (q a)
    rw [hcomm, mul_inv_cancel_right]
  change rationalAbelianAut (upperCentralLayerAut F i g) = 1
  rw [he, map_one]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_UpperCentralLayerMap
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

namespace OAI

/-! # Equivariant rational maps from the actual upper central series -/

noncomputable section
namespace PolycyclicRecognition

open scoped IsMulCommutative
variable {G : Type} [Group G] (F : Subgroup G) [F.Normal]

theorem upperCentralLayerMap_equivariant (i : ℕ) (g : G)
    (a : ambientUpperCentralSeries F (i + 1)) :
    upperCentralLayerMap F i (MulAut.conjNormal g a) =
      upperCentralLayerAut F i g (upperCentralLayerMap F i a) := by
  apply Subtype.ext
  change QuotientGroup.mk' (Subgroup.upperCentralSeries F i) _ =
    characteristicQuotientAut (Subgroup.upperCentralSeries F i)
      (MulAut.conjNormal (H := F) g)
      (QuotientGroup.mk' (Subgroup.upperCentralSeries F i) _)
  rw [characteristicQuotientAut_mk]
  rfl

theorem rationalUpperCentralMap_equivariant (i : ℕ) (g : G)
    (a : ambientUpperCentralSeries F (i + 1)) :
    (rationalUpperCentralMap F i (MulAut.conjNormal g a)).toAdd =
      rationalUpperCentralAction F i g (rationalUpperCentralMap F i a).toAdd := by
  change rationalAbelianMap (Additive.ofMul (upperCentralLayerMap F i (MulAut.conjNormal g a))) =
    rationalAbelianAut (upperCentralLayerAut F i g)
      (rationalAbelianMap (Additive.ofMul (upperCentralLayerMap F i a)))
  change rationalAbelianMap (Additive.ofMul (upperCentralLayerMap F i (MulAut.conjNormal g a))) =
    rationalAbelianMap (Additive.ofMul (upperCentralLayerAut F i g (upperCentralLayerMap F i a)))
  rw [upperCentralLayerMap_equivariant]

omit [F.Normal] in
theorem rationalUpperCentralMap_kernel [Group.IsNilpotent F]
    (hF : HasNoNontrivialTorsion F) (i : ℕ) :
    (rationalUpperCentralMap F i).ker.map (ambientUpperCentralSeries F (i + 1)).subtype =
      ambientUpperCentralSeries F i := by
  have hQ := nilpotent_upperCentralQuotient_torsionFree hF i
  have hZ : HasNoNontrivialTorsion (CentralLayer F i) :=
    hQ.of_injective (Subgroup.center _).subtype Subtype.val_injective
  have hker (a : ambientUpperCentralSeries F (i + 1)) :
      a ∈ (rationalUpperCentralMap F i).ker ↔ (a : G) ∈ ambientUpperCentralSeries F i := by
    change Multiplicative.ofAdd (rationalAbelianMap (Additive.ofMul (upperCentralLayerMap F i a))) = 1 ↔ _
    change _ ↔ (ambientUpperCentralToF F (i + 1) a : G) ∈ ambientUpperCentralSeries F i
    rw [mem_ambientUpperCentralSeries_iff]
    constructor
    · intro ha
      have hz : upperCentralLayerMap F i a = 1 := by
        apply Additive.ofMul.injective
        apply rationalAbelianMap_injective hZ
        simpa only [ofMul_one, map_zero, toAdd_ofAdd, toAdd_one] using
          congrArg Multiplicative.toAdd ha
      exact (QuotientGroup.eq_one_iff _).mp (congrArg Subtype.val hz)
    · intro ha
      have hz : upperCentralLayerMap F i a = 1 :=
        Subtype.ext ((QuotientGroup.eq_one_iff _).mpr ha)
      simp only [hz, ofMul_one, map_zero, ofAdd_zero]
  apply le_antisymm
  · rintro g ⟨a, ha, rfl⟩
    exact (hker a).mp ha
  · intro g hg
    have hg' : g ∈ ambientUpperCentralSeries F (i + 1) :=
      ambientUpperCentralSeries_mono F (Nat.le_succ i) hg
    exact ⟨⟨g, hg'⟩, (hker _).mpr hg, rfl⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_CentralLayerUnipotence
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Lifting unipotence from rational central layers to the original group -/

noncomputable section
namespace PolycyclicRecognition

variable {G : Type} [Group G] (F : Subgroup G) [F.Normal] [Group.IsNilpotent F]

theorem relativeCommutatorSeries_upperCentral_le (hF : HasNoNontrivialTorsion F)
    (K : Subgroup G) (i c : ℕ)
    (hc : linearActionFiltration
      (fun g : K => (rationalUpperCentralAction F i g).toLinearMap - 1) c = ⊥) :
    relativeCommutatorSeries K (ambientUpperCentralSeries F (i + 1)) c ≤
      ambientUpperCentralSeries F i := by
  have h := relativeCommutatorSeries_le_kernel_of_linearFiltration K
    (ambientUpperCentralSeries F (i + 1)) (rationalUpperCentralAction F i)
    (rationalUpperCentralMap F i) (rationalUpperCentralMap_equivariant F i) c hc
  rwa [rationalUpperCentralMap_kernel F hF i] at h

theorem exists_relativeCommutatorSeries_eq_bot_of_central_layers
    (hF : HasNoNontrivialTorsion F) (K : Subgroup G)
    (hc : ∀ i, i < Group.nilpotencyClass F → ∃ c, linearActionFiltration
      (fun g : K => (rationalUpperCentralAction F i g).toLinearMap - 1) c = ⊥) :
    ∃ c, relativeCommutatorSeries K F c = ⊥ := by
  have hi (i : ℕ) (hi : i ≤ Group.nilpotencyClass F) :
      ∃ c, relativeCommutatorSeries K (ambientUpperCentralSeries F i) c = ⊥ := by
    induction i with
    | zero => exact ⟨0, ambientUpperCentralSeries_zero F⟩
    | succ i ih =>
      obtain ⟨c, hci⟩ := hc i (by omega)
      obtain ⟨d, hd⟩ := ih (by omega)
      refine ⟨c + d, eq_bot_iff.mpr ?_⟩
      rw [relativeCommutatorSeries_add]
      exact (relativeCommutatorSeries_mono K
        (relativeCommutatorSeries_upperCentral_le F hF K i c hci) d).trans_eq hd
  simpa only [ambientUpperCentralSeries_top] using hi (Group.nilpotencyClass F) le_rfl

theorem nilpotent_of_unipotent_central_layers (hF : HasNoNontrivialTorsion F)
    (K : Subgroup G) [K.Normal]
    (hcent : Subgroup.centralizer (F : Set G) ≤ F)
    (hc : ∀ i, i < Group.nilpotencyClass F → ∃ c, linearActionFiltration
      (fun g : K => (rationalUpperCentralAction F i g).toLinearMap - 1) c = ⊥) :
    Group.IsNilpotent K := by
  obtain ⟨c, hc⟩ := exists_relativeCommutatorSeries_eq_bot_of_central_layers F hF K hc
  exact nilpotent_of_relativeCommutatorSeries K F c hc hcent

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_IntertwinedActionWords
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Transport of mixed operator words through a linear map -/

namespace PolycyclicRecognition

variable {K V U I : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup U] [Module K U]

theorem actionOperatorWord_intertwines
    (D : I → Module.End K V) (E : I → Module.End K U) (q : V →ₗ[K] U)
    (h : ∀ i v, q (D i v) = E i (q v)) (w : List I) (v : V) :
    q (actionOperatorWord D w v) = actionOperatorWord E w (q v) := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    change q (D i (actionOperatorWord D w v)) = E i (actionOperatorWord E w (q v))
    rw [h, ih]

end PolycyclicRecognition

namespace PolycyclicRecognition

variable {K L V U I : Type*} [Field K] [Field L] [AddCommGroup V] [Module K V]
    [AddCommGroup U] [Module L U]

theorem actionOperatorWord_intertwines_function
    (D : I → Module.End K V) (E : I → Module.End L U) (q : V → U)
    (h : ∀ i v, q (D i v) = E i (q v)) (w : List I) (v : V) :
    q (actionOperatorWord D w v) = actionOperatorWord E w (q v) := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    change q (D i (actionOperatorWord D w v)) = E i (actionOperatorWord E w (q v))
    rw [h, ih]

theorem actionOperatorWord_zero_of_matching_generators
    {J : Type*} (D : I → Module.End K V) (E : J → Module.End K V)
    (hmatch : ∀ i, ∃ j, D i = E j) (c : ℕ)
    (hE : ∀ w : List J, w.length = c → actionOperatorWord E w = 0) :
    ∀ w : List I, w.length = c → actionOperatorWord D w = 0 := by
  classical
  choose f hf using hmatch
  have he (w : List I) : actionOperatorWord D w = actionOperatorWord E (w.map f) := by
    induction w with
    | nil => rfl
    | cons i w ih =>
      change D i * actionOperatorWord D w = E (f i) * actionOperatorWord E (w.map f)
      rw [hf, ih]
  intro w hw
  rw [he]
  exact hE _ (by simpa only [List.length_map] using hw)

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_RationalNilpotentQuotient
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.cyclicTopHomologyInjection_mono _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

namespace OAI

/-! # A faithful rational action on the quotient by the nilpotent radical

The finitely many upper central layers give a direct-product vector space.
For a maximal nilpotent normal subgroup, the action kernel is exactly that
subgroup, by the proved central-filtration criterion.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped IsMulCommutative commutatorElement
variable {G : Type} [Group G] (F : Subgroup G) [F.Normal]

theorem centralLayersAction_ker_iff (c : ℕ) (g : G) :
    g ∈ (centralLayersAction F c).ker ↔
      ∀ i : Fin c, g ∈ (rationalUpperCentralAction F i).ker := by
  classical
  constructor
  · intro hg i
    change centralLayersAction F c g = 1 at hg
    change rationalUpperCentralAction F i g = 1
    apply LinearEquiv.ext
    intro v
    change rationalUpperCentralAction F i g v = v
    let w : CentralLayersSpace F c := Pi.single i v
    have he := congrArg
      (fun e : CentralLayersSpace F c ≃ₗ[ℚ] CentralLayersSpace F c => e w i) hg
    change rationalUpperCentralAction F i g (w i) = w i at he
    simpa only [w, Pi.single_eq_same] using he
  · intro hg
    change centralLayersAction F c g = 1
    ext v i
    change rationalUpperCentralAction F i g (v i) = v i
    rw [show rationalUpperCentralAction F i g = 1 from hg i]
    rfl

theorem subgroup_le_centralLayersAction_ker (c : ℕ) : F ≤ (centralLayersAction F c).ker := by
  intro g hg
  exact (centralLayersAction_ker_iff F c g).mpr
    (fun i => subgroup_le_rationalUpperCentralAction_ker F i hg)

omit [F.Normal] in
theorem centralLayersSpace_finite [Group.IsNilpotent F]
    (hF : HasFiniteIntegralCohomologicalDimension F) (c : ℕ) :
    Module.Finite ℚ (CentralLayersSpace F c) := by
  obtain ⟨d, hd⟩ := hF
  let := hd
  let (i : Fin c) : Module.Finite ℚ (RationalAbelianSpace (CentralLayer F i)) :=
    nilpotent_upperCentral_center_rational_finite d i
  infer_instance

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_CentralLayersWordProjection
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

namespace OAI

/-! # Projecting a uniform action bound to the central factors -/

noncomputable section
namespace PolycyclicRecognition

open scoped IsMulCommutative
variable {G : Type} [Group G] (F : Subgroup G) [F.Normal]

theorem centralLayers_word_projection (c : ℕ) (K : Subgroup G) (d : ℕ)
    (hd : ∀ w : List K, w.length = d → actionOperatorWord
      (fun g : K => (centralLayersAction F c g).toLinearMap - 1) w = 0)
    (i : Fin c) :
    linearActionFiltration (fun g : K => (rationalUpperCentralAction F i g).toLinearMap - 1) d = ⊥ := by
  apply linearActionFiltration_eq_bot_of_word_zero
  intro w hw
  apply LinearMap.ext
  intro v
  let D := fun g : K => (centralLayersAction F c g).toLinearMap - 1
  let E := fun g : K => (rationalUpperCentralAction F i g).toLinearMap - 1
  let q : CentralLayersSpace F c →ₗ[ℚ] RationalAbelianSpace (CentralLayer F i) := LinearMap.proj i
  let x : CentralLayersSpace F c := Pi.single i v
  have hx : q x = v := by simp [q, x]
  have he := actionOperatorWord_intertwines D E q (fun _ _ => rfl) w x
  rw [hd w hw] at he
  simpa only [map_zero, hx, LinearMap.zero_apply] using he.symm

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_CommonEigenvectors
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite common eigenspaces and a common eigenvector

Common eigenspaces form an independent family even when the operators do
not commute. For commuting operators over an algebraically closed field,
a minimal nonzero invariant subspace supplies a common eigenvector.
-/

noncomputable section
namespace PolycyclicRecognition

variable {K V I : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem mem_commonEigenspace (f : I → Module.End K V) (χ : I → K) (v : V) :
    v ∈ commonEigenspace f χ ↔ ∀ i, f i v = χ i • v := by
  simp only [commonEigenspace, Submodule.mem_iInf, Module.End.mem_eigenspace_iff]

theorem commonEigenspace_independent (f : I → Module.End K V) :
    iSupIndep (commonEigenspace f) :=
  iSupIndep.iInf (fun i μ => (f i).eigenspace μ) (fun i => (f i).eigenspaces_iSupIndep)

theorem finite_commonEigenspaces [Module.Finite K V] (f : I → Module.End K V) :
    {χ : I → K | commonEigenspace f χ ≠ ⊥}.Finite :=
  WellFoundedGT.finite_ne_bot_of_iSupIndep (commonEigenspace_independent f)

theorem exists_commonEigenspace [Module.Finite K V] [Nontrivial V] [IsAlgClosed K]
    (f : I → Module.End K V) (hcomm : ∀ i j, Commute (f i) (f j)) :
    ∃ χ : I → K, commonEigenspace f χ ≠ ⊥ := by
  let P (W : Submodule K V) := W ≠ ⊥ ∧ ∀ i, Set.MapsTo (f i) W W
  obtain ⟨W, hW⟩ := exists_minimal_of_wellFoundedLT P
    ⟨⊤, top_ne_bot, fun _ _ _ => Submodule.mem_top⟩
  have hWnonzero := hW.prop.1
  have hWinv := hW.prop.2
  let : Nontrivial W := (Submodule.nontrivial_iff_ne_bot).mpr hWnonzero
  have hs (i : I) : ∃ μ : K, ∀ w : W, f i w = μ • (w : V) := by
    let r := (f i).restrict (hWinv i)
    obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue r
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hμ
    have hvEigen : f i (v : V) = μ • (v : V) := by
      exact congrArg Subtype.val (Module.End.mem_eigenspace_iff.mp hv)
    let U := W ⊓ (f i).eigenspace μ
    have hUnonzero : U ≠ ⊥ := by
      intro heq
      have hh : (v : V) ∈ U := ⟨v.property, Module.End.mem_eigenspace_iff.mpr hvEigen⟩
      rw [heq, Submodule.mem_bot] at hh
      exact hv0 (Subtype.ext hh)
    have hUinv (j : I) : Set.MapsTo (f j) U U := by
      intro x hx
      refine ⟨hWinv j hx.1, Module.End.mem_eigenspace_iff.mpr ?_⟩
      have hxEigen := Module.End.mem_eigenspace_iff.mp hx.2
      calc
        f i (f j x) = f j (f i x) := congrArg (fun a : Module.End K V => a x) (hcomm i j).eq
        _ = μ • f j x := by rw [hxEigen, map_smul]
    have hWU : W ≤ U := hW.le_of_le ⟨hUnonzero, hUinv⟩ inf_le_left
    exact ⟨μ, fun w => Module.End.mem_eigenspace_iff.mp (hWU w.property).2⟩
  choose χ hχ using hs
  refine ⟨χ, ?_⟩
  intro heq
  apply hWnonzero
  apply eq_bot_iff.mpr
  intro v hv
  have hh : v ∈ commonEigenspace f χ := (mem_commonEigenspace f χ v).mpr
    (fun i => hχ i ⟨v, hv⟩)
  simpa only [heq] using hh

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_InvariantSubspaceDeterminant
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Determinants of scalar commutators on an invariant subspace

Restricting an action to a genuinely invariant subspace gives an action
by linear equivalences. Its commutators have determinant one, so a scalar
commutator has scalar a root of unity of degree the subspace dimension.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped commutatorElement
variable {G K V : Type*} [Group G] [Field K] [AddCommGroup V] [Module K V]

theorem invariantSubspaceAction_scalar (ρ : G →* (V ≃ₗ[K] V)) (W : Submodule K V)
    (hW : ∀ g : G, ∀ v ∈ W, ρ g v ∈ W) (g : G) (c : K)
    (hs : ∀ v ∈ W, ρ g v = c • v) :
    (invariantSubspaceAction ρ W hW g).toLinearMap = c • (1 : Module.End K W) := by
  ext v
  exact hs v v.property

theorem scalar_commutator_root_of_unity [Module.Finite K V]
    (ρ : G →* (V ≃ₗ[K] V)) (W : Submodule K V)
    (hW : ∀ g : G, ∀ v ∈ W, ρ g v ∈ W) (g h : G) (c : K)
    (hs : ∀ v ∈ W, ρ ⁅g, h⁆ v = c • v) : c ^ Module.finrank K W = 1 := by
  let δ := LinearEquiv.det.comp (invariantSubspaceAction ρ W hW)
  have hd : δ ⁅g, h⁆ = 1 := by
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm _ _)
  have hh := congrArg (fun a : Kˣ => (a : K)) hd
  have hdet : LinearMap.det (invariantSubspaceAction ρ W hW ⁅g, h⁆).toLinearMap = 1 := by
    simpa only [δ, MonoidHom.comp_apply, LinearEquiv.coe_det, Units.val_one] using hh
  rw [invariantSubspaceAction_scalar ρ W hW _ c hs, LinearMap.det_smul, map_one, mul_one] at hdet
  exact hdet

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_CommonEigenspaceCommutators
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A commutator acts trivially on a common eigenspace -/

noncomputable section
namespace PolycyclicRecognition

open scoped commutatorElement
variable {G K V : Type*} [Group G] [Field K] [AddCommGroup V] [Module K V]

theorem commonEigenspace_invariant (ρ : G →* (V ≃ₗ[K] V)) (χ : G → K) :
    ∀ g : G, ∀ v ∈ commonEigenspace (fun g => (ρ g).toLinearMap) χ,
      ρ g v ∈ commonEigenspace (fun g => (ρ g).toLinearMap) χ := by
  intro g v hv
  change (ρ g).toLinearMap v ∈ _
  rw [(mem_commonEigenspace _ _ _).mp hv g]
  exact Submodule.smul_mem _ _ hv

theorem commutator_fixes_commonEigenspace (ρ : G →* (V ≃ₗ[K] V)) (χ : G → K)
    (a : commutator G) (v : V)
    (hv : v ∈ commonEigenspace (fun g => (ρ g).toLinearMap) χ) : ρ a v = v := by
  let W := commonEigenspace (fun g => (ρ g).toLinearMap) χ
  let R := invariantSubspaceAction ρ W (commonEigenspace_invariant ρ χ)
  have hscalar (g : G) : (R g).toLinearMap = χ g • (1 : Module.End K W) :=
    invariantSubspaceAction_scalar ρ W _ g (χ g) (fun v hv =>
      (mem_commonEigenspace _ _ _).mp hv g)
  have hcomm (g h : G) : Commute (R g) (R h) := by
    change R g * R h = R h * R g
    apply LinearEquiv.toLinearMap_injective
    change (R g).toLinearMap * (R h).toLinearMap =
      (R h).toLinearMap * (R g).toLinearMap
    rw [hscalar, hscalar]
    simp [smul_smul, mul_comm]
  have hle : commutator G ≤ R.ker := by
    rw [_root_.commutator_def]
    apply Subgroup.commutator_le.mpr
    intro g _ h _
    change R ⁅g, h⁆ = 1
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_commute.mpr (hcomm g h)
  have ha : R a = 1 := hle a.property
  exact congrArg (fun f : W ≃ₗ[K] W => (f ⟨v, hv⟩ : V)) ha

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_AffinePolynomialTopology
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The polynomial topology on finite affine coordinates

Points are embedded into the prime spectrum by their evaluation kernels.
This gives a Noetherian T1 topology on finitely many field coordinates.
Polynomial coordinate maps are continuous. This is the topology needed
for the finite-component argument for linear groups.
-/

noncomputable section
namespace PolycyclicRecognition

namespace AffinePolynomialPoint

variable {ι κ K : Type*} [Field K]

theorem inducing_toPrime : Topology.IsInducing (toPrime (ι := ι) (K := K)) :=
  Topology.IsInducing.induced _

theorem toPrime_injective : Function.Injective (toPrime (ι := ι) (K := K)) := by
  intro x y h
  apply AffinePolynomialPoint.ext
  funext i
  have he := congrArg PrimeSpectrum.asIdeal h
  have hx : MvPolynomial.X i - MvPolynomial.C (x.coord i) ∈ (toPrime x).asIdeal := by
    change MvPolynomial.eval x.coord _ = 0
    simp
  rw [he] at hx
  change MvPolynomial.eval y.coord _ = 0 at hx
  simpa using (sub_eq_zero.mp (by simpa using hx : y.coord i - x.coord i = 0)).symm

instance instT1Space : T1Space (AffinePolynomialPoint ι K) := by
  constructor
  intro x
  have hclosed : IsClosed ({toPrime x} : Set (PrimeSpectrum (MvPolynomial ι K))) := by
    apply (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mpr
    exact RingHom.ker_isMaximal_of_surjective (MvPolynomial.eval x.coord)
      (fun a => ⟨MvPolynomial.C a, by simp⟩)
  have he : toPrime ⁻¹' {toPrime x} = ({x} : Set (AffinePolynomialPoint ι K)) := by
    ext y
    simp only [Set.mem_preimage, Set.mem_singleton_iff, toPrime_injective.eq_iff]
  rw [← he]
  exact hclosed.preimage inducing_toPrime.continuous

instance instNoetherianSpaceOfFinite [Finite ι] : TopologicalSpace.NoetherianSpace (AffinePolynomialPoint ι K) :=
  inducing_toPrime.noetherianSpace

theorem toPrime_polynomialMap (p : κ → MvPolynomial ι K) (x : AffinePolynomialPoint ι K) :
    toPrime (polynomialMap p x) =
      PrimeSpectrum.comap (MvPolynomial.eval₂Hom MvPolynomial.C p) (toPrime x) := by
  apply PrimeSpectrum.ext
  apply Ideal.ext
  intro q
  change MvPolynomial.eval (MvPolynomial.eval x.coord ∘ p) q = 0 ↔
    MvPolynomial.eval x.coord (MvPolynomial.eval₂ MvPolynomial.C p q) = 0
  rw [MvPolynomial.eval_assoc]

theorem continuous_polynomialMap (p : κ → MvPolynomial ι K) :
    Continuous (polynomialMap p) := by
  apply inducing_toPrime.continuous_iff.mpr
  have he : toPrime ∘ polynomialMap p =
      PrimeSpectrum.comap (MvPolynomial.eval₂Hom MvPolynomial.C p) ∘ toPrime :=
    funext (toPrime_polynomialMap p)
  rw [he]
  exact (PrimeSpectrum.continuous_comap _).comp inducing_toPrime.continuous

theorem isClosed_zeroSet (p : MvPolynomial ι K) :
    IsClosed {x : AffinePolynomialPoint ι K | MvPolynomial.eval x.coord p = 0} := by
  have he : {x : AffinePolynomialPoint ι K | MvPolynomial.eval x.coord p = 0} =
      toPrime ⁻¹' PrimeSpectrum.zeroLocus {p} := by
    ext x
    change _ ↔ ∀ q ∈ ({p} : Set (MvPolynomial ι K)), q ∈ (toPrime x).asIdeal
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, forall_eq]
    rfl
  rw [he]
  exact (PrimeSpectrum.isClosed_zeroLocus _).preimage inducing_toPrime.continuous

end AffinePolynomialPoint
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_PolynomialMatrixGroup
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.PolynomialMatrixGroup.coordinateLinearAction_apply _root_.OAI.PolycyclicRecognition.PolynomialMatrixGroup.scalarExtension_entries _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial topology on invertible matrices

Both a matrix and its inverse are retained as affine coordinates. Inversion
then exchanges coordinates, and translations are polynomial coordinate maps.
The resulting topology is Noetherian and T1. Only separate continuity of
multiplication is asserted; the product topology need not be the affine
polynomial topology on a product.
-/

noncomputable section
namespace PolycyclicRecognition

namespace PolynomialMatrixGroup

variable {K : Type*} [Field K] {n : ℕ}

theorem inducing_coordinates : Topology.IsInducing (coordinates (K := K) (n := n)) :=
  Topology.IsInducing.induced _

instance instNoetherianSpace : TopologicalSpace.NoetherianSpace (PolynomialMatrixGroup K n) :=
  inducing_coordinates.noetherianSpace

theorem continuous_of_polynomial {m : ℕ} (f : PolynomialMatrixGroup K n → PolynomialMatrixGroup K m)
    (p : Coord m → MvPolynomial (Coord n) K)
    (hp : ∀ g, coordinates (f g) = AffinePolynomialPoint.polynomialMap p (coordinates g)) :
    Continuous f := by
  apply inducing_coordinates.continuous_iff.mpr
  have he : coordinates ∘ f = AffinePolynomialPoint.polynomialMap p ∘ coordinates := funext hp
  rw [he]
  exact (AffinePolynomialPoint.continuous_polynomialMap p).comp inducing_coordinates.continuous

theorem coordinates_mul_left (h g : PolynomialMatrixGroup K n) :
    coordinates (h * g) =
      AffinePolynomialPoint.polynomialMap (leftPolynomial h) (coordinates g) := by
  apply AffinePolynomialPoint.ext
  funext ⟨b, i, j⟩
  cases b <;> simp [coordinates, AffinePolynomialPoint.polynomialMap,
    leftPolynomial, mul_inv_rev, Matrix.mul_apply]

theorem coordinates_mul_right (h g : PolynomialMatrixGroup K n) :
    coordinates (g * h) =
      AffinePolynomialPoint.polynomialMap (rightPolynomial h) (coordinates g) := by
  apply AffinePolynomialPoint.ext
  funext ⟨b, i, j⟩
  cases b <;> simp [coordinates, AffinePolynomialPoint.polynomialMap,
    rightPolynomial, mul_inv_rev, Matrix.mul_apply]

instance instSeparatelyContinuousMul : SeparatelyContinuousMul (PolynomialMatrixGroup K n) where
  continuous_const_mul {h} := continuous_of_polynomial _ (leftPolynomial h) (coordinates_mul_left h)
  continuous_mul_const {h} := continuous_of_polynomial _ (rightPolynomial h) (coordinates_mul_right h)

instance instContinuousInv : ContinuousInv (PolynomialMatrixGroup K n) where
  continuous_inv := by
    apply continuous_of_polynomial _ (fun s => MvPolynomial.X (!s.1, s.2.1, s.2.2))
    intro g
    apply AffinePolynomialPoint.ext
    funext ⟨b, i, j⟩
    cases b <;> simp [coordinates, AffinePolynomialPoint.polynomialMap]

end PolynomialMatrixGroup
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_PolynomialMatrixCommutator
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.PolynomialMatrixGroup.coordinateLinearAction_apply _root_.OAI.PolycyclicRecognition.PolynomialMatrixGroup.scalarExtension_entries _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial continuity of commutator sections

For a fixed matrix, conjugation by the variable matrix is polynomial in
the matrix and inverse coordinates. Hence the commutator is continuous
in either variable separately in the polynomial topology.
-/

noncomputable section
namespace PolycyclicRecognition.PolynomialMatrixGroup

open scoped commutatorElement
variable {K : Type*} [Field K] {n : ℕ}

theorem coordinates_conjugation_fixed (h g : PolynomialMatrixGroup K n) :
    coordinates (g * h * g⁻¹) =
      AffinePolynomialPoint.polynomialMap (conjugationPolynomial h) (coordinates g) := by
  have he : (g * h * g⁻¹)⁻¹ = g * h⁻¹ * g⁻¹ := by group
  apply AffinePolynomialPoint.ext
  funext ⟨b, i, j⟩
  cases b <;> simp [coordinates, AffinePolynomialPoint.polynomialMap, conjugationPolynomial,
    he, Matrix.mul_apply, Finset.sum_mul]

theorem continuous_conjugation_fixed (h : PolynomialMatrixGroup K n) :
    Continuous (fun g : PolynomialMatrixGroup K n => g * h * g⁻¹) :=
  continuous_of_polynomial _ (conjugationPolynomial h) (coordinates_conjugation_fixed h)

theorem continuous_commutator_right (h : PolynomialMatrixGroup K n) :
    Continuous (fun g : PolynomialMatrixGroup K n => ⁅g, h⁆) := by
  change Continuous (fun g : PolynomialMatrixGroup K n => (g * h * g⁻¹) * h⁻¹)
  exact (continuous_conjugation_fixed h).mul_const h⁻¹

theorem continuous_commutator_left (g : PolynomialMatrixGroup K n) :
    Continuous (fun h : PolynomialMatrixGroup K n => ⁅g, h⁆) := by
  have he : (fun h : PolynomialMatrixGroup K n => ⁅g, h⁆) =
      fun h => (⁅h, g⁆)⁻¹ := by
    funext h
    exact (commutatorElement_inv h g).symm
  rw [he]
  exact (continuous_commutator_right g).inv

end PolycyclicRecognition.PolynomialMatrixGroup

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_NormalEigencharacters
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

namespace OAI

/-! # Finite-index stabilizers of normal-subgroup eigenspaces

Conjugation permutes the common eigenvalue functions of a normal subgroup.
There are only finitely many nonzero common eigenspaces. Consequently every
one of them is invariant under a subgroup of finite index in the ambient
group. This separates the finite permutation from the linear action.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped IsMulCommutative

variable {G K V : Type*} [Group G] [Field K] [AddCommGroup V] [Module K V]
  (A : Subgroup G) [A.Normal]

omit [A.Normal] in
theorem mem_normalCommonEigenspace (ρ : G →* (V ≃ₗ[K] V)) (χ : A → K) (v : V) :
    v ∈ normalCommonEigenspace A ρ χ ↔ ∀ a : A, ρ a v = χ a • v :=
  mem_commonEigenspace _ _ _

theorem normalCommonEigenspace_conjugate (ρ : G →* (V ≃ₗ[K] V))
    (χ : A → K) (g : G) {v : V} (hv : v ∈ normalCommonEigenspace A ρ χ) :
    ρ g v ∈ normalCommonEigenspace A ρ (conjugateWeightPerm A g χ) := by
  rw [mem_normalCommonEigenspace] at hv ⊢
  intro a
  have he : ρ (a : G) * ρ g = ρ g * ρ (MulAut.conjNormal (H := A) g⁻¹ a : A) := by
    rw [← map_mul, ← map_mul]
    congr 1
    simp only [MulAut.conjNormal_apply, inv_inv]
    group
  calc
    ρ a (ρ g v) = ρ g (ρ (MulAut.conjNormal (H := A) g⁻¹ a : A) v) :=
      congrArg (fun e : V ≃ₗ[K] V => e v) he
    _ = χ (MulAut.conjNormal (H := A) g⁻¹ a) • ρ g v := by rw [hv, map_smul]
    _ = _ := rfl

theorem normalCommonEigenspace_conjugate_ne_bot (ρ : G →* (V ≃ₗ[K] V))
    (χ : A → K) (g : G) (hχ : normalCommonEigenspace A ρ χ ≠ ⊥) :
    normalCommonEigenspace A ρ (conjugateWeightPerm A g χ) ≠ ⊥ := by
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hχ
  intro he
  have hh := normalCommonEigenspace_conjugate A ρ χ g hv
  rw [he, Submodule.mem_bot] at hh
  exact hv0 ((ρ g).injective (hh.trans (map_zero _).symm))

theorem exists_finiteIndex_preserving_commonEigenspace [Module.Finite K V]
    (ρ : G →* (V ≃ₗ[K] V)) (χ : A → K)
    (hχ : normalCommonEigenspace A ρ χ ≠ ⊥) :
    ∃ H : Subgroup G, H.FiniteIndex ∧
      ∀ g ∈ H, ∀ v ∈ normalCommonEigenspace A ρ χ,
        ρ g v ∈ normalCommonEigenspace A ρ χ := by
  let : MulAction G (A → K) := MulAction.compHom (A → K) (conjugateWeightPerm (K := K) A)
  have hfinite : (MulAction.orbit G χ).Finite := by
    apply (finite_commonEigenspaces (fun a : A => (ρ a).toLinearMap)).subset
    rintro _ ⟨g, rfl⟩
    exact normalCommonEigenspace_conjugate_ne_bot A ρ χ g hχ
  let H := MulAction.stabilizer G χ
  let : Finite (MulAction.orbit G χ) := hfinite
  have hH : H.FiniteIndex := by
    let : Finite (G ⧸ H) := Finite.of_equiv (MulAction.orbit G χ)
      (MulAction.orbitEquivQuotientStabilizer G χ)
    exact Subgroup.finiteIndex_of_finite_quotient
  refine ⟨H, hH, ?_⟩
  intro g hg v hv
  have he : conjugateWeightPerm A g χ = χ := hg
  simpa only [he] using normalCommonEigenspace_conjugate A ρ χ g hv

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_NoetherianComponents
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finitely many connected components in a Noetherian space

Each irreducible component lies in one connected component, and every
point lies in an irreducible component. The finite irreducible-component
cover therefore gives finitely many connected components.
-/

noncomputable section
namespace PolycyclicRecognition

variable {X : Type*} [TopologicalSpace X] [TopologicalSpace.NoetherianSpace X]

theorem finite_connectedComponents_of_noetherian : Finite (ConnectedComponents X) := by
  classical
  let I := irreducibleComponents X
  have hI : I.Finite := TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
  let : Finite I := hI
  let point (s : I) : X := s.property.prop.nonempty.choose
  have hpoint (s : I) : point s ∈ (s : Set X) := s.property.prop.nonempty.choose_spec
  let q : I → ConnectedComponents X := fun s => ConnectedComponents.mk (point s)
  apply Finite.of_surjective q
  intro c
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
  let s : I := ⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩
  refine ⟨s, ?_⟩
  apply ConnectedComponents.coe_eq_coe'.mpr
  exact s.property.prop.2.isPreconnected.subset_connectedComponent
    mem_irreducibleComponent (hpoint s)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_SeparateGroupClosure
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Closures and components using separately continuous multiplication

Polynomial matrix groups have this weaker topological structure. It is
enough to form subgroup closures and the normal identity component. In a
Noetherian space the latter has finite index.
-/

noncomputable section
namespace PolycyclicRecognition

variable {G : Type*} [Group G] [TopologicalSpace G]
  [SeparatelyContinuousMul G] [ContinuousInv G]

theorem separateClosure_closed (S : Subgroup G) : IsClosed (separateClosure S : Set G) :=
  isClosed_closure

theorem separateIdentityComponent_preconnected :
    IsPreconnected (separateIdentityComponent G : Set G) := isPreconnected_connectedComponent

theorem separateIdentityComponent_finiteIndex [TopologicalSpace.NoetherianSpace G] :
    (separateIdentityComponent G).FiniteIndex := by
  let C := separateIdentityComponent G
  let : Finite (ConnectedComponents G) := finite_connectedComponents_of_noetherian
  let q : ConnectedComponents G → G ⧸ C := Quotient.lift
    (fun g => (g : G ⧸ C)) (by
      intro x y hxy
      apply QuotientGroup.eq_iff_div_mem.mpr
      change x / y ∈ connectedComponent (1 : G)
      have hx : x ∈ connectedComponent y := hxy ▸ mem_connectedComponent
      have hm := (continuous_mul_const y⁻¹).mapsTo_connectedComponent y hx
      simpa only [div_eq_mul_inv, mul_inv_cancel] using hm)
  have hq : Function.Surjective q := by
    intro z
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective C z
    exact ⟨ConnectedComponents.mk g, rfl⟩
  let : Finite (G ⧸ C) := Finite.of_surjective q hq
  exact Subgroup.finiteIndex_of_finite_quotient

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_SeparateFiniteIndexDensity
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite-index subgroups are dense in a connected polynomial group

A closed subgroup of finite index is open: its finite quotient is T1 and
therefore discrete. The argument uses only continuous translations. In a
connected group this forces the closure of every finite-index subgroup to
be the whole group.
-/

noncomputable section
namespace PolycyclicRecognition

variable {G : Type*} [Group G] [TopologicalSpace G]
  [SeparatelyContinuousMul G] [ContinuousInv G]

omit [ContinuousInv G] in
theorem separate_isOpen_of_closed_finiteIndex (H : Subgroup G) [H.FiniteIndex]
    (hH : IsClosed (H : Set G)) : IsOpen (H : Set G) := by
  let q : G → G ⧸ H := Quotient.mk''
  let : TopologicalSpace (G ⧸ H) := TopologicalSpace.coinduced q inferInstance
  have hq : Topology.IsQuotientMap q := isQuotientMap_quot_mk
  let : T1Space (G ⧸ H) := by
    constructor
    intro z
    obtain ⟨r, rfl⟩ := Quotient.exists_rep z
    apply hq.isCoinducing.isClosed_preimage.mp
    have he : q ⁻¹' {q r} = (fun g : G => r⁻¹ * g) ⁻¹' (H : Set G) := by
      ext g
      change q g = q r ↔ r⁻¹ * g ∈ H
      rw [eq_comm, QuotientGroup.eq]
    rw [he]
    exact hH.preimage (continuous_const_mul r⁻¹)
  have he : q ⁻¹' {q 1} = (H : Set G) := by
    ext g
    change q g = q 1 ↔ g ∈ H
    rw [eq_comm, QuotientGroup.eq, inv_one, one_mul]
  rw [← he]
  exact (isOpen_discrete _).preimage hq.continuous

theorem separateClosure_eq_top_of_finiteIndex [PreconnectedSpace G]
    (H : Subgroup G) [H.FiniteIndex] : separateClosure H = ⊤ := by
  let C := separateClosure H
  let : C.FiniteIndex := Subgroup.finiteIndex_of_le (show H ≤ C from subset_closure)
  have hCclosed : IsClosed (C : Set G) := separateClosure_closed H
  have hopen := separate_isOpen_of_closed_finiteIndex C hCclosed
  have he : (C : Set G) = Set.univ :=
    (show IsClopen (C : Set G) from ⟨hCclosed, hopen⟩).eq_univ ⟨1, C.one_mem⟩
  exact SetLike.ext' he

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_PolynomialMatrixStabilizer
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.PolynomialMatrixGroup.coordinateLinearAction_apply _root_.OAI.PolycyclicRecognition.PolynomialMatrixGroup.scalarExtension_entries _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

namespace OAI

/-! # Closed linear stabilizers in the polynomial matrix topology

Membership of a matrix translate in a subspace is a family of polynomial
equations, obtained from its annihilating linear functionals. Consequently
the finite-index common eigenspace stabilizer is dense and fixes that
eigenspace under a connected matrix group.
-/

noncomputable section
namespace PolycyclicRecognition.PolynomialMatrixGroup

variable {K : Type*} [Field K] {n : ℕ}

theorem linearAction_apply (g : PolynomialMatrixGroup K n) (v : Fin n → K) :
    linearAction g v = Matrix.mulVec (entries g) v := rfl

theorem eval_functionalPolynomial (φ : Module.Dual K (Fin n → K))
    (v : Fin n → K) (g : PolynomialMatrixGroup K n) :
    MvPolynomial.eval (coordinates g).coord (functionalPolynomial φ v) =
      φ (linearAction g v) := by
  rw [linearAction_apply, LinearMap.pi_apply_eq_sum_univ]
  simp [functionalPolynomial, coordinates, Matrix.mulVec, dotProduct,
    Finset.sum_mul, mul_assoc, mul_comm, mul_left_comm]

theorem isClosed_linearAction_mem (W : Submodule K (Fin n → K)) (v : Fin n → K) :
    IsClosed {g : PolynomialMatrixGroup K n | linearAction g v ∈ W} := by
  have he : {g : PolynomialMatrixGroup K n | linearAction g v ∈ W} =
      ⋂ (φ : Module.Dual K (Fin n → K)) (_ : φ ∈ W.dualAnnihilator),
        {g | φ (linearAction g v) = 0} := by
    ext g
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    exact (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff W _).symm
  rw [he]
  apply isClosed_iInter
  intro φ
  apply isClosed_iInter
  intro _
  have hc := (AffinePolynomialPoint.isClosed_zeroSet (functionalPolynomial φ v)).preimage
    inducing_coordinates.continuous
  simpa only [Set.preimage_ofPred_eq, eval_functionalPolynomial] using hc

theorem isClosed_preserves_subspace (W : Submodule K (Fin n → K)) :
    IsClosed {g : PolynomialMatrixGroup K n | ∀ v ∈ W, linearAction g v ∈ W} := by
  have he : {g : PolynomialMatrixGroup K n | ∀ v ∈ W, linearAction g v ∈ W} =
      ⋂ (v : Fin n → K) (_ : v ∈ W), {g | linearAction g v ∈ W} := by
    ext g
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
  rw [he]
  exact isClosed_iInter fun v => isClosed_iInter fun _ => isClosed_linearAction_mem W v

theorem connected_invariant_commonEigenspace
    {G : Type*} [Group G] [TopologicalSpace G] [PreconnectedSpace G]
    [SeparatelyContinuousMul G] [ContinuousInv G]
    (ι : G →* PolynomialMatrixGroup K n) (hι : Continuous ι)
    (A : Subgroup G) [A.Normal] (χ : A → K)
    (hχ : normalCommonEigenspace A (linearAction.toMonoidHom.comp ι) χ ≠ ⊥) :
    ∀ g : G, ∀ v ∈ normalCommonEigenspace A (linearAction.toMonoidHom.comp ι) χ,
      linearAction (ι g) v ∈ normalCommonEigenspace A (linearAction.toMonoidHom.comp ι) χ := by
  let ρ := linearAction.toMonoidHom.comp ι
  obtain ⟨H, hH, hpres⟩ := exists_finiteIndex_preserving_commonEigenspace A ρ χ hχ
  let := hH
  let W := normalCommonEigenspace A ρ χ
  have hclosed : IsClosed {g : G | ∀ v ∈ W, ρ g v ∈ W} :=
    (isClosed_preserves_subspace W).preimage hι
  have hcontains : closure (H : Set G) ⊆ {g : G | ∀ v ∈ W, ρ g v ∈ W} :=
    closure_minimal hpres hclosed
  have he := separateClosure_eq_top_of_finiteIndex H
  intro g
  apply hcontains
  change g ∈ separateClosure H
  rw [he]
  trivial

end PolycyclicRecognition.PolynomialMatrixGroup

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_ConnectedScalarCommutators
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.PolynomialMatrixGroup.coordinateLinearAction_apply _root_.OAI.PolycyclicRecognition.PolynomialMatrixGroup.scalarExtension_entries _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Scalar commutators of a connected matrix group are trivial

On an invariant subspace a scalar commutator is a root of unity by its
determinant. For each vector its orbit under these commutators is therefore
finite. Polynomial continuity and connectedness make this orbit constant.
-/

noncomputable section
namespace PolycyclicRecognition.PolynomialMatrixGroup

open scoped commutatorElement
variable {K : Type*} [Field K] {n : ℕ}

theorem continuous_vectorAction (v : Fin n → K) :
    Continuous (fun g : PolynomialMatrixGroup K n =>
      (⟨linearAction g v⟩ : AffinePolynomialPoint (Fin n) K)) := by
  have he : (fun g : PolynomialMatrixGroup K n =>
      (⟨linearAction g v⟩ : AffinePolynomialPoint (Fin n) K)) =
      AffinePolynomialPoint.polynomialMap (vectorPolynomial v) ∘ coordinates := by
    funext g
    apply AffinePolynomialPoint.ext
    funext i
    simp [vectorPolynomial, AffinePolynomialPoint.polynomialMap, coordinates,
      linearAction_apply, Matrix.mulVec, dotProduct]
  rw [he]
  exact (AffinePolynomialPoint.continuous_polynomialMap _).comp inducing_coordinates.continuous

theorem finite_power_eq_one (d : ℕ) (hd : 0 < d) : {c : K | c ^ d = 1}.Finite := by
  have hp := Polynomial.finite_setOfPred_isRoot (Polynomial.X_pow_sub_C_ne_zero hd (1 : K))
  simpa only [Polynomial.IsRoot.def, Polynomial.eval_sub, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero] using hp

theorem connected_scalar_commutators_trivial
    {G : Type*} [Group G] [TopologicalSpace G] [PreconnectedSpace G]
    (ι : G →* PolynomialMatrixGroup K n) (hι : Continuous ι)
    (W : Submodule K (Fin n → K))
    (hW : ∀ g : G, ∀ v ∈ W, linearAction (ι g) v ∈ W)
    (hs : ∀ g h : G, ∃ c : K, ∀ v ∈ W,
      linearAction (ι ⁅g, h⁆) v = c • v) :
    ∀ g h : G, ∀ v ∈ W, linearAction (ι ⁅g, h⁆) v = v := by
  by_cases hWzero : W = ⊥
  · intro g h v hv
    have hv0 : v = 0 := by simpa only [hWzero, Submodule.mem_bot] using hv
    rw [hv0, map_zero]
  let : Nontrivial W := (Submodule.nontrivial_iff_ne_bot).mpr hWzero
  let ρ := linearAction.toMonoidHom.comp ι
  let d := Module.finrank K W
  let Z := {c : K | c ^ d = 1}
  have hZfinite : Z.Finite := finite_power_eq_one d (Module.finrank_pos (R := K) (M := W))
  intro g h v hv
  let f : G → AffinePolynomialPoint (Fin n) K := fun a => ⟨ρ ⁅a, h⁆ v⟩
  have hf : Continuous f := by
    have he : f = fun a : G =>
        (⟨linearAction ⁅ι a, ι h⁆ v⟩ : AffinePolynomialPoint (Fin n) K) := by
      funext a
      dsimp [f, ρ]
      rw [map_commutatorElement]
    rw [he]
    have hc := (continuous_commutator_right (ι h)).comp hι
    exact (continuous_vectorAction v).comp hc
  let T : Set (AffinePolynomialPoint (Fin n) K) :=
    (fun c : K => (⟨c • v⟩ : AffinePolynomialPoint (Fin n) K)) '' Z
  have hTfinite : T.Finite := hZfinite.image _
  have hmap : Set.MapsTo f Set.univ T := by
    intro a _
    obtain ⟨c, hc⟩ := hs a h
    have hroot : c ^ d = 1 := scalar_commutator_root_of_unity ρ W hW a h c hc
    exact ⟨c, hroot, congrArg AffinePolynomialPoint.mk (hc v hv).symm⟩
  have hfg : f g = f 1 := isPreconnected_univ.constant_of_mapsTo
    hTfinite.isDiscrete hf.continuousOn hmap (Set.mem_univ g) (Set.mem_univ 1)
  have he := congrArg AffinePolynomialPoint.coord hfg
  simp only [f, commutatorElement_one_left, map_one] at he
  exact he

end PolycyclicRecognition.PolynomialMatrixGroup

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_SeparateConnectedGeneration
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Connected generation with separately continuous operations

Two points in the image of a separately continuous two-variable map are
joined by two intersecting connected slices. A connected set containing
the identity then generates a connected subgroup, by taking the identity
component inside the generated subgroup itself.
-/

noncomputable section
namespace PolycyclicRecognition

theorem isPreconnected_image2_separate {X Y Z : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (f : X → Y → Z) (hf₁ : ∀ x, Continuous (f x))
    (hf₂ : ∀ y, Continuous (fun x => f x y))
    {s : Set X} {t : Set Y} (hs : IsPreconnected s) (ht : IsPreconnected t) :
    IsPreconnected (Set.image2 f s t) := by
  apply isPreconnected_of_forall_pair
  rintro _ ⟨a₁, ha₁, b₁, hb₁, rfl⟩ _ ⟨a₂, ha₂, b₂, hb₂, rfl⟩
  refine ⟨f a₁ '' t ∪ (fun a => f a b₂) '' s, ?_,
    Or.inl ⟨b₁, hb₁, rfl⟩, Or.inr ⟨a₂, ha₂, rfl⟩, ?_⟩
  · rintro _ (⟨b, hb, rfl⟩ | ⟨a, ha, rfl⟩)
    · exact ⟨a₁, ha₁, b, hb, rfl⟩
    · exact ⟨a, ha, b₂, hb₂, rfl⟩
  · exact (ht.image _ (hf₁ a₁).continuousOn).union (f a₁ b₂)
      ⟨b₂, hb₂, rfl⟩ ⟨a₁, ha₁, rfl⟩ (hs.image _ (hf₂ b₂).continuousOn)

variable {G : Type*} [Group G] [TopologicalSpace G]
  [SeparatelyContinuousMul G] [ContinuousInv G]

theorem isPreconnected_subgroup_closure {s : Set G} (hs : IsPreconnected s) (h1 : 1 ∈ s) :
    IsPreconnected (Subgroup.closure s : Set G) := by
  let H := Subgroup.closure s
  let : SeparatelyContinuousMul H :=
    Topology.IsInducing.subtypeVal.separatelyContinuousMul H.subtype
  let : ContinuousInv H := Topology.IsInducing.subtypeVal.continuousInv (fun _ => rfl)
  let T : Set H := H.subtype ⁻¹' s
  have he : H.subtype '' T = s := by
    ext g
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hg
      exact ⟨⟨g, Subgroup.subset_closure hg⟩, hg, rfl⟩
  have hT : IsPreconnected T :=
    Topology.IsInducing.subtypeVal.isPreconnected_image.mp (he.symm ▸ hs)
  have hT1 : (1 : H) ∈ T := h1
  let C := separateIdentityComponent H
  have hsC : s ⊆ (C.map H.subtype : Set G) := by
    intro g hg
    let x : H := ⟨g, Subgroup.subset_closure hg⟩
    exact ⟨x, hT.subset_connectedComponent hT1 hg, rfl⟩
  have hHC : H ≤ C.map H.subtype := (Subgroup.closure_le _).mpr hsC
  have hC : C = ⊤ := by
    apply top_unique
    intro h _
    obtain ⟨c, hc, heq⟩ := hHC h.property
    have hh : c = h := Subtype.ext heq
    exact hh ▸ hc
  have hpre : IsPreconnected (Set.univ : Set H) := by
    have hc := separateIdentityComponent_preconnected (G := H)
    change IsPreconnected (C : Set H) at hc
    simpa only [hC, Subgroup.coe_top] using hc
  have himage := hpre.image H.subtype continuous_subtype_val.continuousOn
  have hrange : Set.range H.subtype = (H : Set G) := by
    ext g
    exact ⟨fun ⟨h, hh⟩ => hh ▸ h.property, fun hg => ⟨⟨g, hg⟩, rfl⟩⟩
  simpa only [Set.image_univ, hrange] using himage

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_SeparateDerivedClosure
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Derived subgroups in the polynomial group topology

Separate continuity of commutators passes derived-series bounds to closure.
It also makes the subgroup generated by the commutators of connected
subgroups connected. These are the two closure facts required in the
solvable matrix-group argument.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped commutatorElement
variable {G : Type*} [Group G] [TopologicalSpace G]
  [SeparatelyContinuousMul G] [ContinuousInv G]
  (hc₁ : ∀ g : G, Continuous (fun h : G => ⁅g, h⁆))
  (hc₂ : ∀ h : G, Continuous (fun g : G => ⁅g, h⁆))

include hc₁ hc₂

theorem isPreconnected_commutator (S T : Subgroup G)
    (hS : IsPreconnected (S : Set G)) (hT : IsPreconnected (T : Set G)) :
    IsPreconnected ((⁅S, T⁆ : Subgroup G) : Set G) := by
  rw [Subgroup.commutator_def]
  apply isPreconnected_subgroup_closure
  · exact isPreconnected_image2_separate (fun g h : G => ⁅g, h⁆) hc₁ hc₂ hS hT
  · exact ⟨1, S.one_mem, 1, T.one_mem, by simp⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_ConnectedSolvableEigenvector
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A common eigenvector for a connected solvable matrix action

Induct on the derived length. The connected derived subgroup has a common
eigenspace. The whole group preserves it, and acts there with scalar
commutators. Those commutators are trivial by connectedness and determinant
one, leaving a commuting action on this nonzero subspace.
-/

noncomputable section
namespace PolycyclicRecognition.PolynomialMatrixGroup

open scoped commutatorElement
variable {K : Type*} [Field K] [IsAlgClosed K] {n : ℕ} [Nontrivial (Fin n → K)]

theorem connected_solvable_commonEigenspace_of_bound
    {G : Type*} [Group G] [TopologicalSpace G] [PreconnectedSpace G]
    [SeparatelyContinuousMul G] [ContinuousInv G]
    (hc₁ : ∀ g : G, Continuous (fun h : G => ⁅g, h⁆))
    (hc₂ : ∀ h : G, Continuous (fun g : G => ⁅g, h⁆))
    (ι : G →* PolynomialMatrixGroup K n) (hι : Continuous ι)
    (d : ℕ) (hd : derivedSeries G d = ⊥) :
    ∃ χ : G → K, commonEigenspace (fun g => (linearAction (ι g)).toLinearMap) χ ≠ ⊥ := by
  induction d generalizing G with
  | zero =>
    have hg1 (g : G) : g = 1 := by
      have hg : g ∈ derivedSeries G 0 := Subgroup.mem_top g
      simpa only [hd, Subgroup.mem_bot] using hg
    obtain ⟨v, hv⟩ := exists_ne (0 : Fin n → K)
    refine ⟨fun _ => 1, ?_⟩
    intro he
    have hm : v ∈ commonEigenspace (fun g => (linearAction (ι g)).toLinearMap) (fun _ => 1) := by
      apply (mem_commonEigenspace _ _ _).mpr
      intro g
      simp only [hg1 g, map_one, one_smul]
      rfl
    exact hv (by simpa only [he, Submodule.mem_bot] using hm)
  | succ d ih =>
    let A := commutator G
    let : SeparatelyContinuousMul A :=
      Topology.IsInducing.subtypeVal.separatelyContinuousMul A.subtype
    let : ContinuousInv A := Topology.IsInducing.subtypeVal.continuousInv (fun _ => rfl)
    have hApre : IsPreconnected (A : Set G) := by
      simpa only [A, _root_.commutator_def, Subgroup.coe_top] using
        isPreconnected_commutator hc₁ hc₂ (⊤ : Subgroup G) ⊤
          isPreconnected_univ isPreconnected_univ
    let : PreconnectedSpace A := Subtype.preconnectedSpace hApre
    have hAc₁ (g : A) : Continuous (fun h : A => ⁅g, h⁆) := by
      apply Topology.IsInducing.subtypeVal.continuous_iff.mpr
      exact (hc₁ (g : G)).comp continuous_subtype_val
    have hAc₂ (h : A) : Continuous (fun g : A => ⁅g, h⁆) := by
      apply Topology.IsInducing.subtypeVal.continuous_iff.mpr
      exact (hc₂ (h : G)).comp continuous_subtype_val
    have hshift (k : ℕ) : (derivedSeries A k).map A.subtype = derivedSeries G (k + 1) := by
      induction k with
      | zero => simp only [derivedSeries_zero, ← MonoidHom.range_eq_map, Subgroup.range_subtype,
          Nat.zero_add, derivedSeries_one, A]
      | succ k ihk =>
        simp only [derivedSeries_succ, Subgroup.map_commutator, ihk]
    have hAd : derivedSeries A d = ⊥ := by
      apply Subgroup.map_injective (f := A.subtype) Subtype.val_injective
      rw [Subgroup.map_bot, hshift, hd]
    obtain ⟨χA, hχA⟩ := ih hAc₁ hAc₂ (ι.comp A.subtype)
      (hι.comp continuous_subtype_val) hAd
    let ρ := linearAction.toMonoidHom.comp ι
    change normalCommonEigenspace A ρ χA ≠ ⊥ at hχA
    let W := normalCommonEigenspace A ρ χA
    have hW : ∀ g : G, ∀ v ∈ W, ρ g v ∈ W :=
      connected_invariant_commonEigenspace ι hι A χA hχA
    have hs : ∀ g h : G, ∃ c : K, ∀ v ∈ W, ρ ⁅g, h⁆ v = c • v := by
      intro g h
      have hgh : ⁅g, h⁆ ∈ A := by
        change ⁅g, h⁆ ∈ (⁅(⊤ : Subgroup G), ⊤⁆ : Subgroup G)
        exact Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top h)
      refine ⟨χA ⟨⁅g, h⁆, hgh⟩, ?_⟩
      intro v hv
      exact (mem_normalCommonEigenspace A ρ χA v).mp hv ⟨⁅g, h⁆, hgh⟩
    have htriv := connected_scalar_commutators_trivial ι hι W hW hs
    let R := invariantSubspaceAction ρ W hW
    let : Nontrivial W := (Submodule.nontrivial_iff_ne_bot).mpr hχA
    have hR (g h : G) : R ⁅g, h⁆ = 1 := by
      apply LinearEquiv.ext
      intro v
      apply Subtype.ext
      exact htriv g h v v.property
    have hcomm (g h : G) : Commute (R g).toLinearMap (R h).toLinearMap := by
      have hh : Commute (R g) (R h) := commutatorElement_eq_one_iff_commute.mp
        (by rw [← map_commutatorElement]; exact hR g h)
      exact hh.map LinearEquiv.automorphismGroup.toLinearMapMonoidHom
    obtain ⟨χ, hχ⟩ := exists_commonEigenspace (fun g => (R g).toLinearMap) hcomm
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hχ
    refine ⟨χ, ?_⟩
    intro he
    have hvG : (v : Fin n → K) ∈
        commonEigenspace (fun g => (linearAction (ι g)).toLinearMap) χ := by
      apply (mem_commonEigenspace _ _ _).mpr
      intro g
      exact congrArg Subtype.val ((mem_commonEigenspace _ _ _).mp hv g)
    have hz : (v : Fin n → K) = 0 := by simpa only [he, Submodule.mem_bot] using hvG
    exact hv0 (Subtype.ext hz)

theorem connected_solvable_commonEigenspace
    {G : Type*} [Group G] [TopologicalSpace G] [PreconnectedSpace G]
    [SeparatelyContinuousMul G] [ContinuousInv G] [Group.IsSolvable G]
    (hc₁ : ∀ g : G, Continuous (fun h : G => ⁅g, h⁆))
    (hc₂ : ∀ h : G, Continuous (fun g : G => ⁅g, h⁆))
    (ι : G →* PolynomialMatrixGroup K n) (hι : Continuous ι) :
    ∃ χ : G → K, commonEigenspace (fun g => (linearAction (ι g)).toLinearMap) χ ≠ ⊥ := by
  obtain ⟨d, hd⟩ := Group.IsSolvable.solvable (G := G)
  exact connected_solvable_commonEigenspace_of_bound hc₁ hc₂ ι hι d hd

end PolycyclicRecognition.PolynomialMatrixGroup

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_PolynomialQuotientAction
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.PolynomialMatrixGroup.scalarExtension_entries _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial coordinates for induced quotient actions

Choose lifts of a quotient basis. Every forward and inverse matrix entry
of the induced action is then one linear functional of an ambient translate.
This gives continuity for the concrete polynomial matrix topology.
-/

noncomputable section
namespace PolycyclicRecognition.PolynomialMatrixGroup

variable {K G U : Type*} [Field K] [Group G] [AddCommGroup U] [Module K U]
    {m n : ℕ}

theorem coordinateLinearAction_entries (ρ : G →* (U ≃ₗ[K] U))
    (e : U ≃ₗ[K] (Fin m → K)) (g : G) (i j : Fin m) :
    entries (coordinateLinearAction ρ e g) i j =
      e (ρ g (e.symm (Pi.single j 1))) i := by
  rw [← coordinateLinearAction_apply, linearAction_apply, Matrix.mulVec_single_one]
  rfl

theorem eval_functionalPolynomialAt (b : Bool) (φ : Module.Dual K (Fin n → K))
    (v : Fin n → K) (g : PolynomialMatrixGroup K n) :
    MvPolynomial.eval (coordinates g).coord (functionalPolynomialAt b φ v) =
      φ (linearAction (if b then g⁻¹ else g) v) := by
  cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
    rw [linearAction_apply, LinearMap.pi_apply_eq_sum_univ] <;>
    simp [functionalPolynomialAt, coordinates, Matrix.mulVec,
      dotProduct, Finset.sum_mul,
      mul_assoc, mul_comm, mul_left_comm]

theorem continuous_quotientLinearAction
    [TopologicalSpace G] (ι : G →* PolynomialMatrixGroup K n) (hι : Continuous ι)
    (W : Submodule K (Fin n → K))
    (hW : ∀ g : G, ∀ v ∈ W, linearAction (ι g) v ∈ W)
    (e : ((Fin n → K) ⧸ W) ≃ₗ[K] (Fin m → K)) :
    Continuous (coordinateLinearAction
      (quotientLinearAction (linearAction.toMonoidHom.comp ι) W hW) e) := by
  let ρ := quotientLinearAction (linearAction.toMonoidHom.comp ι) W hW
  let v (j : Fin m) : Fin n → K :=
    Function.surjInv W.mkQ_surjective (e.symm (Pi.single j 1))
  have hv (j : Fin m) : W.mkQ (v j) = e.symm (Pi.single j 1) :=
    Function.rightInverse_surjInv W.mkQ_surjective _
  let φ (i : Fin m) : Module.Dual K (Fin n → K) :=
    (LinearMap.proj i).comp (e.toLinearMap.comp W.mkQ)
  let p (s : Coord m) : MvPolynomial (Coord n) K :=
    functionalPolynomialAt s.1 (φ s.2.1) (v s.2.2)
  apply inducing_coordinates.continuous_iff.mpr
  have he : coordinates ∘ coordinateLinearAction ρ e =
      AffinePolynomialPoint.polynomialMap p ∘ coordinates ∘ ι := by
    funext g
    apply AffinePolynomialPoint.ext
    funext ⟨b, i, j⟩
    change (if b then entries ((coordinateLinearAction ρ e g)⁻¹) i j
      else entries (coordinateLinearAction ρ e g) i j) =
      MvPolynomial.eval (coordinates (ι g)).coord
        (functionalPolynomialAt b (φ i) (v j))
    rw [eval_functionalPolynomialAt]
    cases b <;> simp only [Bool.false_eq_true, ↓reduceIte, ← map_inv,
      coordinateLinearAction_entries]
    · rw [← hv j]
      rfl
    · rw [← hv j]
      rfl
  rw [he]
  exact ((AffinePolynomialPoint.continuous_polynomialMap p).comp
    inducing_coordinates.continuous).comp hι

end PolycyclicRecognition.PolynomialMatrixGroup

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_ConnectedSolvableUnipotence
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform unipotence of the commutator action

Successive common eigenspaces of a connected solvable matrix action are
fixed by its commutator subgroup. Induction on the quotient dimension
therefore makes every sufficiently long mixed product of commutator
action differences zero.
-/

noncomputable section
namespace PolycyclicRecognition.PolynomialMatrixGroup

open scoped commutatorElement
variable {K G : Type*} [Field K] [IsAlgClosed K] [Group G]
    [TopologicalSpace G] [PreconnectedSpace G] [SeparatelyContinuousMul G]
    [ContinuousInv G] [Group.IsSolvable G]

theorem connected_solvable_commutator_words {n : ℕ}
    (hc₁ : ∀ g : G, Continuous (fun h : G => ⁅g, h⁆))
    (hc₂ : ∀ h : G, Continuous (fun g : G => ⁅g, h⁆))
    (ι : G →* PolynomialMatrixGroup K n) (hι : Continuous ι) :
    ∃ c : ℕ, ∀ w : List (commutator G), w.length = c →
      actionOperatorWord (fun a : commutator G =>
        (linearAction (ι a)).toLinearMap - 1) w = 0 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n = 0
    · subst n
      refine ⟨0, fun _ _ => ?_⟩
      ext v i
      exact Fin.elim0 i
    let : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero hn⟩⟩
    obtain ⟨χ, hχ⟩ := connected_solvable_commonEigenspace hc₁ hc₂ ι hι
    let ρ := linearAction.toMonoidHom.comp ι
    let W := commonEigenspace (fun g => (ρ g).toLinearMap) χ
    have hW : ∀ g : G, ∀ v ∈ W, ρ g v ∈ W := commonEigenspace_invariant ρ χ
    let : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hχ
    let m := Module.finrank K ((Fin n → K) ⧸ W)
    have hm : m < n := by
      have he := W.finrank_quotient_add_finrank
      have hp := Module.finrank_pos (R := K) (M := W)
      rw [Module.finrank_fin_fun] at he
      change m + Module.finrank K W = n at he
      omega
    let e := (Module.finBasis K ((Fin n → K) ⧸ W)).equivFun
    let ρQ := quotientLinearAction ρ W hW
    let ιQ : G →* PolynomialMatrixGroup K m := coordinateLinearAction ρQ e
    have hιQ : Continuous ιQ := continuous_quotientLinearAction ι hι W hW e
    obtain ⟨c, hc⟩ := ih m hm ιQ hιQ
    let D := fun a : commutator G => (ρ a).toLinearMap - 1
    let E := fun a : commutator G => (linearAction (ιQ a)).toLinearMap - 1
    let q : (Fin n → K) →ₗ[K] (Fin m → K) := e.toLinearMap.comp W.mkQ
    have hint (a : commutator G) (v : Fin n → K) : q (D a v) = E a (q v) := by
      change q (ρ a v - v) = linearAction (ιQ a) (q v) - q v
      rw [map_sub, coordinateLinearAction_apply]
      change e (W.mkQ (ρ a v)) - q v = e (ρQ a (e.symm (e (W.mkQ v)))) - q v
      rw [e.symm_apply_apply]
      rfl
    refine ⟨c + 1, ?_⟩
    intro w hw
    cases w with
    | nil => simp only [List.length_nil] at hw; omega
    | cons a w =>
      have hw' : w.length = c := by simp only [List.length_cons] at hw; omega
      have hz : actionOperatorWord E w = 0 := hc w hw'
      apply LinearMap.ext
      intro v
      change ρ a (actionOperatorWord D w v) - actionOperatorWord D w v = 0
      apply sub_eq_zero.mpr
      apply commutator_fixes_commonEigenspace ρ χ a
      change actionOperatorWord D w v ∈ W
      apply (Submodule.Quotient.mk_eq_zero W).mp
      apply e.injective
      have hq := actionOperatorWord_intertwines D E q hint w v
      rw [hz] at hq
      simpa only [q, LinearMap.comp_apply, LinearEquiv.coe_coe, Submodule.mkQ_apply,
        LinearMap.zero_apply, map_zero] using hq

end PolycyclicRecognition.PolynomialMatrixGroup

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_CyclicQuotientDimension
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.cyclicTopHomologyInjection_mono _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Infinite cyclic extensions of groups of finite integral dimension

Finite generation of the kernel's projective resolution is unnecessary for
the dimension bound. Truncate an arbitrary resolution before induction.
-/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory
variable {G : Type} [Group G]

theorem cohomologicalDimension_le_of_infiniteCyclicQuotient
    (N : Subgroup G) [N.Normal] [IsCyclic (G ⧸ N)] [Infinite (G ⧸ N)]
    (d : ℕ) [HasProjectiveDimensionLE (trivialIntegral N) d] :
    HasProjectiveDimensionLE (trivialIntegral G) (d + 1) := by
  let : CommGroup (G ⧸ N) := IsCyclic.commGroup
  obtain ⟨z, hz⟩ := IsCyclic.exists_generator (α := G ⧸ N)
  let P := Rep.standardResolution ℤ N
  let R := finiteProjectiveResolution P d
  let := quotientRegular_projectiveDimension N R d (finiteTruncation_isZero P d)
  exact cohomologicalDimension_bound_of_cyclicQuotientModule
    (G ⧸ N) (QuotientGroup.mk' N) z hz d

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_GroupDimensionTransport
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.cyclicTopHomologyInjection_mono _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integral dimension bounds under embeddings and group isomorphisms -/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory

theorem cohomologicalDimension_le_of_equiv {G J : Type} [Group G] [Group J]
    (e : G ≃* J) (d : ℕ) [HasProjectiveDimensionLE (trivialIntegral G) d] :
    HasProjectiveDimensionLE (trivialIntegral J) d := by
  let P := Rep.standardResolution ℤ G
  let R := finiteProjectiveResolution P d
  let F : Rep ℤ G ⥤ Rep ℤ J := Rep.resFunctor e.symm.toMonoidHom
  let : F.IsEquivalence := (restrictionEquivalence ℤ e.symm).isEquivalence_functor
  apply projectiveDimension_of_boundedResolution (F.mapProjectiveResolution R) d
  intro i hi
  exact F.map_isZero (finiteTruncation_isZero P d i hi)

theorem cohomologicalDimension_le_of_injective {G J : Type} [Group G] [Group J]
    (f : G →* J) (hf : Function.Injective f) (d : ℕ)
    [HasProjectiveDimensionLE (trivialIntegral J) d] :
    HasProjectiveDimensionLE (trivialIntegral G) d := by
  let := subgroup_cohomologicalDimension_le f.range d
  exact cohomologicalDimension_le_of_equiv (MonoidHom.ofInjective hf).symm d

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_CyclicJoinDimension
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.cyclicTopHomologyInjection_mono _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Adjoining a lift of an infinite cyclic quotient

If the lift normalizes a subgroup of the kernel, its join with that subgroup
has precisely the expected kernel. This gives the dimension and solvability
bounds without imposing normality in the whole ambient group.
-/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
open scoped Pointwise
variable {G : Type} [Group G] (q : G →* Multiplicative ℤ)
  (t : G) (ht : q t = Multiplicative.ofAdd 1) (A : Subgroup G)
include ht

theorem cyclicJoinKernelMap_injective (hA : A ≤ q.ker) (hnorm : t ∈ Subgroup.normalizer A) :
    Function.Injective (cyclicJoinKernelMap q t ht A hA hnorm) := by
  intro x y h
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun a : A => (a : G)) h

theorem cyclicJoin_finiteDimension (hA : A ≤ q.ker) (hnorm : t ∈ Subgroup.normalizer A)
    (hcd : HasFiniteIntegralCohomologicalDimension A) :
    HasFiniteIntegralCohomologicalDimension (A ⊔ Subgroup.zpowers t : Subgroup G) := by
  obtain ⟨d, hd⟩ := hcd
  let := hd
  let H := A ⊔ Subgroup.zpowers t
  let p : H →* Multiplicative ℤ := q.comp H.subtype
  let tH : H := ⟨t, (show Subgroup.zpowers t ≤ H from le_sup_right) (Subgroup.mem_zpowers t)⟩
  have htH : p tH = Multiplicative.ofAdd 1 := ht
  let := integerQuotient_isCyclic p tH htH
  let := integerQuotient_infinite p tH htH
  let := cohomologicalDimension_le_of_injective
    (cyclicJoinKernelMap q t ht A hA hnorm)
    (cyclicJoinKernelMap_injective q t ht A hA hnorm) d
  exact ⟨d + 1, cohomologicalDimension_le_of_infiniteCyclicQuotient p.ker d⟩

theorem cyclicJoin_solvable (hA : A ≤ q.ker) (hnorm : t ∈ Subgroup.normalizer A)
    [Group.IsSolvable A] : Group.IsSolvable (A ⊔ Subgroup.zpowers t : Subgroup G) := by
  let H := A ⊔ Subgroup.zpowers t
  let p : H →* Multiplicative ℤ := q.comp H.subtype
  let : Group.IsSolvable p.ker := Group.isSolvable_of_isSolvable_injective
    (cyclicJoinKernelMap_injective q t ht A hA hnorm)
  exact Group.isSolvable_of_ker_le_range p.ker.subtype p
    (by rw [Subgroup.range_subtype])

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_PolynomialMatrixScalarExtension
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.PolynomialMatrixGroup.coordinateLinearAction_apply _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Faithful extension of scalars for concrete matrix groups -/

noncomputable section
namespace PolycyclicRecognition.PolynomialMatrixGroup

variable {K L : Type*} [Field K] [Field L] {n : ℕ}

theorem scalarVector_injective (f : K →+* L) : Function.Injective (scalarVector (n := n) f) := by
  intro v w h
  funext i
  exact f.injective (congrFun h i)

theorem scalarVector_action (f : K →+* L) (g : PolynomialMatrixGroup K n) (v : Fin n → K) :
    scalarVector f (linearAction g v) = linearAction (scalarExtension f g) (scalarVector f v) := by
  ext i
  simp [scalarVector, linearAction_apply, Matrix.mulVec, dotProduct]

end PolycyclicRecognition.PolynomialMatrixGroup

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_VirtuallyUnipotentCommutatorAction
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform commutator-action bounds after passing to finite index

This version retains the action bound even when the original representation
has a kernel, as needed for conjugation on a nilpotent normal subgroup.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped commutatorElement
namespace PolynomialMatrixGroup

variable {G K : Type*} [Group G] [Field K] [IsAlgClosed K] [Group.IsSolvable G]

theorem exists_finiteIndex_commutator_words {n : ℕ} (ι : G →* PolynomialMatrixGroup K n) :
    ∃ H : Subgroup G, H.Normal ∧ H.FiniteIndex ∧
      ∃ c, ∀ w : List (commutator H), w.length = c →
        actionOperatorWord (fun a : commutator H =>
          (linearAction (ι (a : H))).toLinearMap - 1) w = 0 := by
  let : TopologicalSpace G := TopologicalSpace.induced ι inferInstance
  have hι : Topology.IsInducing ι := Topology.IsInducing.induced _
  let : SeparatelyContinuousMul G := hι.separatelyContinuousMul ι
  let : ContinuousInv G := hι.continuousInv (fun g => map_inv ι g)
  let : TopologicalSpace.NoetherianSpace G := hι.noetherianSpace
  let H := separateIdentityComponent G
  let : PreconnectedSpace H :=
    Subtype.preconnectedSpace (separateIdentityComponent_preconnected (G := G))
  let : SeparatelyContinuousMul H :=
    Topology.IsInducing.subtypeVal.separatelyContinuousMul H.subtype
  let : ContinuousInv H := Topology.IsInducing.subtypeVal.continuousInv (fun _ => rfl)
  let j := ι.comp H.subtype
  have hj : Continuous j := hι.continuous.comp continuous_subtype_val
  have hjind : Topology.IsInducing j := hι.comp Topology.IsInducing.subtypeVal
  have hc₁ (g : H) : Continuous (fun h : H => ⁅g, h⁆) := by
    apply hjind.continuous_iff.mpr
    simpa only [Function.comp_def, map_commutatorElement] using
      (continuous_commutator_left (j g)).comp hj
  have hc₂ (h : H) : Continuous (fun g : H => ⁅g, h⁆) := by
    apply hjind.continuous_iff.mpr
    simpa only [Function.comp_def, map_commutatorElement] using
      (continuous_commutator_right (j h)).comp hj
  exact ⟨H, inferInstance, separateIdentityComponent_finiteIndex,
    connected_solvable_commutator_words hc₁ hc₂ j hj⟩

end PolynomialMatrixGroup

theorem exists_finiteIndex_rational_commutator_words
    {G V : Type*} [Group G] [Group.IsSolvable G] [AddCommGroup V] [Module ℚ V]
    [Module.Finite ℚ V] (ρ : G →* (V ≃ₗ[ℚ] V)) :
    ∃ H : Subgroup G, H.Normal ∧ H.FiniteIndex ∧
      ∃ c, ∀ w : List (commutator H), w.length = c →
        actionOperatorWord (fun a : commutator H => (ρ (a : H)).toLinearMap - 1) w = 0 := by
  let e := (Module.finBasis ℚ V).equivFun
  let ι₀ := PolynomialMatrixGroup.coordinateLinearAction ρ e
  let f := algebraMap ℚ (AlgebraicClosure ℚ)
  let ι := (PolynomialMatrixGroup.scalarExtension f).comp ι₀
  obtain ⟨H, hHn, hHi, c, hc⟩ := PolynomialMatrixGroup.exists_finiteIndex_commutator_words ι
  refine ⟨H, hHn, hHi, c, ?_⟩
  let q := (PolynomialMatrixGroup.scalarVector f).comp e.toAddMonoidHom
  have hq : Function.Injective q :=
    (PolynomialMatrixGroup.scalarVector_injective f).comp e.injective
  have hint (a : commutator H) (v : V) :
      q (((ρ (a : H)).toLinearMap - 1) v) =
        ((PolynomialMatrixGroup.linearAction (ι (a : H))).toLinearMap - 1) (q v) := by
    change q (ρ (a : H) v - v) = PolynomialMatrixGroup.linearAction (ι (a : H)) (q v) - q v
    rw [map_sub]
    congr 1
    change PolynomialMatrixGroup.scalarVector f (e (ρ (a : H) v)) = _
    have he : e (ρ (a : H) v) = PolynomialMatrixGroup.linearAction (ι₀ (a : H)) (e v) := by
      simp only [ι₀, PolynomialMatrixGroup.coordinateLinearAction_apply, e.symm_apply_apply]
    rw [he]
    rw [PolynomialMatrixGroup.scalarVector_action]
    rfl
  intro w hw
  apply LinearMap.ext
  intro v
  apply hq
  rw [LinearMap.zero_apply, map_zero]
  have he := actionOperatorWord_intertwines_function
    (fun a : commutator H => (ρ (a : H)).toLinearMap - 1)
    (fun a : commutator H => (PolynomialMatrixGroup.linearAction (ι (a : H))).toLinearMap - 1)
    q hint w v
  rw [hc w hw] at he
  simpa only [LinearMap.zero_apply] using he

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_VirtualNilpotentByAbelian
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite-index nilpotent-by-abelian structure in finite integral dimension

The maximal nilpotent normal subgroup has finite-dimensional rational
central layers. After passing to finite index the derived action on those
layers is uniformly unipotent. The centralizer criterion then puts that
derived subgroup inside the nilpotent normal subgroup itself.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped Pointwise commutatorElement
variable {G : Type} [Group G] [Group.IsSolvable G]

theorem exists_finiteIndex_commutator_le_maximal_nilpotent
    (F : Subgroup G) [F.Normal] [Group.IsNilpotent F]
    (hFcd : HasFiniteIntegralCohomologicalDimension F)
    (hmax : ∀ N : Subgroup G, N.Normal → Group.IsNilpotent N → F ≤ N → N = F) :
    ∃ H : Subgroup G, H.Normal ∧ H.FiniteIndex ∧ (commutator H).map H.subtype ≤ F := by
  let c := Group.nilpotencyClass F
  let := centralLayersSpace_finite F hFcd c
  let ρ := centralLayersAction F c
  obtain ⟨H, hHn, hHi, d, hd⟩ := exists_finiteIndex_rational_commutator_words ρ
  let := hHn
  let D := (commutator H).map H.subtype
  let K := F ⊔ D
  have hmatch (a : K) : ∃ b : commutator H, ρ a = ρ (b : H) := by
    have ha : (a : G) ∈ (F : Set G) * (D : Set G) := by
      rw [← Subgroup.normal_mul]
      exact a.property
    obtain ⟨f, hf, x, hx, he⟩ := ha
    obtain ⟨b, hb, rfl⟩ := hx
    refine ⟨⟨b, hb⟩, ?_⟩
    change ρ (a : G) = ρ (b : G)
    rw [← he, map_mul]
    have hf' : ρ f = 1 := subgroup_le_centralLayersAction_ker F c hf
    rw [hf', one_mul]
    rfl
  have hwords : ∀ w : List K, w.length = d →
      actionOperatorWord (fun g : K => (ρ g).toLinearMap - 1) w = 0 := by
    apply actionOperatorWord_zero_of_matching_generators
      (fun g : K => (ρ g).toLinearMap - 1)
      (fun a : commutator H => (ρ (a : H)).toLinearMap - 1) _ d hd
    intro a
    obtain ⟨b, hb⟩ := hmatch a
    exact ⟨b, by rw [hb]⟩
  have hK : Group.IsNilpotent K := by
    apply nilpotent_of_unipotent_central_layers F hFcd.torsionFree K
      (centralizer_le_maximal_nilpotent_normal F hmax)
    intro i hi
    exact ⟨d, centralLayers_word_projection F c K d hwords ⟨i, hi⟩⟩
  have he : K = F := hmax K inferInstance hK le_sup_left
  exact ⟨H, hHn, hHi, (show D ≤ K from le_sup_right).trans_eq he⟩

theorem exists_nilpotent_normal_finiteIndex_commutator
    (hG : HasFiniteIntegralCohomologicalDimension G) :
    ∃ F : Subgroup G, F.Normal ∧ Group.IsNilpotent F ∧
      ∃ H : Subgroup G, H.Normal ∧ H.FiniteIndex ∧ (commutator H).map H.subtype ≤ F := by
  obtain ⟨F, hFn, hF, hmax⟩ := exists_maximal_nilpotent_normal_subgroup hG
  let := hFn
  let := hF
  exact ⟨F, hFn, hF,
    exists_finiteIndex_commutator_le_maximal_nilpotent F (hG.subgroup F) hmax⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_NilpotentByAbelianReduction
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

namespace OAI

/-! # The concrete nilpotent-by-abelian subgroup for the duality endgame -/

noncomputable section
namespace PolycyclicRecognition

theorem nilpotent_of_injective_hom {A B : Type*} [Group A] [Group B] [Group.IsNilpotent B]
    (f : A →* B) (hf : Function.Injective f) : Group.IsNilpotent A := by
  let e := MonoidHom.ofInjective hf
  exact Group.nilpotent_of_mulEquiv e.symm

theorem exists_finiteIndex_nilpotent_by_abelian
    {G : Type} [Group G] [Group.IsSolvable G]
    (hG : HasFiniteIntegralCohomologicalDimension G) :
    ∃ H : Subgroup G, H.Normal ∧ H.FiniteIndex ∧
      ∃ N : Subgroup H, ∃ _ : N.Normal, Group.IsNilpotent N ∧ IsMulCommutative (H ⧸ N) := by
  obtain ⟨F, hFn, hF, H, hHn, hHi, hcomm⟩ :=
    exists_nilpotent_normal_finiteIndex_commutator hG
  let := hFn
  let := hF
  let N := F.comap H.subtype
  let f : N →* F := (H.subtype.comp N.subtype).codRestrict F (fun a => a.property)
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun x : F => (x : G)) hab
  have hN : Group.IsNilpotent N := nilpotent_of_injective_hom f hf
  have hc : commutator H ≤ N := by
    intro a ha
    exact hcomm ⟨a, ha, rfl⟩
  exact ⟨H, hHn, hHi, N, inferInstance, hN,
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr hc⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_VirtualSolvableDimension
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.cyclicTopHomologyInjection_mono _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalizedGroupIdentityClass_comparison _root_.OAI.PolycyclicRecognition.rationalCoefficientInclusion_apply _root_.OAI.PolycyclicRecognition.resolutionStableSyzygyTransition_class _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite-index solvable dimension bounds along cyclic extensions -/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
variable {G J : Type} [Group G] [Group J]

theorem solvable_finiteDimension_of_equiv (e : G ≃* J)
    [Group.IsSolvable G] (hG : HasFiniteIntegralCohomologicalDimension G) :
    Group.IsSolvable J ∧ HasFiniteIntegralCohomologicalDimension J := by
  obtain ⟨d, hd⟩ := hG
  let := hd
  exact ⟨Group.isSolvable_of_isSolvable_injective (f := e.symm.toMonoidHom) e.symm.injective,
    d, cohomologicalDimension_le_of_equiv e d⟩

theorem exists_solvable_finiteDimension_of_equiv (e : G ≃* J)
    (hG : ∃ V : Subgroup G, V.FiniteIndex ∧ Group.IsSolvable V ∧
      HasFiniteIntegralCohomologicalDimension V) :
    ∃ W : Subgroup J, W.FiniteIndex ∧ Group.IsSolvable W ∧
      HasFiniteIntegralCohomologicalDimension W := by
  obtain ⟨V, hVindex, hVsolv, hVdim⟩ := hG
  let := hVindex
  let := hVsolv
  have hW := solvable_finiteDimension_of_equiv
    (V.equivMapOfInjective e.toMonoidHom e.injective) hVdim
  exact ⟨V.map e.toMonoidHom, Subgroup.FiniteIndex.map_of_surjective V e.surjective,
    hW.1, hW.2⟩

theorem exists_solvable_finiteDimension_of_finiteIndex (H : Subgroup G) [H.FiniteIndex]
    (hH : ∃ V : Subgroup H, V.FiniteIndex ∧ Group.IsSolvable V ∧
      HasFiniteIntegralCohomologicalDimension V) :
    ∃ W : Subgroup G, W.FiniteIndex ∧ Group.IsSolvable W ∧
      HasFiniteIntegralCohomologicalDimension W := by
  obtain ⟨V, hVindex, hVsolv, hVdim⟩ := hH
  let := hVindex
  let := hVsolv
  have hW := solvable_finiteDimension_of_equiv
    (V.equivMapOfInjective H.subtype H.subtype_injective) hVdim
  refine ⟨V.map H.subtype, ⟨?_⟩, hW.1, hW.2⟩
  rw [Subgroup.index_map_subtype]
  exact mul_ne_zero hVindex.index_ne_zero (Subgroup.FiniteIndex.index_ne_zero (H := H))

theorem exists_solvable_finiteDimension_of_cyclic_extension
    (N : Subgroup G) [N.Normal] [Group.FG N] [IsCyclic (G ⧸ N)]
    (hN : ∃ U : Subgroup N, U.FiniteIndex ∧ Group.IsSolvable U ∧
      HasFiniteIntegralCohomologicalDimension U) :
    ∃ V : Subgroup G, V.FiniteIndex ∧ Group.IsSolvable V ∧
      HasFiniteIntegralCohomologicalDimension V := by
  obtain ⟨U, hUindex, hUsolv, d, hUdim⟩ := hN
  let := hUindex
  let := hUsolv
  let := hUdim
  obtain ⟨K, hKU, hKchar, hKindex⟩ := exists_characteristic_finiteIndex_le U
  let := hKchar
  let := hKindex
  let : Group.IsSolvable K := Group.isSolvable_of_isSolvable_injective
    (Subgroup.inclusion_injective hKU)
  have hKdim : HasFiniteIntegralCohomologicalDimension K :=
    ⟨d, cohomologicalDimension_le_of_injective (Subgroup.inclusion hKU)
      (Subgroup.inclusion_injective hKU) d⟩
  let A : Subgroup G := K.map N.subtype
  have hA := solvable_finiteDimension_of_equiv
    (K.equivMapOfInjective N.subtype N.subtype_injective) hKdim
  let := hA.1
  cases finite_or_infinite (G ⧸ N) with
  | inl hfinite =>
    let := hfinite
    let : N.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
    refine ⟨A, ⟨?_⟩, hA.1, hA.2⟩
    change (K.map N.subtype).index ≠ 0
    rw [Subgroup.index_map_subtype]
    exact mul_ne_zero hKindex.index_ne_zero (Subgroup.FiniteIndex.index_ne_zero (H := N))
  | inr hinfinite =>
    let := hinfinite
    let e : G ⧸ N ≃* Multiplicative ℤ := intCyclicMulEquiv.symm
    let q : G →* Multiplicative ℤ := e.toMonoidHom.comp (QuotientGroup.mk' N)
    have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective N)
    obtain ⟨t, ht⟩ := hq (Multiplicative.ofAdd 1)
    have hAq : A ≤ q.ker := by
      rintro _ ⟨a, _, rfl⟩
      change e (QuotientGroup.mk' N a) = 1
      have ha : (QuotientGroup.mk' N) a = 1 :=
        (QuotientGroup.eq_one_iff (a : G)).mpr a.property
      exact (congrArg e ha).trans e.map_one
    have hnorm : t ∈ Subgroup.normalizer A := Subgroup.mem_normalizer_iff.mpr
      (fun _ => ⟨fun h => Subgroup.Normal.conj_mem inferInstance _ h t,
        fun h => by simpa [mul_assoc] using
          Subgroup.Normal.conj_mem (inferInstance : A.Normal) _ h t⁻¹⟩)
    let V : Subgroup G := A ⊔ Subgroup.zpowers t
    have hVindex : V.FiniteIndex := finiteIndex_of_kernel_cover N K V le_sup_left (by
      intro g
      refine ⟨t ^ (q g).toAdd, (show Subgroup.zpowers t ≤ V from le_sup_right)
        (Subgroup.zpow_mem_zpowers t _), ?_⟩
      apply e.injective
      change q (t ^ (q g).toAdd) = q g
      apply Multiplicative.toAdd.injective
      simp [map_zpow, ht])
    exact ⟨V, hVindex, cyclicJoin_solvable q t ht A hAq hnorm,
      cyclicJoin_finiteDimension q t ht A hAq hnorm hA.2⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_PolycyclicExtensionDimension
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Passing finite virtual dimension through a polycyclic quotient -/

noncomputable section
namespace PolycyclicRecognition
open ChromaticCyclic
variable {G : Type} [Group G]

theorem exists_solvable_finiteDimension_of_cyclicSeries
    {H K : Subgroup G} {n : ℕ} (c : CyclicSeries H K n) (hfg : Group.FG H)
    (hH : ∃ V : Subgroup H, V.FiniteIndex ∧ Group.IsSolvable V ∧
      HasFiniteIntegralCohomologicalDimension V) :
    ∃ V : Subgroup K, V.FiniteIndex ∧ Group.IsSolvable V ∧
      HasFiniteIntegralCohomologicalDimension V := by
  have hm : ∀ i, i ≤ n → Group.FG (c.group i) ∧
      ∃ V : Subgroup (c.group i), V.FiniteIndex ∧ Group.IsSolvable V ∧
        HasFiniteIntegralCohomologicalDimension V := by
    intro i
    induction i with
    | zero =>
      intro _
      rw [c.first]
      exact ⟨hfg, hH⟩
    | succ i ih =>
      intro hi
      obtain ⟨hfg, hprev⟩ := ih (by omega)
      let s := c.step i (by omega)
      let := s.normal
      let := s.cyclic
      let e := (Subgroup.subgroupOfEquivOfLe s.le).symm
      let : Group.FG ((c.group i).subgroupOf (c.group (i + 1))) :=
        @Group.fg_of_surjective _ _ _ _ hfg e.toMonoidHom e.surjective
      exact ⟨finitelyGenerated_of_cyclicStep s hfg,
        exists_solvable_finiteDimension_of_cyclic_extension
          ((c.group i).subgroupOf (c.group (i + 1)))
          (exists_solvable_finiteDimension_of_equiv e hprev)⟩
  have htop := (hm n le_rfl).2
  rwa [c.last] at htop

theorem exists_solvable_finiteDimension_of_virtuallyPolycyclic_quotient
    (N : Subgroup G) [N.Normal] [Group.FG N]
    (hN : ∃ V : Subgroup N, V.FiniteIndex ∧ Group.IsSolvable V ∧
      HasFiniteIntegralCohomologicalDimension V)
    (hQ : IsVirtuallyPolycyclic (G ⧸ N)) :
    ∃ V : Subgroup G, V.FiniteIndex ∧ Group.IsSolvable V ∧
      HasFiniteIntegralCohomologicalDimension V := by
  obtain ⟨P, hPindex, n, ⟨c⟩⟩ := hQ
  let := hPindex
  let q := QuotientGroup.mk' N
  let H := P.comap q
  have cQ := c.map P.subtype
  rw [Subgroup.map_bot, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at cQ
  have cG := cQ.comap q
  rw [MonoidHom.comap_bot, QuotientGroup.ker_mk'] at cG
  exact exists_solvable_finiteDimension_of_finiteIndex H
    (exists_solvable_finiteDimension_of_cyclicSeries cG inferInstance hN)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Lattices_UniformLatticeQuotient
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Compact quotient and compact fundamental cover

The concrete uniform lattice definition agrees with the usual compact-coset-
quotient definition. Left and right cosets are interchanged by inversion.
-/

noncomputable section

namespace PolycyclicRecognition

open Set
open scoped Topology

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The compact fundamental cover gives compactness of the ordinary right
coset quotient, without any normality assumption. -/
theorem IsUniformLattice.compactSpace_quotient {Λ : Subgroup G}
    (hΛ : IsUniformLattice Λ) : CompactSpace (G ⧸ Λ) := by
  obtain ⟨K, hK, hcover⟩ := hΛ.2
  let q : G → G ⧸ Λ := QuotientGroup.mk
  have hsurj : (fun k => q k⁻¹) '' K = univ := by
    apply eq_univ_of_forall
    intro y
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨γ, k, hk, heq⟩ := hcover a⁻¹
    refine ⟨k, hk, ?_⟩
    apply QuotientGroup.eq.mpr
    simp only [inv_inv]
    have hka : k * a = (γ : G)⁻¹ := by
      calc
        k * a = (γ : G)⁻¹ * ((γ : G) * k) * a := by group
        _ = (γ : G)⁻¹ := by rw [heq]; group
    rw [hka]
    exact Λ.inv_mem γ.property
  apply isCompact_univ_iff.mp
  rw [← hsurj]
  exact hK.image (QuotientGroup.continuous_mk.comp continuous_inv)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Lattices_LatticeRealizationFiniteIndex
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite-index transport and integral-quotient realization -/

noncomputable section
namespace PolycyclicRecognition
variable {G : Type} [Group G]

theorem uniform_lattice_realization_of_finiteIndex (H : Subgroup G) [H.FiniteIndex]
    (hH : ∃ K : Subgroup H, K.FiniteIndex ∧ ∃ (S : SimplyConnectedSolvableLieModel)
      (Λ : Subgroup S.carrier), IsUniformLattice Λ ∧ Nonempty (K ≃* Λ)) :
    ∃ K : Subgroup G, K.FiniteIndex ∧ ∃ (S : SimplyConnectedSolvableLieModel)
      (Λ : Subgroup S.carrier), IsUniformLattice Λ ∧ Nonempty (K ≃* Λ) := by
  obtain ⟨K, hK, S, Λ, hΛ, ⟨e⟩⟩ := hH
  have hi : (K.map H.subtype).FiniteIndex := ⟨by
    rw [Subgroup.index_map_subtype]
    exact mul_ne_zero hK.index_ne_zero (Subgroup.FiniteIndex.index_ne_zero (H := H))⟩
  let eK := K.equivMapOfInjective H.subtype H.subtype_injective
  exact ⟨K.map H.subtype, hi, S, Λ, hΛ, ⟨eK.symm.trans e⟩⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Lattices_PolycyclicLatticeRealization
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The lattice-realization consequence of Dekimpe's theorem

All extensions used here are actual group extensions.  The nilshadow
construction supplies the connected Lie model without a splitting premise.
-/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold

theorem IsPolycyclic.exists_solvable_finiteDimension {G : Type} [Group G]
    (hG : IsPolycyclic G) :
    ∃ H : Subgroup G, H.FiniteIndex ∧ Group.IsSolvable H ∧
      HasFiniteIntegralCohomologicalDimension H := by
  let B : Subgroup G := ⊥
  let : Group.FG B := finitelyGenerated_of_isCyclic
  have hB : ∃ V : Subgroup B, V.FiniteIndex ∧ Group.IsSolvable V ∧
      HasFiniteIntegralCohomologicalDimension V := by
    let V : Subgroup B := ⊤
    let : Group.IsSolvable V := Group.isSolvable_of_comm (fun _ _ => Subsingleton.elim _ _)
    exact ⟨V, inferInstance, inferInstance,
      (poincareDuality_zero_of_subsingleton V).finiteCohomologicalDimension V⟩
  exact exists_solvable_finiteDimension_of_virtuallyPolycyclic_quotient B hB
    (hG.of_surjective (QuotientGroup.mk' B) (QuotientGroup.mk'_surjective B)).isVirtuallyPolycyclic

theorem virtuallyPolycyclic_uniform_lattice {G : Type} [Group G]
    (hG : IsVirtuallyPolycyclic G) :
    ∃ K : Subgroup G, K.FiniteIndex ∧ ∃ (S : SimplyConnectedSolvableLieModel)
      (Λ : Subgroup S.carrier), IsUniformLattice Λ ∧ Nonempty (K ≃* Λ) := by
  obtain ⟨P, hPi, hP⟩ := hG
  let := hPi
  apply uniform_lattice_realization_of_finiteIndex P
  obtain ⟨H, hHi, hHs, hHcd⟩ := hP.exists_solvable_finiteDimension
  let := hHi
  let := hHs
  apply uniform_lattice_realization_of_finiteIndex H
  obtain ⟨V, hVn, hVi, N, hNn, hNnil, hQ⟩ :=
    exists_finiteIndex_nilpotent_by_abelian hHcd
  let := hVi
  let := hNn
  let := hNnil
  let := hQ
  apply uniform_lattice_realization_of_finiteIndex V
  have hVpoly : IsPolycyclic V :=
    (hP.of_injective H.subtype Subtype.val_injective).of_injective V.subtype Subtype.val_injective
  exact nilpotent_by_abelian_uniform_lattice hVpoly (hHcd.subgroup V).torsionFree N

/-- Dekimpe's lattice-realization conclusion follows from nilpotent completion
and the invariant graph construction. -/
theorem dekimpeLatticeRealizationInput_oai : DekimpeLatticeRealizationInput := by
  intro G _ hG
  obtain ⟨K, hK, S, Λ, hΛ, e⟩ := virtuallyPolycyclic_uniform_lattice hG
  let : IsTopologicalGroup S.carrier := topologicalGroup_of_lieGroup (𝓘(ℝ, S.modelSpace)) ⊤
  exact ⟨K, hK, S, Λ, hΛ.1, hΛ.compactSpace_quotient, e⟩

end PolycyclicRecognition

end

end OAI
end

theorem solution : type_of% @OAI.PolycyclicRecognition.dekimpeLatticeRealizationInput_oai := @OAI.PolycyclicRecognition.dekimpeLatticeRealizationInput_oai
