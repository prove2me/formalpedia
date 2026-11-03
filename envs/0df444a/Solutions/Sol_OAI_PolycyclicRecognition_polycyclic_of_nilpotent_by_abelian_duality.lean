-- Prove2me | solution 1 for OAI.PolycyclicRecognition.polycyclic_of_nilpotent_by_abelian_duality
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-03T00:00:27.311202+00:00
-- url     : https://prove2.me/submissions/b5959ebb-1a83-4222-a0f4-c2483b6a1386

import Mathlib
import Definitions.Def_PolycyclicRecognition
import Definitions.Def_OAIQ093D017

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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_NormalInductionDimension
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
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
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.latticeNormalFlag_normal _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
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

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_AbelianSubgroupRank
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.latticeNormalFlag_normal _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
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

end PolycyclicRecognition

end

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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_RankOneRepresentation
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Nonzero maps determine rank-one integral representations -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2100] Linear.homModule

theorem integralEnd_comp_comm (f g : ℤ →ₗ[ℤ] ℤ) : f ∘ₗ g = g ∘ₗ f := by
  apply LinearMap.ext_ring
  change f (g 1) = g (f 1)
  calc
    f (g 1) = g 1 * f 1 := integralEnd_apply f _
    _ = f 1 * g 1 := mul_comm _ _
    _ = g (f 1) := (integralEnd_apply g _).symm

theorem rankOne_end_comp_comm {V : Type*} [AddCommGroup V] [Module ℤ V]
    (e : V ≃ₗ[ℤ] ℤ) (f g : V →ₗ[ℤ] V) : f ∘ₗ g = g ∘ₗ f := by
  apply e.conj.injective
  rw [LinearEquiv.conj_comp, LinearEquiv.conj_comp]
  exact integralEnd_comp_comm _ _

theorem rankOne_linear_injective {V W : Type*} [AddCommGroup V] [Module ℤ V]
    [AddCommGroup W] [Module ℤ W] (eV : V ≃ₗ[ℤ] ℤ) (eW : W ≃ₗ[ℤ] ℤ)
    (f : V →ₗ[ℤ] W) (hf : f ≠ 0) : Function.Injective f := by
  let F := eW.toLinearMap ∘ₗ f ∘ₗ eV.symm.toLinearMap
  have hF : F 1 ≠ 0 := by
    intro h
    apply hf
    ext x
    apply eW.injective
    have hx := integralEnd_apply F (eV x)
    simpa [F, h] using hx
  intro x y hxy
  apply eV.injective
  apply mul_right_cancel₀ hF
  rw [← integralEnd_apply F, ← integralEnd_apply F]
  simpa only [F, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply] using congrArg eW hxy

theorem rankOne_rep_iso_of_nonzero {G : Type} [Group G] (D E : Rep ℤ G)
    (eD : D.V ≃ₗ[ℤ] ℤ) (eE : E.V ≃ₗ[ℤ] ℤ)
    (f : D ⟶ E) (hf : f ≠ 0) : Nonempty (D ≅ E) := by
  let e := eD.trans eE.symm
  let a := e.symm.toLinearMap ∘ₗ f.hom.toLinearMap
  have hf' : f.hom.toLinearMap ≠ 0 := by
    intro h
    apply hf
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    exact h
  have ha : Function.Injective a := e.symm.injective.comp
    (rankOne_linear_injective eD eE f.hom.toLinearMap hf')
  refine ⟨Rep.mkIso (Representation.Equiv.mk e ?_)⟩
  intro g
  ext x
  apply e.symm.injective
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  change D.ρ g x = (e.symm.toLinearMap ∘ₗ E.ρ g ∘ₗ e.toLinearMap) x
  apply ha
  let b := e.symm.toLinearMap ∘ₗ E.ρ g ∘ₗ e.toLinearMap
  have hb := rankOne_end_comp_comm eD b a
  have hc : a ∘ₗ D.ρ g = b ∘ₗ a := by
    ext y
    change e.symm (f.hom (D.ρ g y)) = e.symm (E.ρ g (e (e.symm (f.hom y))))
    rw [LinearEquiv.apply_symm_apply]
    exact congrArg e.symm (Rep.hom_comm_apply f g y)
  exact congrArg (fun u : D.V →ₗ[ℤ] D.V => u x) (hc.trans hb)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_RankOneCharacter
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The scalar character of a rank-one integral representation -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2100] Linear.homModule
variable {G : Type} [Group G]

theorem rankOneCharacter_eq_of_iso (D E : Rep ℤ G)
    (eD : D.V ≃ₗ[ℤ] ℤ) (eE : E.V ≃ₗ[ℤ] ℤ) (i : D ≅ E) :
    rankOneCharacter D eD = rankOneCharacter E eE := by
  let b := eD.symm.trans ((Representation.equivOfIso i).toLinearEquiv.trans eE)
  have hb : b 1 ≠ 0 := by
    intro h
    have he : b 1 = b 0 := by rw [map_zero]; exact h
    exact one_ne_zero (b.injective he)
  ext g
  apply mul_right_cancel₀ hb
  rw [← show b ((rankOneCharacter D eD) g) = (rankOneCharacter D eD) g * b 1 from
    integralEnd_apply b.toLinearMap ((rankOneCharacter D eD) g)]
  change eE (i.hom.hom (eD.symm (eD (D.ρ g (eD.symm 1))))) =
    eE (E.ρ g (eE.symm 1)) * eE (i.hom.hom (eD.symm 1))
  rw [LinearEquiv.symm_apply_apply, Rep.hom_comm_apply, rankOne_action_coordinate]
  exact mul_comm _ _

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_ExhaustiveCharacter
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Gluing compatible integral characters over an exhaustive subgroup chain -/

noncomputable section
namespace PolycyclicRecognition

attribute [local instance] Classical.propDecidable

variable {G : Type} [Group G] (S : ℕ → Subgroup G)
  (hS : Monotone S) (hcover : ∀ g, ∃ n, g ∈ S n) (χ : ∀ n, S n →* ℤ)
  (hχ : ∀ i j (hij : i ≤ j) (g : S i), χ j (Subgroup.inclusion (hS hij) g) = χ i g)

theorem exhaustiveCharacter_restrict (n : ℕ) :
    (exhaustiveCharacter S hS hcover χ hχ).comp (S n).subtype = χ n := by
  ext g
  exact exhaustiveCharacterValue_eq S hS hcover χ hχ g n g.property

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_DimensionFromRegularCohomology
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.cyclicTopHomologyInjection_mono _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalizedGroupIdentityClass_comparison _root_.OAI.PolycyclicRecognition.rationalCoefficientInclusion_apply _root_.OAI.PolycyclicRecognition.resolutionStableSyzygyTransition_class _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The regular module detects finite cohomological dimension

For a finite resolution, vanishing with regular coefficients implies the
same vanishing with free coefficients. Free covers and dimension shifting
then give vanishing with every coefficient module.
-/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits HomologicalComplex
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2100] Linear.homModule

variable {G : Type} [Group G]

theorem cohomology_vanishes_above_regular_bound
    (hG : HasFiniteProjectiveResolution G) (n : ℕ)
    (hreg : ∀ i, n < i → IsZero (groupCohomology (Rep.leftRegular ℤ G) i)) :
    ∀ i, n < i → ∀ A : Rep ℤ G, IsZero (groupCohomology A i) := by
  obtain ⟨P, d, hfin, hbound⟩ := hG
  let := projectiveDimension_of_boundedResolution P d hbound
  have hfree (i : ℕ) (hi : n < i) (A : Rep ℤ G) :
      IsZero (groupCohomology (Rep.free ℤ G A) i) := by
    exact IsZero.of_iso ((moduleFinsuppFunctor ℤ A).map_isZero (hreg i hi))
      (finsuppCohomologyIso ℤ G A P hfin (Rep.leftRegular ℤ G) i)
  have hshift : ∀ k i, n < i → d < i + k →
      ∀ A : Rep ℤ G, IsZero (groupCohomology A i) := by
    intro k
    induction k with
    | zero =>
      intro i _ hi A
      exact groupCohomology_isZero_above_dimension d A i (by omega)
    | succ k ih =>
      intro i hi hdi A
      let f := regularFreeCover A
      let S := ShortComplex.mk (kernel.ι f) f (kernel.condition f)
      have hS : S.ShortExact := { exact := ShortComplex.exact_kernel f }
      have hz : IsZero (groupCohomology S.X₁ (i + 1)) := ih (i + 1) (by omega) (by omega) _
      let := groupCohomology.mono_δ_of_isZero hS i (hfree i hi A)
      exact IsZero.of_mono (groupCohomology.δ hS i (i + 1) rfl) hz
  intro i hi A
  exact hshift (d + 1) i hi (by omega) A

theorem projectiveDimension_of_regular_cohomology_bound
    (hG : HasFiniteProjectiveResolution G) (n : ℕ)
    (hreg : ∀ i, n < i → IsZero (groupCohomology (Rep.leftRegular ℤ G) i)) :
    HasProjectiveDimensionLE (trivialIntegral G) n := by
  have hAll := cohomology_vanishes_above_regular_bound hG n hreg
  obtain ⟨P, _, _, _⟩ := hG
  let := HasExt.standard (Rep ℤ G)
  refine HasProjectiveDimensionLT.mk ?_
  intro i hi A e
  cases i with
  | zero => omega
  | succ j =>
    obtain ⟨f, hf, rfl⟩ := P.extMk_surjective e (j + 2) rfl
    have hz := hAll (j + 1) (by omega) A
    let C := P.complex.linearYonedaObj ℤ A
    have hC : C.ExactAt (j + 1) :=
      (C.exactAt_iff_isZero_homology (j + 1)).mpr
        (IsZero.of_iso hz (groupCohomologyIso A (j + 1) P).symm)
    have hS : (C.sc' j (j + 1) (j + 2)).Exact :=
      (C.exactAt_iff' j (j + 1) (j + 2) (by simp) (by simp)).mp hC
    have hf' : (C.sc' j (j + 1) (j + 2)).g f = 0 := hf
    obtain ⟨g, hg⟩ := (ShortComplex.moduleCat_exact_iff _).mp hS f hf'
    exact (P.extMk_eq_zero_iff f (j + 2) rfl hf j rfl).mpr ⟨g, hg⟩

theorem IsIntegralPoincareDualityGroup.cohomologicalDimension {n : ℕ}
    (hG : IsIntegralPoincareDualityGroup G n) :
    HasProjectiveDimensionLE (trivialIntegral G) n :=
  projectiveDimension_of_regular_cohomology_bound hG.1 n
    (fun i hi => hG.2.1 i (by omega))

theorem IsIntegralPoincareDualityGroup.dimension_unique {m n : ℕ}
    (hm : IsIntegralPoincareDualityGroup G m) (hn : IsIntegralPoincareDualityGroup G n) :
    m = n := by
  apply Nat.le_antisymm
  · let := hn.cohomologicalDimension
    exact hm.dimension_le
  · let := hm.cohomologicalDimension
    exact hn.dimension_le

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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_FiniteIndexFiniteness
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integral FP finiteness is invariant under finite index

The reverse direction uses the proved coarse filling theorem. The necessary
finite-generation hypotheses are derived from FP one and coset representatives.
-/

noncomputable section
namespace PolycyclicRecognition

variable {G : Type} [Group G] (H : Subgroup G) [H.FiniteIndex]

theorem IsIntegralPoincareDualityGroup.finiteIndex_subgroup {n : ℕ}
    (hG : IsIntegralPoincareDualityGroup G n) : IsIntegralPoincareDualityGroup H n := by
  let : Group.FG G := hG.1.fg
  let : Group.FG H := inferInstance
  exact liDualityInput G H (finiteIndexCoarseEquivalence H).symm
    (hG.finiteCohomologicalDimension G) ((hG.finiteCohomologicalDimension G).subgroup H)
    n hG

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

theorem torsionFree_finiteIndex_of_cyclic_extension
    (N : Subgroup G) [N.Normal] [Group.FG N] [IsCyclic (G ⧸ N)]
    (hN : ∃ L : Subgroup N, L.FiniteIndex ∧ HasNoNontrivialTorsion L) :
    ∃ H : Subgroup G, H.FiniteIndex ∧ HasNoNontrivialTorsion H := by
  obtain ⟨L, hLi, hLt⟩ := hN
  let := hLi
  obtain ⟨K, hKL, hKc, hKi⟩ := exists_characteristic_finiteIndex_le L
  let := hKc
  let := hKi
  have hKt : HasNoNontrivialTorsion K := hLt.of_injective (Subgroup.inclusion hKL)
    (Subgroup.inclusion_injective hKL)
  let A : Subgroup G := K.map N.subtype
  have hAt : HasNoNontrivialTorsion A := by
    let e := K.equivMapOfInjective N.subtype N.subtype_injective
    exact hKt.of_injective e.symm.toMonoidHom e.symm.injective
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
    exact ⟨A, hAi, hAt⟩
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
    refine ⟨H, hHi, ?_⟩
    intro x n hn hxn
    have hxf : (x : G) ^ n = 1 := congrArg Subtype.val hxn
    have hx : (x : G) ∈ (A : Set G) * (Subgroup.zpowers g : Set G) := by
      rw [← Subgroup.normal_mul]
      exact x.property
    obtain ⟨a, ha, b, hb, hab⟩ := hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    have haq : q a = 1 := hAq ha
    have hxq : q (x : G) = z ^ k := by
      rw [← hab, map_mul, haq, one_mul, map_zpow, hg]
    have hkn : k * (n : ℤ) = 0 := by
      apply hzinj
      change z ^ (k * (n : ℤ)) = z ^ (0 : ℤ)
      rw [zpow_zero, zpow_mul, zpow_natCast, ← hxq, ← map_pow, hxf, map_one]
    have hk : k = 0 := (mul_eq_zero.mp hkn).resolve_right (by exact_mod_cast hn)
    have hxa : (x : G) ∈ A := by
      have he : (x : G) = a := by simpa [hk] using hab.symm
      rwa [he]
    apply Subtype.ext
    exact congrArg (fun t : A => (t : G)) (hAt ⟨x, hxa⟩ n hn (Subtype.ext hxf))

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

theorem IsPolyZ.isPolycyclic (h : IsPolyZ G) : IsPolycyclic G := by
  obtain ⟨n, c, _⟩ := h
  exact ⟨n, ⟨c⟩⟩

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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_PolyZNormalExtension
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Extensions of groups with torsion-free cyclic series -/

noncomputable section
namespace PolycyclicRecognition

open ChromaticCyclic
variable {G : Type} [Group G]

theorem TorsionFreeCyclicFactors.join {H K L : Subgroup G} {n m : ℕ}
    {c : CyclicSeries H K n} {d : CyclicSeries K L m}
    (hc : TorsionFreeCyclicFactors c) (hd : TorsionFreeCyclicFactors d) :
    TorsionFreeCyclicFactors (cyclicSeriesJoin c d) := by
  intro i hi
  by_cases hn : i < n
  · apply (cyclicStep_torsionFree_congr ((cyclicSeriesJoin c d).step i hi)
      (c.step i hn) ?_ ?_).mpr (hc i hn)
    · simp only [cyclicSeriesJoin, ite_true, if_true, show i ≤ n by omega]
    · simp only [cyclicSeriesJoin, ite_true, if_true, show i + 1 ≤ n by omega]
  · by_cases he : i = n
    · subst i
      apply (cyclicStep_torsionFree_congr ((cyclicSeriesJoin c d).step n hi)
        (d.step 0 (by omega)) ?_ ?_).mpr (hd 0 (by omega))
      · simp only [cyclicSeriesJoin, ite_true, if_true, le_refl, c.last, d.first]
      · simp only [cyclicSeriesJoin, ite_false, if_false, show ¬ n + 1 ≤ n by omega,
          Nat.add_sub_cancel_left]
    · apply (cyclicStep_torsionFree_congr ((cyclicSeriesJoin c d).step i hi)
        (d.step (i - n) (by omega)) ?_ ?_).mpr (hd (i - n) (by omega))
      · simp only [cyclicSeriesJoin, ite_false, if_false, show ¬ i ≤ n by omega]
      · simp only [cyclicSeriesJoin, ite_false, if_false, show ¬ i + 1 ≤ n by omega,
          show i + 1 - n = (i - n) + 1 by omega]

theorem isPolyZ_of_normal_subgroup (N : Subgroup G) [N.Normal]
    (hN : IsPolyZ N) (hQ : IsPolyZ (G ⧸ N)) : IsPolyZ G := by
  obtain ⟨n, c, hc⟩ := hN
  obtain ⟨m, d, hd⟩ := hQ
  let cG := c.map N.subtype
  let cG' : CyclicSeries (⊥ : Subgroup G) N n :=
    { cG with
      first := by simpa only [Subgroup.map_bot] using cG.first
      last := by simpa only [← MonoidHom.range_eq_map, N.range_subtype] using cG.last }
  let dG := d.comap (QuotientGroup.mk' N)
  let dG' : CyclicSeries N ⊤ m :=
    { dG with
      first := by simpa only [MonoidHom.comap_bot, QuotientGroup.ker_mk'] using dG.first
      last := by simpa only [Subgroup.comap_top] using dG.last }
  have hcG : TorsionFreeCyclicFactors cG' := hc.map N.subtype N.subtype_injective
  have hdG : TorsionFreeCyclicFactors dG' := hd.comap (QuotientGroup.mk' N)
  exact ⟨n + m, cyclicSeriesJoin cG' dG', hcG.join hdG⟩

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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_TorsionFreeAbelianRank
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.latticeNormalFlag_normal _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

namespace OAI

/-! # Uniform rank bounds on finitely generated abelian subgroups

A torsion-free finitely generated abelian group is an integral lattice. The
explicit lattice duality calculation therefore bounds the rank of every such
subgroup by a common ambient cohomological-dimension bound.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped IsMulCommutative

variable {A : Type} [CommGroup A]

theorem exists_integralLattice_equiv [Group.FG A] (hA : HasNoNontrivialTorsion A) :
    ∃ n, Nonempty (IntegralLatticeGroup n ≃* A) := by
  let : IsMulTorsionFree A := isMulTorsionFree_iff_not_isOfFinOrder.mpr (by
    intro a ha hf
    exact ha (hA a (orderOf a) (ne_of_gt hf.orderOf_pos) (pow_orderOf_eq_one a)))
  let : IsAddTorsionFree (Additive A) := inferInstance
  let : Module.IsTorsionFree ℤ (Additive A) := inferInstance
  have hM : Module.Finite ℤ (Additive A) := by
    obtain ⟨s, hs, hfin⟩ := AddGroup.fg_iff.mp (inferInstance : AddGroup.FG (Additive A))
    apply Module.Finite.of_fg_top
    refine Submodule.fg_def.mpr ⟨s, hfin, ?_⟩
    apply AddSubgroup.toIntSubmodule.symm.injective
    simpa only [AddSubgroup.toIntSubmodule_symm, Submodule.span_int_eq_addSubgroupClosure, Submodule.top_toAddSubgroup] using hs
  let := hM
  obtain ⟨n, b⟩ := Module.basisOfFiniteTypeTorsionFree' (R := ℤ) (M := Additive A)
  exact ⟨n, ⟨integralLatticeEquivOfBasis b⟩⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_PolycyclicTorsionFree
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finite_templateSymmetryGroup _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteSubtypeLinearEquivRealIdMemSubgroupLinearSupportSymmetryGroup _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Torsion-free finite-index subgroups of polycyclic groups

This proves the torsion-free consequence of Robinson, *A Course in the
Theory of Groups*, second edition, Theorem 5.4.15(i), needed by the duality
comparison. The proof is induction along the actual cyclic subnormal series.
-/

noncomputable section
namespace PolycyclicRecognition

open ChromaticCyclic

variable {G J : Type} [Group G] [Group J]

theorem torsionFree_finiteIndex_of_equiv (e : G ≃* J)
    (h : ∃ H : Subgroup G, H.FiniteIndex ∧ HasNoNontrivialTorsion H) :
    ∃ K : Subgroup J, K.FiniteIndex ∧ HasNoNontrivialTorsion K := by
  obtain ⟨H, hHi, hHt⟩ := h
  let := hHi
  let d := H.equivMapOfInjective e.toMonoidHom e.injective
  exact ⟨H.map e.toMonoidHom, Subgroup.FiniteIndex.map_of_surjective H e.surjective,
    hHt.of_injective d.symm.toMonoidHom d.symm.injective⟩

theorem torsionFree_finiteIndex_of_cyclicStep {H K : Subgroup G}
    (s : CyclicStep H K) (hfg : Group.FG H)
    (hH : ∃ L : Subgroup H, L.FiniteIndex ∧ HasNoNontrivialTorsion L) :
    ∃ L : Subgroup K, L.FiniteIndex ∧ HasNoNontrivialTorsion L := by
  let e := (Subgroup.subgroupOfEquivOfLe s.le).symm
  let : Group.FG (H.subgroupOf K) :=
    @Group.fg_of_surjective _ _ _ _ hfg e.toMonoidHom e.surjective
  let := s.normal
  let := s.cyclic
  exact torsionFree_finiteIndex_of_cyclic_extension (H.subgroupOf K)
    (torsionFree_finiteIndex_of_equiv e hH)

theorem IsPolycyclic.exists_torsionFree_finiteIndex (hG : IsPolycyclic G) :
    ∃ H : Subgroup G, H.FiniteIndex ∧ HasNoNontrivialTorsion H := by
  obtain ⟨n, ⟨c⟩⟩ := hG
  have hm : ∀ i, i ≤ n → Group.FG (c.group i) ∧
      ∃ H : Subgroup (c.group i), H.FiniteIndex ∧ HasNoNontrivialTorsion H := by
    intro i
    induction i with
    | zero =>
      intro _
      rw [c.first]
      refine ⟨inferInstance, ⊤, inferInstance, ?_⟩
      intro g m hm hg
      exact Subsingleton.elim _ _
    | succ i ih =>
      intro hi
      obtain ⟨hfg, htf⟩ := ih (by omega)
      exact ⟨finitelyGenerated_of_cyclicStep (c.step i (by omega)) hfg,
        torsionFree_finiteIndex_of_cyclicStep (c.step i (by omega)) hfg htf⟩
  have htop := (hm n le_rfl).2
  rw [c.last] at htop
  exact torsionFree_finiteIndex_of_equiv (Subgroup.topEquiv) htop

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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_RationalAbelianRank
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_NilpotentClassBound
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
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

end PolycyclicRecognition

end

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

theorem nilpotent_centerQuotient_torsionFree (hG : HasNoNontrivialTorsion G) :
    HasNoNontrivialTorsion (G ⧸ Subgroup.center G) := by
  intro q n hn hqn
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center G) q
  apply (QuotientGroup.eq_one_iff g).mpr
  apply nilpotent_mem_center_of_pow_mem_center hG g hn
  apply (QuotientGroup.eq_one_iff (g ^ n)).mp
  change (QuotientGroup.mk' (Subgroup.center G)) (g ^ n) = 1
  simpa only [map_pow] using hqn

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_NilpotentPolyZ
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.latticeNormalFlag_normal _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

namespace OAI

/-! # Torsion-free finitely generated nilpotent groups have poly-Z series

The center is a finitely generated integral lattice. Its quotient remains
torsion-free, so induction on nilpotency class and concatenation of the two
actual cyclic series give the result and integral Poincare duality.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped IsMulCommutative

theorem integralLattice_polyZ (n : ℕ) : IsPolyZ (IntegralLatticeGroup n) := by
  induction n with
  | zero => exact isPolyZ_of_subsingleton
  | succ n ih =>
    let q := latticeCoordinate n
    let t := latticeCoordinateSection n
    have ht : q t = Multiplicative.ofAdd 1 := latticeCoordinate_section n
    let := integerQuotient_isCyclic q t ht
    let := integerQuotient_infinite q t ht
    exact isPolyZ_of_normal_cyclic_quotient q.ker
      (ih.of_equiv (latticeCoordinateKernel n).symm) infiniteCyclic_torsionFree

theorem abelian_polyZ_of_finitelyGenerated_torsionFree {A : Type} [CommGroup A]
    [Group.FG A] (hA : HasNoNontrivialTorsion A) : IsPolyZ A := by
  obtain ⟨n, ⟨e⟩⟩ := exists_integralLattice_equiv hA
  exact (integralLattice_polyZ n).of_equiv e

theorem nilpotent_polyZ_of_finitelyGenerated_torsionFree {G : Type} [Group G]
    [Group.IsNilpotent G] [Group.FG G] (hG : HasNoNontrivialTorsion G) : IsPolyZ G := by
  apply Group.nilpotent_center_quotient_ind G
    (P := fun K _ _ => Group.FG K → HasNoNontrivialTorsion K → IsPolyZ K) ?_ ?_
      inferInstance hG
  · intro K _ _ _ _
    exact isPolyZ_of_subsingleton
  · intro K _ _ ih hfg hK
    let := hfg
    have hQ : IsPolyZ (K ⧸ Subgroup.center K) :=
      ih inferInstance (nilpotent_centerQuotient_torsionFree hK)
    let : Group.FG (Subgroup.center K) :=
      CriticalPercolation.nilpotent_subgroup_fg K (Subgroup.center K)
    have hZ : IsPolyZ (Subgroup.center K) :=
      abelian_polyZ_of_finitelyGenerated_torsionFree
        (hK.of_injective (Subgroup.center K).subtype Subtype.val_injective)
    exact isPolyZ_of_normal_subgroup (Subgroup.center K) hZ hQ

theorem nilpotent_poincareDuality_of_finitelyGenerated_torsionFree
    {G : Type} [Group G] [Group.IsNilpotent G] [Group.FG G]
    (hG : HasNoNontrivialTorsion G) : ∃ n, IsIntegralPoincareDualityGroup G n :=
  (nilpotent_polyZ_of_finitelyGenerated_torsionFree hG).exists_poincareDuality

end PolycyclicRecognition

end

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

theorem fg_subgroup_map {G A : Type*} [Group G] [Group A]
    {H : Subgroup G} (hH : H.FG) (q : G →* A) : (H.map q).FG := by
  obtain ⟨S, hS, hfin⟩ := (Subgroup.fg_iff H).mp hH
  refine (Subgroup.fg_iff _).mpr ⟨q '' S, ?_, hfin.image q⟩
  rw [← MonoidHom.map_closure, hS]

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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_RationalSpanDenominators
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Clearing denominators in a rational span -/

noncomputable section
namespace PolycyclicRecognition

variable {V : Type} [AddCommGroup V] [Module ℚ V]

theorem exists_nsmul_mem_integral_span {S : Set V} {v : V}
    (hv : v ∈ Submodule.span ℚ S) :
    ∃ n : ℕ, 0 < n ∧ n • v ∈ Submodule.span ℤ S := by
  induction hv using Submodule.span_induction with
  | mem v hv => exact ⟨1, by omega, by simpa using Submodule.subset_span hv⟩
  | zero => exact ⟨1, by omega, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨n, hn, hnx⟩ := hx
    obtain ⟨m, hm, hmy⟩ := hy
    refine ⟨n * m, Nat.mul_pos hn hm, ?_⟩
    rw [nsmul_add]
    apply Submodule.add_mem
    · simpa only [← mul_nsmul, Submodule.mem_toAddSubmonoid] using
        (Submodule.span ℤ S).nsmul_mem hnx m
    · simpa only [← mul_nsmul, Nat.mul_comm, Submodule.mem_toAddSubmonoid] using
        (Submodule.span ℤ S).nsmul_mem hmy n
  | smul r v _ hv =>
    obtain ⟨n, hn, hnv⟩ := hv
    refine ⟨n * r.den, Nat.mul_pos hn r.den_pos, ?_⟩
    have hcoeff : ((n * r.den : ℕ) : ℚ) * r = (r.num : ℚ) * (n : ℚ) := by
      have hden : (r.den : ℚ) * r = r.num := by
        calc
          (r.den : ℚ) * r = (r.den : ℚ) * ((r.num : ℚ) / (r.den : ℚ)) :=
            congrArg (fun z : ℚ => (r.den : ℚ) * z) r.num_div_den.symm
          _ = r.num := by field_simp
      push_cast
      calc
        (n : ℚ) * (r.den : ℚ) * r = (n : ℚ) * ((r.den : ℚ) * r) := mul_assoc _ _ _
        _ = (r.num : ℚ) * n := by rw [hden, mul_comm]
    have he : (n * r.den) • (r • v) = r.num • (n • v) := by
      rw [← Nat.cast_smul_eq_nsmul ℚ, ← Nat.cast_smul_eq_nsmul ℚ,
        ← Int.cast_smul_eq_zsmul ℚ, smul_smul, smul_smul, hcoeff]
    rw [he]
    exact (Submodule.span ℤ S).smul_mem r.num hnv

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_AbelianRootGenerators
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.rationalAbelianAut_map _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite generation up to roots in a finite-rank abelian group -/

noncomputable section
namespace PolycyclicRecognition

open scoped TensorProduct
variable {A : Type} [CommGroup A]

theorem rationalAbelianMap_span :
    Submodule.span ℚ (Set.range (rationalAbelianMap (A := A))) = ⊤ := by
  apply top_unique
  intro v hv
  clear hv
  induction v using OAI.tensorInductionOn with
  | tmul r a =>
    have ha := Submodule.subset_span (R := ℚ)
      (Set.mem_range_self (f := rationalAbelianMap (A := A)) a)
    have hr := (Submodule.span ℚ (Set.range (rationalAbelianMap (A := A)))).smul_mem r ha
    change r • (1 ⊗ₜ[ℤ] a) ∈ Submodule.span ℚ (Set.range (rationalAbelianMap (A := A))) at hr
    simpa only [TensorProduct.smul_tmul', smul_eq_mul, mul_one] using hr
  | add x y hx hy => exact Submodule.add_mem _ hx hy

theorem exists_finite_rationalAbelian_spanning_set
    (hA : HasNoNontrivialTorsion A) [Module.Finite ℚ (RationalAbelianSpace A)] :
    ∃ S : Set (Additive A), S.Finite ∧
      Submodule.span ℚ (rationalAbelianMap '' S) = ⊤ := by
  let f := rationalAbelianMap (A := A)
  obtain ⟨T, hT⟩ := Module.Finite.fg_top (R := ℚ) (M := RationalAbelianSpace A)
  have hTspan : (T : Set (RationalAbelianSpace A)) ⊆ Submodule.span ℚ (Set.range f) := by
    rw [rationalAbelianMap_span]
    exact fun _ _ => trivial
  obtain ⟨U, hU, hTU⟩ := Submodule.subset_span_finite_of_subset_span hTspan
  let S := f ⁻¹' (U : Set (RationalAbelianSpace A))
  have hS : S.Finite := U.finite_toSet.preimage (rationalAbelianMap_injective hA).injOn
  have himage : f '' S = (U : Set (RationalAbelianSpace A)) := by
    ext v
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ha
    · intro hv
      obtain ⟨a, rfl⟩ := hU hv
      exact ⟨a, hv, rfl⟩
  refine ⟨S, hS, ?_⟩
  rw [himage]
  apply top_unique
  rw [← hT]
  exact Submodule.span_le.mpr hTU

theorem abelian_exists_fg_subgroup_containing_powers
    (hA : HasNoNontrivialTorsion A) [Module.Finite ℚ (RationalAbelianSpace A)] :
    ∃ H : Subgroup A, H.FG ∧ ∀ a : A, ∃ n : ℕ, 0 < n ∧ a ^ n ∈ H := by
  obtain ⟨S, hS, hspan⟩ := exists_finite_rationalAbelian_spanning_set hA
  let H : Subgroup A :=
    { carrier := fun a => Additive.ofMul a ∈ Submodule.span ℤ S
      one_mem' := by
        change (0 : Additive A) ∈ Submodule.span ℤ S
        exact Submodule.zero_mem _
      mul_mem' := by
        intro a b ha hb
        change Additive.ofMul a + Additive.ofMul b ∈ Submodule.span ℤ S
        exact Submodule.add_mem _ ha hb
      inv_mem' := by
        intro a ha
        change -Additive.ofMul a ∈ Submodule.span ℤ S
        exact Submodule.neg_mem _ ha }
  have hH : H = Subgroup.closure (Additive.toMul '' S) := by
    apply Subgroup.toAddSubgroup.injective
    change (Submodule.span ℤ S).toAddSubgroup = _
    rw [Submodule.span_int_eq_addSubgroupClosure, Subgroup.toAddSubgroup_closure]
    congr 1
    ext a
    simp
  refine ⟨H, ?_, ?_⟩
  · rw [hH]
    exact (Subgroup.fg_iff _).mpr ⟨_, rfl, hS.image Additive.toMul⟩
  · intro a
    have ha : rationalAbelianMap (Additive.ofMul a) ∈
        Submodule.span ℚ (rationalAbelianMap '' S) := by rw [hspan]; trivial
    obtain ⟨n, hn, hna⟩ := exists_nsmul_mem_integral_span ha
    have hpre : n • Additive.ofMul a ∈ Submodule.span ℤ S := by
      rw [← map_nsmul, ← Submodule.map_span] at hna
      obtain ⟨b, hb, he⟩ := hna
      have he' := rationalAbelianMap_injective hA he
      exact he' ▸ hb
    refine ⟨n, hn, ?_⟩
    change Additive.ofMul (a ^ n) ∈ Submodule.span ℤ S
    simpa only [ofMul_pow] using hpre

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CentralRootGenerators
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite generation up to roots through a central extension -/

noncomputable section
namespace PolycyclicRecognition

variable {G : Type} [Group G]

theorem exists_fg_subgroup_containing_powers_of_center
    (hZ : ∃ L : Subgroup (Subgroup.center G), L.FG ∧
      ∀ z, ∃ n : ℕ, 0 < n ∧ z ^ n ∈ L)
    (hQ : ∃ L : Subgroup (G ⧸ Subgroup.center G), L.FG ∧
      ∀ x, ∃ n : ℕ, 0 < n ∧ x ^ n ∈ L) :
    ∃ H : Subgroup G, H.FG ∧ ∀ g, ∃ n : ℕ, 0 < n ∧ g ^ n ∈ H := by
  obtain ⟨LZ, hLZ, hz⟩ := hZ
  obtain ⟨LQ, hLQ, hq⟩ := hQ
  let q := QuotientGroup.mk' (Subgroup.center G)
  let P := LQ.comap q
  let : Group.FG LQ := (Group.fg_iff_subgroup_fg LQ).mpr hLQ
  obtain ⟨F, hF, hFsurj⟩ := exists_fg_subgroup_surjective
    (quotientSubgroupMap q LQ)
    (quotientSubgroupMap_surjective q (QuotientGroup.mk'_surjective _) LQ)
  let K := F.map P.subtype
  let Z := LZ.map (Subgroup.center G).subtype
  let H := K ⊔ Z
  refine ⟨H, (fg_subgroup_map hF P.subtype).sup
    (fg_subgroup_map hLZ (Subgroup.center G).subtype), ?_⟩
  intro g
  obtain ⟨n, hn, hgn⟩ := hq (q g)
  have hgn' : q (g ^ n) ∈ LQ := by simpa only [map_pow] using hgn
  obtain ⟨x, hx⟩ := hFsurj ⟨q (g ^ n), hgn'⟩
  let k : G := x.val.val
  have hk : k ∈ K := ⟨x.val, x.property, rfl⟩
  have hqk : q k = q (g ^ n) := congrArg Subtype.val hx
  let z := g ^ n * k⁻¹
  have hzZ : z ∈ Subgroup.center G := by
    apply (QuotientGroup.eq_one_iff z).mp
    change q z = 1
    change q (g ^ n * k⁻¹) = 1
    rw [map_mul, map_inv, hqk, mul_inv_cancel]
  obtain ⟨m, hm, hzm⟩ := hz ⟨z, hzZ⟩
  have hzm' : z ^ m ∈ Z := ⟨(⟨z, hzZ⟩ : Subgroup.center G) ^ m, hzm, rfl⟩
  have hcomm : Commute z k := (Subgroup.mem_center_iff.mp hzZ k).symm
  have he : g ^ n = z * k := by simp [z, mul_assoc]
  refine ⟨n * m, Nat.mul_pos hn hm, ?_⟩
  rw [pow_mul, he, hcomm.mul_pow]
  exact H.mul_mem ((show Z ≤ H from le_sup_right) hzm')
    (H.pow_mem ((show K ≤ H from le_sup_left) hk) m)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_NilpotentRootGenerators
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.cyclicTopHomologyInjection_mono _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.normalizedGroupIdentityClass_comparison _root_.OAI.PolycyclicRecognition.rationalCoefficientInclusion_apply _root_.OAI.PolycyclicRecognition.resolutionStableSyzygyTransition_class _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

namespace OAI

/-! # A finitely generated subgroup containing a power of every element

Central-quotient induction uses the uniform abelian rank bound in all
quotients. The chosen subgroup is an actual finite generating core; the
statement does not assert finite generation of the original nilpotent group.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped IsMulCommutative

theorem nilpotent_quotient_exists_fg_subgroup_containing_powers
    {G Q : Type} [Group G] [Group.IsNilpotent G] [Group Q] [Group.IsNilpotent Q]
    (d : ℕ) [CategoryTheory.HasProjectiveDimensionLE (trivialIntegral G) d]
    (q : G →* Q) (hq : Function.Surjective q) (hQ : HasNoNontrivialTorsion Q) :
    ∃ H : Subgroup Q, H.FG ∧ ∀ g, ∃ n : ℕ, 0 < n ∧ g ^ n ∈ H := by
  apply Group.nilpotent_center_quotient_ind Q
    (P := fun K _ _ => ∀ f : G →* K, Function.Surjective f → HasNoNontrivialTorsion K →
      ∃ H : Subgroup K, H.FG ∧ ∀ g, ∃ n : ℕ, 0 < n ∧ g ^ n ∈ H) ?_ ?_ q hq hQ
  · intro K _ _ _ _ _
    exact ⟨⊥, Subgroup.FG.bot, fun g => ⟨1, by omega, by simp [Subsingleton.elim g 1]⟩⟩
  · intro K _ _ ih f hf hK
    have hrank := nilpotent_quotient_abelian_subgroup_rank_le d f hf (Subgroup.center K)
    have hfinite : Module.Finite ℚ (RationalAbelianSpace (Subgroup.center K)) := by
      apply Module.rank_lt_aleph0_iff.mp
      rw [rationalAbelianSpace_rank]
      exact hrank.trans_lt Cardinal.natCast_lt_aleph0
    let := hfinite
    have hZ := abelian_exists_fg_subgroup_containing_powers
      (hK.of_injective (Subgroup.center K).subtype Subtype.val_injective)
    let qK := QuotientGroup.mk' (Subgroup.center K)
    have hquot := ih (qK.comp f) ((QuotientGroup.mk'_surjective _).comp hf)
      (nilpotent_centerQuotient_torsionFree hK)
    exact exists_fg_subgroup_containing_powers_of_center hZ hquot

theorem nilpotent_exists_fg_subgroup_containing_powers
    {G : Type} [Group G] [Group.IsNilpotent G]
    (hG : HasFiniteIntegralCohomologicalDimension G) :
    ∃ H : Subgroup G, H.FG ∧ ∀ g, ∃ n : ℕ, 0 < n ∧ g ^ n ∈ H := by
  have htf := hG.torsionFree
  obtain ⟨d, hd⟩ := hG
  let := hd
  exact nilpotent_quotient_exists_fg_subgroup_containing_powers d (MonoidHom.id G)
    Function.surjective_id htf

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_FiniteIndexNormalExtension
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite index from the kernel and quotient of a normal extension -/

noncomputable section
namespace PolycyclicRecognition

open scoped Pointwise
variable {G : Type*} [Group G]

theorem finiteIndex_of_normal_extension (N H : Subgroup G) [N.Normal]
    [(H.comap N.subtype).FiniteIndex]
    [(H.map (QuotientGroup.mk' N)).FiniteIndex] : H.FiniteIndex := by
  let P := H ⊔ N
  let J := H.subgroupOf P
  let L := H.comap N.subtype
  let f : (N ⧸ L) → (P ⧸ J) := Quotient.lift (s := QuotientGroup.leftRel L)
    (fun n : N => ((⟨(n : G), (show N ≤ P from le_sup_right) n.property⟩ : P) : P ⧸ J)) (by
      intro x y hxy
      apply QuotientGroup.eq.mpr
      change (x : G)⁻¹ * y ∈ H
      exact (QuotientGroup.leftRel_apply (s := L)).mp hxy)
  have hf : Function.Surjective f := by
    intro x
    obtain ⟨x, rfl⟩ := Quotient.exists_rep x
    have hx : (x : G) ∈ (N : Set G) * (H : Set G) := by
      rw [← Subgroup.normal_mul, sup_comm]
      exact x.property
    obtain ⟨n, hn, h, hh, he⟩ := hx
    refine ⟨Quotient.mk'' (⟨n, hn⟩ : N), ?_⟩
    apply QuotientGroup.eq.mpr
    change n⁻¹ * (x : G) ∈ H
    rw [← he, inv_mul_cancel_left]
    exact hh
  let : Finite (P ⧸ J) := Finite.of_surjective f hf
  have hJ : J.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have hP : P.FiniteIndex := by
    have he : (H.map (QuotientGroup.mk' N)).comap (QuotientGroup.mk' N) = P := by
      rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk']
    rw [← he]
    infer_instance
  refine ⟨?_⟩
  rw [← Subgroup.relIndex_mul_index (show H ≤ P from le_sup_left)]
  exact mul_ne_zero hJ.index_ne_zero hP.index_ne_zero

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_PolycyclicRootIndex
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Compatibility with OpenAI's Mathlib (d13f23b): a lemma it has and ours lacks. -/

private theorem Subgroup.index_zpowers_zpow_p2 {G : Type*} [Group G] {g : G} (hg : Subgroup.zpowers g = ⊤)
    (i : ℤ) : (Subgroup.zpowers (g ^ i)).index = i.gcd (orderOf g) := by
  have hs : Function.Surjective (zpowersHom G g) := by
    intro x
    have hx : x ∈ Subgroup.zpowers g := hg ▸ Subgroup.mem_top x
    obtain ⟨k, rfl⟩ := hx
    exact ⟨Multiplicative.ofAdd k, by simp⟩
  rw [← Subgroup.index_comap_of_surjective (H := Subgroup.zpowers (g ^ i)) hs]
  have hc : (Subgroup.zpowers (g ^ i)).comap (zpowersHom G g) =
      AddSubgroup.toSubgroup (AddSubgroup.zmultiples ((i.gcd (orderOf g) : ℕ) : ℤ)) := by
    ext n
    simp only [Subgroup.mem_comap, zpowersHom_apply, Subgroup.mem_zpowers_iff]
    change (∃ k : ℤ, (g ^ i) ^ k = g ^ n.toAdd) ↔ n.toAdd ∈ AddSubgroup.zmultiples _
    rw [Int.mem_zmultiples_iff]
    simp_rw [← zpow_mul]
    constructor
    · rintro ⟨k, hk⟩
      have h1 : ((orderOf g : ℤ)) ∣ i * k - n.toAdd := by
        rw [orderOf_dvd_iff_zpow_eq_one, zpow_sub, hk, mul_inv_cancel]
      have h2 : (i.gcd (orderOf g) : ℤ) ∣ i * k := (Int.gcd_dvd_left ..).mul_right k
      have h3 : (i.gcd (orderOf g) : ℤ) ∣ (orderOf g : ℤ) := Int.gcd_dvd_right ..
      have := (h3.trans h1)
      have h4 := dvd_sub h2 this
      simpa using h4
    · rintro ⟨d, hd⟩
      obtain ⟨a, b, hab⟩ : ∃ a b : ℤ, (i.gcd (orderOf g) : ℤ) = i * a + (orderOf g) * b :=
        ⟨i.gcdA (orderOf g), i.gcdB (orderOf g), Int.gcd_eq_gcd_ab i (orderOf g)⟩
      refine ⟨a * d, ?_⟩
      rw [hd, hab, add_mul, zpow_add, mul_assoc i a d, mul_assoc, zpow_mul g (orderOf g : ℤ),
        zpow_natCast, pow_orderOf_eq_one, one_zpow, mul_one]
  rw [hc, AddSubgroup.index_toSubgroup, Int.index_zmultiples, Int.natAbs_natCast]

namespace OAI

/-! # Full root subgroups have finite index in a polycyclic group -/

noncomputable section
namespace PolycyclicRecognition

open ChromaticCyclic
variable {G : Type*} [Group G]

theorem finiteIndex_of_cyclic_roots [IsCyclic G] (H : Subgroup G)
    (hH : ∀ g, ∃ n : ℕ, 0 < n ∧ g ^ n ∈ H) : H.FiniteIndex := by
  obtain ⟨g, hg⟩ := isCyclic_iff_exists_zpowers_eq_top.mp (inferInstance : IsCyclic G)
  obtain ⟨n, hn, hgn⟩ := hH g
  have hZ : (Subgroup.zpowers (g ^ (n : ℤ))).FiniteIndex := by
    refine ⟨?_⟩
    rw [Subgroup.index_zpowers_zpow_p2 hg]
    exact ne_of_gt (Int.gcd_pos_of_ne_zero_left _ (by exact_mod_cast ne_of_gt hn))
  let := hZ
  apply Subgroup.finiteIndex_of_le (H := Subgroup.zpowers (g ^ (n : ℤ)))
  exact Subgroup.zpowers_le.mpr (by simpa only [zpow_natCast] using hgn)

theorem finiteIndex_roots_cyclic_extension (N H : Subgroup G) [N.Normal]
    [IsCyclic (G ⧸ N)]
    (hN : ∀ L : Subgroup N, (∀ g, ∃ n : ℕ, 0 < n ∧ g ^ n ∈ L) → L.FiniteIndex)
    (hH : ∀ g, ∃ n : ℕ, 0 < n ∧ g ^ n ∈ H) : H.FiniteIndex := by
  let q := QuotientGroup.mk' N
  have hn : (H.comap N.subtype).FiniteIndex := hN _ (by
    intro g
    obtain ⟨n, hn, hg⟩ := hH g
    exact ⟨n, hn, hg⟩)
  have hq : (H.map q).FiniteIndex := finiteIndex_of_cyclic_roots _ (by
    intro x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N x
    obtain ⟨n, hn, hg⟩ := hH g
    exact ⟨n, hn, ⟨g ^ n, hg, by rw [map_pow]⟩⟩)
  let := hn
  let := hq
  exact finiteIndex_of_normal_extension N H

theorem IsPolycyclic.finiteIndex_of_roots (hG : IsPolycyclic G) (H : Subgroup G)
    (hH : ∀ g, ∃ n : ℕ, 0 < n ∧ g ^ n ∈ H) : H.FiniteIndex := by
  obtain ⟨n, ⟨c⟩⟩ := hG
  have hi (i : ℕ) (hi : i ≤ n) : ∀ L : Subgroup (c.group i),
      (∀ g, ∃ n : ℕ, 0 < n ∧ g ^ n ∈ L) → L.FiniteIndex := by
    induction i with
    | zero =>
      rw [c.first]
      intro L _
      infer_instance
    | succ i ih =>
      let s := c.step i (by omega)
      let N := (c.group i).subgroupOf (c.group (i + 1))
      let := s.normal
      let := s.cyclic
      intro L hL
      apply finiteIndex_roots_cyclic_extension N L _ hL
      intro A hA
      let e := (Subgroup.subgroupOfEquivOfLe s.le).symm
      have hAi : (A.comap e.toMonoidHom).FiniteIndex := ih (by omega) _ (by
        intro g
        obtain ⟨k, hk, hg⟩ := hA (e g)
        refine ⟨k, hk, ?_⟩
        change e (g ^ k) ∈ A
        rw [map_pow]
        exact hg)
      refine ⟨?_⟩
      rw [← A.index_comap_of_surjective (f := e.toMonoidHom) e.surjective]
      exact hAi.index_ne_zero
  have ht := hi n le_rfl
  rw [c.last] at ht
  let e := Subgroup.topEquiv (G := G)
  have htop : (H.comap e.toMonoidHom).FiniteIndex := ht _ (by
    intro g
    obtain ⟨k, hk, hg⟩ := hH (e g)
    exact ⟨k, hk, hg⟩)
  refine ⟨?_⟩
  rw [← H.index_comap_of_surjective (f := e.toMonoidHom) e.surjective]
  exact htop.index_ne_zero

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_NilpotentRootExhaustion
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exhausting a countable nilpotent group by finite-index extensions of a core

Finite integral dimension supplies a finitely generated root core. Every
finitely generated overgroup of that core contains it with finite index.
This gives the directed family needed to compute the kernel's homology.
-/

noncomputable section
namespace PolycyclicRecognition

variable {G : Type} [Group G] [Group.IsNilpotent G]

theorem nilpotent_rootCore_finiteIndex (hG : HasFiniteIntegralCohomologicalDimension G)
    (H : Subgroup G) (hH : ∀ g, ∃ n : ℕ, 0 < n ∧ g ^ n ∈ H)
    (L : Subgroup G) (hL : L.FG) : (H.subgroupOf L).FiniteIndex := by
  let : Group.FG L := (Group.fg_iff_subgroup_fg L).mpr hL
  have hp := (nilpotent_polyZ_of_finitelyGenerated_torsionFree
    (hG.subgroup L).torsionFree).isPolycyclic
  apply hp.finiteIndex_of_roots
  intro g
  obtain ⟨n, hn, hg⟩ := hH g
  exact ⟨n, hn, hg⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_NilpotentExhaustionDimension
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instNonemptyBases _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A common duality dimension for the nilpotent exhaustion -/

noncomputable section
namespace PolycyclicRecognition

variable {G : Type} [Group G] [Group.IsNilpotent G]

theorem nilpotent_rootCore_duality_dimension
    (hG : HasFiniteIntegralCohomologicalDimension G)
    (H : Subgroup G) (hH : H.FG)
    (hroot : ∀ g, ∃ n : ℕ, 0 < n ∧ g ^ n ∈ H) :
    ∃ d, IsIntegralPoincareDualityGroup H d ∧
      ∀ L : Subgroup G, L.FG → H ≤ L → IsIntegralPoincareDualityGroup L d := by
  let : Group.FG H := (Group.fg_iff_subgroup_fg H).mpr hH
  obtain ⟨d, hd⟩ := nilpotent_poincareDuality_of_finitelyGenerated_torsionFree
    (hG.subgroup H).torsionFree
  refine ⟨d, hd, ?_⟩
  intro L hL hHL
  let : Group.FG L := (Group.fg_iff_subgroup_fg L).mpr hL
  obtain ⟨e, he⟩ := nilpotent_poincareDuality_of_finitelyGenerated_torsionFree
    (hG.subgroup L).torsionFree
  let := nilpotent_rootCore_finiteIndex hG H hroot L hL
  have hHe : IsIntegralPoincareDualityGroup H e :=
    (he.finiteIndex_subgroup (H.subgroupOf L)).of_equiv
      (Subgroup.subgroupOfEquivOfLe hHL)
  have hde : d = e := hd.dimension_unique hHe
  exact hde ▸ he

theorem exists_nilpotent_duality_exhaustion_finiteIndex [Countable G]
    (hG : HasFiniteIntegralCohomologicalDimension G) :
    ∃ d : ℕ, ∃ S : ℕ → Subgroup G,
      Monotone S ∧ (∀ n, (S n).FG) ∧ (∀ g, ∃ n, g ∈ S n) ∧
      (∀ n, IsIntegralPoincareDualityGroup (S n) d) ∧
      (∀ i j, ((S i).subgroupOf (S j)).FiniteIndex) := by
  classical
  obtain ⟨H, hH, hroot⟩ := nilpotent_exists_fg_subgroup_containing_powers hG
  obtain ⟨d, _, hd⟩ := nilpotent_rootCore_duality_dimension hG H hH hroot
  obtain ⟨e, he⟩ := exists_surjective_nat G
  let T (n : ℕ) : Set G := Set.range (fun i : Fin n => e i)
  let S (n : ℕ) := H ⊔ Subgroup.closure (T n)
  have hS (n : ℕ) : (S n).FG :=
    hH.sup ((Subgroup.fg_iff _).mpr ⟨T n, rfl, Set.finite_range _⟩)
  refine ⟨d, S, ?_, hS, ?_, (fun n => hd (S n) (hS n) le_sup_left), ?_⟩
  · intro i j hij
    apply sup_le_sup_left
    apply Subgroup.closure_mono
    rintro g ⟨k, rfl⟩
    exact ⟨⟨k, k.isLt.trans_le hij⟩, rfl⟩
  · intro g
    obtain ⟨n, rfl⟩ := he g
    refine ⟨n + 1, (show Subgroup.closure (T (n + 1)) ≤ S (n + 1) from le_sup_right) ?_⟩
    exact Subgroup.subset_closure ⟨⟨n, Nat.lt_succ_self n⟩, rfl⟩
  · intro i j
    apply nilpotent_rootCore_finiteIndex hG (S i) _ (S j) (hS j)
    intro g
    obtain ⟨n, hn, hgn⟩ := hroot g
    exact ⟨n, hn, (show H ≤ S i from le_sup_left) hgn⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_PoincareTopHomology
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.cyclicTopHomologyInjection_mono _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Top homology of an integral Poincare duality group

The orientation representation is the regular-dual cokernel of the last
resolution differential. Its underlying integral module is rank one, and
maps from it represent top-degree homology with arbitrary coefficients.
-/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2100] Linear.homModule
variable {G : Type} [Group G]

theorem IsIntegralPoincareDualityGroup.topHomology_orientation {n : ℕ}
    (hG : IsIntegralPoincareDualityGroup G n) :
    ∃ D : Rep ℤ G, Nonempty (D.V ≃ₗ[ℤ] ℤ) ∧
      ∀ A : Rep ℤ G, Nonempty (groupHomology A n ≃ₗ[ℤ] (D ⟶ A)) := by
  classical
  obtain ⟨P, _, hfin, _⟩ := hG.1
  let := hG.cohomologicalDimension
  let Q := finiteProjectiveResolution P n
  have hQfin : ∀ i, IntegralRepresentationFinite G (Q.complex.X i) :=
    finiteTruncation_finite P n (fun i _ => hfin i)
  have hQbound : IsZero (Q.complex.X (n + 1)) :=
    finiteTruncation_isZero P n (n + 1) (by omega)
  let D := cokernel (regularDualMap (Q.complex.d n (n - 1)))
  obtain ⟨e⟩ := hG.2.2
  refine ⟨D, ⟨((regularDualCokernelCohomologyIso Q n hQbound).trans e).toLinearEquiv⟩, ?_⟩
  intro A
  exact ⟨boundedResolutionTopHomologyEquiv Q n hQfin hQbound A⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_FiniteIndexOrientation
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Compatibility of top-homology orientations at finite index

A nonzero intertwiner between integral rank-one representations determines
their isomorphism. Shapiro and finite-index induction/coinduction produce
that intertwiner without choosing fundamental classes.
-/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2100] Linear.homModule
variable {G : Type} [Group G]

theorem topHomology_orientation_restrict (H : Subgroup G) [H.FiniteIndex] (n : ℕ)
    (D : Rep ℤ G) (E : Rep ℤ H)
    (eD : D.V ≃ₗ[ℤ] ℤ) (eE : E.V ≃ₗ[ℤ] ℤ)
    (hD : ∀ A : Rep ℤ G, Nonempty (groupHomology A n ≃ₗ[ℤ] (D ⟶ A)))
    (hE : ∀ A : Rep ℤ H, Nonempty (groupHomology A n ≃ₗ[ℤ] (E ⟶ A))) :
    Nonempty (Rep.res H.subtype D ≅ E) := by
  classical
  obtain ⟨d⟩ := hD (Rep.ind H.subtype E)
  obtain ⟨e⟩ := hE E
  let a : (D ⟶ Rep.ind H.subtype E) ≃ₗ[ℤ] (Rep.res H.subtype D ⟶ E) :=
    (Linear.homCongr ℤ (Iso.refl D) (Rep.indCoindIso E)).trans
      (Rep.resCoindHomEquiv.{0} H.subtype D E).symm
  let b := a.symm.trans (d.symm.trans
    ((groupHomology.indIso H E n).toLinearEquiv.trans e))
  have hid : (𝟙 E : E ⟶ E) ≠ 0 := by
    intro h
    have hv := congrArg (fun f : E ⟶ E => f.hom (eE.symm 1)) h
    change eE.symm 1 = 0 at hv
    exact (show (1 : ℤ) ≠ 0 from one_ne_zero) (by simpa using congrArg eE hv)
  have hf : b.symm (𝟙 E) ≠ 0 := by
    intro h
    apply hid
    have he := congrArg b h
    simpa using he
  exact rankOne_rep_iso_of_nonzero (Rep.res H.subtype D) E eD eE (b.symm (𝟙 E)) hf

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_HomologyOrientationEquiv
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Transport of a top-homology orientation along a group isomorphism -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2100] Linear.homModule
variable {G J : Type} [Group G] [Group J]

theorem topHomology_orientation_of_equiv (e : G ≃* J) (n : ℕ) (D : Rep ℤ J)
    (hD : ∀ A : Rep ℤ J, Nonempty (groupHomology A n ≃ₗ[ℤ] (D ⟶ A))) :
    ∀ A : Rep ℤ G, Nonempty
      (groupHomology A n ≃ₗ[ℤ] (Rep.res e.toMonoidHom D ⟶ A)) := by
  intro A
  let B := Rep.res e.symm.toMonoidHom A
  let h := groupHomology.mapIso (A := A) (B := B) e (LinearEquiv.refl ℤ A.V) (by
    intro g
    ext a
    change A.ρ g a = A.ρ (e.symm (e g)) a
    rw [e.symm_apply_apply]) n
  obtain ⟨d⟩ := hD B
  exact ⟨h.toLinearEquiv.trans (d.trans ((restrictionHomLinearEquiv e D B).trans
    (Linear.homCongr ℤ (Iso.refl _) (orientationRestrictionRoundtripIso e A))))⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_TopHomologyCharacter
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Compatibility of orientation characters under finite-index embeddings -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2100] Linear.homModule
variable {G K : Type} [Group G] [Group K]

theorem topHomology_character_subgroup (H : Subgroup G) [H.FiniteIndex] (n : ℕ)
    (D : Rep ℤ G) (E : Rep ℤ H)
    (eD : D.V ≃ₗ[ℤ] ℤ) (eE : E.V ≃ₗ[ℤ] ℤ)
    (hD : ∀ A : Rep ℤ G, Nonempty (groupHomology A n ≃ₗ[ℤ] (D ⟶ A)))
    (hE : ∀ A : Rep ℤ H, Nonempty (groupHomology A n ≃ₗ[ℤ] (E ⟶ A))) :
    (rankOneCharacter D eD).comp H.subtype = rankOneCharacter E eE := by
  obtain ⟨i⟩ := topHomology_orientation_restrict H n D E eD eE hD hE
  exact rankOneCharacter_eq_of_iso (Rep.res H.subtype D) E eD eE i

theorem topHomology_character_embedding (f : K →* G) (hf : Function.Injective f)
    [f.range.FiniteIndex] (n : ℕ) (D : Rep ℤ G) (E : Rep ℤ K)
    (eD : D.V ≃ₗ[ℤ] ℤ) (eE : E.V ≃ₗ[ℤ] ℤ)
    (hD : ∀ A : Rep ℤ G, Nonempty (groupHomology A n ≃ₗ[ℤ] (D ⟶ A)))
    (hE : ∀ A : Rep ℤ K, Nonempty (groupHomology A n ≃ₗ[ℤ] (E ⟶ A))) :
    (rankOneCharacter D eD).comp f = rankOneCharacter E eE := by
  let e := MonoidHom.ofInjective hf
  let F := Rep.res e.symm.toMonoidHom E
  have hF := topHomology_orientation_of_equiv e.symm n E hE
  have hc := topHomology_character_subgroup f.range n D F eD eE hD hF
  ext k
  have he := congrArg (fun c : f.range →* ℤ => c (e k)) hc
  change (rankOneCharacter D eD) (f k) =
    (rankOneCharacter E eE) (e.symm (e k)) at he
  simpa only [e.symm_apply_apply, MonoidHom.comp_apply] using he

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_ExhaustionOrientation
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One orientation representation for every stage of the nilpotent exhaustion -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2100] Linear.homModule
variable {G : Type} [Group G]

theorem exists_exhaustion_orientation (S : ℕ → Subgroup G)
    (hS : Monotone S) (hcover : ∀ g, ∃ i, g ∈ S i) (n : ℕ)
    (hd : ∀ i, IsIntegralPoincareDualityGroup (S i) n)
    (hindex : ∀ i j, ((S i).subgroupOf (S j)).FiniteIndex) :
    ∃ R : Rep ℤ G, Nonempty (R.V ≃ₗ[ℤ] ℤ) ∧
      ∀ (i : ℕ) (A : Rep ℤ (S i)),
        Nonempty (groupHomology A n ≃ₗ[ℤ] (Rep.res (S i).subtype R ⟶ A)) := by
  classical
  choose D hDr hD using fun i => (hd i).topHomology_orientation
  let e (i : ℕ) := Classical.choice (hDr i)
  let χ (i : ℕ) := rankOneCharacter (D i) (e i)
  have hχ : ∀ i j (hij : i ≤ j) (g : S i),
      χ j (Subgroup.inclusion (hS hij) g) = χ i g := by
    intro i j hij g
    let f := Subgroup.inclusion (hS hij)
    have hrange : f.range = (S i).subgroupOf (S j) := by
      ext x
      constructor
      · rintro ⟨y, rfl⟩
        exact y.property
      · intro hx
        exact ⟨⟨x, hx⟩, rfl⟩
    let : f.range.FiniteIndex := by rw [hrange]; exact hindex i j
    have hf : Function.Injective f := by
      intro x y h
      exact Subtype.ext (congrArg (fun z : S j => (z : G)) h)
    have hc := topHomology_character_embedding f hf n (D j) (D i) (e j) (e i)
      (hD j) (hD i)
    exact congrArg (fun c : S i →* ℤ => c g) hc
  let ψ := exhaustiveCharacter S hS hcover χ hχ
  let R := scalarCharacterRep ψ
  refine ⟨R, ⟨LinearEquiv.refl ℤ ℤ⟩, ?_⟩
  intro i A
  have hvalue (g : S i) : ψ (g : G) = χ i g :=
    congrArg (fun c : S i →* ℤ => c g) (exhaustiveCharacter_restrict S hS hcover χ hχ i)
  let u : D i ≅ Rep.res (S i).subtype R :=
    Rep.mkIso (Representation.Equiv.mk (e i) (by
      intro g
      ext x
      change (e i) ((D i).ρ g x) = ψ (g : G) * (e i) x
      rw [rankOne_action_coordinate, hvalue]
      exact mul_comm _ _))
  obtain ⟨a⟩ := hD i A
  exact ⟨a.trans (Linear.homCongr ℤ u (Iso.refl A))⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_BarChainExhaustion
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite support in bar chains along a subgroup exhaustion

Every bar chain has a representative in one member of an increasing exhaustive
sequence of subgroups. The inclusion is injective in every degree.
-/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory
variable {G : Type} [Group G]

theorem finite_subset_subgroup_exhaustion (S : ℕ → Subgroup G)
    (hS : Monotone S) (hcover : ∀ g, ∃ n, g ∈ S n) (T : Finset G) :
    ∃ n, ∀ g ∈ T, g ∈ S n := by
  classical
  induction T using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert g T _ ih =>
    obtain ⟨i, hi⟩ := hcover g
    obtain ⟨j, hj⟩ := ih
    refine ⟨max i j, ?_⟩
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hS (le_max_left _ _) hi
    · exact hS (le_max_right _ _) (hj x hx)

theorem subgroupBarInclusion_injective (H : Subgroup G) (A : Rep ℤ G) (i : ℕ) :
    Function.Injective ((subgroupBarInclusion H A).f i) := by
  apply (ModuleCat.mono_iff_injective _).mp
  exact groupHomology.chainsMap_f_map_mono H.subtype
    (𝟙 (Rep.res H.subtype A)) Subtype.val_injective i

theorem exists_barChain_in_subgroup (S : ℕ → Subgroup G)
    (hS : Monotone S) (hcover : ∀ g, ∃ n, g ∈ S n)
    (A : Rep ℤ G) (i : ℕ)
    (z : (groupHomology.inhomogeneousChains A).X i) :
    ∃ n, ∃ w : (groupHomology.inhomogeneousChains (Rep.res (S n).subtype A)).X i,
      (subgroupBarInclusion (S n) A).f i w = z := by
  classical
  let T : Finset G := z.support.biUnion fun f => Finset.univ.image f
  obtain ⟨n, hn⟩ := finite_subset_subgroup_exhaustion S hS hcover T
  let f : (Fin i → S n) → (Fin i → G) := fun x => (S n).subtype ∘ x
  have hf : Function.Injective f := by
    intro a b hab
    funext j
    exact Subtype.val_injective (congrFun hab j)
  have hsupport (x : Fin i → G) (hx : x ∈ z.support) : x ∈ Set.range f := by
    refine ⟨fun j => ⟨x j, hn (x j) ?_⟩, rfl⟩
    exact Finset.mem_biUnion.mpr ⟨x, hx,
      Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩⟩
  obtain ⟨w, hw⟩ := (Finsupp.mem_range_mapDomain_iff f hf z).mpr (by
    intro x hx
    apply Finsupp.notMem_support_iff.mp
    exact fun h => hx (hsupport x h))
  refine ⟨n, w, ?_⟩
  simpa [subgroupBarInclusion, groupHomology.chainsMap_f, f] using hw

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_HomologyClassExhaustion
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Homology classes and finite generation along subgroup exhaustions -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2
variable {G : Type} [Group G]

theorem exists_homologyClass_in_subgroup (S : ℕ → Subgroup G)
    (hS : Monotone S) (hcover : ∀ g, ∃ n, g ∈ S n)
    (A : Rep ℤ G) (i : ℕ) (x : groupHomology A i) :
    ∃ n, ∃ y : groupHomology (Rep.res (S n).subtype A) i,
      subgroupHomologyInclusion (S n) A i y = x := by
  refine groupHomology_induction_on x ?_
  intro z
  obtain ⟨n, w, hw⟩ := exists_barChain_in_subgroup S hS hcover A i
    (groupHomology.iCycles A i z)
  let F := subgroupBarInclusion (S n) A
  let C := groupHomology.inhomogeneousChains (Rep.res (S n).subtype A)
  let j := (ComplexShape.down ℕ).next i
  have hwcycle : C.d i j w = 0 := by
    apply subgroupBarInclusion_injective (S n) A j
    have hc := congrArg (fun f => f.hom w) (F.comm i j)
    change F.f j (C.d i j w) = F.f j 0
    rw [map_zero]
    change (groupHomology.inhomogeneousChains A).d i j (F.f i w) =
      F.f j (C.d i j w) at hc
    rw [← hc, hw]
    exact congrArg (fun f => f.hom z)
      ((groupHomology.inhomogeneousChains A).iCycles_d i j)
  let wz := groupHomology.cyclesMk i j rfl w hwcycle
  have hwz : HomologicalComplex.cyclesMap F i wz = z := by
    apply (ModuleCat.mono_iff_injective (groupHomology.iCycles A i)).mp inferInstance
    have hc := congrArg (fun f => f.hom wz) (HomologicalComplex.cyclesMap_i F i)
    change groupHomology.iCycles A i (HomologicalComplex.cyclesMap F i wz) =
      F.f i (groupHomology.iCycles (Rep.res (S n).subtype A) i wz) at hc
    rw [groupHomology.iCycles_mk] at hc
    exact hc.trans hw
  refine ⟨n, groupHomology.π (Rep.res (S n).subtype A) i wz, ?_⟩
  have hn := congrArg (fun f => f.hom wz) (HomologicalComplex.homologyπ_naturality F i)
  change subgroupHomologyInclusion (S n) A i
      (groupHomology.π (Rep.res (S n).subtype A) i wz) =
    groupHomology.π A i (HomologicalComplex.cyclesMap F i wz) at hn
  exact hn.trans (congrArg (groupHomology.π A i) hwz)

theorem subgroupHomologyInclusion_factor {H K : Subgroup G} (hHK : H ≤ K)
    (A : Rep ℤ G) (i : ℕ) :
    groupHomology.map (Subgroup.inclusion hHK) (subgroupRestrictionMap hHK A) i ≫
        subgroupHomologyInclusion K A i = subgroupHomologyInclusion H A i := by
  change groupHomology.map _ _ i ≫ groupHomology.map _ _ i = groupHomology.map _ _ i
  rw [← groupHomology.map_comp]
  exact groupHomology.map_congr (by ext; rfl) (by ext; rfl) i

theorem subgroupHomologyInclusion_range_mono {H K : Subgroup G} (hHK : H ≤ K)
    (A : Rep ℤ G) (i : ℕ) :
    LinearMap.range (subgroupHomologyInclusion H A i).hom ≤
      LinearMap.range (subgroupHomologyInclusion K A i).hom := by
  rintro x ⟨y, rfl⟩
  refine ⟨groupHomology.map (Subgroup.inclusion hHK) (subgroupRestrictionMap hHK A) i y, ?_⟩
  exact congrArg (fun f => f.hom y) (subgroupHomologyInclusion_factor hHK A i)

theorem exists_surjective_homology_stage (S : ℕ → Subgroup G)
    (hS : Monotone S) (hcover : ∀ g, ∃ n, g ∈ S n)
    (A : Rep ℤ G) (i : ℕ) [Module.Finite ℤ (groupHomology A i)] :
    ∃ n, Epi (subgroupHomologyInclusion (S n) A i) := by
  classical
  have hstage (T : Finset (groupHomology A i)) :
      ∃ n, ∀ x ∈ T, x ∈ LinearMap.range (subgroupHomologyInclusion (S n) A i).hom := by
    induction T using Finset.induction_on with
    | empty => exact ⟨0, by simp⟩
    | @insert x T _ ih =>
      obtain ⟨n, y, hy⟩ := exists_homologyClass_in_subgroup S hS hcover A i x
      obtain ⟨m, hm⟩ := ih
      refine ⟨max n m, ?_⟩
      intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact subgroupHomologyInclusion_range_mono (hS (le_max_left _ _)) A i ⟨y, hy⟩
      · exact subgroupHomologyInclusion_range_mono (hS (le_max_right _ _)) A i (hm z hz)
  obtain ⟨T, hT⟩ := Module.Finite.fg_top (R := ℤ) (M := groupHomology A i)
  obtain ⟨n, hn⟩ := hstage T
  refine ⟨n, (ModuleCat.epi_iff_surjective _).mpr (LinearMap.range_eq_top.mp ?_)⟩
  apply top_unique
  rw [← hT]
  exact Submodule.span_le.mpr hn

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_ExhaustionOrientationDetection
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Detecting the orientation by nonzero top homology

A nonzero class survives in every sufficiently large stage of an exhaustion.
For rank-one integral coefficients, top duality at those stages identifies the
coefficient representation with the compatible orientation.
-/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2100] Linear.homModule
variable {G : Type} [Group G]

theorem exhaustion_orientation_of_nonzero_top
    (S : ℕ → Subgroup G) (hS : Monotone S) (hcover : ∀ g, ∃ i, g ∈ S i)
    (d : ℕ) (R : Rep ℤ G) (eR : R.V ≃ₗ[ℤ] ℤ)
    (hR : ∀ (i : ℕ) (A : Rep ℤ (S i)),
      Nonempty (groupHomology A d ≃ₗ[ℤ] (Rep.res (S i).subtype R ⟶ A)))
    (A : Rep ℤ G) (eA : A.V ≃ₗ[ℤ] ℤ)
    (x : groupHomology A d) (hx : x ≠ 0) : Nonempty (R ≅ A) := by
  obtain ⟨n, y, hy⟩ := exists_homologyClass_in_subgroup S hS hcover A d x
  have hk (k : ℕ) (hnk : n ≤ k) :
      Nonempty (Rep.res (S k).subtype R ≅ Rep.res (S k).subtype A) := by
    let z := groupHomology.map (Subgroup.inclusion (hS hnk))
      (subgroupRestrictionMap (hS hnk) A) d y
    have hz : z ≠ 0 := by
      intro hz
      apply hx
      have hf := congrArg (fun f => f y) (subgroupHomologyInclusion_factor (hS hnk) A d)
      change subgroupHomologyInclusion (S k) A d z =
        subgroupHomologyInclusion (S n) A d y at hf
      rw [hz, map_zero, hy] at hf
      exact hf.symm
    obtain ⟨e⟩ := hR k (Rep.res (S k).subtype A)
    have hf : e z ≠ 0 := by
      intro hf
      exact hz (e.injective (hf.trans (map_zero e).symm))
    exact rankOne_rep_iso_of_nonzero _ _ eR eA (e z) hf
  have hχ : rankOneCharacter R eR = rankOneCharacter A eA := by
    ext g
    obtain ⟨m, hm⟩ := hcover g
    let k := max n m
    obtain ⟨i⟩ := hk k (le_max_left _ _)
    have hkg : g ∈ S k := hS (le_max_right _ _) hm
    have hc := rankOneCharacter_eq_of_iso
      (Rep.res (S k).subtype R) (Rep.res (S k).subtype A) eR eA i
    exact congrArg (fun c : S k →* ℤ => c ⟨g, hkg⟩) hc
  exact ⟨rankOneCharacterIso R eR ≪≫
    eqToIso (congrArg scalarCharacterRep hχ) ≪≫ (rankOneCharacterIso A eA).symm⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_FiniteIndexTrace
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The index in the induction/coinduction trace -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory Representation
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2100] Linear.homModule
variable {G : Type} [Group G] (H : Subgroup G) [H.FiniteIndex] (D : Rep.{0} ℤ G)

theorem finiteIndexLift_return :
    finiteIndexLift H D ≫ finiteIndexReturn H D = H.index • (𝟙 D : D ⟶ D) := by
  classical
  let : Fintype (G ⧸ H) := Subgroup.fintypeQuotientOfFiniteIndex
  apply Rep.hom_ext
  apply IntertwiningMap.ext
  ext a
  change (finiteIndexReturn H D).hom
      (Rep.coindToInd (Rep.res H.subtype D)
        ((Rep.resCoindToHom H.subtype D (Rep.res H.subtype D) (𝟙 _)).hom a)) =
    H.index • a
  rw [Rep.coindToInd_apply, map_sum]
  have hc : Fintype.card (Quotient (QuotientGroup.rightRel H)) = H.index := by
    rw [QuotientGroup.card_quotient_rightRel, ← Nat.card_eq_fintype_card, ← H.index_eq_card]
  rw [← hc, ← Finset.card_univ, ← Finset.sum_const]
  apply Finset.sum_congr rfl
  intro c _
  induction c using Quotient.inductionOn with
  | h g =>
    simp only [Quotient.liftOn_mk, Rep.resCoindToHom_hom_apply_coe]
    change (finiteIndexReturn H D).hom
      (IndV.mk H.subtype (Rep.res H.subtype D).ρ g (D.ρ g a)) = a
    rw [finiteIndexReturn_mk, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]
    rfl

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_FiniteIntegralHomology
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.cyclicTopHomologyInjection_mono _root_.OAI.PolycyclicRecognition.finiteResolution_single_supported _root_.OAI.PolycyclicRecognition.finiteTruncationAugmentation_quasiIso _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integral homology finiteness from FP finiteness

Finite group-ring generators become finite integral generators after tensoring
with a finite integral coefficient module and taking coinvariants. Since the
integers are Noetherian, cycles and homology inherit finite generation.
-/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits
open MonoidalCategory
attribute [local instance 2000] Rep.hV2
variable {G : Type} [Group G]

theorem finite_coinvariantsTensor (A B : Rep ℤ G) [Module.Finite ℤ A]
    (hB : IntegralRepresentationFinite G B) :
    Module.Finite ℤ (((Rep.coinvariantsTensor ℤ G).obj A).obj B) := by
  classical
  obtain ⟨ι, hι, f, hf⟩ := finiteIntegralFreeCover_exists B hB
  let := hι
  let := hf
  let F := (Rep.coinvariantsTensor ℤ G).obj A
  let : Module ℤ (ι →₀ A) := Finsupp.module _ _
  have hfree : Module.Finite ℤ (F.obj (Rep.free ℤ G ι)) :=
    Module.Finite.equiv (Rep.coinvariantsTensorFreeLEquiv A ι).symm
  let := hfree
  have ht : Epi (𝟙 A ⊗ₘ f) := by
    apply (Rep.epi_iff_surjective _).mpr
    exact TensorProduct.map_surjective Function.surjective_id
      ((Rep.epi_iff_surjective f).mp hf)
  have hm : Epi (F.map f) := by
    change Epi ((Rep.coinvariantsFunctor ℤ G).map (𝟙 A ⊗ₘ f))
    infer_instance
  exact Module.Finite.of_surjective (F.map f).hom
    ((ModuleCat.epi_iff_surjective _).mp inferInstance)

theorem finite_homology_of_finite_term (C : ChainComplex (ModuleCat ℤ) ℕ) (i : ℕ)
    [Module.Finite ℤ (C.X i)] : Module.Finite ℤ (C.homology i) := by
  have hcycles : Module.Finite ℤ (C.cycles i) :=
    Module.Finite.of_injective (C.iCycles i).hom
      ((ModuleCat.mono_iff_injective _).mp inferInstance)
  let := hcycles
  exact Module.Finite.of_surjective (C.homologyπ i).hom
    ((ModuleCat.epi_iff_surjective _).mp inferInstance)

theorem TypeFP.homology_finite {n : ℕ} (hG : TypeFP G n)
    (A : Rep ℤ G) [Module.Finite ℤ A] : Module.Finite ℤ (groupHomology A n) := by
  classical
  obtain ⟨P, hP⟩ := hG
  let C := P.complex.coinvariantsTensorObj A
  have hX : Module.Finite ℤ (C.X n) := finite_coinvariantsTensor A _ (hP n le_rfl)
  let := hX
  have hH : Module.Finite ℤ (C.homology n) := finite_homology_of_finite_term C n
  let := hH
  exact Module.Finite.equiv (groupHomologyIso A n P).symm.toLinearEquiv

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_FiniteTopOrientation
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A finite nonzero top orientation homology group -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2100] Linear.homModule
variable {G : Type} [Group G]

theorem IsIntegralPoincareDualityGroup.exists_finite_nonzero_top {n : ℕ}
    (hG : IsIntegralPoincareDualityGroup G n) :
    ∃ D : Rep ℤ G, Nonempty (D.V ≃ₗ[ℤ] ℤ) ∧
      Module.Finite ℤ (groupHomology D n) ∧ ∃ x : groupHomology D n, x ≠ 0 := by
  obtain ⟨D, ⟨eD⟩, hD⟩ := hG.topHomology_orientation
  have hfiniteD : Module.Finite ℤ D := Module.Finite.equiv eD.symm
  let := hfiniteD
  refine ⟨D, ⟨eD⟩, (hG.typeFPInfinity G n).homology_finite D, ?_⟩
  obtain ⟨e⟩ := hD D
  refine ⟨e.symm (𝟙 D), ?_⟩
  intro hx
  have hid : (𝟙 D : D ⟶ D) = 0 := by
    have h := congrArg e hx
    simpa only [LinearEquiv.apply_symm_apply, map_zero] using h
  have hv := congrArg (fun f : D ⟶ D => eD (f.hom (eD.symm 1))) hid
  simp at hv

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_FinitelyGeneratedCountable
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Countability from a finite group generating set -/

namespace PolycyclicRecognition

theorem countable_of_group_fg (G : Type) [Group G] [Group.FG G] : Countable G := by
  obtain ⟨α, hα, f, hf⟩ := Group.fg_iff_exists_freeGroup_hom_surjective_finite.mp
    (inferInstance : Group.FG G)
  let := hα
  have : Countable (FreeGroup α) := by
    unfold FreeGroup
    infer_instance
  exact hf.countable

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_HomologyCoefficientLinearity
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integral linearity in the coefficient map -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory HomologicalComplex
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {k : Type} [CommRing k] {G H : Type} [Group G] [Group H]

theorem chainsMap_coefficient_zsmul (f : G →* H) {A : Rep k G} {B : Rep k H}
    (φ : A ⟶ Rep.res f B) (r : ℤ) :
    groupHomology.chainsMap f (r • φ) = r • groupHomology.chainsMap f φ := by
  apply HomologicalComplex.Hom.ext
  funext i
  apply ModuleCat.hom_ext
  apply Finsupp.lhom_ext'
  intro x
  apply LinearMap.ext
  intro v
  change (groupHomology.chainsMap f (r • φ)).f i (Finsupp.single x v) =
    r • (groupHomology.chainsMap f φ).f i (Finsupp.single x v)
  rw [groupHomology.chainsMap_f_single, groupHomology.chainsMap_f_single]
  change Finsupp.single (f ∘ x) (r • φ.hom v) = r • Finsupp.single (f ∘ x) (φ.hom v)
  exact map_zsmul (Finsupp.lsingle (R := k) (M := B.V) (f ∘ x)).toAddMonoidHom r (φ.hom v)

theorem homologyMap_coefficient_zsmul (f : G →* H) {A : Rep k G} {B : Rep k H}
    (φ : A ⟶ Rep.res f B) (r : ℤ) (i : ℕ) :
    groupHomology.map f (r • φ) i = r • groupHomology.map f φ i := by
  change homologyMap (groupHomology.chainsMap f (r • φ)) i = _
  rw [chainsMap_coefficient_zsmul]
  exact (homologyFunctor (ModuleCat k) (ComplexShape.down ℕ) i).map_zsmul

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_ResolutionHomologyNaturality
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A coefficient-natural comparison with a projective resolution

The comparison uses the bar resolution and a fixed homotopy equivalence of
projective resolutions, so changing coefficients commutes with it.
-/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits HomologicalComplex Rep
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2100] Linear.homModule
variable {G : Type} [Group G] {A B : Rep ℤ G}

theorem inhomogeneousChainsIso_coefficient [DecidableEq G] (f : A ⟶ B) :
    groupHomology.chainsMap (MonoidHom.id G) f ≫ (groupHomology.inhomogeneousChainsIso B).hom =
      (groupHomology.inhomogeneousChainsIso A).hom ≫
        coefficientTensorChainMap (barComplex ℤ G) f := by
  apply HomologicalComplex.Hom.ext
  funext i
  apply ModuleCat.hom_ext
  apply Finsupp.lhom_ext'
  intro x
  apply LinearMap.ext
  intro a
  change (groupHomology.inhomogeneousChainsIso B).hom.f i
      ((groupHomology.chainsMap (MonoidHom.id G) f).f i (Finsupp.single x a)) =
    (coefficientTensorChainMap (barComplex ℤ G) f).f i
      ((groupHomology.inhomogeneousChainsIso A).hom.f i (Finsupp.single x a))
  rw [groupHomology.chainsMap_f_single]
  change Rep.finsuppToCoinvariantsTensorFree B (Fin i → G) (Finsupp.single x (f.hom a)) =
    (coefficientTensorChainMap (barComplex ℤ G) f).f i
      (Rep.finsuppToCoinvariantsTensorFree A (Fin i → G) (Finsupp.single x a))
  rw [Rep.finsuppToCoinvariantsTensorFree_single, Rep.finsuppToCoinvariantsTensorFree_single]
  rfl

theorem coefficientNaturalHomologyIso_naturality [DecidableEq G]
    (P : ProjectiveResolution (Rep.trivial ℤ G ℤ)) (f : A ⟶ B) (n : ℕ) :
    groupHomology.map (MonoidHom.id G) f n ≫ (coefficientNaturalHomologyIso P B n).hom =
      (coefficientNaturalHomologyIso P A n).hom ≫
        HomologicalComplex.homologyMap (coefficientTensorChainMap P.complex f) n := by
  let u : barComplex ℤ G ⟶ P.complex :=
    (ProjectiveResolution.homotopyEquiv (barResolution ℤ G) P).hom
  have hn := (NatTrans.mapHomologicalComplex ((Rep.coinvariantsTensor ℤ G).map f)
    (ComplexShape.down ℕ)).naturality u
  change (((Rep.coinvariantsTensor ℤ G).obj A).mapHomologicalComplex _).map u ≫
      coefficientTensorChainMap P.complex f =
    coefficientTensorChainMap (barComplex ℤ G) f ≫
      (((Rep.coinvariantsTensor ℤ G).obj B).mapHomologicalComplex _).map u at hn
  have hc : groupHomology.chainsMap (MonoidHom.id G) f ≫
      ((groupHomology.inhomogeneousChainsIso B).hom ≫
        (((Rep.coinvariantsTensor ℤ G).obj B).mapHomologicalComplex _).map u) =
      ((groupHomology.inhomogeneousChainsIso A).hom ≫
        (((Rep.coinvariantsTensor ℤ G).obj A).mapHomologicalComplex _).map u) ≫
          coefficientTensorChainMap P.complex f := by
    rw [← Category.assoc, inhomogeneousChainsIso_coefficient, Category.assoc]
    rw [← hn, ← Category.assoc]
  change HomologicalComplex.homologyMap (groupHomology.chainsMap (MonoidHom.id G) f) n ≫
      (HomologicalComplex.homologyMap (groupHomology.inhomogeneousChainsIso B).hom n ≫
        HomologicalComplex.homologyMap
          ((((Rep.coinvariantsTensor ℤ G).obj B).mapHomologicalComplex _).map u) n) =
    (HomologicalComplex.homologyMap (groupHomology.inhomogeneousChainsIso A).hom n ≫
      HomologicalComplex.homologyMap
        ((((Rep.coinvariantsTensor ℤ G).obj A).mapHomologicalComplex _).map u) n) ≫
      HomologicalComplex.homologyMap (coefficientTensorChainMap P.complex f) n
  simpa only [HomologicalComplex.homologyMap_comp] using
    congrArg (fun v => HomologicalComplex.homologyMap v n) hc

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_InnerHomologyAction
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Inner conjugation is the identity on group homology -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory HomologicalComplex
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2200] TensorProduct.instModule
attribute [local instance 2300] Representation.Coinvariants.instModule Pi.Function.module
variable {G : Type} [Group G] (A : Rep ℤ G)

theorem innerBarMap_tensor_chains [DecidableEq G] (a : G) :
    groupHomology.chainsMap (MulAut.conj a).toMonoidHom (innerHomologyCoefficient A a) ≫
        (groupHomology.inhomogeneousChainsIso A).hom =
      (groupHomology.inhomogeneousChainsIso A).hom ≫
        (((Rep.coinvariantsTensor ℤ G).obj A).mapHomologicalComplex _).map (innerBarMap a) := by
  apply HomologicalComplex.Hom.ext
  funext i
  apply ModuleCat.hom_ext
  apply Finsupp.lhom_ext'
  intro x
  apply LinearMap.ext
  intro v
  change Rep.finsuppToCoinvariantsTensorFree A (Fin i → G)
      ((groupHomology.chainsMap (MulAut.conj a).toMonoidHom
        (innerHomologyCoefficient A a)).f i (Finsupp.single x v)) =
    (((Rep.coinvariantsTensor ℤ G).obj A).map (innerBarFreeMap a i))
      (Rep.finsuppToCoinvariantsTensorFree A (Fin i → G) (Finsupp.single x v))
  rw [groupHomology.chainsMap_f_single, Rep.finsuppToCoinvariantsTensorFree_single,
    Rep.finsuppToCoinvariantsTensorFree_single]
  change Representation.Coinvariants.mk (A.ρ.tprod (Representation.free ℤ G (Fin i → G)))
      ((A.ρ a v) ⊗ₜ[ℤ] Finsupp.single ((MulAut.conj a) ∘ x) (MonoidAlgebra.single 1 1)) =
    Representation.Coinvariants.mk (A.ρ.tprod (Representation.free ℤ G (Fin i → G)))
      (v ⊗ₜ[ℤ] (innerBarFreeMap a i).hom (Finsupp.single x (MonoidAlgebra.single 1 1)))
  rw [innerBarFreeMap_single, one_mul]
  have h := Representation.Coinvariants.mk_tmul_inv A.ρ
    (Representation.free ℤ G (Fin i → G)) v
    (Finsupp.single ((MulAut.conj a) ∘ x) (MonoidAlgebra.single 1 1)) a
  rw [Representation.free_single_single, mul_one] at h
  exact h.symm

theorem innerHomologyMap_eq_id (a : G) (i : ℕ) :
    groupHomology.map (MulAut.conj a).toMonoidHom (innerHomologyCoefficient A a) i =
      𝟙 (groupHomology A i) := by
  classical
  let F := (((Rep.coinvariantsTensor ℤ G).obj A).mapHomologicalComplex _).map (innerBarMap a)
  have hF : homologyMap F i = 𝟙 _ := by
    have h := (((Rep.coinvariantsTensor ℤ G).obj A).mapHomotopy
      (innerBarMapHomotopy a)).homologyMap_eq i
    let T := ((Rep.coinvariantsTensor ℤ G).obj A).mapHomologicalComplex (ComplexShape.down ℕ)
    have hId : T.map (𝟙 (Rep.barComplex ℤ G)) = 𝟙 (T.obj (Rep.barComplex ℤ G)) :=
      T.map_id _
    change homologyMap F i = homologyMap (T.map (𝟙 (Rep.barComplex ℤ G))) i at h
    rw [hId, homologyMap_id] at h
    exact h
  have hc := congrArg (fun f => homologyMap f i) (innerBarMap_tensor_chains A a)
  rw [homologyMap_comp, homologyMap_comp] at hc
  change groupHomology.map (MulAut.conj a).toMonoidHom (innerHomologyCoefficient A a) i ≫
      homologyMap (groupHomology.inhomogeneousChainsIso A).hom i =
    homologyMap (groupHomology.inhomogeneousChainsIso A).hom i ≫ homologyMap F i at hc
  rw [hF, Category.comp_id] at hc
  exact (cancel_mono (homologyMap (groupHomology.inhomogeneousChainsIso A).hom i)).mp
    (hc.trans (Category.id_comp _).symm)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_HomologyBoundary
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Boundaries detected by vanishing homology classes -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits HomologicalComplex

variable {R : Type} [CommRing R]

theorem exists_boundary_of_homologyπ_eq_zero (C : ChainComplex (ModuleCat R) ℕ)
    (n : ℕ) (z : C.cycles n) (hz : C.homologyπ n z = 0) :
    ∃ w : C.X (n + 1), C.d (n + 1) n w = C.iCycles n z := by
  let S := ShortComplex.mk (C.toCycles (n + 1) n) (C.homologyπ n)
    (C.toCycles_comp_homologyπ (n + 1) n)
  have he : S.Exact := S.exact_of_g_is_cokernel
    (C.homologyIsCokernel (n + 1) n (ChainComplex.prev ℕ n))
  obtain ⟨w, hw⟩ := (ShortComplex.moduleCat_exact_iff S).mp he z hz
  refine ⟨w, ?_⟩
  have h := congrArg (fun t => C.iCycles n t) hw
  exact (congrArg (fun f => f w) (C.toCycles_i (n + 1) n)).symm.trans h

theorem homologyπ_eq_zero_of_boundary (C : ChainComplex (ModuleCat R) ℕ)
    (n : ℕ) (z : C.cycles n) (w : C.X (n + 1))
    (hw : C.d (n + 1) n w = C.iCycles n z) : C.homologyπ n z = 0 := by
  have hz : C.toCycles (n + 1) n w = z := by
    apply (ModuleCat.mono_iff_injective (C.iCycles n)).mp inferInstance
    exact (congrArg (fun f => f w) (C.toCycles_i (n + 1) n)).trans hw
  rw [← hz]
  exact congrArg (fun f => f w) (C.toCycles_comp_homologyπ (n + 1) n)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_HomologyExhaustionInjectivity
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Detection of zero classes in a subgroup exhaustion -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory HomologicalComplex
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G]

theorem subgroupBarInclusion_factor {H K : Subgroup G} (hHK : H ≤ K)
    (A : Rep ℤ G) :
    groupHomology.chainsMap (Subgroup.inclusion hHK) (subgroupRestrictionMap hHK A) ≫
      subgroupBarInclusion K A = subgroupBarInclusion H A := by
  change groupHomology.chainsMap _ _ ≫ groupHomology.chainsMap _ _ =
    groupHomology.chainsMap _ _
  rw [← groupHomology.chainsMap_comp]
  exact groupHomology.chainsMap_congr (by ext; rfl)
    (by apply DFunLike.ext; intro x; rfl)

theorem homology_zero_in_stage (S : ℕ → Subgroup G) (hS : Monotone S)
    (hcover : ∀ g, ∃ n, g ∈ S n) (A : Rep ℤ G) (i n : ℕ)
    (x : groupHomology (Rep.res (S n).subtype A) i)
    (hx : subgroupHomologyInclusion (S n) A i x = 0) :
    ∃ m, ∃ hnm : n ≤ m,
      groupHomology.map (Subgroup.inclusion (hS hnm))
        (subgroupRestrictionMap (hS hnm) A) i x = 0 := by
  induction x using groupHomology_induction_on with
  | h z =>
    let C := groupHomology.inhomogeneousChains A
    let F := subgroupBarInclusion (S n) A
    have hn := congrArg (fun f => f z) (homologyπ_naturality F i)
    change subgroupHomologyInclusion (S n) A i (groupHomology.π _ i z) =
      C.homologyπ i (cyclesMap F i z) at hn
    obtain ⟨w, hw⟩ := exists_boundary_of_homologyπ_eq_zero C i (cyclesMap F i z)
      (hn.symm.trans hx)
    let T (k : ℕ) := S (n + k)
    have hT : Monotone T := fun a b hab => hS (Nat.add_le_add_left hab n)
    have hcoverT : ∀ g, ∃ k, g ∈ T k := by
      intro g
      obtain ⟨k, hk⟩ := hcover g
      exact ⟨k, hS (Nat.le_add_left k n) hk⟩
    obtain ⟨k, v, hv⟩ := exists_barChain_in_subgroup T hT hcoverT A (i + 1) w
    let m := n + k
    have hnm : n ≤ m := Nat.le_add_right n k
    let J := groupHomology.chainsMap (Subgroup.inclusion (hS hnm))
      (subgroupRestrictionMap (hS hnm) A)
    let Cm := groupHomology.inhomogeneousChains (Rep.res (S m).subtype A)
    let Fm := subgroupBarInclusion (S m) A
    have hj : Fm.f i (Cm.iCycles i (cyclesMap J i z)) = C.iCycles i (cyclesMap F i z) := by
      have hc := congrArg (fun f => f z) (cyclesMap_i J i)
      change Cm.iCycles i (cyclesMap J i z) = J.f i (groupHomology.iCycles _ i z) at hc
      rw [hc]
      have hcomp := congrArg (fun f => f.f i (groupHomology.iCycles _ i z))
        (subgroupBarInclusion_factor (hS hnm) A)
      have hcy := congrArg (fun f => f z) (cyclesMap_i F i)
      exact hcomp.trans hcy.symm
    have hb : Cm.d (i + 1) i v = Cm.iCycles i (cyclesMap J i z) := by
      apply subgroupBarInclusion_injective (S m) A i
      have hc := congrArg (fun f => f v) (Fm.comm (i + 1) i)
      change C.d (i + 1) i (Fm.f (i + 1) v) = Fm.f i (Cm.d (i + 1) i v) at hc
      rw [← hc, hv, hw, hj]
    have hz := homologyπ_eq_zero_of_boundary Cm i (cyclesMap J i z) v hb
    refine ⟨m, hnm, ?_⟩
    have hc := congrArg (fun f => f z) (homologyπ_naturality J i)
    exact hc.trans hz

theorem subgroupHomologyInclusion_injective_of_stages
    (S : ℕ → Subgroup G) (hS : Monotone S) (hcover : ∀ g, ∃ n, g ∈ S n)
    (A : Rep ℤ G) (i : ℕ)
    (hinj : ∀ n m (hnm : n ≤ m), Function.Injective
      (groupHomology.map (Subgroup.inclusion (hS hnm))
        (subgroupRestrictionMap (hS hnm) A) i)) (n : ℕ) :
    Function.Injective (subgroupHomologyInclusion (S n) A i) := by
  apply (injective_iff_map_eq_zero (subgroupHomologyInclusion (S n) A i).hom).mpr
  intro x hx
  obtain ⟨m, hnm, hm⟩ := homology_zero_in_stage S hS hcover A i n x hx
  apply hinj n m hnm
  simpa using hm

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_HomologyRankOneLimit
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integral rank-one properties of the exhausted top homology -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory
attribute [local instance 2000] Rep.hV2 Rep.instLinear ModuleCat.isModule
variable {G : Type} [Group G]

theorem exists_pair_in_homology_stage (S : ℕ → Subgroup G) (hS : Monotone S)
    (hcover : ∀ g, ∃ n, g ∈ S n) (A : Rep ℤ G) (i : ℕ)
    (x y : groupHomology A i) :
    ∃ n, ∃ x' y' : groupHomology (Rep.res (S n).subtype A) i,
      subgroupHomologyInclusion (S n) A i x' = x ∧
        subgroupHomologyInclusion (S n) A i y' = y := by
  obtain ⟨n, x', hx⟩ := exists_homologyClass_in_subgroup S hS hcover A i x
  obtain ⟨m, y', hy⟩ := exists_homologyClass_in_subgroup S hS hcover A i y
  refine ⟨max n m,
    groupHomology.map (Subgroup.inclusion (hS (le_max_left n m)))
      (subgroupRestrictionMap (hS (le_max_left n m)) A) i x',
    groupHomology.map (Subgroup.inclusion (hS (le_max_right n m)))
      (subgroupRestrictionMap (hS (le_max_right n m)) A) i y', ?_, ?_⟩
  · exact (congrArg (fun f => f x')
      (subgroupHomologyInclusion_factor (hS (le_max_left n m)) A i)).trans hx
  · exact (congrArg (fun f => f y')
      (subgroupHomologyInclusion_factor (hS (le_max_right n m)) A i)).trans hy

theorem homology_commensurable_of_rankOne_stages
    (S : ℕ → Subgroup G) (hS : Monotone S) (hcover : ∀ g, ∃ n, g ∈ S n)
    (A : Rep ℤ G) (i : ℕ)
    (hrank : ∀ n, Nonempty (groupHomology (Rep.res (S n).subtype A) i ≃ₗ[ℤ] ℤ))
    (x y : groupHomology A i) (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ a b : ℤ, a ≠ 0 ∧ b ≠ 0 ∧ a • x = b • y := by
  obtain ⟨n, x', y', hx', hy'⟩ := exists_pair_in_homology_stage S hS hcover A i x y
  obtain ⟨e⟩ := hrank n
  have hxn : e x' ≠ 0 := by
    intro h
    have hz : x' = 0 := e.injective (h.trans (map_zero e).symm)
    exact hx (hx'.symm.trans (hz ▸ map_zero _))
  have hyn : e y' ≠ 0 := by
    intro h
    have hz : y' = 0 := e.injective (h.trans (map_zero e).symm)
    exact hy (hy'.symm.trans (hz ▸ map_zero _))
  have heq : (e y') • x' = (e x') • y' := by
    apply e.injective
    simp only [map_zsmul, zsmul_eq_mul]
    exact mul_comm _ _
  refine ⟨e y', e x', hyn, hxn, ?_⟩
  have he := congrArg (fun z => subgroupHomologyInclusion (S n) A i z) heq
  simpa only [map_zsmul, hx', hy'] using he

theorem homology_torsionFree_of_rankOne_stages
    (S : ℕ → Subgroup G) (hS : Monotone S) (hcover : ∀ g, ∃ n, g ∈ S n)
    (A : Rep ℤ G) (i : ℕ)
    (hrank : ∀ n, Nonempty (groupHomology (Rep.res (S n).subtype A) i ≃ₗ[ℤ] ℤ))
    (hinj : ∀ n, Function.Injective (subgroupHomologyInclusion (S n) A i)) :
    ∀ (z : ℤ) (x : groupHomology A i), z • x = 0 → z = 0 ∨ x = 0 := by
  intro z x hzx
  obtain ⟨n, x', hx'⟩ := exists_homologyClass_in_subgroup S hS hcover A i x
  obtain ⟨e⟩ := hrank n
  have hxz : z • x' = 0 := hinj n (by simpa only [map_zsmul, hx', map_zero] using hzx)
  have h := congrArg e hxz
  simp only [map_zsmul, map_zero, zsmul_eq_mul] at h
  rcases mul_eq_zero.mp h with hz | hx
  · exact Or.inl hz
  · right
    have hx0 : x' = 0 := e.injective (hx.trans (map_zero e).symm)
    exact hx'.symm.trans (hx0 ▸ map_zero _)

theorem rankOne_homology_map_eq_zero_of_nonzero_kernel
    {M : ModuleCat ℤ}
    (htorsion : ∀ (z : ℤ) (x : M), z • x = 0 → z = 0 ∨ x = 0)
    (hcomm : ∀ x y : M, x ≠ 0 → y ≠ 0 →
      ∃ a b : ℤ, a ≠ 0 ∧ b ≠ 0 ∧ a • x = b • y)
    (f : M ⟶ M) (x : M) (hx : x ≠ 0) (hfx : f x = 0) : f = 0 := by
  apply ModuleCat.hom_ext
  apply DFunLike.ext
  intro y
  by_cases hy : y = 0
  · simp [hy]
  obtain ⟨a, b, _, hb, he⟩ := hcomm x y hx hy
  have hf := congrArg (fun z => f z) he
  simp only [map_zsmul, hfx, zsmul_zero] at hf
  exact (htorsion b (f y) hf.symm).resolve_left hb

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_RationalRankOneHomology
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Rationalizing a torsion-free commensurable homology group -/

noncomputable section
namespace PolycyclicRecognition

open scoped TensorProduct
variable {M : Type} [AddCommGroup M] [Module ℤ M]

theorem rational_rankOne_span
    (hcomm : ∀ x y : M, x ≠ 0 → y ≠ 0 →
      ∃ a b : ℤ, a ≠ 0 ∧ b ≠ 0 ∧ a • x = b • y)
    (x : M) (hx : x ≠ 0) :
    Submodule.span ℚ ({1 ⊗ₜ[ℤ] x} : Set (ℚ ⊗[ℤ] M)) = ⊤ := by
  have hy (y : M) : (1 : ℚ) ⊗ₜ[ℤ] y ∈
      Submodule.span ℚ ({1 ⊗ₜ[ℤ] x} : Set (ℚ ⊗[ℤ] M)) := by
    by_cases hzero : y = 0
    · simp [hzero]
    obtain ⟨a, b, ha, _, hab⟩ := hcomm y x hzero hx
    have haQ : (a : ℚ) ≠ 0 := by exact_mod_cast ha
    have ht : (a : ℚ) • ((1 : ℚ) ⊗ₜ[ℤ] y) =
        (b : ℚ) • ((1 : ℚ) ⊗ₜ[ℤ] x) := by
      calc
        (a : ℚ) • ((1 : ℚ) ⊗ₜ[ℤ] y) = (a • (1 : ℚ)) ⊗ₜ[ℤ] y := by
          simp only [TensorProduct.smul_tmul', smul_eq_mul, zsmul_eq_mul, mul_one]
        _ = (1 : ℚ) ⊗ₜ[ℤ] (a • y) := by
          have h₁ := LinearMap.congr_fun ((TensorProduct.mk ℤ ℚ M).map_smul a 1) y
          have h₂ := ((TensorProduct.mk ℤ ℚ M) 1).map_smul a y
          exact (h₁.trans h₂.symm).trans (congrArg (fun z : M => (1 : ℚ) ⊗ₜ[ℤ] z)
            (int_smul_eq_zsmul (inferInstance : Module ℤ M) a y))
        _ = (1 : ℚ) ⊗ₜ[ℤ] (b • x) := congrArg (fun z : M => (1 : ℚ) ⊗ₜ[ℤ] z) hab
        _ = (b • (1 : ℚ)) ⊗ₜ[ℤ] x := by
          have h₁ := LinearMap.congr_fun ((TensorProduct.mk ℤ ℚ M).map_smul b 1) x
          have h₂ := ((TensorProduct.mk ℤ ℚ M) 1).map_smul b x
          exact (congrArg (fun z : M => (1 : ℚ) ⊗ₜ[ℤ] z)
            (int_smul_eq_zsmul (inferInstance : Module ℤ M) b x)).symm.trans (h₂.trans h₁.symm)
        _ = (b : ℚ) • ((1 : ℚ) ⊗ₜ[ℤ] x) := by
          simp only [TensorProduct.smul_tmul', smul_eq_mul, zsmul_eq_mul, mul_one]
    have he : (1 : ℚ) ⊗ₜ[ℤ] y =
        (a : ℚ)⁻¹ • ((b : ℚ) • ((1 : ℚ) ⊗ₜ[ℤ] x)) := by
      rw [← ht, inv_smul_smul₀ haQ]
    rw [he]
    exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  apply top_unique
  intro z hz
  clear hz
  induction z using OAI.tensorInductionOn with
  | tmul r y =>
    have h := Submodule.smul_mem (Submodule.span ℚ ({1 ⊗ₜ[ℤ] x} : Set (ℚ ⊗[ℤ] M))) r (hy y)
    simpa only [TensorProduct.smul_tmul', smul_eq_mul, mul_one] using h
  | add z w hz hw => exact Submodule.add_mem _ hz hw

theorem rational_rankOne_equiv
    (htor : ∀ (a : ℤ) (x : M), a • x = 0 → a = 0 ∨ x = 0)
    (hcomm : ∀ x y : M, x ≠ 0 → y ≠ 0 →
      ∃ a b : ℤ, a ≠ 0 ∧ b ≠ 0 ∧ a • x = b • y)
    (x : M) (hx : x ≠ 0) : Nonempty ((ℚ ⊗[ℤ] M) ≃ₗ[ℚ] ℚ) := by
  let : Module.IsTorsionFree ℤ M := Module.isTorsionFree_iff_smul_eq_zero.mpr (by
    intro a x hx
    apply htor a x
    change (inferInstance : Module ℤ M).smul a x = 0 at hx
    rwa [int_smul_eq_zsmul] at hx)
  have hi := Module.Flat.tensorProduct_mk_injective ℤ M ℚ
  have hxQ : (1 : ℚ) ⊗ₜ[ℤ] x ≠ 0 := by
    intro h
    exact hx (hi (h.trans (TensorProduct.tmul_zero M 1).symm))
  have hspan := rational_rankOne_span hcomm x hx
  let e := LinearEquiv.toSpanNonzeroSingleton ℚ (ℚ ⊗[ℤ] M) (1 ⊗ₜ[ℤ] x) hxQ
  exact ⟨(e.trans ((LinearEquiv.ofEq _ _ hspan).trans Submodule.topEquiv)).symm⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_RationalRankOneAction
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The rational character of an action on a rank-one abelian group -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory
open scoped TensorProduct
variable {G M : Type} [Group G] [AddCommGroup M] [Module ℤ M]

theorem rationalActionCharacter_ne_zero (ρ : G →* AddMonoid.End M)
    (e : (ℚ ⊗[ℤ] M) ≃ₗ[ℚ] ℚ) (g : G) : rationalActionCharacter ρ e g ≠ 0 := by
  intro hz
  have h := map_mul (rationalActionCharacter ρ e) g g⁻¹
  rw [mul_inv_cancel, map_one, hz, zero_mul] at h
  exact one_ne_zero h

theorem rationalActionCharacter_of_zsmul (ρ : G →* AddMonoid.End M)
    (e : (ℚ ⊗[ℤ] M) ≃ₗ[ℚ] ℚ) (g : G) (r : ℤ)
    (hρ : ∀ x, ρ g x = r • x) : rationalActionCharacter ρ e g = (r : ℚ) := by
  have hf : integralLinear (ρ g) = r • (1 : Module.End ℤ M) := by
    apply LinearMap.ext
    intro x
    exact hρ x
  have hb : (r • (1 : Module.End ℤ M)).baseChange ℚ =
      r • (1 : Module.End ℚ (ℚ ⊗[ℤ] M)) := by
    exact ((Module.End.baseChangeHom ℤ ℚ M).map_zsmul r 1).trans
      (congrArg (fun f => r • f) (Module.End.baseChangeHom ℤ ℚ M).map_one)
  change e ((integralLinear (ρ g)).baseChange ℚ (e.symm 1)) = (r : ℚ)
  rw [hf, hb]
  change e (r • e.symm 1) = (r : ℚ)
  rw [map_zsmul, LinearEquiv.apply_symm_apply]
  simp only [zsmul_eq_mul, mul_one]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_TopOrientationAutomorphisms
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The top orientation character is preserved by automorphisms -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2100] Linear.homModule
variable {G : Type} [Group G]

theorem topOrientation_character_aut (R : Rep ℤ G) (eR : R.V ≃ₗ[ℤ] ℤ) (d : ℕ)
    (x : groupHomology R d) (hx : x ≠ 0)
    (hdetect : ∀ A : Rep ℤ G, Nonempty (A.V ≃ₗ[ℤ] ℤ) →
      (∃ y : groupHomology A d, y ≠ 0) → Nonempty (R ≅ A))
    (e : G ≃* G) :
    (rankOneCharacter R eR).comp e.toMonoidHom = rankOneCharacter R eR := by
  let A := Rep.res e.toMonoidHom R
  let E : groupHomology A d ≅ groupHomology R d :=
    groupHomology.mapIso (A := A) (B := R) e (LinearEquiv.refl ℤ R.V)
      (by intro g; rfl) d
  have hi : Function.Injective E.inv := (ModuleCat.mono_iff_injective _).mp inferInstance
  have hy : E.inv x ≠ 0 := fun h => hx (hi (h.trans (map_zero E.inv.hom).symm))
  obtain ⟨i⟩ := hdetect A ⟨eR⟩ ⟨E.inv x, hy⟩
  have h := rankOneCharacter_eq_of_iso R A eR eR i
  exact h.symm

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_OrientationHomologyAction
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Ambient conjugation on the local top orientation homology -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2100] Linear.homModule
variable {G : Type} [Group G] (N : Subgroup G) [N.Normal]

theorem orientation_action_invariant (R : Rep ℤ N) (eR : R.V ≃ₗ[ℤ] ℤ) (d : ℕ)
    (x : groupHomology R d) (hx : x ≠ 0)
    (hdetect : ∀ A : Rep ℤ N, Nonempty (A.V ≃ₗ[ℤ] ℤ) →
      (∃ y : groupHomology A d, y ≠ 0) → Nonempty (R ≅ A))
    (g : G) (a : N) : R.ρ (MulAut.conjNormal g a) = R.ρ a := by
  have hc := topOrientation_character_aut R eR d x hx hdetect (MulAut.conjNormal g)
  have he := congrArg (fun c : N →* ℤ => c a) hc
  apply LinearMap.ext
  intro v
  apply eR.injective
  calc
    eR (R.ρ (MulAut.conjNormal g a) v) =
        eR v * (rankOneCharacter R eR (MulAut.conjNormal g a)) :=
      rankOne_action_coordinate R eR _ v
    _ = eR v * (rankOneCharacter R eR a) := congrArg (fun z : ℤ => eR v * z) he
    _ = eR (R.ρ a v) := (rankOne_action_coordinate R eR a v).symm

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_OrientationInnerAction
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The restriction of the orientation-homology action to the kernel -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2100] Linear.homModule
variable {G : Type} [Group G]

theorem rankOne_action_zsmul (R : Rep ℤ G) (eR : R.V ≃ₗ[ℤ] ℤ) (g : G) (v : R) :
    R.ρ g v = rankOneCharacter R eR g • v := by
  apply eR.injective
  rw [rankOne_action_coordinate, map_zsmul]
  exact mul_comm _ _

variable (N : Subgroup G) [N.Normal] (R : Rep ℤ N)
  (hinv : ∀ (g : G) (a : N), R.ρ (MulAut.conjNormal g a) = R.ρ a)

theorem orientationHomology_inner_relation (eR : R.V ≃ₗ[ℤ] ℤ) (d : ℕ) (a : N) :
    rankOneCharacter R eR a • invariantConjugationHomologyMap N R hinv d (a : G) =
      𝟙 (groupHomology R d) := by
  rw [invariantConjugationHomologyMap, ← homologyMap_coefficient_zsmul]
  have h := groupHomology.map_congr
    (A := R) (B := R)
    (f := (MulAut.conjNormal (H := N) (a : G)).toMonoidHom)
    (g := (MulAut.conj a).toMonoidHom)
    (φ := rankOneCharacter R eR a • invariantConjugationCoefficient N R hinv (a : G))
    (ψ := innerHomologyCoefficient R a) (by ext n; rfl) (by
      apply DFunLike.ext
      intro v
      exact (rankOne_action_zsmul R eR a v).symm) d
  exact h.trans (innerHomologyMap_eq_id R a d)

theorem orientationHomology_inner_action (eR : R.V ≃ₗ[ℤ] ℤ) (d : ℕ) (a : N) :
    invariantConjugationHomologyMap N R hinv d (a : G) =
      rankOneCharacter R eR a⁻¹ • 𝟙 (groupHomology R d) := by
  have hmul : rankOneCharacter R eR a⁻¹ * rankOneCharacter R eR a = 1 := by
    rw [← map_mul, inv_mul_cancel, map_one]
  calc
    _ = (rankOneCharacter R eR a⁻¹ * rankOneCharacter R eR a) •
        invariantConjugationHomologyMap N R hinv d (a : G) := by rw [hmul, one_zsmul]
    _ = rankOneCharacter R eR a⁻¹ •
        (rankOneCharacter R eR a • invariantConjugationHomologyMap N R hinv d (a : G)) :=
      mul_zsmul _ _ _
    _ = _ := by rw [orientationHomology_inner_relation N R hinv eR d a]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_RationalCharacterCancellation
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Cancelling a rational character on its one-dimensional representation -/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
open scoped TensorProduct
variable {G M : Type} [Group G] [AddCommGroup M] [Module ℤ M]

theorem rationalActionCharacter_action (ρ : G →* AddMonoid.End M)
    (e : (ℚ ⊗[ℤ] M) ≃ₗ[ℚ] ℚ) (g : G) (z : ℚ ⊗[ℤ] M) :
    rationalizedAction ρ g z = rationalActionCharacter ρ e g • z := by
  apply e.injective
  let F := e.toLinearMap.comp ((rationalizedAction ρ g).comp e.symm.toLinearMap)
  have h := F.map_smul (e z) 1
  change e (rationalizedAction ρ g (e.symm ((e z) • (1 : ℚ)))) =
    (e z) • e (rationalizedAction ρ g (e.symm 1)) at h
  simp only [smul_eq_mul, mul_one, LinearEquiv.symm_apply_apply] at h
  rw [map_smul]
  exact h.trans (mul_comm _ _)

theorem rationalTensorAction_cancel (ρ : G →* AddMonoid.End M)
    (e : (ℚ ⊗[ℤ] M) ≃ₗ[ℚ] ℚ) (g : G) (r : ℚ)
    (hr : r * rationalActionCharacter ρ e g = 1) (z : ℚ ⊗[ℤ] M) :
    TensorProduct.map (rationalScalarMap r).hom (integralLinear (ρ g)) z = z := by
  have hm : TensorProduct.map (rationalScalarMap r).hom (integralLinear (ρ g)) z =
      r • rationalizedAction ρ g z := by
    induction z using OAI.tensorInductionOn with
    | tmul q x =>
      change (r * q) ⊗ₜ[ℤ] (ρ g x) = r • (q ⊗ₜ[ℤ] (ρ g x))
      exact TensorProduct.smul_tmul' r q (ρ g x)
    | add x y hx hy => simp only [map_add, smul_add, hx, hy]
  rw [hm, rationalActionCharacter_action, smul_smul, hr, one_smul]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_TrivialTensorChainNaturality
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Naturality of the trivial-coefficient tensor comparison -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory MonoidalCategory
open scoped TensorProduct
attribute [local instance 2000] Rep.hV2
variable {k G H : Type} [CommRing k] [Group G] [Group H]
  {V W : ModuleCat k} {A : Rep k G} {B : Rep k H}

theorem trivialTensorChainsIso_naturality [DecidableEq G] [DecidableEq H]
    (u : V ⟶ W) (f : G →* H) (φ : A ⟶ Rep.res f B) :
    (trivialTensorChainsIso V A).hom ≫
        groupHomology.chainsMap f (trivialTensorCoefficientMap u f φ) =
      (((tensorLeft V).mapHomologicalComplex (ComplexShape.down ℕ)).map
        (groupHomology.chainsMap f φ)) ≫
        (NatTrans.mapHomologicalComplex ((curriedTensor (ModuleCat k)).map u) (ComplexShape.down ℕ)).app
          (groupHomology.inhomogeneousChains B) ≫
        (trivialTensorChainsIso W B).hom := by
  apply HomologicalComplex.Hom.ext
  funext i
  apply ModuleCat.hom_ext
  apply TensorProduct.ext
  apply LinearMap.ext
  intro v
  apply Finsupp.lhom_ext'
  intro x
  apply LinearMap.ext
  intro a
  change (groupHomology.chainsMap f (trivialTensorCoefficientMap u f φ)).f i
      (TensorProduct.finsuppRight k k V A.V (Fin i → G) (v ⊗ₜ[k] Finsupp.single x a)) =
    TensorProduct.finsuppRight k k W B.V (Fin i → H)
      (u.hom v ⊗ₜ[k] (groupHomology.chainsMap f φ).f i (Finsupp.single x a))
  erw [TensorProduct.finsuppRight_tmul_single, groupHomology.chainsMap_f_single,
    groupHomology.chainsMap_f_single, TensorProduct.finsuppRight_tmul_single]
  rfl

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_RationalTensorHomology
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Rational tensoring commutes with the homology used here -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory MonoidalCategory

theorem rationalChainHomologyIso_naturality {C D : ChainComplex (ModuleCat ℤ) ℕ}
    (f : C ⟶ D) (n : ℕ) :
    HomologicalComplex.homologyMap
        (((tensorLeft (ModuleCat.of ℤ ℚ)).mapHomologicalComplex (ComplexShape.down ℕ)).map f) n ≫
        (rationalChainHomologyIso D n).hom =
      (rationalChainHomologyIso C n).hom ≫
        (tensorLeft (ModuleCat.of ℤ ℚ)).map (HomologicalComplex.homologyMap f n) := by
  exact ShortComplex.mapHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) n).map f)
    (tensorLeft (ModuleCat.of ℤ ℚ))

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_RationalTensorNaturality
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Naturality of rational coefficient homology -/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory MonoidalCategory
attribute [local instance 2000] Rep.hV2

theorem rationalChainHomologyIso_tensorMap (C : ChainComplex (ModuleCat ℤ) ℕ)
    (u : ModuleCat.of ℤ ℚ ⟶ ModuleCat.of ℤ ℚ) (n : ℕ) :
    HomologicalComplex.homologyMap
        ((NatTrans.mapHomologicalComplex ((curriedTensor (ModuleCat ℤ)).map u)
          (ComplexShape.down ℕ)).app C) n ≫ (rationalChainHomologyIso C n).hom =
      (rationalChainHomologyIso C n).hom ≫
        (((curriedTensor (ModuleCat ℤ)).map u).app (C.homology n)) := by
  have h := NatTrans.app_homology ((curriedTensor (ModuleCat ℤ)).map u) (C.sc n)
  change ((curriedTensor (ModuleCat ℤ)).map u).app (C.homology n) =
    (rationalChainHomologyIso C n).inv ≫
      HomologicalComplex.homologyMap
        ((NatTrans.mapHomologicalComplex ((curriedTensor (ModuleCat ℤ)).map u)
          (ComplexShape.down ℕ)).app C) n ≫ (rationalChainHomologyIso C n).hom at h
  rw [h]
  simp only [Iso.hom_inv_id_assoc]

theorem rationalTensorHomologyIso_naturality {G H : Type} [Group G] [Group H]
    [DecidableEq G] [DecidableEq H] (A : Rep ℤ G) (B : Rep ℤ H)
    (u : ModuleCat.of ℤ ℚ ⟶ ModuleCat.of ℤ ℚ) (f : G →* H)
    (φ : A ⟶ Rep.res f B) (n : ℕ) :
    groupHomology.map f (trivialTensorCoefficientMap u f φ) n ≫
        (rationalTensorHomologyIso B n).hom =
      (rationalTensorHomologyIso A n).hom ≫
        (tensorLeft (ModuleCat.of ℤ ℚ)).map (groupHomology.map f φ n) ≫
        (((curriedTensor (ModuleCat ℤ)).map u).app (groupHomology B n)) := by
  let T := (tensorLeft (ModuleCat.of ℤ ℚ)).mapHomologicalComplex (ComplexShape.down ℕ)
  let E := trivialTensorChainsIso (ModuleCat.of ℤ ℚ) A
  let F := trivialTensorChainsIso (ModuleCat.of ℤ ℚ) B
  let c := groupHomology.chainsMap f φ
  let v := (NatTrans.mapHomologicalComplex ((curriedTensor (ModuleCat ℤ)).map u)
    (ComplexShape.down ℕ)).app (groupHomology.inhomogeneousChains B)
  have h := trivialTensorChainsIso_naturality u f φ
  change E.hom ≫ groupHomology.chainsMap f (trivialTensorCoefficientMap u f φ) =
    T.map c ≫ v ≫ F.hom at h
  have hc : groupHomology.chainsMap f (trivialTensorCoefficientMap u f φ) ≫ F.inv =
      E.inv ≫ T.map c ≫ v := by
    rw [← cancel_epi E.hom]
    simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id,
      Category.comp_id] using congrArg (fun z => z ≫ F.inv) h
  change HomologicalComplex.homologyMap _ n ≫
      (HomologicalComplex.homologyMap F.inv n ≫
        (rationalChainHomologyIso (groupHomology.inhomogeneousChains B) n).hom) = _
  rw [← Category.assoc, ← HomologicalComplex.homologyMap_comp, hc,
    HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp]
  simp only [Category.assoc]
  rw [rationalChainHomologyIso_tensorMap,
    ← Category.assoc (HomologicalComplex.homologyMap (T.map c) n),
    rationalChainHomologyIso_naturality]
  rfl

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_NormalHomologyQuotient
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The quotient action on normal-subgroup homology -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G] (N : Subgroup G) [N.Normal] (A : Rep ℤ G)

theorem normalHomologyMap_subgroup (i : ℕ) (a : N) :
    normalHomologyMap ℤ N A i (a : G) = 𝟙 _ := by
  change groupHomology.map _ _ i = _
  have h := groupHomology.map_congr
    (A := Rep.res N.subtype A) (B := Rep.res N.subtype A)
    (f := (MulAut.conjNormal (H := N) (a : G)).toMonoidHom)
    (g := (MulAut.conj a).toMonoidHom)
    (φ := normalHomologyCoefficient ℤ N A (a : G))
    (ψ := innerHomologyCoefficient (Rep.res N.subtype A) a)
    (by ext n; rfl) (by rfl) i
  exact h.trans (innerHomologyMap_eq_id (Rep.res N.subtype A) a i)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_RationalScalarTwist
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Rational scalar twists of an ambient coefficient representation -/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory MonoidalCategory
open scoped TensorProduct
attribute [local instance 2000] Rep.hV2 Rep.instLinear ModuleCat.isModule
attribute [local instance 2100] Linear.homModule
variable {G : Type} [Group G]

variable (N : Subgroup G) [N.Normal] (A : Rep ℤ G)

theorem scalarTwist_conjugation_naturality (η : G →* ℚ)
    (hη : ∀ a : N, η (a : G) = 1) (d : ℕ) (g : G) :
    groupHomology.map (MonoidHom.id N) (rationalScalarTwistRestrictionIso N A η hη).hom d ≫
        normalHomologyMap ℤ N (rationalScalarTwist A η) d g =
      groupHomology.map (MulAut.conjNormal (H := N) g).toMonoidHom
          (trivialTensorCoefficientMap (rationalScalarMap (η g)) _
            (normalHomologyCoefficient ℤ N A g)) d ≫
        groupHomology.map (MonoidHom.id N) (rationalScalarTwistRestrictionIso N A η hη).hom d := by
  rw [normalHomologyMap, ← groupHomology.map_comp, ← groupHomology.map_comp]
  apply groupHomology.map_congr rfl
  apply TensorProduct.ext
  apply LinearMap.ext
  intro q
  apply LinearMap.ext
  intro v
  rfl

theorem scalarTwistHomology_trivial (η : G →* ℚ)
    (hη : ∀ a : N, η (a : G) = 1) (d : ℕ)
    (e : (ℚ ⊗[ℤ] (groupHomology (Rep.res N.subtype A) d)) ≃ₗ[ℚ] ℚ)
    (hc : ∀ g, η g * rationalActionCharacter (normalHomologyAddAction N A d) e g = 1)
    (g : G) : normalHomologyMap ℤ N (rationalScalarTwist A η) d g = 𝟙 _ := by
  classical
  let R := Rep.res N.subtype A
  let f := (MulAut.conjNormal (H := N) g).toMonoidHom
  let φ := normalHomologyCoefficient ℤ N A g
  let ψ := trivialTensorCoefficientMap (rationalScalarMap (η g)) f φ
  let I := rationalTensorHomologyIso R d
  have ht : (tensorLeft (ModuleCat.of ℤ ℚ)).map (groupHomology.map f φ d) ≫
      (((curriedTensor (ModuleCat ℤ)).map (rationalScalarMap (η g))).app
        (groupHomology R d)) = 𝟙 _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    have he : ((tensorLeft (ModuleCat.of ℤ ℚ)).map (groupHomology.map f φ d) ≫
        (((curriedTensor (ModuleCat ℤ)).map (rationalScalarMap (η g))).app
          (groupHomology R d))).hom z =
        TensorProduct.map (rationalScalarMap (η g)).hom
          (integralLinear ((normalHomologyAddAction N A d) g)) z := by
      induction z using OAI.tensorInductionOn with
      | tmul q x => rfl
      | add x y hx hy => simp only [map_add, hx, hy]
    exact he.trans (rationalTensorAction_cancel _ e g _ (hc g) z)
  have hm : groupHomology.map f ψ d = 𝟙 _ := by
    apply (cancel_mono I.hom).mp
    rw [rationalTensorHomologyIso_naturality R R (rationalScalarMap (η g)) f φ d,
      ht, Category.comp_id, Category.id_comp]
  let J := (groupHomology.functor ℤ N d).mapIso (rationalScalarTwistRestrictionIso N A η hη)
  apply (cancel_epi J.hom).mp
  change groupHomology.map (MonoidHom.id N) (rationalScalarTwistRestrictionIso N A η hη).hom d ≫
      normalHomologyMap ℤ N (rationalScalarTwist A η) d g = J.hom ≫ 𝟙 _
  rw [scalarTwist_conjugation_naturality N A η hη d g, hm]
  simp only [Category.id_comp, Category.comp_id]
  rfl

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_InvariantTopTwist
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Making rank-one top homology invariant by a scalar twist

The twist is trivial on the normal subgroup. Its character is obtained from
actual conjugation on rationalized homology, so no orientation extension is
assumed for an intermediate subgroup of a lattice quotient.
-/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
open scoped TensorProduct
attribute [local instance 2000] Rep.hV2 Rep.instLinear ModuleCat.isModule
attribute [local instance 2100] Linear.homModule
variable {G : Type} [Group G]

theorem exists_invariantTopTwist (N : Subgroup G) [N.Normal] (A : Rep ℤ G) (d : ℕ)
    (x : groupHomology (Rep.res N.subtype A) d) (hx : x ≠ 0)
    (htor : ∀ (a : ℤ) (y : groupHomology (Rep.res N.subtype A) d),
      a • y = 0 → a = 0 ∨ y = 0)
    (hcomm : ∀ y z : groupHomology (Rep.res N.subtype A) d, y ≠ 0 → z ≠ 0 →
      ∃ a b : ℤ, a ≠ 0 ∧ b ≠ 0 ∧ a • y = b • z) :
    ∃ η : G →* ℚ, (∀ a : N, η (a : G) = 1) ∧
      Nonempty ((groupHomology (Rep.res N.subtype (rationalScalarTwist A η)) d) ≃ₗ[ℤ] ℚ) ∧
      ∀ g, normalHomologyMap ℤ N (rationalScalarTwist A η) d g = 𝟙 _ := by
  classical
  let R := Rep.res N.subtype A
  let ρ := normalHomologyAddAction N A d
  obtain ⟨e⟩ := rational_rankOne_equiv htor hcomm x hx
  let c := rationalActionCharacter ρ e
  let η := inverseSourceRationalCharacter c
  have hη : ∀ a : N, η (a : G) = 1 := by
    intro a
    change c ((a : G)⁻¹) = 1
    apply rationalActionCharacter_of_zsmul ρ e _ (1 : ℤ)
    intro z
    change (normalHomologyMap ℤ N A d ((a⁻¹ : N) : G)).hom z = (1 : ℤ) • z
    rw [normalHomologyMap_subgroup]
    simp only [one_zsmul, ModuleCat.id_apply]
  have hc : ∀ g, η g * c g = 1 := by
    intro g
    change c g⁻¹ * c g = 1
    rw [← map_mul, inv_mul_cancel, map_one]
  refine ⟨η, hη, ?_, scalarTwistHomology_trivial N A η hη d e hc⟩
  let J := (groupHomology.functor ℤ N d).mapIso (rationalScalarTwistRestrictionIso N A η hη)
  let I := rationalTensorHomologyIso R d
  exact ⟨J.symm.toLinearEquiv.trans (I.toLinearEquiv.trans (e.restrictScalars ℤ))⟩

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

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_RationalLineProperties
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integral properties of a rational line -/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory

theorem rational_commensurable (x y : ℚ) (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ a b : ℤ, a ≠ 0 ∧ b ≠ 0 ∧ a • x = b • y := by
  have hden (q : ℚ) : (q.den : ℚ) * q = q.num := by
    calc
      _ = (q.den : ℚ) * ((q.num : ℚ) / (q.den : ℚ)) :=
        congrArg (fun z : ℚ => (q.den : ℚ) * z) q.num_div_den.symm
      _ = q.num := mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr q.den_nz)
  refine ⟨y.num * x.den, x.num * y.den,
    mul_ne_zero (Rat.num_ne_zero.mpr hy) (Int.natCast_ne_zero.mpr x.den_nz),
    mul_ne_zero (Rat.num_ne_zero.mpr hx) (Int.natCast_ne_zero.mpr y.den_nz), ?_⟩
  simp only [zsmul_eq_mul, Int.cast_mul, Int.cast_natCast]
  calc
    (y.num : ℚ) * x.den * x = y.num * ((x.den : ℚ) * x) := by ring
    _ = y.num * x.num := by rw [hden]
    _ = x.num * y.num := mul_comm _ _
    _ = x.num * ((y.den : ℚ) * y) := by rw [hden]
    _ = (x.num : ℚ) * y.den * y := by ring

theorem rationalLine_properties (M : ModuleCat ℤ) (e : M ≃ₗ[ℤ] ℚ) :
    (∃ x : M, x ≠ 0) ∧
    (∀ (a : ℤ) (x : M), a • x = 0 → a = 0 ∨ x = 0) ∧
    (∀ x y : M, x ≠ 0 → y ≠ 0 →
      ∃ a b : ℤ, a ≠ 0 ∧ b ≠ 0 ∧ a • x = b • y) := by
  refine ⟨⟨e.symm 1, ?_⟩, ?_, ?_⟩
  · intro h
    have he := congrArg e h
    exact one_ne_zero (by simpa only [LinearEquiv.apply_symm_apply, map_zero] using he)
  · intro a x h
    have he := congrArg e h
    simp only [map_zsmul, map_zero, zsmul_eq_mul] at he
    rcases mul_eq_zero.mp he with ha | hx
    · exact Or.inl (Int.cast_eq_zero.mp ha)
    · exact Or.inr (e.injective (hx.trans (map_zero e).symm))
  · intro x y hx hy
    have hx' : e x ≠ 0 := fun h => hx (e.injective (h.trans (map_zero e).symm))
    have hy' : e y ≠ 0 := fun h => hy (e.injective (h.trans (map_zero e).symm))
    obtain ⟨a, b, ha, hb, he⟩ := rational_commensurable (e x) (e y) hx' hy'
    exact ⟨a, b, ha, hb, e.injective (by simpa only [map_zsmul] using he)⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_IntegerExtensionHomologyBound
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A homology dimension bound through an infinite cyclic quotient -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits
variable {G : Type} [Group G]

theorem homology_bound_of_integer_quotient
    (q : G →* Multiplicative ℤ) (t : G) (ht : q t = Multiplicative.ofAdd 1)
    (d : ℕ)
    (hN : ∀ B : Rep ℤ q.ker, ∀ i, d < i → IsZero (groupHomology B i)) :
    ∀ A : Rep ℤ G, ∀ i, d + 1 < i → IsZero (groupHomology A i) := by
  classical
  let := integerQuotient_isCyclic q t ht
  let := integerQuotient_infinite q t ht
  intro A i hi
  cases i with
  | zero => omega
  | succ i =>
    let P := Rep.standardResolution ℤ q.ker
    let f := HomologicalComplex.homologyMap (integerExtensionTensorMap q t P A) i
    have hsource : IsZero
        (((quotientInducedResolution q.ker P).complex.coinvariantsTensorObj A).homology i) :=
      IsZero.of_iso (hN (Rep.res q.ker.subtype A) i (by omega))
        (inducedResolutionHomologyIso q.ker A P i)
    have hk : IsZero (kernel f) := IsZero.of_mono (kernel.ι f) hsource
    exact IsZero.of_iso hk (integerExtensionHomologyKernelIso q t ht P A i
      (hN (Rep.res q.ker.subtype A) (i + 1) (by omega)))

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_HomologyBoundTransport
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Transporting a homology bound through a group isomorphism -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2

theorem homology_bound_of_equiv {G J : Type} [Group G] [Group J]
    (e : G ≃* J) (d : ℕ)
    (hG : ∀ A : Rep ℤ G, ∀ i, d < i → IsZero (groupHomology A i)) :
    ∀ A : Rep ℤ J, ∀ i, d < i → IsZero (groupHomology A i) := by
  intro A i hi
  let E := groupHomology.mapIso (A := Rep.res e.toMonoidHom A) (B := A)
    e (LinearEquiv.refl ℤ A.V) (by intro g; rfl) i
  exact IsZero.of_iso (hG (Rep.res e.toMonoidHom A) i hi) E.symm

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_NestedNormalHomology
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Conjugation on homology under nested normal subgroups -/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G] (N K : Subgroup G) [N.Normal]
  (hNK : N ≤ K) (A : Rep ℤ G)

variable (M : Subgroup K) [M.Normal] (e : M ≃* N)
  (he : ∀ a : M, ((e a : N) : G) = ((a : K) : G))

theorem embeddedSubgroupHomologyIso_conjugation (d : ℕ) (g : K) :
    normalHomologyMap ℤ M (Rep.res K.subtype A) d g ≫
        (embeddedSubgroupHomologyIso N K A M e he d).hom =
      (embeddedSubgroupHomologyIso N K A M e he d).hom ≫
        normalHomologyMap ℤ N A d (g : G) := by
  change groupHomology.map _ _ d ≫ groupHomology.map _ _ d =
    groupHomology.map _ _ d ≫ groupHomology.map _ _ d
  rw [← groupHomology.map_comp, ← groupHomology.map_comp]
  apply groupHomology.map_congr
  · ext a
    change ((e (MulAut.conjNormal (H := M) g a) : N) : G) =
      (g : G) * ((e a : N) : G) * (g : G)⁻¹
    rw [he, he]
    rfl
  · rfl

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_NormalCyclicTopStep
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Raising invariant top homology along a normal cyclic step -/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear ModuleCat.isModule
variable {G : Type} [Group G]

theorem exists_normalCyclicTopStep (N K : Subgroup G) [N.Normal] [K.Normal]
    (hNK : N ≤ K) (q : K →* Multiplicative ℤ) (t : K)
    (ht : q t = Multiplicative.ofAdd 1) (hker : q.ker = N.subgroupOf K)
    (d : ℕ) (hbound : ∀ R : Rep ℤ N, ∀ j, d < j → IsZero (groupHomology R j))
    (A : Rep ℤ G) (eN : groupHomology (Rep.res N.subtype A) d ≃ₗ[ℤ] ℚ)
    (hA : ∀ g, normalHomologyMap ℤ N A d g = 𝟙 _) :
    ∃ B : Rep ℤ G,
      Nonempty (groupHomology (Rep.res K.subtype B) (d + 1) ≃ₗ[ℤ] ℚ) ∧
      ∀ g, normalHomologyMap ℤ K B (d + 1) g = 𝟙 _ := by
  let e : q.ker ≃* N := (MulEquiv.subgroupCongr hker).trans (Subgroup.subgroupOfEquivOfLe hNK)
  have he : ∀ a : q.ker, ((e a : N) : G) = ((a : K) : G) := by intro a; rfl
  let E := embeddedSubgroupHomologyIso N K A q.ker e he d
  have ha : normalHomologyMap ℤ q.ker (Rep.res K.subtype A) d t⁻¹ = 𝟙 _ := by
    apply (cancel_mono E.hom).mp
    have h := embeddedSubgroupHomologyIso_conjugation N K A q.ker e he d t⁻¹
    rw [hA] at h
    simpa only [Category.comp_id, Category.id_comp] using h
  have hb := homology_bound_of_equiv e.symm d hbound
  have hv := hb (Rep.res q.ker.subtype (Rep.res K.subtype A)) (d + 1) (by omega)
  let F := cyclicInvariantTopHomologyIso q t ht (Rep.res K.subtype A) d hv ha
  let eK : groupHomology (Rep.res K.subtype A) (d + 1) ≃ₗ[ℤ] ℚ :=
    F.toLinearEquiv.trans (E.toLinearEquiv.trans eN)
  obtain ⟨⟨x, hx⟩, htor, hcomm⟩ := rationalLine_properties _ eK
  obtain ⟨η, _, hB, hinv⟩ := exists_invariantTopTwist K A (d + 1) x hx htor hcomm
  exact ⟨rationalScalarTwist A η, hB, hinv⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_RationalOrientationConjugation
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Cancelling conjugation on rational top homology -/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory MonoidalCategory
open scoped TensorProduct
attribute [local instance 2000] Rep.hV2 Rep.instLinear ModuleCat.isModule
attribute [local instance 2100] Linear.homModule
variable {G : Type} [Group G] (N : Subgroup G) [N.Normal]

theorem rationalOrientation_conjugation_naturality (R : Rep ℤ N)
    (eR : R.V ≃ₗ[ℤ] ℤ) (χ : G →* ℚ)
    (hχ : ∀ a : N, χ (a : G) = (rankOneCharacter R eR a : ℚ))
    (hinv : ∀ (g : G) (a : N), R.ρ (MulAut.conjNormal g a) = R.ρ a)
    (d : ℕ) (g : G) :
    groupHomology.map (MonoidHom.id N) (rationalizedOrientationIso N R eR χ hχ).hom d ≫
        normalHomologyMap ℤ N (rationalCharacterRep χ) d g =
      groupHomology.map (MulAut.conjNormal (H := N) g).toMonoidHom
          (trivialTensorCoefficientMap (rationalScalarMap (χ g)) _
            (invariantConjugationCoefficient N R hinv g)) d ≫
        groupHomology.map (MonoidHom.id N) (rationalizedOrientationIso N R eR χ hχ).hom d := by
  rw [normalHomologyMap, ← groupHomology.map_comp, ← groupHomology.map_comp]
  apply groupHomology.map_congr rfl
  apply TensorProduct.ext
  apply LinearMap.ext
  intro q
  apply LinearMap.ext
  intro v
  change χ g * rationalizedOrientationEquiv R eR (q ⊗ₜ[ℤ] v) =
    rationalizedOrientationEquiv R eR ((χ g * q) ⊗ₜ[ℤ] v)
  rw [rationalizedOrientationEquiv_tmul, rationalizedOrientationEquiv_tmul]
  ring

theorem rationalOrientationHomology_trivial (R : Rep ℤ N)
    (eR : R.V ≃ₗ[ℤ] ℤ) (χ : G →* ℚ)
    (hχ : ∀ a : N, χ (a : G) = (rankOneCharacter R eR a : ℚ))
    (hinv : ∀ (g : G) (a : N), R.ρ (MulAut.conjNormal g a) = R.ρ a)
    (d : ℕ) (e : (ℚ ⊗[ℤ] (groupHomology R d)) ≃ₗ[ℚ] ℚ)
    (hc : ∀ g, χ g * rationalActionCharacter
      (invariantConjugationHomologyAction N R hinv d) e g = 1) (g : G) :
    normalHomologyMap ℤ N (rationalCharacterRep χ) d g = 𝟙 _ := by
  classical
  let f := (MulAut.conjNormal (H := N) g).toMonoidHom
  let φ := invariantConjugationCoefficient N R hinv g
  let ψ := trivialTensorCoefficientMap (rationalScalarMap (χ g)) f φ
  let I := rationalTensorHomologyIso R d
  have ht : (tensorLeft (ModuleCat.of ℤ ℚ)).map (groupHomology.map f φ d) ≫
      (((curriedTensor (ModuleCat ℤ)).map (rationalScalarMap (χ g))).app
        (groupHomology R d)) = 𝟙 _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    have he : ((tensorLeft (ModuleCat.of ℤ ℚ)).map (groupHomology.map f φ d) ≫
        (((curriedTensor (ModuleCat ℤ)).map (rationalScalarMap (χ g))).app
          (groupHomology R d))).hom z =
        TensorProduct.map (rationalScalarMap (χ g)).hom
          (integralLinear ((invariantConjugationHomologyAction N R hinv d) g)) z := by
      induction z using OAI.tensorInductionOn with
      | tmul q x => rfl
      | add x y hx hy =>
        simp only [map_add, hx, hy]
    exact he.trans (rationalTensorAction_cancel _ e g _ (hc g) z)
  have hm : groupHomology.map f ψ d = 𝟙 _ := by
    apply (cancel_mono I.hom).mp
    rw [rationalTensorHomologyIso_naturality R R (rationalScalarMap (χ g)) f φ d,
      ht, Category.comp_id, Category.id_comp]
  let J := (groupHomology.functor ℤ N d).mapIso (rationalizedOrientationIso N R eR χ hχ)
  apply (cancel_epi J.hom).mp
  change groupHomology.map (MonoidHom.id N) (rationalizedOrientationIso N R eR χ hχ).hom d ≫
      normalHomologyMap ℤ N (rationalCharacterRep χ) d g = J.hom ≫ 𝟙 _
  rw [rationalOrientation_conjugation_naturality N R eR χ hχ hinv d g, hm]
  simp only [Category.id_comp, Category.comp_id]
  rfl

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_RationalInvariantTopClass
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # An ambient rational twist with invariant nonzero kernel top homology -/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
open scoped TensorProduct
attribute [local instance 2000] Rep.hV2 Rep.instLinear ModuleCat.isModule
attribute [local instance 2100] Linear.homModule
variable {G : Type} [Group G]

theorem rationalOrientation_topLine (N : Subgroup G) (R : Rep ℤ N)
    (eR : R.V ≃ₗ[ℤ] ℤ) (d : ℕ) (χ : G →* ℚ)
    (hχ : ∀ a : N, χ (a : G) = (rankOneCharacter R eR a : ℚ))
    (x : groupHomology R d) (hx : x ≠ 0)
    (htor : ∀ (a : ℤ) (y : groupHomology R d), a • y = 0 → a = 0 ∨ y = 0)
    (hcomm : ∀ y z : groupHomology R d, y ≠ 0 → z ≠ 0 →
      ∃ a b : ℤ, a ≠ 0 ∧ b ≠ 0 ∧ a • y = b • z) :
    Nonempty (groupHomology (Rep.res N.subtype (rationalCharacterRep χ)) d ≃ₗ[ℤ] ℚ) := by
  classical
  obtain ⟨e⟩ := rational_rankOne_equiv htor hcomm x hx
  let J := (groupHomology.functor ℤ N d).mapIso (rationalizedOrientationIso N R eR χ hχ)
  let I := rationalTensorHomologyIso R d
  exact ⟨J.symm.toLinearEquiv.trans (I.toLinearEquiv.trans (e.restrictScalars ℤ))⟩

theorem exists_rationalInvariantTopClass (N : Subgroup G) [N.Normal]
    (R : Rep ℤ N) (eR : R.V ≃ₗ[ℤ] ℤ) (d : ℕ)
    (x : groupHomology R d) (hx : x ≠ 0)
    (htor : ∀ (a : ℤ) (y : groupHomology R d), a • y = 0 → a = 0 ∨ y = 0)
    (hcomm : ∀ y z : groupHomology R d, y ≠ 0 → z ≠ 0 →
      ∃ a b : ℤ, a ≠ 0 ∧ b ≠ 0 ∧ a • y = b • z)
    (hdetect : ∀ A : Rep ℤ N, Nonempty (A.V ≃ₗ[ℤ] ℤ) →
      (∃ y : groupHomology A d, y ≠ 0) → Nonempty (R ≅ A)) :
    ∃ χ : G →* ℚ, (∀ g, χ g ≠ 0) ∧
      (∀ a : N, χ (a : G) = (rankOneCharacter R eR a : ℚ)) ∧
      (∃ y : groupHomology (Rep.res N.subtype (rationalCharacterRep χ)) d, y ≠ 0) ∧
      ∀ g, normalHomologyMap ℤ N (rationalCharacterRep χ) d g = 𝟙 _ := by
  classical
  let hinv := orientation_action_invariant N R eR d x hx hdetect
  let ρ := invariantConjugationHomologyAction N R hinv d
  obtain ⟨e⟩ := rational_rankOne_equiv htor hcomm x hx
  let c := rationalActionCharacter ρ e
  let χ := inverseSourceRationalCharacter c
  have hχ : ∀ a : N, χ (a : G) = (rankOneCharacter R eR a : ℚ) := by
    intro a
    change c ((a : G)⁻¹) = _
    have hρ : ∀ z, ρ ((a : G)⁻¹) z = rankOneCharacter R eR a • z := by
      intro z
      have h := orientationHomology_inner_action N R hinv eR d a⁻¹
      rw [inv_inv] at h
      change (invariantConjugationHomologyMap N R hinv d ((a : G)⁻¹)).hom z = _
      calc
        _ = (rankOneCharacter R eR a • 𝟙 (groupHomology R d)).hom z :=
          congrArg (fun f : groupHomology R d ⟶ groupHomology R d => f.hom z) h
        _ = rankOneCharacter R eR a • z := rfl
    exact rationalActionCharacter_of_zsmul ρ e _ _ hρ
  have hc : ∀ g, χ g * c g = 1 := by
    intro g
    change c g⁻¹ * c g = 1
    rw [← map_mul, inv_mul_cancel, map_one]
  refine ⟨χ, fun g => rationalActionCharacter_ne_zero ρ e g⁻¹, hχ, ?_, ?_⟩
  · let I := rationalTensorHomologyIso R d
    let J := (groupHomology.functor ℤ N d).mapIso (rationalizedOrientationIso N R eR χ hχ)
    refine ⟨J.hom (I.inv (e.symm 1)), ?_⟩
    intro hz
    have hJ : Function.Injective J.hom := (ModuleCat.mono_iff_injective _).mp inferInstance
    have hI : Function.Injective I.inv := (ModuleCat.mono_iff_injective _).mp inferInstance
    have hzero : e.symm 1 = 0 := hI (hJ (hz.trans (map_zero J.hom.hom).symm) |>.trans
      (map_zero I.inv.hom).symm)
    have h := congrArg e hzero
    exact one_ne_zero (by simpa only [LinearEquiv.apply_symm_apply, map_zero] using h)
  · intro g
    exact rationalOrientationHomology_trivial N R eR χ hχ hinv d e hc g

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_RegularCoefficientNaturality
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Naturality of regular evaluation in the coefficient representation -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits
open scoped MonoidAlgebra
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2100] Linear.homModule
variable {G : Type} [Group G] {A B : Rep ℤ G}

theorem regularCoefficientAction_naturality (f : A ⟶ B) (q : ℤ[G]) (a : A) :
    regularCoefficientAction B q (f.hom a) = f.hom (regularCoefficientAction A q a) := by
  induction q using MonoidAlgebra.induction_on with
  | of g =>
    simp only [MonoidAlgebra.of_apply, regularCoefficientAction_single, one_smul]
    exact (Rep.hom_comm_apply f g⁻¹ a).symm
  | add q r hq hr => simp only [map_add, LinearMap.add_apply, hq, hr]
  | smul r q hq =>
    simp only [map_smul]
    change r • regularCoefficientAction B q (f.hom a) =
      f.hom (r • regularCoefficientAction A q a)
    rw [hq]
    exact (map_zsmul f.hom r (regularCoefficientAction A q a)).symm

theorem regularDualEvaluation_coefficient (P : Rep ℤ G) (f : A ⟶ B) (a : A) (p : P) :
    regularDualEvaluation P B (f.hom a) p = regularDualEvaluation P A a p ≫ f := by
  apply Rep.hom_ext
  apply DFunLike.ext
  intro q
  exact regularCoefficientAction_naturality f (q.hom p) a

theorem regularCoinvariantEvaluation_coefficient (P : Rep ℤ G) (f : A ⟶ B)
    (x : ((Rep.coinvariantsTensor ℤ G).obj A).obj P) :
    regularCoinvariantEvaluation P B (((Rep.coinvariantsTensor ℤ G).map f).app P x) =
      regularCoinvariantEvaluation P A x ≫ f := by
  induction x using Representation.Coinvariants.induction_on with
  | h x =>
    induction x using OAI.tensorInductionOn with
    | tmul a p => exact regularDualEvaluation_coefficient P f a p
    | add x y hx hy => simp only [map_add, hx, hy, Preadditive.add_comp]

theorem regularKernelCokernelEquiv_π {P Q : Rep ℤ G} (d : P ⟶ Q) (A : Rep ℤ G)
    [Projective P] [Projective Q]
    (hP : IntegralRepresentationFinite G P) (hQ : IntegralRepresentationFinite G Q)
    (x : LinearMap.ker (((Rep.coinvariantsTensor ℤ G).obj A).map d).hom) :
    cokernel.π (regularDualMap d) ≫ regularKernelCokernelEquiv d A hP hQ x =
      regularCoinvariantEvaluation P A x.val := by
  exact cokernel.π_desc _ _ _

theorem regularKernelCokernelEquiv_coefficient {P Q : Rep ℤ G} (d : P ⟶ Q)
    [Projective P] [Projective Q]
    (hP : IntegralRepresentationFinite G P) (hQ : IntegralRepresentationFinite G Q)
    (f : A ⟶ B)
    (x : LinearMap.ker (((Rep.coinvariantsTensor ℤ G).obj A).map d).hom)
    (y : LinearMap.ker (((Rep.coinvariantsTensor ℤ G).obj B).map d).hom)
    (hxy : y.val = ((Rep.coinvariantsTensor ℤ G).map f).app P x.val) :
    regularKernelCokernelEquiv d B hP hQ y = regularKernelCokernelEquiv d A hP hQ x ≫ f := by
  apply (cancel_epi (cokernel.π (regularDualMap d))).mp
  rw [regularKernelCokernelEquiv_π, ← Category.assoc, regularKernelCokernelEquiv_π,
    hxy, regularCoinvariantEvaluation_coefficient]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_SolvableFiniteExtension
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Solvable finite extensions of polycyclic groups

Take the normal core of a polycyclic finite-index subgroup. Its quotient is
finite and solvable, and thus has a cyclic series. The extension construction
then gives a cyclic series for the original group.
-/

namespace PolycyclicRecognition

variable {G : Type} [Group G]

theorem isPolycyclic_of_finite_solvable [Finite G] [Group.IsSolvable G] : IsPolycyclic G :=
  isPolycyclic_of_solvable_subgroups_fg (fun _ => inferInstance)

theorem IsVirtuallyPolycyclic.polycyclic_of_solvable [Group.IsSolvable G]
    (hG : IsVirtuallyPolycyclic G) : IsPolycyclic G := by
  obtain ⟨H, hindex, hH⟩ := hG
  let := hindex
  let N := H.normalCore
  have hN : IsPolycyclic N := hH.of_injective
    (Subgroup.inclusion H.normalCore_le) (Subgroup.inclusion_injective _)
  exact isPolycyclic_of_normal_subgroup N hN isPolycyclic_of_finite_solvable

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_SubgroupShapiro
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The Shapiro comparison associated to subgroup inclusion -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory HomologicalComplex Rep
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2100] Linear.homModule
variable {G : Type} [Group G] (H : Subgroup G)

theorem subgroupShapiro_return_chain [DecidableEq G] [DecidableEq H] (A : Rep ℤ G) :
    (groupHomology.inhomogeneousChainsIso (Rep.res H.subtype A)).hom ≫
      (((Rep.coinvariantsTensor ℤ H).obj (Rep.res H.subtype A)).mapHomologicalComplex _).map
        (subgroupBarResolutionMap H) ≫
      (groupHomology.coinvariantsTensorResProjectiveResolutionIso H
        (Rep.res H.subtype A) (Rep.barResolution ℤ G)).hom ≫
      coefficientTensorChainMap (Rep.barComplex ℤ G) (finiteIndexReturn H A) =
    subgroupBarInclusion H A ≫ (groupHomology.inhomogeneousChainsIso A).hom := by
  apply HomologicalComplex.Hom.ext
  funext i
  apply ModuleCat.hom_ext
  apply Finsupp.lhom_ext'
  intro x
  apply LinearMap.ext
  intro a
  change (coefficientTensorChainMap (Rep.barComplex ℤ G) (finiteIndexReturn H A)).f i
      ((groupHomology.coinvariantsTensorResProjectiveResolutionIso H
        (Rep.res H.subtype A) (Rep.barResolution ℤ G)).hom.f i
        ((((Rep.coinvariantsTensor ℤ H).obj (Rep.res H.subtype A)).map
          (subgroupFreeInclusion H i))
          (Rep.finsuppToCoinvariantsTensorFree (Rep.res H.subtype A) (Fin i → H)
            (Finsupp.single x a)))) =
    (groupHomology.inhomogeneousChainsIso A).hom.f i
      ((subgroupBarInclusion H A).f i (Finsupp.single x a))
  rw [Rep.finsuppToCoinvariantsTensorFree_single]
  change (coefficientTensorChainMap (Rep.barComplex ℤ G) (finiteIndexReturn H A)).f i
    (Rep.coinvariantsTensorIndInv H.subtype (Rep.res H.subtype A) (Rep.free ℤ G (Fin i → G))
      (Rep.coinvariantsTensorMk (Rep.res H.subtype A)
        (Rep.res H.subtype (Rep.free ℤ G (Fin i → G))) a
        ((subgroupFreeInclusion H i).hom (Finsupp.single x (MonoidAlgebra.single 1 1))))) = _
  rw [subgroupFreeInclusion_single, Subgroup.coe_one]
  have hi : Rep.coinvariantsTensorIndInv H.subtype (Rep.res H.subtype A)
      (Rep.free ℤ G (Fin i → G))
      (Rep.coinvariantsTensorMk (Rep.res H.subtype A)
        (Rep.res H.subtype (Rep.free ℤ G (Fin i → G))) a
        (Finsupp.single (H.subtype ∘ x) (MonoidAlgebra.single 1 1))) =
    Rep.coinvariantsTensorMk (Rep.ind H.subtype (Rep.res H.subtype A))
      (Rep.free ℤ G (Fin i → G))
      (Representation.IndV.mk H.subtype (Rep.res H.subtype A).ρ 1 a)
      (Finsupp.single (H.subtype ∘ x) (MonoidAlgebra.single 1 1)) :=
    Rep.coinvariantsTensorIndInv_mk_tmul_indMk H.subtype a _
  rw [hi]
  change Rep.coinvariantsTensorMk A (Rep.free ℤ G (Fin i → G))
      ((finiteIndexReturn H A).hom (Representation.IndV.mk H.subtype
        (Rep.res H.subtype A).ρ 1 a))
      (Finsupp.single (H.subtype ∘ x) (MonoidAlgebra.single 1 1)) = _
  rw [finiteIndexReturn_mk, inv_one, map_one]
  change Rep.coinvariantsTensorMk A (Rep.free ℤ G (Fin i → G)) a
      (Finsupp.single (H.subtype ∘ x) (MonoidAlgebra.single 1 1)) =
    Rep.finsuppToCoinvariantsTensorFree A (Fin i → G)
      ((subgroupBarInclusion H A).f i (Finsupp.single x a))
  rw [show (subgroupBarInclusion H A).f i (Finsupp.single x a) =
    Finsupp.single (H.subtype ∘ x) a from groupHomology.chainsMap_f_single _ _ _ _ _]
  rw [Rep.finsuppToCoinvariantsTensorFree_single]
  rfl

theorem subgroup_comparison_homology [DecidableEq G] [DecidableEq H]
    (A : Rep ℤ H) (n : ℕ) :
    (coefficientNaturalHomologyIso
      ((Rep.resFunctor H.subtype).mapProjectiveResolution (Rep.barResolution ℤ G)) A n).hom =
    homologyMap (groupHomology.inhomogeneousChainsIso A).hom n ≫
      homologyMap ((((Rep.coinvariantsTensor ℤ H).obj A).mapHomologicalComplex _).map
        (subgroupBarResolutionMap H)) n := by
  let Q : ProjectiveResolution (Rep.trivial ℤ H ℤ) :=
    (Rep.resFunctor H.subtype).mapProjectiveResolution (Rep.barResolution ℤ G)
  let u : Rep.barComplex ℤ H ⟶ Q.complex := subgroupBarResolutionMap H
  let v : Rep.barComplex ℤ H ⟶ Q.complex :=
    (ProjectiveResolution.homotopyEquiv (Rep.barResolution ℤ H) Q).hom
  have hv : Homotopy u v := subgroupBarResolutionHomotopy H
  have h := (((Rep.coinvariantsTensor ℤ H).obj A).mapHomotopy hv).homologyMap_eq n
  change homologyMap (groupHomology.inhomogeneousChainsIso A).hom n ≫
      homologyMap ((((Rep.coinvariantsTensor ℤ H).obj A).mapHomologicalComplex _).map
        v) n = homologyMap (groupHomology.inhomogeneousChainsIso A).hom n ≫
      homologyMap ((((Rep.coinvariantsTensor ℤ H).obj A).mapHomologicalComplex _).map u) n
  exact congrArg (fun f => homologyMap (groupHomology.inhomogeneousChainsIso A).hom n ≫ f) h.symm

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_SubgroupShapiroReturn
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Subgroup inclusion is the Shapiro coefficient return -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory HomologicalComplex
variable {G : Type} [Group G]

theorem subgroupShapiro_return (H : Subgroup G) (A : Rep ℤ G) (n : ℕ) :
    (subgroupShapiroIso H (Rep.res H.subtype A) n).hom ≫
      groupHomology.map (MonoidHom.id G) (finiteIndexReturn H A) n =
        subgroupHomologyInclusion H A n := by
  classical
  let Q : ProjectiveResolution (Rep.trivial ℤ H ℤ) :=
    (Rep.resFunctor H.subtype).mapProjectiveResolution (Rep.barResolution ℤ G)
  let u : Rep.barComplex ℤ H ⟶ Q.complex := subgroupBarResolutionMap H
  let F := (Rep.coinvariantsTensor ℤ H).obj (Rep.res H.subtype A)
  let s : Q.complex.coinvariantsTensorObj (Rep.res H.subtype A) ≅
      (Rep.barComplex ℤ G).coinvariantsTensorObj (Rep.ind H.subtype (Rep.res H.subtype A)) :=
    groupHomology.coinvariantsTensorResProjectiveResolutionIso H
      (Rep.res H.subtype A) (Rep.barResolution ℤ G)
  let a := groupHomology.inhomogeneousChainsIso (Rep.res H.subtype A)
  let b := groupHomology.inhomogeneousChainsIso (Rep.ind H.subtype (Rep.res H.subtype A))
  let e := groupHomology.inhomogeneousChainsIso A
  apply (cancel_mono (homologyMap e.hom n)).mp
  have hn := congrArg (fun f => homologyMap f n)
    (inhomogeneousChainsIso_coefficient (finiteIndexReturn H A))
  simp only [homologyMap_comp] at hn
  have hc := congrArg (fun f => homologyMap f n) (subgroupShapiro_return_chain H A)
  change homologyMap (a.hom ≫ (F.mapHomologicalComplex _).map u ≫ s.hom ≫
    coefficientTensorChainMap (Rep.barComplex ℤ G) (finiteIndexReturn H A)) n =
      homologyMap (subgroupBarInclusion H A ≫ e.hom) n at hc
  simp only [homologyMap_comp] at hc
  change (((coefficientNaturalHomologyIso Q (Rep.res H.subtype A) n).hom ≫
      homologyMap s.hom n) ≫ homologyMap b.inv n) ≫
      homologyMap (groupHomology.chainsMap (MonoidHom.id G) (finiteIndexReturn H A)) n ≫
      homologyMap e.hom n = homologyMap (subgroupBarInclusion H A) n ≫ homologyMap e.hom n
  rw [subgroup_comparison_homology]
  simp only [Category.assoc]
  rw [hn]
  have hb : homologyMap b.inv n ≫ homologyMap b.hom n = 𝟙 _ := by
    rw [← homologyMap_comp, b.inv_hom_id, homologyMap_id]
  erw [← Category.assoc (homologyMap b.inv n), hb, Category.id_comp]
  exact hc

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_TopHomologyKernelNaturality
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Naturality of top homology as a kernel -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory HomologicalComplex
attribute [local instance 2000] ModuleCat.isModule

theorem topHomologyKernelEquiv_π (C : ChainComplex (ModuleCat ℤ) ℕ) (n : ℕ)
    (h : C.d (n + 1) n = 0) (z : C.cycles n) :
    (topHomologyKernelEquiv C n h (C.homologyπ n z)).val = C.iCycles n z := by
  change ((C.homologyπ n ≫
      (C.isoHomologyπ (n + 1) n (ChainComplex.prev ℕ n) h).inv ≫
      (C.cyclesIsoSc' (n + 1) n (n - 1) (ChainComplex.prev ℕ n)
        (by cases n <;> simp)).hom ≫
      (C.sc' (n + 1) n (n - 1)).moduleCatCyclesIso.hom ≫
      (C.sc' (n + 1) n (n - 1)).moduleCatLeftHomologyData.i) z) = C.iCycles n z
  simp only [ShortComplex.moduleCatCyclesIso_hom_i, cyclesIsoSc'_hom_iCycles]
  change (C.homologyπ n ≫
    (C.isoHomologyπ (n + 1) n (ChainComplex.prev ℕ n) h).inv ≫ C.iCycles n) z =
      C.iCycles n z
  simpa only [Category.assoc, Category.id_comp] using
    congrArg (fun f : C.cycles n ⟶ C.cycles n => (f ≫ C.iCycles n) z)
      (C.isoHomologyπ_hom_inv_id (n + 1) n (ChainComplex.prev ℕ n) h)

theorem topHomologyKernelEquiv_naturality
    {C D : ChainComplex (ModuleCat ℤ) ℕ} (f : C ⟶ D) (n : ℕ)
    (hC : C.d (n + 1) n = 0) (hD : D.d (n + 1) n = 0) (x : C.homology n) :
    (topHomologyKernelEquiv D n hD (HomologicalComplex.homologyMap f n x)).val =
      f.f n (topHomologyKernelEquiv C n hC x).val := by
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective (C.homologyπ n)).mp inferInstance x
  have he := congrArg (fun k => k z) (HomologicalComplex.homologyπ_naturality f n)
  change HomologicalComplex.homologyMap f n (C.homologyπ n z) =
    D.homologyπ n (HomologicalComplex.cyclesMap f n z) at he
  rw [he, topHomologyKernelEquiv_π, topHomologyKernelEquiv_π]
  exact congrArg (fun k => k z) (HomologicalComplex.cyclesMap_i f n)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_TopHomologyNaturality
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.cyclicTopHomologyInjection_mono _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Coefficient naturality of top-dimensional duality

Use one fixed resolution comparison for all coefficients. This records the
naturality needed to turn a coefficient trace into a top-homology trace.
-/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits HomologicalComplex
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2100] Linear.homModule
variable {G : Type} [Group G]

theorem naturalTopHomologyEquiv_naturality [DecidableEq G]
    (P : ProjectiveResolution (trivialIntegral G)) (n : ℕ)
    (hfin : ∀ i, IntegralRepresentationFinite G (P.complex.X i))
    (hbound : IsZero (P.complex.X (n + 1))) {A B : Rep ℤ G}
    (f : A ⟶ B) (x : groupHomology A n) :
    naturalTopHomologyEquiv P n hfin hbound B
        (groupHomology.map (MonoidHom.id G) f n x) =
      naturalTopHomologyEquiv P n hfin hbound A x ≫ f := by
  apply regularKernelCokernelEquiv_coefficient
  have he := congrArg (fun k => k x) (coefficientNaturalHomologyIso_naturality P f n)
  change (coefficientNaturalHomologyIso P B n).hom
      (groupHomology.map (MonoidHom.id G) f n x) =
    homologyMap (coefficientTensorChainMap P.complex f) n
      ((coefficientNaturalHomologyIso P A n).hom x) at he
  change (topHomologyKernelEquiv (P.complex.coinvariantsTensorObj B) n
      (tensor_top_d_zero P n hbound B)
      ((coefficientNaturalHomologyIso P B n).hom
        (groupHomology.map (MonoidHom.id G) f n x))).val =
    (coefficientTensorChainMap P.complex f).f n
      (topHomologyKernelEquiv (P.complex.coinvariantsTensorObj A) n
        (tensor_top_d_zero P n hbound A)
        ((coefficientNaturalHomologyIso P A n).hom x)).val
  rw [he]
  exact topHomologyKernelEquiv_naturality (coefficientTensorChainMap P.complex f) n
    (tensor_top_d_zero P n hbound A) (tensor_top_d_zero P n hbound B)
    ((coefficientNaturalHomologyIso P A n).hom x)

theorem IsIntegralPoincareDualityGroup.topHomology_natural {n : ℕ}
    (hG : IsIntegralPoincareDualityGroup G n) :
    ∃ (D : Rep ℤ G) (_ : Nonempty (D.V ≃ₗ[ℤ] ℤ))
      (e : ∀ A : Rep ℤ G, groupHomology A n ≃ₗ[ℤ] (D ⟶ A)),
      ∀ (A B : Rep ℤ G) (f : A ⟶ B) (x : groupHomology A n),
        e B (groupHomology.map (MonoidHom.id G) f n x) = e A x ≫ f := by
  classical
  obtain ⟨P, _, hfin, _⟩ := hG.1
  let := hG.cohomologicalDimension
  let Q := finiteProjectiveResolution P n
  have hQfin : ∀ i, IntegralRepresentationFinite G (Q.complex.X i) :=
    finiteTruncation_finite P n (fun i _ => hfin i)
  have hQbound : IsZero (Q.complex.X (n + 1)) :=
    finiteTruncation_isZero P n (n + 1) (by omega)
  let D := cokernel (regularDualMap (Q.complex.d n (n - 1)))
  obtain ⟨e⟩ := hG.2.2
  refine ⟨D, ⟨((regularDualCokernelCohomologyIso Q n hQbound).trans e).toLinearEquiv⟩,
    naturalTopHomologyEquiv Q n hQfin hQbound, ?_⟩
  exact fun A B f x => naturalTopHomologyEquiv_naturality Q n hQfin hQbound f x

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_NaturalOrientationTransport
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Naturality for a prescribed top-homology orientation -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2100] Linear.homModule
variable {G : Type} [Group G]

theorem topHomology_orientation_unique (n : ℕ) (D E : Rep ℤ G)
    (eD : D.V ≃ₗ[ℤ] ℤ) (eE : E.V ≃ₗ[ℤ] ℤ)
    (hD : ∀ A : Rep ℤ G, Nonempty (groupHomology A n ≃ₗ[ℤ] (D ⟶ A)))
    (hE : ∀ A : Rep ℤ G, Nonempty (groupHomology A n ≃ₗ[ℤ] (E ⟶ A))) :
    Nonempty (D ≅ E) := by
  obtain ⟨d⟩ := hD E
  obtain ⟨e⟩ := hE E
  let b := d.symm.trans e
  have hid : (𝟙 E : E ⟶ E) ≠ 0 := by
    intro h
    have hv := congrArg (fun f : E ⟶ E => eE (f.hom (eE.symm 1))) h
    simp at hv
  have hf : b.symm (𝟙 E) ≠ 0 := by
    intro h
    apply hid
    have he := congrArg b h
    simpa using he
  exact rankOne_rep_iso_of_nonzero D E eD eE (b.symm (𝟙 E)) hf

theorem topHomology_natural_prescribed {n : ℕ}
    (hG : IsIntegralPoincareDualityGroup G n) (D : Rep ℤ G)
    (eD : D.V ≃ₗ[ℤ] ℤ)
    (hD : ∀ A : Rep ℤ G, Nonempty (groupHomology A n ≃ₗ[ℤ] (D ⟶ A))) :
    ∃ e : ∀ A : Rep ℤ G, groupHomology A n ≃ₗ[ℤ] (D ⟶ A),
      ∀ (A B : Rep ℤ G) (f : A ⟶ B) (x : groupHomology A n),
        e B (groupHomology.map (MonoidHom.id G) f n x) = e A x ≫ f := by
  obtain ⟨E, ⟨eE⟩, e, he⟩ := hG.topHomology_natural
  obtain ⟨j⟩ := topHomology_orientation_unique n D E eD eE hD (fun A => ⟨e A⟩)
  refine ⟨fun A => (e A).trans (Linear.homCongr ℤ j.symm (Iso.refl A)), ?_⟩
  intro A B f x
  change (j.hom ≫ e B (groupHomology.map (MonoidHom.id G) f n x)) ≫ 𝟙 B =
    ((j.hom ≫ e A x) ≫ 𝟙 A) ≫ f
  rw [he, Category.comp_id, Category.comp_id, Category.assoc]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_CyclicTopHomologyInjection
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The top homology injection for an infinite cyclic quotient -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] ModuleCat.isModule Rep.hV2

theorem integralRankOne_properties_of_injective {M N : ModuleCat ℤ} (f : M ⟶ N)
    (hf : Function.Injective f)
    (htorsion : ∀ (z : ℤ) (x : N), z • x = 0 → z = 0 ∨ x = 0)
    (hcomm : ∀ x y : N, x ≠ 0 → y ≠ 0 →
      ∃ a b : ℤ, a ≠ 0 ∧ b ≠ 0 ∧ a • x = b • y) :
    (∀ (z : ℤ) (x : M), z • x = 0 → z = 0 ∨ x = 0) ∧
    (∀ x y : M, x ≠ 0 → y ≠ 0 →
      ∃ a b : ℤ, a ≠ 0 ∧ b ≠ 0 ∧ a • x = b • y) := by
  constructor
  · intro z x hx
    have h := congrArg (fun x => f x) hx
    simp only [map_zsmul, map_zero] at h
    rcases htorsion z (f x) h with hz | hx
    · exact Or.inl hz
    · exact Or.inr (hf (hx.trans (map_zero f.hom).symm))
  · intro x y hx hy
    have hx' : f x ≠ 0 := fun h => hx (hf (h.trans (map_zero f.hom).symm))
    have hy' : f y ≠ 0 := fun h => hy (hf (h.trans (map_zero f.hom).symm))
    obtain ⟨a, b, ha, hb, h⟩ := hcomm _ _ hx' hy'
    refine ⟨a, b, ha, hb, hf ?_⟩
    simpa only [map_zsmul] using h

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_RankOneKernelFiniteness
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A nonzero top kernel preserves rank-one homology finiteness -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] ModuleCat.isModule

theorem rankOne_module_finite_of_nonzero_kernel {M V : ModuleCat ℤ}
    (htorsion : ∀ (z : ℤ) (x : M), z • x = 0 → z = 0 ∨ x = 0)
    (hcomm : ∀ x y : M, x ≠ 0 → y ≠ 0 →
      ∃ a b : ℤ, a ≠ 0 ∧ b ≠ 0 ∧ a • x = b • y)
    (f : M ⟶ M) (e : V ≅ kernel f) [Module.Finite ℤ V]
    (x : V) (hx : x ≠ 0) : Module.Finite ℤ M := by
  let j : V ⟶ M := e.hom ≫ kernel.ι f
  have hj : Function.Injective j := (ModuleCat.mono_iff_injective j).mp inferInstance
  have hjx : j x ≠ 0 := by
    intro h
    exact hx (hj (h.trans (map_zero j.hom).symm))
  have hfx : f (j x) = 0 := by
    have h : j ≫ f = 0 := by simp only [j, Category.assoc, kernel.condition, comp_zero]
    exact congrArg (fun g : V ⟶ M => g x) h
  have hf : f = 0 := rankOne_homology_map_eq_zero_of_nonzero_kernel htorsion hcomm f _ hjx hfx
  have hfinite : Module.Finite ℤ (kernel f : ModuleCat ℤ) :=
    Module.Finite.of_surjective e.hom.hom ((ModuleCat.epi_iff_surjective e.hom).mp inferInstance)
  let := hfinite
  have hs : Function.Surjective (kernel.ι f) := by
    intro y
    refine ⟨kernel.lift f (𝟙 M) (by rw [hf, comp_zero]) y, ?_⟩
    exact congrArg (fun g => g y) (kernel.lift_ι f (𝟙 M) (by rw [hf, comp_zero]))
  exact Module.Finite.of_surjective (kernel.ι f).hom hs

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_CyclicKernelHomologyFiniteness
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteResolution_single_supported _root_.OAI.PolycyclicRecognition.finiteTruncationAugmentation_quasiIso _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finiteness descends through a nonzero cyclic top-degree kernel -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] ModuleCat.isModule Rep.hV2

theorem cyclic_topHomology_finiteness {G : Type} [Group G]
    (q : G →* Multiplicative ℤ) (t : G) (ht : q t = Multiplicative.ofAdd 1)
    (P : ProjectiveResolution (trivialIntegral q.ker)) (A : Rep ℤ G) (d : ℕ)
    (hvanish : IsZero (groupHomology (Rep.res q.ker.subtype A) (d + 1)))
    (htorsion : ∀ (z : ℤ) (x : groupHomology (Rep.res q.ker.subtype A) d),
      z • x = 0 → z = 0 ∨ x = 0)
    (hcomm : ∀ x y : groupHomology (Rep.res q.ker.subtype A) d,
      x ≠ 0 → y ≠ 0 → ∃ a b : ℤ, a ≠ 0 ∧ b ≠ 0 ∧ a • x = b • y)
    [Module.Finite ℤ (groupHomology A (d + 1))]
    (x : groupHomology A (d + 1)) (hx : x ≠ 0) :
    Module.Finite ℤ (groupHomology (Rep.res q.ker.subtype A) d) := by
  let := integerQuotient_isCyclic q t ht
  let := integerQuotient_infinite q t ht
  let M : ModuleCat ℤ := ((quotientInducedResolution q.ker P).complex.coinvariantsTensorObj A).homology d
  let E : M ≅ groupHomology (Rep.res q.ker.subtype A) d :=
    inducedResolutionHomologyIso q.ker A P d
  have hEinj : Function.Injective E.hom :=
    (ModuleCat.mono_iff_injective E.hom).mp inferInstance
  obtain ⟨htor, hcom⟩ := integralRankOne_properties_of_injective E.hom hEinj htorsion hcomm
  let f : M ⟶ M := HomologicalComplex.homologyMap (integerExtensionTensorMap q t P A) d
  have hfinite : Module.Finite ℤ M := rankOne_module_finite_of_nonzero_kernel htor hcom f
    (integerExtensionHomologyKernelIso q t ht P A d hvanish) x hx
  let := hfinite
  exact Module.Finite.equiv E.toLinearEquiv

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_FiniteDimensionHomology
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.cyclicTopHomologyInjection_mono _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Homology vanishing above the integral dimension bound -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits
variable {G : Type} [Group G]

theorem groupHomology_isZero_above_dimension (d : ℕ)
    [HasProjectiveDimensionLE (trivialIntegral G) d]
    (A : Rep ℤ G) (i : ℕ) (hi : d < i) : IsZero (groupHomology A i) := by
  classical
  let P := finiteProjectiveResolution (Rep.standardResolution ℤ G) d
  have hP : IsZero (P.complex.X i) :=
    finiteTruncation_isZero (Rep.standardResolution ℤ G) d i hi
  have hX : IsZero ((P.complex.coinvariantsTensorObj A).X i) :=
    ((Rep.coinvariantsTensor ℤ G).obj A).map_isZero hP
  refine IsZero.of_iso ?_ (groupHomologyIso A i P)
  apply HomologicalComplex.ExactAt.isZero_homology
  apply ShortComplex.exact_of_isZero_X₂
  simpa only [HomologicalComplex.shortComplexFunctor_obj_X₂] using hX

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_FiniteIndexTopHomology
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The index on top homology with induced orientation coefficients

The coefficient return map becomes multiplication by the subgroup index.
Identifying it with subgroup inclusion is a separate bar-resolution step.
-/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2100] Linear.homModule
variable {G : Type} [Group G] (H : Subgroup G) [H.FiniteIndex] (D : Rep ℤ G)

theorem finiteIndexOrientationHomEquiv_symm_id :
    (finiteIndexOrientationHomEquiv H D).symm (𝟙 _) = finiteIndexLift H D := by
  classical
  simp [finiteIndexOrientationHomEquiv, Linear.homCongr, finiteIndexLift]

theorem finiteIndexOrientationHom_return (eD : D.V ≃ₗ[ℤ] ℤ)
    (f : D ⟶ Rep.ind H.subtype (Rep.res H.subtype D)) :
    f ≫ finiteIndexReturn H D =
      ((rankOneEndomorphismsEquiv (Rep.res H.subtype D) eD)
        (finiteIndexOrientationHomEquiv H D f) * (H.index : ℤ)) • (𝟙 D : D ⟶ D) := by
  let z := (rankOneEndomorphismsEquiv (Rep.res H.subtype D) eD)
    (finiteIndexOrientationHomEquiv H D f)
  have ha : finiteIndexOrientationHomEquiv H D f = z • (𝟙 _) :=
    (rankOneEndomorphismsEquiv (Rep.res H.subtype D) eD).symm_apply_apply _ |>.symm
  have hf : f = z • finiteIndexLift H D := by
    apply (finiteIndexOrientationHomEquiv H D).injective
    rw [map_zsmul]
    rw [← finiteIndexOrientationHomEquiv_symm_id, LinearEquiv.apply_symm_apply]
    exact ha
  change f ≫ finiteIndexReturn H D = (z * (H.index : ℤ)) • (𝟙 D : D ⟶ D)
  rw [hf, Preadditive.zsmul_comp, finiteIndexLift_return]
  rw [← natCast_zsmul, smul_smul]

theorem finiteIndex_topHomology_return {n : ℕ} (eD : D.V ≃ₗ[ℤ] ℤ)
    (e : ∀ A : Rep ℤ G, groupHomology A n ≃ₗ[ℤ] (D ⟶ A))
    (he : ∀ (A B : Rep ℤ G) (f : A ⟶ B) (x : groupHomology A n),
      e B (groupHomology.map (MonoidHom.id G) f n x) = e A x ≫ f) :
    ∃ (u : groupHomology (Rep.ind H.subtype (Rep.res H.subtype D)) n ≃ₗ[ℤ] ℤ)
      (v : groupHomology D n ≃ₗ[ℤ] ℤ),
      ∀ x, v (groupHomology.map (MonoidHom.id G) (finiteIndexReturn H D) n x) =
        (H.index : ℤ) * u x := by
  let u := (e _).trans ((finiteIndexOrientationHomEquiv H D).trans
    (rankOneEndomorphismsEquiv (Rep.res H.subtype D) eD))
  let v := (e D).trans (rankOneEndomorphismsEquiv D eD)
  refine ⟨u, v, ?_⟩
  intro x
  change rankOneEndomorphismsEquiv D eD
    (e D (groupHomology.map (MonoidHom.id G) (finiteIndexReturn H D) n x)) = _
  rw [he, finiteIndexOrientationHom_return H D eD, map_zsmul]
  change (_ * (H.index : ℤ)) * (rankOneEndomorphismsEquiv D eD (𝟙 D)) = _
  simp [rankOneEndomorphismsEquiv, u, mul_comm]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_FiniteIndexHomologyDegree
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The degree of a finite-index inclusion in top homology -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2100] Linear.homModule
variable {G : Type} [Group G]

theorem finiteIndex_subgroup_topHomology_degree (H : Subgroup G) [H.FiniteIndex]
    (D : Rep ℤ G) {n : ℕ} (eD : D.V ≃ₗ[ℤ] ℤ)
    (e : ∀ A : Rep ℤ G, groupHomology A n ≃ₗ[ℤ] (D ⟶ A))
    (he : ∀ (A B : Rep ℤ G) (f : A ⟶ B) (x : groupHomology A n),
      e B (groupHomology.map (MonoidHom.id G) f n x) = e A x ≫ f) :
    ∃ (u : groupHomology (Rep.res H.subtype D) n ≃ₗ[ℤ] ℤ)
      (v : groupHomology D n ≃ₗ[ℤ] ℤ),
      ∀ x, v (subgroupHomologyInclusion H D n x) = (H.index : ℤ) * u x := by
  obtain ⟨u, v, h⟩ := finiteIndex_topHomology_return H D eD e he
  let s := (subgroupShapiroIso H (Rep.res H.subtype D) n).toLinearEquiv
  refine ⟨s.trans u, v, ?_⟩
  intro x
  have hx := congrArg (fun f => f x) (subgroupShapiro_return H D n)
  change groupHomology.map (MonoidHom.id G) (finiteIndexReturn H D) n (s x) =
    subgroupHomologyInclusion H D n x at hx
  change v (subgroupHomologyInclusion H D n x) = (H.index : ℤ) * u (s x)
  rw [← hx]
  exact h (s x)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_HomologyExhaustion
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Homology vanishing passes from an exhaustive sequence of subgroups

The proof uses finite support directly: a cycle lifts to a stage, injectivity
of its bar inclusion detects that it is a cycle there, and a local filling
maps to a global filling. No spectral sequence or colimit hypothesis is used.
-/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits
variable {G : Type} [Group G]

theorem groupHomology_isZero_of_exhaustion (S : ℕ → Subgroup G)
    (hS : Monotone S) (hcover : ∀ g, ∃ n, g ∈ S n)
    (A : Rep ℤ G) (i : ℕ)
    (hlocal : ∀ n, IsZero (groupHomology (Rep.res (S n).subtype A) i)) :
    IsZero (groupHomology A i) := by
  apply HomologicalComplex.ExactAt.isZero_homology
  apply (ShortComplex.moduleCat_exact_iff _).mpr
  intro z hz
  obtain ⟨n, w, hw⟩ := exists_barChain_in_subgroup S hS hcover A i z
  let F := subgroupBarInclusion (S n) A
  let C := groupHomology.inhomogeneousChains (Rep.res (S n).subtype A)
  let j := (ComplexShape.down ℕ).next i
  let k := (ComplexShape.down ℕ).prev i
  have hwcycle : C.d i j w = 0 := by
    apply subgroupBarInclusion_injective (S n) A j
    have hc := congrArg (fun f => f.hom w) (F.comm i j)
    change F.f j (C.d i j w) = F.f j 0
    rw [map_zero]
    change (groupHomology.inhomogeneousChains A).d i j (F.f i w) =
      F.f j (C.d i j w) at hc
    rw [← hc, hw]
    exact hz
  have hex : (C.sc i).Exact :=
    (C.exactAt_iff_isZero_homology i).mpr (hlocal n)
  obtain ⟨v, hv⟩ := (ShortComplex.moduleCat_exact_iff _).mp hex w hwcycle
  refine ⟨F.f k v, ?_⟩
  have hc := congrArg (fun f => f.hom v) (F.comm k i)
  change (groupHomology.inhomogeneousChains A).d k i (F.f k v) = z
  change (groupHomology.inhomogeneousChains A).d k i (F.f k v) =
    F.f i (C.d k i v) at hc
  change C.d k i v = w at hv
  rw [hc, hv]
  exact hw

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_HomologyExhaustionFiniteness
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite top homology forces an index-detecting exhaustion to stabilize -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory
attribute [local instance 2000] ModuleCat.isModule Rep.hV2 Rep.instLinear

theorem indexCoordinate_injective {M N : ModuleCat ℤ} (f : M ⟶ N)
    (u : M ≃ₗ[ℤ] ℤ) (v : N ≃ₗ[ℤ] ℤ) (k : ℕ) (hk : k ≠ 0)
    (h : ∀ x, v (f x) = (k : ℤ) * u x) : Function.Injective f := by
  intro x y hxy
  apply u.injective
  apply mul_left_cancel₀ (show (k : ℤ) ≠ 0 by exact_mod_cast hk)
  rw [← h, ← h, hxy]

theorem indexCoordinate_surjective {M N : ModuleCat ℤ} (f : M ⟶ N)
    (u : M ≃ₗ[ℤ] ℤ) (v : N ≃ₗ[ℤ] ℤ) (k : ℕ)
    (h : ∀ x, v (f x) = (k : ℤ) * u x) (hf : Function.Surjective f) : k = 1 := by
  obtain ⟨x, hx⟩ := hf (v.symm 1)
  have hd : (k : ℤ) ∣ 1 := ⟨u x, by rw [← h, hx, LinearEquiv.apply_symm_apply]⟩
  exact Nat.dvd_one.mp (Int.natCast_dvd_natCast.mp hd)

theorem exhaustion_stabilizes_of_finite_homology
    {G : Type} [Group G] (S : ℕ → Subgroup G) (hS : Monotone S)
    (hcover : ∀ g, ∃ n, g ∈ S n) (A : Rep ℤ G) (i : ℕ)
    [Module.Finite ℤ (groupHomology A i)]
    (hindex : ∀ n m, ((S n).subgroupOf (S m)).FiniteIndex)
    (hdegree : ∀ n m (hnm : n ≤ m),
      ∃ (u : groupHomology (Rep.res (S n).subtype A) i ≃ₗ[ℤ] ℤ)
        (v : groupHomology (Rep.res (S m).subtype A) i ≃ₗ[ℤ] ℤ),
        ∀ x, v (groupHomology.map (Subgroup.inclusion (hS hnm))
          (subgroupRestrictionMap (hS hnm) A) i x) =
          (((S n).subgroupOf (S m)).index : ℤ) * u x) :
    ∃ n, S n = ⊤ := by
  have hinj n m (hnm : n ≤ m) : Function.Injective
      (groupHomology.map (Subgroup.inclusion (hS hnm))
        (subgroupRestrictionMap (hS hnm) A) i) := by
    obtain ⟨u, v, h⟩ := hdegree n m hnm
    let := hindex n m
    exact indexCoordinate_injective _ u v _ Subgroup.FiniteIndex.index_ne_zero h
  obtain ⟨n, hn⟩ := exists_surjective_homology_stage S hS hcover A i
  have hsurj := (ModuleCat.epi_iff_surjective (subgroupHomologyInclusion (S n) A i)).mp hn
  have heq m (hnm : n ≤ m) : S m = S n := by
    have hi := subgroupHomologyInclusion_injective_of_stages S hS hcover A i hinj m
    have ht : Function.Surjective (groupHomology.map (Subgroup.inclusion (hS hnm))
        (subgroupRestrictionMap (hS hnm) A) i) := by
      intro y
      obtain ⟨x, hx⟩ := hsurj (subgroupHomologyInclusion (S m) A i y)
      refine ⟨x, hi ?_⟩
      exact (congrArg (fun f => f x) (subgroupHomologyInclusion_factor (hS hnm) A i)).trans hx
    obtain ⟨u, v, h⟩ := hdegree n m hnm
    have hk := indexCoordinate_surjective _ u v _ h ht
    have hback : S m ≤ S n := (Subgroup.relIndex_eq_one).mp hk
    exact le_antisymm hback (hS hnm)
  refine ⟨n, top_unique ?_⟩
  intro g _
  obtain ⟨m, hm⟩ := hcover g
  have hgm := hS (le_max_right n m) hm
  rwa [heq (max n m) (le_max_left n m)] at hgm

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_PoincareHomologyDimension
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Detecting Poincare dimension with homology coefficients -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2100] Linear.homModule
variable {G : Type} [Group G]

theorem IsIntegralPoincareDualityGroup.homologicalDimension_le {n : ℕ}
    (hG : IsIntegralPoincareDualityGroup G n) (d : ℕ)
    (hvanish : ∀ A : Rep ℤ G, ∀ i, d < i → IsZero (groupHomology A i)) : n ≤ d := by
  by_contra hn
  have hdn : d < n := Nat.lt_of_not_ge hn
  obtain ⟨D, ⟨eD⟩, he⟩ := hG.topHomology_orientation
  obtain ⟨eH⟩ := he D
  let := ModuleCat.subsingleton_of_isZero (hvanish D n hdn)
  have hid : (𝟙 D : D ⟶ D) = 0 := by
    apply eH.symm.injective
    exact Subsingleton.elim _ _
  have hv := congrArg (fun f : D ⟶ D => f.hom (eD.symm 1)) hid
  change eD.symm 1 = 0 at hv
  have h10 : (1 : ℤ) = 0 := by
    simpa only [LinearEquiv.apply_symm_apply, map_zero] using congrArg eD hv
  exact one_ne_zero h10

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Lattices_LatticeKernelTail
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.latticeNormalFlag_normal _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Removing the first coordinate of a free abelian quotient -/

noncomputable section
namespace PolycyclicRecognition

variable {G : Type} [Group G] {n : ℕ} (q : G →* IntegralLatticeGroup (n + 1))

theorem latticeKernelTail_surjective (hq : Function.Surjective q) :
    Function.Surjective (latticeKernelTail q) := by
  intro a
  obtain ⟨g, hg⟩ := hq (Multiplicative.ofAdd (Fin.cases 0 a.toAdd))
  have hg0 : g ∈ ((latticeCoordinate n).comp q).ker := by
    change latticeCoordinate n (q g) = 1
    rw [hg]
    rfl
  refine ⟨⟨g, hg0⟩, ?_⟩
  change latticeTail n (q g) = a
  rw [hg]
  rfl

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_LatticeExtensionHomologyBound
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.latticeNormalFlag_normal _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Homology dimension through a free abelian quotient

The explicit cyclic mapping cone is iterated over the quotient coordinates.
-/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits

theorem homology_bound_of_lattice_quotient (r : ℕ) {G : Type} [Group G]
    (q : G →* IntegralLatticeGroup r) (hq : Function.Surjective q) (d : ℕ)
    (hN : ∀ B : Rep ℤ q.ker, ∀ i, d < i → IsZero (groupHomology B i)) :
    ∀ A : Rep ℤ G, ∀ i, d + r < i → IsZero (groupHomology A i) := by
  induction r generalizing G with
  | zero =>
    have hker : q.ker = ⊤ := by
      ext g
      exact iff_of_true (Subsingleton.elim (q g) 1) (Subgroup.mem_top g)
    have e : q.ker ≃* G := (MulEquiv.subgroupCongr hker).trans Subgroup.topEquiv
    simpa only [Nat.add_zero] using homology_bound_of_equiv e d hN
  | succ r ih =>
    let p := (latticeCoordinate r).comp q
    obtain ⟨t, ht⟩ := hq (latticeCoordinateSection r)
    have hpt : p t = Multiplicative.ofAdd 1 := by
      change latticeCoordinate r (q t) = _
      rw [ht, latticeCoordinate_section]
    have htail : ∀ B : Rep ℤ (latticeKernelTail q).ker, ∀ i,
        d < i → IsZero (groupHomology B i) :=
      homology_bound_of_equiv (latticeKernelTailEquiv q) d hN
    have hK := ih (latticeKernelTail q) (latticeKernelTail_surjective q hq) htail
    simpa only [Nat.add_assoc, Nat.add_comm r 1] using
      homology_bound_of_integer_quotient p t hpt (d + r) hK

theorem IsIntegralPoincareDualityGroup.dimension_le_of_lattice_quotient
    {G : Type} [Group G] {n : ℕ} (hG : IsIntegralPoincareDualityGroup G n)
    (r : ℕ) (q : G →* IntegralLatticeGroup r) (hq : Function.Surjective q) (d : ℕ)
    (hN : ∀ B : Rep ℤ q.ker, ∀ i, d < i → IsZero (groupHomology B i)) : n ≤ d + r :=
  hG.homologicalDimension_le (d + r) (homology_bound_of_lattice_quotient r q hq d hN)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_LatticeKernelHomologyFiniteness
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.latticeNormalFlag_normal _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Descending top-homology finiteness through a free abelian quotient -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] ModuleCat.isModule Rep.hV2

theorem lattice_topHomology_finiteness (r : ℕ) {G : Type} [Group G]
    (q : G →* IntegralLatticeGroup r) (hq : Function.Surjective q) (d : ℕ)
    (hbound : ∀ B : Rep ℤ q.ker, ∀ i, d < i → IsZero (groupHomology B i))
    (A : Rep ℤ G)
    (htorsion : ∀ (z : ℤ) (x : groupHomology (Rep.res q.ker.subtype A) d),
      z • x = 0 → z = 0 ∨ x = 0)
    (hcomm : ∀ x y : groupHomology (Rep.res q.ker.subtype A) d,
      x ≠ 0 → y ≠ 0 → ∃ a b : ℤ, a ≠ 0 ∧ b ≠ 0 ∧ a • x = b • y) :
    (∀ (z : ℤ) (x : groupHomology A (d + r)), z • x = 0 → z = 0 ∨ x = 0) ∧
    (∀ x y : groupHomology A (d + r), x ≠ 0 → y ≠ 0 →
      ∃ a b : ℤ, a ≠ 0 ∧ b ≠ 0 ∧ a • x = b • y) ∧
    (∀ x : groupHomology A (d + r), x ≠ 0 → Module.Finite ℤ (groupHomology A (d + r)) →
      Module.Finite ℤ (groupHomology (Rep.res q.ker.subtype A) d)) := by
  induction r generalizing G with
  | zero =>
    have hker : q.ker = ⊤ := by
      ext g
      exact iff_of_true (Subsingleton.elim (q g) 1) (Subgroup.mem_top g)
    let f : q.ker ≃* G := (MulEquiv.subgroupCongr hker).trans Subgroup.topEquiv
    let E := groupHomology.mapIso (A := Rep.res q.ker.subtype A) (B := A)
      f (LinearEquiv.refl ℤ A.V) (by intro g; rfl) d
    have hi : Function.Injective E.inv := (ModuleCat.mono_iff_injective _).mp inferInstance
    obtain ⟨ht, hc⟩ := integralRankOne_properties_of_injective E.inv hi htorsion hcomm
    refine ⟨ht, hc, ?_⟩
    intro x hx hfinite
    let := hfinite
    exact Module.Finite.equiv E.symm.toLinearEquiv
  | succ r ih =>
    let p := (latticeCoordinate r).comp q
    obtain ⟨t, ht⟩ := hq (latticeCoordinateSection r)
    have hpt : p t = Multiplicative.ofAdd 1 := by
      change latticeCoordinate r (q t) = _
      rw [ht, latticeCoordinate_section]
    let q' := latticeKernelTail q
    let A' := Rep.res p.ker.subtype A
    let B := Rep.res q'.ker.subtype A'
    let E : groupHomology (Rep.res q.ker.subtype A) d ≅ groupHomology B d :=
      groupHomology.mapIso (A := Rep.res q.ker.subtype A) (B := B)
        (latticeKernelTailEquiv q) (LinearEquiv.refl ℤ A.V) (by intro g; rfl) d
    have hi : Function.Injective E.inv := (ModuleCat.mono_iff_injective _).mp inferInstance
    obtain ⟨htB, hcB⟩ := integralRankOne_properties_of_injective E.inv hi htorsion hcomm
    have hbB : ∀ B : Rep ℤ q'.ker, ∀ i, d < i → IsZero (groupHomology B i) :=
      homology_bound_of_equiv (latticeKernelTailEquiv q) d hbound
    obtain ⟨htK, hcK, hfiniteK⟩ := ih q' (latticeKernelTail_surjective q hq) hbB A' htB hcB
    have hvanish : IsZero (groupHomology A' (d + r + 1)) :=
      homology_bound_of_lattice_quotient r q' (latticeKernelTail_surjective q hq) d hbB
        A' (d + r + 1) (by omega)
    let P := Rep.standardResolution ℤ p.ker
    let j := cyclicTopHomologyInjection p t hpt P A (d + r) hvanish
    have hj : Function.Injective j := (ModuleCat.mono_iff_injective _).mp inferInstance
    obtain ⟨htG, hcG⟩ := integralRankOne_properties_of_injective j hj htK hcK
    have hdeg : d + (r + 1) = d + r + 1 := by omega
    rw [hdeg]
    refine ⟨htG, hcG, ?_⟩
    intro x hx hfinite
    let := hfinite
    have hKfinite := cyclic_topHomology_finiteness p t hpt P A (d + r) hvanish htK hcK x hx
    have hy : j x ≠ 0 := fun h => hx (hj (h.trans (map_zero j.hom).symm))
    have hBfinite : Module.Finite ℤ (groupHomology B d) := hfiniteK (j x) hy hKfinite
    let := hBfinite
    exact Module.Finite.equiv E.symm.toLinearEquiv

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_LatticeTopHomologyInjection
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.latticeNormalFlag_normal _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Injecting top homology into the kernel of a lattice quotient -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] ModuleCat.isModule Rep.hV2

theorem exists_latticeTopHomologyInjection (r : ℕ) {G : Type} [Group G]
    (q : G →* IntegralLatticeGroup r) (hq : Function.Surjective q) (d : ℕ)
    (hbound : ∀ B : Rep ℤ q.ker, ∀ i, d < i → IsZero (groupHomology B i))
    (A : Rep ℤ G) :
    ∃ f : groupHomology A (d + r) ⟶ groupHomology (Rep.res q.ker.subtype A) d,
      Function.Injective f := by
  induction r generalizing G with
  | zero =>
    have hker : q.ker = ⊤ := by
      ext g
      exact iff_of_true (Subsingleton.elim (q g) 1) (Subgroup.mem_top g)
    let e : q.ker ≃* G := (MulEquiv.subgroupCongr hker).trans Subgroup.topEquiv
    let E := groupHomology.mapIso (A := Rep.res q.ker.subtype A) (B := A)
      e (LinearEquiv.refl ℤ A.V) (by intro g; rfl) d
    exact ⟨E.inv, (ModuleCat.mono_iff_injective _).mp inferInstance⟩
  | succ r ih =>
    let p := (latticeCoordinate r).comp q
    obtain ⟨t, ht⟩ := hq (latticeCoordinateSection r)
    have hpt : p t = Multiplicative.ofAdd 1 := by
      change latticeCoordinate r (q t) = _
      rw [ht, latticeCoordinate_section]
    let q' := latticeKernelTail q
    let A' := Rep.res p.ker.subtype A
    let B := Rep.res q'.ker.subtype A'
    let E : groupHomology (Rep.res q.ker.subtype A) d ≅ groupHomology B d :=
      groupHomology.mapIso (A := Rep.res q.ker.subtype A) (B := B)
        (latticeKernelTailEquiv q) (LinearEquiv.refl ℤ A.V) (by intro g; rfl) d
    have hbB : ∀ B : Rep ℤ q'.ker, ∀ i, d < i → IsZero (groupHomology B i) :=
      homology_bound_of_equiv (latticeKernelTailEquiv q) d hbound
    obtain ⟨f, hf⟩ := ih q' (latticeKernelTail_surjective q hq) hbB A'
    have hv : IsZero (groupHomology A' (d + r + 1)) :=
      homology_bound_of_lattice_quotient r q' (latticeKernelTail_surjective q hq) d hbB
        A' (d + r + 1) (by omega)
    let j := cyclicTopHomologyInjection p t hpt (Rep.standardResolution ℤ p.ker) A (d + r) hv
    have hj : Function.Injective j := (ModuleCat.mono_iff_injective _).mp inferInstance
    have hE : Function.Injective E.inv := (ModuleCat.mono_iff_injective _).mp inferInstance
    have hdeg : d + (r + 1) = d + r + 1 := by omega
    rw [hdeg]
    exact ⟨j ≫ f ≫ E.inv, hE.comp (hf.comp hj)⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_SubgroupTopHomologyDegree
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Index coordinates for nested subgroups with a common orientation -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2100] Linear.homModule
variable {G : Type} [Group G]

theorem nestedSubgroup_topHomology_degree {H K : Subgroup G} (hHK : H ≤ K)
    [((H.subgroupOf K)).FiniteIndex] (D : Rep ℤ G) (eD : D.V ≃ₗ[ℤ] ℤ) {n : ℕ}
    (hK : IsIntegralPoincareDualityGroup K n)
    (hD : ∀ A : Rep ℤ K,
      Nonempty (groupHomology A n ≃ₗ[ℤ] (Rep.res K.subtype D ⟶ A))) :
    ∃ (u : groupHomology (Rep.res H.subtype D) n ≃ₗ[ℤ] ℤ)
      (v : groupHomology (Rep.res K.subtype D) n ≃ₗ[ℤ] ℤ),
      ∀ x, v (groupHomology.map (Subgroup.inclusion hHK)
        (subgroupRestrictionMap hHK D) n x) = ((H.subgroupOf K).index : ℤ) * u x := by
  obtain ⟨e, he⟩ := topHomology_natural_prescribed hK (Rep.res K.subtype D) eD hD
  obtain ⟨u, v, hd⟩ := finiteIndex_subgroup_topHomology_degree
    (H.subgroupOf K) (Rep.res K.subtype D) eD e he
  let f := (Subgroup.subgroupOfEquivOfLe hHK).symm
  let s := groupHomology.mapIso (A := Rep.res H.subtype D)
    (B := Rep.res (H.subgroupOf K).subtype (Rep.res K.subtype D)) f
    (LinearEquiv.refl ℤ D.V) (by intro g; rfl) n
  have hs : s.hom ≫ subgroupHomologyInclusion (H.subgroupOf K) (Rep.res K.subtype D) n =
      groupHomology.map (Subgroup.inclusion hHK) (subgroupRestrictionMap hHK D) n := by
    change groupHomology.map _ _ n ≫ groupHomology.map _ _ n = groupHomology.map _ _ n
    rw [← groupHomology.map_comp]
    exact groupHomology.map_congr (by ext; rfl) (by apply DFunLike.ext; intro x; rfl) n
  refine ⟨s.toLinearEquiv.trans u, v, ?_⟩
  intro x
  have hx := congrArg (fun f => f x) hs
  change subgroupHomologyInclusion (H.subgroupOf K) (Rep.res K.subtype D) n (s.hom x) =
    groupHomology.map (Subgroup.inclusion hHK) (subgroupRestrictionMap hHK D) n x at hx
  rw [← hx]
  exact hd (s.hom x)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_NilpotentTopHomologyFiniteness
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.cyclicTopHomologyInjection_mono _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.normalizedGroupIdentityClass_comparison _root_.OAI.PolycyclicRecognition.rationalCoefficientInclusion_apply _root_.OAI.PolycyclicRecognition.resolutionStableSyzygyTransition_class _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Detecting finite generation of the nilpotent kernel by its top homology -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2100] Linear.homModule
variable {G : Type} [Group G] [Countable G] [Group.IsNilpotent G]

theorem nilpotent_topHomology_finiteness_criterion
    (hG : HasFiniteIntegralCohomologicalDimension G) :
    ∃ d : ℕ, ∃ R : Rep ℤ G, Nonempty (R.V ≃ₗ[ℤ] ℤ) ∧
      (∀ A : Rep ℤ G, ∀ i, d < i → IsZero (groupHomology A i)) ∧
      (∃ x : groupHomology R d, x ≠ 0) ∧
      (∀ (z : ℤ) (x : groupHomology R d), z • x = 0 → z = 0 ∨ x = 0) ∧
      (∀ x y : groupHomology R d, x ≠ 0 → y ≠ 0 →
        ∃ a b : ℤ, a ≠ 0 ∧ b ≠ 0 ∧ a • x = b • y) ∧
      (Module.Finite ℤ (groupHomology R d) → Group.FG G) ∧
      (∀ A : Rep ℤ G, Nonempty (A.V ≃ₗ[ℤ] ℤ) →
        (∃ x : groupHomology A d, x ≠ 0) → Nonempty (R ≅ A)) := by
  obtain ⟨d, S, hS, hfg, hcover, hd, hindex⟩ :=
    exists_nilpotent_duality_exhaustion_finiteIndex hG
  obtain ⟨R, ⟨eR⟩, hR⟩ := exists_exhaustion_orientation S hS hcover d hd hindex
  have hdegree n m (hnm : n ≤ m) :
      ∃ (u : groupHomology (Rep.res (S n).subtype R) d ≃ₗ[ℤ] ℤ)
        (v : groupHomology (Rep.res (S m).subtype R) d ≃ₗ[ℤ] ℤ),
        ∀ x, v (groupHomology.map (Subgroup.inclusion (hS hnm))
          (subgroupRestrictionMap (hS hnm) R) d x) =
          (((S n).subgroupOf (S m)).index : ℤ) * u x := by
    let := hindex n m
    exact nestedSubgroup_topHomology_degree (hS hnm) R eR (hd m) (hR m)
  have hinj n m (hnm : n ≤ m) : Function.Injective
      (groupHomology.map (Subgroup.inclusion (hS hnm))
        (subgroupRestrictionMap (hS hnm) R) d) := by
    obtain ⟨u, v, h⟩ := hdegree n m hnm
    let := hindex n m
    exact indexCoordinate_injective _ u v _ Subgroup.FiniteIndex.index_ne_zero h
  have hrank n : Nonempty (groupHomology (Rep.res (S n).subtype R) d ≃ₗ[ℤ] ℤ) := by
    obtain ⟨e⟩ := hR n (Rep.res (S n).subtype R)
    exact ⟨e.trans (rankOneEndomorphismsEquiv (Rep.res (S n).subtype R) eR)⟩
  refine ⟨d, R, ⟨eR⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro A i hi
    apply groupHomology_isZero_of_exhaustion S hS hcover A i
    intro n
    let := (hd n).cohomologicalDimension
    exact groupHomology_isZero_above_dimension d _ i hi
  · obtain ⟨e⟩ := hR 0 (Rep.res (S 0).subtype R)
    let e0 := e.trans (rankOneEndomorphismsEquiv (Rep.res (S 0).subtype R) eR)
    refine ⟨subgroupHomologyInclusion (S 0) R d (e0.symm 1), ?_⟩
    intro h
    have hi := subgroupHomologyInclusion_injective_of_stages S hS hcover R d hinj 0
    have hz : e0.symm 1 = 0 := hi (h.trans (map_zero _).symm)
    have he := congrArg e0 hz
    simp at he
  · exact homology_torsionFree_of_rankOne_stages S hS hcover R d hrank
      (subgroupHomologyInclusion_injective_of_stages S hS hcover R d hinj)
  · exact homology_commensurable_of_rankOne_stages S hS hcover R d hrank
  · intro hfinite
    let := hfinite
    obtain ⟨n, hn⟩ := exhaustion_stabilizes_of_finite_homology S hS hcover R d hindex hdegree
    exact ⟨hn ▸ hfg n⟩

  · rintro A ⟨eA⟩ ⟨x, hx⟩
    exact exhaustion_orientation_of_nonzero_top S hS hcover d R eR hR A eA x hx

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Lattices_LatticeNormalFlag
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.commutingIntegralHom_generator _root_.OAI.PolycyclicRecognition.integralQuotientDrop_insert _root_.OAI.PolycyclicRecognition.integralQuotientLast_insert _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The normal cyclic flag of a lattice quotient -/

noncomputable section
namespace PolycyclicRecognition
variable {G : Type} [Group G] {r : ℕ} (q : G →* IntegralLatticeGroup r)

theorem latticeNormalFlag_mono {i j : ℕ} (hij : i ≤ j) :
    latticeNormalFlag q i ≤ latticeNormalFlag q j :=
  fun _ hx k hk => hx k (hij.trans hk)

theorem latticeNormalFlag_zero : latticeNormalFlag q 0 = q.ker := by
  ext g
  constructor
  · intro hg
    change q g = 1
    apply Multiplicative.toAdd.injective
    funext j
    exact hg j (Nat.zero_le _)
  · intro hg j _
    change q g = 1 at hg
    rw [hg]
    rfl

theorem latticeNormalFlag_top : latticeNormalFlag q r = ⊤ := by
  apply top_unique
  intro g _ j hj
  exact False.elim (Nat.not_le_of_gt j.isLt hj)

theorem latticeNormalFlagStep_ker (i : Fin r) :
    (latticeNormalFlagStep q i).ker =
      (latticeNormalFlag q i.val).subgroupOf (latticeNormalFlag q (i.val + 1)) := by
  ext g
  constructor
  · intro hg j hj
    have hh := congrArg Multiplicative.toAdd hg
    change (q (g : G)).toAdd i = 0 at hh
    by_cases hji : j = i
    · subst j; exact hh
    · exact g.property j (by have hne : j.val ≠ i.val := fun h => hji (Fin.ext h); omega)
  · intro hg
    exact congrArg Multiplicative.ofAdd (hg i (le_refl _))

theorem latticeNormalFlagStep_generator (hq : Function.Surjective q) (i : Fin r) :
    ∃ t : latticeNormalFlag q (i.val + 1), latticeNormalFlagStep q i t = Multiplicative.ofAdd 1 := by
  classical
  obtain ⟨g, hg⟩ := hq (Multiplicative.ofAdd (Pi.single i 1))
  have hmem : g ∈ latticeNormalFlag q (i.val + 1) := by
    intro j hj
    rw [hg]
    change (Pi.single i 1 : Fin r → ℤ) j = 0
    have hji : j ≠ i := by intro h; subst j; omega
    simp [hji]
  refine ⟨⟨g, hmem⟩, ?_⟩
  change Multiplicative.ofAdd ((q g).toAdd i) = _
  rw [hg]
  simp

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Lattices_LatticeTopLine
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A nonzero top class above a free abelian quotient -/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear ModuleCat.isModule
variable {G : Type} [Group G] {r : ℕ}

theorem invariantTopLine_of_subgroup_eq (N M : Subgroup G) [N.Normal] [M.Normal]
    (h : N = M) (d : ℕ)
    (hN : ∃ A : Rep ℤ G,
      Nonempty (groupHomology (Rep.res N.subtype A) d ≃ₗ[ℤ] ℚ) ∧
      ∀ g, normalHomologyMap ℤ N A d g = 𝟙 _) :
    ∃ A : Rep ℤ G,
      Nonempty (groupHomology (Rep.res M.subtype A) d ≃ₗ[ℤ] ℚ) ∧
      ∀ g, normalHomologyMap ℤ M A d g = 𝟙 _ := by
  subst M
  exact hN

theorem exists_latticeTopLine_of_kernelLine
    (q : G →* IntegralLatticeGroup r) (hq : Function.Surjective q) (d : ℕ)
    (hbound : ∀ R : Rep ℤ q.ker, ∀ j, d < j → IsZero (groupHomology R j))
    (A : Rep ℤ G) (eA : groupHomology (Rep.res q.ker.subtype A) d ≃ₗ[ℤ] ℚ)
    (hA : ∀ g, normalHomologyMap ℤ q.ker A d g = 𝟙 _) :
    ∃ B : Rep ℤ G, Nonempty (groupHomology B (d + r) ≃ₗ[ℤ] ℚ) := by
  have H : ∀ i, i ≤ r →
      (∀ R : Rep ℤ (latticeNormalFlag q i), ∀ j, d + i < j → IsZero (groupHomology R j)) ∧
      ∃ B : Rep ℤ G,
        Nonempty (groupHomology (Rep.res (latticeNormalFlag q i).subtype B) (d + i) ≃ₗ[ℤ] ℚ) ∧
        ∀ g, normalHomologyMap ℤ (latticeNormalFlag q i) B (d + i) g = 𝟙 _ := by
    intro i
    induction i with
    | zero =>
      intro _
      let e := MulEquiv.subgroupCongr (latticeNormalFlag_zero q).symm
      exact ⟨homology_bound_of_equiv e d hbound,
        invariantTopLine_of_subgroup_eq q.ker (latticeNormalFlag q 0)
          (latticeNormalFlag_zero q).symm d ⟨A, ⟨eA⟩, hA⟩⟩

    | succ i ih =>
      intro hi
      obtain ⟨hb, B, ⟨eB⟩, hB⟩ := ih (by omega)
      let j : Fin r := ⟨i, by omega⟩
      let p := latticeNormalFlagStep q j
      obtain ⟨t, ht⟩ := latticeNormalFlagStep_generator q hq j
      have hker : p.ker = (latticeNormalFlag q i).subgroupOf (latticeNormalFlag q (i + 1)) :=
        latticeNormalFlagStep_ker q j
      have hle : latticeNormalFlag q i ≤ latticeNormalFlag q (i + 1) :=
        latticeNormalFlag_mono q (Nat.le_succ i)
      let e : p.ker ≃* latticeNormalFlag q i :=
        (MulEquiv.subgroupCongr hker).trans (Subgroup.subgroupOfEquivOfLe hle)
      have hbker := homology_bound_of_equiv e.symm (d + i) hb
      have hbnext := homology_bound_of_integer_quotient p t ht (d + i) hbker
      have hnext := exists_normalCyclicTopStep (latticeNormalFlag q i)
        (latticeNormalFlag q (i + 1)) hle p t ht hker (d + i) hb B eB hB
      have hdim : d + i + 1 = d + (i + 1) := Nat.add_assoc d i 1
      rw [hdim] at hbnext hnext
      exact ⟨hbnext, hnext⟩
  obtain ⟨_, B, ⟨eB⟩, _⟩ := H r (le_refl r)
  have eTop : groupHomology (Rep.res (⊤ : Subgroup G).subtype B) (d + r) ≃ₗ[ℤ] ℚ := by
    rw [latticeNormalFlag_top] at eB
    exact eB
  let E := groupHomology.mapIso (A := Rep.res (⊤ : Subgroup G).subtype B) (B := B)
    Subgroup.topEquiv (LinearEquiv.refl ℤ B.V) (by intro g; rfl) (d + r)
  exact ⟨B, ⟨E.symm.toLinearEquiv.trans eTop⟩⟩

theorem exists_latticeTopLine
    (q : G →* IntegralLatticeGroup r) (hq : Function.Surjective q) (d : ℕ)
    (hbound : ∀ A : Rep ℤ q.ker, ∀ j, d < j → IsZero (groupHomology A j))
    (R : Rep ℤ q.ker) (eR : R.V ≃ₗ[ℤ] ℤ)
    (x : groupHomology R d) (hx : x ≠ 0)
    (htor : ∀ (a : ℤ) (y : groupHomology R d), a • y = 0 → a = 0 ∨ y = 0)
    (hcomm : ∀ y z : groupHomology R d, y ≠ 0 → z ≠ 0 →
      ∃ a b : ℤ, a ≠ 0 ∧ b ≠ 0 ∧ a • y = b • z)
    (hdetect : ∀ A : Rep ℤ q.ker, Nonempty (A.V ≃ₗ[ℤ] ℤ) →
      (∃ y : groupHomology A d, y ≠ 0) → Nonempty (R ≅ A)) :
    ∃ B : Rep ℤ G, Nonempty (groupHomology B (d + r) ≃ₗ[ℤ] ℚ) := by
  obtain ⟨χ, _, hχ, _, hact⟩ := exists_rationalInvariantTopClass q.ker R eR d x hx htor hcomm hdetect
  obtain ⟨eA⟩ := rationalOrientation_topLine q.ker R eR d χ hχ x hx htor hcomm
  exact exists_latticeTopLine_of_kernelLine q hq d hbound (rationalCharacterRep χ) eA hact

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_NilpotentLatticeFiniteness
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.finitelyGeneratedSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finiteness of a nilpotent kernel below a lattice quotient

The rational top class supplies the lower dimension bound. Integral
orientation homology and exhaustion stabilization then force finite generation.
-/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] ModuleCat.isModule Rep.hV2
variable {G : Type} [Group G] [Countable G]

theorem nilpotent_kernel_finitelyGenerated_of_latticeQuotient (r : ℕ)
    (q : G →* IntegralLatticeGroup r) (hq : Function.Surjective q)
    [Group.IsNilpotent q.ker] {n : ℕ} (hG : IsIntegralPoincareDualityGroup G n) :
    Group.FG q.ker := by
  obtain ⟨d, R, ⟨eR⟩, hb, ⟨z, hz⟩, htor, hcom, hfinite, horientation⟩ :=
    nilpotent_topHomology_finiteness_criterion ((hG.finiteCohomologicalDimension G).subgroup q.ker)
  obtain ⟨B, ⟨eB⟩⟩ := exists_latticeTopLine q hq d hb R eR z hz htor hcom horientation
  have hlow : d + r ≤ n := by
    by_contra h
    let : HasProjectiveDimensionLE (trivialIntegral G) n := hG.cohomologicalDimension
    have hzero := groupHomology_isZero_above_dimension n B (d + r) (by omega)
    let : Subsingleton (groupHomology B (d + r)) := ModuleCat.subsingleton_of_isZero hzero
    have he : eB.symm (1 : ℚ) = eB.symm 0 := Subsingleton.elim _ _
    exact one_ne_zero (eB.symm.injective he)
  have hupp := hG.dimension_le_of_lattice_quotient r q hq d hb
  have hn : n = d + r := le_antisymm hupp hlow
  subst n
  obtain ⟨D, ⟨eD⟩, hfiniteD, x, hx⟩ := hG.exists_finite_nonzero_top
  let := hfiniteD
  obtain ⟨j, hj⟩ := exists_latticeTopHomologyInjection r q hq d hb D
  have hy : j x ≠ 0 := fun h => hx (hj (h.trans (map_zero j.hom).symm))
  obtain ⟨i⟩ := horientation (Rep.res q.ker.subtype D) ⟨eD⟩ ⟨j x, hy⟩
  let E : groupHomology R d ≅ groupHomology (Rep.res q.ker.subtype D) d :=
    (groupHomology.functor ℤ q.ker d).mapIso i
  have hEi : Function.Injective E.inv := (ModuleCat.mono_iff_injective _).mp inferInstance
  obtain ⟨htD, hcD⟩ := integralRankOne_properties_of_injective E.inv hEi htor hcom
  have hFD := (lattice_topHomology_finiteness r q hq d hb D htD hcD).2.2 x hx hfiniteD
  let := hFD
  exact hfinite (Module.Finite.equiv E.symm.toLinearEquiv)

theorem polycyclic_of_nilpotent_latticeQuotient (r : ℕ)
    (q : G →* IntegralLatticeGroup r) (hq : Function.Surjective q)
    [Group.IsNilpotent q.ker] {n : ℕ} (hG : IsIntegralPoincareDualityGroup G n) :
    IsPolycyclic G := by
  let := nilpotent_kernel_finitelyGenerated_of_latticeQuotient r q hq hG
  let e := QuotientGroup.quotientKerEquivOfSurjective q hq
  let : Group.FG (IntegralLatticeGroup r) := (integralLattice_poincareDuality r).1.fg
  have hQ : IsPolycyclic (G ⧸ q.ker) :=
    (isPolycyclic_of_finitelyGenerated_nilpotent (IntegralLatticeGroup r)).of_surjective
      e.symm.toMonoidHom e.symm.surjective
  exact isPolycyclic_of_normal_subgroup q.ker
    (isPolycyclic_of_finitelyGenerated_nilpotent q.ker) hQ

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_SolvablePoincareFiniteness
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

namespace OAI

/-! # The solvable integral Poincare duality finiteness theorem -/

noncomputable section
namespace PolycyclicRecognition
open scoped IsMulCommutative
variable {G : Type} [Group G] [Group.IsSolvable G]

theorem polycyclic_of_nilpotent_by_abelian_duality_oai (N : Subgroup G) [N.Normal]
    [Group.IsNilpotent N] [IsMulCommutative (G ⧸ N)] {n : ℕ}
    (hG : IsIntegralPoincareDualityGroup G n) : IsPolycyclic G := by
  let : Group.FG G := hG.1.fg
  let : CommGroup (G ⧸ N) := inferInstance
  have hQ : IsPolycyclic (G ⧸ N) := isPolycyclic_of_finitelyGenerated_nilpotent (G ⧸ N)
  obtain ⟨U, hU, htf⟩ := hQ.exists_torsionFree_finiteIndex
  let := hU
  let : Group.FG U := inferInstance
  obtain ⟨r, ⟨e⟩⟩ := exists_integralLattice_equiv (A := U) htf
  let π := QuotientGroup.mk' N
  let P := U.comap π
  let : P.FiniteIndex := inferInstance
  let f : P →* U := (π.comp P.subtype).codRestrict U (fun x => x.property)
  have hf : Function.Surjective f := by
    intro u
    obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective N (u : G ⧸ N)
    have hgP : g ∈ P := by change π g ∈ U; rw [hg]; exact u.property
    refine ⟨⟨g, hgP⟩, ?_⟩
    apply Subtype.ext
    exact hg
  let q := e.symm.toMonoidHom.comp f
  have hq : Function.Surjective q := e.symm.surjective.comp hf
  have hk (a : q.ker) : ((a : P) : G) ∈ N := by
    have ha : q (a : P) = 1 := a.property
    have hfa : f (a : P) = 1 := by
      apply e.symm.injective
      exact ha.trans (map_one e.symm.toMonoidHom).symm
    have hh := congrArg (fun u : U => (u : G ⧸ N)) hfa
    change π ((a : P) : G) = ((1 : U) : G ⧸ N) at hh
    have hπ : π ((a : P) : G) = 1 := by
      simpa only [Subgroup.coe_one] using hh
    exact (QuotientGroup.eq_one_iff _).mp hπ
  let k : q.ker →* N := (P.subtype.comp q.ker.subtype).codRestrict N hk
  have hki : Function.Injective k := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun x : N => (x : G)) hab
  let : Group.IsNilpotent q.ker := nilpotent_of_injective_hom k hki
  let : Group.FG P := inferInstance
  let : Countable P := countable_of_group_fg P
  have hP : IsPolycyclic P := polycyclic_of_nilpotent_latticeQuotient r q hq
    (hG.finiteIndex_subgroup P)
  exact (show IsVirtuallyPolycyclic G from ⟨P, inferInstance, hP⟩).polycyclic_of_solvable

end PolycyclicRecognition

end

end OAI
end

theorem solution : type_of% @OAI.PolycyclicRecognition.polycyclic_of_nilpotent_by_abelian_duality_oai := @OAI.PolycyclicRecognition.polycyclic_of_nilpotent_by_abelian_duality_oai
