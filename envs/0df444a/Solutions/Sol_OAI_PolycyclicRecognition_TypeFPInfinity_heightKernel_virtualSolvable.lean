-- Prove2me | solution 1 for OAI.PolycyclicRecognition.TypeFPInfinity.heightKernel_virtualSolvable
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-02T22:18:30.507762+00:00
-- url     : https://prove2.me/submissions/a607ff2c-76f5-40cd-8ea6-21418f9fe298

import Mathlib
import Definitions.Def_PolycyclicRecognition
import Definitions.Def_OAIQ093D020

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
attribute [-instance] _root_.GeneratesNS.rho_g_FG _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
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

/-- Schreier finite generation applies to the nilpotent finite-index subgroup. -/
theorem isVirtuallyPolycyclic_of_finitelyGenerated_virtuallyNilpotent
    (hG : Group.IsVirtuallyNilpotent G) : IsVirtuallyPolycyclic G := by
  obtain ⟨N, hnil, hindex⟩ := hG
  let := hnil
  let := hindex
  exact ⟨N, hindex, isPolycyclic_of_finitelyGenerated_nilpotent N⟩

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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_SquareZeroPower
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Powers of a unit plus a square-zero element -/
namespace PolycyclicRecognition

theorem one_add_pow_of_square_zero {R : Type*} [Semiring R]
    (x : R) (hx : x * x = 0) (n : ℕ) : (1 + x) ^ n = 1 + n • x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih]
    calc
      (1 + n • x) * (1 + x) = 1 + (n + 1) • x := by
        rw [add_mul, one_mul, mul_add, mul_one, smul_mul_assoc, hx, nsmul_zero,
          add_zero, succ_nsmul]
        ac_rfl

theorem one_add_cube {R : Type*} [Ring R] (x : R) :
    (1 + x) ^ 3 = 1 + 3 • x + 3 • (x * x) + x * x * x := by
  noncomm_ring

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_ThreePrimitiveIntegerFamily
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A primitive integral family after removing its common power of three -/
noncomputable section
namespace PolycyclicRecognition

theorem integerFamily_three_primitive {I : Type} (a : I → ℤ)
    (ha : ∃ i, a i ≠ 0) (h3 : ∀ i, (3 : ℤ) ∣ a i) :
    ∃ k : ℕ, 0 < k ∧ ∃ c : I → ℤ,
      (∀ i, a i = 3 ^ k * c i) ∧ ∃ i, ¬(3 : ℤ) ∣ c i := by
  classical
  obtain ⟨i, hi⟩ := ha
  have hex : ∃ n : ℕ, ¬∀ i, (3 : ℤ) ^ (n + 1) ∣ a i := by
    refine ⟨padicValNat 3 (a i).natAbs, ?_⟩
    intro h
    have hd := h i
    have hd' : (3 : ℕ) ^ (padicValNat 3 (a i).natAbs + 1) ∣ (a i).natAbs := by
      apply Int.natCast_dvd.mp
      simpa only [Nat.cast_pow, Nat.cast_ofNat] using hd
    exact pow_succ_padicValNat_not_dvd (p := 3) (Int.natAbs_ne_zero.mpr hi) hd'
  let k := Nat.find hex
  have hnot : ¬∀ i, (3 : ℤ) ^ (k + 1) ∣ a i := Nat.find_spec hex
  have hk : 0 < k := by
    by_contra h
    have he : k = 0 := by omega
    apply hnot
    simpa only [he, zero_add, pow_one] using h3
  have hd : ∀ i, (3 : ℤ) ^ k ∣ a i := by
    obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
    have hmin := Nat.find_min hex (show j < Nat.find hex by change j < k; omega)
    have hprev : ∀ i, (3 : ℤ) ^ (j + 1) ∣ a i := not_not.mp hmin
    simpa only [hj] using hprev
  choose c hc using hd
  refine ⟨k, hk, c, hc, ?_⟩
  by_contra h
  have hall : ∀ i, (3 : ℤ) ∣ c i := by simpa only [not_exists, not_not] using h
  apply hnot
  intro j
  obtain ⟨b, hb⟩ := hall j
  refine ⟨b, ?_⟩
  rw [hc j, hb, pow_succ, mul_assoc]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_ThreeCongruenceMatrix
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integral matrices congruent to the identity modulo three -/
noncomputable section
namespace PolycyclicRecognition
open Matrix
variable {I : Type} [Fintype I] [DecidableEq I]

theorem matrixMod_zsmul (m : ℕ) (a : ℤ) (A : Matrix I I ℤ) :
    matrixMod m (a • A) = (a : ZMod m) • matrixMod m A := by
  ext i j
  change ((a * A i j : ℤ) : ZMod m) = (a : ZMod m) * (A i j : ZMod m)
  exact Int.cast_mul a (A i j)

theorem zmod_three_power_zero (a b : ℕ) (h : a ≤ b) :
    (3 : ZMod (3 ^ a)) ^ b = 0 := by
  have hd : 3 ^ a ∣ (3 : ℕ) ^ b := pow_dvd_pow 3 h
  have hz := (ZMod.natCast_eq_zero_iff (3 ^ b) (3 ^ a)).mpr hd
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using hz

theorem integerMatrix_three_primitive (A : Matrix I I ℤ)
    (hne : A ≠ 1) (h3 : ∀ i j, (3 : ℤ) ∣ (A - 1) i j) :
    ∃ k : ℕ, 0 < k ∧ ∃ C : Matrix I I ℤ,
      A = 1 + (3 ^ k : ℤ) • C ∧ ∃ i j, ¬(3 : ℤ) ∣ C i j := by
  have hnon : ∃ p : I × I, (A - 1) p.1 p.2 ≠ 0 := by
    by_contra h
    apply hne
    have hz : A - 1 = 0 := by
      ext i j
      exact not_not.mp (fun hij => h ⟨(i, j), hij⟩)
    exact sub_eq_zero.mp hz
  obtain ⟨k, hk, c, hc, p, hp⟩ :=
    integerFamily_three_primitive (fun p : I × I => (A - 1) p.1 p.2) hnon
      (fun p => h3 p.1 p.2)
  let C : Matrix I I ℤ := fun i j => c (i, j)
  refine ⟨k, hk, C, ?_, p.1, p.2, hp⟩
  have he : A - 1 = (3 ^ k : ℤ) • C := by
    ext i j
    exact hc (i, j)
  simpa only [add_comm] using sub_eq_iff_eq_add.mp he

theorem integerMatrix_prime_three_dvd (A C : Matrix I I ℤ) (k p : ℕ)
    (hk : 0 < k) (hA : A = 1 + (3 ^ k : ℤ) • C) (hpow : A ^ p = 1) :
    ∀ i j, (3 : ℤ) ∣ (p : ℤ) * C i j := by
  let m := 3 ^ (k + 1)
  let D := matrixMod (I := I) m C
  let s : ZMod m := 3 ^ k
  let X : Matrix I I (ZMod m) := s • D
  have hX : X * X = 0 := by
    change (s • D) * (s • D) = 0
    rw [smul_mul_assoc, mul_smul_comm, smul_smul]
    have hs : s * s = 0 := by
      change (3 : ZMod (3 ^ (k + 1))) ^ k * 3 ^ k = 0
      rw [← pow_add]
      exact zmod_three_power_zero (k + 1) (k + k) (by omega)
    rw [hs, zero_smul]
  have he : (1 + X) ^ p = 1 := by
    have hm := congrArg (matrixMod (I := I) m) hpow
    rw [map_pow, map_one, hA, map_add, map_one, matrixMod_zsmul] at hm
    simpa only [Int.cast_pow, Int.cast_ofNat] using hm
  rw [one_add_pow_of_square_zero X hX p] at he
  have hz : p • X = 0 := by simpa using he
  intro i j
  have hc : (((p : ℤ) * (3 ^ k * C i j) : ℤ) : ZMod m) = 0 := by
    have hij := congrArg (fun M : Matrix I I (ZMod m) => M i j) hz
    simpa [X, s, D, Matrix.smul_apply, nsmul_eq_mul, smul_eq_mul] using hij
  have hd := (ZMod.intCast_zmod_eq_zero_iff_dvd
    ((p : ℤ) * (3 ^ k * C i j)) m).mp hc
  have heq : (p : ℤ) * (3 ^ k * C i j) = 3 ^ k * ((p : ℤ) * C i j) := by ring
  rw [heq] at hd
  have hd' : (3 ^ k : ℤ) * 3 ∣ 3 ^ k * ((p : ℤ) * C i j) := by
    simpa only [m, Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat, pow_succ] using hd
  exact (mul_dvd_mul_iff_left (pow_ne_zero k (by norm_num : (3 : ℤ) ≠ 0))).mp hd'

theorem integerMatrix_cube_three_dvd (A C : Matrix I I ℤ) (k : ℕ)
    (hk : 0 < k) (hA : A = 1 + (3 ^ k : ℤ) • C) (hpow : A ^ 3 = 1) :
    ∀ i j, (3 : ℤ) ∣ C i j := by
  let m := 3 ^ (k + 2)
  let D := matrixMod (I := I) m C
  let s : ZMod m := 3 ^ k
  let X : Matrix I I (ZMod m) := s • D
  have hsq : X * X = (s * s) • (D * D) := by
    change (s • D) * (s • D) = _
    rw [smul_mul_assoc, mul_smul_comm, smul_smul]
  have hX2 : 3 • (X * X) = 0 := by
    rw [← Nat.cast_smul_eq_nsmul (ZMod m) 3, hsq, smul_smul]
    norm_num only [Nat.cast_ofNat]
    have hs : (3 : ZMod m) * (s * s) = 0 := by
      change (3 : ZMod (3 ^ (k + 2))) * (3 ^ k * 3 ^ k) = 0
      rw [← pow_add, ← pow_succ']
      exact zmod_three_power_zero (k + 2) (k + k + 1) (by omega)
    rw [hs, zero_smul]
  have hX3 : X * X * X = 0 := by
    rw [hsq]
    change ((s * s) • (D * D)) * (s • D) = 0
    rw [smul_mul_assoc, mul_smul_comm, smul_smul]
    have hs : (s * s) * s = 0 := by
      change ((3 : ZMod (3 ^ (k + 2))) ^ k * 3 ^ k) * 3 ^ k = 0
      rw [← pow_add, ← pow_add]
      exact zmod_three_power_zero (k + 2) (k + k + k) (by omega)
    rw [hs, zero_smul]
  have he : (1 + X) ^ 3 = 1 := by
    have hm := congrArg (matrixMod (I := I) m) hpow
    rw [map_pow, map_one, hA, map_add, map_one, matrixMod_zsmul] at hm
    simpa only [Int.cast_pow, Int.cast_ofNat] using hm
  rw [one_add_cube X, hX2, hX3, add_zero, add_zero] at he
  have hz : 3 • X = 0 := by simpa using he
  intro i j
  have hc : (((3 : ℤ) * (3 ^ k * C i j) : ℤ) : ZMod m) = 0 := by
    have hij := congrArg (fun M : Matrix I I (ZMod m) => M i j) hz
    simpa [X, s, D, Matrix.smul_apply, nsmul_eq_mul, smul_eq_mul] using hij
  have hd := (ZMod.intCast_zmod_eq_zero_iff_dvd
    ((3 : ℤ) * (3 ^ k * C i j)) m).mp hc
  have heq : (3 : ℤ) * (3 ^ k * C i j) = 3 ^ (k + 1) * C i j := by
    rw [pow_succ]
    ring
  rw [heq] at hd
  have hd' : (3 ^ (k + 1) : ℤ) * 3 ∣ 3 ^ (k + 1) * C i j := by
    simpa only [m, Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat, show k + 2 = (k + 1) + 1 by omega,
      pow_succ] using hd
  exact (mul_dvd_mul_iff_left (pow_ne_zero (k + 1) (by norm_num : (3 : ℤ) ≠ 0))).mp hd'

theorem integerMatrix_eq_one_of_prime_order_three_congruence
    (A : Matrix I I ℤ) (p : ℕ) (hp : p.Prime) (hpow : A ^ p = 1)
    (h3 : ∀ i j, (3 : ℤ) ∣ (A - 1) i j) : A = 1 := by
  by_contra hne
  obtain ⟨k, hk, C, hA, i, j, hij⟩ := integerMatrix_three_primitive A hne h3
  have hdiv := integerMatrix_prime_three_dvd A C k p hk hA hpow i j
  have hpp : (3 : ℤ) ∣ (p : ℤ) := ((by norm_num : Prime (3 : ℤ)).dvd_mul.mp hdiv).resolve_right hij
  have hpn : 3 ∣ p := by exact_mod_cast hpp
  have hp3 : p = 3 := (hp.eq_one_or_self_of_dvd 3 hpn).resolve_left (by norm_num) |>.symm
  subst p
  exact hij (integerMatrix_cube_three_dvd A C k hk hA hpow i j)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_IntegralMatrixFiniteOrder
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reduction modulo three is faithful on finite integral matrix groups -/
noncomputable section
namespace PolycyclicRecognition
open Matrix
variable {I : Type} [Fintype I] [DecidableEq I]

theorem matrixMod_eq_one_iff (m : ℕ) (A : Matrix I I ℤ) :
    matrixMod m A = 1 ↔ ∀ i j, (m : ℤ) ∣ (A - 1) i j := by
  have h : matrixMod m A = 1 ↔ matrixMod m (A - 1) = 0 := by
    rw [map_sub, map_one, sub_eq_zero]
  rw [h]
  constructor
  · intro hz i j
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ m).mp
    exact congrArg (fun M : Matrix I I (ZMod m) => M i j) hz
  · intro hz
    ext i j
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ m).mpr (hz i j)

theorem integerMatrix_eq_one_of_finite_order_three_congruence
    (A : Matrix I I ℤ) (hfin : IsOfFinOrder A)
    (h3 : ∀ i j, (3 : ℤ) ∣ (A - 1) i j) : A = 1 := by
  by_contra hne
  have hon : orderOf A ≠ 1 := fun h => hne (orderOf_eq_one_iff.mp h)
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hon
  let B := A ^ (orderOf A / p)
  have ho : orderOf B = p := orderOf_pow_orderOf_div (ne_of_gt hfin.orderOf_pos) hpd
  have hpw : B ^ p = 1 := by rw [← ho]; exact pow_orderOf_eq_one B
  have hm : matrixMod 3 B = 1 := by
    dsimp only [B]
    rw [map_pow, (matrixMod_eq_one_iff 3 A).mpr h3, one_pow]
  have he := integerMatrix_eq_one_of_prime_order_three_congruence B p hp hpw
    ((matrixMod_eq_one_iff 3 B).mp hm)
  have hbad : p = 1 := by rw [← ho, he, orderOf_one]
  exact hp.ne_one hbad

theorem finite_integral_matrix_representation_card_le
    {G : Type} [Group G] [Finite G] (ρ : G →* Matrix I I ℤ)
    (hρ : Function.Injective ρ) : Nat.card G ≤ 3 ^ (Fintype.card I * Fintype.card I) := by
  let f : G →* Matrix I I (ZMod 3) := (matrixMod 3).toMonoidHom.comp ρ
  have hf : Function.Injective f := by
    intro x y hxy
    have hz : f (x⁻¹ * y) = 1 := by
      rw [map_mul, ← hxy, ← map_mul, inv_mul_cancel, map_one]
    have hfin : IsOfFinOrder (ρ (x⁻¹ * y)) :=
      (isOfFinOrder_of_finite (x⁻¹ * y)).mono (orderOf_map_dvd ρ (x⁻¹ * y))
    have he : ρ (x⁻¹ * y) = 1 :=
      integerMatrix_eq_one_of_finite_order_three_congruence _ hfin
        ((matrixMod_eq_one_iff 3 _).mp hz)
    have hg : x⁻¹ * y = 1 := hρ (he.trans ρ.map_one.symm)
    exact inv_mul_eq_one.mp hg
  have hc := Nat.card_le_card_of_injective f hf
  simpa only [Nat.card_eq_fintype_card, Matrix, Fintype.card_fun, ZMod.card, ← pow_mul] using hc

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_FiniteRationalRepresentation
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A uniform bound for finite faithful rational representations

The integral lattice is the span of the finite orbit of a rational basis.
Reduction modulo three then bounds the group order.
-/
noncomputable section
namespace PolycyclicRecognition
open Module
variable {G V I : Type} [Group G] [Finite G]
  [AddCommGroup V] [Module ℚ V] [Fintype I]

omit [Finite G] [Fintype I] in
theorem finiteOrbitIntegerLattice_basis_mem (ρ : G →* Module.End ℚ V)
    (b : Basis I ℚ V) (i : I) : b i ∈ finiteOrbitIntegerLattice ρ b := by
  apply Submodule.subset_span
  exact ⟨(1, i), by simp⟩

theorem finiteOrbitIntegerLattice_isLattice (ρ : G →* Module.End ℚ V)
    (b : Basis I ℚ V) : Submodule.IsLattice ℚ (finiteOrbitIntegerLattice ρ b) where
  fg := Submodule.fg_span (Set.finite_range _)
  span_eq_top := by
    apply top_unique
    rw [← b.span_eq]
    apply Submodule.span_le.mpr
    rintro v ⟨i, rfl⟩
    exact Submodule.subset_span (finiteOrbitIntegerLattice_basis_mem ρ b i)

omit [Finite G] [Fintype I] in
theorem finiteOrbitIntegerRepresentation_injective (ρ : G →* Module.End ℚ V)
    (hρ : Function.Injective ρ) (b : Basis I ℚ V) :
    Function.Injective (finiteOrbitIntegerRepresentation ρ b) := by
  intro g h he
  apply hρ
  apply b.ext
  intro i
  exact congrArg (fun f : Module.End ℤ (finiteOrbitIntegerLattice ρ b) =>
    (f ⟨b i, finiteOrbitIntegerLattice_basis_mem ρ b i⟩ : V)) he

theorem finite_rational_representation_card_le [Module.Finite ℚ V]
    (ρ : G →* Module.End ℚ V) (hρ : Function.Injective ρ) :
    Nat.card G ≤ 3 ^ (Module.finrank ℚ V * Module.finrank ℚ V) := by
  classical
  let b := Module.Free.chooseBasis ℚ V
  let L := finiteOrbitIntegerLattice ρ b
  let : Submodule.IsLattice ℚ L := finiteOrbitIntegerLattice_isLattice ρ b
  let c := Module.Free.chooseBasis ℤ L
  let σ : G →* Matrix (Module.Free.ChooseBasisIndex ℤ L)
      (Module.Free.ChooseBasisIndex ℤ L) ℤ :=
    (LinearMap.toMatrixAlgEquiv c).toMonoidHom.comp (finiteOrbitIntegerRepresentation ρ b)
  have hσ : Function.Injective σ :=
    (LinearMap.toMatrixAlgEquiv c).injective.comp (finiteOrbitIntegerRepresentation_injective ρ hρ b)
  have hc : Fintype.card (Module.Free.ChooseBasisIndex ℤ L) = Module.finrank ℚ V := by
    rw [← Module.finrank_eq_card_basis c]
    exact congrArg Cardinal.toNat (Submodule.IsLattice.rank' ℚ L)
  simpa only [hc] using finite_integral_matrix_representation_card_le σ hσ

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

end PolycyclicRecognition

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

theorem ambientUpperCentralSeries_zero (F : Subgroup G) :
    ambientUpperCentralSeries F 0 = ⊥ := by
  simp only [ambientUpperCentralSeries, Subgroup.upperCentralSeries_zero, Subgroup.map_bot]

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
attribute [-instance] _root_.GeneratesNS.rho_g_FG _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finite_templateSymmetryGroup _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteSubtypeLinearEquivRealIdMemSubgroupLinearSupportSymmetryGroup _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_PolycyclicTorsionFree
attribute [-instance] _root_.GeneratesNS.rho_g_FG _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finite_templateSymmetryGroup _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteSubtypeLinearEquivRealIdMemSubgroupLinearSupportSymmetryGroup _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
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
attribute [-instance] _root_.GeneratesNS.rho_g_FG _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finite_templateSymmetryGroup _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteSubtypeLinearEquivRealIdMemSubgroupLinearSupportSymmetryGroup _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
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

theorem upperCentralLayerAut_eq_one_of_rational [Group.IsNilpotent F]
    (hF : HasNoNontrivialTorsion F) (i : ℕ) (g : G)
    (hg : rationalUpperCentralAction F i g = 1) : upperCentralLayerAut F i g = 1 := by
  have hQ := nilpotent_upperCentralQuotient_torsionFree hF i
  have hZ : HasNoNontrivialTorsion (CentralLayer F i) :=
    hQ.of_injective (Subgroup.center _).subtype Subtype.val_injective
  apply rationalAbelianAut_injective hZ
  simpa only [rationalUpperCentralAction, MonoidHom.comp_apply, map_one] using hg

theorem commutator_centralLayer_le_of_rational_kernel [Group.IsNilpotent F]
    (hF : HasNoNontrivialTorsion F) (i : ℕ) (K : Subgroup G)
    (hK : K ≤ (rationalUpperCentralAction F i).ker) :
    ⁅K, ambientUpperCentralSeries F (i + 1)⁆ ≤ ambientUpperCentralSeries F i := by
  apply Subgroup.commutator_le.mpr
  intro g hg a ha
  obtain ⟨b, hb, rfl⟩ := ha
  let U := Subgroup.upperCentralSeries F i
  let q := QuotientGroup.mk' U
  have hbZ : q b ∈ Subgroup.center (F ⧸ U) := by
    change b ∈ (Subgroup.center (F ⧸ U)).comap q
    rw [← Subgroup.upperCentralSeriesStep_eq_comap_center]
    exact hb
  have hfix := upperCentralLayerAut_eq_one_of_rational F hF i g (hK hg)
  have hqb : q ((MulAut.conjNormal (H := F) g) b) = q b := by
    have hh := congrArg
      (fun e : MulAut (CentralLayer F i) => ((e ⟨q b, hbZ⟩ : CentralLayer F i) : F ⧸ U)) hfix
    exact hh
  have hdiff : (MulAut.conjNormal (H := F) g) b * b⁻¹ ∈ U := by
    apply (QuotientGroup.eq_one_iff _).mp
    change q ((MulAut.conjNormal (H := F) g) b * b⁻¹) = 1
    rw [map_mul, map_inv, hqb, mul_inv_cancel]
  refine ⟨(MulAut.conjNormal (H := F) g) b * b⁻¹, hdiff, ?_⟩
  rfl

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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_FiniteCentralLayerAction
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.cyclicTopHomologyInjection_mono _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.normalizedGroupIdentityClass_comparison _root_.OAI.PolycyclicRecognition.rationalCoefficientInclusion_apply _root_.OAI.PolycyclicRecognition.resolutionStableSyzygyTransition_class _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

namespace OAI

/-! # Uniform index of the central-layer action kernel -/
noncomputable section
namespace PolycyclicRecognition
open Module
open scoped IsMulCommutative
variable {G : Type} [Group G] (F : Subgroup G) [F.Normal] [Group.IsNilpotent F]

omit [F.Normal] in
theorem centralLayer_finrank_le (d : ℕ)
    [CategoryTheory.HasProjectiveDimensionLE (trivialIntegral F) d] (i : ℕ) :
    Module.finrank ℚ (RationalAbelianSpace (CentralLayer F i)) ≤ d := by
  let := nilpotent_upperCentral_center_rational_finite (G := F) d i
  apply FiniteDimensional.finrank_le_iff_rank_le.mpr
  rw [rationalAbelianSpace_rank]
  exact nilpotent_quotient_abelian_subgroup_rank_le d
    (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _) (Subgroup.center _)

omit [F.Normal] in
theorem centralLayersSpace_finrank_le (d c : ℕ)
    [CategoryTheory.HasProjectiveDimensionLE (trivialIntegral F) d] :
    Module.finrank ℚ (CentralLayersSpace F c) ≤ c * d := by
  let := centralLayersSpace_finite F ⟨d, inferInstance⟩ c
  let (i : Fin c) : Module.Finite ℚ (RationalAbelianSpace (CentralLayer F i)) :=
    nilpotent_upperCentral_center_rational_finite (G := F) d i
  change Module.finrank ℚ ((i : Fin c) → RationalAbelianSpace (CentralLayer F i)) ≤ c * d
  rw [Module.finrank_pi_fintype]
  calc
    ∑ i : Fin c, Module.finrank ℚ (RationalAbelianSpace (CentralLayer F i)) ≤
        ∑ _i : Fin c, d := Finset.sum_le_sum (fun i _ => centralLayer_finrank_le F d i)
    _ = c * d := by simp

theorem centralLayersAction_index_le [F.FiniteIndex] (d c : ℕ)
    [CategoryTheory.HasProjectiveDimensionLE (trivialIntegral F) d] :
    (centralLayersAction F c).ker.index ≤ 3 ^ ((c * d) * (c * d)) := by
  let ρ := centralLayersAction F c
  let : ρ.ker.FiniteIndex := Subgroup.finiteIndex_of_le (subgroup_le_centralLayersAction_ker F c)
  let : Finite ρ.range := Nat.finite_of_card_ne_zero (by
    rw [← Subgroup.index_ker]
    exact Subgroup.FiniteIndex.index_ne_zero)
  let := centralLayersSpace_finite F ⟨d, inferInstance⟩ c
  let σ : ρ.range →* Module.End ℚ (CentralLayersSpace F c) :=
    LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp ρ.range.subtype
  have hσ : Function.Injective σ :=
    LinearEquiv.toLinearMap_injective.comp Subtype.val_injective
  have hb := finite_rational_representation_card_le σ hσ
  rw [Subgroup.index_ker]
  exact hb.trans (Nat.pow_le_pow_right (by omega)
    (Nat.mul_self_le_mul_self (centralLayersSpace_finrank_le F d c)))

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_FiniteCentralizerCommutator
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The centralizer of a finite-index subgroup has finite commutator -/
noncomputable section
namespace PolycyclicRecognition
open scoped commutatorElement
variable {G : Type} [Group G]

theorem commutatorElement_center_mul_left (z a b : G) (hz : z ∈ Subgroup.center G) :
    ⁅z * a, b⁆ = ⁅a, b⁆ := by
  rw [commutatorElement_mul_left_eq_conj_mul]
  have hzb : ⁅z, b⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr
    ((Subgroup.mem_center_iff.mp hz b).symm)
  rw [hzb, mul_one, ← Subgroup.mem_center_iff.mp hz ⁅a, b⁆, mul_inv_cancel_right]

theorem commutatorElement_center_mul_right (z a b : G) (hz : z ∈ Subgroup.center G) :
    ⁅a, z * b⁆ = ⁅a, b⁆ := by
  rw [commutatorElement_mul_right_eq_mul_conj]
  have haz : ⁅a, z⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr
    (Subgroup.mem_center_iff.mp hz a)
  rw [haz, one_mul, ← Subgroup.mem_center_iff.mp hz ⁅a, b⁆, mul_inv_cancel_right]

theorem commutator_finite_of_center_finiteIndex [(Subgroup.center G).FiniteIndex] :
    Finite (commutator G) := by
  classical
  let q := QuotientGroup.mk' (Subgroup.center G)
  let rep : G ⧸ Subgroup.center G → G := Quotient.out
  have hrep (g : G) : g * (rep (q g))⁻¹ ∈ Subgroup.center G := by
    apply (QuotientGroup.eq_one_iff _).mp
    change q (g * (rep (q g))⁻¹) = 1
    rw [map_mul, map_inv]
    have hr : q (rep (q g)) = q g := Quotient.out_eq' (q g)
    rw [hr, mul_inv_cancel]
  have he (g h : G) : ⁅g, h⁆ = ⁅rep (q g), rep (q h)⁆ := by
    calc
      ⁅g, h⁆ = ⁅(g * (rep (q g))⁻¹) * rep (q g), h⁆ := by simp
      _ = ⁅rep (q g), h⁆ := commutatorElement_center_mul_left _ _ _ (hrep g)
      _ = ⁅rep (q g), (h * (rep (q h))⁻¹) * rep (q h)⁆ := by simp
      _ = ⁅rep (q g), rep (q h)⁆ := commutatorElement_center_mul_right _ _ _ (hrep h)
  let f : (G ⧸ Subgroup.center G) × (G ⧸ Subgroup.center G) → G :=
    fun p => ⁅rep p.1, rep p.2⁆
  have hs : (commutatorSet G).Finite := (Set.finite_range f).subset (by
    rintro x ⟨g, h, rfl⟩
    exact ⟨(q g, q h), (he g h).symm⟩)
  let : Finite (commutatorSet G) := Set.finite_coe_iff.mpr hs
  infer_instance

theorem centralizer_commutator_finite (F : Subgroup G) [F.FiniteIndex] :
    Finite (commutator (Subgroup.centralizer (F : Set G))) := by
  let C := Subgroup.centralizer (F : Set G)
  have hle : F.subgroupOf C ≤ Subgroup.center C := by
    intro x hx
    apply Subgroup.mem_center_iff.mpr
    intro y
    apply Subtype.ext
    exact (y.property x hx).symm
  let : (Subgroup.center C).FiniteIndex := Subgroup.finiteIndex_of_le hle
  exact commutator_finite_of_center_finiteIndex

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_FiniteKernelSolvable
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Removing a finite normal kernel from virtual solvability

This is the elementary centralizer step used in §2 of
Kropholler–Martínez-Pérez–Nucinkis (2009). It does not assume any finiteness
theorem for elementary amenable groups.
-/

noncomputable section
namespace PolycyclicRecognition

variable {G : Type*} [Group G] (N : Subgroup G) [N.Normal]

theorem conjugation_ker_eq_centralizer :
    (MulAut.conjNormal : G →* MulAut N).ker = Subgroup.centralizer (N : Set G) := by
  ext g
  constructor
  · intro hg n hn
    have he := congrArg (fun a : MulAut N => (a ⟨n, hn⟩ : G)) hg
    change g * n * g⁻¹ = n at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  · intro hg
    apply MulEquiv.ext
    intro n
    apply Subtype.ext
    change g * (n : G) * g⁻¹ = (n : G)
    rw [← hg n n.property, mul_inv_cancel_right]

theorem finiteIndex_centralizer_of_finite_normal [Finite N] :
    (Subgroup.centralizer (N : Set G)).FiniteIndex := by
  rw [← conjugation_ker_eq_centralizer N]
  infer_instance

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_FiniteConjugationIndexBound
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instNonemptyBases _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A uniform bound for centralizing a finite normal subgroup -/
noncomputable section
namespace PolycyclicRecognition
variable {G : Type} [Group G]

theorem finite_normal_centralizer_index_le (N : Subgroup G) [N.Normal] [Finite N]
    (b : ℕ) (hb : Nat.card N ≤ b) :
    (Subgroup.centralizer (N : Set G)).index ≤ b ^ b := by
  have hp : 0 < b := lt_of_lt_of_le Nat.card_pos hb
  have hA : Nat.card (MulAut N) ≤ Nat.card N ^ Nat.card N := by
    have h := Nat.card_le_card_of_injective (fun a : MulAut N => (a : N → N))
      DFunLike.coe_injective
    simpa only [Nat.card_fun] using h
  rw [← conjugation_ker_eq_centralizer N, Subgroup.index_ker]
  exact (Nat.card_le_card_of_injective _ Subtype.val_injective).trans
    (hA.trans ((Nat.pow_le_pow_left hb _).trans (Nat.pow_le_pow_right hp hb)))

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_LocallyBoundedDerivedSeries
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A uniform derived-series bound passes from finitely generated subgroups -/
noncomputable section
namespace PolycyclicRecognition
open scoped commutatorElement
variable {G : Type} [Group G]

theorem ambientDerivedSeries_zero (H : Subgroup G) : ambientDerivedSeries H 0 = H := by
  simp only [ambientDerivedSeries, derivedSeries_zero, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem ambientDerivedSeries_succ (H : Subgroup G) (n : ℕ) :
    ambientDerivedSeries H (n + 1) = ⁅ambientDerivedSeries H n, ambientDerivedSeries H n⁆ := by
  simp only [ambientDerivedSeries, derivedSeries_succ, Subgroup.map_commutator]

theorem derivedSeries_le_fgDerivedSubgroup (n : ℕ) :
    derivedSeries G n ≤ fgDerivedSubgroup n := by
  induction n with
  | zero =>
    intro g _
    let H : Subgroup G := Subgroup.closure {g}
    have hH : H.FG := (Subgroup.fg_iff H).mpr ⟨{g}, rfl, Set.finite_singleton g⟩
    refine ⟨H, hH, ?_⟩
    rw [ambientDerivedSeries_zero]
    exact Subgroup.subset_closure (Set.mem_singleton g)
  | succ n ih =>
    rw [derivedSeries_succ]
    apply Subgroup.commutator_le.mpr
    intro x hx y hy
    obtain ⟨H, hH, hxH⟩ := ih hx
    obtain ⟨K, hK, hyK⟩ := ih hy
    refine ⟨H ⊔ K, hH.sup hK, ?_⟩
    rw [ambientDerivedSeries_succ]
    exact Subgroup.commutator_mem_commutator
      (ambientDerivedSeries_mono le_sup_left n hxH)
      (ambientDerivedSeries_mono le_sup_right n hyK)

theorem derivedSeries_eq_bot_of_fg_subgroups (n : ℕ)
    (h : ∀ H : Subgroup G, H.FG → derivedSeries H n = ⊥) : derivedSeries G n = ⊥ := by
  apply eq_bot_iff.mpr
  intro g hg
  obtain ⟨H, hH, hgH⟩ := derivedSeries_le_fgDerivedSubgroup n hg
  simpa only [ambientDerivedSeries, h H hH, Subgroup.map_bot] using hgH

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_TrivialCentralLayerDerived
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Trivial central-layer action bounds the derived series modulo the centralizer -/
noncomputable section
namespace PolycyclicRecognition
open scoped commutatorElement
variable {G : Type} [Group G] (F : Subgroup G) [F.Normal] [Group.IsNilpotent F]

theorem centralLayers_kernel_derived_le_centralizer (hF : HasNoNontrivialTorsion F) :
    ambientDerivedSeries (centralLayersAction F (Group.nilpotencyClass F)).ker
      (Group.nilpotencyClass F) ≤ Subgroup.centralizer (F : Set G) := by
  let c := Group.nilpotencyClass F
  let K := (centralLayersAction F c).ker
  let U := ambientUpperCentralSeries F
  have hstep (i : ℕ) : ⁅K, U (i + 1)⁆ ≤ U i := by
    by_cases hi : i < c
    · apply commutator_centralLayer_le_of_rational_kernel F hF i K
      intro g hg
      exact (centralLayersAction_ker_iff F c g).mp hg ⟨i, hi⟩
    · have he (j : ℕ) (hj : c ≤ j) : U j = F := by
        dsimp [U, ambientUpperCentralSeries]
        rw [Subgroup.upperCentralSeries_eq_top_iff_nilpotencyClass_le.mpr hj]
        simp only [← MonoidHom.range_eq_map, Subgroup.range_subtype]
      rw [he i (by omega), he (i + 1) (by omega)]
      exact Subgroup.commutator_le_right K F
  have hz : ⁅K.lowerCentralSeries c, F⁆ = ⊥ := by
    apply eq_bot_iff.mpr
    have he : U (c + 1) = F := by
      dsimp [U, ambientUpperCentralSeries]
      rw [Subgroup.upperCentralSeries_eq_top_iff_nilpotencyClass_le.mpr (Nat.le_succ c)]
      simp only [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    have hd := lowerCentralSeries_action_depth K U hstep c 0
    simpa only [Nat.zero_add, he, U, ambientUpperCentralSeries_zero] using hd
  have hder : ambientDerivedSeries K c ≤ K.lowerCentralSeries c := by
    rw [ambientDerivedSeries, ← Subgroup.top_subtype_lowerCentralSeries]
    exact Subgroup.map_mono (Subgroup.derived_le_lower_central c)
  exact hder.trans (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hz)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_BoundedCentralLayerSolvability
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.cyclicTopHomologyInjection_mono _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.normalizedGroupIdentityClass_comparison _root_.OAI.PolycyclicRecognition.rationalCoefficientInclusion_apply _root_.OAI.PolycyclicRecognition.resolutionStableSyzygyTransition_class _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform solvability bounds from a nilpotent finite-index subgroup -/
noncomputable section
namespace PolycyclicRecognition
open scoped commutatorElement
variable {G : Type} [Group G] (F : Subgroup G)
  [F.Normal] [F.FiniteIndex] [Group.IsNilpotent F]

theorem bounded_solvable_subgroup_of_nilpotent_finiteIndex
    (hF : HasNoNontrivialTorsion F) (b d : ℕ)
    (hb : ∀ N : Subgroup G, Finite N → Nat.card N ≤ b)
    [CategoryTheory.HasProjectiveDimensionLE (trivialIntegral F) d] :
    ∃ H : Subgroup G, H.FiniteIndex ∧
      H.index ≤ 3 ^ (((Group.nilpotencyClass F) * d) * ((Group.nilpotencyClass F) * d)) * b ^ b ∧
      derivedSeries H (Group.nilpotencyClass F + 2) = ⊥ := by
  let c := Group.nilpotencyClass F
  let K := (centralLayersAction F c).ker
  let C := Subgroup.centralizer (F : Set G)
  let D := (commutator C).map C.subtype
  let : Finite (commutator C) := centralizer_commutator_finite F
  let : Finite D := Finite.of_equiv (commutator C)
    ((commutator C).equivMapOfInjective C.subtype Subtype.val_injective).toEquiv
  let : D.Normal := by dsimp [D, C]; infer_instance
  let T := Subgroup.centralizer (D : Set G)
  let : T.FiniteIndex := finiteIndex_centralizer_of_finite_normal D
  let : K.FiniteIndex := Subgroup.finiteIndex_of_le (subgroup_le_centralLayersAction_ker F c)
  let H := K ⊓ T
  have hKD : ambientDerivedSeries K (c + 1) ≤ D := by
    rw [ambientDerivedSeries_succ]
    have hKC := centralLayers_kernel_derived_le_centralizer F hF
    simpa only [D, Subgroup.map_subtype_commutator] using Subgroup.commutator_mono hKC hKC
  have hHD : ambientDerivedSeries H (c + 1) ≤ D :=
    (ambientDerivedSeries_mono inf_le_left (c + 1)).trans hKD
  have hHT : ambientDerivedSeries H (c + 1) ≤ T :=
    (Subgroup.map_subtype_le _).trans inf_le_right
  have hzero : ambientDerivedSeries H (c + 2) = ⊥ := by
    change ambientDerivedSeries H ((c + 1) + 1) = ⊥
    rw [ambientDerivedSeries_succ]
    apply eq_bot_iff.mpr
    apply (Subgroup.commutator_mono hHD hHT).trans
    rw [Subgroup.commutator_comm D T]
    exact le_of_eq (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr le_rfl)
  refine ⟨H, inferInstance, ?_, ?_⟩
  · exact (Subgroup.index_inf_le (H := K) (K := T)).trans (Nat.mul_le_mul
      (centralLayersAction_index_le F d c) (finite_normal_centralizer_index_le D b (hb D inferInstance)))
  · apply eq_bot_iff.mpr
    intro x hx
    have hm : (x : G) ∈ ambientDerivedSeries H (c + 2) := ⟨x, hx, rfl⟩
    rw [hzero] at hm
    exact Subtype.ext hm

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_BoundedLocallyFiniteKernel
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finite_templateSymmetryGroup _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteSubtypeLinearEquivRealIdMemSubgroupLinearSupportSymmetryGroup _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

namespace OAI

/-! # Removing a locally finite kernel with bounded finite subgroup orders

The bound on finite subgroups remains an explicit premise. Local finiteness
then makes the whole kernel finite, and a finite kernel preserves virtual
solvability by centralizing that kernel.
-/
noncomputable section
namespace PolycyclicRecognition
variable {G : Type} [Group G]

theorem HasBoundedFiniteSubgroupOrders.subgroup
    (hG : HasBoundedFiniteSubgroupOrders G) (H : Subgroup G) :
    HasBoundedFiniteSubgroupOrders H := by
  obtain ⟨b, hb⟩ := hG
  refine ⟨b, fun K hK => ?_⟩
  let := hK
  let e := K.equivMapOfInjective H.subtype Subtype.val_injective
  let : Finite (K.map H.subtype) := Finite.of_equiv K e.toEquiv
  simpa only [Nat.card_congr e.toEquiv] using hb (K.map H.subtype) inferInstance

theorem virtually_solvable_of_finite_kernel
    {Q : Type} [Group Q] [Group.IsSolvable Q] (f : G →* Q) [Finite f.ker] :
    ∃ H : Subgroup G, H.FiniteIndex ∧ Group.IsSolvable H := by
  let K := f.ker
  let : Finite (MulAut K) := Finite.of_injective
    (fun a : MulAut K => (a : K → K)) DFunLike.coe_injective
  let ρ : G →* MulAut K := MulAut.conjNormal
  let H := ρ.ker
  let : H.FiniteIndex := inferInstance
  let p : H →* Q := f.comp H.subtype
  have hcomm : ∀ a b : p.ker, a * b = b * a := by
    intro a b
    apply Subtype.ext
    apply Subtype.ext
    have hb : ((b : H) : G) ∈ K := b.property
    have ha : ρ ((a : H) : G) = 1 := (a : H).property
    have he := congrArg (fun u : MulAut K => (u ⟨((b : H) : G), hb⟩ : G)) ha
    change ((a : H) : G) * ((b : H) : G) * ((a : H) : G)⁻¹ = ((b : H) : G) at he
    exact (mul_inv_eq_iff_eq_mul).mp he
  let : IsMulCommutative p.ker := ⟨⟨hcomm⟩⟩
  let : Group.IsSolvable p.ker := Group.isSolvable_of_comm hcomm
  let e := QuotientGroup.quotientKerEquivRange p
  let : Group.IsSolvable (H ⧸ p.ker) := Group.isSolvable_of_isSolvable_injective
    (f := e.toMonoidHom) e.injective
  let : Group.IsSolvable H := (Group.isSolvable_iff_subgroup_quotient p.ker).mpr ⟨inferInstance, inferInstance⟩
  exact ⟨H, inferInstance, inferInstance⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_DirectedDerivedSeries
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Directed unions with uniformly bounded derived series -/
namespace PolycyclicRecognition
open scoped commutatorElement
variable {G : Type} [Group G]

theorem sSup_ambientDerivedSeries_le_directed (C : Set (Subgroup G)) (hne : C.Nonempty)
    (hdir : DirectedOn (· ≤ ·) C) (n : ℕ) :
    ambientDerivedSeries (sSup C) n ≤ directedDerivedSeries C hne hdir n := by
  induction n with
  | zero =>
    rw [ambientDerivedSeries_zero]
    intro g hg
    obtain ⟨H, hH, hg⟩ := (Subgroup.mem_sSup_of_directedOn hne hdir).mp hg
    exact ⟨H, hH, by rwa [ambientDerivedSeries_zero]⟩
  | succ n ih =>
    rw [ambientDerivedSeries_succ]
    apply Subgroup.commutator_le.mpr
    intro x hx y hy
    obtain ⟨H, hH, hxH⟩ := ih hx
    obtain ⟨K, hK, hyK⟩ := ih hy
    obtain ⟨L, hL, hHL, hKL⟩ := hdir H hH K hK
    refine ⟨L, hL, ?_⟩
    rw [ambientDerivedSeries_succ]
    exact Subgroup.commutator_mem_commutator
      (ambientDerivedSeries_mono hHL n hxH) (ambientDerivedSeries_mono hKL n hyK)

theorem sSup_derivedSeries_eq_bot (C : Set (Subgroup G)) (hne : C.Nonempty)
    (hdir : DirectedOn (· ≤ ·) C) (n : ℕ) (hn : ∀ H ∈ C, derivedSeries H n = ⊥) :
    derivedSeries (sSup C : Subgroup G) n = ⊥ := by
  apply Subgroup.map_injective (f := (sSup C).subtype) Subtype.val_injective
  rw [Subgroup.map_bot]
  apply eq_bot_iff.mpr
  intro g hg
  obtain ⟨H, hH, hgH⟩ := sSup_ambientDerivedSeries_le_directed C hne hdir n hg
  simpa only [ambientDerivedSeries, hn H hH, Subgroup.map_bot] using hgH

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_BoundedSolvableRadical
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finite_templateSymmetryGroup _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteSubtypeLinearEquivRealIdMemSubgroupLinearSupportSymmetryGroup _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A characteristic solvable radical under a uniform derived-length bound -/
noncomputable section
namespace PolycyclicRecognition
variable {G : Type} [Group G]

theorem solvable_sup_of_normal (H K : Subgroup G) [H.Normal] [K.Normal]
    [Group.IsSolvable H] [Group.IsSolvable K] : Group.IsSolvable (H ⊔ K : Subgroup G) := by
  let S := K ⊔ H
  let N := H.subgroupOf S
  let e := Subgroup.subgroupOfEquivOfLe (show H ≤ S from le_sup_right)
  let : Group.IsSolvable N :=
    Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  let q := QuotientGroup.quotientInfEquivProdNormalQuotient K H
  let : Group.IsSolvable (S ⧸ N) :=
    Group.isSolvable_of_surjective (f := q.toMonoidHom) q.surjective
  have hs : Group.IsSolvable S := (Group.isSolvable_iff_subgroup_quotient N).mpr ⟨inferInstance, inferInstance⟩
  change Group.IsSolvable (K ⊔ H : Subgroup G) at hs
  rwa [sup_comm K H] at hs

theorem exists_characteristic_solvable_radical_of_bound (r : ℕ)
    (hbound : ∀ H : Subgroup G, Group.IsSolvable H → derivedSeries H r = ⊥) :
    ∃ R : Subgroup G, R.Characteristic ∧ Group.IsSolvable R ∧
      ∀ H : Subgroup G, H.Normal → Group.IsSolvable H → H ≤ R := by
  let P : Set (Subgroup G) := {H | H.Normal ∧ Group.IsSolvable H}
  obtain ⟨R, hR, hmax⟩ := zorn_le₀ P (by
    intro C hC hchain
    rcases C.eq_empty_or_nonempty with rfl | hne
    · exact ⟨⊥, ⟨inferInstance, inferInstance⟩, by simp⟩
    · have hn : (sSup C).Normal := Subgroup.sSup_normal C (fun H hH => (hC hH).1)
      have hs : Group.IsSolvable (sSup C : Subgroup G) :=
        ⟨r, sSup_derivedSeries_eq_bot C hne hchain.directedOn r
          (fun H hH => hbound H (hC hH).2)⟩
      exact ⟨sSup C, ⟨hn, hs⟩, fun H hH => le_sSup hH⟩)
  let := hR.1
  let := hR.2
  have hle (H : Subgroup G) (hn : H.Normal) (hs : Group.IsSolvable H) : H ≤ R := by
    let := hn
    let := hs
    have hj : Group.IsSolvable (R ⊔ H : Subgroup G) := solvable_sup_of_normal R H
    have he : R ⊔ H ≤ R := hmax ⟨inferInstance, hj⟩ le_sup_left
    exact le_sup_right.trans he
  have hchar : R.Characteristic := by
    apply Subgroup.characteristic_iff_map_le.mpr
    intro e
    have hs : Group.IsSolvable (R.map e.toMonoidHom) :=
      Group.isSolvable_of_surjective
        (f := (R.equivMapOfInjective e.toMonoidHom e.injective).toMonoidHom)
        (R.equivMapOfInjective e.toMonoidHom e.injective).surjective
    exact hle _ (Subgroup.Normal.map inferInstance e.toMonoidHom e.surjective) hs
  exact ⟨R, hchar, hR.2, hle⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_CoefficientNaturalCohomology
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Coefficient naturality for cohomology from a chosen resolution

The comparison uses one fixed homotopy equivalence with the bar resolution.
Consequently it commutes with every coefficient morphism.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits HomologicalComplex
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2100] Linear.homModule
variable {G : Type} [Group G] {A B : Rep.{0} ℤ G}

theorem coefficientNaturalCohomologyIso_naturality
    (P : ProjectiveResolution (Rep.trivial ℤ G ℤ)) (f : A ⟶ B) (n : ℕ) :
    groupCohomology.map (MonoidHom.id G) f n ≫
        (coefficientNaturalCohomologyIso P B n).hom =
      (coefficientNaturalCohomologyIso P A n).hom ≫
        homologyMap (repCochainPostcomp ℤ P.complex f) n := by
  let u : P.complex ⟶ Rep.barComplex ℤ G :=
    (ProjectiveResolution.homotopyEquiv P (Rep.barResolution ℤ G)).hom
  have hc : groupCohomology.cochainsMap (MonoidHom.id G) f ≫
      ((groupCohomology.inhomogeneousCochainsIso B).hom ≫ repCochainPrecomp ℤ u B) =
    ((groupCohomology.inhomogeneousCochainsIso A).hom ≫ repCochainPrecomp ℤ u A) ≫
      repCochainPostcomp ℤ P.complex f := by
    rw [← Category.assoc, inhomogeneousCochainsIso_coefficient,
      Category.assoc, ← repCochainPrecomp_postcomp, ← Category.assoc]
  change homologyMap (groupCohomology.cochainsMap (MonoidHom.id G) f) n ≫
      (homologyMap (groupCohomology.inhomogeneousCochainsIso B).hom n ≫
        homologyMap (repCochainPrecomp ℤ u B) n) =
    (homologyMap (groupCohomology.inhomogeneousCochainsIso A).hom n ≫
      homologyMap (repCochainPrecomp ℤ u A) n) ≫
        homologyMap (repCochainPostcomp ℤ P.complex f) n
  simpa only [homologyMap_comp] using congrArg (fun c => homologyMap c n) hc

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_CoefficientConnectingNaturality
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Connecting homomorphisms commute with the chosen-resolution comparison -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits HomologicalComplex
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2100] Linear.homModule
variable {G : Type} [Group G]

theorem coefficientNaturalCochainMap_homology
    (P : ProjectiveResolution (Rep.trivial ℤ G ℤ)) (A : Rep.{0} ℤ G) (n : ℕ) :
    homologyMap (coefficientNaturalCochainMap P A) n =
      (coefficientNaturalCohomologyIso P A n).hom := by
  change homologyMap ((groupCohomology.inhomogeneousCochainsIso A).hom ≫
      repCochainPrecomp ℤ (ProjectiveResolution.homotopyEquiv P (Rep.barResolution ℤ G)).hom A) n =
    homologyMap (groupCohomology.inhomogeneousCochainsIso A).hom n ≫
      homologyMap (repCochainPrecomp ℤ
        (ProjectiveResolution.homotopyEquiv P (Rep.barResolution ℤ G)).hom A) n
  exact homologyMap_comp _ _ _

theorem coefficientNaturalCohomologyIso_connecting
    (P : ProjectiveResolution (Rep.trivial ℤ G ℤ))
    (S : ShortComplex (Rep.{0} ℤ G)) (hS : S.ShortExact) (n : ℕ) :
    groupCohomology.δ hS n (n + 1) rfl ≫ (coefficientNaturalCohomologyIso P S.X₁ (n + 1)).hom =
      (coefficientNaturalCohomologyIso P S.X₃ n).hom ≫
        (resolutionCoefficientSequence_shortExact P S hS).δ n (n + 1) rfl := by
  have h := HomologicalComplex.HomologySequence.δ_naturality
    (coefficientComparisonSequenceMap P S)
    (groupCohomology.map_cochainsFunctor_shortExact hS)
    (resolutionCoefficientSequence_shortExact P S hS) n (n + 1) rfl
  change groupCohomology.δ hS n (n + 1) rfl ≫
      homologyMap (coefficientNaturalCochainMap P S.X₁) (n + 1) =
    homologyMap (coefficientNaturalCochainMap P S.X₃) n ≫
      (resolutionCoefficientSequence_shortExact P S hS).δ n (n + 1) rfl at h
  erw [coefficientNaturalCochainMap_homology, coefficientNaturalCochainMap_homology] at h
  exact h

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_PresentationKernelMap
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.booleanPartitionStage_projective _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.horseshoeCover_projective _root_.OAI.PolycyclicRecognition.integralRepresentationSum_projective _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.normalizedFreeRepresentation_countable _root_.OAI.PolycyclicRecognition.normalizedFreeRepresentation_integral_projective _root_.OAI.PolycyclicRecognition.normalizedSyzygy_countable _root_.OAI.PolycyclicRecognition.normalizedSyzygy_integral_projective _root_.OAI.PolycyclicRecognition.normalizedSyzygy_projective _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The stable kernel map of a short exact sequence

A lift of the normalized free cover of the quotient gives a map from its
syzygy to the submodule. Changing the lift changes this map by a projective
factor, and the construction is natural in the stable quotient.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G]

theorem presentationKernelMapOfLift_stable_natural
    {S T : ShortComplex (Rep.{0} ℤ G)} (hS : S.ShortExact) (hT : T.ShortExact)
    (φ : S ⟶ T)
    (lS : normalizedFreeRepresentation S.X₃ ⟶ S.X₂)
    (hlS : lS ≫ S.g = normalizedFreeAugmentation S.X₃)
    (lT : normalizedFreeRepresentation T.X₃ ⟶ T.X₂)
    (hlT : lT ≫ T.g = normalizedFreeAugmentation T.X₃) :
    stableRepresentationClass _ _
      (normalizedSyzygyMap φ.τ₃ ≫ presentationKernelMapOfLift T hT lT hlT) =
    stableRepresentationClass _ _
      (presentationKernelMapOfLift S hS lS hlS ≫ φ.τ₁) := by
  let : Mono T.f := hT.mono_f
  let d := normalizedFreeMap φ.τ₃ ≫ lT - lS ≫ φ.τ₂
  have hd : d ≫ T.g = 0 := by
    dsimp only [d]
    rw [Preadditive.sub_comp, Category.assoc, hlT,
      Category.assoc, φ.comm₂₃, ← Category.assoc, hlS,
      normalizedFreeAugmentation_natural, sub_self]
  let v := hT.exact.lift d hd
  apply (stableRepresentationClass_eq_iff_projective_factor _ _).mpr
  refine ⟨normalizedFreeRepresentation S.X₃, inferInstance,
    kernel.ι (normalizedFreeAugmentation S.X₃), v, ?_⟩
  apply (cancel_mono T.f).mp
  rw [Category.assoc, hT.exact.lift_f, Preadditive.sub_comp,
    Category.assoc, presentationKernelMapOfLift_f,
    ← Category.assoc, normalizedSyzygyMap_ι, Category.assoc,
    Category.assoc, φ.comm₁₂, presentationKernelMapOfLift_f_assoc]
  exact Preadditive.comp_sub _ _ _

theorem presentationKernelMap_stable_natural
    {S T : ShortComplex (Rep.{0} ℤ G)} (hS : S.ShortExact) (hT : T.ShortExact)
    (φ : S ⟶ T) :
    stableRepresentationClass _ _ (normalizedSyzygyMap φ.τ₃ ≫ presentationKernelMap T hT) =
      stableRepresentationClass _ _ (presentationKernelMap S hS ≫ φ.τ₁) :=
  presentationKernelMapOfLift_stable_natural hS hT φ _ _ _ _

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_NormalizedSyzygyIteration
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.iteratedNormalizedSyzygy_integral_projective _root_.OAI.PolycyclicRecognition.iteratedNormalizedSyzygy_projective _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.normalizedCohomologyForward_directed _root_.OAI.PolycyclicRecognition.normalizedSyzygy_countable _root_.OAI.PolycyclicRecognition.normalizedSyzygy_integral_projective _root_.OAI.PolycyclicRecognition.normalizedSyzygy_projective _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.shiftedCohomologyForward_directed _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Moving one normalized syzygy across an iterated syzygy -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G]

theorem normalizedSyzygyIterationIso_natural {A B : Rep.{0} ℤ G}
    (f : A ⟶ B) (n : ℕ) :
    (iteratedNormalizedSyzygy n).map (normalizedSyzygyMap f) ≫
        (normalizedSyzygyIterationIso B n).hom =
      (normalizedSyzygyIterationIso A n).hom ≫ (iteratedNormalizedSyzygy (n + 1)).map f := by
  have h := (eqToHom (normalizedSyzygy_iterate_comm (G := G) n)).naturality f
  rw [eqToHom_app, eqToHom_app] at h
  exact h

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_FinitePresentationSequentialLimit
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instNonemptyBases _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite presentation and sequential module limits

Finite generators can be moved to one stage, and finitely many relations
vanish at one later stage. The ring need not be commutative, as required for
integral group rings.
-/
noncomputable section
namespace PolycyclicRecognition

variable {R : Type*} [Ring R] {D : ℕ → Type*}
  [∀ i, AddCommGroup (D i)] [∀ i, Module R (D i)]
  (f : ∀ i j, i ≤ j → D i →ₗ[R] D j)
  [DirectedSystem D (fun i j h => f i j h)]

omit [DirectedSystem D (fun i j h => f i j h)] in
theorem sequentialLimit_lift_finite_free (n : ℕ)
    (u : (Fin n → R) →ₗ[R] Module.DirectLimit D f) :
    ∃ (i : ℕ) (v : (Fin n → R) →ₗ[R] D i),
      (Module.DirectLimit.of R ℕ D f i).comp v = u := by
  classical
  let b := Pi.basisFun R (Fin n)
  choose k x hx using fun a : Fin n => Module.DirectLimit.exists_of (u (b a))
  let i := Finset.univ.sup k
  have hk (a : Fin n) : k a ≤ i := Finset.le_sup (f := k) (Finset.mem_univ a)
  refine ⟨i, b.constr ℕ (fun a => f (k a) i (hk a) (x a)), ?_⟩
  apply b.ext
  intro a
  simp only [LinearMap.comp_apply, Module.Basis.constr_basis]
  rw [Module.DirectLimit.of_f, hx]

theorem sequentialLimit_eventually_zero_finite
    {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (i : ℕ) (u : M →ₗ[R] D i)
    (hu : (Module.DirectLimit.of R ℕ D f i).comp u = 0) :
    ∃ (j : ℕ) (hij : i ≤ j), (f i j hij).comp u = 0 := by
  classical
  obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' R M
  let b := Pi.basisFun R (Fin n)
  have hz (a : Fin n) : Module.DirectLimit.of R ℕ D f i (u (π (b a))) = 0 :=
    LinearMap.congr_fun hu (π (b a))
  choose k hk he using fun a => Module.DirectLimit.of.zero_exact (hz a)
  let j := max i (Finset.univ.sup k)
  have hij : i ≤ j := le_max_left _ _
  have hkj (a : Fin n) : k a ≤ j :=
    (Finset.le_sup (f := k) (Finset.mem_univ a)).trans (le_max_right _ _)
  have hzero : ((f i j hij).comp u).comp π = 0 := by
    apply b.ext
    intro a
    change f i j hij (u (π (b a))) = 0
    rw [← DirectedSystem.map_map (f := fun i j h => f i j h) (hk a) (hkj a)]
    rw [he a, map_zero]
  refine ⟨j, hij, ?_⟩
  ext x
  obtain ⟨y, rfl⟩ := hπ x
  exact LinearMap.congr_fun hzero y

theorem sequentialLimit_lift_finitelyPresented
    {M : Type*} [AddCommGroup M] [Module R M] [Module.FinitePresentation R M]
    (u : M →ₗ[R] Module.DirectLimit D f) :
    ∃ (i : ℕ) (v : M →ₗ[R] D i), (Module.DirectLimit.of R ℕ D f i).comp v = u := by
  obtain ⟨n, m, π, r, hπ, hr⟩ := Module.FinitePresentation.exists_fin' R M
  obtain ⟨i, v, hv⟩ := sequentialLimit_lift_finite_free f n (u.comp π)
  have hvr : (Module.DirectLimit.of R ℕ D f i).comp (v.comp r) = 0 := by
    rw [← LinearMap.comp_assoc, hv, LinearMap.comp_assoc]
    have hπr : π.comp r = 0 := by
      apply LinearMap.ext
      intro x
      exact hr.apply_apply_eq_zero x
    rw [hπr, LinearMap.comp_zero]
  obtain ⟨j, hij, hj⟩ := sequentialLimit_eventually_zero_finite f i (v.comp r) hvr
  let w := (f i j hij).comp v
  have hker : LinearMap.ker π ≤ LinearMap.ker w := by
    intro x hx
    obtain ⟨y, rfl⟩ := (hr x).mp hx
    exact LinearMap.congr_fun hj y
  let v' := (Submodule.liftQ (LinearMap.ker π) w hker).comp
    (LinearMap.quotKerEquivOfSurjective π hπ).symm.toLinearMap
  refine ⟨j, v', ?_⟩
  ext x
  obtain ⟨y, rfl⟩ := hπ x
  change Module.DirectLimit.of R ℕ D f j
    ((Submodule.liftQ (LinearMap.ker π) w hker)
      ((LinearMap.quotKerEquivOfSurjective π hπ).symm (π y))) = u (π y)
  rw [LinearMap.quotKerEquivOfSurjective_symm_apply]
  change Module.DirectLimit.of R ℕ D f j (f i j hij (v y)) = u (π y)
  rw [Module.DirectLimit.of_f]
  exact LinearMap.congr_fun hv y

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_FinitePresentationSyzygies
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite presentation of integral resolution syzygies

Two consecutive finite projective terms give a finitely presented quotient
syzygy. This supplies the finite-presentation input for passing Hom through
directed colimits in the FP-infinity argument.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
open scoped MonoidAlgebra
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G]

theorem projectiveRepresentation_module (A : Rep.{0} ℤ G) [Projective A] :
    Module.Projective ℤ[G] A.ρ.asModule := by
  have h : Projective (Rep.toModuleMonoidAlgebra.obj A) :=
    (Rep.equivalenceModuleMonoidAlgebra.map_projective_iff A).mpr inferInstance
  let := h
  exact ModuleCat.projective_of_module_projective (Rep.toModuleMonoidAlgebra.obj A)

theorem projectiveRepresentation_finitePresentation (A : Rep.{0} ℤ G) [Projective A]
    (hA : IntegralRepresentationFinite G A) : Module.FinitePresentation ℤ[G] A.ρ.asModule := by
  let := projectiveRepresentation_module A
  let : Module.Finite ℤ[G] A.ρ.asModule := hA
  exact Module.finitePresentation_of_projective ℤ[G] A.ρ.asModule

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_SequentialRepresentationColimit
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.IntegralProjectiveTower.instDirectedSystemNatCohomologyStageCoeLinearMapIntIdForward _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.SequentialRepresentationDiagram.ColimitCocone.telescopeAugmentation_epi _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.moduleTailMap_directed _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.normalizedCohomologyForward_directed _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.shiftedCohomologyForward_directed _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Concrete sequential colimits of representations

Only the two elementwise properties used in coefficient calculations are
packaged: every element comes from a stage, and zero is detected at a later
stage. They identify the cocone with the actual group-ring module colimit.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
open scoped MonoidAlgebra
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G]
namespace SequentialRepresentationDiagram
variable (D : SequentialRepresentationDiagram G) (A : Rep.{0} ℤ G)

namespace ColimitCocone
variable {D A} (c : D.ColimitCocone A)

theorem lift_finitelyPresented (B : Rep.{0} ℤ G)
    [Module.FinitePresentation ℤ[G] B.ρ.asModule] (u : B ⟶ A) :
    ∃ (i : ℕ) (v : B ⟶ D.obj i), v ≫ c.ι i = u := by
  let u' := representationModuleHomEquiv ℤ G B A u
  obtain ⟨i, v, hv⟩ := sequentialLimit_lift_finitelyPresented D.moduleMap
    (c.moduleEquiv.symm.toLinearMap.comp u')
  refine ⟨i, (representationModuleHomEquiv ℤ G B (D.obj i)).symm v, ?_⟩
  apply (representationModuleHomEquiv ℤ G B A).injective
  apply LinearMap.ext
  intro b
  have he := LinearMap.congr_fun hv b
  have he' := congrArg c.moduleEquiv he
  change c.moduleEquiv (Module.DirectLimit.of ℤ[G] ℕ _ D.moduleMap i (v b)) =
    c.moduleEquiv (c.moduleEquiv.symm (u' b)) at he'
  rw [c.moduleEquiv.apply_symm_apply] at he'
  change c.moduleLift (Module.DirectLimit.of ℤ[G] ℕ _ D.moduleMap i (v b)) = u' b at he'
  rw [c.moduleLift_of] at he'
  exact he'

theorem eventually_zero_hom (B : Rep.{0} ℤ G) [Module.Finite ℤ[G] B.ρ.asModule]
    (i : ℕ) (u : B ⟶ D.obj i) (hu : u ≫ c.ι i = 0) :
    ∃ (j : ℕ) (hij : i ≤ j), u ≫ D.map i j hij = 0 := by
  let u' := representationModuleHomEquiv ℤ G B (D.obj i) u
  have hz : (Module.DirectLimit.of ℤ[G] ℕ _ D.moduleMap i).comp u' = 0 := by
    apply LinearMap.ext
    intro b
    apply c.moduleLift_bijective.1
    change c.moduleLift (Module.DirectLimit.of ℤ[G] ℕ _ D.moduleMap i (u' b)) = c.moduleLift 0
    rw [map_zero]
    rw [c.moduleLift_of]
    have he := congrArg (fun f => representationModuleHomEquiv ℤ G B A f b) hu
    exact he
  obtain ⟨j, hij, hj⟩ := sequentialLimit_eventually_zero_finite D.moduleMap i u' hz
  refine ⟨j, hij, ?_⟩
  apply (representationModuleHomEquiv ℤ G B (D.obj j)).injective
  exact hj

end ColimitCocone
end SequentialRepresentationDiagram
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_CompletedCohomologyProjective
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instNonemptyBases _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.booleanPartitionStage_projective _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.horseshoeCover_projective _root_.OAI.PolycyclicRecognition.integralRepresentationSum_projective _root_.OAI.PolycyclicRecognition.iteratedNormalizedSyzygy_integral_projective _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.normalizedFreeRepresentation_countable _root_.OAI.PolycyclicRecognition.normalizedFreeRepresentation_integral_projective _root_.OAI.PolycyclicRecognition.normalizedSyzygy_countable _root_.OAI.PolycyclicRecognition.normalizedSyzygy_integral_projective _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.shiftedCohomologyForward_directed _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.SequentialRepresentationDiagram.ColimitCocone.iteratedNormalizedSyzygy_ι _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.normalizedGroupIdentityClass_comparison _root_.OAI.PolycyclicRecognition.normalizedResolutionComplex_d _root_.OAI.PolycyclicRecognition.normalizedStableSyzygyIterate_class _root_.OAI.PolycyclicRecognition.normalizedSyzygyIterationIso_succ _root_.OAI.PolycyclicRecognition.shiftedCohomologyStageMap_id _root_.OAI.PolycyclicRecognition.shiftedCompletedCohomologyMap_of _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Complete cohomology vanishes on projective coefficients -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G]

theorem normalizedSyzygy_delta_eq_zero (A : Rep.{0} ℤ G) [Projective A] (n : ℕ) :
    groupCohomology.δ (normalizedSyzygySequence_shortExact A) n (n + 1) rfl = 0 := by
  let s := Projective.factorThru (𝟙 A) (normalizedFreeAugmentation A)
  have hs : s ≫ normalizedFreeAugmentation A = 𝟙 A := Projective.factorThru_comp _ _
  let F := groupCohomology.functor ℤ G n
  let δ : F.obj A ⟶ groupCohomology (normalizedSyzygy A) (n + 1) :=
    groupCohomology.δ (normalizedSyzygySequence_shortExact A) n (n + 1) rfl
  change δ = 0
  have hs' : F.map s ≫ F.map (normalizedFreeAugmentation A) = 𝟙 _ := by
    rw [← F.map_comp, hs, F.map_id]
  have hz := (groupCohomology.mapShortComplex₃
    (normalizedSyzygySequence_shortExact A) (rfl : n + 1 = n + 1)).zero
  change F.map (normalizedFreeAugmentation A) ≫ δ = 0 at hz
  have he : (F.map s ≫ F.map (normalizedFreeAugmentation A)) ≫ δ = 0 := by
    rw [Category.assoc, hz, comp_zero]
  simpa only [hs', Category.id_comp] using he

theorem iteratedNormalizedSyzygy_projectiveDimension
    (A : Rep.{0} ℤ G) (n d : ℕ) (hA : HasProjectiveDimensionLE A (n + d)) :
    HasProjectiveDimensionLE ((iteratedNormalizedSyzygy n).obj A) d := by
  induction n generalizing d with
  | zero => simpa only [Nat.zero_add, iteratedNormalizedSyzygy, Functor.id_obj] using hA
  | succ n ih =>
    have hA' : HasProjectiveDimensionLE A (n + (d + 1)) := by
      simpa only [Nat.succ_add, Nat.add_succ] using hA
    have hprev := ih (d + 1) hA'
    exact (normalizedSyzygySequence_shortExact ((iteratedNormalizedSyzygy n).obj A)).hasProjectiveDimensionLT_X₁ (d + 1)
        (hasProjectiveDimensionLT_of_ge
          (normalizedFreeRepresentation ((iteratedNormalizedSyzygy n).obj A))
          1 (d + 1) (by omega)) hprev

theorem completedCohomology_subsingleton_of_finite_projectiveDimension
    (A : Rep.{0} ℤ G) (d : ℕ) [HasProjectiveDimensionLE A d] :
    Subsingleton (CompletedCohomology A) := by
  apply subsingleton_of_forall_eq (0 : CompletedCohomology A)
  intro z
  obtain ⟨i, x, rfl⟩ := Module.DirectLimit.exists_of z
  let m := max i d
  have hAm : HasProjectiveDimensionLE A (m + 0) :=
    hasProjectiveDimensionLT_of_ge A (d + 1) (m + 0 + 1)
      (by dsimp [m]; omega)
  let : Projective ((iteratedNormalizedSyzygy m).obj A) :=
    (projective_iff_hasProjectiveDimensionLE_zero _).mpr
      (iteratedNormalizedSyzygy_projectiveDimension A m 0 hAm)
  let y := normalizedCohomologyForward A i m (le_max_left i d) x
  have hz : normalizedCohomologyForward A m (m + 1) (Nat.le_succ m) y = 0 := by
    change Nat.leRecOn (C := normalizedCohomologyStage A) (Nat.le_succ m)
      (fun {k} => (normalizedSyzygyConnecting A k).hom) y = 0
    rw [Nat.leRecOn_succ (le_refl m), Nat.leRecOn_self]
    change (normalizedSyzygyConnecting A m).hom y = 0
    rw [show normalizedSyzygyConnecting A m = 0 from
      normalizedSyzygy_delta_eq_zero ((iteratedNormalizedSyzygy m).obj A) m]
    rfl
  have he := Module.DirectLimit.of_f (R := ℤ) (ι := ℕ)
    (G := normalizedCohomologyStage A) (f := normalizedCohomologyForward A)
    (hij := Nat.le_succ m) (x := y)
  rw [hz, map_zero] at he
  have hi := Module.DirectLimit.of_f (R := ℤ) (ι := ℕ)
    (G := normalizedCohomologyStage A) (f := normalizedCohomologyForward A)
    (hij := le_max_left i d) (x := x)
  exact hi.symm.trans he.symm

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_NormalizedIdentityClass
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.iteratedNormalizedSyzygy_integral_projective _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.shiftedCohomologyForward_directed _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.SequentialRepresentationDiagram.ColimitCocone.iteratedNormalizedSyzygy_ι _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalizedGroupIdentityClass_comparison _root_.OAI.PolycyclicRecognition.normalizedStableSyzygyIterate_class _root_.OAI.PolycyclicRecognition.normalizedSyzygyIterationIso_succ _root_.OAI.PolycyclicRecognition.shiftedCohomologyStageMap_id _root_.OAI.PolycyclicRecognition.shiftedCompletedCohomologyMap_of _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Identity cocycles in the normalized resolution

The projection onto the n-th syzygy is a cocycle. If its class vanishes in a
positive degree, the next kernel inclusion splits; this gives a projective
syzygy and hence finite integral dimension for the trivial coefficient.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits HomologicalComplex
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2100] Linear.homModule
variable {G : Type} [Group G]

theorem normalizedIdentityCycle_projection (A : Rep.{0} ℤ G) (n : ℕ) :
    ((normalizedResolutionComplex A).linearYonedaObj ℤ
      ((iteratedNormalizedSyzygy n).obj A)).iCycles n (normalizedIdentityCycle A n) =
        normalizedResolutionProjection A n := by
  let C := (normalizedResolutionComplex A).linearYonedaObj ℤ
    ((iteratedNormalizedSyzygy n).obj A)
  exact C.i_cyclesMk (normalizedResolutionProjection A n) (n + 1) (by simp)
    (by exact normalizedResolution_d_projection A n)

theorem cochain_boundary_of_class_zero (C : CochainComplex (ModuleCat ℤ) ℕ) (n : ℕ)
    (z : C.cycles (n + 1)) (hz : C.homologyπ (n + 1) z = 0) :
    ∃ y : C.X n, C.d n (n + 1) y = C.iCycles (n + 1) z := by
  let S := ShortComplex.mk (C.toCycles n (n + 1)) (C.homologyπ (n + 1))
    (C.toCycles_comp_homologyπ n (n + 1))
  have hS : S.Exact := ShortComplex.exact_of_g_is_cokernel _
    (C.homologyIsCokernel n (n + 1) (by simp))
  obtain ⟨y, hy⟩ := (ShortComplex.moduleCat_exact_iff S).mp hS z hz
  refine ⟨y, ?_⟩
  have he := congrArg (fun v => C.iCycles (n + 1) v) hy
  have hc := congrArg (fun v => v.hom y) (C.toCycles_i n (n + 1))
  exact hc.symm.trans he

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_SequentialCohomologyKernel
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.SequentialRepresentationDiagram.ColimitCocone.telescopeAugmentation_epi _root_.OAI.PolycyclicRecognition.booleanPartitionStage_projective _root_.OAI.PolycyclicRecognition.cyclicTopHomologyInjection_mono _root_.OAI.PolycyclicRecognition.finiteResolution_single_supported _root_.OAI.PolycyclicRecognition.finiteTruncationAugmentation_quasiIso _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.horseshoeCover_projective _root_.OAI.PolycyclicRecognition.integralRepresentationSum_projective _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.repCofiber_projective _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Detecting a zero cohomology class at a finite coefficient stage

For positive degrees, a boundary in the coefficient colimit can be lifted to
one finite stage. Finite presentation lifts the cochain, and finite generation
kills the resulting error at a later stage.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped MonoidAlgebra
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2100] Linear.homModule
variable {G : Type} [Group G]

theorem cochain_class_zero_of_boundary (C : CochainComplex (ModuleCat ℤ) ℕ) (n : ℕ)
    (z : C.cycles (n + 1)) (y : C.X n) (hy : C.d n (n + 1) y = C.iCycles (n + 1) z) :
    C.homologyπ (n + 1) z = 0 := by
  have he : C.toCycles n (n + 1) y = z := by
    apply (ModuleCat.mono_iff_injective (C.iCycles (n + 1))).mp inferInstance
    have h := ConcreteCategory.congr_hom (C.toCycles_i n (n + 1)) y
    exact h.trans hy
  rw [← he]
  exact ConcreteCategory.congr_hom (C.toCycles_comp_homologyπ n (n + 1)) y

theorem resolution_cohomologyMap_zero_of_boundary
    (P : ProjectiveResolution (trivialIntegral G)) (n : ℕ)
    {A B : Rep.{0} ℤ G} (f : A ⟶ B)
    (z : (P.complex.linearYonedaObj ℤ A).cycles (n + 1))
    (y : P.complex.X n ⟶ B)
    (hy : P.complex.d (n + 1) n ≫ y =
      (P.complex.linearYonedaObj ℤ A).iCycles (n + 1) z ≫ f) :
    homologyMap (repCochainPostcomp ℤ P.complex f) (n + 1)
      ((P.complex.linearYonedaObj ℤ A).homologyπ (n + 1) z) = 0 := by
  let φ := repCochainPostcomp ℤ P.complex f
  let C := P.complex.linearYonedaObj ℤ B
  have hd : C.d n (n + 1) y = C.iCycles (n + 1) (cyclesMap φ (n + 1) z) := by
    have he := ConcreteCategory.congr_hom (cyclesMap_i φ (n + 1)) z
    change C.iCycles (n + 1) (cyclesMap φ (n + 1) z) =
      (P.complex.linearYonedaObj ℤ A).iCycles (n + 1) z ≫ f at he
    exact hy.trans he.symm
  have hz := cochain_class_zero_of_boundary C n (cyclesMap φ (n + 1) z) y hd
  have he := ConcreteCategory.congr_hom (homologyπ_naturality φ (n + 1)) z
  change homologyMap φ (n + 1) ((P.complex.linearYonedaObj ℤ A).homologyπ (n + 1) z) =
    C.homologyπ (n + 1) (cyclesMap φ (n + 1) z) at he
  exact he.trans hz

theorem finiteResolutionCohomology_colimit_kernel
    (D : SequentialRepresentationDiagram G) (A : Rep.{0} ℤ G) (c : D.ColimitCocone A)
    (P : ProjectiveResolution (trivialIntegral G)) (n : ℕ)
    [Module.FinitePresentation ℤ[G] (P.complex.X n).ρ.asModule]
    [Module.Finite ℤ[G] (P.complex.X (n + 1)).ρ.asModule]
    (i : ℕ) (x : (P.complex.linearYonedaObj ℤ (D.obj i)).homology (n + 1))
    (hx : homologyMap (repCochainPostcomp ℤ P.complex (c.ι i)) (n + 1) x = 0) :
    ∃ (j : ℕ) (hij : i ≤ j),
      homologyMap (repCochainPostcomp ℤ P.complex (D.map i j hij)) (n + 1) x = 0 := by
  let Ci := P.complex.linearYonedaObj ℤ (D.obj i)
  let C := P.complex.linearYonedaObj ℤ A
  let φ := repCochainPostcomp ℤ P.complex (c.ι i)
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective (Ci.homologyπ (n + 1))).mp inferInstance x
  have hz : C.homologyπ (n + 1) (cyclesMap φ (n + 1) z) = 0 := by
    have he := ConcreteCategory.congr_hom (homologyπ_naturality φ (n + 1)) z
    change homologyMap φ (n + 1) (Ci.homologyπ (n + 1) z) =
      C.homologyπ (n + 1) (cyclesMap φ (n + 1) z) at he
    exact he.symm.trans hx
  obtain ⟨y, hy⟩ := cochain_boundary_of_class_zero C n (cyclesMap φ (n + 1) z) hz
  let y' : P.complex.X n ⟶ A := y
  let u : P.complex.X (n + 1) ⟶ D.obj i := Ci.iCycles (n + 1) z
  have hdy : P.complex.d (n + 1) n ≫ y' = u ≫ c.ι i := by
    have he := ConcreteCategory.congr_hom (cyclesMap_i φ (n + 1)) z
    exact hy.trans he
  obtain ⟨j, v, hv⟩ := c.lift_finitelyPresented (P.complex.X n) y'
  let k := max i j
  let vk := v ≫ D.map j k (le_max_right i j)
  let uk := u ≫ D.map i k (le_max_left i j)
  let r := uk - P.complex.d (n + 1) n ≫ vk
  have hr : r ≫ c.ι k = 0 := by
    change (uk - P.complex.d (n + 1) n ≫ vk) ≫ c.ι k = 0
    rw [Preadditive.sub_comp]
    change (u ≫ D.map i k _) ≫ c.ι k -
      (P.complex.d (n + 1) n ≫ (v ≫ D.map j k _)) ≫ c.ι k = 0
    rw [Category.assoc, c.comm, Category.assoc, Category.assoc, c.comm,
      hv, hdy, sub_self]
  obtain ⟨l, hkl, hl⟩ := c.eventually_zero_hom (P.complex.X (n + 1)) k r hr
  refine ⟨l, (le_max_left i j).trans hkl, ?_⟩
  apply resolution_cohomologyMap_zero_of_boundary P n (D.map i l _) z
    (vk ≫ D.map k l hkl)
  have he : uk ≫ D.map k l hkl = (P.complex.d (n + 1) n ≫ vk) ≫ D.map k l hkl := by
    exact sub_eq_zero.mp ((Preadditive.sub_comp _ _ _).symm.trans hl)
  change P.complex.d (n + 1) n ≫ vk ≫ D.map k l hkl = u ≫ D.map i l _
  rw [← Category.assoc, ← he]
  change (u ≫ D.map i k _) ≫ D.map k l _ = u ≫ D.map i l _
  rw [Category.assoc, D.map_comp]

theorem TypeFPInfinity.cohomology_colimit_kernel
    (hG : TypeFPInfinity G) (D : SequentialRepresentationDiagram G)
    (A : Rep.{0} ℤ G) (c : D.ColimitCocone A) (n i : ℕ)
    (x : groupCohomology (D.obj i) (n + 1))
    (hx : groupCohomology.map (MonoidHom.id G) (c.ι i) (n + 1) x = 0) :
    ∃ (j : ℕ) (hij : i ≤ j),
      groupCohomology.map (MonoidHom.id G) (D.map i j hij) (n + 1) x = 0 := by
  obtain ⟨P, hP⟩ := hG (n + 1)
  let : Module.FinitePresentation ℤ[G] (P.complex.X n).ρ.asModule :=
    projectiveRepresentation_finitePresentation _ (hP n (by omega))
  let : Module.Finite ℤ[G] (P.complex.X (n + 1)).ρ.asModule := hP (n + 1) le_rfl
  have hz : homologyMap (repCochainPostcomp ℤ P.complex (c.ι i)) (n + 1)
      ((coefficientNaturalCohomologyIso P (D.obj i) (n + 1)).hom x) = 0 := by
    have he := ConcreteCategory.congr_hom
      (coefficientNaturalCohomologyIso_naturality P (c.ι i) (n + 1)) x
    change (coefficientNaturalCohomologyIso P A (n + 1)).hom
        (groupCohomology.map (MonoidHom.id G) (c.ι i) (n + 1) x) =
      homologyMap (repCochainPostcomp ℤ P.complex (c.ι i)) (n + 1)
        ((coefficientNaturalCohomologyIso P (D.obj i) (n + 1)).hom x) at he
    rw [hx, map_zero] at he
    exact he.symm
  obtain ⟨j, hij, hj⟩ := finiteResolutionCohomology_colimit_kernel D A c P n i
    ((coefficientNaturalCohomologyIso P (D.obj i) (n + 1)).hom x) hz
  refine ⟨j, hij, ?_⟩
  apply (coefficientNaturalCohomologyIso P (D.obj j) (n + 1)).toLinearEquiv.injective
  change (coefficientNaturalCohomologyIso P (D.obj j) (n + 1)).hom.hom
      (groupCohomology.map (MonoidHom.id G) (D.map i j hij) (n + 1) x) =
    (coefficientNaturalCohomologyIso P (D.obj j) (n + 1)).hom.hom 0
  have he := ConcreteCategory.congr_hom
    (coefficientNaturalCohomologyIso_naturality P (D.map i j hij) (n + 1)) x
  change (coefficientNaturalCohomologyIso P (D.obj j) (n + 1)).hom
      (groupCohomology.map (MonoidHom.id G) (D.map i j hij) (n + 1) x) =
    homologyMap (repCochainPostcomp ℤ P.complex (D.map i j hij)) (n + 1)
      ((coefficientNaturalCohomologyIso P (D.obj i) (n + 1)).hom x) at he
  simpa only [map_zero, hj] using he

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_CompletedCohomologyColimitKernel
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instNonemptyBases _root_.OAI.PolycyclicRecognition.IntegralProjectiveTower.instDirectedSystemNatCohomologyStageCoeLinearMapIntIdForward _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.SequentialRepresentationDiagram.ColimitCocone.telescopeAugmentation_epi _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.iteratedNormalizedSyzygy_integral_projective _root_.OAI.PolycyclicRecognition.moduleTailMap_directed _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalizedFreeRepresentation_countable _root_.OAI.PolycyclicRecognition.normalizedFreeRepresentation_integral_projective _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.shiftedCohomologyForward_directed _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Detecting zero complete classes in a coefficient colimit

Under FP-infinity, a complete class whose image in the coefficient colimit is
zero already dies at a finite coefficient stage.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G]

theorem normalizedCohomologyForward_comp (A : Rep.{0} ℤ G) (i j k : ℕ)
    (hij : i ≤ j) (hjk : j ≤ k) (x : normalizedCohomologyStage A i) :
    normalizedCohomologyForward A j k hjk (normalizedCohomologyForward A i j hij x) =
      normalizedCohomologyForward A i k (hij.trans hjk) x :=
  Module.DirectedSystem.map_map (f := normalizedCohomologyForward A) hij hjk x

theorem TypeFPInfinity.completedCohomology_colimit_kernel
    (hG : TypeFPInfinity G) (D : SequentialRepresentationDiagram G)
    (A : Rep.{0} ℤ G) (c : D.ColimitCocone A) (i : ℕ)
    (x : CompletedCohomology (D.obj i)) (hx : completedCohomologyMap (c.ι i) x = 0) :
    ∃ (j : ℕ) (hij : i ≤ j), completedCohomologyMap (D.map i j hij) x = 0 := by
  obtain ⟨n, y, rfl⟩ := Module.DirectLimit.exists_of x
  rw [completedCohomologyMap_of] at hx
  obtain ⟨m, hnm, hm⟩ := Module.DirectLimit.of.zero_exact hx
  let z := normalizedCohomologyForward (D.obj i) n (m + 1) (hnm.trans (Nat.le_succ m)) y
  have hz : normalizedCohomologyStageMap (c.ι i) (m + 1) z = 0 := by
    rw [normalizedCohomologyForward_natural]
    rw [← normalizedCohomologyForward_comp A n m (m + 1) hnm (Nat.le_succ m), hm, map_zero]
  let E := D.mapFunctor (iteratedNormalizedSyzygy (m + 1))
  let ec := c.iteratedNormalizedSyzygy (m + 1)
  have hz' : groupCohomology.map (MonoidHom.id G) (ec.ι i) (m + 1) z = 0 := by
    rw [SequentialRepresentationDiagram.ColimitCocone.iteratedNormalizedSyzygy_ι]
    exact hz
  obtain ⟨j, hij, hj⟩ := hG.cohomology_colimit_kernel E
    ((iteratedNormalizedSyzygy (m + 1)).obj A) ec m i z hz'
  refine ⟨j, hij, ?_⟩
  have hrepr := Module.DirectLimit.of_f (R := ℤ) (ι := ℕ)
    (G := normalizedCohomologyStage (D.obj i)) (f := normalizedCohomologyForward (D.obj i))
    (hij := hnm.trans (Nat.le_succ m)) (x := y)
  change Module.DirectLimit.of ℤ ℕ _ (normalizedCohomologyForward (D.obj i)) (m + 1) z = _ at hrepr
  rw [← hrepr, completedCohomologyMap_of]
  have hj' : normalizedCohomologyStageMap (D.map i j hij) (m + 1) z = 0 := hj
  rw [hj', map_zero]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_NormalizedIdentityScalar
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.booleanPartitionStage_projective _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.horseshoeCover_projective _root_.OAI.PolycyclicRecognition.integralRepresentationSum_projective _root_.OAI.PolycyclicRecognition.iteratedNormalizedSyzygy_integral_projective _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalizedFreeRepresentation_countable _root_.OAI.PolycyclicRecognition.normalizedFreeRepresentation_integral_projective _root_.OAI.PolycyclicRecognition.normalizedSyzygy_countable _root_.OAI.PolycyclicRecognition.normalizedSyzygy_integral_projective _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.shiftedCohomologyForward_directed _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A scalar annihilating an identity cocycle factors through a projective -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2100] Linear.homModule
variable {G : Type} [Group G]

theorem normalizedIdentityClass_scalar_zero_stable (A : Rep.{0} ℤ G) (n : ℕ) (m : ℤ)
    (h : m • normalizedIdentityClass A (n + 1) = 0) :
    stableRepresentationClass ((iteratedNormalizedSyzygy (n + 1)).obj A)
      ((iteratedNormalizedSyzygy (n + 1)).obj A) (m • 𝟙 _) = 0 := by
  let C := (normalizedResolutionComplex A).linearYonedaObj ℤ
    ((iteratedNormalizedSyzygy (n + 1)).obj A)
  have hz : C.homologyπ (n + 1) (m • normalizedIdentityCycle A (n + 1)) = 0 := by
    rw [map_zsmul]
    exact h
  obtain ⟨r, hr⟩ := cochain_boundary_of_class_zero C n
    (m • normalizedIdentityCycle A (n + 1)) hz
  rw [map_zsmul, normalizedIdentityCycle_projection] at hr
  change (normalizedResolutionComplex A).d (n + 1) n ≫ r =
    m • normalizedResolutionProjection A (n + 1) at hr
  rw [normalizedResolutionComplex_d] at hr
  let r' : normalizedFreeRepresentation ((iteratedNormalizedSyzygy n).obj A) ⟶
      (iteratedNormalizedSyzygy (n + 1)).obj A := r
  let u : (iteratedNormalizedSyzygy (n + 1)).obj A ⟶
      normalizedFreeRepresentation ((iteratedNormalizedSyzygy n).obj A) :=
    kernel.ι (normalizedFreeAugmentation ((iteratedNormalizedSyzygy n).obj A))
  have hur : u ≫ r' = m • 𝟙 ((iteratedNormalizedSyzygy (n + 1)).obj A) := by
    apply (cancel_epi (normalizedFreeAugmentation ((iteratedNormalizedSyzygy (n + 1)).obj A))).mp
    change normalizedFreeStep ((iteratedNormalizedSyzygy n).obj A) ≫ r' =
      normalizedFreeAugmentation ((iteratedNormalizedSyzygy (n + 1)).obj A) ≫
        (m • 𝟙 ((iteratedNormalizedSyzygy (n + 1)).obj A))
    rw [Preadditive.comp_zsmul, Category.comp_id]
    exact hr
  exact (stableRepresentationClass_eq_zero_iff_projective_factor _).mpr
    ⟨normalizedFreeRepresentation ((iteratedNormalizedSyzygy n).obj A), inferInstance,
      u, r', hur⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_NormalizedIdentityConnecting
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.cyclicTopHomologyInjection_mono _root_.OAI.PolycyclicRecognition.finiteResolution_single_supported _root_.OAI.PolycyclicRecognition.finiteTruncationAugmentation_quasiIso _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.iteratedNormalizedSyzygy_integral_projective _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalizedFreeRepresentation_countable _root_.OAI.PolycyclicRecognition.normalizedFreeRepresentation_integral_projective _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.shiftedCohomologyForward_directed _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.SequentialRepresentationDiagram.ColimitCocone.freeLimitGenerator_basis _root_.OAI.PolycyclicRecognition.SequentialRepresentationDiagram.ColimitCocone.freeModuleGenerator_zero _root_.OAI.PolycyclicRecognition.SequentialRepresentationDiagram.ColimitCocone.freeModuleInverse_basis _root_.OAI.PolycyclicRecognition.SequentialRepresentationDiagram.ColimitCocone.freeModuleLift_of _root_.OAI.PolycyclicRecognition.SequentialRepresentationDiagram.ColimitCocone.iteratedNormalizedSyzygy_ι _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalizedGroupIdentityClass_comparison _root_.OAI.PolycyclicRecognition.normalizedStableSyzygyIterate_class _root_.OAI.PolycyclicRecognition.normalizedSyzygyIterationIso_succ _root_.OAI.PolycyclicRecognition.rationalCoefficientInclusion_apply _root_.OAI.PolycyclicRecognition.shiftedCohomologyStageMap_id _root_.OAI.PolycyclicRecognition.shiftedCompletedCohomologyMap_of _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The connecting maps carry the normalized identity cocycle forward -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits HomologicalComplex
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2100] Linear.homModule
variable (G : Type) [Group G]

theorem normalizedIdentityConnecting_class (n : ℕ) :
    normalizedIdentityConnecting G n (normalizedIdentityClass (trivialIntegral G) n) =
      normalizedIdentityClass (trivialIntegral G) (n + 1) := by
  let A := trivialIntegral G
  let P := normalizedProjectiveResolution A
  let S := normalizedSyzygySequence ((iteratedNormalizedSyzygy n).obj A)
  let hS := resolutionCoefficientSequence_shortExact P S
    (normalizedSyzygySequence_shortExact ((iteratedNormalizedSyzygy n).obj A))
  have hz : ((forget₂ (ModuleCat ℤ) Ab).map
      ((resolutionCoefficientSequence P S).X₃.d n (n + 1)))
        (normalizedResolutionProjection A n) = 0 := by
    change (normalizedResolutionComplex A).d (n + 1) n ≫
      normalizedResolutionProjection A n = 0
    exact normalizedResolution_d_projection A n
  have hl : ((forget₂ (ModuleCat ℤ) Ab).map
      ((resolutionCoefficientSequence P S).g.f n)) (𝟙 (P.complex.X n)) =
        normalizedResolutionProjection A n := by
    change 𝟙 _ ≫ normalizedResolutionProjection A n = normalizedResolutionProjection A n
    exact Category.id_comp _
  have hd : ((forget₂ (ModuleCat ℤ) Ab).map
      ((resolutionCoefficientSequence P S).f.f (n + 1)))
        (normalizedResolutionProjection A (n + 1)) =
      ((forget₂ (ModuleCat ℤ) Ab).map
        ((resolutionCoefficientSequence P S).X₂.d n (n + 1))) (𝟙 (P.complex.X n)) := by
    change normalizedResolutionProjection A (n + 1) ≫
        kernel.ι (normalizedFreeAugmentation ((iteratedNormalizedSyzygy n).obj A)) =
      (normalizedResolutionComplex A).d (n + 1) n ≫ 𝟙 _
    rw [Category.comp_id, normalizedResolutionComplex_d]
    rfl
  exact hS.δ_apply n (n + 1) rfl (normalizedResolutionProjection A n) hz
    (𝟙 (P.complex.X n)) hl (normalizedResolutionProjection A (n + 1)) hd (n + 2) (by simp)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_CompletedIdentity
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.cyclicTopHomologyInjection_mono _root_.OAI.PolycyclicRecognition.finiteResolution_single_supported _root_.OAI.PolycyclicRecognition.finiteTruncationAugmentation_quasiIso _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.iteratedNormalizedSyzygy_integral_projective _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.shiftedCohomologyForward_directed _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The complete identity detects finite integral cohomological dimension

The class of the augmentation is transported into ordinary cohomology. Its
successive connecting images are the syzygy identity classes. Vanishing of
its image in complete cohomology therefore forces a projective syzygy.
No vanishing from FP-infinity is assumed or asserted.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable (G : Type) [Group G]

theorem normalizedSyzygyConnecting_identity (n : ℕ) :
    normalizedSyzygyConnecting (trivialIntegral G) n (normalizedGroupIdentityClass G n) =
      normalizedGroupIdentityClass G (n + 1) := by
  let P := normalizedProjectiveResolution (trivialIntegral G)
  let S := normalizedSyzygySequence ((iteratedNormalizedSyzygy n).obj (trivialIntegral G))
  let e := coefficientNaturalCohomologyIso P S.X₁ (n + 1)
  apply ((ModuleCat.mono_iff_injective e.hom).mp inferInstance)
  have he := ConcreteCategory.congr_hom
    (coefficientNaturalCohomologyIso_connecting P S
      (normalizedSyzygySequence_shortExact ((iteratedNormalizedSyzygy n).obj
        (trivialIntegral G))) n) (normalizedGroupIdentityClass G n)
  change e.hom (normalizedSyzygyConnecting (trivialIntegral G) n
      (normalizedGroupIdentityClass G n)) = normalizedIdentityConnecting G n
        ((coefficientNaturalCohomologyIso (normalizedProjectiveResolution (trivialIntegral G))
          ((iteratedNormalizedSyzygy n).obj (trivialIntegral G)) n).hom
            (normalizedGroupIdentityClass G n)) at he
  rw [normalizedGroupIdentityClass_comparison] at he
  exact he.trans (normalizedIdentityConnecting_class G n) |>.trans
    (normalizedGroupIdentityClass_comparison G (n + 1)).symm

theorem normalizedCohomologyForward_identity (i j : ℕ) (h : i ≤ j) :
    normalizedCohomologyForward (trivialIntegral G) i j h (normalizedGroupIdentityClass G i) =
      normalizedGroupIdentityClass G j := by
  induction h with
  | refl => exact Nat.leRecOn_self _
  | @step j h ih =>
    change Nat.leRecOn (C := normalizedCohomologyStage (trivialIntegral G)) _
      (fun {k} => (normalizedSyzygyConnecting (trivialIntegral G) k).hom)
        (normalizedGroupIdentityClass G i) = _
    rw [Nat.leRecOn_succ h]
    change normalizedSyzygyConnecting (trivialIntegral G) j
      (normalizedCohomologyForward (trivialIntegral G) i j h
        (normalizedGroupIdentityClass G i)) = _
    rw [ih]
    exact normalizedSyzygyConnecting_identity G j

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_FiniteGroupProjectiveNorm
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.booleanPartitionStage_projective _root_.OAI.PolycyclicRecognition.cyclicTopHomologyInjection_mono _root_.OAI.PolycyclicRecognition.finiteResolution_single_supported _root_.OAI.PolycyclicRecognition.finiteTruncationAugmentation_quasiIso _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.horseshoeCover_projective _root_.OAI.PolycyclicRecognition.integralRepresentationSum_projective _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.normalizedFreeRepresentation_countable _root_.OAI.PolycyclicRecognition.normalizedFreeRepresentation_integral_projective _root_.OAI.PolycyclicRecognition.normalizedSyzygy_projective _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.SequentialRepresentationDiagram.ColimitCocone.freeLimitGenerator_basis _root_.OAI.PolycyclicRecognition.SequentialRepresentationDiagram.ColimitCocone.freeModuleGenerator_zero _root_.OAI.PolycyclicRecognition.SequentialRepresentationDiagram.ColimitCocone.freeModuleInverse_basis _root_.OAI.PolycyclicRecognition.SequentialRepresentationDiagram.ColimitCocone.freeModuleLift_of _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.normalizedGroupIdentityClass_comparison _root_.OAI.PolycyclicRecognition.normalizedStableSyzygyIterate_class _root_.OAI.PolycyclicRecognition.normalizedStableSyzygyMap_class _root_.OAI.PolycyclicRecognition.rationalCoefficientInclusion_apply _root_.OAI.PolycyclicRecognition.resolutionStableSyzygyTransition_class _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Norms on projective integral representations of finite groups

Every invariant vector in a free representation is a norm. Splitting the
normalized free cover extends this to projective representations. Consequently,
a scalar endomorphism of the trivial representation factors through a projective
representation exactly when the group order divides that scalar.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
open scoped MonoidAlgebra
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G]

variable [Fintype G]

theorem freeRepresentation_invariant_is_norm {α : Type} (x : Rep.free ℤ G α)
    (hx : ∀ g : G, (Rep.free ℤ G α).ρ g x = x) :
    ∃ y : Rep.free ℤ G α, (Rep.norm (Rep.free ℤ G α)).hom y = x := by
  classical
  have hc (a : α) (g : G) : (x a).coeff g = (x a).coeff 1 := by
    have he := congrArg (fun z : Rep.free ℤ G α => (z a).coeff g) (hx g)
    simpa only [freeRepresentation_action_coeff, inv_mul_cancel] using he.symm
  let y : Rep.free ℤ G α := x.mapRange (fun z => MonoidAlgebra.single 1 (z.coeff 1)) (by simp)
  refine ⟨y, ?_⟩
  ext a h
  change (Representation.norm (Representation.free ℤ G α) y a).coeff h = (x a).coeff h
  calc
    _ = ∑ g : G, (Representation.free ℤ G α g y a).coeff h := by
      simp [Representation.norm]
    _ = ∑ g : G, (y a).coeff (g⁻¹ * h) := by
      apply Finset.sum_congr rfl
      intro g _
      exact freeRepresentation_action_coeff g y a h
    _ = (x a).coeff h := by
      simp [y, MonoidAlgebra.coeff_single, Finsupp.single_apply, eq_comm, inv_mul_eq_one, hc]

theorem projectiveRepresentation_invariant_is_norm (P : Rep.{0} ℤ G) [Projective P]
    (x : P) (hx : ∀ g : G, P.ρ g x = x) :
    ∃ y : P, (Rep.norm P).hom y = x := by
  let s := Projective.factorThru (𝟙 P) (normalizedFreeAugmentation P)
  have hs : s ≫ normalizedFreeAugmentation P = 𝟙 P := Projective.factorThru_comp _ _
  have hxs (g : G) : (normalizedFreeRepresentation P).ρ g (s.hom x) = s.hom x := by
    rw [← Rep.hom_comm_apply, hx]
  obtain ⟨y, hy⟩ := freeRepresentation_invariant_is_norm (s.hom x) hxs
  refine ⟨(normalizedFreeAugmentation P).hom y, ?_⟩
  have hn := ConcreteCategory.congr_hom (Rep.norm_comm (normalizedFreeAugmentation P)) y
  change (Rep.norm P).hom ((normalizedFreeAugmentation P).hom y) =
    (normalizedFreeAugmentation P).hom ((Rep.norm (normalizedFreeRepresentation P)).hom y) at hn
  change (Rep.norm (normalizedFreeRepresentation P)).hom y = s.hom x at hy
  rw [hy] at hn
  exact hn.trans (ConcreteCategory.congr_hom hs x)

theorem projective_trivial_factor_divisible (P : Rep.{0} ℤ G) [Projective P]
    (u : trivialIntegral G ⟶ P) (v : P ⟶ trivialIntegral G) :
    (Fintype.card G : ℤ) ∣ v.hom (u.hom 1) := by
  have hu (g : G) : P.ρ g (u.hom 1) = u.hom 1 := by
    rw [← Rep.hom_comm_apply]
    rfl
  obtain ⟨y, hy⟩ := projectiveRepresentation_invariant_is_norm P (u.hom 1) hu
  refine ⟨v.hom y, ?_⟩
  have hn := ConcreteCategory.congr_hom (Rep.norm_comm v) y
  change (Rep.norm (trivialIntegral G)).hom (v.hom y) = v.hom ((Rep.norm P).hom y) at hn
  rw [hy] at hn
  simpa [Rep.norm, Representation.norm, trivialIntegral, nsmul_eq_mul] using hn.symm

theorem stableTrivialScalar_eq_zero_iff (m : ℤ) :
    stableRepresentationClass (trivialIntegral G) (trivialIntegral G)
      (m • 𝟙 (trivialIntegral G)) = 0 ↔ (Fintype.card G : ℤ) ∣ m := by
  rw [stableRepresentationClass_eq_zero_iff_projective_factor]
  constructor
  · rintro ⟨P, hP, u, v, huv⟩
    let := hP
    have h := projective_trivial_factor_divisible P u v
    have he := ConcreteCategory.congr_hom huv (1 : ℤ)
    change v.hom (u.hom 1) = m * 1 at he
    simpa only [he, mul_one] using h
  · rintro ⟨k, rfl⟩
    let A := trivialIntegral G
    let F := normalizedFreeRepresentation A
    let e : F := normalizedFreeGenerator A 1
    let u : A ⟶ F := Rep.ofHom
      ⟨{ toFun := fun z => z • (Rep.norm F).hom e
         map_add' := fun x y => add_smul x y _
         map_smul' := fun r z => by
           simp only [RingHom.id_apply, smul_eq_mul]
           exact @mul_smul ℤ F _ F.hV2.toSemigroupAction r z ((Rep.norm F).hom e) },
       fun g => by
         apply LinearMap.ext
         intro z
         change z • (Rep.norm F).hom e = F.ρ g (z • (Rep.norm F).hom e)
         rw [map_smul]
         congr 1
         exact (Representation.self_norm_apply F.ρ g e).symm⟩
    refine ⟨F, inferInstance, u, k • normalizedFreeAugmentation A, ?_⟩
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro z
    change k • (normalizedFreeAugmentation A).hom (z • (Rep.norm F).hom e) =
      ((Fintype.card G : ℤ) * k) • z
    rw [map_smul]
    have hn := ConcreteCategory.congr_hom (Rep.norm_comm (normalizedFreeAugmentation A)) e
    change (Rep.norm A).hom ((normalizedFreeAugmentation A).hom e) =
      (normalizedFreeAugmentation A).hom ((Rep.norm F).hom e) at hn
    rw [← hn]
    have he : (normalizedFreeAugmentation A).hom e = 1 :=
      normalizedFreeAugmentation_generator A 1
    rw [he]
    simp [A, Rep.norm, Representation.norm, trivialIntegral]
    ring

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_FiniteGroupRelativeInjective
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.normalizedFreeRepresentation_countable _root_.OAI.PolycyclicRecognition.normalizedFreeRepresentation_integral_projective _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Extending maps into projectives across integral split inclusions

For a finite group, a projective representation is injective with respect to
short exact sequences that split as sequences of abelian groups. The extension
uses the coefficient at the identity followed by the finite group sum.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
open scoped MonoidAlgebra
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G] [Fintype G]

theorem freeAveragedExtension_eq {α : Type} {A B : Rep.{0} ℤ G}
    (i : A ⟶ B) (f : A ⟶ Rep.free ℤ G α)
    (l : B →ₗ[ℤ] Rep.free ℤ G α) (hl : ∀ a, l (i.hom a) = f.hom a) :
    i ≫ freeAveragedExtension B l = f := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  ext a h
  change (freeAveragedLinearMap B l (i.hom x) a).coeff h = (f.hom x a).coeff h
  rw [freeAveragedLinearMap_coeff, ← Rep.hom_comm_apply, hl, Rep.hom_comm_apply]
  change (Representation.free ℤ G α h⁻¹ (f.hom x) a).coeff 1 = _
  rw [freeRepresentation_action_coeff]
  simp

theorem projective_extend_of_integral_retraction {A B : Rep.{0} ℤ G}
    (i : A ⟶ B) (r : B →ₗ[ℤ] A) (hr : ∀ a, r (i.hom a) = a)
    (P : Rep.{0} ℤ G) [Projective P] (f : A ⟶ P) :
    ∃ F : B ⟶ P, i ≫ F = f := by
  let s := Projective.factorThru (𝟙 P) (normalizedFreeAugmentation P)
  have hs : s ≫ normalizedFreeAugmentation P = 𝟙 P := Projective.factorThru_comp _ _
  let l : B →ₗ[ℤ] normalizedFreeRepresentation P := (f ≫ s).hom.toLinearMap ∘ₗ r
  let F := freeAveragedExtension B l
  have he : i ≫ F = f ≫ s := by
    apply freeAveragedExtension_eq
    intro a
    change (f ≫ s).hom (r (i.hom a)) = (f ≫ s).hom a
    rw [hr]
  refine ⟨F ≫ normalizedFreeAugmentation P, ?_⟩
  erw [← Category.assoc, he, Category.assoc, hs, Category.comp_id]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_FiniteGroupSyzygyScalar
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Descending a stable scalar through an integral split syzygy sequence -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
open scoped MonoidAlgebra
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2100] Linear.homModule
variable {G : Type} [Group G]

variable [Fintype G]

theorem stableScalar_descend (S : ShortComplex (Rep.{0} ℤ G)) (hS : S.ShortExact)
    [Projective S.X₂] [Module.Projective ℤ S.X₃] (m : ℤ)
    (h : stableRepresentationClass S.X₁ S.X₁ (m • 𝟙 S.X₁) = 0) :
    stableRepresentationClass S.X₃ S.X₃ (m • 𝟙 S.X₃) = 0 := by
  let F := forget₂ (Rep.{0} ℤ G) (ModuleCat ℤ)
  let : Projective ((S.map F).X₃) := by
    change Projective (ModuleCat.of ℤ S.X₃)
    infer_instance
  let sp := (hS.map_of_exact F).splittingOfProjective
  obtain ⟨P, hP, u, v, huv⟩ :=
    (stableRepresentationClass_eq_zero_iff_projective_factor _).mp h
  let := hP
  obtain ⟨l, hl⟩ := projective_extend_of_integral_retraction S.f sp.r.hom
    (fun a => ConcreteCategory.congr_hom sp.f_r a) P u
  let k : S.X₂ ⟶ S.X₂ := m • 𝟙 S.X₂ - l ≫ v ≫ S.f
  have hf : S.f ≫ (l ≫ v ≫ S.f) = m • S.f := by
    rw [← Category.assoc S.f l, hl, ← Category.assoc u v, huv,
      Preadditive.zsmul_comp, Category.id_comp]
  have hk : S.f ≫ k = 0 := by
    change S.f ≫ (m • 𝟙 S.X₂ - l ≫ v ≫ S.f) = 0
    rw [Preadditive.comp_sub, Preadditive.comp_zsmul, Category.comp_id, hf, sub_self]
  let := hS.epi_g
  let t := hS.exact.desc k hk
  have ht : S.g ≫ t = k := hS.exact.g_desc k hk
  apply (stableRepresentationClass_eq_zero_iff_projective_factor _).mpr
  refine ⟨S.X₂, inferInstance, t, S.g, ?_⟩
  apply (cancel_epi S.g).mp
  rw [← Category.assoc, ht]
  have hg : (l ≫ v ≫ S.f) ≫ S.g = 0 := by
    rw [Category.assoc, Category.assoc, S.zero, comp_zero, comp_zero]
  change (m • 𝟙 S.X₂ - l ≫ v ≫ S.f) ≫ S.g = S.g ≫ (m • 𝟙 S.X₃)
  rw [Preadditive.sub_comp, Preadditive.zsmul_comp, Category.id_comp,
    hg, sub_zero, Preadditive.comp_zsmul, Category.comp_id]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_CompletedIdentityTorsion
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.IntegralProjectiveTower.instDirectedSystemNatCohomologyStageCoeLinearMapIntIdForward _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.booleanPartitionStage_projective _root_.OAI.PolycyclicRecognition.cyclicTopHomologyInjection_mono _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.horseshoeCover_projective _root_.OAI.PolycyclicRecognition.integralRepresentationSum_projective _root_.OAI.PolycyclicRecognition.moduleTailMap_directed _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalizedFreeRepresentation_countable _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.shiftedCohomologyForward_directed _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Torsion of the complete identity bounds all finite subgroup orders

The annihilator is kept as an explicit premise. In particular, the theorem
below does not claim that FP-infinity by itself supplies an annihilator.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2100] Linear.homModule
variable {G : Type} [Group G]

theorem normalizedStableScalar_restrict_descend (H : Subgroup G) [Fintype H]
    (n : ℕ) (m : ℤ)
    (h : stableRepresentationClass
      (Rep.res H.subtype ((iteratedNormalizedSyzygy n).obj (trivialIntegral G)))
      (Rep.res H.subtype ((iteratedNormalizedSyzygy n).obj (trivialIntegral G)))
      (m • 𝟙 _) = 0) :
    stableRepresentationClass (trivialIntegral H) (trivialIntegral H)
      (m • 𝟙 _) = 0 := by
  induction n with
  | zero => exact h
  | succ n ih =>
    apply ih
    let F : Rep.{0} ℤ G ⥤ Rep.{0} ℤ H := Rep.resFunctor H.subtype
    let S := normalizedSyzygySequence ((iteratedNormalizedSyzygy n).obj (trivialIntegral G))
    let : Projective ((S.map F).X₂) := by
      change Projective (F.obj (normalizedFreeRepresentation
        ((iteratedNormalizedSyzygy n).obj (trivialIntegral G))))
      exact (Rep.resFunctor (k := ℤ) H.subtype).projective_obj_of_projective inferInstance
    let : Module.Projective ℤ ((S.map F).X₃) := by
      change Module.Projective ℤ ((iteratedNormalizedSyzygy n).obj (trivialIntegral G))
      infer_instance
    exact stableScalar_descend (S.map F)
      ((normalizedSyzygySequence_shortExact _).map_of_exact F) m h

theorem finite_subgroup_order_dvd_of_completedIdentity_annihilator
    (H : Subgroup G) [Fintype H] (m : ℤ) (hm : m • completedIdentity G = 0) :
    (Fintype.card H : ℤ) ∣ m := by
  have hz : Module.DirectLimit.of ℤ ℕ _ (normalizedCohomologyForward (trivialIntegral G)) 0
      (m • normalizedGroupIdentityClass G 0) = 0 := by
    rw [map_zsmul]
    exact hm
  obtain ⟨j, hj, he⟩ := Module.DirectLimit.of.zero_exact hz
  rw [map_zsmul, normalizedCohomologyForward_identity] at he
  have hs : m • normalizedGroupIdentityClass G (j + 1) = 0 := by
    have hd := congrArg (fun x => normalizedSyzygyConnecting (trivialIntegral G) j x) he
    simpa only [map_zsmul, normalizedSyzygyConnecting_identity, map_zero] using hd
  have hc : m • normalizedIdentityClass (trivialIntegral G) (j + 1) = 0 := by
    have hd := congrArg (fun x => (coefficientNaturalCohomologyIso
      (normalizedProjectiveResolution (trivialIntegral G))
      ((iteratedNormalizedSyzygy (j + 1)).obj (trivialIntegral G)) (j + 1)).hom x) hs
    simp only [map_zsmul, normalizedGroupIdentityClass_comparison, map_zero] at hd
    exact hd
  have hstable := normalizedIdentityClass_scalar_zero_stable (trivialIntegral G) j m hc
  obtain ⟨P, hP, u, v, huv⟩ :=
    (stableRepresentationClass_eq_zero_iff_projective_factor _).mp hstable
  let := hP
  let F : Rep.{0} ℤ G ⥤ Rep.{0} ℤ H := Rep.resFunctor H.subtype
  have hres : stableRepresentationClass
      (F.obj ((iteratedNormalizedSyzygy (j + 1)).obj (trivialIntegral G)))
      (F.obj ((iteratedNormalizedSyzygy (j + 1)).obj (trivialIntegral G))) (m • 𝟙 _) = 0 := by
    apply (stableRepresentationClass_eq_zero_iff_projective_factor _).mpr
    refine ⟨F.obj P, (Rep.resFunctor (k := ℤ) H.subtype).projective_obj_of_projective hP,
      F.map u, F.map v, ?_⟩
    rw [← F.map_comp, huv, F.map_zsmul, F.map_id]
  exact (stableTrivialScalar_eq_zero_iff m).mp
    (normalizedStableScalar_restrict_descend H (j + 1) m hres)

theorem boundedFiniteSubgroupOrders_of_completedIdentity_torsion
    (m : ℤ) (hm0 : m ≠ 0) (hm : m • completedIdentity G = 0) :
    HasBoundedFiniteSubgroupOrders G := by
  refine ⟨m.natAbs, fun H hH => ?_⟩
  let := hH
  let := Fintype.ofFinite H
  have hd := finite_subgroup_order_dvd_of_completedIdentity_annihilator H m hm
  have hn : Fintype.card H ∣ m.natAbs := by
    simpa only [Int.natAbs_natCast] using Int.natAbs_dvd_natAbs.mpr hd
  rw [Nat.card_eq_fintype_card]
  exact Nat.le_of_dvd (Int.natAbs_pos.mpr hm0) hn

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_RationalCompleteIdentity
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.SequentialRepresentationDiagram.ColimitCocone.telescopeAugmentation_epi _root_.OAI.PolycyclicRecognition.cyclicTopHomologyInjection_mono _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.shiftedCohomologyForward_directed _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Rational vanishing gives an integral annihilator of the complete identity

This is the coefficient step in the torsion endgame. Rational vanishing remains
an explicit intermediate premise until the hierarchical argument supplies it.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable (G : Type) [Group G]

theorem completedCohomologyMap_scalar_identity (m : ℤ) :
    completedCohomologyMap (m • 𝟙 (trivialIntegral G)) (completedIdentity G) =
      m • completedIdentity G := by
  unfold completedIdentity
  rw [completedCohomologyMap_of]
  have hs : normalizedCohomologyStageMap (m • 𝟙 (trivialIntegral G)) 0 =
      m • LinearMap.id := by
    unfold normalizedCohomologyStageMap
    change ((groupCohomology.functor ℤ G 0).map (m • 𝟙 (trivialIntegral G))).hom = _
    rw [CategoryTheory.Functor.map_zsmul, CategoryTheory.Functor.map_id]
    rfl
  rw [hs]
  change Module.DirectLimit.of ℤ ℕ _ (normalizedCohomologyForward (trivialIntegral G)) 0
    (m • normalizedGroupIdentityClass G 0) = _
  exact map_zsmul _ _ _

theorem TypeFPInfinity.completedIdentity_factorial_annihilator
    (hG : TypeFPInfinity G)
    (hq : completedCohomologyMap (rationalCoefficientInclusion G 0) (completedIdentity G) = 0) :
    ∃ j : ℕ, (j.factorial : ℤ) • completedIdentity G = 0 := by
  obtain ⟨j, hj, he⟩ := hG.completedCohomology_colimit_kernel
    (rationalCoefficientDiagram G) (Rep.trivial ℤ G ℚ) (rationalCoefficientColimit G) 0
    (completedIdentity G) hq
  refine ⟨j, ?_⟩
  change completedCohomologyMap (factorialMultiplier 0 j • 𝟙 (trivialIntegral G))
    (completedIdentity G) = 0 at he
  rw [completedCohomologyMap_scalar_identity, factorialMultiplier_zero] at he
  exact he

theorem TypeFPInfinity.boundedFiniteSubgroupOrders_of_rational_vanishing
    (hG : TypeFPInfinity G)
    (hq : completedCohomologyMap (rationalCoefficientInclusion G 0) (completedIdentity G) = 0) :
    HasBoundedFiniteSubgroupOrders G := by
  obtain ⟨j, hj⟩ := hG.completedIdentity_factorial_annihilator G hq
  exact boundedFiniteSubgroupOrders_of_completedIdentity_torsion (j.factorial : ℤ)
    (by exact_mod_cast Nat.factorial_ne_zero j) hj

theorem TypeFPInfinity.boundedFiniteSubgroupOrders_of_rational_projectiveDimension
    (hG : TypeFPInfinity G) (d : ℕ) [HasProjectiveDimensionLE (Rep.trivial ℤ G ℚ) d] :
    HasBoundedFiniteSubgroupOrders G := by
  let := completedCohomology_subsingleton_of_finite_projectiveDimension (Rep.trivial ℤ G ℚ) d
  exact hG.boundedFiniteSubgroupOrders_of_rational_vanishing G (Subsingleton.elim _ _)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_CompletedCohomologyAdditive
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalizedSyzygy_countable _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Additivity of complete cohomology

The free-cover construction is nonlinear, but its error is a projective factor.
The next connecting homomorphism kills that error, so the limit is additive.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G]

theorem cohomology_connecting_zero_of_projective_factor
    {U V : Rep.{0} ℤ G} (n : ℕ) (f : U ⟶ V)
    (hf : stableRepresentationClass U V f = 0) :
    (groupCohomology.functor ℤ G n).map f ≫
      groupCohomology.δ (normalizedSyzygySequence_shortExact V) n (n + 1) rfl = 0 := by
  obtain ⟨P, hP, u, v, huv⟩ := (stableRepresentationClass_eq_zero_iff_projective_factor f).mp hf
  let := hP
  let F := groupCohomology.functor ℤ G n
  let δ : F.obj V ⟶ groupCohomology (normalizedSyzygy V) (n + 1) :=
    groupCohomology.δ (normalizedSyzygySequence_shortExact V) n (n + 1) rfl
  change F.map f ≫ δ = 0
  have hn := groupCohomology.δ_naturality (normalizedSyzygySequence_shortExact P)
    (normalizedSyzygySequence_shortExact V) (normalizedSyzygySequenceMap v) n (n + 1) rfl
  rw [normalizedSyzygy_delta_eq_zero P n, zero_comp] at hn
  change 0 = F.map v ≫ δ at hn
  rw [← huv, CategoryTheory.Functor.map_comp, Category.assoc, ← hn, comp_zero]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_SequentialCohomologySurjectivity
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.SequentialRepresentationDiagram.ColimitCocone.telescopeAugmentation_epi _root_.OAI.PolycyclicRecognition.booleanPartitionStage_projective _root_.OAI.PolycyclicRecognition.cyclicTopHomologyInjection_mono _root_.OAI.PolycyclicRecognition.finiteResolution_single_supported _root_.OAI.PolycyclicRecognition.finiteTruncationAugmentation_quasiIso _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.horseshoeCover_projective _root_.OAI.PolycyclicRecognition.integralRepresentationSum_projective _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.repCofiber_projective _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.SequentialRepresentationDiagram.ColimitCocone.freeLimitGenerator_basis _root_.OAI.PolycyclicRecognition.SequentialRepresentationDiagram.ColimitCocone.freeLimitGenerator_zero _root_.OAI.PolycyclicRecognition.SequentialRepresentationDiagram.ColimitCocone.freeModuleInverse_basis _root_.OAI.PolycyclicRecognition.SequentialRepresentationDiagram.ColimitCocone.freeModuleLift_of _root_.OAI.PolycyclicRecognition.SequentialRepresentationDiagram.ColimitCocone.iteratedNormalizedSyzygy_ι _root_.OAI.PolycyclicRecognition.SequentialRepresentationDiagram.telescopeShift_inclusion _root_.OAI.PolycyclicRecognition.SequentialRepresentationDiagram.telescopeShift_succ _root_.OAI.PolycyclicRecognition.SequentialRepresentationDiagram.telescopeShift_zero _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalizedGroupIdentityClass_comparison _root_.OAI.PolycyclicRecognition.rationalCoefficientInclusion_apply _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Lifting cohomology classes from a sequential coefficient colimit -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped MonoidAlgebra
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2100] Linear.homModule
variable {G : Type} [Group G]

theorem finiteResolutionCohomology_colimit_surj
    (D : SequentialRepresentationDiagram G) (A : Rep.{0} ℤ G) (c : D.ColimitCocone A)
    (P : ProjectiveResolution (trivialIntegral G)) (n : ℕ)
    [Module.FinitePresentation ℤ[G] (P.complex.X n).ρ.asModule]
    [Module.Finite ℤ[G] (P.complex.X (n + 1)).ρ.asModule]
    (x : (P.complex.linearYonedaObj ℤ A).homology n) :
    ∃ (i : ℕ) (y : (P.complex.linearYonedaObj ℤ (D.obj i)).homology n),
      homologyMap (repCochainPostcomp ℤ P.complex (c.ι i)) n y = x := by
  let C := P.complex.linearYonedaObj ℤ A
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective (C.homologyπ n)).mp inferInstance x
  let u : P.complex.X n ⟶ A := C.iCycles n z
  have hdu : P.complex.d (n + 1) n ≫ u = 0 :=
    ConcreteCategory.congr_hom (C.iCycles_d n (n + 1)) z
  obtain ⟨i, v, hv⟩ := c.lift_finitelyPresented (P.complex.X n) u
  have hr : (P.complex.d (n + 1) n ≫ v) ≫ c.ι i = 0 := by
    rw [Category.assoc, hv, hdu]
  obtain ⟨j, hij, hj⟩ := c.eventually_zero_hom (P.complex.X (n + 1)) i
    (P.complex.d (n + 1) n ≫ v) hr
  let Cj := P.complex.linearYonedaObj ℤ (D.obj j)
  let v' := v ≫ D.map i j hij
  have hv' : P.complex.d (n + 1) n ≫ v' = 0 := by
    change P.complex.d (n + 1) n ≫ v ≫ D.map i j hij = 0
    rw [← Category.assoc, hj]
  let z' : Cj.cycles n := Cj.cyclesMk v' (n + 1) (by simp) hv'
  let φ := repCochainPostcomp ℤ P.complex (c.ι j)
  have he : cyclesMap φ n z' = z := by
    apply (ModuleCat.mono_iff_injective (C.iCycles n)).mp inferInstance
    have hm := ConcreteCategory.congr_hom (cyclesMap_i φ n) z'
    change C.iCycles n (cyclesMap φ n z') = C.iCycles n z
    change C.iCycles n (cyclesMap φ n z') = Cj.iCycles n z' ≫ c.ι j at hm
    have hz' : Cj.iCycles n z' = v' := Cj.i_cyclesMk v' (n + 1) (by simp) hv'
    rw [hm]
    change (Cj.iCycles n z' : P.complex.X n ⟶ D.obj j) ≫ c.ι j = u
    rw [hz']
    change (v ≫ D.map i j hij) ≫ c.ι j = u
    rw [Category.assoc, c.comm, hv]
  refine ⟨j, Cj.homologyπ n z', ?_⟩
  have hm := ConcreteCategory.congr_hom (homologyπ_naturality φ n) z'
  change homologyMap φ n (Cj.homologyπ n z') = C.homologyπ n (cyclesMap φ n z') at hm
  exact hm.trans (congrArg (C.homologyπ n) he)

theorem TypeFPInfinity.cohomology_colimit_surj
    (hG : TypeFPInfinity G) (D : SequentialRepresentationDiagram G)
    (A : Rep.{0} ℤ G) (c : D.ColimitCocone A) (n : ℕ) (x : groupCohomology A n) :
    ∃ (i : ℕ) (y : groupCohomology (D.obj i) n),
      groupCohomology.map (MonoidHom.id G) (c.ι i) n y = x := by
  obtain ⟨P, hP⟩ := hG (n + 1)
  let : Module.FinitePresentation ℤ[G] (P.complex.X n).ρ.asModule :=
    projectiveRepresentation_finitePresentation _ (hP n (by omega))
  let : Module.Finite ℤ[G] (P.complex.X (n + 1)).ρ.asModule := hP (n + 1) le_rfl
  obtain ⟨i, y, hy⟩ := finiteResolutionCohomology_colimit_surj D A c P n
    ((coefficientNaturalCohomologyIso P A n).hom x)
  let e := coefficientNaturalCohomologyIso P (D.obj i) n
  refine ⟨i, e.inv y, ?_⟩
  apply (coefficientNaturalCohomologyIso P A n).toLinearEquiv.injective
  have hn := ConcreteCategory.congr_hom
    (coefficientNaturalCohomologyIso_naturality P (c.ι i) n) (e.inv y)
  have hei : e.hom (e.inv y) = y := ConcreteCategory.congr_hom e.inv_hom_id y
  change (coefficientNaturalCohomologyIso P A n).hom
    (groupCohomology.map (MonoidHom.id G) (c.ι i) n (e.inv y)) =
      homologyMap (repCochainPostcomp ℤ P.complex (c.ι i)) n
        (e.hom (e.inv y)) at hn
  rw [hei] at hn
  exact hn.trans hy

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_ShiftedCompleteCohomologyVanishing
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instNonemptyBases _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.SequentialRepresentationDiagram.ColimitCocone.telescopeAugmentation_epi _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.iteratedNormalizedSyzygy_integral_projective _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalizedGroupIdentityClass_comparison _root_.OAI.PolycyclicRecognition.normalizedStableSyzygyIterate_class _root_.OAI.PolycyclicRecognition.normalizedSyzygyIterationIso_succ _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Projective vanishing and coefficient limits in nonnegative complete degrees -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G]

theorem normalizedSyzygy_delta_eq_zero_of_eq (A : Rep.{0} ℤ G) [Projective A]
    (i j : ℕ) (h : i + 1 = j) :
    groupCohomology.δ (normalizedSyzygySequence_shortExact A) i j h = 0 := by
  subst j
  exact normalizedSyzygy_delta_eq_zero A i

theorem shiftedCompleteCohomology_subsingleton_of_finite_projectiveDimension
    (p : ℕ) (A : Rep.{0} ℤ G) (d : ℕ) [HasProjectiveDimensionLE A d] :
    Subsingleton (ShiftedCompletedCohomology p A) := by
  apply subsingleton_of_forall_eq (0 : ShiftedCompletedCohomology p A)
  intro z
  obtain ⟨i, x, rfl⟩ := Module.DirectLimit.exists_of z
  let m := max i d
  have hAm : HasProjectiveDimensionLE A (m + 0) :=
    hasProjectiveDimensionLT_of_ge A (d + 1) (m + 0 + 1) (by dsimp [m]; omega)
  let : Projective ((iteratedNormalizedSyzygy m).obj A) :=
    (projective_iff_hasProjectiveDimensionLE_zero _).mpr
      (iteratedNormalizedSyzygy_projectiveDimension A m 0 hAm)
  let y := shiftedCohomologyForward p A i m (le_max_left i d) x
  have hz : shiftedCohomologyForward p A m (m + 1) (Nat.le_succ m) y = 0 := by
    change Nat.leRecOn (C := shiftedCohomologyStage p A) (Nat.le_succ m)
      (fun {k} => (shiftedSyzygyConnecting p A k).hom) y = 0
    rw [Nat.leRecOn_succ (le_refl m), Nat.leRecOn_self]
    change (shiftedSyzygyConnecting p A m).hom y = 0
    rw [show shiftedSyzygyConnecting p A m = 0 from
      normalizedSyzygy_delta_eq_zero_of_eq ((iteratedNormalizedSyzygy m).obj A)
        (m + p) (m + 1 + p) (by omega)]
    rfl
  have he := Module.DirectLimit.of_f (R := ℤ) (ι := ℕ)
    (G := shiftedCohomologyStage p A) (f := shiftedCohomologyForward p A)
    (hij := Nat.le_succ m) (x := y)
  rw [hz, map_zero] at he
  have hi := Module.DirectLimit.of_f (R := ℤ) (ι := ℕ)
    (G := shiftedCohomologyStage p A) (f := shiftedCohomologyForward p A)
    (hij := le_max_left i d) (x := x)
  exact hi.symm.trans he.symm

theorem TypeFPInfinity.shiftedCompleteCohomology_colimit_surj
    (hG : TypeFPInfinity G) (p : ℕ) (D : SequentialRepresentationDiagram G)
    (A : Rep.{0} ℤ G) (c : D.ColimitCocone A) (x : ShiftedCompletedCohomology p A) :
    ∃ (i : ℕ) (y : ShiftedCompletedCohomology p (D.obj i)),
      shiftedCompletedCohomologyMap p (c.ι i) y = x := by
  obtain ⟨n, z, rfl⟩ := Module.DirectLimit.exists_of x
  let E := D.mapFunctor (iteratedNormalizedSyzygy n)
  let ec := c.iteratedNormalizedSyzygy n
  obtain ⟨i, y, hy⟩ := hG.cohomology_colimit_surj E
    ((iteratedNormalizedSyzygy n).obj A) ec (n + p) z
  change shiftedCohomologyStage p (D.obj i) n at y
  refine ⟨i, Module.DirectLimit.of ℤ ℕ _ (shiftedCohomologyForward p (D.obj i)) n y, ?_⟩
  rw [shiftedCompletedCohomologyMap_of]
  have hy' : shiftedCohomologyStageMap p (c.ι i) n y = z := by
    rw [SequentialRepresentationDiagram.ColimitCocone.iteratedNormalizedSyzygy_ι] at hy
    exact hy
  rw [hy']

theorem TypeFPInfinity.shiftedCompleteCohomology_colimit_subsingleton
    (hG : TypeFPInfinity G) (p : ℕ) (D : SequentialRepresentationDiagram G)
    (A : Rep.{0} ℤ G) (c : D.ColimitCocone A)
    (hz : ∀ i, Subsingleton (ShiftedCompletedCohomology p (D.obj i))) :
    Subsingleton (ShiftedCompletedCohomology p A) := by
  apply subsingleton_of_forall_eq (0 : ShiftedCompletedCohomology p A)
  intro x
  obtain ⟨i, y, rfl⟩ := hG.shiftedCompleteCohomology_colimit_surj p D A c x
  rw [(hz i).elim y 0, map_zero]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_ShiftedCompleteCohomologyAdditive
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instNonemptyBases _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Additivity in nonnegative complete-cohomology degrees -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G]

theorem cohomology_connecting_zero_of_projective_factor_of_eq
    {U V : Rep.{0} ℤ G} (i j : ℕ) (h : i + 1 = j) (f : U ⟶ V)
    (hf : stableRepresentationClass U V f = 0) :
    (groupCohomology.functor ℤ G i).map f ≫
      groupCohomology.δ (normalizedSyzygySequence_shortExact V) i j h = 0 := by
  subst j
  exact cohomology_connecting_zero_of_projective_factor i f hf

theorem shiftedCompletedCohomologyMap_add (p : ℕ) {A B : Rep.{0} ℤ G} (f g : A ⟶ B) :
    shiftedCompletedCohomologyMap p (f + g) = shiftedCompletedCohomologyMap p f + shiftedCompletedCohomologyMap p g := by
  apply LinearMap.ext
  intro x
  obtain ⟨n, z, rfl⟩ := Module.DirectLimit.exists_of x
  let F := iteratedNormalizedSyzygy (G := G) n
  let H := groupCohomology.functor ℤ G (n + p)
  let a := F.map (f + g)
  let b := F.map f + F.map g
  have he : stableRepresentationClass _ _ a = stableRepresentationClass _ _ b := by
    change stableRepresentationClass _ _ (F.map (f + g)) = _
    rw [← normalizedStableSyzygyIterate_class n (f + g), map_add, map_add,
      normalizedStableSyzygyIterate_class, normalizedStableSyzygyIterate_class, map_add]
  have hd : stableRepresentationClass _ _ (a - b) = 0 := by
    rw [map_sub, he, sub_self]
  have hδ := cohomology_connecting_zero_of_projective_factor_of_eq (n + p) (n + 1 + p) (by omega) (a - b) hd
  have hstep : (shiftedSyzygyConnecting p B n).hom
      (shiftedCohomologyStageMap p (f + g) n z -
        (shiftedCohomologyStageMap p f n z + shiftedCohomologyStageMap p g n z)) = 0 := by
    have hz := ConcreteCategory.congr_hom hδ z
    change (shiftedSyzygyConnecting p B n).hom ((H.map (a - b)).hom z) = 0 at hz
    have hm : H.map (a - b) = H.map a - (H.map (F.map f) + H.map (F.map g)) := by
      simp only [b, CategoryTheory.Functor.map_sub, CategoryTheory.Functor.map_add]
    rw [hm] at hz
    exact hz
  let w := shiftedCohomologyStageMap p (f + g) n z -
    (shiftedCohomologyStageMap p f n z + shiftedCohomologyStageMap p g n z)
  have hw : shiftedCohomologyForward p B n (n + 1) (Nat.le_succ n) w = 0 := by
    change Nat.leRecOn (C := shiftedCohomologyStage p B) (Nat.le_succ n)
      (fun {k} => (shiftedSyzygyConnecting p B k).hom) w = 0
    rw [Nat.leRecOn_succ (le_refl n), Nat.leRecOn_self]
    exact hstep
  have hc := Module.DirectLimit.of_f (R := ℤ) (ι := ℕ)
    (G := shiftedCohomologyStage p B) (f := shiftedCohomologyForward p B)
    (hij := Nat.le_succ n) (x := w)
  rw [hw, map_zero] at hc
  change shiftedCompletedCohomologyMap p (f + g) _ = shiftedCompletedCohomologyMap p f _ + shiftedCompletedCohomologyMap p g _
  simp only [shiftedCompletedCohomologyMap_of]
  rw [← map_add, ← sub_eq_zero, ← map_sub]
  exact hc.symm

instance shiftedCompletedCohomologyFunctor_additive (p : ℕ) :
    (shiftedCompletedCohomologyFunctor p (G := G)).Additive where
  map_add {A B f g} := by
    apply ModuleCat.hom_ext
    exact shiftedCompletedCohomologyMap_add p f g


end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_ShiftedCohomologyDimensionShift
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instNonemptyBases _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalizedSyzygy_countable _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Dimension shifting in the completed coefficient theory -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2300] Module.DirectLimit.module
variable {G : Type} [Group G]

theorem cohomologyMap_reindex {A B : Rep.{0} ℤ G} (f : A ⟶ B)
    (i j : ℕ) (h : i = j) :
    (groupCohomology.functor ℤ G i).map f ≫
        (eqToIso (congrArg (fun d => groupCohomology B d) h)).hom =
      (eqToIso (congrArg (fun d => groupCohomology A d) h)).hom ≫
        (groupCohomology.functor ℤ G j).map f := by
  subst j
  change (groupCohomology.functor ℤ G i).map f ≫ 𝟙 _ =
    𝟙 _ ≫ (groupCohomology.functor ℤ G i).map f
  rw [Category.comp_id, Category.id_comp]

theorem shiftedSyzygyStageIso_natural (p : ℕ) {A B : Rep.{0} ℤ G}
    (f : A ⟶ B) (n : ℕ) :
    (groupCohomology.functor ℤ G (n + (p + 1))).map
        ((iteratedNormalizedSyzygy n).map (normalizedSyzygyMap f)) ≫
        (shiftedSyzygyStageIso p B n).hom =
      (shiftedSyzygyStageIso p A n).hom ≫
        (groupCohomology.functor ℤ G (n + 1 + p)).map
          ((iteratedNormalizedSyzygy (n + 1)).map f) := by
  have h := congrArg ((groupCohomology.functor ℤ G (n + (p + 1))).map)
    (normalizedSyzygyIterationIso_natural f n)
  simp only [CategoryTheory.Functor.map_comp] at h
  simp only [shiftedSyzygyStageIso]
  erw [← Category.assoc, h, Category.assoc,
    cohomologyMap_reindex _ (n + (p + 1)) (n + 1 + p) (by omega), ← Category.assoc]

theorem shiftedSyzygyEquiv_of (p : ℕ) (A : Rep.{0} ℤ G) (n : ℕ)
    (x : shiftedCohomologyStage (p + 1) (normalizedSyzygy A) n) :
    shiftedSyzygyAddEquiv p A
        (Module.DirectLimit.of ℤ ℕ _ (shiftedCohomologyForward (p + 1) (normalizedSyzygy A)) n x) =
      Module.DirectLimit.of ℤ ℕ _ (shiftedCohomologyForward p A) (n + 1)
        ((shiftedSyzygyStageIso p A n).hom x) := by
  change moduleTailToOriginal (shiftedCohomologyStage p A) (shiftedCohomologyForward p A)
    (shiftedSyzygyTailEquiv p A
      (Module.DirectLimit.of ℤ ℕ _ (shiftedCohomologyForward (p + 1) (normalizedSyzygy A)) n x)) = _
  unfold shiftedSyzygyTailEquiv
  rw [Module.DirectLimit.congr_apply_of, moduleTailToOriginal_of]
  rfl

theorem shiftedSyzygyEquiv_natural (p : ℕ) {A B : Rep.{0} ℤ G} (f : A ⟶ B)
    (x : ShiftedCompletedCohomology (p + 1) (normalizedSyzygy A)) :
    shiftedSyzygyAddEquiv p B (shiftedCompletedCohomologyMap (p + 1) (normalizedSyzygyMap f) x) =
      shiftedCompletedCohomologyMap p f (shiftedSyzygyAddEquiv p A x) := by
  obtain ⟨n, z, rfl⟩ := Module.DirectLimit.exists_of x
  rw [shiftedCompletedCohomologyMap_of, shiftedSyzygyEquiv_of,
    shiftedSyzygyEquiv_of, shiftedCompletedCohomologyMap_of]
  congr 1
  exact ConcreteCategory.congr_hom (shiftedSyzygyStageIso_natural p f n) z

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_CompleteCohomologyStableMaps
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Stable maps and projective presentations in complete cohomology -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G]

theorem shiftedCompleteFunctor_map_zero_of_stable_zero
    (p : ℕ) {A B : Rep.{0} ℤ G} (f : A ⟶ B)
    (hf : stableRepresentationClass A B f = 0) :
    (shiftedCompletedCohomologyFunctor p).map f = 0 := by
  obtain ⟨P, hP, u, v, huv⟩ :=
    (stableRepresentationClass_eq_zero_iff_projective_factor f).mp hf
  let : Projective P := hP
  let : Subsingleton (ShiftedCompletedCohomology p P) :=
    shiftedCompleteCohomology_subsingleton_of_finite_projectiveDimension p P 0
  have hu : (shiftedCompletedCohomologyFunctor p).map u = 0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change shiftedCompletedCohomologyMap p u x = 0
    exact Subsingleton.elim _ _
  rw [← huv, Functor.map_comp, hu, zero_comp]

theorem shiftedCompleteFunctor_map_eq_of_stable_eq
    (p : ℕ) {A B : Rep.{0} ℤ G} (f g : A ⟶ B)
    (hfg : stableRepresentationClass A B f = stableRepresentationClass A B g) :
    (shiftedCompletedCohomologyFunctor p).map f =
      (shiftedCompletedCohomologyFunctor p).map g := by
  have hz : stableRepresentationClass A B (f - g) = 0 := by
    rw [map_sub, hfg, sub_self]
  have h := shiftedCompleteFunctor_map_zero_of_stable_zero p (f - g) hz
  rw [Functor.map_sub] at h
  exact sub_eq_zero.mp h

theorem shiftedCompletedCohomologyMap_comp_apply (p : ℕ) {A B C : Rep.{0} ℤ G}
    (f : A ⟶ B) (g : B ⟶ C) (x : ShiftedCompletedCohomology p A) :
    shiftedCompletedCohomologyMap p (f ≫ g) x =
      shiftedCompletedCohomologyMap p g (shiftedCompletedCohomologyMap p f x) :=
  ConcreteCategory.congr_hom ((shiftedCompletedCohomologyFunctor p).map_comp f g) x

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_CompleteCohomologyConnecting
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalizedSyzygy_countable _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Connecting maps for the completed coefficient theory

The kernel map of a projective cover and the syzygy dimension equivalence
give connecting maps for every short exact coefficient sequence. Naturality
holds because different choices of projective lift have the same stable map.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G]

theorem shiftedCompleteBoundary_apply (p : ℕ) (S : ShortComplex (Rep.{0} ℤ G))
    (hS : S.ShortExact) (x : ShiftedCompletedCohomology p S.X₃) :
    shiftedCompleteBoundary p S hS x =
      shiftedCompletedCohomologyMap (p + 1) (presentationKernelMap S hS)
        ((shiftedSyzygyAddEquiv p S.X₃).symm x) := rfl

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_NormalizedProjectiveTower
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instNonemptyBases _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Comparison with the normalized complete-cohomology construction -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G]

theorem normalizedProjectiveTowerMap_cohomology {A B : Rep.{0} ℤ G} (f : A ⟶ B) (p : ℕ)
    (x : (normalizedProjectiveTower A).Cohomology p) :
    normalizedProjectiveTowerCohomology B p ((normalizedProjectiveTowerMap f).cohomologyMap p x) =
      shiftedCompletedCohomologyMap p f (normalizedProjectiveTowerCohomology A p x) := by
  obtain ⟨n, z, rfl⟩ := Module.DirectLimit.exists_of x
  rw [IntegralProjectiveTower.Map.cohomologyMap_of]
  change shiftedCohomologyStage p A n at z
  change Module.DirectLimit.of ℤ ℕ _ (shiftedCohomologyForward p B) n
      (shiftedCohomologyStageMap p f n z) =
    shiftedCompletedCohomologyMap p f
      (Module.DirectLimit.of ℤ ℕ _ (shiftedCohomologyForward p A) n z)
  rw [shiftedCompletedCohomologyMap_of]

theorem IntegralProjectiveTower.completeCohomologyEquiv_apply
    (T : IntegralProjectiveTower G) (p : ℕ) (x : T.Cohomology p) :
    T.completeCohomologyEquiv (T.obj 0) (Iso.refl _) p x =
      normalizedProjectiveTowerCohomology (T.obj 0) p (T.normalization.cohomologyMap p x) := rfl

theorem IntegralProjectiveTower.completeCohomologyEquiv_natural
    {T U : IntegralProjectiveTower G} (f : IntegralProjectiveTower.Map T U)
    (p : ℕ) (x : T.Cohomology p) :
    U.completeCohomologyEquiv (U.obj 0) (Iso.refl _) p (f.cohomologyMap p x) =
      shiftedCompletedCohomologyMap p (f.app 0)
        (T.completeCohomologyEquiv (T.obj 0) (Iso.refl _) p x) := by
  rw [IntegralProjectiveTower.completeCohomologyEquiv_apply,
    IntegralProjectiveTower.completeCohomologyEquiv_apply,
    ← normalizedProjectiveTowerMap_cohomology]
  have h : (f.comp U.normalization).cohomologyMap p =
      (T.normalization.comp (normalizedProjectiveTowerMap (f.app 0))).cohomologyMap p := by
    apply IntegralProjectiveTower.Map.cohomologyMap_eq_of_stable_eq
    change stableRepresentationClass _ _ (f.app 0 ≫ 𝟙 _) =
      stableRepresentationClass _ _ (𝟙 _ ≫ f.app 0)
    rw [Category.comp_id, Category.id_comp]
  have he := LinearMap.congr_fun h x
  rw [IntegralProjectiveTower.Map.cohomologyMap_comp,
    IntegralProjectiveTower.Map.cohomologyMap_comp] at he
  exact congrArg (normalizedProjectiveTowerCohomology (U.obj 0) p) he

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_ProjectiveTowerExactness
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instNonemptyBases _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.moduleTailMap_directed _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exactness of cohomology limits for degreewise exact towers -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G]
namespace IntegralProjectiveTower

theorem cohomology_exact {T U V : IntegralProjectiveTower G} (f : Map T U) (g : Map U V)
    (hzero : ∀ n, f.app n ≫ g.app n = 0)
    (hexact : ∀ n, (ShortComplex.mk (f.app n) (g.app n) (hzero n)).ShortExact)
    (p : ℕ) (x : U.Cohomology p) (hx : g.cohomologyMap p x = 0) :
    ∃ y : T.Cohomology p, f.cohomologyMap p y = x := by
  obtain ⟨n, z, rfl⟩ := Module.DirectLimit.exists_of x
  rw [Map.cohomologyMap_of] at hx
  obtain ⟨m, hnm, hm⟩ := Module.DirectLimit.of.zero_exact hx
  have hz : g.stageMap p m (U.forward p n m hnm z) = 0 := by
    rw [g.forward_natural]
    exact hm
  let S := ShortComplex.mk (f.app m) (g.app m) (hzero m)
  have h := (ShortComplex.moduleCat_exact_iff _).mp
    (groupCohomology.mapShortComplex₂_exact (hexact m) (m + p))
  obtain ⟨a, ha⟩ := h (U.forward p n m hnm z) hz
  change T.cohomologyStage p m at a
  refine ⟨Module.DirectLimit.of ℤ ℕ _ (T.forward p) m a, ?_⟩
  rw [Map.cohomologyMap_of]
  have ha' : f.stageMap p m a = U.forward p n m hnm z := ha
  rw [ha']
  exact Module.DirectLimit.of_f (R := ℤ) (ι := ℕ) (f := U.forward p) (hij := hnm) (x := z)

end IntegralProjectiveTower
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_HorseshoeProjectiveTowers
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Three compatible projective towers resolving a short exact sequence -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G]

theorem horseshoeTower_shortExact (S : ShortComplex (Rep.{0} ℤ G)) (hS : S.ShortExact) (n : ℕ) :
    (ShortComplex.mk ((horseshoeTowerInl S hS).app n) ((horseshoeTowerSnd S hS).app n)
      (horseshoeTower_zero S hS n)).ShortExact :=
  (horseshoeStage S hS n).2

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_CompleteCohomologyMiddleExact
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exactness at the middle coefficient in complete cohomology -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G]

theorem shiftedCompleteCohomology_middle_exact (p : ℕ)
    (S : ShortComplex (Rep.{0} ℤ G)) (hS : S.ShortExact)
    (x : ShiftedCompletedCohomology p S.X₂)
    (hx : shiftedCompletedCohomologyMap p S.g x = 0) :
    ∃ y : ShiftedCompletedCohomology p S.X₁, shiftedCompletedCohomologyMap p S.f y = x := by
  let L := horseshoeLeftTower S hS
  let M := horseshoeMiddleTower S hS
  let R := horseshoeRightTower S hS
  let f := horseshoeTowerInl S hS
  let g := horseshoeTowerSnd S hS
  let eL := L.completeCohomologyEquiv (L.obj 0) (Iso.refl _) p
  let eM := M.completeCohomologyEquiv (M.obj 0) (Iso.refl _) p
  let eR := R.completeCohomologyEquiv (R.obj 0) (Iso.refl _) p
  let z := eM.symm x
  have hz : g.cohomologyMap p z = 0 := by
    apply eR.injective
    rw [map_zero]
    have h := IntegralProjectiveTower.completeCohomologyEquiv_natural g p z
    change eR (g.cohomologyMap p z) = shiftedCompletedCohomologyMap p S.g (eM z) at h
    rw [show eM z = x from eM.apply_symm_apply x] at h
    exact h.trans hx
  obtain ⟨a, ha⟩ := IntegralProjectiveTower.cohomology_exact f g
    (horseshoeTower_zero S hS) (horseshoeTower_shortExact S hS) p z hz
  refine ⟨eL a, ?_⟩
  have h := IntegralProjectiveTower.completeCohomologyEquiv_natural f p a
  change eM (f.cohomologyMap p a) = shiftedCompletedCohomologyMap p S.f (eL a) at h
  rw [ha] at h
  exact h.symm.trans (eM.apply_symm_apply x)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_PresentationRotation
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.booleanPartitionStage_projective _root_.OAI.PolycyclicRecognition.integralRepresentationSum_projective _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalizedFreeRepresentation_countable _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Rotating a short exact sequence using a projective cover -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2300] Prod.instModule
variable {G : Type} [Group G]

theorem rotation_fst_inl_stable (S : ShortComplex (Rep.{0} ℤ G)) :
    stableRepresentationClass _ _ (rotationFst S ≫ rotationInl S) =
      stableRepresentationClass _ _ (𝟙 (rotationMiddle S)) := by
  apply (stableRepresentationClass_eq_iff_projective_factor _ _).mpr
  refine ⟨normalizedFreeRepresentation S.X₃, inferInstance, -rotationSnd S, rotationInr S, ?_⟩
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  change (0, -x.2) = (x.1, 0) - x
  ext <;> simp

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_CompleteCohomologyLongExact
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalizedFreeRepresentation_countable _root_.OAI.PolycyclicRecognition.normalizedSyzygy_countable _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exactness at the completed connecting maps -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G]

theorem shiftedCompleteCohomology_boundary_exact (p : ℕ)
    (S : ShortComplex (Rep.{0} ℤ G)) (hS : S.ShortExact)
    (x : ShiftedCompletedCohomology (p + 1) S.X₁)
    (hx : shiftedCompletedCohomologyMap (p + 1) S.f x = 0) :
    ∃ y : ShiftedCompletedCohomology p S.X₃, shiftedCompleteBoundary p S hS y = x := by
  let R := presentationRotation S hS
  let hR := presentationRotation_shortExact S hS
  let z := shiftedCompletedCohomologyMap (p + 1) (rotationInl S) x
  have hz : shiftedCompletedCohomologyMap (p + 1) R.g z = 0 := by
    change shiftedCompletedCohomologyMap (p + 1) (rotationProjection S hS)
      (shiftedCompletedCohomologyMap (p + 1) (rotationInl S) x) = 0
    rw [← shiftedCompletedCohomologyMap_comp_apply, rotationInl_projection]
    exact hx
  obtain ⟨a, ha⟩ := shiftedCompleteCohomology_middle_exact (p + 1) R hR z hz
  change ShiftedCompletedCohomology (p + 1) (normalizedSyzygy S.X₃) at a
  refine ⟨shiftedSyzygyAddEquiv p S.X₃ a, ?_⟩
  rw [shiftedCompleteBoundary_apply, AddEquiv.symm_apply_apply]
  have h := congrArg (shiftedCompletedCohomologyMap (p + 1) (rotationFst S)) ha
  change shiftedCompletedCohomologyMap (p + 1) (rotationFst S)
    (shiftedCompletedCohomologyMap (p + 1) (rotationInclusion S hS) a) =
      shiftedCompletedCohomologyMap (p + 1) (rotationFst S)
        (shiftedCompletedCohomologyMap (p + 1) (rotationInl S) x) at h
  rw [← shiftedCompletedCohomologyMap_comp_apply, ← shiftedCompletedCohomologyMap_comp_apply,
    rotationInclusion_fst, rotationInl_fst] at h
  have hi := ConcreteCategory.congr_hom ((shiftedCompletedCohomologyFunctor (p + 1)).map_id S.X₁) x
  exact h.trans hi

theorem presentationKernelMap_normalized_stable (A : Rep.{0} ℤ G) :
    stableRepresentationClass _ _
        (presentationKernelMap (normalizedSyzygySequence A) (normalizedSyzygySequence_shortExact A)) =
      stableRepresentationClass _ _ (𝟙 (normalizedSyzygy A)) := by
  have h := normalizedSyzygy_stable_of_lift (𝟙 A)
    (presentationFreeLift (normalizedSyzygySequence A) (normalizedSyzygySequence_shortExact A))
    (by
      have h := presentationFreeLift_g (normalizedSyzygySequence A) (normalizedSyzygySequence_shortExact A)
      change presentationFreeLift (normalizedSyzygySequence A) (normalizedSyzygySequence_shortExact A) ≫
        normalizedFreeAugmentation A = normalizedFreeAugmentation A at h
      exact h.trans (Category.comp_id (normalizedFreeAugmentation A)).symm)
    (presentationKernelMap (normalizedSyzygySequence A) (normalizedSyzygySequence_shortExact A))
    (presentationKernelMap_f (normalizedSyzygySequence A) (normalizedSyzygySequence_shortExact A))
  change stableRepresentationClass _ _ (normalizedSyzygyFunctor.map (𝟙 A)) = _ at h
  rw [CategoryTheory.Functor.map_id] at h
  exact h.symm

theorem shiftedCompleteBoundary_rotation (p : ℕ)
    (S : ShortComplex (Rep.{0} ℤ G)) (hS : S.ShortExact)
    (x : ShiftedCompletedCohomology p S.X₂) :
    shiftedSyzygyAddEquiv p S.X₃
      (shiftedCompleteBoundary p (presentationRotation S hS) (presentationRotation_shortExact S hS) x) =
        -shiftedCompletedCohomologyMap p S.g x := by
  let F := shiftedCompletedCohomologyFunctor (p + 1) (G := G)
  let a : normalizedSyzygy S.X₂ ⟶ normalizedSyzygy S.X₃ :=
    presentationKernelMap (presentationRotation S hS) (presentationRotation_shortExact S hS)
  let b : normalizedSyzygy S.X₃ ⟶ normalizedSyzygy S.X₃ :=
    presentationKernelMap (normalizedSyzygySequence S.X₃) (normalizedSyzygySequence_shortExact S.X₃)
  change shiftedSyzygyAddEquiv p S.X₃
    (shiftedCompletedCohomologyMap (p + 1) a ((shiftedSyzygyAddEquiv p S.X₂).symm x)) = _
  have h := shiftedCompleteFunctor_map_eq_of_stable_eq (p + 1) _ _
    (presentationKernelMap_stable_natural (presentationRotation_shortExact S hS)
      (normalizedSyzygySequence_shortExact S.X₃) (rotationToNormalized S hS))
  change F.map (normalizedSyzygyMap S.g ≫ b) = F.map (a ≫ (-𝟙 (normalizedSyzygy S.X₃))) at h
  have hn := shiftedCompleteFunctor_map_eq_of_stable_eq (p + 1) _ _
    (presentationKernelMap_normalized_stable S.X₃)
  change F.map b = F.map (𝟙 (normalizedSyzygy S.X₃)) at hn
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp, hn,
    CategoryTheory.Functor.map_id, Category.comp_id, CategoryTheory.Functor.map_neg,
    CategoryTheory.Functor.map_id, Preadditive.comp_neg, Category.comp_id] at h
  have he := congrArg ModuleCat.Hom.hom h
  change shiftedCompletedCohomologyMap (p + 1) (normalizedSyzygyMap S.g) =
    -shiftedCompletedCohomologyMap (p + 1) a at he
  have hv := LinearMap.congr_fun he ((shiftedSyzygyAddEquiv p S.X₂).symm x)
  change shiftedCompletedCohomologyMap (p + 1) (normalizedSyzygyMap S.g)
      ((shiftedSyzygyAddEquiv p S.X₂).symm x) =
    -(shiftedCompletedCohomologyMap (p + 1) a ((shiftedSyzygyAddEquiv p S.X₂).symm x)) at hv
  have hv' := congrArg Neg.neg hv
  simp only [neg_neg] at hv'
  rw [← hv', map_neg, shiftedSyzygyEquiv_natural, AddEquiv.apply_symm_apply]

theorem rotation_complete_retract (p : ℕ) (S : ShortComplex (Rep.{0} ℤ G))
    (x : ShiftedCompletedCohomology p (rotationMiddle S)) :
    shiftedCompletedCohomologyMap p (rotationInl S)
      (shiftedCompletedCohomologyMap p (rotationFst S) x) = x := by
  rw [← shiftedCompletedCohomologyMap_comp_apply]
  have h := shiftedCompleteFunctor_map_eq_of_stable_eq p _ _ (rotation_fst_inl_stable S)
  rw [CategoryTheory.Functor.map_id] at h
  exact ConcreteCategory.congr_hom h x

theorem rotation_complete_inclusion_zero (p : ℕ) (S : ShortComplex (Rep.{0} ℤ G))
    (hS : S.ShortExact) (x : ShiftedCompletedCohomology p (normalizedSyzygy S.X₃))
    (hx : shiftedCompletedCohomologyMap p (presentationKernelMap S hS) x = 0) :
    shiftedCompletedCohomologyMap p (rotationInclusion S hS) x = 0 := by
  let z := shiftedCompletedCohomologyMap p (rotationInclusion S hS) x
  have hz : shiftedCompletedCohomologyMap p (rotationFst S) z = 0 := by
    change shiftedCompletedCohomologyMap p (rotationFst S)
      (shiftedCompletedCohomologyMap p (rotationInclusion S hS) x) = 0
    rw [← shiftedCompletedCohomologyMap_comp_apply, rotationInclusion_fst]
    exact hx
  change z = 0
  rw [← rotation_complete_retract p S z, hz, map_zero]

theorem shiftedCompleteCohomology_map_boundary_exact (p : ℕ)
    (S : ShortComplex (Rep.{0} ℤ G)) (hS : S.ShortExact)
    (x : ShiftedCompletedCohomology p S.X₃) (hx : shiftedCompleteBoundary p S hS x = 0) :
    ∃ y : ShiftedCompletedCohomology p S.X₂, shiftedCompletedCohomologyMap p S.g y = x := by
  let a := (shiftedSyzygyAddEquiv p S.X₃).symm x
  have ha : shiftedCompletedCohomologyMap (p + 1) (presentationKernelMap S hS) a = 0 := hx
  have hj := rotation_complete_inclusion_zero (p + 1) S hS a ha
  obtain ⟨b, hb⟩ := shiftedCompleteCohomology_boundary_exact p
    (presentationRotation S hS) (presentationRotation_shortExact S hS) a hj
  change ShiftedCompletedCohomology p S.X₂ at b
  refine ⟨-b, ?_⟩
  have h := shiftedCompleteBoundary_rotation p S hS b
  rw [hb, show shiftedSyzygyAddEquiv p S.X₃ a = x from
    (shiftedSyzygyAddEquiv p S.X₃).apply_symm_apply x] at h
  rw [map_neg]
  exact h.symm

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_CompleteCohomologyFiniteResolution
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Vanishing along a finite exact coefficient resolution -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G]

theorem shiftedCompleteCohomology_vanishing_of_shortExact (p : ℕ)
    (S : ShortComplex (Rep.{0} ℤ G)) (hS : S.ShortExact)
    (hA : Subsingleton (ShiftedCompletedCohomology (p + 1) S.X₁))
    (hB : Subsingleton (ShiftedCompletedCohomology p S.X₂)) :
    Subsingleton (ShiftedCompletedCohomology p S.X₃) := by
  apply subsingleton_of_forall_eq (0 : ShiftedCompletedCohomology p S.X₃)
  intro x
  have hx : shiftedCompleteBoundary p S hS x = 0 := hA.elim _ _
  obtain ⟨y, hy⟩ := shiftedCompleteCohomology_map_boundary_exact p S hS x hx
  rw [← hy, hB.elim y 0, map_zero]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_SubgroupInductionExact
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact induction from arbitrary subgroups -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits Representation
open scoped MonoidAlgebra TensorProduct
attribute [local instance 2000] Rep.hV2
variable (k : Type) [CommRing k] {G : Type} [Group G] (N : Subgroup G)

theorem subgroupInductionCoordinates_naturality {A B : Rep k N} (f : A ⟶ B) :
    (subgroupInductionCoordinates N k B).comp (Rep.indMap N.subtype f).hom.toLinearMap =
      (Finsupp.mapRange.linearMap f.hom.toLinearMap).comp (subgroupInductionCoordinates N k A) := by
  apply IndV.hom_ext
  intro g
  apply LinearMap.ext
  intro a
  change subgroupInductionCoordinates N k B ((Rep.indMap N.subtype f).hom
      (IndV.mk N.subtype A.ρ g a)) = _
  rw [subgroupInductionMap_mk k N f g a, subgroupInductionCoordinates_mk N k B g (f.hom a)]
  change _ = Finsupp.mapRange.linearMap f.hom.toLinearMap
    (subgroupInductionCoordinates N k A (IndV.mk N.subtype A.ρ g a))
  rw [subgroupInductionCoordinates_mk N k A g a]
  simp only [Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single]
  congr 1
  exact (Rep.hom_comm_apply f (subgroupRightPart N g)⁻¹ a).symm

theorem subgroupInductionMap_injective {A B : Rep k N} (f : A ⟶ B)
    (hf : Function.Injective f.hom) : Function.Injective (Rep.indMap N.subtype f).hom := by
  intro x y hxy
  apply (subgroupInductionEquiv N k A).injective
  have h := congrArg (subgroupInductionCoordinates N k B) hxy
  have hx := LinearMap.congr_fun (subgroupInductionCoordinates_naturality k N f) x
  have hy := LinearMap.congr_fun (subgroupInductionCoordinates_naturality k N f) y
  simp only [LinearMap.comp_apply, IntertwiningMap.toLinearMap_apply] at hx hy
  change subgroupInductionCoordinates N k B ((Rep.indMap N.subtype f).hom x) =
    subgroupInductionCoordinates N k B ((Rep.indMap N.subtype f).hom y) at h
  rw [hx, hy] at h
  exact Finsupp.mapRange_injective _ (map_zero f.hom) hf h

instance subgroupInduction_preservesMonomorphisms :
    (Rep.indFunctor k N.subtype).PreservesMonomorphisms where
  preserves f hf := by
    rw [Rep.mono_iff_injective]
    exact subgroupInductionMap_injective k N f ((Rep.mono_iff_injective f).mp hf)

instance subgroupInduction_preservesHomology :
    (Rep.indFunctor k N.subtype).PreservesHomology :=
  Functor.preservesHomology_of_preservesMonos_and_cokernels _


end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_SubgroupInductionDimension
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.booleanPartitionStage_projective _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.horseshoeCover_projective _root_.OAI.PolycyclicRecognition.integralRepresentationSum_projective _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.normalizedFreeRepresentation_countable _root_.OAI.PolycyclicRecognition.normalizedFreeRepresentation_integral_projective _root_.OAI.PolycyclicRecognition.normalizedSyzygy_countable _root_.OAI.PolycyclicRecognition.normalizedSyzygy_integral_projective _root_.OAI.PolycyclicRecognition.normalizedSyzygy_projective _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact subgroup induction preserves finite projective-dimension bounds -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G] (H : Subgroup G)

theorem subgroupInduction_projectiveDimension_le (A : Rep.{0} ℤ H) (d : ℕ)
    (hA : HasProjectiveDimensionLE A d) :
    HasProjectiveDimensionLE (Rep.ind H.subtype A) d := by
  induction d generalizing A with
  | zero =>
    have hp : Projective A := (projective_iff_hasProjectiveDimensionLE_zero A).mpr hA
    exact (projective_iff_hasProjectiveDimensionLE_zero _).mp
      ((Rep.indFunctor ℤ H.subtype).projective_obj_of_projective hp)
  | succ d ih =>
    let S := normalizedSyzygySequence A
    have hS := normalizedSyzygySequence_shortExact A
    have hk : HasProjectiveDimensionLE (normalizedSyzygy A) d :=
      hS.hasProjectiveDimensionLT_X₁ (d + 1)
        (hasProjectiveDimensionLT_of_ge (normalizedFreeRepresentation A) 1 (d + 1) (by omega)) hA
    have hki := ih (normalizedSyzygy A) hk
    let F := Rep.indFunctor ℤ H.subtype
    let : Mono S.f := hS.mono_f
    let : Epi S.g := hS.epi_g
    have hFS := hS.map F
    let : Projective (F.obj (normalizedFreeRepresentation A)) :=
      F.projective_obj_of_projective (inferInstance : Projective (normalizedFreeRepresentation A))
    exact hFS.hasProjectiveDimensionLT_X₃ (d + 1) hki
      (hasProjectiveDimensionLT_of_ge (F.obj (normalizedFreeRepresentation A)) 1 (d + 2) (by omega))

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_CompleteVanishingExactFunctor
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.booleanPartitionStage_projective _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.finitelyGeneratedSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.integralRepresentationSum_projective _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite-dimensional resolutions after an exact coefficient functor

Only the images of countable free covers must have vanishing completion.
The terminal projective is handled by its actual retract of a free cover.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
open scoped MonoidAlgebra
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G Q : Type} [Group G] [Group Q]

theorem shiftedCompleteCohomology_subsingleton_of_retract
    (p : ℕ) {A B : Rep.{0} ℤ G} (r : Retract A B)
    (hB : Subsingleton (ShiftedCompletedCohomology p B)) :
    Subsingleton (ShiftedCompletedCohomology p A) := by
  let F := shiftedCompletedCohomologyFunctor (G := G) p
  have hr : F.map r.i ≫ F.map r.r = 𝟙 (F.obj A) := by
    rw [← F.map_comp, r.retract, F.map_id]
  apply subsingleton_of_forall_eq (0 : ShiftedCompletedCohomology p A)
  intro x
  have hx := ConcreteCategory.congr_hom hr x
  change (F.map r.r) ((F.map r.i) x) = x at hx
  rw [hB.elim ((F.map r.i) x) 0] at hx
  exact hx.symm.trans (map_zero (F.map r.r).hom)

variable (F : Rep.{0} ℤ Q ⥤ Rep.{0} ℤ G) [F.Additive]
variable [F.PreservesHomology] [F.PreservesMonomorphisms] [F.PreservesEpimorphisms]

/-- A finite projective-dimensional coefficient can be used without choosing
finitely generated projectives, provided its countable free covers vanish. -/
theorem exactFunctor_complete_vanishing_of_finite_dimension [Countable Q]
    (hfree : ∀ (B : Rep.{0} ℤ Q) [Countable B] (p : ℕ),
      Subsingleton (ShiftedCompletedCohomology p (F.obj (normalizedFreeRepresentation B))))
    (A : Rep.{0} ℤ Q) [Countable A] (d : ℕ)
    (hd : HasProjectiveDimensionLE A d) (p : ℕ) :
    Subsingleton (ShiftedCompletedCohomology p (F.obj A)) := by
  induction d generalizing A p with
  | zero =>
    let : Projective A := (projective_iff_hasProjectiveDimensionLE_zero A).mpr hd
    let r : Retract A (normalizedFreeRepresentation A) :=
      ⟨Projective.factorThru (𝟙 A) (normalizedFreeAugmentation A),
        normalizedFreeAugmentation A, Projective.factorThru_comp _ _⟩
    apply shiftedCompleteCohomology_subsingleton_of_retract p (r.map F)
    exact hfree A p
  | succ d ih =>
    let S := normalizedSyzygySequence A
    have hS := normalizedSyzygySequence_shortExact A
    have hk : HasProjectiveDimensionLE (normalizedSyzygy A) d :=
      hS.hasProjectiveDimensionLT_X₁ (d + 1)
        (hasProjectiveDimensionLT_of_ge (normalizedFreeRepresentation A) 1 (d + 1) (by omega)) hd
    let : Mono S.f := hS.mono_f
    let : Epi S.g := hS.epi_g
    exact shiftedCompleteCohomology_vanishing_of_shortExact p (S.map F) (hS.map F)
      (ih (normalizedSyzygy A) hk (p + 1)) (hfree A p)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_CountableFreeRetract
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.finitelyGeneratedSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Countably generated free representations are retracts of one fixed free module -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
open scoped MonoidAlgebra
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {Q G : Type} [Group Q] [Group G]

variable (F : Rep.{0} ℤ Q ⥤ Rep.{0} ℤ G) [F.Additive]
variable [F.PreservesHomology] [F.PreservesMonomorphisms] [F.PreservesEpimorphisms]

theorem exactFunctor_complete_vanishing_of_countable_free [Countable Q]
    (hfree : ∀ p : ℕ,
      Subsingleton (ShiftedCompletedCohomology p (F.obj (Rep.free ℤ Q ℕ))))
    (A : Rep.{0} ℤ Q) [Countable A] (d : ℕ)
    (hd : HasProjectiveDimensionLE A d) (p : ℕ) :
    Subsingleton (ShiftedCompletedCohomology p (F.obj A)) := by
  apply exactFunctor_complete_vanishing_of_finite_dimension F _ A d hd p
  intro B _ p
  exact shiftedCompleteCohomology_subsingleton_of_retract p
    ((countableFreeRetract (Q := Q) {b : B // b ≠ 0}).map F) (hfree p)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_CountableUnionDimension
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instNonemptyBases _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesHomology _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integral dimension bounds for countable increasing unions -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2100] Linear.homModule

variable {G : Type} [Group G]

theorem exists_fg_subgroup_exhaustion [Countable G] :
    ∃ S : ℕ → Subgroup G, Monotone S ∧ (∀ n, (S n).FG) ∧
      ∀ g, ∃ n, g ∈ S n := by
  obtain ⟨e, he⟩ := exists_surjective_nat G
  let T (n : ℕ) : Set G := Set.range (fun i : Fin n => e i)
  let S (n : ℕ) := Subgroup.closure (T n)
  refine ⟨S, ?_, ?_, ?_⟩
  · intro i j hij
    apply Subgroup.closure_mono
    rintro g ⟨k, rfl⟩
    exact ⟨⟨k, k.isLt.trans_le hij⟩, rfl⟩
  · intro n
    exact (Subgroup.fg_iff _).mpr ⟨T n, rfl, Set.finite_range _⟩
  · intro g
    obtain ⟨n, rfl⟩ := he g
    exact ⟨n + 1, Subgroup.subset_closure ⟨⟨n, Nat.lt_succ_self n⟩, rfl⟩⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_FiniteIndexTraceRetract
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Relative trace-one coefficients are retracts of induced restrictions

The averaging is over a finite coset space, so the subgroup itself may be
infinite. The trace element is invariant under that subgroup.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits Representation
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G R : Type} [Group G] [Ring R] [MulSemiringAction G R]
variable (N : Subgroup G)

variable (e : R) (he : ∀ n : N, (n : G) • e = e)

variable [Fintype (subgroupRightCosets N)]

include he in
theorem relativeTraceSection_counit
    (htrace : ∑ c : subgroupRightCosets N,
      (subgroupRightRepresentative N c)⁻¹ • e = 1) :
    relativeTraceSection N e he ≫ relativeTraceCounit N = 𝟙 _ := by
  apply Rep.hom_ext
  apply IntertwiningMap.ext
  ext b
  change (relativeTraceCounit N).hom (relativeTraceSectionLinear N e he b) = b
  simp only [relativeTraceSectionLinear, LinearMap.sum_apply]
  rw [map_sum]
  have hc (c : subgroupRightCosets N) :
      (relativeTraceCounit N).hom (relativeTraceCosetTerm N e he c b) =
        ((subgroupRightRepresentative N c)⁻¹ • e) * b := by
    rw [← subgroupRightRepresentative_coset N c, relativeTraceCosetTerm_mk]
    change (relativeTraceCounit N).hom (IndV.mk _ _ _ _) = _
    rw [relativeTraceCounit_mk]
    change (subgroupRightRepresentative N c)⁻¹ •
      (e * ((subgroupRightRepresentative N c) • b)) = _
    rw [smul_mul', inv_smul_smul, subgroupRightRepresentative_coset]
  simp_rw [hc]
  rw [← Finset.sum_mul, htrace, one_mul]

include he in
theorem relativeTrace_dimension_le (d : ℕ)
    (htrace : ∑ c : subgroupRightCosets N,
      (subgroupRightRepresentative N c)⁻¹ • e = 1)
    (hd : HasProjectiveDimensionLE
      (Rep.res N.subtype (relativeTraceRepresentation (G := G) (R := R))) d) :
    HasProjectiveDimensionLE (relativeTraceRepresentation (G := G) (R := R)) d := by
  let := subgroupInduction_projectiveDimension_le N _ d hd
  let r : Retract (relativeTraceRepresentation (G := G) (R := R))
      (Rep.ind N.subtype (Rep.res N.subtype (relativeTraceRepresentation (G := G) (R := R)))) :=
    ⟨relativeTraceSection N e he, relativeTraceCounit N,
      relativeTraceSection_counit N e he htrace⟩
  exact r.hasProjectiveDimensionLT (d + 1)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_FiniteSolvableDerivedBound
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instNonemptyBases _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.finite_templateSymmetryGroup _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteSubtypeLinearEquivRealIdMemSubgroupLinearSupportSymmetryGroup _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesHomology _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Compatibility with OpenAI's Mathlib (d13f23b): a lemma it has and ours lacks. -/

private theorem Subgroup.card_lt_of_lt_p0 {G : Type*} [Group G] {H K : Subgroup G} [Finite K] (h : H < K) :
    Nat.card H < Nat.card K :=
  (Set.toFinite _).card_lt_card h

namespace OAI

/-! # Explicit derived-length bounds for finite soluble quotients -/
noncomputable section
namespace PolycyclicRecognition
variable {G : Type} [Group G]

theorem finite_solvable_derivedSeries_card [Finite G] [Group.IsSolvable G] :
    derivedSeries G (Nat.card G) = ⊥ := by
  have hb (n : ℕ) (hn : derivedSeries G n ≠ ⊥) :
      Nat.card (derivedSeries G n) + n ≤ Nat.card G := by
    induction n with
    | zero => simpa only [derivedSeries_zero, add_zero] using (⊤ : Subgroup G).card_le_card_group
    | succ n ih =>
      have hn' : derivedSeries G n ≠ ⊥ := by
        intro he
        apply hn
        simp only [derivedSeries_succ, he, Subgroup.commutator_bot_left]
      have hs := Subgroup.card_lt_of_lt_p0 (Group.IsSolvable.commutator_lt_of_ne_bot hn')
      have hi := ih hn'
      change Nat.card (derivedSeries G (n + 1)) < Nat.card (derivedSeries G n) at hs
      omega
  by_contra h
  have hh := hb (Nat.card G) h
  have hp : 0 < Nat.card (derivedSeries G (Nat.card G)) := Nat.card_pos
  omega

theorem normalCore_index_le_factorial (H : Subgroup G) [H.FiniteIndex] :
    H.normalCore.index ≤ H.index.factorial := by
  rw [Subgroup.normalCore_eq_ker, Subgroup.index_ker, Subgroup.index_eq_card, ← Nat.card_perm]
  exact Subgroup.card_le_card_group _

theorem derivedSeries_add_le_ambient (H : Subgroup G) (n r : ℕ)
    (hn : derivedSeries G n ≤ H) : derivedSeries G (n + r) ≤ ambientDerivedSeries H r := by
  induction r with
  | zero => simpa only [add_zero, ambientDerivedSeries_zero] using hn
  | succ r ih =>
    rw [Nat.add_succ, derivedSeries_succ, ambientDerivedSeries_succ]
    exact Subgroup.commutator_mono ih ih

theorem solvable_derivedSeries_bound_of_finiteIndex [Group.IsSolvable G]
    (H : Subgroup G) [H.FiniteIndex] (b r : ℕ) (hb : H.index ≤ b)
    (hr : derivedSeries H r = ⊥) : derivedSeries G (b.factorial + r) = ⊥ := by
  let N := H.normalCore
  let q := QuotientGroup.mk' N
  have hNi : N.index ≤ b.factorial :=
    (normalCore_index_le_factorial H).trans (Nat.factorial_le hb)
  have hq : derivedSeries (G ⧸ N) b.factorial = ⊥ := by
    apply eq_bot_iff.mpr
    have hi : Nat.card (G ⧸ N) ≤ b.factorial := by
      simpa only [← Subgroup.index_eq_card] using hNi
    exact (derivedSeries_antitone (G ⧸ N) hi).trans_eq finite_solvable_derivedSeries_card
  have hn : derivedSeries G b.factorial ≤ H := by
    apply le_trans _ H.normalCore_le
    change derivedSeries G b.factorial ≤ N
    rw [← QuotientGroup.ker_mk' N, ← Subgroup.map_eq_bot_iff]
    rw [map_derivedSeries_eq (QuotientGroup.mk'_surjective N), hq]
  apply eq_bot_iff.mpr
  have hd := derivedSeries_add_le_ambient H b.factorial r hn
  simpa only [ambientDerivedSeries, hr, Subgroup.map_bot] using hd

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_FinitelyGeneratedCountable
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesHomology _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_RationalRepresentationFunctor
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Rationalization and restriction of scalars for group representations

The tensor extension is exact and left adjoint to scalar restriction. Thus it
preserves the projectives used in the finite rational-coefficient resolution.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2300] TensorProduct.instModule
variable {G : Type} [Group G]

attribute [local instance] OAI.PolycyclicRecognition.instModuleRatVIntIntegralRestrictionRepresentation
theorem rationalizeRepresentationFunctor_map_exact
    (S : ShortComplex (Rep.{0} ℤ G)) (hS : S.Exact) :
    (S.map rationalizeRepresentationFunctor).Exact := by
  have hs := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact
    (S.map (forget₂ (Rep ℤ G) (ModuleCat ℤ)))).mp
      (hS.map (forget₂ (Rep ℤ G) (ModuleCat ℤ)))
  apply (forget₂ (Rep ℚ G) (ModuleCat ℚ)).reflects_exact_of_faithful
  apply (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr
  exact Module.Flat.lTensor_exact ℚ (f := S.f.hom.toLinearMap) (g := S.g.hom.toLinearMap) hs

instance instPreservesHomologyRepIntRatRationalizeRepresentationFunctor : (rationalizeRepresentationFunctor (G := G)).PreservesHomology :=
  Functor.preservesHomology_of_map_exact _ rationalizeRepresentationFunctor_map_exact

instance instPreservesMonomorphismsRepIntRatRationalizeRepresentationFunctor : (rationalizeRepresentationFunctor (G := G)).PreservesMonomorphisms :=
  Functor.preservesMonomorphisms_of_map_exact _ rationalizeRepresentationFunctor_map_exact

instance instPreservesEpimorphismsRepIntRatRationalizeRepresentationFunctor : (rationalizeRepresentationFunctor (G := G)).PreservesEpimorphisms :=
  Functor.preservesEpimorphisms_of_map_exact _ rationalizeRepresentationFunctor_map_exact

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_RationalGroupDimension
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.booleanPartitionStage_projective _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.horseshoeCover_projective _root_.OAI.PolycyclicRecognition.integralRepresentationSum_projective _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.normalizedFreeRepresentation_countable _root_.OAI.PolycyclicRecognition.normalizedFreeRepresentation_integral_projective _root_.OAI.PolycyclicRecognition.normalizedSyzygy_countable _root_.OAI.PolycyclicRecognition.normalizedSyzygy_integral_projective _root_.OAI.PolycyclicRecognition.normalizedSyzygy_projective _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The rational group dimension supplied by the integral rational coefficient -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2300] TensorProduct.instModule
variable {G : Type} [Group G]

theorem rationalize_projectiveDimension_le (A : Rep.{0} ℤ G) (d : ℕ)
    (hd : HasProjectiveDimensionLE A d) :
    HasProjectiveDimensionLE (rationalizeRepresentation A) d := by
  let F := rationalizeRepresentationFunctor (G := G)
  induction d generalizing A with
  | zero =>
    have hp : Projective A := (projective_iff_hasProjectiveDimensionLE_zero A).mpr hd
    exact (projective_iff_hasProjectiveDimensionLE_zero _).mp (F.projective_obj_of_projective hp)
  | succ d ih =>
    let S := normalizedSyzygySequence A
    have hS := normalizedSyzygySequence_shortExact A
    have hk : HasProjectiveDimensionLE (normalizedSyzygy A) d :=
      hS.hasProjectiveDimensionLT_X₁ (d + 1)
        (hasProjectiveDimensionLT_of_ge (normalizedFreeRepresentation A) 1 (d + 1) (by omega)) hd
    have hki := ih (normalizedSyzygy A) hk
    let : Mono S.f := hS.mono_f
    let : Epi S.g := hS.epi_g
    let : Projective (F.obj (normalizedFreeRepresentation A)) :=
      F.projective_obj_of_projective (inferInstance : Projective (normalizedFreeRepresentation A))
    exact (hS.map F).hasProjectiveDimensionLT_X₃ (d + 1) hki
      (hasProjectiveDimensionLT_of_ge (F.obj (normalizedFreeRepresentation A)) 1 (d + 2) (by omega))

theorem rationalGroup_dimension_le_of_integral_rational (d : ℕ)
    (hd : HasProjectiveDimensionLE (Rep.trivial ℤ G ℚ) d) :
    HasProjectiveDimensionLE (Rep.trivial ℚ G ℚ) d := by
  let := rationalize_projectiveDimension_le (Rep.trivial ℤ G ℚ) d hd
  exact (rationalTrivialRetract (G := G)).hasProjectiveDimensionLT (d + 1)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_RationalFiniteResolution
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The finite rational group resolution needed for the homology bound -/
noncomputable section
namespace PolycyclicRecognition.RationalResolution
open CategoryTheory CategoryTheory.Limits
variable {G : Type} [Group G] (P : ProjectiveResolution (Rep.trivial ℚ G ℚ))

variable {G : Type} [Group G] (P : ProjectiveResolution (Rep.trivial ℚ G ℚ)) (d : ℕ)


theorem groupHomology_isZero_above_dimension (d : ℕ)
    [HasProjectiveDimensionLE (Rep.trivial ℚ G ℚ) d]
    (A : Rep ℚ G) (i : ℕ) (hi : d < i) : IsZero (groupHomology A i) := by
  classical
  let P := finiteProjectiveResolution (Rep.standardResolution ℚ G) d
  have hP : IsZero (P.complex.X i) :=
    finiteTruncation_isZero (Rep.standardResolution ℚ G) d i hi
  have hX : IsZero ((P.complex.coinvariantsTensorObj A).X i) :=
    ((Rep.coinvariantsTensor ℚ G).obj A).map_isZero hP
  refine IsZero.of_iso ?_ (groupHomologyIso A i P)
  apply HomologicalComplex.ExactAt.isZero_homology
  apply ShortComplex.exact_of_isZero_X₂
  simpa only [HomologicalComplex.shortComplexFunctor_obj_X₂] using hX

end PolycyclicRecognition.RationalResolution

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_DimensionFromRegularCohomology
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.cyclicTopHomologyInjection_mono _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesHomology _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
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

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_PoincareTopHomology
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.cyclicTopHomologyInjection_mono _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesHomology _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_RationalHomologyDimension
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.rationalModuleFunctor_preservesFiniteColimits _root_.OAI.PolycyclicRecognition.rationalModuleFunctor_preservesFiniteLimits _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesHomology _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Detecting dimension using rational homology with coefficients

Shapiro's lemma passes a uniform bound to subgroups. The orientation module
detects the dimension of an integral Poincare duality group even after
rationalization. No finiteness of coefficient representations is required.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
attribute [local instance 2000] Rep.hV2 Rep.instLinear ModuleCat.isModule
attribute [local instance 2300] TensorProduct.instModule
variable {G : Type} [Group G]

theorem RationalHomologyDimensionLE.subgroup {d : ℕ}
    (hG : RationalHomologyDimensionLE G d) (H : Subgroup G) :
    RationalHomologyDimensionLE H d := by
  classical
  intro A i hi
  exact (hG (Rep.ind H.subtype A) i hi).of_iso
    (rationalModuleFunctor.mapIso (groupHomology.indIso H A i).symm)

theorem IsIntegralPoincareDualityGroup.dimension_le_of_rational_homology_bound
    {n d : ℕ} (hG : IsIntegralPoincareDualityGroup G n)
    (hd : RationalHomologyDimensionLE G d) : n ≤ d := by
  by_contra hnd
  obtain ⟨D, ⟨eD⟩, hD⟩ := hG.topHomology_orientation
  obtain ⟨eH⟩ := hD D
  let e : groupHomology D n ≃ₗ[ℤ] ℤ :=
    eH.trans (rankOneEndomorphismsEquiv D eD)
  let eQ : (ℚ ⊗[ℤ] groupHomology D n) ≃ₗ[ℤ] ℚ :=
    ((e.baseChange ℤ ℚ _ _).restrictScalars ℤ).trans (TensorProduct.rid ℤ ℚ)
  have hz := hd D n (by omega)
  let : Subsingleton (ℚ ⊗[ℤ] groupHomology D n) :=
    ModuleCat.isZero_iff_subsingleton.mp hz
  have h : (1 : ℚ) = 0 := by
    calc
      1 = eQ (eQ.symm 1) := (eQ.apply_symm_apply 1).symm
      _ = eQ 0 := congrArg eQ (Subsingleton.elim _ _)
      _ = 0 := map_zero eQ
  exact one_ne_zero h

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_ProjectiveTowerDimension
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.IntegralProjectiveTower.instDirectedSystemNatCohomologyStageCoeLinearMapIntIdForward _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.booleanPartitionStage_projective _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.horseshoeCover_projective _root_.OAI.PolycyclicRecognition.integralRepresentationSum_projective _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.normalizedSyzygy_projective _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesHomology _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A projective tail bounds the dimension at the base of a tower -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
variable {G : Type} [Group G]

theorem IntegralProjectiveTower.dimension_of_tail (T : IntegralProjectiveTower G)
    (n d : ℕ) (h : HasProjectiveDimensionLE (T.obj n) d) :
    HasProjectiveDimensionLE (T.obj 0) (n + d) := by
  induction n generalizing d with
  | zero => simpa only [Nat.zero_add] using h
  | succ n ih =>
    have hprev : HasProjectiveDimensionLE (T.obj n) (d + 1) :=
      (T.shortExact n).hasProjectiveDimensionLT_X₃ (d + 1) h
        (hasProjectiveDimensionLT_of_ge (T.projectiveObj n) 1 (d + 2) (by omega))
    simpa only [Nat.succ_add, Nat.add_succ] using ih (d + 1) hprev

theorem IntegralProjectiveTower.dimension_of_projective_tail (T : IntegralProjectiveTower G)
    (n : ℕ) [Projective (T.obj n)] : HasProjectiveDimensionLE (T.obj 0) n := by
  simpa only [Nat.add_zero] using T.dimension_of_tail n 0 inferInstance

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_IntegerProjectiveCoefficientDimension
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.cyclicTopHomologyInjection_mono _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesHomology _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The integral dimension bound for an integer-projective coefficient -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits MonoidalCategory
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G]

set_option synthInstance.maxHeartbeats 400000 in
theorem integerProjectiveCoefficient_dimension_le (A : Rep.{0} ℤ G)
    [Module.Projective ℤ A] (d : ℕ) (hd : HasProjectiveDimensionLE (trivialIntegral G) d) :
    HasProjectiveDimensionLE A d := by
  have hΩ : HasProjectiveDimensionLE
      ((iteratedNormalizedSyzygy d).obj (trivialIntegral G)) 0 :=
    iteratedNormalizedSyzygy_projectiveDimension (trivialIntegral G) d 0
      (by simpa only [Nat.add_zero] using hd)
  have hproj : Projective ((iteratedNormalizedSyzygy d).obj (trivialIntegral G)) :=
    (projective_iff_hasProjectiveDimensionLE_zero _).mpr hΩ
  let : Projective ((tensorNormalizedProjectiveTower A).obj d) :=
    @representation_tensor_projective G _ A
      ((iteratedNormalizedSyzygy d).obj (trivialIntegral G)) inferInstance hproj
  let := (tensorNormalizedProjectiveTower A).dimension_of_projective_tail d
  exact hasProjectiveDimensionLT_of_iso (tensorNormalizedTowerBaseIso A) (d + 1)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_TensorFiniteDimension
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.horseshoeCover_projective _root_.OAI.PolycyclicRecognition.integralRepresentationSum_projective _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalizedFreeRepresentation_countable _root_.OAI.PolycyclicRecognition.normalizedSyzygy_countable _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesHomology _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Tensoring a finite-dimensional coefficient with an integer-projective module -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits MonoidalCategory
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2300] TensorProduct.instModule
variable {G : Type} [Group G]

theorem integerProjective_tensor_dimension_le (C : Rep.{0} ℤ G)
    [Module.Projective ℤ C] (B : Rep.{0} ℤ G) (d : ℕ)
    (hd : HasProjectiveDimensionLE B d) : HasProjectiveDimensionLE (C ⊗ B) d := by
  induction d generalizing B with
  | zero =>
    let : Projective B := (projective_iff_hasProjectiveDimensionLE_zero B).mpr hd
    exact (projective_iff_hasProjectiveDimensionLE_zero _).mp
      (representation_tensor_projective C B)
  | succ d ih =>
    have hS := normalizedSyzygySequence_shortExact B
    have hK : HasProjectiveDimensionLE (normalizedSyzygy B) d :=
      hS.hasProjectiveDimensionLT_X₁ (d + 1)
        (hasProjectiveDimensionLT_of_ge (normalizedFreeRepresentation B) 1 (d + 1) (by omega)) hd
    have ht := representation_tensorLeft_map_shortExact C (normalizedSyzygySequence B) hS
    let : Projective (C ⊗ normalizedFreeRepresentation B) :=
      representation_tensor_projective C (normalizedFreeRepresentation B)
    exact ht.hasProjectiveDimensionLT_X₃ (d + 1) (ih _ hK)
      (hasProjectiveDimensionLT_of_ge (C ⊗ normalizedFreeRepresentation B) 1 (d + 2) (by omega))

theorem integerProjective_rightTensor_dimension_le (C : Rep.{0} ℤ G)
    [Module.Projective ℤ C] (B : Rep.{0} ℤ G) (d : ℕ)
    (hd : HasProjectiveDimensionLE B d) : HasProjectiveDimensionLE (B ⊗ C) d := by
  let := integerProjective_tensor_dimension_le C B d hd
  exact hasProjectiveDimensionLT_of_iso (β_ C B) (d + 1)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_SequentialProjectiveTelescope
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesHomology _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A length-one projective resolution of a sequential projective colimit

The differential is identity minus the forward shift. Its injectivity uses
induction on coordinates, and the cokernel is the given concrete colimit.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2300] DirectSum.instModule
variable {G : Type} [Group G]
namespace SequentialRepresentationDiagram
variable (D : SequentialRepresentationDiagram G)

theorem telescopeDifferential_injective : Function.Injective D.telescopeDifferential.hom := by
  apply (injective_iff_map_eq_zero _).mpr
  intro x hx
  change DirectSum ℕ (fun i => (D.obj i).V) at x
  have hc (i : ℕ) : x i = 0 := by
    induction i with
    | zero =>
      have h := congrArg (fun y : D.telescopeSum => y 0) hx
      change x 0 - (D.telescopeShift.hom x) 0 = 0 at h
      rw [telescopeShift_zero D x, sub_zero] at h
      exact h
    | succ i hi =>
      have h := congrArg (fun y : D.telescopeSum => y (i + 1)) hx
      change x (i + 1) - (D.telescopeShift.hom x) (i + 1) = 0 at h
      rw [telescopeShift_succ D x i, hi, map_zero, sub_zero] at h
      exact h
  exact DFinsupp.ext hc

namespace ColimitCocone
variable {D} {A : Rep.{0} ℤ G} (c : D.ColimitCocone A)

theorem telescopeAugmentation_cokernelDescent :
    c.telescopeAugmentation ≫ c.telescopeCokernelDescent =
      cokernel.π D.telescopeDifferential := by
  apply integralRepresentationSum_hom_ext
  intro i
  rw [← Category.assoc]
  change (integralRepresentationSumInclusion D.obj i ≫
    integralRepresentationSumDesc D.obj A c.ι) ≫ c.telescopeCokernelDescent = _
  rw [integralRepresentationSumInclusion_desc]
  exact c.ι_desc _ _ _ i

theorem telescopeSequence_shortExact : c.telescopeSequence.ShortExact := by
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · apply (rep_shortComplex_exact_iff _).mpr
    intro x hx
    change D.telescopeSum at x
    change c.telescopeAugmentation.hom x = 0 at hx
    have hz : (cokernel.π D.telescopeDifferential).hom x = 0 := by
      rw [← c.telescopeAugmentation_cokernelDescent]
      change c.telescopeCokernelDescent.hom (c.telescopeAugmentation.hom x) = 0
      rw [hx, map_zero]
    exact (rep_shortComplex_exact_iff _).mp
      (ShortComplex.exact_cokernel D.telescopeDifferential) x hz
  · exact (Rep.mono_iff_injective _).mpr D.telescopeDifferential_injective
  · exact inferInstanceAs (Epi c.telescopeAugmentation)

end ColimitCocone
end SequentialRepresentationDiagram
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_RationalTensorDimension
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesHomology _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Rational tensoring costs at most one integral projective dimension -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped DirectSum
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2300] TensorProduct.instModule DirectSum.instModule
variable {G : Type} [Group G]

theorem rationalTensor_dimension_le (B : Rep.{0} ℤ G) [Module.Flat ℤ B]
    (d : ℕ) (hd : HasProjectiveDimensionLE B d) :
    HasProjectiveDimensionLE (B ⊗ Rep.trivial ℤ G ℚ) (d + 1) := by
  let c := rationalCoefficientColimit G
  let S := c.telescopeSequence
  let : Module.Projective ℤ S.X₁ := by
    change Module.Projective ℤ (⨁ _ : ℕ, ℤ)
    infer_instance
  let : Module.Projective ℤ S.X₂ := by
    change Module.Projective ℤ (⨁ _ : ℕ, ℤ)
    infer_instance
  have h₁ := integerProjective_rightTensor_dimension_le S.X₁ B d hd
  have h₂ := integerProjective_rightTensor_dimension_le S.X₂ B d hd
  let := h₂
  have hs := representation_tensorLeft_map_shortExact B S c.telescopeSequence_shortExact
  exact hs.hasProjectiveDimensionLT_X₃ (d + 1) h₁
    (hasProjectiveDimensionLT_of_ge (B ⊗ S.X₂) (d + 1) (d + 2) (by omega))

theorem rationalTensor_left_dimension_le (B : Rep.{0} ℤ G) [Module.Flat ℤ B]
    (d : ℕ) (hd : HasProjectiveDimensionLE B d) :
    HasProjectiveDimensionLE (Rep.trivial ℤ G ℚ ⊗ B) (d + 1) := by
  let := rationalTensor_dimension_le B d hd
  exact hasProjectiveDimensionLT_of_iso (β_ B (Rep.trivial ℤ G ℚ)) (d + 2)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_SmallCoefficientRationalRetract
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesHomology _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Rational constants split off the rationalized bounded coefficient ring -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits MonoidalCategory ThompsonNonamenability
open scoped TensorProduct
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2300] TensorProduct.instModule
variable {G : Type} [Group G]

set_option synthInstance.maxHeartbeats 400000 in
theorem rationalCoefficient_dimension_of_smallCoefficient [Countable G]
    (M : InvariantMean G) (d : ℕ)
    (hd : HasProjectiveDimensionLE (smallCoefficientRepresentation G) d) :
    HasProjectiveDimensionLE (Rep.trivial ℤ G ℚ) (d + 1) := by
  let := rationalTensor_left_dimension_le (smallCoefficientRepresentation G) d hd
  exact (smallCoefficientRationalRetract M).hasProjectiveDimensionLT (d + 2)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_SmallCoefficientFiniteIndex
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.cyclicTopHomologyInjection_mono _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.smallCoefficientBoundedReal_apply _root_.OAI.PolycyclicRecognition.smallCoefficientBoundedReal_one _root_.OAI.PolycyclicRecognition.smallCoefficientRealCoinvariantMean_one _root_.OAI.PolycyclicRecognition.smallCoefficientRealMean_one _root_.OAI.PolycyclicRecognition.smallCoefficientTensorMultiply_apply _root_.OAI.PolycyclicRecognition.smallCoefficientTensorUnit_apply _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The small coefficient ring over finite-index subgroups

Relative coset indicators provide an actual trace-one element. Restriction to
an integer-finite-dimensional subgroup therefore bounds the dimension of the
ring over the larger subgroup, without requiring normality.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
attribute [local instance] Classical.propDecidable
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable (G : Type) [Group G] (J : Subgroup G) (hJ : J.FG)
variable (N : Subgroup J) (hN : N.FG)

set_option synthInstance.maxHeartbeats 400000 in
theorem smallCoefficientRelativeTransversal_invariant (n : N) :
    ((n : J) : G) • smallCoefficientRelativeTransversal G J hJ N hN =
      smallCoefficientRelativeTransversal G J hJ N hN := by
  apply Subtype.ext
  funext x
  simp only [smallCoefficientRing_smul_apply, smallCoefficientRelativeTransversal_apply]
  have hp : subgroupRightPart J (((n : J) : G)⁻¹ * x) =
      (n : J)⁻¹ * subgroupRightPart J x := subgroupRightPart_mul J (n : J)⁻¹ x
  rw [hp, N.mul_mem_cancel_left (N.inv_mem n.property)]

set_option synthInstance.maxHeartbeats 400000 in
theorem rightCoset_representative_mul_mem_iff (c : subgroupRightCosets N) (x : J) :
    subgroupRightRepresentative N c * x ∈ N ↔ c = subgroupRightCoset N x⁻¹ := by
  rw [← subgroupRightRepresentative_coset N c]
  constructor
  · intro h
    apply Quotient.sound
    apply (QuotientGroup.rightRel_apply).mpr
    simpa [mul_inv_rev] using N.inv_mem h
  · intro h
    have hh := (QuotientGroup.rightRel_apply).mp (Quotient.exact h)
    simpa [mul_inv_rev] using N.inv_mem hh

local instance instMulSemiringActionSubtypeMemSubgroupForallIntSubringSmallCoefficientRing_r5d1e9b_1 : MulSemiringAction J (SmallCoefficientRing G) :=
  MulSemiringAction.compHom (SmallCoefficientRing G) J.subtype
set_option synthInstance.maxHeartbeats 400000 in
theorem smallCoefficientRelativeTransversal_trace_one
    [Fintype (subgroupRightCosets N)] :
    (∑ c : subgroupRightCosets N, ((subgroupRightRepresentative N c : J)⁻¹ : J) •
      smallCoefficientRelativeTransversal G J hJ N hN) = 1 := by
  let := MulSemiringAction.compHom (SmallCoefficientRing G) J.subtype
  apply Subtype.ext
  funext x
  change ((SmallCoefficientRing G).subtype
    (∑ c : subgroupRightCosets N, (subgroupRightRepresentative N c)⁻¹ •
      smallCoefficientRelativeTransversal G J hJ N hN)) x = 1
  rw [map_sum, Finset.sum_apply]
  change (∑ c : subgroupRightCosets N, (((subgroupRightRepresentative N c)⁻¹ : J) •
    smallCoefficientRelativeTransversal G J hJ N hN).val x) = 1
  have hp (c : subgroupRightCosets N) :
      (((subgroupRightRepresentative N c)⁻¹ : J) •
        smallCoefficientRelativeTransversal G J hJ N hN).val x =
      if c = subgroupRightCoset N (subgroupRightPart J x)⁻¹ then 1 else 0 := by
    change ((((subgroupRightRepresentative N c)⁻¹ : J) : G) •
      smallCoefficientRelativeTransversal G J hJ N hN).val x = _
    rw [smallCoefficientRing_smul_apply, smallCoefficientRelativeTransversal_apply]
    simp only [Subgroup.coe_inv, inv_inv]
    rw [subgroupRightPart_mul, rightCoset_representative_mul_mem_iff]
    split_ifs <;> rfl
  simp_rw [hp]
  simp

set_option synthInstance.maxHeartbeats 400000 in
include hJ hN in
theorem smallCoefficient_finiteIndex_dimension_le [Countable G] [N.FiniteIndex]
    (d : ℕ) (hd : HasProjectiveDimensionLE (trivialIntegral N) d) :
    HasProjectiveDimensionLE (Rep.res J.subtype (smallCoefficientRepresentation G)) d := by
  let := MulSemiringAction.compHom (SmallCoefficientRing G) J.subtype
  let : Finite (subgroupRightCosets N) :=
    Finite.of_equiv (J ⧸ N) (QuotientGroup.quotientRightRelEquivQuotientLeftRel N).symm
  let := Fintype.ofFinite (subgroupRightCosets N)
  apply relativeTrace_dimension_le N (smallCoefficientRelativeTransversal G J hJ N hN)
    (smallCoefficientRelativeTransversal_invariant G J hJ N hN) d
    (smallCoefficientRelativeTransversal_trace_one G J hJ N hN)
  exact integerProjectiveCoefficient_dimension_le _ d hd

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_InductionExhaustionVanishing
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.SequentialRepresentationDiagram.ColimitCocone.telescopeAugmentation_epi _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.iteratedNormalizedSyzygy_integral_projective _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.shiftedCompletedCohomologyFunctor_additive _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Complete vanishing for induction along a subgroup exhaustion

The finite stages may have arbitrarily large projective dimensions. The
ambient group's FP-infinity hypothesis supplies continuity of its completed
cohomology for the actual induced-coefficient colimit.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G]

variable (A : Rep.{0} ℤ G) (H : ℕ → Subgroup G) (K : Subgroup G)
variable (hmono : Monotone H) (hHK : ∀ n, H n ≤ K)
variable (hcover : ∀ g ∈ K, ∃ n, g ∈ H n)

include hmono hHK hcover in
theorem TypeFPInfinity.induction_exhaustion_complete_vanishing (hG : TypeFPInfinity G)
    (p : ℕ)
    (hH : ∀ n, Subsingleton (ShiftedCompletedCohomology p
      (Rep.ind (H n).subtype (Rep.res (H n).subtype A)))) :
    Subsingleton (ShiftedCompletedCohomology p (Rep.ind K.subtype (Rep.res K.subtype A))) := by
  apply hG.shiftedCompleteCohomology_colimit_subsingleton p
    (inducedExhaustionDiagram A H hmono) _ (inducedExhaustionColimit A H K hmono hHK hcover)
  intro n
  let e := (shiftedCompletedCohomologyFunctor p).mapIso (inductionAmbientQuotientIso A (H n))
  apply subsingleton_of_forall_eq (0 : ShiftedCompletedCohomology p
    ((inducedExhaustionDiagram A H hmono).obj n))
  intro x
  apply e.toLinearEquiv.injective
  exact (hH n).elim _ _

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_LocalInductionVanishing
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Vanishing for locally controlled height-kernel coefficients

Only finite projective dimension at each finitely generated subgroup is used;
there is no uniform bound on those dimensions. In particular this applies to
locally finite kernels, and to torsion-free locally nilpotent kernels.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G] [Countable G]

set_option synthInstance.maxHeartbeats 400000 in
theorem TypeFPInfinity.induction_locally_finite_dimension_vanishing
    (hG : TypeFPInfinity G) (A : Rep.{0} ℤ G) (K : Subgroup G) (p : ℕ)
    (hlocal : ∀ J : Subgroup G, J ≤ K → J.FG →
      ∃ d : ℕ, HasProjectiveDimensionLE (Rep.res J.subtype A) d) :
    Subsingleton (ShiftedCompletedCohomology p (Rep.ind K.subtype (Rep.res K.subtype A))) := by
  obtain ⟨S, hS, hfg, hcov⟩ := exists_fg_subgroup_exhaustion (G := K)
  let H : ℕ → Subgroup G := fun n => (S n).map K.subtype
  have hmono : Monotone H := fun _ _ h => Subgroup.map_mono (hS h)
  have hHK (n : ℕ) : H n ≤ K := by
    rintro x ⟨y, _, rfl⟩
    exact y.property
  have hcover : ∀ g ∈ K, ∃ n, g ∈ H n := by
    intro g hg
    obtain ⟨n, hn⟩ := hcov ⟨g, hg⟩
    exact ⟨n, ⟨⟨g, hg⟩, hn, rfl⟩⟩
  apply TypeFPInfinity.induction_exhaustion_complete_vanishing
    A H K hmono hHK hcover hG p
  intro n
  obtain ⟨d, hd⟩ := hlocal (H n) (hHK n) (fg_subgroup_map (hfg n) K.subtype)
  let := subgroupInduction_projectiveDimension_le (H n) (Rep.res (H n).subtype A) d hd
  exact shiftedCompleteCohomology_subsingleton_of_finite_projectiveDimension p _ d

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_LocalVirtualPolycyclicVanishing
attribute [-instance] _root_.GeneratesNS.rho_g_FG _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.cyclicTopHomologyInjection_mono _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Vanishing for locally virtually polycyclic height kernels

The finite-index passage uses the constructed relative trace, allowing torsion
and avoiding a uniform bound on the ranks of finitely generated subgroups.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G]

set_option synthInstance.maxHeartbeats 400000 in
theorem IsVirtuallyPolycyclic.exists_poincareDuality_finiteIndex
    (hG : IsVirtuallyPolycyclic G) :
    ∃ V : Subgroup G, V.FiniteIndex ∧ ∃ n, IsIntegralPoincareDualityGroup V n := by
  obtain ⟨N, hi, hN⟩ := hG
  obtain ⟨T, ht, n, hT⟩ := hN.exists_poincareDuality_finiteIndex
  let V := T.map N.subtype
  have hV : V.FiniteIndex := ⟨by
    change (T.map N.subtype).index ≠ 0
    rw [Subgroup.index_map_subtype]
    exact mul_ne_zero ht.index_ne_zero hi.index_ne_zero⟩
  let e : T ≃* V := T.equivMapOfInjective N.subtype N.subtype_injective
  exact ⟨V, hV, n, hT.of_equiv e⟩

set_option synthInstance.maxHeartbeats 400000 in
theorem smallCoefficient_virtuallyPolycyclic_finite_dimension [Countable G]
    (J : Subgroup G) (hfg : J.FG) (hJ : IsVirtuallyPolycyclic J) :
    ∃ d : ℕ, HasProjectiveDimensionLE (Rep.res J.subtype (smallCoefficientRepresentation G)) d := by
  let : Group.FG J := (Group.fg_iff_subgroup_fg J).mpr hfg
  obtain ⟨N, hi, n, hN⟩ := hJ.exists_poincareDuality_finiteIndex
  let := hi
  have hNfg : N.FG := (Group.fg_iff_subgroup_fg N).mp inferInstance
  obtain ⟨d, hd⟩ := hN.finiteCohomologicalDimension N
  exact ⟨d, smallCoefficient_finiteIndex_dimension_le G J hfg N hNfg d hd⟩

set_option synthInstance.maxHeartbeats 400000 in
theorem TypeFPInfinity.locallyVirtuallyPolycyclic_smallCoefficient_induction_vanishing
    [Countable G] (hG : TypeFPInfinity G) (K : Subgroup G) (p : ℕ)
    (hlocal : ∀ J : Subgroup G, J ≤ K → J.FG → IsVirtuallyPolycyclic J) :
    Subsingleton (ShiftedCompletedCohomology p
      (Rep.ind K.subtype (Rep.res K.subtype (smallCoefficientRepresentation G)))) := by
  apply hG.induction_locally_finite_dimension_vanishing (smallCoefficientRepresentation G) K p
  intro J hJK hfg
  exact smallCoefficient_virtuallyPolycyclic_finite_dimension J hfg (hlocal J hJK hfg)

set_option synthInstance.maxHeartbeats 400000 in
theorem TypeFPInfinity.locallyVirtuallyNilpotent_smallCoefficient_induction_vanishing
    [Countable G] (hG : TypeFPInfinity G) (K : Subgroup G) (p : ℕ)
    (hlocal : ∀ J : Subgroup G, J ≤ K → J.FG → Group.IsVirtuallyNilpotent J) :
    Subsingleton (ShiftedCompletedCohomology p
      (Rep.ind K.subtype (Rep.res K.subtype (smallCoefficientRepresentation G)))) := by
  apply hG.locallyVirtuallyPolycyclic_smallCoefficient_induction_vanishing K p
  intro J hJK hfg
  let : Group.FG J := (Group.fg_iff_subgroup_fg J).mpr hfg
  exact isVirtuallyPolycyclic_of_finitelyGenerated_virtuallyNilpotent J (hlocal J hJK hfg)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_FiniteSumCompleteVanishing
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesHomology _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Complete cohomology of finite sums of vanishing coefficients -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2300] DirectSum.instModule
variable {G ι : Type} [Group G]

theorem integralRepresentationSum_total [Fintype ι] (A : ι → Rep.{0} ℤ G) :
    ∑ i, integralRepresentationSumProjection A i ≫ integralRepresentationSumInclusion A i =
      𝟙 (integralRepresentationSum A) := by
  classical
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  simp only [Rep.sum_hom, Representation.IntertwiningMap.toLinearMap_sum, LinearMap.sum_apply]
  apply DFinsupp.ext
  intro j
  change (∑ i, (integralRepresentationSumInclusion A i).hom (x i)) j = x j
  rw [DFinsupp.finsetSum_apply]
  rw [Finset.sum_eq_single j]
  · exact integralRepresentationSumInclusion_same A j (x j)
  · intro i _ hij
    exact integralRepresentationSumInclusion_ne A i j hij (x i)
  · intro hj
    exact (hj (Finset.mem_univ j)).elim

theorem finiteSum_completeCohomology [Finite ι] (A : ι → Rep.{0} ℤ G) (p : ℕ)
    (hA : ∀ i, Subsingleton (ShiftedCompletedCohomology p (A i))) :
    Subsingleton (ShiftedCompletedCohomology p (integralRepresentationSum A)) := by
  classical
  let := Fintype.ofFinite ι
  let F := shiftedCompletedCohomologyFunctor p (G := G)
  have hmap (i : ι) : F.map (integralRepresentationSumProjection A i) = 0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change shiftedCompletedCohomologyMap p (integralRepresentationSumProjection A i) x = 0
    exact (hA i).elim _ _
  have hzero : 𝟙 (F.obj (integralRepresentationSum A)) = 0 := by
    rw [← F.map_id, ← integralRepresentationSum_total A, F.map_sum]
    apply Finset.sum_eq_zero
    intro i _
    rw [F.map_comp, hmap, zero_comp]
  apply subsingleton_of_forall_eq (0 : ShiftedCompletedCohomology p (integralRepresentationSum A))
  intro x
  exact ConcreteCategory.congr_hom hzero x

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_CountableSumVanishing
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesHomology _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Countable sums of vanishing coefficients under FP-infinity -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2300] DirectSum.instModule
attribute [local instance 2300] Submodule.module
variable {G : Type} [Group G]

theorem sumPrefix_completeCohomology (A : ℕ → Rep.{0} ℤ G) (p n : ℕ)
    (hA : ∀ i, Subsingleton (ShiftedCompletedCohomology p (A i))) :
    Subsingleton (ShiftedCompletedCohomology p (sumPrefixRepresentation A n)) := by
  have hfinite := finiteSum_completeCohomology (fun i : Fin n => A i) p (fun i => hA i)
  let e := (shiftedCompletedCohomologyFunctor p).mapIso (sumPrefixFiniteIso A n)
  apply subsingleton_of_forall_eq (0 : ShiftedCompletedCohomology p (sumPrefixRepresentation A n))
  intro x
  apply e.toLinearEquiv.injective
  exact hfinite.elim _ _

theorem TypeFPInfinity.countableSum_completeCohomology (hG : TypeFPInfinity G)
    (A : ℕ → Rep.{0} ℤ G) (p : ℕ)
    (hA : ∀ i, Subsingleton (ShiftedCompletedCohomology p (A i))) :
    Subsingleton (ShiftedCompletedCohomology p (integralRepresentationSum A)) :=
  hG.shiftedCompleteCohomology_colimit_subsingleton p (sumPrefixDiagram A)
    (integralRepresentationSum A) (sumPrefixColimit A)
    (fun n => sumPrefix_completeCohomology A p n hA)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_FinsuppCompleteVanishing
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesHomology _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The constant-family direct sum form of a countable coefficient sum -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2300] DirectSum.instModule Finsupp.module
variable {G : Type} [Group G]

theorem TypeFPInfinity.finsupp_completeCohomology (hG : TypeFPInfinity G)
    (A : Rep.{0} ℤ G) (p : ℕ)
    (hA : Subsingleton (ShiftedCompletedCohomology p A)) :
    Subsingleton (ShiftedCompletedCohomology p (A.finsupp ℕ)) := by
  have hs := hG.countableSum_completeCohomology (fun _ : ℕ => A) p (fun _ => hA)
  let e := (shiftedCompletedCohomologyFunctor p).mapIso (finsuppIntegralSumIso A ℕ)
  apply subsingleton_of_forall_eq (0 : ShiftedCompletedCohomology p (A.finsupp ℕ))
  intro x
  apply e.toLinearEquiv.injective
  exact hs.elim _ _

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_NormalQuotientCompleteVanishing
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.cyclicTopHomologyInjection_mono _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite-dimensional quotients propagate induced-kernel vanishing

The quotient resolution is inflated and tensored with the coefficient.
Its countable free terms are actual sums of the induced kernel coefficient.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits MonoidalCategory
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2300] TensorProduct.instModule
variable {G : Type} [Group G] (N : Subgroup G) [N.Normal] (A : Rep.{0} ℤ G)

theorem quotientTensorFunctor_map_exact [Module.Flat ℤ A]
    (S : ShortComplex (Rep.{0} ℤ (G ⧸ N))) (hS : S.Exact) :
    (S.map (quotientTensorFunctor N A)).Exact :=
  representation_tensorLeft_map_exact A
    (S.map (Rep.resFunctor (k := ℤ) (QuotientGroup.mk' N)))
    (hS.map (Rep.resFunctor (k := ℤ) (QuotientGroup.mk' N)))

instance quotientTensorFunctor_preservesHomology [Module.Flat ℤ A] :
    (quotientTensorFunctor N A).PreservesHomology :=
  Functor.preservesHomology_of_map_exact _ (quotientTensorFunctor_map_exact N A)

instance quotientTensorFunctor_preservesMonomorphisms [Module.Flat ℤ A] :
    (quotientTensorFunctor N A).PreservesMonomorphisms :=
  Functor.preservesMonomorphisms_of_map_exact _ (quotientTensorFunctor_map_exact N A)

instance quotientTensorFunctor_preservesEpimorphisms [Module.Flat ℤ A] :
    (quotientTensorFunctor N A).PreservesEpimorphisms :=
  Functor.preservesEpimorphisms_of_map_exact _ (quotientTensorFunctor_map_exact N A)

theorem TypeFPInfinity.normalQuotient_complete_vanishing [Countable G]
    [Module.Flat ℤ A] (hG : TypeFPInfinity G)
    (hQ : HasFiniteIntegralCohomologicalDimension (G ⧸ N))
    (hN : ∀ p : ℕ, Subsingleton (ShiftedCompletedCohomology p
      (Rep.ind N.subtype (Rep.res N.subtype A)))) (p : ℕ) :
    Subsingleton (ShiftedCompletedCohomology p A) := by
  let : Countable (G ⧸ N) := Function.Surjective.countable (QuotientGroup.mk'_surjective N)
  have hreg (r : ℕ) : Subsingleton (ShiftedCompletedCohomology r
      ((quotientTensorFunctor N A).obj (Rep.leftRegular ℤ (G ⧸ N)))) := by
    let e := (shiftedCompletedCohomologyFunctor r).mapIso (quotientTensorRegularIso N A)
    apply subsingleton_of_forall_eq 0
    intro x
    apply e.toLinearEquiv.injective
    exact (hN r).elim _ _
  have hfree (r : ℕ) : Subsingleton (ShiftedCompletedCohomology r
      ((quotientTensorFunctor N A).obj (Rep.free ℤ (G ⧸ N) ℕ))) := by
    have hs := hG.finsupp_completeCohomology _ r (hreg r)
    let e := (shiftedCompletedCohomologyFunctor r).mapIso (quotientTensorFreeNatIso N A)
    apply subsingleton_of_forall_eq 0
    intro x
    apply e.toLinearEquiv.injective
    exact hs.elim _ _
  obtain ⟨d, hd⟩ := hQ
  have hz := exactFunctor_complete_vanishing_of_countable_free
    (quotientTensorFunctor N A) hfree (trivialIntegral (G ⧸ N)) d hd p
  let e : (quotientTensorFunctor N A).obj (trivialIntegral (G ⧸ N)) ≅ A := ρ_ A
  let ce := (shiftedCompletedCohomologyFunctor p).mapIso e
  apply subsingleton_of_forall_eq 0
  intro x
  apply ce.symm.toLinearEquiv.injective
  exact hz.elim _ _

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_SmallCoefficientTensorAlgebra
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.quotientTensorFunctor_preservesEpimorphisms _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesHomology _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Unit and multiplication on the small coefficient tensor functor -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped TensorProduct
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2300] TensorProduct.instModule
variable {G : Type} [Group G]

set_option synthInstance.maxHeartbeats 400000 in
theorem smallCoefficientTensorUnit_natural {A B : Rep.{0} ℤ G} (f : A ⟶ B) :
    f ≫ smallCoefficientTensorUnit B =
      smallCoefficientTensorUnit A ≫ (tensorLeft (smallCoefficientRepresentation G)).map f := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  rfl

set_option synthInstance.maxHeartbeats 400000 in
theorem smallCoefficientTensorMultiply_map_unit (A : Rep.{0} ℤ G) :
    (tensorLeft (smallCoefficientRepresentation G)).map (smallCoefficientTensorUnit A) ≫
      smallCoefficientTensorMultiply A = 𝟙 _ := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply TensorProduct.ext'
  intro b x
  change (b * 1) ⊗ₜ[ℤ] x = b ⊗ₜ[ℤ] x
  rw [mul_one]

set_option synthInstance.maxHeartbeats 400000 in
/-- Extend a primitive using ring multiplication and cancel its epimorphic cover. -/
theorem smallCoefficientTensor_split_of_unit_homotopy {P Q K : Rep.{0} ℤ G}
    (π : Q ⟶ K) [Epi π] (ι : K ⟶ P) (r : P ⟶ smallCoefficientTensor K)
    (hr : (π ≫ ι) ≫ r = π ≫ smallCoefficientTensorUnit K) :
    (tensorLeft (smallCoefficientRepresentation G)).map ι ≫
      ((tensorLeft (smallCoefficientRepresentation G)).map r ≫
        smallCoefficientTensorMultiply K) = 𝟙 _ := by
  let F := tensorLeft (smallCoefficientRepresentation G)
  apply (cancel_epi (F.map π)).mp
  have h := congrArg (fun f => F.map f ≫ smallCoefficientTensorMultiply K) hr
  dsimp only [F] at h ⊢
  simpa only [CategoryTheory.Functor.map_comp, Category.assoc,
    smallCoefficientTensorMultiply_map_unit, Category.comp_id] using h

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_SmallCoefficientIdentityCycle
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.cyclicTopHomologyInjection_mono _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalizedFreeRepresentation_countable _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesHomology _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalizedSyzygyIterationIso_succ _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The unit identity cocycles in the coefficient-ring tower

The ordinary integral resolution remains the source of the cochains. Their
coefficients are the same syzygies tensored with the small coefficient ring.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits HomologicalComplex MonoidalCategory
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2100] Linear.homModule
attribute [local instance 2300] TensorProduct.instModule
variable (G : Type) [Group G] [Countable G]

set_option synthInstance.maxHeartbeats 400000 in
theorem smallCoefficientIdentityCycle_projection (n : ℕ) :
    ((normalizedResolutionComplex (trivialIntegral G)).linearYonedaObj ℤ
      ((smallCoefficientTower G).obj n)).iCycles n (smallCoefficientIdentityCycle G n) =
        smallCoefficientIdentityCochain G n := by
  exact ((normalizedResolutionComplex (trivialIntegral G)).linearYonedaObj ℤ
    ((smallCoefficientTower G).obj n)).i_cyclesMk (smallCoefficientIdentityCochain G n)
      (n + 1) (by simp) (smallCoefficientIdentityCochain_closed G n)

set_option synthInstance.maxHeartbeats 400000 in
theorem smallCoefficientIdentityClass_connecting (n : ℕ) :
    (resolutionCoefficientSequence_shortExact (normalizedProjectiveResolution (trivialIntegral G))
      ((smallCoefficientTower G).sequence n) ((smallCoefficientTower G).shortExact n)).δ
        n (n + 1) rfl (smallCoefficientIdentityClass G n) =
      smallCoefficientIdentityClass G (n + 1) := by
  let P := normalizedProjectiveResolution (trivialIntegral G)
  let T := smallCoefficientTower G
  let S := T.sequence n
  let hS := resolutionCoefficientSequence_shortExact P S (T.shortExact n)
  let u := smallCoefficientTensorUnit (normalizedResolutionTerm (trivialIntegral G) n)
  have hz : ((forget₂ (ModuleCat ℤ) Ab).map
      ((resolutionCoefficientSequence P S).X₃.d n (n + 1)))
        (smallCoefficientIdentityCochain G n) = 0 :=
    smallCoefficientIdentityCochain_closed G n
  have hl : ((forget₂ (ModuleCat ℤ) Ab).map
      ((resolutionCoefficientSequence P S).g.f n)) u = smallCoefficientIdentityCochain G n := by
    change u ≫ T.π n = _
    exact (smallCoefficientTensorUnit_natural
      (normalizedFreeAugmentation ((iteratedNormalizedSyzygy n).obj (trivialIntegral G)))).symm
  have hd : ((forget₂ (ModuleCat ℤ) Ab).map
      ((resolutionCoefficientSequence P S).f.f (n + 1)))
        (smallCoefficientIdentityCochain G (n + 1)) =
      ((forget₂ (ModuleCat ℤ) Ab).map
        ((resolutionCoefficientSequence P S).X₂.d n (n + 1))) u := by
    change smallCoefficientIdentityCochain G (n + 1) ≫ T.ι n =
      (normalizedResolutionComplex (trivialIntegral G)).d (n + 1) n ≫ u
    unfold smallCoefficientIdentityCochain
    change (normalizedResolutionProjection (trivialIntegral G) (n + 1) ≫ _) ≫
      (tensorLeft (smallCoefficientRepresentation G)).map
        (kernel.ι (normalizedFreeAugmentation
          ((iteratedNormalizedSyzygy n).obj (trivialIntegral G)))) = _
    erw [Category.assoc, ← smallCoefficientTensorUnit_natural, ← Category.assoc,
      normalizedResolutionComplex_d]
    rfl
  exact hS.δ_apply n (n + 1) rfl (smallCoefficientIdentityCochain G n) hz
    u hl (smallCoefficientIdentityCochain G (n + 1)) hd (n + 2) (by simp)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_SmallCoefficientIdentityDimension
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.cyclicTopHomologyInjection_mono _root_.OAI.PolycyclicRecognition.horseshoeCover_projective _root_.OAI.PolycyclicRecognition.integralRepresentationSum_projective _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalizedFreeRepresentation_countable _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesHomology _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A vanishing unit cocycle splits the coefficient-ring syzygy

Multiplication in the coefficient ring extends an integral cochain to a
coefficient-linear cochain. Applied to a primitive of the identity cocycle,
this splits the next kernel and gives finite projective dimension.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits HomologicalComplex MonoidalCategory
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2100] Linear.homModule
attribute [local instance 2300] TensorProduct.instModule
variable (G : Type) [Group G] [Countable G]

set_option synthInstance.maxHeartbeats 400000 in
theorem smallCoefficientIdentityClass_zero_projective (n : ℕ)
    (h : smallCoefficientIdentityClass G (n + 1) = 0) :
    Projective ((smallCoefficientTower G).obj (n + 1)) := by
  let C := (normalizedResolutionComplex (trivialIntegral G)).linearYonedaObj ℤ
    ((smallCoefficientTower G).obj (n + 1))
  obtain ⟨r, hr⟩ := cochain_boundary_of_class_zero C n
    (smallCoefficientIdentityCycle G (n + 1)) h
  rw [smallCoefficientIdentityCycle_projection] at hr
  change (normalizedResolutionComplex (trivialIntegral G)).d (n + 1) n ≫ r =
    smallCoefficientIdentityCochain G (n + 1) at hr
  let F := tensorLeft (smallCoefficientRepresentation G)
  let T := smallCoefficientTower G
  let A := (iteratedNormalizedSyzygy (n + 1)).obj (trivialIntegral G)
  let π := normalizedResolutionProjection (trivialIntegral G) (n + 1)
  let ι := kernel.ι (normalizedFreeAugmentation
    ((iteratedNormalizedSyzygy n).obj (trivialIntegral G)))
  let s : T.projectiveObj n ⟶ T.obj (n + 1) := F.map r ≫ smallCoefficientTensorMultiply A
  have hprimitive : (π ≫ ι) ≫ r = π ≫ smallCoefficientTensorUnit A := by
    rw [normalizedResolutionComplex_d] at hr
    exact hr
  let : Epi π := inferInstanceAs (Epi (normalizedFreeAugmentation A))
  have hsplit : T.ι n ≫ s = 𝟙 _ :=
    smallCoefficientTensor_split_of_unit_homotopy π ι r hprimitive
  exact (show Retract (T.obj (n + 1)) (T.projectiveObj n) from
    ⟨T.ι n, s, hsplit⟩).projective

set_option synthInstance.maxHeartbeats 400000 in
theorem smallCoefficient_finite_dimension_of_identityClass_zero (n : ℕ)
    (h : smallCoefficientIdentityClass G (n + 1) = 0) :
    HasProjectiveDimensionLE (smallCoefficientRepresentation G) (n + 1) := by
  let := smallCoefficientIdentityClass_zero_projective G n h
  have hd := (smallCoefficientTower G).dimension_of_projective_tail (n + 1)
  let := hd
  exact hasProjectiveDimensionLT_of_iso
    (tensorNormalizedTowerBaseIso (smallCoefficientRepresentation G)) (n + 2)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_SmallCoefficientCompletedUnit
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.cyclicTopHomologyInjection_mono _root_.OAI.PolycyclicRecognition.moduleTailMap_directed _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesHomology _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Complete vanishing detects the dimension of the coefficient ring

The unit cocycles are carried by the connecting maps in the tensor tower.
If their completed class vanishes, an actual positive-degree identity class
vanishes and the previous splitting theorem applies.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2300] Module.DirectLimit.module
variable (G : Type) [Group G] [Countable G]

set_option synthInstance.maxHeartbeats 400000 in
theorem smallCoefficientGroupIdentity_comparison (n : ℕ) :
    (coefficientNaturalCohomologyIso (normalizedProjectiveResolution (trivialIntegral G))
      ((smallCoefficientTower G).obj n) n).hom (smallCoefficientGroupIdentity G n) =
      smallCoefficientIdentityClass G n :=
  ConcreteCategory.congr_hom
    (coefficientNaturalCohomologyIso (normalizedProjectiveResolution (trivialIntegral G))
      ((smallCoefficientTower G).obj n) n).inv_hom_id (smallCoefficientIdentityClass G n)

set_option synthInstance.maxHeartbeats 400000 in
theorem smallCoefficientGroupIdentity_connecting (n : ℕ) :
    ((smallCoefficientTower G).connecting 0 n).hom (smallCoefficientGroupIdentity G n) =
      smallCoefficientGroupIdentity G (n + 1) := by
  let T := smallCoefficientTower G
  let P := normalizedProjectiveResolution (trivialIntegral G)
  let e := coefficientNaturalCohomologyIso P (T.obj (n + 1)) (n + 1)
  apply (ModuleCat.mono_iff_injective e.hom).mp inferInstance
  have he := ConcreteCategory.congr_hom
    (coefficientNaturalCohomologyIso_connecting P (T.sequence n) (T.shortExact n) n)
      (smallCoefficientGroupIdentity G n)
  change e.hom (((smallCoefficientTower G).connecting 0 n).hom
    (smallCoefficientGroupIdentity G n)) =
      (resolutionCoefficientSequence_shortExact P (T.sequence n) (T.shortExact n)).δ
        n (n + 1) rfl
        ((coefficientNaturalCohomologyIso P (T.obj n) n).hom
          (smallCoefficientGroupIdentity G n)) at he
  rw [smallCoefficientGroupIdentity_comparison] at he
  exact he.trans (smallCoefficientIdentityClass_connecting G n) |>.trans
    (smallCoefficientGroupIdentity_comparison G (n + 1)).symm

set_option synthInstance.maxHeartbeats 400000 in
theorem smallCoefficientGroupIdentity_forward (i j : ℕ) (h : i ≤ j) :
    (smallCoefficientTower G).forward 0 i j h (smallCoefficientGroupIdentity G i) =
      smallCoefficientGroupIdentity G j := by
  induction h with
  | refl => exact Nat.leRecOn_self _
  | @step j h ih =>
    change Nat.leRecOn (C := (smallCoefficientTower G).cohomologyStage 0) _
      (fun {k} => ((smallCoefficientTower G).connecting 0 k).hom)
        (smallCoefficientGroupIdentity G i) = _
    rw [Nat.leRecOn_succ h]
    change ((smallCoefficientTower G).connecting 0 j).hom
      ((smallCoefficientTower G).forward 0 i j h (smallCoefficientGroupIdentity G i)) = _
    rw [ih, smallCoefficientGroupIdentity_connecting]

set_option synthInstance.maxHeartbeats 400000 in
theorem smallCoefficient_finite_dimension_of_completedUnit_zero
    (h : smallCoefficientCompletedUnit G = 0) :
    ∃ n : ℕ, HasProjectiveDimensionLE (smallCoefficientRepresentation G) n := by
  obtain ⟨j, _, hj⟩ := Module.DirectLimit.of.zero_exact h
  rw [smallCoefficientGroupIdentity_forward] at hj
  have hs : smallCoefficientGroupIdentity G (j + 1) = 0 := by
    rw [← smallCoefficientGroupIdentity_connecting, hj, map_zero]
  have hc : smallCoefficientIdentityClass G (j + 1) = 0 := by
    rw [← smallCoefficientGroupIdentity_comparison, hs, map_zero]
    rfl
  exact ⟨j + 1, smallCoefficient_finite_dimension_of_identityClass_zero G j hc⟩

set_option synthInstance.maxHeartbeats 400000 in
theorem smallCoefficient_finite_dimension_of_complete_vanishing
    (h : Subsingleton (ShiftedCompletedCohomology 0 (smallCoefficientRepresentation G))) :
    ∃ n : ℕ, HasProjectiveDimensionLE (smallCoefficientRepresentation G) n := by
  apply smallCoefficient_finite_dimension_of_completedUnit_zero G
  let e := tensorNormalizedTowerCompletion (smallCoefficientRepresentation G) 0
  apply e.injective
  exact h.elim _ _

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_HeightKernelCoefficientDimension
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite dimension of the coefficient ring for the height-kernel extension

The kernel may contain torsion and its finitely generated subgroups may have
unbounded ranks. The quotient alone is assumed to have finite integral dimension.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G] [Countable G]

set_option synthInstance.maxHeartbeats 400000 in
theorem TypeFPInfinity.heightKernel_smallCoefficient_vanishing
    (hG : TypeFPInfinity G) (N : Subgroup G) [N.Normal]
    (hQ : HasFiniteIntegralCohomologicalDimension (G ⧸ N))
    (hN : ∀ J : Subgroup G, J ≤ N → J.FG → Group.IsVirtuallyNilpotent J)
    (p : ℕ) :
    Subsingleton (ShiftedCompletedCohomology p (smallCoefficientRepresentation G)) := by
  exact hG.normalQuotient_complete_vanishing N (smallCoefficientRepresentation G) hQ
    (fun r => hG.locallyVirtuallyNilpotent_smallCoefficient_induction_vanishing N r hN) p

set_option synthInstance.maxHeartbeats 400000 in
theorem TypeFPInfinity.heightKernel_smallCoefficient_finite_dimension
    (hG : TypeFPInfinity G) (N : Subgroup G) [N.Normal]
    (hQ : HasFiniteIntegralCohomologicalDimension (G ⧸ N))
    (hN : ∀ J : Subgroup G, J ≤ N → J.FG → Group.IsVirtuallyNilpotent J) :
    ∃ d : ℕ, HasProjectiveDimensionLE (smallCoefficientRepresentation G) d :=
  smallCoefficient_finite_dimension_of_complete_vanishing G
    (hG.heightKernel_smallCoefficient_vanishing N hQ hN 0)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_HeightKernelTorsionBound
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bounded finite subgroup orders for the height-kernel extension

The coefficient-ring dimension theorem and the actual invariant mean give
finite integral projective dimension of the rational coefficient. FP-infinity
then detects a nonzero factorial annihilator of the complete integral identity.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory ThompsonNonamenability
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G] [Countable G]

theorem TypeFPInfinity.heightKernel_rationalCoefficient_finite_dimension
    (hG : TypeFPInfinity G) (M : InvariantMean G) (N : Subgroup G) [N.Normal]
    (hQ : HasFiniteIntegralCohomologicalDimension (G ⧸ N))
    (hN : ∀ J : Subgroup G, J ≤ N → J.FG → Group.IsVirtuallyNilpotent J) :
    ∃ d : ℕ, HasProjectiveDimensionLE (Rep.trivial ℤ G ℚ) d := by
  obtain ⟨d, hd⟩ := hG.heightKernel_smallCoefficient_finite_dimension N hQ hN
  exact ⟨d + 1, rationalCoefficient_dimension_of_smallCoefficient M d hd⟩

theorem TypeFPInfinity.heightKernel_boundedFiniteSubgroupOrders
    (hG : TypeFPInfinity G) (M : InvariantMean G) (N : Subgroup G) [N.Normal]
    (hQ : HasFiniteIntegralCohomologicalDimension (G ⧸ N))
    (hN : ∀ J : Subgroup G, J ≤ N → J.FG → Group.IsVirtuallyNilpotent J) :
    HasBoundedFiniteSubgroupOrders G := by
  obtain ⟨d, hd⟩ := hG.heightKernel_rationalCoefficient_finite_dimension M N hQ hN
  let := hd
  exact hG.boundedFiniteSubgroupOrders_of_rational_projectiveDimension G d

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_RationalCoefficientDimensionBound
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Rational homology bounds from the actual rational-coefficient resolution -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits ThompsonNonamenability
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G]

theorem rationalHomologyDimension_of_rational_representation (d : ℕ)
    (hd : HasProjectiveDimensionLE (Rep.trivial ℚ G ℚ) d) :
    RationalHomologyDimensionLE G d := by
  let := hd
  intro A i hi
  exact (RationalResolution.groupHomology_isZero_above_dimension d
    (rationalizeRepresentation A) i hi).of_iso (rationalizeGroupHomologyIso A i).symm

theorem rationalHomologyDimension_of_rational_coefficient (d : ℕ)
    (hd : HasProjectiveDimensionLE (Rep.trivial ℤ G ℚ) d) :
    RationalHomologyDimensionLE G d :=
  rationalHomologyDimension_of_rational_representation d
    (rationalGroup_dimension_le_of_integral_rational d hd)

theorem TypeFPInfinity.heightKernel_rationalHomologyDimension [Countable G]
    (hG : TypeFPInfinity G) (M : InvariantMean G) (N : Subgroup G) [N.Normal]
    (hQ : HasFiniteIntegralCohomologicalDimension (G ⧸ N))
    (hN : ∀ J : Subgroup G, J ≤ N → J.FG → Group.IsVirtuallyNilpotent J) :
    ∃ d : ℕ, RationalHomologyDimensionLE G d := by
  obtain ⟨d, hd⟩ := hG.heightKernel_rationalCoefficient_finite_dimension M N hQ hN
  exact ⟨d, rationalHomologyDimension_of_rational_coefficient d hd⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_RationalLocallyNilpotentDimension
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.cyclicTopHomologyInjection_mono _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integral dimension from a rational bound for locally nilpotent groups

A finitely generated torsion-free nilpotent subgroup is an integral duality
group. Its orientation class detects its dimension over the rationals.
The countable exhaustion therefore has uniformly bounded integral dimension.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
variable {G : Type} [Group G]

theorem RationalHomologyDimensionLE.nilpotent_subgroup_dimension {d : ℕ}
    (hd : RationalHomologyDimensionLE G d) (H : Subgroup G) (hH : H.FG)
    [Group.IsNilpotent H] (htf : HasNoNontrivialTorsion H) :
    HasProjectiveDimensionLE (trivialIntegral H) d := by
  let : Group.FG H := (Group.fg_iff_subgroup_fg H).mpr hH
  obtain ⟨n, hn⟩ := nilpotent_poincareDuality_of_finitelyGenerated_torsionFree htf
  let := hn.cohomologicalDimension
  exact hasProjectiveDimensionLT_of_ge (trivialIntegral H) (n + 1) (d + 1)
    (Nat.add_le_add_right (hn.dimension_le_of_rational_homology_bound (hd.subgroup H)) 1)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_UltrafilterSubgroup
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesHomology _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Subgroup limits preserve a fixed derived-series bound -/
noncomputable section
namespace PolycyclicRecognition
open Filter
variable {G I : Type} [Group G]

theorem ultrafilterSubgroup_fg_le_eventually (U : Ultrafilter I) (K : I → Subgroup G)
    (H : Subgroup G) (hH : H.FG) (hHK : H ≤ ultrafilterSubgroup U K) :
    ∀ᶠ i in U, H ≤ K i := by
  obtain ⟨S, hS, hSf⟩ := (Subgroup.fg_iff H).mp hH
  have hs : ∀ᶠ i in U, ∀ s ∈ S, s ∈ K i :=
    hSf.eventually_all.mpr (fun s hs => hHK (hS ▸ Subgroup.subset_closure hs))
  filter_upwards [hs] with i hi
  rw [← hS]
  exact (Subgroup.closure_le (K i)).mpr hi

theorem ultrafilterSubgroup_derivedSeries (U : Ultrafilter I) (K : I → Subgroup G)
    (r : ℕ) (hr : ∀ i, derivedSeries (K i) r = ⊥) :
    derivedSeries (ultrafilterSubgroup U K) r = ⊥ := by
  apply derivedSeries_eq_bot_of_fg_subgroups
  intro H hH
  let L := ultrafilterSubgroup U K
  let J := H.map L.subtype
  have hJ : J.FG := fg_subgroup_map hH L.subtype
  have hJL : J ≤ L := by rintro _ ⟨x, _, rfl⟩; exact x.property
  obtain ⟨i, hi⟩ := (ultrafilterSubgroup_fg_le_eventually U K J hJ hJL).exists
  let f : H →* K i := (L.subtype.comp H.subtype).codRestrict (K i)
    (fun x => hi ⟨x, x.property, rfl⟩)
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun x : K i => (x : G)) hab
  have hm := map_derivedSeries_le_derivedSeries f r
  rw [hr i] at hm
  have he : (derivedSeries H r).map f = ⊥ := eq_bot_iff.mpr hm
  rw [Subgroup.map_eq_bot_iff, f.ker_eq_bot hf] at he
  exact eq_bot_iff.mpr he

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_UniformCosetBound
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesHomology _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A finite tuple criterion for bounded subgroup index -/
noncomputable section
namespace PolycyclicRecognition
variable {G : Type} [Group G]

theorem finiteIndex_of_cosetCollisionBound (H : Subgroup G) (b : ℕ)
    (h : CosetCollisionBound H b) : H.FiniteIndex ∧ H.index ≤ b := by
  classical
  have hn : ¬ Nonempty (Fin (b + 1) ↪ (G ⧸ H)) := by
    rintro ⟨e⟩
    obtain ⟨i, j, hij, hm⟩ := h (fun i => Quotient.out (e i))
    apply hij
    apply e.injective
    have he : (Quotient.mk'' (Quotient.out (e i)) : G ⧸ H) =
        Quotient.mk'' (Quotient.out (e j)) :=
      Quotient.sound (QuotientGroup.leftRel_apply.mpr hm)
    simpa only [Quotient.out_eq'] using he
  have hfin : Finite (G ⧸ H) := by
    by_contra hf
    let : Infinite (G ⧸ H) := not_finite_iff_infinite.mp hf
    apply hn
    exact ⟨⟨fun i => Infinite.natEmbedding (G ⧸ H) i.val,
      (Infinite.natEmbedding (G ⧸ H)).injective.comp Fin.val_injective⟩⟩
  let := hfin
  let : Fintype (G ⧸ H) := Fintype.ofFinite _
  refine ⟨Subgroup.finiteIndex_of_finite_quotient, ?_⟩
  by_contra hb
  apply hn
  apply Function.Embedding.nonempty_of_card_le
  simpa only [Fintype.card_fin, ← Nat.card_eq_fintype_card, H.index_eq_card, Nat.card_fin] using
    Nat.succ_le_of_lt (lt_of_not_ge hb)

theorem cosetCollisionBound_of_index (H : Subgroup G) [H.FiniteIndex]
    (b : ℕ) (hb : H.index ≤ b) : CosetCollisionBound H b := by
  classical
  let : Fintype (G ⧸ H) := Fintype.ofFinite _
  intro f
  by_contra h
  have hf : Function.Injective (fun i => (Quotient.mk'' (f i) : G ⧸ H)) := by
    intro i j hij
    by_contra hne
    exact h ⟨i, j, hne, QuotientGroup.leftRel_apply.mp (Quotient.exact hij)⟩
  have hc := Fintype.card_le_of_injective _ hf
  have hb' : Fintype.card (G ⧸ H) ≤ b := by
    simpa only [← Nat.card_eq_fintype_card, ← H.index_eq_card] using hb
  simp only [Fintype.card_fin] at hc
  change b + 1 ≤ Fintype.card (G ⧸ H) at hc
  omega

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_UltrafilterIndexBound
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesHomology _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A uniform local coset bound survives an ultrafilter limit -/
noncomputable section
namespace PolycyclicRecognition
open Filter
variable {G I : Type} [Group G]

theorem ultrafilterSubgroup_index (U : Ultrafilter I) (K : I → Subgroup G)
    (b : ℕ) (h : ∀ f : Fin (b + 1) → G,
      ∀ᶠ k in U, ∃ i j, i ≠ j ∧ (f i)⁻¹ * f j ∈ K k) :
    (ultrafilterSubgroup U K).FiniteIndex ∧ (ultrafilterSubgroup U K).index ≤ b := by
  apply finiteIndex_of_cosetCollisionBound
  intro f
  have he : ∀ᶠ k in U, ∃ p : Fin (b + 1) × Fin (b + 1),
      p.1 ≠ p.2 ∧ (f p.1)⁻¹ * f p.2 ∈ K k := by
    filter_upwards [h f] with k hk
    obtain ⟨i, j, hij, hm⟩ := hk
    exact ⟨(i, j), hij, hm⟩
  obtain ⟨p, hp⟩ := Ultrafilter.eventually_exists_iff.mp he
  have hne := hp.exists.choose_spec.1
  exact ⟨p.1, p.2, hne, hp.mono (fun _ h => h.2)⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_UniformLocalVirtualSolvability
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instNonemptyBases _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesHomology _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform local solvability and index bounds give global virtual solvability

The ultrafilter is only a compactness device. The finite-index and derived
length bounds remain explicit hypotheses of this supporting implication.
-/
noncomputable section
namespace PolycyclicRecognition
open Filter
variable {G : Type} [Group G]

theorem uniformLocalVirtualSolvability (b r : ℕ)
    (hlocal : ∀ H : Subgroup G, H.FG → ∃ K : Subgroup H,
      K.FiniteIndex ∧ K.index ≤ b ∧ derivedSeries K r = ⊥) :
    ∃ K : Subgroup G, K.FiniteIndex ∧ K.index ≤ b ∧ derivedSeries K r = ⊥ := by
  classical
  let H (S : Finset G) := Subgroup.closure (S : Set G)
  have hH (S : Finset G) : (H S).FG :=
    (Subgroup.fg_iff _).mpr ⟨S, rfl, S.finite_toSet⟩
  choose K hKi hKb hKr using (fun S => hlocal (H S) (hH S))
  let L (S : Finset G) := (K S).map (H S).subtype
  let U := Ultrafilter.of (atTop : Filter (Finset G))
  have hLr (S : Finset G) : derivedSeries (L S) r = ⊥ := by
    let e := (K S).equivMapOfInjective (H S).subtype Subtype.val_injective
    rw [← map_derivedSeries_eq (f := e.toMonoidHom) e.surjective r, hKr S, Subgroup.map_bot]
  obtain ⟨hI, hb⟩ := ultrafilterSubgroup_index U L b (fun f => by
    have hev : ∀ᶠ S : Finset G in U, Finset.univ.image f ⊆ S :=
      Ultrafilter.of_le (atTop : Filter (Finset G)) (eventually_finset_atTop_subset _)
    filter_upwards [hev] with S hS
    let fH : Fin (b + 1) → H S := fun i =>
      ⟨f i, Subgroup.subset_closure (hS (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩))⟩
    let := hKi S
    obtain ⟨i, j, hij, hm⟩ := cosetCollisionBound_of_index (K S) b (hKb S) fH
    exact ⟨i, j, hij, ⟨(fH i)⁻¹ * fH j, hm, rfl⟩⟩)
  exact ⟨ultrafilterSubgroup U L, hI, hb, ultrafilterSubgroup_derivedSeries U L r hLr⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_VirtualNilpotentNormalCore
attribute [-instance] _root_.GeneratesNS.rho_g_FG _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesHomology _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A torsion-free nilpotent normal core -/
noncomputable section
namespace PolycyclicRecognition
variable {G : Type} [Group G] [Group.FG G]

theorem exists_normal_torsionFree_nilpotent_finiteIndex
    (hG : Group.IsVirtuallyNilpotent G) :
    ∃ F : Subgroup G, F.Normal ∧ F.FiniteIndex ∧ Group.IsNilpotent F ∧ HasNoNontrivialTorsion F := by
  obtain ⟨N, hN, hNi⟩ := hG
  let := hN
  let := hNi
  obtain ⟨U, hUi, hU⟩ :=
    (isPolycyclic_of_finitelyGenerated_nilpotent N).exists_torsionFree_finiteIndex
  let := hUi
  let P := U.map N.subtype
  let e := U.equivMapOfInjective N.subtype Subtype.val_injective
  let : P.FiniteIndex := ⟨by
    change (U.map N.subtype).index ≠ 0
    rw [Subgroup.index_map_subtype]
    exact mul_ne_zero hUi.index_ne_zero hNi.index_ne_zero⟩
  let f : P.normalCore →* U := e.symm.toMonoidHom.comp (Subgroup.inclusion P.normalCore_le)
  have hf : Function.Injective f := e.symm.injective.comp (Subgroup.inclusion_injective _)
  have hnil : Group.IsNilpotent P.normalCore :=
    Subgroup.isNilpotent_of_ker_le_center f (by rw [f.ker_eq_bot hf]; exact bot_le)
  exact ⟨P.normalCore, inferInstance, inferInstance, hnil, hU.of_injective f hf⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_LocalVirtualSolvabilityBound
attribute [-instance] _root_.GeneratesNS.rho_g_FG _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.cyclicTopHomologyInjection_mono _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform virtual solvability in locally virtually nilpotent groups -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
variable {G : Type} [Group G]

theorem virtuallyNilpotent_bounded_solvable_subgroup [Group.FG G]
    (b d : ℕ) (hd : RationalHomologyDimensionLE G d)
    (hb : ∀ N : Subgroup G, Finite N → Nat.card N ≤ b)
    (hG : Group.IsVirtuallyNilpotent G) :
    ∃ H : Subgroup G, H.FiniteIndex ∧ H.index ≤ virtualSolvabilityIndexBound b d ∧
      derivedSeries H (2 * d + 2) = ⊥ := by
  obtain ⟨F, hFn, hFi, hF, hFt⟩ := exists_normal_torsionFree_nilpotent_finiteIndex hG
  let := hFn
  let := hFi
  let := hF
  have hFg : F.FG := (Group.fg_iff_subgroup_fg F).mp inferInstance
  let : HasProjectiveDimensionLE (trivialIntegral F) d := hd.nilpotent_subgroup_dimension F hFg hFt
  obtain ⟨H, hHi, hHb, hHr⟩ := bounded_solvable_subgroup_of_nilpotent_finiteIndex F hFt b d hb
  have hc : Group.nilpotencyClass F ≤ 2 * d := nilpotencyClass_le_twice_cohomologicalDimension d
  refine ⟨H, hHi, ?_, ?_⟩
  · apply hHb.trans
    apply Nat.mul_le_mul_right
    apply Nat.pow_le_pow_right (by omega)
    exact Nat.mul_self_le_mul_self (Nat.mul_le_mul_right d hc)
  · apply eq_bot_iff.mpr
    exact (derivedSeries_antitone H (Nat.add_le_add_right hc 2)).trans_eq hHr

theorem locallyVirtuallyNilpotent_bounded_solvable_subgroup
    (b d : ℕ) (hd : RationalHomologyDimensionLE G d)
    (hb : ∀ N : Subgroup G, Finite N → Nat.card N ≤ b)
    (hlocal : ∀ H : Subgroup G, H.FG → Group.IsVirtuallyNilpotent H) :
    ∃ H : Subgroup G, H.FiniteIndex ∧ H.index ≤ virtualSolvabilityIndexBound b d ∧
      derivedSeries H (2 * d + 2) = ⊥ := by
  apply uniformLocalVirtualSolvability
  intro H hH
  let : Group.FG H := (Group.fg_iff_subgroup_fg H).mpr hH
  apply virtuallyNilpotent_bounded_solvable_subgroup b d (hd.subgroup H) _ (hlocal H hH)
  intro N hN
  let := hN
  let e := N.equivMapOfInjective H.subtype Subtype.val_injective
  let : Finite (N.map H.subtype) := Finite.of_equiv N e.toEquiv
  simpa only [Nat.card_congr e.toEquiv] using hb (N.map H.subtype) inferInstance

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_LocalSolvableRadical
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A characteristic soluble subgroup for the locally virtually nilpotent kernel -/
noncomputable section
namespace PolycyclicRecognition
variable {G : Type} [Group G]

theorem virtuallyNilpotent_of_mulEquiv {J : Type} [Group J] (e : G ≃* J)
    (hG : Group.IsVirtuallyNilpotent G) : Group.IsVirtuallyNilpotent J := by
  obtain ⟨N, hN, hNi⟩ := hG
  let := hN
  let := hNi
  let f := N.equivMapOfInjective e.toMonoidHom e.injective
  exact ⟨N.map e.toMonoidHom, Group.nilpotent_of_mulEquiv f,
    Subgroup.FiniteIndex.map_of_surjective N e.surjective⟩

theorem locallyVirtuallyNilpotent_subgroup
    (hlocal : ∀ H : Subgroup G, H.FG → Group.IsVirtuallyNilpotent H) (S : Subgroup G) :
    ∀ H : Subgroup S, H.FG → Group.IsVirtuallyNilpotent H := by
  intro H hH
  exact virtuallyNilpotent_of_mulEquiv
    (H.equivMapOfInjective S.subtype Subtype.val_injective).symm
    (hlocal (H.map S.subtype) (fg_subgroup_map hH S.subtype))

theorem finiteSubgroupOrders_le_subgroup (b : ℕ)
    (hb : ∀ N : Subgroup G, Finite N → Nat.card N ≤ b) (S : Subgroup G) :
    ∀ N : Subgroup S, Finite N → Nat.card N ≤ b := by
  intro N hN
  let := hN
  let e := N.equivMapOfInjective S.subtype Subtype.val_injective
  let : Finite (N.map S.subtype) := Finite.of_equiv N e.toEquiv
  simpa only [Nat.card_congr e.toEquiv] using hb (N.map S.subtype) inferInstance

theorem locallyVirtuallyNilpotent_solvable_derived_bound [Group.IsSolvable G]
    (b d : ℕ) (hd : RationalHomologyDimensionLE G d)
    (hb : ∀ N : Subgroup G, Finite N → Nat.card N ≤ b)
    (hlocal : ∀ H : Subgroup G, H.FG → Group.IsVirtuallyNilpotent H) :
    derivedSeries G ((virtualSolvabilityIndexBound b d).factorial + (2 * d + 2)) = ⊥ := by
  obtain ⟨H, hHi, hHb, hHr⟩ := locallyVirtuallyNilpotent_bounded_solvable_subgroup b d hd hb hlocal
  let := hHi
  exact solvable_derivedSeries_bound_of_finiteIndex H _ _ hHb hHr

theorem locallyVirtuallyNilpotent_characteristic_solvable
    (d : ℕ) (hd : RationalHomologyDimensionLE G d) (hb : HasBoundedFiniteSubgroupOrders G)
    (hlocal : ∀ H : Subgroup G, H.FG → Group.IsVirtuallyNilpotent H) :
    ∃ R : Subgroup G, R.Characteristic ∧ R.FiniteIndex ∧ Group.IsSolvable R := by
  obtain ⟨b, hb⟩ := hb
  let r := (virtualSolvabilityIndexBound b d).factorial + (2 * d + 2)
  obtain ⟨R, hRchar, hRs, hmax⟩ := exists_characteristic_solvable_radical_of_bound r (by
    intro S hS
    let := hS
    exact locallyVirtuallyNilpotent_solvable_derived_bound b d (hd.subgroup S)
      (finiteSubgroupOrders_le_subgroup b hb S) (locallyVirtuallyNilpotent_subgroup hlocal S))
  obtain ⟨H, hHi, _, hHr⟩ := locallyVirtuallyNilpotent_bounded_solvable_subgroup b d hd hb hlocal
  let := hHi
  let : Group.IsSolvable H := ⟨2 * d + 2, hHr⟩
  have hNs : Group.IsSolvable H.normalCore :=
    Group.isSolvable_of_isSolvable_injective
      (f := Subgroup.inclusion H.normalCore_le) (Subgroup.inclusion_injective _)
  let : R.FiniteIndex := Subgroup.finiteIndex_of_le (hmax H.normalCore inferInstance hNs)
  exact ⟨R, hRchar, inferInstance, hRs⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_SolvableSubgroupFiniteExtension
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesHomology _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A solvable normal subgroup with finite index in the height kernel -/
noncomputable section
namespace PolycyclicRecognition
variable {G : Type} [Group G]

theorem quotientImage_finite_of_relative_finiteIndex (S N : Subgroup G) [S.Normal]
    [(S.subgroupOf N).FiniteIndex] : Finite (N.map (QuotientGroup.mk' S)) := by
  let f := (QuotientGroup.mk' S).comp N.subtype
  have hk : f.ker = S.subgroupOf N := by
    ext n
    change (QuotientGroup.mk' S) (n : G) = 1 ↔ (n : G) ∈ S
    exact QuotientGroup.eq_one_iff (n : G)
  let : f.ker.FiniteIndex := hk.symm ▸ inferInstance
  have hr : f.range = N.map (QuotientGroup.mk' S) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [← hr]
  exact Nat.finite_of_card_ne_zero (by
    rw [← Subgroup.index_ker]
    exact Subgroup.FiniteIndex.index_ne_zero)

theorem virtuallySolvable_of_relative_finiteIndex_solvable
    (S N : Subgroup G) [S.Normal] [N.Normal] (hSN : S ≤ N)
    [Group.IsSolvable S] [(S.subgroupOf N).FiniteIndex] [Group.IsSolvable (G ⧸ N)] :
    ∃ H : Subgroup G, H.FiniteIndex ∧ Group.IsSolvable H := by
  let q := QuotientGroup.mk' S
  let M := N.map q
  let : Finite M := quotientImage_finite_of_relative_finiteIndex S N
  let e := QuotientGroup.quotientQuotientEquivQuotient S N hSN
  let : Group.IsSolvable ((G ⧸ S) ⧸ M) :=
    Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  let : Finite (QuotientGroup.mk' M).ker := by
    simpa only [QuotientGroup.ker_mk'] using (inferInstance : Finite M)
  obtain ⟨V, hVi, hVs⟩ := virtually_solvable_of_finite_kernel (QuotientGroup.mk' M)
  let := hVi
  let := hVs
  let H := V.comap q
  let p : H →* V := (q.comp H.subtype).codRestrict V (fun x => x.property)
  let j : p.ker →* S :=
    { toFun x := ⟨((x : H) : G), (QuotientGroup.eq_one_iff _).mp
        (congrArg (fun v : V => (v : G ⧸ S)) x.property)⟩
      map_one' := rfl
      map_mul' _ _ := rfl }
  have hj : Function.Injective j := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun s : S => (s : G)) hxy
  let : Group.IsSolvable p.ker := Group.isSolvable_of_isSolvable_injective (f := j) hj
  let : Group.IsSolvable H :=
    Group.isSolvable_of_ker_le_range p.ker.subtype p (by simp)
  exact ⟨H, inferInstance, inferInstance⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_HeightKernelVirtualSolvable
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.kernelAverage_one _root_.OAI.PolycyclicRecognition.meanCorrection_one _root_.OAI.PolycyclicRecognition.vectorMeanCorrection_one _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

namespace OAI

/-! # Virtual solvability for the full locally virtually nilpotent height kernel

The rational dimension and torsion bounds come from the actual FP-infinity
coefficient argument. A characteristic soluble subgroup permits passage
from the kernel to the ambient extension.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory ThompsonNonamenability
open scoped IsMulCommutative
variable {G : Type} [Group G] [Group.FG G]

theorem TypeFPInfinity.heightKernel_virtualSolvable_oai
    (hG : TypeFPInfinity G) (M : InvariantMean G) (N : Subgroup G) [N.Normal]
    [IsMulCommutative (G ⧸ N)]
    (hQ : HasFiniteIntegralCohomologicalDimension (G ⧸ N))
    (hN : ∀ J : Subgroup G, J ≤ N → J.FG → Group.IsVirtuallyNilpotent J) :
    ∃ H : Subgroup G, H.FiniteIndex ∧ Group.IsSolvable H := by
  let : Countable G := countable_of_group_fg G
  obtain ⟨d, hd⟩ := hG.heightKernel_rationalHomologyDimension M N hQ hN
  have hb := hG.heightKernel_boundedFiniteSubgroupOrders M N hQ hN
  have hlocal : ∀ J : Subgroup N, J.FG → Group.IsVirtuallyNilpotent J := by
    intro J hJ
    exact virtuallyNilpotent_of_mulEquiv
      (J.equivMapOfInjective N.subtype Subtype.val_injective).symm
      (hN (J.map N.subtype) (Subgroup.map_subtype_le J) (fg_subgroup_map hJ N.subtype))
  obtain ⟨R, hRc, hRi, hRs⟩ := locallyVirtuallyNilpotent_characteristic_solvable d
    (hd.subgroup N) (hb.subgroup N) hlocal
  let := hRc
  let := hRi
  let := hRs
  let S := R.map N.subtype
  let : S.Normal := by dsimp [S]; infer_instance
  let e := R.equivMapOfInjective N.subtype Subtype.val_injective
  let : Group.IsSolvable S :=
    Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective
  let : (S.subgroupOf N).FiniteIndex := by
    change (S.comap N.subtype).FiniteIndex
    dsimp only [S]
    rw [Subgroup.comap_map_eq_self_of_injective Subtype.val_injective]
    infer_instance
  exact virtuallySolvable_of_relative_finiteIndex_solvable S N (Subgroup.map_subtype_le R)

end PolycyclicRecognition

end

end OAI
end

theorem solution : type_of% @OAI.PolycyclicRecognition.TypeFPInfinity.heightKernel_virtualSolvable_oai := @OAI.PolycyclicRecognition.TypeFPInfinity.heightKernel_virtualSolvable_oai
