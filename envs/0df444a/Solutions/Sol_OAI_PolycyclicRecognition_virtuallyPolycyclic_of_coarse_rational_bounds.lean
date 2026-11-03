-- Prove2me | solution 1 for OAI.PolycyclicRecognition.virtuallyPolycyclic_of_coarse_rational_bounds
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-03T00:02:14.693714+00:00
-- url     : https://prove2.me/submissions/4a07d706-4404-490b-82c4-fa61a6ddd4b7

import Mathlib
import Definitions.Def_PolycyclicRecognition
import Definitions.Def_OAIQ093D017
import Theorems.Thm_OAI_PolycyclicRecognition_polycyclic_of_nilpotent_by_abelian_duality

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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_BoundedLocallyFiniteKernel
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
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

theorem finite_of_locallyFinite_bounded
    (hlocal : ∀ H : Subgroup G, H.FG → Finite H)
    (hbound : HasBoundedFiniteSubgroupOrders G) : Finite G := by
  classical
  obtain ⟨b, hb⟩ := hbound
  by_contra h
  let : Infinite G := not_finite_iff_infinite.mp h
  let f : Fin (b + 1) → G := fun i => Infinite.natEmbedding G i.val
  have hf : Function.Injective f := (Infinite.natEmbedding G).injective.comp Fin.val_injective
  let H := Subgroup.closure (Set.range f)
  have hH : H.FG := (Subgroup.fg_iff H).mpr ⟨Set.range f, rfl, Set.finite_range f⟩
  let : Finite H := hlocal H hH
  let fH : Fin (b + 1) → H := fun i => ⟨f i, Subgroup.subset_closure ⟨i, rfl⟩⟩
  have hfH : Function.Injective fH := fun a c hac => hf (congrArg Subtype.val hac)
  have hc := Nat.card_le_card_of_injective fH hfH
  have hh := hb H inferInstance
  simp only [Nat.card_fin] at hc
  omega

theorem finite_locallyFinite_normal_subgroup (N : Subgroup G)
    (hlocal : ∀ H : Subgroup N, H.FG → Finite H)
    (hbound : HasBoundedFiniteSubgroupOrders G) : Finite N :=
  finite_of_locallyFinite_bounded hlocal (hbound.subgroup N)

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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_TensorMultilinearGenerators
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Testing multilinear maps on scalar tensor generators -/

noncomputable section
namespace PolycyclicRecognition
open scoped TensorProduct
variable {K M V : Type} [Field K] [AddCommGroup M] [Module ℤ M]
  [AddCommGroup V] [Module K V]

theorem scalarTensorUnit_smul (r : K) (a : M) :
    r • scalarTensorUnit K M a = r ⊗ₜ[ℤ] a := by
  change r • ((1 : K) ⊗ₜ[ℤ] a) = _
  rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_CentralLayerTensor
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

namespace OAI

/-! # Tensor generators of a central commutator layer -/

noncomputable section
namespace PolycyclicRecognition
open scoped TensorProduct commutatorElement IsMulCommutative
variable {G : Type} [Group G] (N : Subgroup G)
variable (h : ⁅(⊤ : Subgroup G), N⁆ ≤ Subgroup.center G)
  (K : Subgroup N) [K.Normal] [IsMulCommutative (N ⧸ K)]
  (hK : K.map N.subtype ≤ Subgroup.center G)

include h hK in
theorem centralLayer_scalar_finite (k : Type) [Field k]
    [Module.Finite k (k ⊗[ℤ] Additive (Abelianization G))]
    [Module.Finite k (k ⊗[ℤ] Additive (N ⧸ K))] :
    Module.Finite k (k ⊗[ℤ] centralLayerSubmodule N) := by
  let e := TensorProduct.AlgebraTensorModule.distribBaseChange ℤ k
    (Additive (Abelianization G)) (Additive (N ⧸ K))
  let : Module.Finite k (k ⊗[ℤ] (Additive (Abelianization G) ⊗[ℤ] Additive (N ⧸ K))) :=
    Module.Finite.of_surjective e.symm.toLinearMap e.symm.surjective
  exact Module.Finite.of_surjective ((centralLayerTensorSurjection N h K hK).baseChange k)
    ((centralLayerTensorSurjection N h K hK).baseChange_surjective k
      (centralLayerTensor_surjective N h K hK))

include h hK in
theorem central_commutator_scalar_finite (k : Type) [Field k]
    [IsMulCommutative (⁅(⊤ : Subgroup G), N⁆ : Subgroup G)]
    [Module.Finite k (k ⊗[ℤ] Additive (Abelianization G))]
    [Module.Finite k (k ⊗[ℤ] Additive (N ⧸ K))] :
    Module.Finite k (k ⊗[ℤ] Additive (⁅(⊤ : Subgroup G), N⁆ : Subgroup G)) := by
  let := centralLayer_scalar_finite N h K hK k
  let e := (centralLayerAddEquiv N h).toIntLinearEquiv.baseChange ℤ k _ _
  exact Module.Finite.of_surjective e.toLinearMap e.surjective

end PolycyclicRecognition

end

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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_LocallyNilpotentDimension
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.cyclicTopHomologyInjection_mono _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite integral dimension makes local nilpotence uniform

Every element of a lower-central term is witnessed in a finitely generated
subgroup. The common class bound from cohomological dimension therefore makes
a locally nilpotent group nilpotent, including groups not finitely generated.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped commutatorElement

variable {G : Type} [Group G]

theorem lowerCentralSeries_le_fgLowerCentral (n : ℕ) :
    (⊤ : Subgroup G).lowerCentralSeries n ≤ fgLowerCentralSubgroup n := by
  induction n with
  | zero =>
    intro g _
    refine ⟨Subgroup.closure {g}, ?_, Subgroup.subset_closure (Set.mem_singleton g)⟩
    exact (Subgroup.fg_iff _).mpr ⟨{g}, rfl, Set.finite_singleton g⟩
  | succ n ih =>
    rw [Subgroup.lowerCentralSeries_succ]
    apply Subgroup.commutator_le.mpr
    intro x hx y _
    obtain ⟨H, hH, hxH⟩ := ih hx
    let K := H ⊔ Subgroup.closure {y}
    have hY : (Subgroup.closure {y}).FG :=
      (Subgroup.fg_iff _).mpr ⟨{y}, rfl, Set.finite_singleton y⟩
    refine ⟨K, hH.sup hY, ?_⟩
    rw [Subgroup.lowerCentralSeries_succ]
    exact Subgroup.commutator_mem_commutator
      (Subgroup.lowerCentralSeries_mono n le_sup_left hxH)
      ((show Subgroup.closure {y} ≤ K from le_sup_right)
        (Subgroup.subset_closure (Set.mem_singleton y)))

theorem lowerCentralSeries_eq_bot_of_fg_subgroups (n : ℕ)
    (h : ∀ H : Subgroup G, H.FG → H.lowerCentralSeries n = ⊥) :
    (⊤ : Subgroup G).lowerCentralSeries n = ⊥ := by
  apply eq_bot_iff.mpr
  intro g hg
  obtain ⟨H, hH, hgH⟩ := lowerCentralSeries_le_fgLowerCentral n hg
  simpa only [h H hH] using hgH

theorem locallyNilpotent_lowerCentralSeries_bound (d : ℕ)
    [CategoryTheory.HasProjectiveDimensionLE (trivialIntegral G) d]
    (hlocal : ∀ H : Subgroup G, Group.FG H → Group.IsNilpotent H) :
    (⊤ : Subgroup G).lowerCentralSeries (2 * d) = ⊥ := by
  apply lowerCentralSeries_eq_bot_of_fg_subgroups
  intro H hH
  have hfg : Group.FG H := (Group.fg_iff_subgroup_fg H).mpr hH
  let := hlocal H hfg
  exact Subgroup.lowerCentralSeries_eq_bot_of_nilpotencyClass_le
    (nilpotent_subgroup_class_le d H)

theorem HasFiniteIntegralCohomologicalDimension.nilpotent_of_locallyNilpotent
    (hG : HasFiniteIntegralCohomologicalDimension G)
    (hlocal : ∀ H : Subgroup G, Group.FG H → Group.IsNilpotent H) :
    Group.IsNilpotent G := by
  obtain ⟨d, hd⟩ := hG
  let := hd
  exact Subgroup.nilpotent_iff_lowerCentralSeries.mpr
    ⟨2 * d, locallyNilpotent_lowerCentralSeries_bound d hlocal⟩

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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_CompatiblePrimitives
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Compatible primitives along a countable tower

A primitive at the next stage can be corrected by a coboundary to agree
with the previous one. This is the algebraic step in the dimension bound
for a countable increasing union of subgroups.
-/

noncomputable section
namespace PolycyclicRecognition

theorem exists_compatible_primitives
    {X Y Z : ℕ → Type*}
    [∀ n, AddCommGroup (X n)] [∀ n, AddCommGroup (Y n)] [∀ n, AddCommGroup (Z n)]
    (d : ∀ n, X n →+ Y n) (e : ∀ n, Y n →+ Z n)
    (rX : ∀ n, X (n + 1) →+ X n) (rY : ∀ n, Y (n + 1) →+ Y n)
    (rZ : ∀ n, Z (n + 1) →+ Z n)
    (hd : ∀ n x, rY n (d (n + 1) x) = d n (rX n x))
    (he : ∀ n y, rZ n (e (n + 1) y) = e n (rY n y))
    (hzero : ∀ n x, e n (d n x) = 0)
    (hexact : ∀ n y, e n y = 0 → ∃ x, d n x = y)
    (hsurj : ∀ n, Function.Surjective (rX n))
    (z : ∀ n, Z n) (hz : ∀ n, rZ n (z (n + 1)) = z n)
    (hprim : ∀ n, ∃ y, e n y = z n) :
    ∃ y : ∀ n, Y n, (∀ n, e n (y n) = z n) ∧
      ∀ n, rY n (y (n + 1)) = y n := by
  have step (n : ℕ) (y : Y n) (hy : e n y = z n) :
      ∃ y' : Y (n + 1), e (n + 1) y' = z (n + 1) ∧ rY n y' = y := by
    obtain ⟨v, hv⟩ := hprim (n + 1)
    have hvy : e n (rY n v - y) = 0 := by
      rw [map_sub, ← he, hv, hz, hy, sub_self]
    obtain ⟨w, hw⟩ := hexact n _ hvy
    obtain ⟨w', hw'⟩ := hsurj n w
    refine ⟨v - d (n + 1) w', ?_, ?_⟩
    · rw [map_sub, hzero, sub_zero, hv]
    · rw [map_sub, hd, hw', hw, sub_sub_cancel]
  let start : {y : Y 0 // e 0 y = z 0} :=
    ⟨(hprim 0).choose, (hprim 0).choose_spec⟩
  let next (n : ℕ) (y : {y : Y n // e n y = z n}) :
      {y : Y (n + 1) // e (n + 1) y = z (n + 1)} :=
    ⟨(step n y y.property).choose, (step n y y.property).choose_spec.1⟩
  let ys : ∀ n, {y : Y n // e n y = z n} := Nat.rec start next
  refine ⟨fun n => (ys n).val, fun n => (ys n).property, ?_⟩
  intro n
  exact (step n (ys n).val (ys n).property).choose_spec.2

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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_ExhaustionFunctionGluing
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Gluing compatible functions on an increasing countable cover -/

noncomputable section
namespace PolycyclicRecognition

theorem exists_function_of_compatible_exhaustion
    {α β : Type*} (S : ℕ → Set α) (hS : Monotone S)
    (hcover : ∀ a, ∃ n, a ∈ S n) (f : ∀ n, S n → β)
    (hf : ∀ n (a : S n), f (n + 1) ⟨a, hS (Nat.le_succ n) a.property⟩ = f n a) :
    ∃ g : α → β, ∀ n (a : S n), g a = f n a := by
  have hle (n m : ℕ) (hnm : n ≤ m) (a : S n) :
      f m ⟨a, hS hnm a.property⟩ = f n a := by
    induction m, hnm using Nat.le_induction with
    | base => rfl
    | succ m hnm ih =>
      exact (hf m ⟨a, hS hnm a.property⟩).trans ih
  let g (a : α) := f (hcover a).choose ⟨a, (hcover a).choose_spec⟩
  refine ⟨g, ?_⟩
  intro n a
  let m := (hcover (a : α)).choose
  let b : S m := ⟨a, (hcover (a : α)).choose_spec⟩
  exact (hle m (max m n) (le_max_left _ _) b).symm.trans
    (hle n (max m n) (le_max_right _ _) a)

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

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_CochainExhaustion
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Cochains on an increasing exhaustive sequence of subgroups -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory
variable {G : Type} [Group G]

theorem cochains_eq_of_exhaustive_restrictions (S : ℕ → Subgroup G)
    (hS : Monotone S) (hcover : ∀ g, ∃ n, g ∈ S n) (A : Rep ℤ G) (k : ℕ)
    {f g : (Fin k → G) → A}
    (h : ∀ n, (subgroupCochainRestriction (S n) A).f k f =
      (subgroupCochainRestriction (S n) A).f k g) : f = g := by
  classical
  funext a
  obtain ⟨n, hn⟩ := finite_subset_subgroup_exhaustion S hS hcover (Finset.univ.image a)
  let b : Fin k → S n := fun i => ⟨a i, hn (a i) (Finset.mem_image.mpr ⟨i, by simp, rfl⟩)⟩
  exact congrFun (h n) b

theorem exists_cochain_of_compatible_restrictions (S : ℕ → Subgroup G)
    (hS : Monotone S) (hcover : ∀ g, ∃ n, g ∈ S n) (A : Rep ℤ G) (k : ℕ)
    (f : ∀ n, (Fin k → S n) → A)
    (hf : ∀ n (a : Fin k → S n),
      f (n + 1) (fun i => ⟨a i, hS (Nat.le_succ n) (a i).property⟩) = f n a) :
    ∃ g : (Fin k → G) → A, ∀ n,
      (subgroupCochainRestriction (S n) A).f k g = f n := by
  classical
  let T (n : ℕ) : Set (Fin k → G) := {a | ∀ i, a i ∈ S n}
  have hT : Monotone T := fun n m hnm a ha i => hS hnm (ha i)
  have hcoverT (a : Fin k → G) : ∃ n, a ∈ T n := by
    obtain ⟨n, hn⟩ := finite_subset_subgroup_exhaustion S hS hcover (Finset.univ.image a)
    exact ⟨n, fun i => hn (a i) (Finset.mem_image.mpr ⟨i, by simp, rfl⟩)⟩
  let F (n : ℕ) (a : T n) := f n (fun i => ⟨a.val i, a.property i⟩)
  have hF (n : ℕ) (a : T n) :
      F (n + 1) ⟨a, hT (Nat.le_succ n) a.property⟩ = F n a :=
    hf n (fun i => ⟨a.val i, a.property i⟩)
  obtain ⟨g, hg⟩ := exists_function_of_compatible_exhaustion T hT hcoverT F hF
  refine ⟨g, ?_⟩
  intro n
  funext a
  exact hg n ⟨fun i => a i, fun i => (a i).property⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_CountableUnionCohomology
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Cohomology above a uniform dimension bound on an exhaustive sequence

Two consecutive local vanishings suffice. The primitive-correction argument
accounts for the one extra dimension in a countable increasing union.
-/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear

theorem cochain_primitive_of_isZero (C : CochainComplex (ModuleCat ℤ) ℕ) (k : ℕ)
    (h : IsZero (C.homology (k + 1))) (z : C.X (k + 1))
    (hz : C.d (k + 1) (k + 2) z = 0) :
    ∃ y : C.X k, C.d k (k + 1) y = z := by
  have he : (C.sc' k (k + 1) (k + 2)).Exact :=
    (C.exactAt_iff' k (k + 1) (k + 2) (by simp) (by simp)).mp
      ((C.exactAt_iff_isZero_homology (k + 1)).mpr h)
  exact (ShortComplex.moduleCat_exact_iff _).mp he z hz

variable {G : Type} [Group G]

theorem subgroupCochainStep_surjective {H K : Subgroup G} (hHK : H ≤ K)
    (A : Rep ℤ G) (k : ℕ) :
    Function.Surjective ((subgroupCochainStep hHK A).f k) := by
  change Function.Surjective (fun f : (Fin k → K) → A =>
    fun a : Fin k → H => f (fun i => Subgroup.inclusion hHK (a i)))
  apply Function.Injective.surjective_comp_right
  intro a b hab
  funext i
  exact (Subgroup.inclusion_injective hHK) (congrFun hab i)

theorem groupCohomology_isZero_of_exhaustion (S : ℕ → Subgroup G)
    (hS : Monotone S) (hcover : ∀ g, ∃ n, g ∈ S n) (A : Rep ℤ G) (k : ℕ)
    (hlocal₁ : ∀ n, IsZero (groupCohomology (Rep.res (S n).subtype A) (k + 1)))
    (hlocal₂ : ∀ n, IsZero (groupCohomology (Rep.res (S n).subtype A) (k + 2))) :
    IsZero (groupCohomology A (k + 2)) := by
  let C := groupCohomology.inhomogeneousCochains A
  let D (n : ℕ) := groupCohomology.inhomogeneousCochains (Rep.res (S n).subtype A)
  let R (n : ℕ) := subgroupCochainRestriction (S n) A
  let T (n : ℕ) := subgroupCochainStep (hS (Nat.le_succ n)) A
  apply HomologicalComplex.ExactAt.isZero_homology
  apply (C.exactAt_iff' (k + 1) (k + 2) (k + 3) (by simp) (by simp)).mpr
  apply (ShortComplex.moduleCat_exact_iff _).mpr
  intro z hz
  change C.d (k + 2) (k + 3) z = 0 at hz
  let zn (n : ℕ) := (R n).f (k + 2) z
  have hzn (n : ℕ) : (D n).d (k + 2) (k + 3) (zn n) = 0 := by
    have hc := congrArg (fun f => f z) ((R n).comm (k + 2) (k + 3))
    change (D n).d (k + 2) (k + 3) (zn n) =
      (R n).f (k + 3) (C.d (k + 2) (k + 3) z) at hc
    rw [hc, hz, map_zero]
  have hprim (n : ℕ) : ∃ y, (D n).d (k + 1) (k + 2) y = zn n :=
    cochain_primitive_of_isZero (D n) (k + 1) (hlocal₂ n) (zn n) (hzn n)
  obtain ⟨ys, hys, hcompat⟩ := exists_compatible_primitives
    (fun n => ((D n).d k (k + 1)).hom.toAddMonoidHom)
    (fun n => ((D n).d (k + 1) (k + 2)).hom.toAddMonoidHom)
    (fun n => ((T n).f k).hom.toAddMonoidHom)
    (fun n => ((T n).f (k + 1)).hom.toAddMonoidHom)
    (fun n => ((T n).f (k + 2)).hom.toAddMonoidHom)
    (fun n x => (congrArg (fun f => f x) ((T n).comm k (k + 1))).symm)
    (fun n x => (congrArg (fun f => f x) ((T n).comm (k + 1) (k + 2))).symm)
    (fun n x => by
      exact congrArg (fun f => f x) ((D n).d_comp_d k (k + 1) (k + 2)))
    (fun n y hy => cochain_primitive_of_isZero (D n) k (hlocal₁ n) y hy)
    (fun n => subgroupCochainStep_surjective (hS (Nat.le_succ n)) A k)
    zn (fun _ => rfl) hprim
  obtain ⟨y, hy⟩ := exists_cochain_of_compatible_restrictions S hS hcover A (k + 1)
    ys (fun n a => congrFun (hcompat n) a)
  refine ⟨y, ?_⟩
  change C.d (k + 1) (k + 2) y = z
  apply cochains_eq_of_exhaustive_restrictions S hS hcover A (k + 2)
  intro n
  have hc := congrArg (fun f => f y) ((R n).comm (k + 1) (k + 2))
  change (D n).d (k + 1) (k + 2) ((R n).f (k + 1) y) =
    (R n).f (k + 2) (C.d (k + 1) (k + 2) y) at hc
  rw [← hc, hy]
  exact hys n

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_CountableUnionDimension
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instNonemptyBases _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.cyclicTopHomologyInjection_mono _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalizedGroupIdentityClass_comparison _root_.OAI.PolycyclicRecognition.rationalCoefficientInclusion_apply _root_.OAI.PolycyclicRecognition.resolutionStableSyzygyTransition_class _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
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

theorem projectiveDimension_of_cohomology_vanishing (d : ℕ)
    (h : ∀ (A : Rep ℤ G) (i : ℕ), d < i → IsZero (groupCohomology A i)) :
    HasProjectiveDimensionLE (trivialIntegral G) d := by
  let P := Rep.standardResolution ℤ G
  let := HasExt.standard (Rep ℤ G)
  refine HasProjectiveDimensionLT.mk ?_
  intro i hi A e
  cases i with
  | zero => omega
  | succ j =>
    obtain ⟨f, hf, rfl⟩ := P.extMk_surjective e (j + 2) rfl
    let C := P.complex.linearYonedaObj ℤ A
    have hC : C.ExactAt (j + 1) :=
      (C.exactAt_iff_isZero_homology (j + 1)).mpr
        (IsZero.of_iso (h A (j + 1) (by omega)) (groupCohomologyIso A (j + 1) P).symm)
    have hS : (C.sc' j (j + 1) (j + 2)).Exact :=
      (C.exactAt_iff' j (j + 1) (j + 2) (by simp) (by simp)).mp hC
    have hf' : (C.sc' j (j + 1) (j + 2)).g f = 0 := hf
    obtain ⟨g, hg⟩ := (ShortComplex.moduleCat_exact_iff _).mp hS f hf'
    exact (P.extMk_eq_zero_iff f (j + 2) rfl hf j rfl).mpr ⟨g, hg⟩

/-- Countable unions cost at most one additional integral dimension. -/
theorem cohomologicalDimension_le_of_exhaustion (S : ℕ → Subgroup G)
    (hS : Monotone S) (hcover : ∀ g, ∃ n, g ∈ S n) (d : ℕ)
    (hd : ∀ n, HasProjectiveDimensionLE (trivialIntegral (S n)) d) :
    HasProjectiveDimensionLE (trivialIntegral G) (d + 1) := by
  apply projectiveDimension_of_cohomology_vanishing
  intro A i hi
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 2 := ⟨i - 2, by omega⟩
  apply groupCohomology_isZero_of_exhaustion S hS hcover A k
  · intro n
    let := hd n
    exact groupCohomology_isZero_above_dimension d _ _ (by omega)
  · intro n
    let := hd n
    exact groupCohomology_isZero_above_dimension d _ _ (by omega)

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

theorem cohomologicalDimension_le_of_fg_subgroups [Countable G] (d : ℕ)
    (h : ∀ H : Subgroup G, H.FG → HasProjectiveDimensionLE (trivialIntegral H) d) :
    HasProjectiveDimensionLE (trivialIntegral G) (d + 1) := by
  obtain ⟨S, hS, hfg, hcover⟩ := exists_fg_subgroup_exhaustion (G := G)
  exact cohomologicalDimension_le_of_exhaustion S hS hcover d (fun n => h (S n) (hfg n))

end PolycyclicRecognition

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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_FiniteNormalRadical
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finite_templateSymmetryGroup _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteSubtypeLinearEquivRealIdMemSubgroupLinearSupportSymmetryGroup _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The largest finite normal subgroup under a finite-subgroup order bound -/
noncomputable section
namespace PolycyclicRecognition
variable {G : Type} [Group G]

theorem finite_sup_of_normal (H K : Subgroup G) [H.Normal] [Finite H] [Finite K] :
    Finite (H ⊔ K : Subgroup G) := by
  let f : H × K → (H ⊔ K : Subgroup G) := fun p =>
    ⟨(p.1 : G) * p.2, Subgroup.mul_mem_sup p.1.property p.2.property⟩
  apply Finite.of_surjective f
  intro x
  obtain ⟨h, hh, k, hk, he⟩ := Subgroup.mem_sup_of_normal_left.mp x.property
  exact ⟨(⟨h, hh⟩, ⟨k, hk⟩), Subtype.ext he⟩

theorem exists_largest_finite_normal (hb : HasBoundedFiniteSubgroupOrders G) :
    ∃ T : Subgroup G, T.Characteristic ∧ Finite T ∧
      ∀ N : Subgroup G, N.Normal → Finite N → N ≤ T := by
  obtain ⟨b, hb⟩ := hb
  let P : Set (Subgroup G) := {N | N.Normal ∧ Finite N}
  have hP : (Nat.card ∘ (fun N : Subgroup G => N) '' P).Finite := by
    apply (Set.finite_Iic b).subset
    rintro n ⟨N, hN, rfl⟩
    exact hb N hN.2
  obtain ⟨T, hT, hmax⟩ := Set.Finite.exists_maximalFor' (fun N : Subgroup G => Nat.card N)
    P hP ⟨⊥, inferInstance, inferInstance⟩
  let := hT.1
  let := hT.2
  have hle (N : Subgroup G) (hn : N.Normal) (hf : Finite N) : N ≤ T := by
    let := hn
    let := hf
    let : Finite (T ⊔ N : Subgroup G) := finite_sup_of_normal T N
    have hcard : Nat.card (T ⊔ N : Subgroup G) ≤ Nat.card T :=
      hmax ⟨inferInstance, inferInstance⟩ (Subgroup.card_le_of_le le_sup_left)
    have he : T = T ⊔ N := Subgroup.eq_of_le_of_card_ge le_sup_left hcard
    exact le_sup_right.trans_eq he.symm
  have hchar : T.Characteristic := by
    apply Subgroup.characteristic_iff_map_le.mpr
    intro e
    let : Finite (T.map e.toMonoidHom) := Finite.of_equiv T
      (T.equivMapOfInjective e.toMonoidHom e.injective).toEquiv
    exact hle _ (Subgroup.Normal.map inferInstance e.toMonoidHom e.surjective) inferInstance
  exact ⟨T, hchar, hT.2, hle⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_FiniteKernelSubgroupBounds
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finite_templateSymmetryGroup _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteSubtypeLinearEquivRealIdMemSubgroupLinearSupportSymmetryGroup _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite-subgroup bounds and the quotient by the finite radical -/
noncomputable section
namespace PolycyclicRecognition
variable {G Q : Type} [Group G] [Group Q]

theorem finite_subgroup_preimage (q : G →* Q) [Finite q.ker]
    (S : Subgroup Q) [Finite S] : Finite (S.comap q) := by
  let P := S.comap q
  let f : P →* S := (q.comp P.subtype).codRestrict S (fun p => p.property)
  let j : f.ker → q.ker := fun p => ⟨((p : P) : G),
    congrArg (fun s : S => (s : Q)) p.property⟩
  have hj : Function.Injective j := by
    intro p r hpr
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : q.ker => (z : G)) hpr
  let : Finite f.ker := Finite.of_injective j hj
  exact f.finite_iff_finite_ker_range.mpr ⟨inferInstance, inferInstance⟩

theorem boundedFiniteSubgroupOrders_of_finite_kernel_quotient
    (q : G →* Q) (hq : Function.Surjective q) [Finite q.ker]
    (hb : HasBoundedFiniteSubgroupOrders G) : HasBoundedFiniteSubgroupOrders Q := by
  obtain ⟨b, hb⟩ := hb
  refine ⟨b, fun S hS => ?_⟩
  let := hS
  let : Finite (S.comap q) := finite_subgroup_preimage q S
  let f : S.comap q →* S := (q.comp (S.comap q).subtype).codRestrict S (fun p => p.property)
  have hf : Function.Surjective f := by
    intro s
    obtain ⟨g, hg⟩ := hq s
    exact ⟨⟨g, by change q g ∈ S; rw [hg]; exact s.property⟩, Subtype.ext hg⟩
  exact (Nat.card_le_card_of_surjective f hf).trans (hb (S.comap q) inferInstance)

theorem finite_normal_quotient_eq_bot (T : Subgroup G) [T.Normal] [Finite T]
    (hT : ∀ N : Subgroup G, N.Normal → Finite N → N ≤ T)
    (S : Subgroup (G ⧸ T)) [S.Normal] [Finite S] : S = ⊥ := by
  let q := QuotientGroup.mk' T
  let P := S.comap q
  let : Finite q.ker := by simpa only [q, QuotientGroup.ker_mk'] using (inferInstance : Finite T)
  let : Finite P := finite_subgroup_preimage q S
  have hP : P ≤ T := hT P inferInstance inferInstance
  apply eq_bot_iff.mpr
  intro s hs
  obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective T s
  have hgP : g ∈ P := by change q g ∈ S; rw [hg]; exact hs
  exact hg.symm.trans ((QuotientGroup.eq_one_iff g).mpr (hP hgP))

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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_RationalFiniteCoinvariants
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instNonemptyBases _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact rational coinvariants for a finite group

The averaging map descends to coinvariants and is a section of their quotient
map. Its naturality proves preservation of injections directly.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2300] Representation.Coinvariants.instModule
variable {H : Type} [Group H] [Fintype H]
variable {V W : Type} [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]

theorem finiteRationalAverage_mk (ρ : Representation ℚ H V) (x : V) :
    Representation.Coinvariants.mk ρ (finiteRationalAverage ρ x) =
      Representation.Coinvariants.mk ρ x := by
  rw [finiteRationalAverage_apply, map_smul, map_sum]
  simp only [Representation.Coinvariants.mk_self_apply, Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℚ, smul_smul,
    inv_mul_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero), one_smul]

theorem finiteRationalAverage_natural (ρ : Representation ℚ H V)
    (σ : Representation ℚ H W) (f : Representation.IntertwiningMap ρ σ) (x : V) :
    f (finiteRationalAverage ρ x) = finiteRationalAverage σ (f x) := by
  simp only [finiteRationalAverage_apply, map_smul, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro g _
  exact congrArg (fun u : V →ₗ[ℚ] W => u x) (f.isIntertwining' g)

theorem finiteRationalCoinvariants_map_injective (ρ : Representation ℚ H V)
    (σ : Representation ℚ H W) (f : Representation.IntertwiningMap ρ σ)
    (hf : Function.Injective f) :
    Function.Injective (Representation.Coinvariants.map ρ σ f) := by
  intro x y hxy
  induction x using Representation.Coinvariants.induction_on with
  | h x =>
    induction y using Representation.Coinvariants.induction_on with
    | h y =>
      have he := congrArg (finiteRationalCoinvariantsSection σ) hxy
      change finiteRationalAverage σ (f x) = finiteRationalAverage σ (f y) at he
      rw [← finiteRationalAverage_natural ρ σ f, ← finiteRationalAverage_natural ρ σ f] at he
      calc
        Representation.Coinvariants.mk ρ x =
          Representation.Coinvariants.mk ρ (finiteRationalAverage ρ x) :=
            (finiteRationalAverage_mk ρ x).symm
        _ = Representation.Coinvariants.mk ρ (finiteRationalAverage ρ y) :=
          congrArg (Representation.Coinvariants.mk ρ) (hf he)
        _ = Representation.Coinvariants.mk ρ y := finiteRationalAverage_mk ρ y

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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Lattices_LatticeQuotientDimension
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.cyclicTopHomologyInjection_mono _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.latticeNormalFlag_normal _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integral dimension through a free abelian quotient -/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory

theorem cohomologicalDimension_le_of_lattice_quotient (r : ℕ)
    {G : Type} [Group G] (q : G →* IntegralLatticeGroup r)
    (hq : Function.Surjective q) (d : ℕ)
    [HasProjectiveDimensionLE (trivialIntegral q.ker) d] :
    HasProjectiveDimensionLE (trivialIntegral G) (d + r) := by
  induction r generalizing G with
  | zero =>
    have hker : q.ker = ⊤ := by
      ext g
      exact iff_of_true (Subsingleton.elim (q g) 1) (Subgroup.mem_top g)
    let e := (MulEquiv.subgroupCongr hker).trans Subgroup.topEquiv
    simpa only [Nat.add_zero] using cohomologicalDimension_le_of_equiv e d
  | succ r ih =>
    let p := (latticeCoordinate r).comp q
    obtain ⟨t, ht⟩ := hq (latticeCoordinateSection r)
    have hpt : p t = Multiplicative.ofAdd 1 := by
      change latticeCoordinate r (q t) = _
      rw [ht, latticeCoordinate_section]
    let := integerQuotient_isCyclic p t hpt
    let := integerQuotient_infinite p t hpt
    let := cohomologicalDimension_le_of_equiv (latticeKernelTailEquiv q) d
    let := ih (latticeKernelTail q) (latticeKernelTail_surjective q hq)
    simpa only [Nat.add_assoc] using
      cohomologicalDimension_le_of_infiniteCyclicQuotient p.ker (d + r)

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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CentralExtensionRootCore
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Root cores lift through an actual central kernel -/

noncomputable section
namespace PolycyclicRecognition
variable {G : Type} [Group G]

theorem central_extension_rootCore (N : Subgroup G) [N.Normal]
    (hcentral : N ≤ Subgroup.center G)
    (hN : ∃ L : Subgroup N, L.FG ∧ ∀ a, ∃ n : ℕ, 0 < n ∧ a ^ n ∈ L)
    (hQ : ∃ L : Subgroup (G ⧸ N), L.FG ∧ ∀ a, ∃ n : ℕ, 0 < n ∧ a ^ n ∈ L) :
    ∃ H : Subgroup G, H.FG ∧ ∀ a, ∃ n : ℕ, 0 < n ∧ a ^ n ∈ H := by
  obtain ⟨LN, hLN, hn⟩ := hN
  obtain ⟨LQ, hLQ, hq⟩ := hQ
  let q := QuotientGroup.mk' N
  let P := LQ.comap q
  let : Group.FG LQ := (Group.fg_iff_subgroup_fg LQ).mpr hLQ
  obtain ⟨F, hF, hFsurj⟩ := exists_fg_subgroup_surjective
    (quotientSubgroupMap q LQ)
    (quotientSubgroupMap_surjective q (QuotientGroup.mk'_surjective _) LQ)
  let K := F.map P.subtype
  let Z := LN.map N.subtype
  let H := K ⊔ Z
  refine ⟨H, (fg_subgroup_map hF P.subtype).sup (fg_subgroup_map hLN N.subtype), ?_⟩
  intro g
  obtain ⟨n, hnpos, hgn⟩ := hq (q g)
  have hgn' : q (g ^ n) ∈ LQ := by simpa only [map_pow] using hgn
  obtain ⟨x, hx⟩ := hFsurj ⟨q (g ^ n), hgn'⟩
  let k : G := x.val.val
  have hk : k ∈ K := ⟨x.val, x.property, rfl⟩
  have hqk : q k = q (g ^ n) := congrArg Subtype.val hx
  let z := g ^ n * k⁻¹
  have hzN : z ∈ N := by
    apply (QuotientGroup.eq_one_iff _).mp
    change q (g ^ n * k⁻¹) = 1
    rw [map_mul, map_inv, hqk, mul_inv_cancel]
  obtain ⟨m, hm, hzm⟩ := hn ⟨z, hzN⟩
  have hzm' : z ^ m ∈ Z := ⟨(⟨z, hzN⟩ : N) ^ m, hzm, rfl⟩
  have hcomm : Commute z k := (Subgroup.mem_center_iff.mp (hcentral hzN) k).symm
  have he : g ^ n = z * k := by simp [z, mul_assoc]
  refine ⟨n * m, Nat.mul_pos hnpos hm, ?_⟩
  rw [pow_mul, he, hcomm.mul_pow]
  exact H.mul_mem ((show Z ≤ H from le_sup_right) hzm')
    (H.pow_mem ((show K ≤ H from le_sup_left) hk) m)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_AbelianFiniteRankRootCore
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A finite root core for an abelian group with arbitrary torsion

Only finite rational rank is needed. Quotienting by the actual torsion
subgroup gives a torsion-free root core, and finite lifts suffice upstairs.
-/

noncomputable section
namespace PolycyclicRecognition
open scoped TensorProduct
variable {A : Type} [CommGroup A]

theorem abelian_finiteRank_rootCore [Module.Finite ℚ (RationalAbelianSpace A)] :
    ∃ H : Subgroup A, H.FG ∧ ∀ a, ∃ n : ℕ, 0 < n ∧ a ^ n ∈ H := by
  let T := CommGroup.torsion A
  let Q := A ⧸ T
  let q : A →* Q := QuotientGroup.mk' T
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective T
  let f := q.toAdditive.toIntLinearMap
  have hf : Function.Surjective f := hq
  let : Module.Finite ℚ (RationalAbelianSpace Q) :=
    Module.Finite.of_surjective (f.baseChange ℚ) (f.baseChange_surjective ℚ hf)
  have htQ : HasNoNontrivialTorsion Q := by
    intro a n hn ha
    exact (pow_eq_one_iff_left hn).mp ha
  obtain ⟨L, hL, hroot⟩ := abelian_exists_fg_subgroup_containing_powers htQ
  let P := L.comap q
  let : Group.FG L := (Group.fg_iff_subgroup_fg L).mpr hL
  obtain ⟨F, hF, hFq⟩ := exists_fg_subgroup_surjective
    (quotientSubgroupMap q L) (quotientSubgroupMap_surjective q hq L)
  let H := F.map P.subtype
  refine ⟨H, fg_subgroup_map hF P.subtype, ?_⟩
  intro a
  obtain ⟨n, hn, hna⟩ := hroot (q a)
  have hna' : q (a ^ n) ∈ L := by simpa only [map_pow] using hna
  obtain ⟨x, hx⟩ := hFq ⟨q (a ^ n), hna'⟩
  let b : A := x.val.val
  have hb : b ∈ H := ⟨x.val, x.property, rfl⟩
  have hqb : q b = q (a ^ n) := congrArg Subtype.val hx
  have ht : a ^ n * b⁻¹ ∈ T := by
    apply (QuotientGroup.eq_one_iff _).mp
    change q (a ^ n * b⁻¹) = 1
    rw [map_mul, map_inv, hqb, mul_inv_cancel]
  obtain ⟨m, hm, he⟩ := ht.exists_pow_eq_one
  have hab : a ^ (n * m) = b ^ m := by
    rw [mul_pow, inv_pow, mul_inv_eq_one, ← pow_mul] at he
    exact he
  refine ⟨n * m, Nat.mul_pos hn hm, ?_⟩
  rw [hab]
  exact H.pow_mem hb m

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_RationalRootSurjection
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Rational surjectivity from positive powers in the image -/

noncomputable section
namespace PolycyclicRecognition
open scoped TensorProduct
variable {A B : Type} [CommGroup A] [CommGroup B]

theorem rational_map_surjective_of_roots (f : A →* B)
    (hroot : ∀ b : B, ∃ n : ℕ, 0 < n ∧ b ^ n ∈ f.range) :
    Function.Surjective (f.toAdditive.toIntLinearMap.baseChange ℚ) := by
  let F := f.toAdditive.toIntLinearMap.baseChange ℚ
  have hunit (b : B) : scalarTensorUnit ℚ (Additive B) (Additive.ofMul b) ∈
      LinearMap.range F := by
    obtain ⟨n, hn, a, ha⟩ := hroot b
    have hnQ : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
    have hnmem : (n : ℚ) • scalarTensorUnit ℚ (Additive B) (Additive.ofMul b) ∈
        LinearMap.range F := by
      refine ⟨scalarTensorUnit ℚ (Additive A) (Additive.ofMul a), ?_⟩
      change (1 : ℚ) ⊗ₜ[ℤ] Additive.ofMul (f a) = _
      rw [ha]
      change scalarTensorUnit ℚ (Additive B) (n • Additive.ofMul b) = _
      rw [map_nsmul, Nat.cast_smul_eq_nsmul]
    have h := (LinearMap.range F).smul_mem ((n : ℚ)⁻¹) hnmem
    simpa only [inv_smul_smul₀ hnQ] using h
  apply LinearMap.range_eq_top.mp
  suffices ∀ z, z ∈ LinearMap.range F from top_unique (fun z _ => this z)
  intro z
  induction z using OAI.tensorInductionOn with
  | tmul r b =>
    simpa only [scalarTensorUnit_smul, ofMul_toMul] using
      (LinearMap.range F).smul_mem r (hunit b.toMul)
  | add x y hx hy => exact (LinearMap.range F).add_mem hx hy

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_RootCoreAbelianRank
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

namespace OAI

/-! # Abelian subgroups of nilpotent groups with a finite root core

A finitely generated core meets every abelian subgroup in a finitely
generated subgroup with the same rational span. No torsion-free hypothesis
is needed for this rank statement.
-/

noncomputable section
namespace PolycyclicRecognition
open scoped IsMulCommutative
variable {G : Type} [Group G] [Group.IsNilpotent G]

theorem nilpotent_rootCore_abelian_subgroup_finite
    (H : Subgroup G) (hH : H.FG)
    (hroot : ∀ g : G, ∃ n : ℕ, 0 < n ∧ g ^ n ∈ H)
    (A : Subgroup G) [IsMulCommutative A] :
    Module.Finite ℚ (RationalAbelianSpace A) := by
  let : Group.FG H := (Group.fg_iff_subgroup_fg H).mpr hH
  let J := A.comap H.subtype
  let : Group.FG J := CriticalPercolation.nilpotent_subgroup_fg H J
  let f : J →* A := (H.subtype.comp J.subtype).codRestrict A (fun j => j.property)
  have hf : Function.Injective f := by
    intro a b he
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun x : A => (x : G)) he
  let : IsMulCommutative J := ⟨⟨fun a b => hf (by
    rw [map_mul, map_mul, mul_comm])⟩⟩
  let : Module.Finite ℤ (Additive J) := Module.Finite.iff_addGroup_fg.mpr inferInstance
  apply Module.Finite.of_surjective (f.toAdditive.toIntLinearMap.baseChange ℚ)
  apply rational_map_surjective_of_roots
  intro a
  obtain ⟨n, hn, hna⟩ := hroot (a : G)
  refine ⟨n, hn, ?_⟩
  let b : J := ⟨⟨(a : G) ^ n, hna⟩, A.pow_mem a.property n⟩
  exact ⟨b, Subtype.ext rfl⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_NilpotentFiniteRankRootCore
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

namespace OAI

/-! # Finite root cores from the rational abelianization of a nilpotent group

Induction uses the last lower-central layer. Its commutator tensor
presentation is finite because the preceding layer is an abelian subgroup
of the quotient, where a finite root core has already been constructed.
-/

noncomputable section
namespace PolycyclicRecognition
open scoped TensorProduct IsMulCommutative commutatorElement
variable {G Q : Type} [Group G] [Group Q]

theorem rational_abelianization_finite_of_surjective (f : G →* Q)
    (hf : Function.Surjective f)
    [Module.Finite ℚ (RationalAbelianSpace (Abelianization G))] :
    Module.Finite ℚ (RationalAbelianSpace (Abelianization Q)) :=
  Module.Finite.of_surjective ((Abelianization.map f).toAdditive.toIntLinearMap.baseChange ℚ)
    ((Abelianization.map f).toAdditive.toIntLinearMap.baseChange_surjective ℚ
      (abelianization_map_surjective f hf))

theorem lowerCentral_rootCore_of_finite_abelianization (n : ℕ)
    (hbound : (⊤ : Subgroup G).lowerCentralSeries n = ⊥)
    [Module.Finite ℚ (RationalAbelianSpace (Abelianization G))] :
    ∃ H : Subgroup G, H.FG ∧ ∀ g, ∃ m : ℕ, 0 < m ∧ g ^ m ∈ H := by
  induction n generalizing G with
  | zero =>
    have hg (g : G) : g = 1 := by
      have hm : g ∈ (⊤ : Subgroup G) := Subgroup.mem_top g
      rw [show (⊤ : Subgroup G) = ⊥ from hbound] at hm
      exact hm
    exact ⟨⊥, Subgroup.FG.bot, fun g => ⟨1, by omega, by simp [hg g]⟩⟩
  | succ n ih =>
    cases n with
    | zero =>
      let : IsMulCommutative G := (commutator_eq_bot_iff G).mp hbound
      let e : Additive (Abelianization G) ≃ₗ[ℤ] Additive G :=
        (Abelianization.equivOfComm (H := G)).symm.toAdditive.toIntLinearEquiv
      let : Module.Finite ℚ (RationalAbelianSpace G) :=
        Module.Finite.of_surjective (e.baseChange ℤ ℚ _ _).toLinearMap
          (e.baseChange ℤ ℚ _ _).surjective
      exact abelian_finiteRank_rootCore
    | succ n =>
      let J := (⊤ : Subgroup G).lowerCentralSeries (n + 1)
      let N := (⊤ : Subgroup G).lowerCentralSeries n
      have hJcenter : J ≤ Subgroup.center G :=
        Subgroup.commutator_top_right_eq_bot_iff_le_center.mp hbound
      have hC : ⁅(⊤ : Subgroup G), N⁆ = J :=
        Subgroup.commutator_comm _ _
      let q := QuotientGroup.mk' J
      have hq : Function.Surjective q := QuotientGroup.mk'_surjective J
      have hJmap : J.map q = ⊥ := by
        rw [Subgroup.map_eq_bot_iff]
        exact le_of_eq (QuotientGroup.ker_mk' J).symm
      have hQbound : (⊤ : Subgroup (G ⧸ J)).lowerCentralSeries (n + 1) = ⊥ := by
        have he := Subgroup.map_lowerCentralSeries (⊤ : Subgroup G) q (n + 1)
        rw [← MonoidHom.range_eq_map, q.range_eq_top_of_surjective hq] at he
        exact he.symm.trans hJmap
      let : Module.Finite ℚ (RationalAbelianSpace (Abelianization (G ⧸ J))) :=
        rational_abelianization_finite_of_surjective q hq
      obtain ⟨H, hH, hroot⟩ := ih hQbound
      let : Group.IsNilpotent (G ⧸ J) :=
        Subgroup.nilpotent_iff_lowerCentralSeries.mpr ⟨n + 1, hQbound⟩
      let f := q.comp N.subtype
      have hAc : f.range ≤ Subgroup.center (G ⧸ J) := by
        rintro _ ⟨b, rfl⟩
        rw [Subgroup.mem_center_iff]
        intro a
        obtain ⟨g, rfl⟩ := hq a
        apply commutatorElement_eq_one_iff_mul_comm.mp
        change ⁅q g, q (b : G)⁆ = 1
        rw [← map_commutatorElement]
        apply (QuotientGroup.eq_one_iff _).mpr
        rw [← hC]
        exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) b.property
      let : IsMulCommutative f.range := ⟨⟨fun a b =>
        Subtype.ext (Subgroup.mem_center_iff.mp (hAc a.property) b).symm⟩⟩
      let : Module.Finite ℚ (RationalAbelianSpace f.range) :=
        nilpotent_rootCore_abelian_subgroup_finite H hH hroot f.range
      let K := f.ker
      let e := QuotientGroup.quotientKerEquivRange f
      let : IsMulCommutative (N ⧸ K) := ⟨⟨fun a b => e.injective (by
        rw [map_mul, map_mul, mul_comm])⟩⟩
      let : Module.Finite ℚ (RationalAbelianSpace (N ⧸ K)) :=
        Module.Finite.of_surjective (e.symm.toAdditive.toIntLinearEquiv.baseChange ℤ ℚ _ _).toLinearMap
          (e.symm.toAdditive.toIntLinearEquiv.baseChange ℤ ℚ _ _).surjective
      have hKc : K.map N.subtype ≤ Subgroup.center G := by
        rintro _ ⟨b, hb, rfl⟩
        apply hJcenter
        exact (QuotientGroup.eq_one_iff _).mp hb
      have hCc : ⁅(⊤ : Subgroup G), N⁆ ≤ Subgroup.center G := hC ▸ hJcenter
      let : IsMulCommutative J := ⟨⟨fun a b =>
        Subtype.ext (Subgroup.mem_center_iff.mp (hJcenter a.property) b).symm⟩⟩
      let : IsMulCommutative (⁅(⊤ : Subgroup G), N⁆ : Subgroup G) := hC.symm ▸ inferInstance
      have hfin := central_commutator_scalar_finite N hCc K hKc ℚ
      let : Module.Finite ℚ (RationalAbelianSpace J) := by
        let := hfin
        let eJ : Additive (⁅(⊤ : Subgroup G), N⁆ : Subgroup G) ≃ₗ[ℤ] Additive J :=
          (MulEquiv.subgroupCongr hC).toAdditive.toIntLinearEquiv
        exact Module.Finite.of_surjective (eJ.baseChange ℤ ℚ _ _).toLinearMap
          (eJ.baseChange ℤ ℚ _ _).surjective
      exact central_extension_rootCore J hJcenter abelian_finiteRank_rootCore ⟨H, hH, hroot⟩

theorem nilpotent_rootCore_of_finite_abelianization [Group.IsNilpotent G]
    [Module.Finite ℚ (RationalAbelianSpace (Abelianization G))] :
    ∃ H : Subgroup G, H.FG ∧ ∀ g, ∃ n : ℕ, 0 < n ∧ g ^ n ∈ H :=
  lowerCentral_rootCore_of_finite_abelianization (Group.nilpotencyClass G)
    (Subgroup.lowerCentralSeries_nilpotencyClass (G := G))

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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_NilpotentRootDimension
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.cyclicTopHomologyInjection_mono _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite integral dimension from a finite nilpotent root core

A finitely generated subgroup containing a positive power of every element
has finite index in each finitely generated overgroup. Those overgroups have
one common duality dimension. The countable-union theorem then supplies a
finite integral dimension for the original, possibly infinitely generated,
nilpotent group. No ambient dimension bound is assumed.
-/

noncomputable section
namespace PolycyclicRecognition

variable {G : Type} [Group G] [Group.IsNilpotent G]

theorem nilpotent_rootCore_finiteIndex_of_torsionFree
    (htf : HasNoNontrivialTorsion G) (H : Subgroup G)
    (hroot : ∀ g, ∃ n : ℕ, 0 < n ∧ g ^ n ∈ H)
    (L : Subgroup G) (hL : L.FG) : (H.subgroupOf L).FiniteIndex := by
  let : Group.FG L := (Group.fg_iff_subgroup_fg L).mpr hL
  have hp := (nilpotent_polyZ_of_finitelyGenerated_torsionFree
    (htf.of_injective L.subtype Subtype.val_injective)).isPolycyclic
  apply hp.finiteIndex_of_roots
  intro g
  obtain ⟨n, hn, hg⟩ := hroot g
  exact ⟨n, hn, hg⟩

theorem nilpotent_rootCore_common_duality
    (htf : HasNoNontrivialTorsion G) (H : Subgroup G) (hH : H.FG)
    (hroot : ∀ g, ∃ n : ℕ, 0 < n ∧ g ^ n ∈ H) :
    ∃ d, IsIntegralPoincareDualityGroup H d ∧
      ∀ L : Subgroup G, L.FG → H ≤ L → IsIntegralPoincareDualityGroup L d := by
  let : Group.FG H := (Group.fg_iff_subgroup_fg H).mpr hH
  obtain ⟨d, hd⟩ := nilpotent_poincareDuality_of_finitelyGenerated_torsionFree
    (htf.of_injective H.subtype Subtype.val_injective)
  refine ⟨d, hd, ?_⟩
  intro L hL hHL
  let : Group.FG L := (Group.fg_iff_subgroup_fg L).mpr hL
  obtain ⟨e, he⟩ := nilpotent_poincareDuality_of_finitelyGenerated_torsionFree
    (htf.of_injective L.subtype Subtype.val_injective)
  let := nilpotent_rootCore_finiteIndex_of_torsionFree htf H hroot L hL
  have hHe : IsIntegralPoincareDualityGroup H e :=
    (he.finiteIndex_subgroup (H.subgroupOf L)).of_equiv
      (Subgroup.subgroupOfEquivOfLe hHL)
  have hde : d = e := hd.dimension_unique hHe
  exact hde ▸ he

theorem nilpotent_finiteDimension_of_rootCore [Countable G]
    (htf : HasNoNontrivialTorsion G) (H : Subgroup G) (hH : H.FG)
    (hroot : ∀ g, ∃ n : ℕ, 0 < n ∧ g ^ n ∈ H) :
    HasFiniteIntegralCohomologicalDimension G := by
  obtain ⟨d, _, hd⟩ := nilpotent_rootCore_common_duality htf H hH hroot
  obtain ⟨T, hT, hfg, hcover⟩ := exists_fg_subgroup_exhaustion (G := G)
  let S (n : ℕ) := H ⊔ T n
  have hS : Monotone S := fun _ _ h => sup_le_sup_left (hT h) H
  have hSfg (n : ℕ) : (S n).FG := hH.sup (hfg n)
  have hScover (g : G) : ∃ n, g ∈ S n := by
    obtain ⟨n, hn⟩ := hcover g
    exact ⟨n, (show T n ≤ S n from le_sup_right) hn⟩
  exact ⟨d + 1, cohomologicalDimension_le_of_exhaustion S hS hScover d
    (fun n => (hd (S n) (hSfg n) le_sup_left).cohomologicalDimension)⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_NilpotentAbelianizedDimension
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.cyclicTopHomologyInjection_mono _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.finitelyGeneratedSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.latticeNormalFlag_normal _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

namespace OAI

/-! # The nilpotent-kernel finite-dimension endgame from rational H1

The rank premise is explicit. This module does not assert that FP-infinity
has already supplied it for arbitrary nilpotent kernels.
-/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
open scoped IsMulCommutative

theorem nilpotent_finiteDimension_of_finite_abelianization
    {G : Type} [Group G] [Group.IsNilpotent G] [Countable G]
    (htf : HasNoNontrivialTorsion G)
    [Module.Finite ℚ (RationalAbelianSpace (Abelianization G))] :
    HasFiniteIntegralCohomologicalDimension G := by
  obtain ⟨H, hH, hroot⟩ := nilpotent_rootCore_of_finite_abelianization (G := G)
  exact nilpotent_finiteDimension_of_rootCore htf H hH hroot

theorem nilpotent_abelianization_virtual_finite_dimension
    {G : Type} [Group G] [Group.FG G]
    (N : Subgroup G) [N.Normal] [Group.IsNilpotent N] [IsMulCommutative (G ⧸ N)]
    (htfN : HasNoNontrivialTorsion N)
    [Module.Finite ℚ (RationalAbelianSpace (Abelianization N))] :
    ∃ V : Subgroup G, V.FiniteIndex ∧ Group.IsSolvable V ∧
      HasFiniteIntegralCohomologicalDimension V := by
  let : Group.IsSolvable G := (Group.isSolvable_iff_subgroup_quotient N).mpr ⟨inferInstance, inferInstance⟩
  let : Countable G := countable_of_group_fg G
  obtain ⟨d, hd⟩ := nilpotent_finiteDimension_of_finite_abelianization htfN
  let := hd
  have hQ : IsPolycyclic (G ⧸ N) := isPolycyclic_of_finitelyGenerated_nilpotent (G ⧸ N)
  obtain ⟨U, hU, htfU⟩ := hQ.exists_torsionFree_finiteIndex
  let := hU
  obtain ⟨r, ⟨e⟩⟩ := exists_integralLattice_equiv (A := U) htfU
  let π := QuotientGroup.mk' N
  let P := U.comap π
  let : P.FiniteIndex := inferInstance
  let f : P →* U := (π.comp P.subtype).codRestrict U (fun x => x.property)
  have hf : Function.Surjective f := by
    intro u
    obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective N (u : G ⧸ N)
    have hgP : g ∈ P := by change π g ∈ U; rw [hg]; exact u.property
    exact ⟨⟨g, hgP⟩, Subtype.ext hg⟩
  let q := e.symm.toMonoidHom.comp f
  have hq : Function.Surjective q := e.symm.surjective.comp hf
  have hk (a : q.ker) : ((a : P) : G) ∈ N := by
    have ha : q (a : P) = 1 := a.property
    have hfa : f (a : P) = 1 := e.symm.injective (ha.trans e.symm.map_one.symm)
    apply (QuotientGroup.eq_one_iff _).mp
    exact congrArg (fun u : U => (u : G ⧸ N)) hfa
  let k : q.ker →* N := (P.subtype.comp q.ker.subtype).codRestrict N hk
  have hki : Function.Injective k := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun x : N => (x : G)) hab
  let := cohomologicalDimension_le_of_injective k hki d
  let := cohomologicalDimension_le_of_lattice_quotient r q hq d
  exact ⟨P, inferInstance, inferInstance, d + r, inferInstance⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_RationalHomologyDimension
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.rationalModuleFunctor_preservesFiniteColimits _root_.OAI.PolycyclicRecognition.rationalModuleFunctor_preservesFiniteLimits _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
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

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_RationalFiniteQuotient
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Rational dimension under a finite normal quotient -/
noncomputable section
namespace PolycyclicRecognition.RationalQuotient
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2300] Representation.Coinvariants.instModule
variable {G : Type} [Group G] (N : Subgroup G) [N.Normal]

instance instPreservesMonomorphismsRepRatQuotientSubgroupQuotientToCoinvariantsFunctorOfFiniteSubtypeMem_solutions [Finite N] :
    (Rep.quotientToCoinvariantsFunctor.{0} ℚ N).PreservesMonomorphisms where
  preserves f hf := by
    classical
    let : Fintype N := Fintype.ofFinite N
    apply (Rep.mono_iff_injective _).mpr
    exact finiteRationalCoinvariants_map_injective _ _
      ((Rep.resFunctor N.subtype).map f).hom ((Rep.mono_iff_injective f).mp hf)

instance instPreservesHomologyRepRatQuotientSubgroupQuotientToCoinvariantsFunctorOfFiniteSubtypeMem_solutions [Finite N] : (Rep.quotientToCoinvariantsFunctor.{0} ℚ N).PreservesHomology := by
  let F := Rep.quotientToCoinvariantsFunctor.{0} ℚ N
  apply (Functor.exact_tfae F).out (1-1) (3-1) |>.mp
  intro S hS
  have hm : Mono (F.map S.f) := by
    let : Mono S.f := hS.mono_f
    infer_instance
  have he := (Functor.preservesFiniteColimits_iff_forall_exact_map_and_epi F).mp
    (inferInstance : PreservesFiniteColimits F) S hS
  exact { exact := he.1, mono_f := hm, epi_g := he.2 }

theorem exactFunctor_rational_dimension {K : Type} [Group K]
    (F : Rep.{0} ℚ G ⥤ Rep.{0} ℚ K)
    [F.Additive] [F.PreservesHomology] [F.PreservesMonomorphisms]
    [F.PreservesEpimorphisms] [F.PreservesProjectiveObjects]
    (A : Rep.{0} ℚ G) (d : ℕ) (hd : HasProjectiveDimensionLE A d) :
    HasProjectiveDimensionLE (F.obj A) d := by
  induction d generalizing A with
  | zero =>
    exact (projective_iff_hasProjectiveDimensionLE_zero _).mp
      (F.projective_obj_of_projective ((projective_iff_hasProjectiveDimensionLE_zero A).mpr hd))
  | succ d ih =>
    let p := Projective.π A
    let S := ShortComplex.mk (kernel.ι p) p (kernel.condition p)
    have hS : S.ShortExact :=
      { exact := ShortComplex.exact_of_f_is_kernel S (kernelIsKernel p) }
    have hk : HasProjectiveDimensionLE (kernel p) d :=
      hS.hasProjectiveDimensionLT_X₁ (d + 1)
        (hasProjectiveDimensionLT_of_ge (Projective.over A) 1 (d + 1) (by omega)) hd
    have hki := ih (kernel p) hk
    let : Mono S.f := hS.mono_f
    let : Epi S.g := hS.epi_g
    let : Projective (F.obj (Projective.over A)) :=
      F.projective_obj_of_projective (inferInstance : Projective (Projective.over A))
    exact (hS.map F).hasProjectiveDimensionLT_X₃ (d + 1) hki
      (hasProjectiveDimensionLT_of_ge (F.obj (Projective.over A)) 1 (d + 2) (by omega))

theorem rational_dimension_quotient [Finite N] (d : ℕ)
    (hd : HasProjectiveDimensionLE (Rep.trivial ℚ G ℚ) d) :
    HasProjectiveDimensionLE (Rep.trivial ℚ (G ⧸ N) ℚ) d := by
  let : HasProjectiveDimensionLE ((Rep.trivial ℚ G ℚ).quotientToCoinvariants N) d :=
    exactFunctor_rational_dimension (Rep.quotientToCoinvariantsFunctor.{0} ℚ N)
    (Rep.trivial ℚ G ℚ) d hd
  exact hasProjectiveDimensionLT_of_iso (trivialCoinvariantsIso N) (d + 1)


theorem rational_dimension_subgroup (H : Subgroup G) (d : ℕ)
    (hd : HasProjectiveDimensionLE (Rep.trivial ℚ G ℚ) d) :
    HasProjectiveDimensionLE (Rep.trivial ℚ H ℚ) d :=
  exactFunctor_rational_dimension (Rep.resFunctor H.subtype) (Rep.trivial ℚ G ℚ) d hd

end PolycyclicRecognition.RationalQuotient

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_RationalLocallyNilpotentDimension
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.instPreservesMonomorphismsRepRatQuotientSubgroupQuotientToCoinvariantsFunctorOfFiniteSubtypeMem_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.cyclicTopHomologyInjection_mono _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
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

theorem RationalHomologyDimensionLE.locallyNilpotent_integralDimension [Countable G]
    {d : ℕ} (hd : RationalHomologyDimensionLE G d)
    (htf : HasNoNontrivialTorsion G)
    (hlocal : ∀ H : Subgroup G, H.FG → Group.IsNilpotent H) :
    HasProjectiveDimensionLE (trivialIntegral G) (d + 1) := by
  apply cohomologicalDimension_le_of_fg_subgroups d
  intro H hH
  let := hlocal H hH
  exact hd.nilpotent_subgroup_dimension H hH
    (htf.of_injective H.subtype Subtype.val_injective)

theorem RationalHomologyDimensionLE.locallyNilpotent_isNilpotent [Countable G]
    {d : ℕ} (hd : RationalHomologyDimensionLE G d)
    (htf : HasNoNontrivialTorsion G)
    (hlocal : ∀ H : Subgroup G, H.FG → Group.IsNilpotent H) :
    Group.IsNilpotent G := by
  apply (show HasFiniteIntegralCohomologicalDimension G from
    ⟨d + 1, hd.locallyNilpotent_integralDimension htf hlocal⟩).nilpotent_of_locallyNilpotent
  intro H hH
  exact hlocal H ((Group.fg_iff_subgroup_fg H).mp hH)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_NilpotentTorsionSubgroup
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.instPreservesMonomorphismsRepRatQuotientSubgroupQuotientToCoinvariantsFunctorOfFiniteSubtypeMem_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finite_templateSymmetryGroup _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteSubtypeLinearEquivRealIdMemSubgroupLinearSupportSymmetryGroup _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The characteristic torsion subgroup of a nilpotent group

Zero rational abelianization shows that a subgroup generated by torsion
elements is torsion. This constructs the subgroup and its torsion-free
quotient without a finite-generation premise.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
variable {G : Type} [Group G] [Group.IsNilpotent G]

theorem finitelyGenerated_torsion_nilpotent_finite [Group.FG G]
    (ht : ∀ g : G, IsOfFinOrder g) : Finite G := by
  obtain ⟨U, hU, htf⟩ :=
    (isPolycyclic_of_finitelyGenerated_nilpotent G).exists_torsionFree_finiteIndex
  have hone (g : U) : g = 1 := by
    obtain ⟨n, hn, hg⟩ := (ht g).exists_pow_eq_one
    exact htf g n (Nat.ne_of_gt hn) (Subtype.ext hg)
  let : Subsingleton U := ⟨fun a b => (hone a).trans (hone b).symm⟩
  exact (Subgroup.finite_iff_finite_and_finiteIndex U).mpr ⟨inferInstance, hU⟩

theorem nilpotentTorsionSubgroup_locallyFinite
    (H : Subgroup (nilpotentTorsionSubgroup (G := G))) (hH : H.FG) : Finite H := by
  let : Group.FG H := (Group.fg_iff_subgroup_fg _).mpr hH
  apply finitelyGenerated_torsion_nilpotent_finite
  intro g
  obtain ⟨n, hn, hg⟩ := g.val.property.exists_pow_eq_one
  exact isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn, Subtype.ext (Subtype.ext hg)⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_LocallyNilpotentTorsion
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.instPreservesMonomorphismsRepRatQuotientSubgroupQuotientToCoinvariantsFunctorOfFiniteSubtypeMem_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The finite torsion kernel of a locally nilpotent group with bounded torsion -/
noncomputable section
namespace PolycyclicRecognition
variable {G : Type} [Group G]

theorem locallyNilpotent_subgroup (hlocal : ∀ H : Subgroup G, H.FG → Group.IsNilpotent H)
    (K : Subgroup G) (H : Subgroup K) (hH : H.FG) : Group.IsNilpotent H := by
  let := hlocal (H.map K.subtype) (fg_subgroup_map hH K.subtype)
  exact Group.nilpotent_of_mulEquiv (H.equivMapOfInjective K.subtype Subtype.val_injective).symm

variable (hlocal : ∀ H : Subgroup G, H.FG → Group.IsNilpotent H)

theorem locallyNilpotentTorsionSubgroup_locallyFinite
    (H : Subgroup (locallyNilpotentTorsionSubgroup hlocal)) (hH : H.FG) : Finite H := by
  let : Group.FG H := (Group.fg_iff_subgroup_fg _).mpr hH
  let := locallyNilpotent_subgroup hlocal _ H hH
  apply finitelyGenerated_torsion_nilpotent_finite
  intro g
  obtain ⟨n, hn, he⟩ := g.val.property.exists_pow_eq_one
  exact isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn, Subtype.ext (Subtype.ext he)⟩

theorem locallyNilpotentTorsionSubgroup_finite (hb : HasBoundedFiniteSubgroupOrders G) :
    Finite (locallyNilpotentTorsionSubgroup hlocal) :=
  finite_locallyFinite_normal_subgroup _
    (locallyNilpotentTorsionSubgroup_locallyFinite hlocal) hb

theorem locallyNilpotentTorsionQuotient_torsionFree :
    HasNoNontrivialTorsion (G ⧸ locallyNilpotentTorsionSubgroup hlocal) := by
  intro a n hn ha
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (locallyNilpotentTorsionSubgroup hlocal) a
  apply (QuotientGroup.eq_one_iff g).mpr
  have hg : g ^ n ∈ locallyNilpotentTorsionSubgroup hlocal :=
    (QuotientGroup.eq_one_iff _).mp (by
      change (QuotientGroup.mk' (locallyNilpotentTorsionSubgroup hlocal)) (g ^ n) = 1
      rw [map_pow]
      exact ha)
  obtain ⟨m, hm, he⟩ := hg.exists_pow_eq_one
  exact isOfFinOrder_iff_pow_eq_one.mpr
    ⟨n * m, Nat.mul_pos (Nat.pos_of_ne_zero hn) hm, by simpa only [pow_mul] using he⟩

include hlocal in
theorem locallyNilpotent_quotient {Q : Type} [Group Q]
    (q : G →* Q) (hq : Function.Surjective q) (K : Subgroup Q) (hK : K.FG) :
    Group.IsNilpotent K := by
  let P := K.comap q
  let p : P →* K := (q.comp P.subtype).codRestrict K (fun x => x.property)
  have hp : Function.Surjective p := by
    intro k
    obtain ⟨g, hg⟩ := hq k
    exact ⟨⟨g, by change q g ∈ K; rw [hg]; exact k.property⟩, Subtype.ext hg⟩
  let : Group.FG K := (Group.fg_iff_subgroup_fg K).mpr hK
  obtain ⟨H, hH, hs⟩ := exists_fg_subgroup_surjective p hp
  let := locallyNilpotent_subgroup hlocal P H hH
  exact Group.nilpotent_of_surjective (p.comp H.subtype) hs

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_LocallyNilpotentRationalEndgame
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.cyclicTopHomologyInjection_mono _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite torsion removal from the locally nilpotent rational-dimension step -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
variable {G : Type} [Group G] [Countable G]

theorem locallyNilpotent_mod_finite_torsion (d : ℕ)
    (hd : HasProjectiveDimensionLE (Rep.trivial ℚ G ℚ) d)
    (hb : HasBoundedFiniteSubgroupOrders G)
    (hlocal : ∀ H : Subgroup G, H.FG → Group.IsNilpotent H) :
    let T := locallyNilpotentTorsionSubgroup hlocal
    Finite T ∧ Group.IsNilpotent (G ⧸ T) ∧
      HasProjectiveDimensionLE (trivialIntegral (G ⧸ T)) (d + 1) := by
  let T := locallyNilpotentTorsionSubgroup hlocal
  let : Finite T := locallyNilpotentTorsionSubgroup_finite hlocal hb
  let : Countable (G ⧸ T) := Function.Surjective.countable (QuotientGroup.mk'_surjective T)
  have hQ := RationalQuotient.rational_dimension_quotient T d hd
  have hr := rationalHomologyDimension_of_rational_representation d hQ
  have ht := locallyNilpotentTorsionQuotient_torsionFree hlocal
  have hl : ∀ K : Subgroup (G ⧸ T), K.FG → Group.IsNilpotent K :=
    locallyNilpotent_quotient hlocal (QuotientGroup.mk' T) (QuotientGroup.mk'_surjective T)
  exact ⟨inferInstance, hr.locallyNilpotent_isNilpotent ht hl,
    hr.locallyNilpotent_integralDimension ht hl⟩


end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_PolynomialMatrixScalarExtension
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.instPreservesMonomorphismsRepRatQuotientSubgroupQuotientToCoinvariantsFunctorOfFiniteSubtypeMem_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
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
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.instPreservesMonomorphismsRepRatQuotientSubgroupQuotientToCoinvariantsFunctorOfFiniteSubtypeMem_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
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
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.instPreservesMonomorphismsRepRatQuotientSubgroupQuotientToCoinvariantsFunctorOfFiniteSubtypeMem_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
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
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.instPreservesMonomorphismsRepRatQuotientSubgroupQuotientToCoinvariantsFunctorOfFiniteSubtypeMem_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_NilpotentFiniteTailBound
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instNonemptyBases _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.instPreservesMonomorphismsRepRatQuotientSubgroupQuotientToCoinvariantsFunctorOfFiniteSubtypeMem_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Compatibility with OpenAI's Mathlib (d13f23b): a lemma it has and ours lacks. -/

private theorem Subgroup.card_lt_of_lt_p1 {G : Type*} [Group G] {H K : Subgroup G} [Finite K] (h : H < K) :
    Nat.card H < Nat.card K :=
  (Set.toFinite _).card_lt_card h

namespace OAI

/-! # A finite tail in a nilpotent lower central series has bounded length -/
noncomputable section
namespace PolycyclicRecognition
variable {G : Type} [Group G] [Group.IsNilpotent G]

theorem lowerCentralSeries_succ_lt_of_ne_bot (n : ℕ)
    (hn : (⊤ : Subgroup G).lowerCentralSeries n ≠ ⊥) :
    (⊤ : Subgroup G).lowerCentralSeries (n + 1) < (⊤ : Subgroup G).lowerCentralSeries n := by
  refine lt_of_le_of_ne ((⊤ : Subgroup G).lowerCentralSeries_antitone (Nat.le_succ n)) ?_
  intro he
  have hsame (k : ℕ) : (⊤ : Subgroup G).lowerCentralSeries (n + k) =
      (⊤ : Subgroup G).lowerCentralSeries n := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Nat.add_succ, Subgroup.lowerCentralSeries_succ, ih]
      exact he
  apply hn
  rw [← hsame (Group.nilpotencyClass G)]
  apply eq_bot_iff.mpr
  exact ((⊤ : Subgroup G).lowerCentralSeries_antitone
    (Nat.le_add_left (Group.nilpotencyClass G) n)).trans_eq
    Subgroup.lowerCentralSeries_nilpotencyClass

theorem lowerCentralSeries_eq_bot_of_finite_tail (T : Subgroup G) [Finite T]
    (n : ℕ) (hn : (⊤ : Subgroup G).lowerCentralSeries n ≤ T) :
    (⊤ : Subgroup G).lowerCentralSeries (n + Nat.card T) = ⊥ := by
  let L (k : ℕ) := (⊤ : Subgroup G).lowerCentralSeries (n + k)
  have hLT (k : ℕ) : L k ≤ T :=
    ((⊤ : Subgroup G).lowerCentralSeries_antitone (Nat.le_add_right n k)).trans hn
  let (k : ℕ) : Finite (L k) := Finite.of_injective (Subgroup.inclusion (hLT k))
    (Subgroup.inclusion_injective _)
  have hb (k : ℕ) (hk : L k ≠ ⊥) : Nat.card (L k) + k ≤ Nat.card T := by
    induction k with
    | zero => simpa only [add_zero] using Subgroup.card_le_of_le (hLT 0)
    | succ k ih =>
      have hk' : L k ≠ ⊥ := by
        intro he
        apply hk
        apply eq_bot_iff.mpr
        exact ((⊤ : Subgroup G).lowerCentralSeries_antitone (by omega)).trans_eq he
      have hi := ih hk'
      have hs : Nat.card (L (k + 1)) < Nat.card (L k) :=
        Subgroup.card_lt_of_lt_p1 (lowerCentralSeries_succ_lt_of_ne_bot (n + k) hk')
      omega
  by_contra h
  have hbound := hb (Nat.card T) h
  have hp : 0 < Nat.card (L (Nat.card T)) := Nat.card_pos
  omega

theorem nilpotencyClass_le_quotient_add_finite_kernel (T : Subgroup G) [T.Normal] [Finite T] :
    Group.nilpotencyClass G ≤ Group.nilpotencyClass (G ⧸ T) + Nat.card T := by
  apply Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mp
  apply lowerCentralSeries_eq_bot_of_finite_tail T
  have hm : ((⊤ : Subgroup G).lowerCentralSeries (Group.nilpotencyClass (G ⧸ T))).map
      (QuotientGroup.mk' T) = ⊥ := by
    rw [Subgroup.map_lowerCentralSeries, ← MonoidHom.range_eq_map, QuotientGroup.range_mk']
    exact Subgroup.lowerCentralSeries_nilpotencyClass
  simpa only [QuotientGroup.ker_mk'] using (Subgroup.map_eq_bot_iff _).mp hm

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_RationalNilpotentClassBound
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.cyclicTopHomologyInjection_mono _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A nilpotency-class bound allowing finite torsion -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
variable {G : Type} [Group G] [Countable G]

theorem rational_nilpotencyClass_le [Group.IsNilpotent G] (d b : ℕ)
    (hd : HasProjectiveDimensionLE (Rep.trivial ℚ G ℚ) d)
    (hb : ∀ T : Subgroup G, Finite T → Nat.card T ≤ b) :
    Group.nilpotencyClass G ≤ 2 * (d + 1) + b := by
  let hlocal : ∀ H : Subgroup G, H.FG → Group.IsNilpotent H := fun _ _ => inferInstance
  let T := locallyNilpotentTorsionSubgroup hlocal
  obtain ⟨hTf, hQ, hQd⟩ := locallyNilpotent_mod_finite_torsion d hd ⟨b, hb⟩ hlocal
  let : Finite T := hTf
  let : Group.IsNilpotent (G ⧸ T) := hQ
  let : HasProjectiveDimensionLE (trivialIntegral (G ⧸ T)) (d + 1) := hQd
  exact (nilpotencyClass_le_quotient_add_finite_kernel T).trans
    (Nat.add_le_add (nilpotencyClass_le_twice_cohomologicalDimension (d + 1)) (hb T inferInstance))

theorem exists_maximal_nilpotent_normal_of_rational_dimension (d : ℕ)
    (hd : HasProjectiveDimensionLE (Rep.trivial ℚ G ℚ) d)
    (hb : HasBoundedFiniteSubgroupOrders G) :
    ∃ F : Subgroup G, F.Normal ∧ Group.IsNilpotent F ∧
      ∀ N : Subgroup G, N.Normal → Group.IsNilpotent N → F ≤ N → N = F := by
  obtain ⟨b, hb⟩ := hb
  have hclass (N : Subgroup G) [Group.IsNilpotent N] :
      Group.nilpotencyClass N ≤ 2 * (d + 1) + b := by
    apply rational_nilpotencyClass_le d b (RationalQuotient.rational_dimension_subgroup N d hd)
    intro T hT
    let := hT
    let e := T.equivMapOfInjective N.subtype Subtype.val_injective
    let : Finite (T.map N.subtype) := Finite.of_equiv T e.toEquiv
    simpa only [Nat.card_congr e.toEquiv] using hb (T.map N.subtype) inferInstance
  let P : Set (Subgroup G) := {N | N.Normal ∧ Group.IsNilpotent N}
  obtain ⟨F, hF, hmax⟩ := zorn_le₀ P (by
    intro C hC hchain
    rcases C.eq_empty_or_nonempty with rfl | hne
    · exact ⟨⊥, ⟨inferInstance, inferInstance⟩, by simp⟩
    · have hn : (sSup C).Normal := Subgroup.sSup_normal C (fun N hN => (hC hN).1)
      have hnil : Group.IsNilpotent (sSup C : Subgroup G) := by
        apply (Subgroup.isNilpotent_iff_lowerCentralSeries (sSup C)).mpr
        refine ⟨2 * (d + 1) + b, sSup_lowerCentralSeries_eq_bot C hne hchain.directedOn _ ?_⟩
        intro N hN
        let := (hC hN).2
        exact Subgroup.lowerCentralSeries_eq_bot_of_nilpotencyClass_le (hclass N)
      exact ⟨sSup C, ⟨hn, hnil⟩, fun N hN => le_sSup hN⟩)
  exact ⟨F, hF.1, hF.2, fun N hn hnil hFN => le_antisymm (hmax ⟨hn, hnil⟩ hFN) hFN⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Lattices_IntegralLatticePowerIndex
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.instPreservesMonomorphismsRepRatQuotientSubgroupQuotientToCoinvariantsFunctorOfFiniteSubtypeMem_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.latticeNormalFlag_normal _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite-index powers in an integral vector lattice -/

noncomputable section
namespace PolycyclicRecognition

theorem latticePowerHom_injective (n : ℕ) {m : ℕ} (hm : 0 < m) :
    Function.Injective (latticePowerHom n m) := by
  intro z w h
  apply Multiplicative.ext
  funext i
  have hi := congrArg (fun a : IntegralLatticeGroup n => a.toAdd i) h
  change (m : ℤ) * z.toAdd i = (m : ℤ) * w.toAdd i at hi
  exact mul_left_cancel₀ (by exact_mod_cast Nat.ne_of_gt hm) hi

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_RationalNilpotentRank
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.instPreservesMonomorphismsRepRatQuotientSubgroupQuotientToCoinvariantsFunctorOfFiniteSubtypeMem_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.cyclicTopHomologyInjection_mono _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.latticeNormalFlag_normal _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Nilpotent rational rank from a homology bound

Finite-index torsion-free subgroups of finitely generated nilpotent groups
have a top orientation class. Detecting this class after rationalization
bounds every lattice quotient. Lifting finite independent families then
bounds abelian quotients of arbitrary nilpotent groups, including torsion.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
variable {G : Type} [Group G] [Group.IsNilpotent G]

theorem finitelyGenerated_nilpotent_lattice_quotient_rank_le_of_rational_bound
    [Group.FG G] {d : ℕ} (hd : RationalHomologyDimensionLE G d)
    (n : ℕ) (q : G →* IntegralLatticeGroup n) (hq : Function.Surjective q) : n ≤ d := by
  obtain ⟨U, hU, htf⟩ :=
    (isPolycyclic_of_finitelyGenerated_nilpotent G).exists_torsionFree_finiteIndex
  let := hU
  let : Group.FG U := inferInstance
  obtain ⟨m, hm⟩ := nilpotent_poincareDuality_of_finitelyGenerated_torsionFree htf
  have hmd : m ≤ d := hm.dimension_le_of_rational_homology_bound (hd.subgroup U)
  let := hm.cohomologicalDimension
  let P := U.map q
  let : P.FiniteIndex := Subgroup.FiniteIndex.map_of_surjective U hq
  let qU : U →* P := (q.comp U.subtype).codRestrict P (fun u => ⟨u, u.property, rfl⟩)
  have hqU : Function.Surjective qU := by
    rintro ⟨a, u, hu, rfl⟩
    exact ⟨⟨u, hu⟩, rfl⟩
  let : Group.FG P := Group.fg_of_surjective hqU
  have htfP : HasNoNontrivialTorsion P :=
    ((integralLattice_poincareDuality n).finiteCohomologicalDimension _).torsionFree.of_injective
      P.subtype Subtype.val_injective
  obtain ⟨r, ⟨e⟩⟩ := exists_integralLattice_equiv htfP
  have hrm : r ≤ m := (isPolycyclic_of_finitelyGenerated_nilpotent U).lattice_quotient_rank_le
    m r (e.symm.toMonoidHom.comp qU) (e.symm.surjective.comp hqU)
  let := (integralLattice_poincareDuality r).of_equiv e |>.cohomologicalDimension
  let f : IntegralLatticeGroup n →* P :=
    (latticePowerHom n P.index).codRestrict P (fun a => P.pow_index_mem a)
  have hf : Function.Injective f := by
    intro a b h
    exact latticePowerHom_injective n (Nat.pos_of_ne_zero (Subgroup.FiniteIndex.index_ne_zero (H := P)))
      (congrArg Subtype.val h)
  exact (lattice_rank_le_cohomologicalDimension r n f hf).trans (hrm.trans hmd)

theorem nilpotent_abelian_quotient_lattice_rank_le_of_rational_bound
    {A : Type} [CommGroup A] {d : ℕ} (hd : RationalHomologyDimensionLE G d)
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
  exact finitelyGenerated_nilpotent_lattice_quotient_rank_le_of_rational_bound
    ((hd.subgroup P).subgroup H) n
    (e.symm.toMonoidHom.comp (qP.comp H.subtype)) (e.symm.surjective.comp hsurj)

theorem nilpotent_abelian_quotient_rank_le_of_rational_bound
    {A : Type} [CommGroup A] {d : ℕ} (hd : RationalHomologyDimensionLE G d)
    (q : G →* A) (hq : Function.Surjective q) : Module.rank ℤ (Additive A) ≤ d := by
  by_contra h
  have hlt : (d : Cardinal) < Module.rank ℤ (Additive A) := lt_of_not_ge h
  have hle : ((d + 1 : ℕ) : Cardinal) ≤ Module.rank ℤ (Additive A) := by
    rw [Nat.cast_add, Nat.cast_one]
    exact Cardinal.natCast_add_one_le_iff.mpr hlt
  obtain ⟨b, hb⟩ := exists_linearIndependent_of_le_rank hle
  have hn := nilpotent_abelian_quotient_lattice_rank_le_of_rational_bound hd q hq (d + 1)
    (independentLatticeHom b) (independentLatticeHom_injective hb)
  omega

theorem nilpotent_rational_abelianization_finite_of_homology_bound
    {d : ℕ} (hd : RationalHomologyDimensionLE G d) :
    Module.Finite ℚ (RationalAbelianSpace (Abelianization G)) := by
  apply Module.rank_lt_aleph0_iff.mp
  rw [rationalAbelianSpace_rank]
  exact (nilpotent_abelian_quotient_rank_le_of_rational_bound hd
    (Abelianization.of (G := G)) (QuotientGroup.mk'_surjective (commutator G))).trans_lt
      Cardinal.natCast_lt_aleph0

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_VirtualSolvableDimension
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.instPreservesMonomorphismsRepRatQuotientSubgroupQuotientToCoinvariantsFunctorOfFiniteSubtypeMem_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.cyclicTopHomologyInjection_mono _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
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

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_RationalSolvableDimension
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.cyclicTopHomologyInjection_mono _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

namespace OAI

/-! # Finite virtual integral dimension modulo the finite normal radical

The nilpotent radical is selected using rational dimension and the bound on
finite subgroup orders. No integral dimension of the ambient group is assumed.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
open scoped IsMulCommutative
variable {G : Type} [Group G] [Group.FG G] [Group.IsSolvable G]

omit [Group.FG G] [Group.IsSolvable G] in
theorem nilpotent_normal_torsionFree_of_no_finite_normal
    (hb : HasBoundedFiniteSubgroupOrders G)
    (hfinite : ∀ T : Subgroup G, T.Normal → Finite T → T = ⊥)
    (F : Subgroup G) [F.Normal] [Group.IsNilpotent F] :
    HasNoNontrivialTorsion F := by
  let T := nilpotentTorsionSubgroup (G := F)
  let : Finite T := finite_locallyFinite_normal_subgroup T
    nilpotentTorsionSubgroup_locallyFinite (hb.subgroup F)
  let e := T.equivMapOfInjective F.subtype Subtype.val_injective
  let : Finite (normalNilpotentTorsionSubgroup F) := Finite.of_equiv T e.toEquiv
  have hD := hfinite (normalNilpotentTorsionSubgroup F) inferInstance inferInstance
  intro x n hn hx
  have hxt : x ∈ T := isOfFinOrder_iff_pow_eq_one.mpr
    ⟨n, Nat.pos_of_ne_zero hn, hx⟩
  have hxD : (x : G) ∈ normalNilpotentTorsionSubgroup F := ⟨x, hxt, rfl⟩
  rw [hD] at hxD
  exact Subtype.ext hxD

theorem solvable_rational_virtual_finite_dimension_of_no_finite_normal
    (d : ℕ) (hd : HasProjectiveDimensionLE (Rep.trivial ℚ G ℚ) d)
    (hb : HasBoundedFiniteSubgroupOrders G)
    (hfinite : ∀ T : Subgroup G, T.Normal → Finite T → T = ⊥) :
    ∃ V : Subgroup G, V.FiniteIndex ∧ Group.IsSolvable V ∧
      HasFiniteIntegralCohomologicalDimension V := by
  let : Countable G := countable_of_group_fg G
  obtain ⟨F, hFn, hF, hmax⟩ :=
    exists_maximal_nilpotent_normal_of_rational_dimension d hd hb
  let := hFn
  let := hF
  have htf := nilpotent_normal_torsionFree_of_no_finite_normal hb hfinite F
  have hFdim : HasFiniteIntegralCohomologicalDimension F :=
    ⟨d + 1, (rationalHomologyDimension_of_rational_representation d
      (RationalQuotient.rational_dimension_subgroup F d hd)).locallyNilpotent_integralDimension
      htf (fun _ _ => inferInstance)⟩
  obtain ⟨H, hHn, hHi, hcomm⟩ :=
    exists_finiteIndex_commutator_le_maximal_nilpotent F hFdim hmax
  let := hHn
  let := hHi
  let N := commutator H
  let f : N →* F := (H.subtype.comp N.subtype).codRestrict F
    (fun x => hcomm ⟨x, x.property, rfl⟩)
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : F => (z : G)) hxy
  let : Group.IsNilpotent N := nilpotent_of_injective_hom f hf
  let : Module.Finite ℚ (RationalAbelianSpace (Abelianization N)) :=
    nilpotent_rational_abelianization_finite_of_homology_bound
      (((rationalHomologyDimension_of_rational_representation d hd).subgroup H).subgroup N)
  -- `H ⧸ commutator H` is `Abelianization H` by definition; ours has no instance on the quotient
  have : IsMulCommutative (H ⧸ N) :=
    ⟨⟨fun a b => (inferInstance : CommGroup (Abelianization H)).mul_comm a b⟩⟩
  exact exists_solvable_finiteDimension_of_finiteIndex H
    (nilpotent_abelianization_virtual_finite_dimension N (htf.of_injective f hf))

theorem solvable_rational_mod_finite_radical_dimension
    (d : ℕ) (hd : HasProjectiveDimensionLE (Rep.trivial ℚ G ℚ) d)
    (hb : HasBoundedFiniteSubgroupOrders G) :
    ∃ T : Subgroup G, ∃ hT : T.Normal, letI := hT
      Finite T ∧ (∃ V : Subgroup (G ⧸ T), V.FiniteIndex ∧ Group.IsSolvable V ∧
        HasFiniteIntegralCohomologicalDimension V) := by
  obtain ⟨T, hTc, hTf, hmax⟩ := exists_largest_finite_normal hb
  let := hTc
  let := hTf
  have hq : HasBoundedFiniteSubgroupOrders (G ⧸ T) := by
    let : Finite (QuotientGroup.mk' T).ker := by
      simpa only [QuotientGroup.ker_mk'] using hTf
    exact boundedFiniteSubgroupOrders_of_finite_kernel_quotient
      (QuotientGroup.mk' T) (QuotientGroup.mk'_surjective T) hb
  refine ⟨T, inferInstance, hTf, ?_⟩
  apply solvable_rational_virtual_finite_dimension_of_no_finite_normal d
    (RationalQuotient.rational_dimension_quotient T d hd) hq
  intro S hn hs
  let := hn
  let := hs
  exact finite_normal_quotient_eq_bot T hmax S

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_SolvableFiniteExtension
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.instPreservesMonomorphismsRepRatQuotientSubgroupQuotientToCoinvariantsFunctorOfFiniteSubtypeMem_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_SolvablePoincareFiniteness
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.instPreservesMonomorphismsRepRatQuotientSubgroupQuotientToCoinvariantsFunctorOfFiniteSubtypeMem_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
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

theorem IsIntegralPoincareDualityGroup.polycyclic {n : ℕ}
    (hG : IsIntegralPoincareDualityGroup G n) : IsPolycyclic G := by
  obtain ⟨H, hHn, hHi, N, hNn, hNnil, hQ⟩ :=
    exists_finiteIndex_nilpotent_by_abelian (hG.finiteCohomologicalDimension G)
  let := hHn
  let := hHi
  let := hNn
  let := hNnil
  let := hQ
  have hH := polycyclic_of_nilpotent_by_abelian_duality N (hG.finiteIndex_subgroup H)
  exact (show IsVirtuallyPolycyclic G from ⟨H, hHi, hH⟩).polycyclic_of_solvable

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_VirtualPolycyclicDuality
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.instPreservesMonomorphismsRepRatQuotientSubgroupQuotientToCoinvariantsFunctorOfFiniteSubtypeMem_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A proved duality comparison for virtually polycyclic groups

The polycyclic comparison group's duality follows from a finite-index poly-Z
series and the cyclic-extension resolution. The recognition consequence is
conditional on the four finiteness and transfer inputs.
-/

namespace PolycyclicRecognition

theorem exists_coarse_poincareDuality_comparison_proved
    (P H : Type) [Group P] [Group H] [Group.FG P]
    (hP : IsVirtuallyPolycyclic P) (e : GroupCoarseEquivalence P H) :
    ∃ (K : Subgroup P) (Γ : Subgroup K),
      K.FiniteIndex ∧ Γ.FiniteIndex ∧ Group.FG Γ ∧
      Nonempty (GroupCoarseEquivalence Γ H) ∧
      ∃ n : ℕ, IsIntegralPoincareDualityGroup Γ n := by
  obtain ⟨K, hKindex, hKpoly⟩ := hP
  let := hKindex
  obtain ⟨Γ, hΓindex, n, hΓPD⟩ := hKpoly.exists_poincareDuality_finiteIndex
  let := hΓindex
  exact ⟨K, Γ, hKindex, hΓindex, inferInstance,
    ⟨(finiteIndexCoarseEquivalence Γ).trans ((finiteIndexCoarseEquivalence K).trans e)⟩,
    n, hΓPD⟩

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_RationalRecognitionEndgame
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Recognition from virtual solvability and the proved rational bounds

A finite normal subgroup is removed before duality transfer. Polycyclicity
then lifts across that finite kernel. No virtual integral dimension of the
original group is assumed in this argument.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
variable {P G : Type} [Group P] [Group G] [Group.FG P] [Group.FG G]

theorem virtuallyPolycyclic_of_coarse_rational_bounds_oai
    (e : GroupCoarseEquivalence P G) (hP : IsVirtuallyPolycyclic P)
    (d : ℕ) (hd : HasProjectiveDimensionLE (Rep.trivial ℚ G ℚ) d)
    (hb : HasBoundedFiniteSubgroupOrders G)
    (hs : ∃ H : Subgroup G, H.FiniteIndex ∧ Group.IsSolvable H) :
    IsVirtuallyPolycyclic G := by
  obtain ⟨H, hHi, hHs⟩ := hs
  let := hHi
  let := hHs
  obtain ⟨T, hTn, hTf, V, hVi, hVs, hVdim⟩ :=
    solvable_rational_mod_finite_radical_dimension d
      (RationalQuotient.rational_dimension_subgroup H d hd) (hb.subgroup H)
  let := hTn
  let := hTf
  let := hVi
  let := hVs
  let : Finite (QuotientGroup.mk' T).ker := by
    simpa only [QuotientGroup.ker_mk'] using hTf
  let eQ : GroupCoarseEquivalence P (H ⧸ T) :=
    (e.trans (finiteIndexCoarseEquivalence H).symm).trans
      (finiteKernelCoarseEquivalence (QuotientGroup.mk' T) (QuotientGroup.mk'_surjective T))
  obtain ⟨K, Γ, _, _, hΓfg, ⟨eΓ⟩, n, hΓPD⟩ :=
    exists_coarse_poincareDuality_comparison_proved P (H ⧸ T) hP eQ
  let := hΓfg
  have hVPD := liDualityInput Γ V (eΓ.trans (finiteIndexCoarseEquivalence V).symm)
    (hΓPD.finiteCohomologicalDimension Γ) hVdim n hΓPD
  have hQ : IsPolycyclic (H ⧸ T) :=
    (show IsVirtuallyPolycyclic (H ⧸ T) from
      ⟨V, hVi, hVPD.polycyclic⟩).polycyclic_of_solvable
  exact ⟨H, hHi, isPolycyclic_of_normal_subgroup T isPolycyclic_of_finite_solvable hQ⟩

end PolycyclicRecognition

end

end OAI
end

theorem solution : type_of% @OAI.PolycyclicRecognition.virtuallyPolycyclic_of_coarse_rational_bounds_oai := @OAI.PolycyclicRecognition.virtuallyPolycyclic_of_coarse_rational_bounds_oai
