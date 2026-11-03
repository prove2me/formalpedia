-- Prove2me | solution 1 for OAI.PolycyclicRecognition.nilpotent_by_abelian_uniform_lattice
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-03T01:04:35.147794+00:00
-- url     : https://prove2.me/submissions/11bc0f60-5e75-4a8c-9343-c32cdc734996

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_PolycyclicRecognition
import Definitions.Def_OAIQ093D022
import Definitions.Def_OAIQ093D024

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

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_ActionDepth
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
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

theorem mul (hf : ActionDepth D k f) (hg : ActionDepth D l g) :
    ActionDepth D (k + l) (f * g) := by
  intro n v hv
  simpa only [Module.End.mul_apply, Nat.add_assoc, Nat.add_comm l k] using hf (n + l) (g v) (hg n v hv)

theorem generator (i : I) : ActionDepth D 1 (D i) := by
  intro n v hv
  exact (le_iSup (fun j => (linearActionFiltration D n).map (D j)) i) ⟨v, hv, rfl⟩

end ActionDepth

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

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_FilteredBijection
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Inverting a map whose error raises a finite filtration

The fixed-point correction terminates after the filtration length. This
gives a concrete inverse for triangular polynomial translations.
-/

noncomputable section
namespace PolycyclicRecognition

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

theorem bijective_of_raises_difference_filtration
    (F : ℕ → Submodule ℝ V) (hF0 : F 0 = ⊤) {c : ℕ} (hFc : F c = ⊥)
    (f : V → V)
    (hraise : ∀ k x y, x - y ∈ F k → (f x - f y) - (x - y) ∈ F (k + 1)) :
    Function.Bijective f :=
  ⟨injective_of_raises_difference_filtration F hF0 hFc f hraise,
    fun y => ⟨filteredNewton f y c, filteredNewton_right_inverse F hF0 hFc f hraise y⟩⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_PolynomialCommutingProduct
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.JointFixedReductionData.residualLayer_normal _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.abelianRealCoordinates _root_.OAI.PolycyclicRecognition.abelianRealFiniteDimensional _root_.OAI.PolycyclicRecognition.abelianRealLieAbelian _root_.OAI.PolycyclicRecognition.abelianRealNormedLie _root_.OAI.PolycyclicRecognition.derivationLieSpaceFiniteDimensional _root_.OAI.PolycyclicRecognition.derivationLieSpaceRealNormed _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.polynomialLieIdealSubgroup_normal _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Products of commuting logarithms

The finite BCH law is addition when the two logarithms have zero bracket.
-/

noncomputable section
namespace PolycyclicRecognition
variable {L : Type*} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L]

theorem polynomial_mul_eq_add_of_lie_eq_zero (x y : L) (hxy : ⁅x, y⁆ = 0) :
    x * y = x + y := by
  have hp (i j : Fin 2) : ⁅![x, y] i, ![x, y] j⁆ = 0 := by
    fin_cases i <;> fin_cases j
    · exact lie_self x
    · exact hxy
    · change ⁅y, x⁆ = 0
      rw [← lie_skew, hxy, neg_zero]
    · exact lie_self y
  have hw (d : ℕ) (w : Fin (d + 2) → Fin 2) :
      evalBracketWord ![x, y] (rightNestedWord (d + 1) w) = 0 := by
    induction d with
    | zero => exact hp (w 0) (w 1)
    | succ d ih =>
      change ⁅![x, y] (w 0),
        evalBracketWord ![x, y] (rightNestedWord (d + 1) (fun i => w i.succ))⁆ = 0
      rw [ih, lie_zero]
  have he (d : ℕ) (w : Fin (d + 1) → Fin 2) :
      evalBracketWord ![x, y] (rightNestedWord d w) =
        wordLinearPart (rightNestedWord d w) ![x, y] := by
    cases d with
    | zero => rfl
    | succ d => rw [hw]; rfl
  rw [P.mul_eq]
  have hlin : finiteDynkinPolynomial P.coefficients ![x, y] =
      finiteDynkinLinearPart P.coefficients ![x, y] := by
    simp only [finiteDynkinPolynomial, finiteDynkinLinearPart, LinearMap.sum_apply,
      LinearMap.smul_apply, he]
  rw [hlin, binaryDynkinLinearPart P.coefficients
    PolynomialExponentialCoordinates.axis_normalized]

theorem polynomial_mem_center_of_lie_eq_zero (x : L) (hx : ∀ y : L, ⁅x, y⁆ = 0) :
    x ∈ Subgroup.center L := by
  apply Subgroup.mem_center_iff.mpr
  intro y
  have hyx : ⁅y, x⁆ = 0 := by rw [← lie_skew, hx y, neg_zero]
  rw [polynomial_mul_eq_add_of_lie_eq_zero _ _ (hx y),
    polynomial_mul_eq_add_of_lie_eq_zero _ _ hyx, add_comm]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_SemisimpleKernelProjection
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The canonical fixed-space projection preserves invariant filtrations

For a semisimple operator, its kernel and range are complementary. The
projection to the kernel preserves every invariant subspace, including the
lower central series when the operator is A - 1.
-/

noncomputable section
namespace PolycyclicRecognition
variable {L : Type*} [AddCommGroup L] [Module ℝ L] [FiniteDimensional ℝ L]

theorem semisimpleKernelProjection_commute (B T : Module.End ℝ L)
    (hB : B.IsSemisimple) (hBT : Commute B T) :
    Commute (semisimpleKernelProjection B hB) T := by
  let P := semisimpleKernelProjection B hB
  apply LinearMap.ext
  intro x
  have hp : T (P x) ∈ B.ker := by
    change B (T (P x)) = 0
    have he := LinearMap.congr_fun hBT.eq (P x)
    change B (T (P x)) = T (B (P x)) at he
    rw [he, LinearMap.mem_ker.mp (semisimpleKernelProjection_mem B hB x), map_zero]
  have hq : T (x - P x) ∈ B.range := by
    obtain ⟨y, hy⟩ := Submodule.sub_projection_mem (semisimple_kernel_range_isCompl B hB) x
    refine ⟨T y, ?_⟩
    have he := LinearMap.congr_fun hBT.eq y
    change B (T y) = T (B y) at he
    rw [he, hy]
    rfl
  have hs : x = P x + (x - P x) := by abel
  change P (T x) = T (P x)
  conv_lhs => rw [hs, map_add, map_add]
  have hpp : P (T (P x)) = T (P x) := Submodule.projection_apply_of_mem_left _ hp
  have hpq : P (T (x - P x)) = 0 := Submodule.projection_apply_of_mem_right _ hq
  rw [hpp, hpq, add_zero]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_SemisimpleInnerFixedRepresentative
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.JointFixedReductionData.residualLayer_normal _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.abelianRealCoordinates _root_.OAI.PolycyclicRecognition.abelianRealFiniteDimensional _root_.OAI.PolycyclicRecognition.abelianRealLieAbelian _root_.OAI.PolycyclicRecognition.abelianRealNormedLie _root_.OAI.PolycyclicRecognition.derivationLieSpaceFiniteDimensional _root_.OAI.PolycyclicRecognition.derivationLieSpaceRealNormed _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.polynomialLieIdealSubgroup_normal _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Fixed representatives of inner automorphisms centralizing a semisimple map

An element whose inner action centralizes S differs, by a central element,
from an S-fixed element. The representative is the canonical linear fixed
projection, so it preserves all invariant subspaces as well.
-/

noncomputable section
namespace PolycyclicRecognition
attribute [local instance] LieRing.ofAssociativeRing
variable {L : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [C : PolynomialExponentialCoordinates L] [LieRing.IsNilpotent L]

theorem semisimple_inner_fixed_representative_preserves (S : L ≃ₗ⁅ℝ⁆ L)
    (hS : Module.End.IsSemisimple S.toLinearMap) (x : L)
    (hcomm : Commute S.toLinearMap (polynomialInnerLieEquiv x).toLinearMap) :
    ∃ y : L, S y = y ∧
      (polynomialInnerLieEquiv y).toLinearMap = (polynomialInnerLieEquiv x).toLinearMap ∧
      ∀ T : L ≃ₗ⁅ℝ⁆ L, Commute T.toLinearMap S.toLinearMap → T x = x → T y = y := by
  let s := PolynomialExponentialCoordinates.groupAutomorphism (P := C) S
  have hi : (polynomialInnerLieEquiv (S x)).toLinearMap =
      (polynomialInnerLieEquiv x).toLinearMap := by
    apply LinearMap.ext
    intro z
    have hh : S (polynomialInnerLieEquiv x (S.symm z)) =
        polynomialInnerLieEquiv x (S (S.symm z)) :=
      LinearMap.congr_fun hcomm.eq (S.symm z)
    rw [S.apply_symm_apply, polynomialInnerLieEquiv_apply,
      polynomialInnerLieEquiv_apply] at hh
    have hs : s (x * S.symm z * x⁻¹) = S x * z * (S x)⁻¹ := by
      rw [map_mul, map_mul, map_inv]
      change S x * S (S.symm z) * (S x)⁻¹ = S x * z * (S x)⁻¹
      rw [S.apply_symm_apply]
    change S (x * S.symm z * x⁻¹) = x * z * x⁻¹ at hh
    change s (x * S.symm z * x⁻¹) = x * z * x⁻¹ at hh
    rw [hs] at hh
    change polynomialInnerLieEquiv (S x) z = polynomialInnerLieEquiv x z
    simpa only [polynomialInnerLieEquiv_apply] using hh
  have had := polynomial_inner_eq_implies_ad_eq (S x) x hi
  let Z : Submodule ℝ L := (LieAlgebra.ad ℝ L).ker.toSubmodule
  have hZ (z : L) (hz : z ∈ Z) : S z ∈ Z := by
    change LieAlgebra.ad ℝ L z = 0 at hz
    change LieAlgebra.ad ℝ L (S z) = 0
    apply LinearMap.ext
    intro w
    have hzw : ⁅z, S.symm w⁆ = 0 := LinearMap.congr_fun hz (S.symm w)
    change ⁅S z, w⁆ = 0
    calc
      _ = S ⁅z, S.symm w⁆ := by rw [S.map_lie, S.apply_symm_apply]
      _ = 0 := by rw [hzw, map_zero]
  let B : Module.End ℝ L := S.toLinearMap - 1
  have hB : B.IsSemisimple := semisimple_sub_one S.toLinearMap hS
  let P := semisimpleKernelProjection B hB
  have hx : B x ∈ Z := by
    change LieAlgebra.ad ℝ L (S x - x) = 0
    rw [map_sub, had, sub_self]
  have hd : x - P x ∈ Z := semisimple_sub_projection_mem_of_apply_mem B hB Z
    (fun z hz => Z.sub_mem (hZ z hz) hz) hx
  refine ⟨P x, sub_eq_zero.mp (semisimpleKernelProjection_mem B hB x), ?_, ?_⟩
  · apply polynomial_inner_eq_of_ad_eq
    change LieAlgebra.ad ℝ L (x - P x) = 0 at hd
    rw [map_sub, sub_eq_zero] at hd
    exact hd.symm
  · intro T hTS hTx
    have hPT : Commute P T.toLinearMap := semisimpleKernelProjection_commute B T.toLinearMap hB
      (hTS.symm.sub_left (Commute.one_left _))
    have hh : P (T x) = T (P x) := LinearMap.congr_fun hPT.eq x
    rw [hTx] at hh
    exact hh.symm

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_InnerCentralizerProduct
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.JointFixedReductionData.residualLayer_normal _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.abelianRealCoordinates _root_.OAI.PolycyclicRecognition.abelianRealFiniteDimensional _root_.OAI.PolycyclicRecognition.abelianRealLieAbelian _root_.OAI.PolycyclicRecognition.abelianRealNormedLie _root_.OAI.PolycyclicRecognition.derivationLieSpaceFiniteDimensional _root_.OAI.PolycyclicRecognition.derivationLieSpaceRealNormed _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.polynomialLieIdealSubgroup_normal _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A direct product decomposition of the semisimple inner centralizer

The moving factor is central and the other factor is fixed pointwise. Both
projections preserve the actual polynomial group law.
-/

noncomputable section
namespace PolycyclicRecognition
attribute [local instance] LieRing.ofAssociativeRing polynomialSubalgebraGroup
variable {L : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]

variable [P : PolynomialExponentialCoordinates L]

theorem innerCentralizerMovingProjection_section (S : L ≃ₗ⁅ℝ⁆ L)
    (hS : Module.End.IsSemisimple S.toLinearMap) (x : semisimpleMovingCenter S) :
    innerCentralizerMovingGroupProjection S hS (innerCentralizerMovingInclusion S x) = x := by
  apply Subtype.ext
  change (x : L) - semisimpleOneProjection S.toLinearMap hS x = x
  have hp : semisimpleOneProjection S.toLinearMap hS x = 0 :=
    Submodule.projection_apply_of_mem_right _ x.property.2
  rw [hp, sub_zero]

theorem innerCentralizerMovingProjection_eq_one_iff (S : L ≃ₗ⁅ℝ⁆ L)
    (hS : Module.End.IsSemisimple S.toLinearMap) (x : innerCentralizerLieSubalgebra S) :
    innerCentralizerMovingGroupProjection S hS x = 1 ↔ S x = x := by
  let p := semisimpleOneProjection S.toLinearMap hS
  constructor
  · intro h
    have he : (x : L) - p x = 0 := by
      have hh := congrArg Subtype.val h
      change (x : L) - p x = (1 : L) at hh
      rwa [P.one_eq_zero] at hh
    have hp : S (p x) = p x := sub_eq_zero.mp
      (semisimpleKernelProjection_mem _ (semisimple_sub_one S.toLinearMap hS) x)
    have hx : (x : L) = p x := sub_eq_zero.mp he
    rw [hx, hp]
  · intro hx
    apply Subtype.ext
    have hp : p x = x := Submodule.projection_apply_of_mem_left _ (sub_eq_zero.mpr hx)
    change (x : L) - p x = (1 : L)
    rw [hp, sub_self, P.one_eq_zero]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_LinearConjugationCentralizer
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Commutation through invertible linear factors -/

namespace PolycyclicRecognition
variable {V : Type*} [AddCommGroup V] [Module ℝ V]

theorem linear_commute_conj (e : V ≃ₗ[ℝ] V) (T A : Module.End ℝ V)
    (he : Commute T e.toLinearMap) (hA : Commute T A) : Commute T (e.conjRingEquiv A) := by
  have hh : e.conjRingEquiv A = e.toLinearMap * A * e.symm.toLinearMap := by
    apply LinearMap.ext
    intro x
    rfl
  rw [hh]
  exact (he.mul_right hA).mul_right (linear_commute_symm e T he)

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_SemisimpleMovingAction
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.JointFixedReductionData.residualLayer_normal _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.abelianRealCoordinates _root_.OAI.PolycyclicRecognition.abelianRealFiniteDimensional _root_.OAI.PolycyclicRecognition.abelianRealLieAbelian _root_.OAI.PolycyclicRecognition.abelianRealNormedLie _root_.OAI.PolycyclicRecognition.derivationLieSpaceFiniteDimensional _root_.OAI.PolycyclicRecognition.derivationLieSpaceRealNormed _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.polynomialLieIdealSubgroup_normal _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Equivariance of the centralizer product decomposition -/

noncomputable section
namespace PolycyclicRecognition
attribute [local instance] LieRing.ofAssociativeRing polynomialSubalgebraGroup
variable {L : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]

theorem semisimple_projection_commutes (S T : L ≃ₗ⁅ℝ⁆ L)
    (hS : Module.End.IsSemisimple S.toLinearMap)
    (hST : Commute S.toLinearMap T.toLinearMap) (x : L) :
    semisimpleOneProjection S.toLinearMap hS (T x) =
      T (semisimpleOneProjection S.toLinearMap hS x) :=
  LinearMap.congr_fun (semisimpleKernelProjection_commute (S.toLinearMap - 1) T.toLinearMap
    (semisimple_sub_one S.toLinearMap hS) (hST.sub_left (Commute.one_left _))).eq x

variable [P : PolynomialExponentialCoordinates L]

theorem movingGroupProjection_equivariant (S T : L ≃ₗ⁅ℝ⁆ L)
    (hS : Module.End.IsSemisimple S.toLinearMap)
    (hST : Commute S.toLinearMap T.toLinearMap) (x : innerCentralizerLieSubalgebra S) :
    innerCentralizerMovingGroupProjection S hS (innerCentralizerGroupAction S T hST x) =
      semisimpleMovingGroupAction S T hST (innerCentralizerMovingGroupProjection S hS x) := by
  apply Subtype.ext
  change T x - semisimpleOneProjection S.toLinearMap hS (T x) =
    T ((x : L) - semisimpleOneProjection S.toLinearMap hS x)
  rw [semisimple_projection_commutes S T hS hST, map_sub]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_EquivariantCentralizerSplitting
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Equivariance of the uniquely selected centralizing lifts -/

noncomputable section
namespace PolycyclicRecognition
variable {N G Q : Type*} [Group N] [Group G] [Group Q]

theorem centralizerSplitting_mem (E : GroupExtension N G Q) (t : G)
    (ht : ∀ q : Q, Commute (E.rightHom t) q)
    (hLang : Function.Bijective (extensionLangMap E t)) (q : Q) :
    centralizerSplitting E t ht hLang q ∈ Subgroup.centralizer ({t} : Set G) := by
  let e : Subgroup.centralizer ({t} : Set G) ≃* Q :=
    MulEquiv.ofBijective (centralizerProjection E t)
      ⟨centralizerProjection_injective E t hLang.1,
        centralizerProjection_surjective E t ht hLang.2⟩
  change ((e.symm q : Subgroup.centralizer ({t} : Set G)) : G) ∈ _
  exact (e.symm q).property

theorem centralizerSplitting_fixed (E : GroupExtension N G Q) (t : G)
    (ht : ∀ q : Q, Commute (E.rightHom t) q)
    (hLang : Function.Bijective (extensionLangMap E t))
    (f : G →* G) (hft : f t = t) (hfQ : ∀ g, E.rightHom (f g) = E.rightHom g)
    (q : Q) : f (centralizerSplitting E t ht hLang q) = centralizerSplitting E t ht hLang q := by
  let s := centralizerSplitting E t ht hLang
  have hs : s q ∈ Subgroup.centralizer ({t} : Set G) := centralizerSplitting_mem E t ht hLang q
  have hfs : f (s q) ∈ Subgroup.centralizer ({t} : Set G) := by
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    have hh := congrArg f (Subgroup.mem_centralizer_singleton_iff.mp hs)
    simpa only [map_mul, hft] using hh
  have he := centralizerProjection_injective E t hLang.1
    (a₁ := ⟨f (s q), hfs⟩) (a₂ := ⟨s q, hs⟩) (hfQ (s q))
  exact congrArg Subtype.val he

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_FactorSystemSymmetry
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.JointFixedReductionData.residualLayer_normal _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instLocallyCompactSpaceFactorExtension _root_.OAI.PolycyclicRecognition.instT2SpaceFactorExtension _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Symmetries preserve the canonical projected section -/

noncomputable section
namespace PolycyclicRecognition
variable {K Q : Type*} [Group K] [Group Q]

theorem factorSystem_centralizing_section_fixed
    (R : NonabelianFactorSystem K Q) (q₀ : Q) (hq₀ : ∀ q, Commute q₀ q)
    (hLang : Function.Bijective (fun x : K => x⁻¹ * R.action q₀ x))
    (T : K →* K) (hact : ∀ q x, T (R.action q x) = R.action q (T x))
    (hfactor : ∀ q r, T (R.factor q r) = R.factor q r) (q : Q) :
    let E := FactorExtension.groupExtension R
    let t : FactorExtension R := ⟨1, q₀⟩
    let heq : extensionLangMap E t = fun x : K => x⁻¹ * R.action q₀ x := by
      funext x
      change x⁻¹ * E.conjAct t x = x⁻¹ * R.action q₀ x
      rw [FactorExtension.conjugation_section]
    let s := centralizerSplitting E t hq₀ (heq.symm ▸ hLang)
    T (s q).left = (s q).left := by
  dsimp only
  let E := FactorExtension.groupExtension R
  let t : FactorExtension R := ⟨1, q₀⟩
  have heq : extensionLangMap E t = fun x : K => x⁻¹ * R.action q₀ x := by
    funext x
    change x⁻¹ * E.conjAct t x = x⁻¹ * R.action q₀ x
    rw [FactorExtension.conjugation_section]
  let f := FactorExtension.map R R T hact hfactor
  have hft : f t = t := by
    apply FactorExtension.ext
    · exact T.map_one
    · rfl
  have hh := centralizerSplitting_fixed E t hq₀ (heq.symm ▸ hLang) f hft
    (fun _ => rfl) q
  exact congrArg FactorExtension.left hh

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_EquivariantCocycleReduction
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.JointFixedReductionData.residualLayer_normal _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instLocallyCompactSpaceFactorExtension _root_.OAI.PolycyclicRecognition.instT2SpaceFactorExtension _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A single canonical cocycle correction preserves all compatible symmetries -/

noncomputable section
namespace PolycyclicRecognition
variable {N K Q : Type*} [Group N] [Group K] [Group Q]

theorem factorSystem_cocycle_reduction_equivariant
    (S : NonabelianFactorSystem N Q) (R : NonabelianFactorSystem K Q)
    (p : N →* K) (j : K →* N) (hpj : ∀ x, p (j x) = x)
    (hact : ∀ q x, p (S.action q x) = R.action q (p x))
    (hfactor : ∀ q r, p (S.factor q r) = R.factor q r)
    (q₀ : Q) (hq₀ : ∀ q, Commute q₀ q)
    (hLang : Function.Bijective (fun x : K => x⁻¹ * R.action q₀ x)) :
    ∃ b : Q → N, ∃ hb : b 1 = 1,
      (∀ q r, p ((S.gauge b hb).factor q r) = 1) ∧
      (∀ q, ∃ x, b q = j x) ∧
      ∀ (T : N →* N) (U : K →* K), (∀ x, T (j x) = j (U x)) →
        (∀ q x, U (R.action q x) = R.action q (U x)) →
        (∀ q r, U (R.factor q r) = R.factor q r) → ∀ q, T (b q) = b q := by
  let E := FactorExtension.groupExtension R
  let t : FactorExtension R := ⟨1, q₀⟩
  have heq : extensionLangMap E t = fun x : K => x⁻¹ * R.action q₀ x := by
    funext x
    change x⁻¹ * E.conjAct t x = x⁻¹ * R.action q₀ x
    rw [FactorExtension.conjugation_section]
  let s := centralizerSplitting E t hq₀ (heq.symm ▸ hLang)
  let b : Q → N := fun q => j (s q).left
  have hb : b 1 = 1 := by
    change j (s 1).left = 1
    rw [map_one]
    exact j.map_one
  refine ⟨b, hb, ?_, fun q => ⟨(s q).left, rfl⟩, ?_⟩
  · intro q r
    have hq : (s q).right = q := s.rightInverse_rightHom q
    have hr : (s r).right = r := s.rightInverse_rightHom r
    have hm := congrArg FactorExtension.left (s.map_mul q r)
    change (s (q * r)).left =
      (s q).left * R.action (s q).right (s r).left * R.factor (s q).right (s r).right at hm
    rw [hq, hr] at hm
    change p (b q * S.action q (b r) * S.factor q r * (b (q * r))⁻¹) = 1
    simp only [map_mul, map_inv, hact, hfactor, b, hpj]
    have hs : (s (q * r)).left = (s q * s r).left :=
      congrArg FactorExtension.left (s.map_mul q r)
    rw [← hm, hs, mul_inv_cancel]
  · intro T U hTU hUa hUf q
    change T (j (s q).left) = j (s q).left
    rw [hTU]
    exact congrArg j (factorSystem_centralizing_section_fixed R q₀ hq₀ hLang U hUa hUf q)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_JordanTransversalLinearMap
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The invertible leading term for a general Jordan Lang transversal

Only the moving part of the semisimple operator is inverted. Its commuting
unipotent factor is a nilpotent perturbation of this invertible leading term.
-/

noncomputable section
namespace PolycyclicRecognition
variable {L : Type*} [AddCommGroup L] [Module ℝ L] [FiniteDimensional ℝ L]

theorem jordan_transversal_linear_bijective
    (S U : Module.End ℝ L) (hS : S.IsSemisimple)
    (hU : IsNilpotent (U - 1)) (hSU : Commute S U) :
    let B := S - 1
    let hB := semisimple_sub_one S hS
    let P := semisimpleKernelProjection B hB
    Function.Bijective (((S * U - 1) * (1 - P) + P : Module.End ℝ L) : L → L) := by
  let B := S - 1
  have hB : B.IsSemisimple := semisimple_sub_one S hS
  let P := semisimpleKernelProjection B hB
  let Q : Module.End ℝ L := 1 - P
  let E : Module.End ℝ L := B + P
  let N : Module.End ℝ L := S * (U - 1) * Q
  have hPS : Commute P S := semisimpleKernelProjection_commute B S hB
    ((Commute.refl S).sub_left (Commute.one_left S))
  have hPU : Commute P U := semisimpleKernelProjection_commute B U hB
    (hSU.sub_left (Commute.one_left U))
  have hBP : B * P = 0 := by
    apply LinearMap.ext
    intro x
    exact semisimpleKernelProjection_mem B hB x
  have hSP : S * P = P := by
    have hh : S * P - P = 0 := by simpa only [B, sub_mul, one_mul] using hBP
    exact sub_eq_zero.mp hh
  have hQd : Commute Q (U - 1) :=
    ((Commute.one_left U).sub_left hPU).sub_right (Commute.one_right Q)
  have hQS : Commute Q S := (Commute.one_left S).sub_left hPS
  have hSd : Commute S (U - 1) := hSU.sub_right (Commute.one_right S)
  have hN : IsNilpotent N :=
    (hQS.symm.mul_left hQd.symm).isNilpotent_mul_right
      (hSd.isNilpotent_mul_left hU)
  have hES : Commute E S :=
    ((Commute.refl S).sub_left (Commute.one_left S)).add_left hPS
  have hEU : Commute E U := (hSU.sub_left (Commute.one_left U)).add_left hPU
  have hEP : Commute E P :=
    (hPS.symm.sub_left (Commute.one_left P)).add_left (Commute.refl P)
  have hEN : Commute E N :=
    (hES.mul_right (hEU.sub_right (Commute.one_right E))).mul_right
      ((Commute.one_right E).sub_right hEP)
  have hE : IsUnit E := (Module.End.isUnit_iff E).mpr
    (semisimple_add_kernelProjection_bijective B hB)
  have hsum : (S * U - 1) * Q + P = E + N := by
    dsimp only [E, N, B, Q]
    noncomm_ring [hSP]
  change Function.Bijective (((S * U - 1) * Q + P : Module.End ℝ L) : L → L)
  rw [hsum]
  exact (Module.End.isUnit_iff _).mp (hN.isUnit_add_left_of_commute hE hEN.symm)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_SemisimpleMovingLang
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.JointFixedReductionData.residualLayer_normal _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.abelianRealCoordinates _root_.OAI.PolycyclicRecognition.abelianRealFiniteDimensional _root_.OAI.PolycyclicRecognition.abelianRealLieAbelian _root_.OAI.PolycyclicRecognition.abelianRealNormedLie _root_.OAI.PolycyclicRecognition.derivationLieSpaceFiniteDimensional _root_.OAI.PolycyclicRecognition.derivationLieSpaceRealNormed _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.polynomialLieIdealSubgroup_normal _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bijective Lang maps on the moving central factor

The unipotent factor causes no fixed directions on the range of S-1. The
central group's Lang map is exactly that invertible linear difference.
-/

noncomputable section
namespace PolycyclicRecognition
attribute [local instance] LieRing.ofAssociativeRing polynomialSubalgebraGroup
variable {L : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]

theorem semisimpleMovingDifference_bijective (S U T : L ≃ₗ⁅ℝ⁆ L)
    (hS : Module.End.IsSemisimple S.toLinearMap)
    (hU : IsNilpotent (U.toLinearMap - 1))
    (hSU : Commute S.toLinearMap U.toLinearMap)
    (hST : Commute S.toLinearMap T.toLinearMap)
    (hT : T.toLinearMap = S.toLinearMap * U.toLinearMap) :
    Function.Bijective (semisimpleMovingDifference S T hST) := by
  let p := semisimpleOneProjection S.toLinearMap hS
  let e : Module.End ℝ L := (S.toLinearMap * U.toLinearMap - 1) * (1 - p) + p
  have hb : Function.Bijective e := jordan_transversal_linear_bijective
    S.toLinearMap U.toLinearMap hS hU hSU
  have he (x : semisimpleMovingCenter S) : e x = T x - x := by
    have hp : p x = 0 := Submodule.projection_apply_of_mem_right _ x.property.2
    change S (U ((x : L) - p x)) - ((x : L) - p x) + p x = T x - x
    rw [hp, sub_zero, add_zero]
    have ht : T x = S (U x) := LinearMap.congr_fun hT x
    rw [ht]
  have hi : Function.Injective (semisimpleMovingDifference S T hST) := by
    intro x y h
    apply Subtype.ext
    apply hb.injective
    rw [he, he]
    exact congrArg Subtype.val h
  exact ⟨hi, LinearMap.injective_iff_surjective.mp hi⟩

variable [P : PolynomialExponentialCoordinates L]

theorem semisimpleMoving_lang_eq_difference (S T : L ≃ₗ⁅ℝ⁆ L)
    (hST : Commute S.toLinearMap T.toLinearMap) (x : semisimpleMovingCenter S) :
    x⁻¹ * semisimpleMovingGroupAction S T hST x = semisimpleMovingDifference S T hST x := by
  apply Subtype.ext
  change (x : L)⁻¹ * T x = T x - x
  have hz : ⁅-(x : L), T x⁆ = 0 := by
    rw [neg_lie]
    have hh : ⁅(x : L), T x⁆ = 0 := LinearMap.congr_fun x.property.1 (T x)
    rw [hh, neg_zero]
  rw [P.inv_eq_neg, polynomial_mul_eq_add_of_lie_eq_zero _ _ hz]
  abel

theorem semisimpleMoving_lang_bijective (S U T : L ≃ₗ⁅ℝ⁆ L)
    (hS : Module.End.IsSemisimple S.toLinearMap)
    (hU : IsNilpotent (U.toLinearMap - 1))
    (hSU : Commute S.toLinearMap U.toLinearMap)
    (hST : Commute S.toLinearMap T.toLinearMap)
    (hT : T.toLinearMap = S.toLinearMap * U.toLinearMap) :
    Function.Bijective (fun x : semisimpleMovingCenter S =>
      x⁻¹ * semisimpleMovingGroupAction S T hST x) := by
  have he : (fun x : semisimpleMovingCenter S =>
      x⁻¹ * semisimpleMovingGroupAction S T hST x) = semisimpleMovingDifference S T hST := by
    funext x
    exact semisimpleMoving_lang_eq_difference S T hST x
  rw [he]
  exact semisimpleMovingDifference_bijective S U T hS hU hSU hST hT

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_SemisimpleCocycleReductionPreserving
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.JointFixedReductionData.residualLayer_normal _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.abelianRealCoordinates _root_.OAI.PolycyclicRecognition.abelianRealFiniteDimensional _root_.OAI.PolycyclicRecognition.abelianRealLieAbelian _root_.OAI.PolycyclicRecognition.abelianRealNormedLie _root_.OAI.PolycyclicRecognition.derivationLieSpaceFiniteDimensional _root_.OAI.PolycyclicRecognition.derivationLieSpaceRealNormed _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instLocallyCompactSpaceFactorExtension _root_.OAI.PolycyclicRecognition.instT2SpaceFactorExtension _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.polynomialLieIdealSubgroup_normal _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

namespace OAI

/-! # Moving-central corrections preserve all earlier commuting symmetries -/

noncomputable section
namespace PolycyclicRecognition
open scoped IsMulCommutative
attribute [local instance] LieRing.ofAssociativeRing polynomialSubalgebraGroup
variable {L Q : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L] [Group Q] [IsMulCommutative Q]

theorem semisimple_cocycle_reduction_preserving (S : L ≃ₗ⁅ℝ⁆ L)
    (hS : Module.End.IsSemisimple S.toLinearMap)
    (F : NonabelianFactorSystem (innerCentralizerLieSubalgebra S) Q)
    (A : Q → L ≃ₗ⁅ℝ⁆ L) (hSA : ∀ q, Commute S.toLinearMap (A q).toLinearMap)
    (hact : ∀ q x, (F.action q x : L) = A q x)
    (q₀ : Q) (U : L ≃ₗ⁅ℝ⁆ L) (hU : IsNilpotent (U.toLinearMap - 1))
    (hSU : Commute S.toLinearMap U.toLinearMap)
    (hA : (A q₀).toLinearMap = S.toLinearMap * U.toLinearMap) :
    ∃ b : Q → innerCentralizerLieSubalgebra S, ∃ hb : b 1 = 1,
      (∀ q, LieAlgebra.ad ℝ L (b q : L) = 0) ∧
      (∀ q r, S ((F.gauge b hb).factor q r : L) = ((F.gauge b hb).factor q r : L)) ∧
      ∀ T : L ≃ₗ⁅ℝ⁆ L, Commute S.toLinearMap T.toLinearMap →
        (∀ q, Commute T.toLinearMap (A q).toLinearMap) →
        (∀ q r, T (F.factor q r : L) = (F.factor q r : L)) → ∀ q, T (b q : L) = (b q : L) := by
  let p := innerCentralizerMovingGroupProjection S hS
  let j := innerCentralizerMovingInclusion S
  have hpj : ∀ x, p (j x) = x := innerCentralizerMovingProjection_section S hS
  have hp : Function.Surjective p := fun x => ⟨j x, hpj x⟩
  let a := fun q => semisimpleMovingGroupAction S (A q) (hSA q)
  have ha : ∀ q x, p (F.action q x) = a q (p x) := by
    intro q x
    have hh : F.action q x = innerCentralizerGroupAction S (A q) (hSA q) x :=
      Subtype.ext (hact q x)
    rw [hh]
    exact movingGroupProjection_equivariant S (A q) hS (hSA q) x
  let R := F.mapSurjective p hp a ha
  have hLang : Function.Bijective (fun x => x⁻¹ * R.action q₀ x) :=
    semisimpleMoving_lang_bijective S U (A q₀) hS hU hSU (hSA q₀) hA
  obtain ⟨b, hb, hc, hj, hequiv⟩ := factorSystem_cocycle_reduction_equivariant F R p j hpj ha
    (fun _ _ => rfl) q₀ (fun _ => Commute.all _ _) hLang
  refine ⟨b, hb, ?_, ?_, ?_⟩
  · intro q
    obtain ⟨x, hx⟩ := hj q
    rw [hx]
    exact x.property.1
  · intro q r
    exact (innerCentralizerMovingProjection_eq_one_iff S hS _).mp (hc q r)
  · intro T hST hTA hTf q
    let TN := innerCentralizerGroupAction S T hST
    let TM := semisimpleMovingGroupAction S T hST
    have hTj : ∀ x, TN.toMonoidHom (j x) = j (TM.toMonoidHom x) := by
      intro x
      apply Subtype.ext
      rfl
    have hTa : ∀ r x, TM.toMonoidHom (R.action r x) = R.action r (TM.toMonoidHom x) := by
      intro r x
      apply Subtype.ext
      exact LinearMap.congr_fun (hTA r).eq x
    have hTc : ∀ r s, TM.toMonoidHom (R.factor r s) = R.factor r s := by
      intro r s
      change TM (p (F.factor r s)) = p (F.factor r s)
      rw [← movingGroupProjection_equivariant S T hS hST]
      have hh : TN (F.factor r s) = F.factor r s := Subtype.ext (hTf r s)
      exact congrArg p hh
    exact congrArg Subtype.val (hequiv TN.toMonoidHom TM.toMonoidHom hTj hTa hTc q)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_AmbientSemisimpleCocycleReduction
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.JointFixedReductionData.residualLayer_normal _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.abelianRealCoordinates _root_.OAI.PolycyclicRecognition.abelianRealFiniteDimensional _root_.OAI.PolycyclicRecognition.abelianRealLieAbelian _root_.OAI.PolycyclicRecognition.abelianRealNormedLie _root_.OAI.PolycyclicRecognition.derivationLieSpaceFiniteDimensional _root_.OAI.PolycyclicRecognition.derivationLieSpaceRealNormed _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instLocallyCompactSpaceFactorExtension _root_.OAI.PolycyclicRecognition.instT2SpaceFactorExtension _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.polynomialLieIdealSubgroup_normal _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

namespace OAI

/-! # Central cocycle corrections in ambient exponential coordinates -/

noncomputable section
namespace PolycyclicRecognition
open scoped IsMulCommutative
attribute [local instance] LieRing.ofAssociativeRing polynomialSubalgebraGroup
variable {L Q : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L] [LieRing.IsNilpotent L]
  [Group Q] [IsMulCommutative Q]

theorem ambient_semisimple_cocycle_reduction (F : NonabelianFactorSystem L Q)
    (A : Q → L ≃ₗ⁅ℝ⁆ L) (hact : ∀ q x, F.action q x = A q x)
    (S : L ≃ₗ⁅ℝ⁆ L) (hS : Module.End.IsSemisimple S.toLinearMap)
    (hSA : ∀ q, Commute S.toLinearMap (A q).toLinearMap)
    (q₀ : Q) (U : L ≃ₗ⁅ℝ⁆ L) (hU : IsNilpotent (U.toLinearMap - 1))
    (hSU : Commute S.toLinearMap U.toLinearMap)
    (hA : (A q₀).toLinearMap = S.toLinearMap * U.toLinearMap) :
    ∃ b : Q → L, ∃ hb : b 1 = 1,
      (∀ q, b q ∈ Subgroup.center L) ∧
      (∀ q x, (F.gauge b hb).action q x = F.action q x) ∧
      (∀ q r, S ((F.gauge b hb).factor q r) = (F.gauge b hb).factor q r) ∧
      ∀ T : L ≃ₗ⁅ℝ⁆ L, Commute S.toLinearMap T.toLinearMap →
        (∀ q, Commute T.toLinearMap (A q).toLinearMap) →
        (∀ q r, T (F.factor q r) = F.factor q r) → ∀ q, T (b q) = b q := by
  let R := innerCentralizerFactorSystem F A hact S hSA
  obtain ⟨c, hc, hcZ, hcS, hcT⟩ := semisimple_cocycle_reduction_preserving S hS R A hSA
    (fun _ _ => rfl) q₀ U hU hSU hA
  let b : Q → L := fun q => c q
  have hb : b 1 = 1 := congrArg Subtype.val hc
  have hZ : ∀ q, b q ∈ Subgroup.center L := fun q =>
    polynomial_mem_center_of_lie_eq_zero _ (fun y => LinearMap.congr_fun (hcZ q) y)
  refine ⟨b, hb, hZ, ?_, ?_, ?_⟩
  · intro q x
    change b q * F.action q x * (b q)⁻¹ = F.action q x
    rw [← Subgroup.mem_center_iff.mp (hZ q) (F.action q x)]
    group
  · intro q r
    have he : ((R.gauge c hc).factor q r : L) = (F.gauge b hb).factor q r := by
      change b q * A q (b r) * F.factor q r * (b (q * r))⁻¹ =
        b q * F.action q (b r) * F.factor q r * (b (q * r))⁻¹
      rw [hact]
    rw [← he]
    exact hcS q r
  · intro T hST hTA hTF q
    exact hcT T hST hTA hTF q

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_PolynomialCoordinateOperations
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomiality of the coordinate operations in a finite Lie word -/

noncomputable section
namespace PolycyclicRecognition
namespace IsCoordinatePolynomial
variable {I J S : Type*}

theorem neg {f : (I → ℝ) → (J → ℝ)} (hf : IsCoordinatePolynomial f) :
    IsCoordinatePolynomial (fun x => -f x) := by
  simpa only [neg_one_smul] using hf.smul (-1)

end IsCoordinatePolynomial
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_PolynomialCoordinateSmooth
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Smoothness of the polynomial extensions of lattice maps -/

noncomputable section
namespace PolycyclicRecognition

theorem IsCoordinatePolynomial.contDiff {I J : Type*} [Fintype I] [Fintype J]
    {f : (I → ℝ) → (J → ℝ)} (hf : IsCoordinatePolynomial f) : ContDiff ℝ ⊤ f := by
  obtain ⟨p, hp⟩ := hf
  apply contDiff_pi.mpr
  intro j
  have he : (fun x => f x j) = (fun x => MvPolynomial.eval x (p j)) := by
    funext x
    exact (hp x j).symm
  rw [he]
  exact (AnalyticOnNhd.eval_mvPolynomial (p j)).contDiff

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_BasisPolynomialMaps
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial maps in specified finite-dimensional bases -/

noncomputable section
namespace PolycyclicRecognition
open Module
variable {V W U : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup U] [NormedSpace ℝ U]
  {d e k : ℕ}

namespace IsPolynomialInBasis
variable {b : Basis (Fin d) ℝ V} {c : Basis (Fin e) ℝ W}
  {a : Basis (Fin k) ℝ U}

theorem contDiff {f : V → W} (hf : IsPolynomialInBasis b c f) : ContDiff ℝ ⊤ f := by
  let : FiniteDimensional ℝ V := Module.Finite.of_basis b
  let : FiniteDimensional ℝ W := Module.Finite.of_basis c
  have h := c.equivFun.toContinuousLinearEquiv.symm.contDiff.comp
    ((IsCoordinatePolynomial.contDiff hf).comp b.equivFun.toContinuousLinearEquiv.contDiff)
  change ContDiff ℝ ⊤ (fun x => c.equivFun.symm
    (c.equivFun (f (b.equivFun.symm (b.equivFun x))))) at h
  simpa only [LinearEquiv.symm_apply_apply] using h

theorem iterate {f : V → V} (hf : IsPolynomialInBasis b b f) (n : ℕ) :
    IsPolynomialInBasis b b (f^[n]) := by
  induction n with
  | zero => exact linear (LinearMap.id : V →ₗ[ℝ] V)
  | succ n ih =>
    have he : f^[n + 1] = f ∘ f^[n] := funext (Function.iterate_succ_apply' f n)
    rw [he]
    exact hf.comp ih

end IsPolynomialInBasis
end PolycyclicRecognition

end

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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_CommutingSemisimpleFixedRepresentative
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.JointFixedReductionData.residualLayer_normal _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.abelianRealCoordinates _root_.OAI.PolycyclicRecognition.abelianRealFiniteDimensional _root_.OAI.PolycyclicRecognition.abelianRealLieAbelian _root_.OAI.PolycyclicRecognition.abelianRealNormedLie _root_.OAI.PolycyclicRecognition.derivationLieSpaceFiniteDimensional _root_.OAI.PolycyclicRecognition.derivationLieSpaceRealNormed _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.polynomialLieIdealSubgroup_normal _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.JointFixedReductionData.residualLayerProjection_equiv _root_.OAI.PolycyclicRecognition.NilpotentKernelCompletion.extendedAction_embed _root_.OAI.PolycyclicRecognition.NilpotentLatticeCoordinates.automorphism_mul _root_.OAI.PolycyclicRecognition.NilpotentLatticeCoordinates.automorphism_on_lattice _root_.OAI.PolycyclicRecognition.NilpotentLatticeCoordinates.automorphism_one _root_.OAI.PolycyclicRecognition.PolynomialExponentialCoordinates.analyticDerivationAction_apply _root_.OAI.PolycyclicRecognition.abelianRealLatticeEquiv_apply _root_.OAI.PolycyclicRecognition.analyticDerivationExp_apply _root_.OAI.PolycyclicRecognition.derivationSemidirectHom_apply _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.polynomialCoordinateHom_apply _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Simultaneous fixed representatives for commuting semisimple factors

Successive canonical projections preserve all previously fixed symmetries.
Every inner automorphism centralizing a finite commuting semisimple family
therefore has a representative fixed by the whole family.
-/

noncomputable section
namespace PolycyclicRecognition
variable {L : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [C : PolynomialExponentialCoordinates L] [LieRing.IsNilpotent L]

theorem commuting_semisimple_inner_fixed_representative
    (ss : List (L ≃ₗ⁅ℝ⁆ L))
    (hss : ∀ S ∈ ss, Module.End.IsSemisimple S.toLinearMap)
    (hpair : ∀ S ∈ ss, ∀ T ∈ ss, Commute S.toLinearMap T.toLinearMap)
    (x : L) (hx : ∀ S ∈ ss, Commute S.toLinearMap (polynomialInnerLieEquiv x).toLinearMap) :
    ∃ y : L, (∀ S ∈ ss, S y = y) ∧
      (polynomialInnerLieEquiv y).toLinearMap = (polynomialInnerLieEquiv x).toLinearMap ∧
      ∀ T : L ≃ₗ⁅ℝ⁆ L, (∀ S ∈ ss, Commute T.toLinearMap S.toLinearMap) →
        T x = x → T y = y := by
  induction ss generalizing x with
  | nil => exact ⟨x, by simp, rfl, fun _ _ ht => ht⟩
  | cons S ss ih =>
    have hhead : S ∈ S :: ss := by simp
    have hmem {T : L ≃ₗ⁅ℝ⁆ L} (ht : T ∈ ss) : T ∈ S :: ss := List.mem_cons_of_mem S ht
    obtain ⟨y, hy, hiy, hpres⟩ :=
      semisimple_inner_fixed_representative_preserves S (hss S hhead) x (hx S hhead)
    obtain ⟨z, hz, hiz, hpz⟩ := ih
      (fun T ht => hss T (hmem ht))
      (fun T ht U hu => hpair T (hmem ht) U (hmem hu)) y
      (fun T ht => by rw [hiy]; exact hx T (hmem ht))
    refine ⟨z, ?_, hiz.trans hiy, ?_⟩
    · intro T ht
      rcases List.mem_cons.mp ht with h | ht
      · subst T
        exact hpz S (fun T ht => hpair S hhead T (hmem ht)) hy
      · exact hz T ht
    · intro T hT hTx
      have hTy : T y = y := hpres T (hT S hhead) hTx
      exact hpz T (fun U hu => hT U (hmem hu)) hTy

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_PolynomialLangTransversal
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.JointFixedReductionData.residualLayer_normal _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.abelianRealCoordinates _root_.OAI.PolycyclicRecognition.abelianRealFiniteDimensional _root_.OAI.PolycyclicRecognition.abelianRealLieAbelian _root_.OAI.PolycyclicRecognition.abelianRealNormedLie _root_.OAI.PolycyclicRecognition.derivationLieSpaceFiniteDimensional _root_.OAI.PolycyclicRecognition.derivationLieSpaceRealNormed _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.polynomialLieIdealSubgroup_normal _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.JointFixedReductionData.residualLayerProjection_equiv _root_.OAI.PolycyclicRecognition.NilpotentKernelCompletion.extendedAction_embed _root_.OAI.PolycyclicRecognition.NilpotentLatticeCoordinates.automorphism_mul _root_.OAI.PolycyclicRecognition.NilpotentLatticeCoordinates.automorphism_on_lattice _root_.OAI.PolycyclicRecognition.NilpotentLatticeCoordinates.automorphism_one _root_.OAI.PolycyclicRecognition.PolynomialExponentialCoordinates.analyticDerivationAction_apply _root_.OAI.PolycyclicRecognition.PolynomialExponentialCoordinates.derivationAction_apply _root_.OAI.PolycyclicRecognition.PolynomialExponentialCoordinates.groupAutomorphism_apply _root_.OAI.PolycyclicRecognition.abelianRealLatticeEquiv_apply _root_.OAI.PolycyclicRecognition.analyticDerivationExp_apply _root_.OAI.PolycyclicRecognition.derivationSemidirectHom_apply _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.polynomialCoordinateHom_apply _root_.OAI.PolycyclicRecognition.polynomialInnerLieEquiv_apply _root_.OAI.PolycyclicRecognition.polynomialModelLieEquiv_apply _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial Lang transversals from an invertible leading term

All nonlinear errors raise the finite lower central filtration. The inverse
is therefore obtained by the finite correction algorithm already constructed.
-/

noncomputable section
namespace PolycyclicRecognition
open LieModule
variable {L : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [C : PolynomialExponentialCoordinates L] [LieRing.IsNilpotent L]

theorem polynomial_transversal_bijective (A : L ≃ₗ⁅ℝ⁆ L) (P : Module.End ℝ L)
    (hPpres : ∀ k x, x ∈ (lowerCentralSeries ℝ L L k).toSubmodule →
      P x ∈ (lowerCentralSeries ℝ L L k).toSubmodule)
    (e : L ≃ₗ[ℝ] L)
    (he : ∀ z, -(z - P z) + P z + A (z - P z) = e z)
    (hepres : ∀ k x, x ∈ (lowerCentralSeries ℝ L L k).toSubmodule →
      e x ∈ (lowerCentralSeries ℝ L L k).toSubmodule) :
    Function.Bijective (fun x : L => (x - P x)⁻¹ * P x * A (x - P x)) := by
  let Q := (LinearMap.id : Module.End ℝ L) - P
  have hQ (x : L) : Q x = x - P x := rfl
  let U : ℕ → Submodule ℝ L := fun k => (lowerCentralSeries ℝ L L k).toSubmodule
  have hApres (k : ℕ) (x : L) (hx : x ∈ U k) : A x ∈ U k :=
    LieIdeal.map_lowerCentralSeries_le k (LieIdeal.mem_map hx)
  have hQpres (k : ℕ) (x : L) (hx : x ∈ U k) : Q x ∈ U k :=
    (U k).sub_mem hx (hPpres k x hx)
  have hinv (k : ℕ) (x : L) (hx : x ∈ U k) : e.symm x ∈ U k :=
    inverse_mem_of_preserves_submodule e (U k)
      (hepres k) hx
  let g : L → L := fun x => (Q x)⁻¹ * P x
  let f : L → L := fun x => g x * A (Q x)
  have hraise (k : ℕ) (x y : L) (hxy : x - y ∈ U k) :
      (f x - f y) - e (x - y) ∈ U (k + 1) := by
    have hQd : Q x - Q y ∈ U k := by rw [← map_sub]; exact hQpres k _ hxy
    have hPd : P x - P y ∈ U k := by rw [← map_sub]; exact hPpres k _ hxy
    have hQn : -Q x - -Q y ∈ U k := by
      simpa only [neg_sub_neg, neg_sub] using (U k).neg_mem hQd
    have h1 : (g x - g y) - ((-Q x - -Q y) + (P x - P y)) ∈ U (k + 1) := by
      simpa only [g, C.inv_eq_neg] using
        polynomial_mul_difference k (-Q x) (P x) (-Q y) (P y) hQn hPd
    have hgm : g x - g y ∈ U k := by
      have herr : (g x - g y) - ((-Q x - -Q y) + (P x - P y)) ∈ U k :=
        (antitone_lowerCentralSeries ℝ L L (Nat.le_succ k)) h1
      have hlin := (U k).add_mem hQn hPd
      have hh := (U k).add_mem herr hlin
      convert hh using 1 <;> first | (with_reducible_and_instances rfl) | (abel)
    have hAd : A (Q x) - A (Q y) ∈ U k := by
      rw [← map_sub]
      exact hApres k _ hQd
    have h2 := polynomial_mul_difference k (g x) (A (Q x)) (g y) (A (Q y)) hgm hAd
    have hlead : (-Q x - -Q y) + (P x - P y) + (A (Q x) - A (Q y)) = e (x - y) := by
      rw [← map_sub P, ← map_sub A, ← map_sub Q]
      have hn : -Q x - -Q y = -Q (x - y) := by rw [map_sub]; abel
      rw [hn]
      simpa only [hQ] using he (x - y)
    rw [← hlead]
    change ((g x * A (Q x)) - (g y * A (Q y))) - _ ∈ U (k + 1)
    have hh := (U (k + 1)).add_mem h2 h1
    convert hh using 1 <;> first | (with_reducible_and_instances rfl) | (abel)
  obtain ⟨c, hc⟩ := (LieModule.isNilpotent_iff ℝ L L).mp (inferInstance : LieModule.IsNilpotent L L)
  have hbij : Function.Bijective (fun x => e.symm (f x)) := by
    apply bijective_of_raises_difference_filtration U (by simp [U])
      (congrArg LieSubmodule.toSubmodule hc)
    intro k x y hxy
    have hh := hinv (k + 1) ((f x - f y) - e (x - y)) (hraise k x y hxy)
    simpa only [map_sub, e.symm_apply_apply] using hh
  have hf := e.bijective.comp hbij
  simpa only [Function.comp_def, e.apply_symm_apply, f, g, hQ] using hf

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_JordanLangTransversal
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.JointFixedReductionData.residualLayer_normal _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.abelianRealCoordinates _root_.OAI.PolycyclicRecognition.abelianRealFiniteDimensional _root_.OAI.PolycyclicRecognition.abelianRealLieAbelian _root_.OAI.PolycyclicRecognition.abelianRealNormedLie _root_.OAI.PolycyclicRecognition.derivationLieSpaceFiniteDimensional _root_.OAI.PolycyclicRecognition.derivationLieSpaceRealNormed _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.polynomialLieIdealSubgroup_normal _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Lang transversals for commuting semisimple and unipotent factors -/

noncomputable section
namespace PolycyclicRecognition
open LieModule
variable {L : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [C : PolynomialExponentialCoordinates L] [LieRing.IsNilpotent L]

theorem jordan_lang_transversal_bijective (A S U : L ≃ₗ⁅ℝ⁆ L)
    (hS : Module.End.IsSemisimple S.toLinearMap)
    (hU : IsNilpotent (U.toLinearMap - 1))
    (hSU : Commute S.toLinearMap U.toLinearMap)
    (hA : A.toLinearMap = S.toLinearMap * U.toLinearMap) :
    let B : Module.End ℝ L := S.toLinearMap - 1
    let hB := semisimple_sub_one S.toLinearMap hS
    let P := semisimpleKernelProjection B hB
    Function.Bijective (fun x : L => (x - P x)⁻¹ * P x * A (x - P x)) := by
  let B : Module.End ℝ L := S.toLinearMap - 1
  have hB : B.IsSemisimple := semisimple_sub_one S.toLinearMap hS
  let P := semisimpleKernelProjection B hB
  let F : ℕ → Submodule ℝ L := fun k => (lowerCentralSeries ℝ L L k).toSubmodule
  have hSp (k : ℕ) (x : L) (hx : x ∈ F k) : S x ∈ F k :=
    LieIdeal.map_lowerCentralSeries_le k (LieIdeal.mem_map hx)
  have hAp (k : ℕ) (x : L) (hx : x ∈ F k) : A x ∈ F k :=
    LieIdeal.map_lowerCentralSeries_le k (LieIdeal.mem_map hx)
  have hPp (k : ℕ) (x : L) (hx : x ∈ F k) : P x ∈ F k :=
    semisimpleKernelProjection_preserves B hB (F k)
      (fun y hy => (F k).sub_mem (hSp k y hy) hy) hx
  let E : Module.End ℝ L := (S.toLinearMap * U.toLinearMap - 1) * (1 - P) + P
  let e : L ≃ₗ[ℝ] L := LinearEquiv.ofBijective E
    (jordan_transversal_linear_bijective S.toLinearMap U.toLinearMap hS hU hSU)
  have he (z : L) : -(z - P z) + P z + A (z - P z) = e z := by
    change -(z - P z) + P z + A (z - P z) =
      (S (U (z - P z)) - (z - P z)) + P z
    have hz : A (z - P z) = S (U (z - P z)) := LinearMap.congr_fun hA _
    rw [hz]
    abel
  apply polynomial_transversal_bijective A P hPp e he
  intro k x hx
  rw [← he]
  exact (F k).add_mem ((F k).add_mem ((F k).neg_mem ((F k).sub_mem hx (hPp k x hx)))
    (hPp k x hx)) (hAp k _ ((F k).sub_mem hx (hPp k x hx)))

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_InvertibleJordanDecomposition
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The multiplicative decomposition needed for a real matrix logarithm

The additive Jordan decomposition of an invertible operator gives a commuting
semisimple unit and a unipotent factor. Both factors are constructed here.
-/

noncomputable section
namespace PolycyclicRecognition
variable {K V : Type*} [Field K] [PerfectField K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem invertible_jordan_decomposition_centralizer (A : Module.End K V) (hA : IsUnit A) :
    ∃ (S : (Module.End K V)ˣ) (U : Module.End K V),
      Module.End.IsSemisimple (S : Module.End K V) ∧ IsNilpotent (U - 1) ∧
      Commute (S : Module.End K V) U ∧ A = (S : Module.End K V) * U ∧ IsUnit U ∧
      ∀ T : Module.End K V, Commute A T → Commute (S : Module.End K V) T ∧ Commute U T := by
  obtain ⟨n, hn, s, hs, hnil, hsem, hsum⟩ := A.exists_isNilpotent_isSemisimple
  have hnA : Commute n A := (Algebra.commute_of_mem_adjoin_self hn).symm
  have hns : Commute n s := Algebra.commute_of_mem_adjoin_singleton_of_commute hs hnA
  have hsu : IsUnit s := by
    have hu := hnil.neg.isUnit_add_left_of_commute hA hnA.neg_left
    have he : A + -n = s := by rw [hsum]; abel
    rwa [he] at hu
  obtain ⟨S, hS⟩ := hsu
  have hnS : Commute n (S : Module.End K V) := hS.symm ▸ hns
  let q : Module.End K V := (S⁻¹ : (Module.End K V)ˣ) * n
  have hq : IsNilpotent q := by
    obtain ⟨k, hk⟩ := hnil
    refine ⟨k, ?_⟩
    change ((S⁻¹ : (Module.End K V)ˣ) * n) ^ k = 0
    rw [(hnS.units_inv_right).symm.mul_pow, hk, mul_zero]
  have hSq : Commute (S : Module.End K V) q := by
    change (S : Module.End K V) * ((S⁻¹ : (Module.End K V)ˣ) * n) =
      ((S⁻¹ : (Module.End K V)ˣ) * n) * (S : Module.End K V)
    calc
      _ = n := by simp [← mul_assoc]
      _ = (S⁻¹ : (Module.End K V)ˣ) * ((S : Module.End K V) * n) := by
        simp [← mul_assoc]
      _ = _ := by rw [← hnS.eq, mul_assoc]
  refine ⟨S, 1 + q, hS.symm ▸ hsem, ?_, (Commute.one_right _).add_right hSq, ?_,
    hq.isUnit_one_add, ?_⟩
  · simpa only [add_sub_cancel_left] using hq
  · have he : (S : Module.End K V) * q = n := by simp [q, ← mul_assoc]
    rw [mul_add, mul_one, he, hS, add_comm]
    exact hsum
  · intro T hT
    have hsT : Commute (S : Module.End K V) T := by
      rw [hS]
      exact (Algebra.commute_of_mem_adjoin_singleton_of_commute hs hT.symm).symm
    have hnT : Commute n T :=
      (Algebra.commute_of_mem_adjoin_singleton_of_commute hn hT.symm).symm
    exact ⟨hsT, (Commute.one_left T).add_left (hsT.units_inv_left.mul_left hnT)⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_SemisimpleSpectralOperator
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Scalar functional calculus on the eigenspaces of a semisimple operator

Only the finite-dimensional application needed for a matrix logarithm is
used. The operator is constructed from the internal eigenspace direct sum.
-/

noncomputable section
namespace PolycyclicRecognition
open scoped DirectSum
variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

theorem semisimpleSpectralOperator_commute (S : Module.End ℂ V) (hS : S.IsSemisimple)
    (f : ℂ → ℂ) (T : Module.End ℂ V) (hT : Commute S T) :
    Commute (semisimpleSpectralOperator S hS f) T := by
  change semisimpleSpectralOperator S hS f * T = T * semisimpleSpectralOperator S hS f
  apply semisimple_eigenspace_ext S hS
  intro μ x hx
  have hTx : T x ∈ S.eigenspace μ := by
    rw [Module.End.mem_eigenspace_iff]
    change (S * T) x = μ • T x
    rw [hT.eq]
    change T (S x) = μ • T x
    rw [Module.End.mem_eigenspace_iff.mp hx, map_smul]
  change semisimpleSpectralOperator S hS f (T x) = T (semisimpleSpectralOperator S hS f x)
  rw [semisimpleSpectralOperator_apply S hS _ hTx,
    semisimpleSpectralOperator_apply S hS _ hx, map_smul]

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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_FreeAbelianLogarithm
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.latticeNormalFlag_normal _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Compatible logarithms of characters of free abelian groups

Choosing logarithms only on a basis preserves all multiplicative relations.
-/

noncomputable section
namespace PolycyclicRecognition

theorem freeAbelianLogarithm_exp {n : ℕ} (ρ : IntegralLatticeGroup n →* ℂˣ) :
    complexUnitExp.comp (freeAbelianLogarithm ρ) = ρ := by
  let f := ((Pi.basisFun ℤ (Fin n)).constr ℤ
    (fun i => Complex.log (ρ (Multiplicative.ofAdd ((Pi.basisFun ℤ (Fin n)) i)) : ℂ)))
  have he : (complexUnitExp.toAdditive.toIntLinearMap).comp f =
      ρ.toAdditive.toIntLinearMap := by
    apply (Pi.basisFun ℤ (Fin n)).ext
    intro i
    erw [LinearMap.comp_apply]
    change complexUnitExp (Multiplicative.ofAdd (f ((Pi.basisFun ℤ (Fin n)) i))) = _
    rw [Module.Basis.constr_basis]
    apply Units.ext
    exact Complex.exp_log (Units.ne_zero _)
  apply MonoidHom.ext
  intro x
  exact DFunLike.congr_fun he x.toAdd

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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_FiniteGeneratedCharacterLog
attribute [-instance] _root_.GeneratesNS.rho_g_FG _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.latticeNormalFlag_normal _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Logarithms of powers of finitely generated abelian characters

A finite-index free subgroup supplies a compatible choice on a basis.
The index-power map pulls that choice back to the whole group.
-/

noncomputable section
namespace PolycyclicRecognition

variable {G : Type} [CommGroup G]

theorem finitelyGenerated_character_power_log [Group.FG G] (ρ : G →* ℂˣ) :
    ∃ m : ℕ, 0 < m ∧ ∃ L : G →* Multiplicative ℂ,
      ∀ g, complexUnitExp (L g) = ρ g ^ m := by
  have hpoly := isPolycyclic_of_finitelyGenerated_commGroup G
  obtain ⟨K, hK, htf⟩ := hpoly.exists_torsionFree_finiteIndex
  let := hK
  obtain ⟨n, ⟨e⟩⟩ := exists_integralLattice_equiv htf
  let r := ρ.comp (K.subtype.comp e.toMonoidHom)
  let p := e.symm.toMonoidHom.comp (finiteIndexPowerHom K)
  refine ⟨K.index, Nat.pos_of_ne_zero hK.index_ne_zero,
    (freeAbelianLogarithm r).comp p, ?_⟩
  intro g
  have h := DFunLike.congr_fun (freeAbelianLogarithm_exp r) (p g)
  change complexUnitExp (freeAbelianLogarithm r (p g)) = _
  rw [MonoidHom.comp_apply] at h
  rw [h]
  change ρ (e (e.symm (finiteIndexPowerHom K g))) = ρ g ^ K.index
  rw [e.apply_symm_apply]
  exact map_pow ρ g K.index

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_ConjugateCharacterLog
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Conjugation-compatible logarithms after a finite power

Symmetrizing a compatible logarithm doubles its power and makes it respect
the involution. This will preserve real forms in the spectral construction.
-/

noncomputable section
namespace PolycyclicRecognition
variable {G : Type} [CommGroup G]

theorem conjugateCharacterLog_exp (L : G →* Multiplicative ℂ) (c : G →* G) (g : G) :
    complexUnitExp (conjugateCharacterLog L c g) = star (complexUnitExp (L (c g))) := by
  apply Units.ext
  exact Complex.exp_conj _

theorem symmetrizedCharacterLog_conjugation (L : G →* Multiplicative ℂ)
    (c : G →* G) (hc : ∀ g, c (c g) = g) (g : G) :
    ((L * conjugateCharacterLog L c) (c g)).toAdd =
      star (((L * conjugateCharacterLog L c) g).toAdd) := by
  change (L (c g)).toAdd + star (L (c (c g))).toAdd =
    star ((L g).toAdd + star (L (c g)).toAdd)
  rw [hc, star_add, star_star, add_comm]

theorem finitelyGenerated_real_character_power_log [Group.FG G]
    (ρ : G →* ℂˣ) (c : G →* G) (hc : ∀ g, c (c g) = g)
    (hρ : ∀ g, ρ (c g) = star (ρ g)) :
    ∃ m : ℕ, 0 < m ∧ ∃ L : G →* Multiplicative ℂ,
      (∀ g, complexUnitExp (L g) = ρ g ^ m) ∧
      (∀ g, (L (c g)).toAdd = star (L g).toAdd) := by
  obtain ⟨m, hm, L, hL⟩ := finitelyGenerated_character_power_log ρ
  refine ⟨2 * m, Nat.mul_pos (by decide) hm, L * conjugateCharacterLog L c, ?_,
    symmetrizedCharacterLog_conjugation L c hc⟩
  intro g
  rw [MonoidHom.mul_apply, map_mul, hL, conjugateCharacterLog_exp, hL, hρ,
    star_pow, star_star, two_mul, pow_add]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_SpectralUnitGroup
attribute [-instance] _root_.GeneratesNS.rho_g_FG _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The finitely generated group of nonzero spectral values

We include the conjugate eigenvalues so the resulting group has its actual
conjugation involution, independently of a later choice of logarithm.
-/

noncomputable section
namespace PolycyclicRecognition

variable {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

theorem spectralUnits_finite (S : Module.End ℂ V) : (spectralUnits S).Finite :=
  S.finite_hasEigenvalue.preimage Units.val_injective.injOn

instance spectralUnitGroup_fg (S : Module.End ℂ V) : Group.FG (spectralUnitGroup S) := by
  let : Finite ↥(spectralUnits S ∪ star '' spectralUnits S : Set ℂˣ) :=
    ((spectralUnits_finite S).union ((spectralUnits_finite S).image star)).to_subtype
  exact Group.closure_finite_fg _

omit [FiniteDimensional ℂ V] in
theorem spectralUnitConjugation_involutive (S : Module.End ℂ V)
    (z : spectralUnitGroup S) :
    spectralUnitConjugation S (spectralUnitConjugation S z) = z := by
  apply Subtype.ext
  exact star_star z.val

theorem spectralUnitGroup_logarithm (S : Module.End ℂ V) :
    ∃ m : ℕ, 0 < m ∧ ∃ L : spectralUnitGroup S →* Multiplicative ℂ,
      (∀ z, complexUnitExp (L z) = z.val ^ m) ∧
      (∀ z, (L (spectralUnitConjugation S z)).toAdd = star (L z).toAdd) := by
  exact finitelyGenerated_real_character_power_log (spectralUnitGroup S).subtype
    (spectralUnitConjugation S) (spectralUnitConjugation_involutive S) (fun _ => rfl)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_SpectralLogValue
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Scalar values of a compatible spectral logarithm -/

noncomputable section
namespace PolycyclicRecognition
variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem spectralLogValue_conjugation (S : Module.End ℂ V)
    (L : spectralUnitGroup S →* Multiplicative ℂ)
    (hc : ∀ z, (L (spectralUnitConjugation S z)).toAdd = star (L z).toAdd)
    (z : spectralUnitGroup S) :
    spectralLogValue S L (star (z.val : ℂ)) = star (spectralLogValue S L (z.val : ℂ)) := by
  rw [spectralLogValue_unit]
  exact (spectralLogValue_unit S L (spectralUnitConjugation S z)).trans (hc z)

theorem spectralLogValue_conjugation_all (S : Module.End ℂ V)
    (L : spectralUnitGroup S →* Multiplicative ℂ)
    (hc : ∀ z, (L (spectralUnitConjugation S z)).toAdd = star (L z).toAdd)
    (z : ℂ) : spectralLogValue S L (star z) = star (spectralLogValue S L z) := by
  classical
  by_cases hz : z = 0
  · simp [hz, spectralLogValue]
  have hcz : star z ≠ 0 := by simpa using hz
  let u : ℂˣ := Units.mk0 z hz
  by_cases hu : u ∈ spectralUnitGroup S
  · exact spectralLogValue_conjugation S L hc ⟨u, hu⟩
  · have hv : Units.mk0 (star z) hcz ∉ spectralUnitGroup S := by
      intro hv
      apply hu
      have h := spectralUnitGroup_star S hv
      convert h using 1
      all_goals try with_reducible_and_instances rfl
      apply Units.ext
      exact (star_star z).symm
    simp only [spectralLogValue, dite_eq_left hz, dite_eq_left hcz, dite_eq_right hv]
    have hu' : Units.mk0 z hz ∉ spectralUnitGroup S := hu
    rw [dite_eq_right hu', star_zero]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_SemisimpleExponential
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exponentiating scalar operators on eigenspaces -/

noncomputable section
namespace PolycyclicRecognition

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]

theorem continuousLinear_exp_eigenvector (T : V →L[ℂ] V) {x : V} {μ : ℂ}
    (hx : T x = μ • x) : NormedSpace.exp T x = Complex.exp μ • x := by
  have hp (n : ℕ) : (T ^ n) x = μ ^ n • x := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', mul_apply_eq_comp, ih, map_smul, hx,
        smul_smul, pow_succ, mul_comm]
  have h := (ContinuousLinearMap.apply ℂ V x).hasSum
    (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) T)
  have hs := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) μ).smul_const x
  rw [← Complex.exp_eq_exp_ℂ] at hs
  apply h.unique
  convert hs using 1
  all_goals try with_reducible_and_instances rfl
  ext n
  simp only [ContinuousLinearMap.apply_apply, smul_apply,
    hp, smul_smul, smul_eq_mul]

variable [FiniteDimensional ℂ V]

theorem exp_semisimpleSpectralOperator (S : Module.End ℂ V) (hS : S.IsSemisimple)
    (f : ℂ → ℂ) :
    (NormedSpace.exp (LinearMap.toContinuousLinearMap
      (semisimpleSpectralOperator S hS f))).toLinearMap =
      semisimpleSpectralOperator S hS (fun μ => Complex.exp (f μ)) := by
  apply semisimple_eigenspace_ext S hS
  intro μ x hx
  exact (continuousLinear_exp_eigenvector _
    (semisimpleSpectralOperator_apply S hS f hx)).trans
      (semisimpleSpectralOperator_apply S hS (fun μ => Complex.exp (f μ)) hx).symm

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_SpectralConjugation
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Conjugation compatibility of the spectral logarithm -/

noncomputable section
namespace PolycyclicRecognition

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

theorem semisimple_starLinear_ext (S : Module.End ℂ V) (hS : S.IsSemisimple)
    {F G : V →ₗ⋆[ℂ] V}
    (h : ∀ μ x, x ∈ S.eigenspace μ → F x = G x) : F = G := by
  apply sub_eq_zero.mp
  apply LinearMap.ker_eq_top.mp
  apply top_unique
  rw [← hS.iSup_eigenspace_eq_top]
  apply iSup_le
  intro μ x hx
  rw [LinearMap.mem_ker, LinearMap.sub_apply, h μ x hx, sub_self]

theorem semisimpleSpectralOperator_conjugation (S : Module.End ℂ V)
    (hS : S.IsSemisimple) (c : V →ₗ⋆[ℂ] V)
    (hc : ∀ x, c (S x) = S (c x)) (f : ℂ → ℂ)
    (hf : ∀ z, f (star z) = star (f z)) (x : V) :
    c (semisimpleSpectralOperator S hS f x) =
      semisimpleSpectralOperator S hS f (c x) := by
  have he : c.comp (semisimpleSpectralOperator S hS f) =
      (semisimpleSpectralOperator S hS f).comp c := by
    apply semisimple_starLinear_ext S hS
    intro μ y hy
    have hcy : c y ∈ S.eigenspace (star μ) := by
      rw [Module.End.mem_eigenspace_iff, ← hc y,
        Module.End.mem_eigenspace_iff.mp hy, map_smulₛₗ]
      rfl
    change c (semisimpleSpectralOperator S hS f y) =
      semisimpleSpectralOperator S hS f (c y)
    rw [semisimpleSpectralOperator_apply S hS f hy,
      semisimpleSpectralOperator_apply S hS f hcy, map_smulₛₗ, hf]
    rfl
  exact DFunLike.congr_fun he x

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_SpectralLogExponential
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exponentiating the compatible spectral logarithm -/

noncomputable section
namespace PolycyclicRecognition
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [FiniteDimensional ℂ V] [CompleteSpace V]

theorem exp_compatibleSpectralLog (S : Module.End ℂ V) (hS : S.IsSemisimple)
    (hu : IsUnit S) (l : spectralUnitGroup S →* Multiplicative ℂ)
    (m : ℕ) (hl : ∀ z, complexUnitExp (l z) = z.val ^ m) :
    (NormedSpace.exp (LinearMap.toContinuousLinearMap
      (semisimpleSpectralOperator S hS (spectralLogValue S l)))).toLinearMap = S ^ m := by
  rw [exp_semisimpleSpectralOperator]
  apply semisimple_eigenspace_ext S hS
  intro μ x hx
  by_cases hx0 : x = 0
  · simp [hx0]
  have hμ : S.HasEigenvalue μ := Module.End.hasEigenvalue_of_hasEigenvector ⟨hx, hx0⟩
  let z := spectralEigenvalue S hu μ hμ
  have hz : Complex.exp (spectralLogValue S l μ) = μ ^ m := by
    rw [show μ = (z.val : ℂ) from rfl, spectralLogValue_unit]
    exact congrArg Units.val (hl z)
  rw [semisimpleSpectralOperator_apply S hS _ hx, hz]
  exact (Module.End.HasEigenvector.pow_apply ⟨hx, hx0⟩ m).symm

omit [CompleteSpace V] in
theorem compatibleSpectralLog_conjugation (S : Module.End ℂ V) (hS : S.IsSemisimple)
    (l : spectralUnitGroup S →* Multiplicative ℂ)
    (hl : ∀ z, (l (spectralUnitConjugation S z)).toAdd = star (l z).toAdd)
    (c : V →ₗ⋆[ℂ] V) (hc : ∀ x, c (S x) = S (c x)) (x : V) :
    c (semisimpleSpectralOperator S hS (spectralLogValue S l) x) =
      semisimpleSpectralOperator S hS (spectralLogValue S l) (c x) :=
  semisimpleSpectralOperator_conjugation S hS c hc _
    (spectralLogValue_conjugation_all S l hl) x

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ComplexifiedLieAutomorphism
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Complexification of a real semisimple Lie automorphism -/

noncomputable section
namespace PolycyclicRecognition
open scoped TensorProduct

variable (L : Type) [LieRing L] [LieAlgebra ℝ L]

theorem complexifiedLieEquiv_conj (S : L ≃ₗ⁅ℝ⁆ L) (x : ℂ ⊗[ℝ] L) :
    complexificationConjSemilinear L (complexifiedLieEquiv L S x) =
      complexifiedLieEquiv L S (complexificationConjSemilinear L x) := by
  induction x using OAI.tensorInductionOn with
  | tmul z x => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem complexifiedEnd_semisimple [FiniteDimensional ℝ L]
    (S : Module.End ℝ L) (hS : S.IsSemisimple) :
    Module.End.IsSemisimple (S.baseChange ℂ) := by
  let f := Module.End.baseChangeHom ℝ ℂ L
  have hp : Squarefree ((minpoly ℝ S).map (algebraMap ℝ ℂ)) :=
    (PerfectField.separable_iff_squarefree.mpr hS.minpoly_squarefree).map.squarefree
  apply Module.End.isSemisimple_of_squarefree_aeval_eq_zero hp
  have he := Polynomial.map_aeval_eq_aeval_map
    (φ := algebraMap ℝ ℂ) (ψ := f.toRingHom)
    (by apply RingHom.ext; intro r; exact (f.commutes r).symm)
    (minpoly ℝ S) S
  rw [minpoly.aeval, map_zero] at he
  exact he.symm

theorem complexifiedLieEquiv_semisimple [FiniteDimensional ℝ L]
    (S : L ≃ₗ⁅ℝ⁆ L) (hS : Module.End.IsSemisimple S.toLinearMap) :
    Module.End.IsSemisimple (complexifiedLieEquiv L S).toLinearMap :=
  complexifiedEnd_semisimple L S.toLinearMap hS

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_GeneralizedLieEigenvectors
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Brackets of generalized eigenvectors of a Lie endomorphism -/

noncomputable section
namespace PolycyclicRecognition
variable {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]

theorem lie_generalized_eigenvector_annihilated (A : L →ₗ⁅K⁆ L)
    (μ ν : K) (k l : ℕ) (x y : L)
    (hx : ((A.toLinearMap - μ • 1) ^ k) x = 0)
    (hy : ((A.toLinearMap - ν • 1) ^ l) y = 0) :
    ((A.toLinearMap - (μ * ν) • 1) ^ (k + l)) ⁅x, y⁆ = 0 := by
  induction k generalizing l x y with
  | zero =>
    have : x = 0 := by simpa using hx
    simp [this]
  | succ k ihk =>
    induction l generalizing x y with
    | zero =>
      have : y = 0 := by simpa using hy
      simp [this]
    | succ l ihl =>
      let Nμ := A.toLinearMap - μ • 1
      let Nν := A.toLinearMap - ν • 1
      let T := A.toLinearMap - (μ * ν) • 1
      have hx' : (Nμ ^ k) (Nμ x) = 0 := by
        simpa only [Nμ, pow_succ, Module.End.mul_apply] using hx
      have hy' : (Nν ^ l) (Nν y) = 0 := by
        simpa only [Nν, pow_succ, Module.End.mul_apply] using hy
      have hc : Commute Nν A.toLinearMap :=
        (Commute.refl A.toLinearMap).sub_left (Algebra.commute_algebraMap_left ν _)
      have hyA : (Nν ^ (l + 1)) (A y) = 0 := by
        have h := congrArg (fun F : Module.End K L => F y) (hc.pow_left (l + 1)).eq
        change (Nν ^ (l + 1)) (A y) = A ((Nν ^ (l + 1)) y) at h
        rw [h, hy, map_zero]
      have h₁ := ihk (l + 1) (Nμ x) (A y) hx' hyA
      have h₂ := ihl x (Nν y) hx hy'
      have hid : T ⁅x, y⁆ = ⁅Nμ x, A y⁆ + μ • ⁅x, Nν y⁆ := by
        change A ⁅x, y⁆ - (μ * ν) • ⁅x, y⁆ = _
        rw [A.map_lie]
        simp only [Nμ, Nν, LinearMap.sub_apply, LinearMap.smul_apply,
          Module.End.one_apply, sub_lie, lie_sub, smul_lie, lie_smul,
          smul_sub, smul_smul]
        change ⁅A x, A y⁆ - (μ * ν) • ⁅x, y⁆ =
          (⁅A x, A y⁆ - μ • ⁅x, A y⁆) +
            (μ • ⁅x, A y⁆ - (μ * ν) • ⁅x, y⁆)
        abel
      change (T ^ (k + 1 + (l + 1))) ⁅x, y⁆ = 0
      rw [show k + 1 + (l + 1) = (k + (l + 1)) + 1 by omega,
        pow_succ, Module.End.mul_apply, hid, map_add, map_smul]
      have h₂' : (T ^ (k + (l + 1))) ⁅x, Nν y⁆ = 0 := by
        simpa only [T, show k + (l + 1) = k + 1 + l by omega] using h₂
      rw [h₁, h₂', smul_zero, add_zero]

theorem lie_mem_maxGenEigenspace (A : L →ₗ⁅K⁆ L) (μ ν : K)
    {x y : L} (hx : x ∈ Module.End.maxGenEigenspace A.toLinearMap μ)
    (hy : y ∈ Module.End.maxGenEigenspace A.toLinearMap ν) :
    ⁅x, y⁆ ∈ Module.End.maxGenEigenspace A.toLinearMap (μ * ν) := by
  obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace _ _ _).mp hx
  obtain ⟨l, hl⟩ := (Module.End.mem_maxGenEigenspace _ _ _).mp hy
  exact (Module.End.mem_maxGenEigenspace _ _ _).mpr
    ⟨k + l, lie_generalized_eigenvector_annihilated A μ ν k l x y hk hl⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_JordanLieFactor
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The semisimple Jordan factor preserves the Lie bracket -/

noncomputable section
namespace PolycyclicRecognition
attribute [local instance] LieRing.ofAssociativeRing
variable {L : Type} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]

omit [FiniteDimensional ℂ L] in
theorem semisimple_factor_eigenvector_generalized (A S : Module.End ℂ L)
    (hc : Commute A S) (hn : IsNilpotent (A - S))
    {μ : ℂ} {x : L} (hx : x ∈ S.eigenspace μ) :
    x ∈ A.maxGenEigenspace μ := by
  have hxS : x ∈ S.genEigenspace μ ⊤ := S.eigenspace_le_maxGenEigenspace hx
  have hxN : x ∈ (A - S).genEigenspace 0 ⊤ := by
    obtain ⟨k, hk⟩ := hn
    apply (Module.End.mem_maxGenEigenspace _ _ _).mpr
    exact ⟨k, by simp only [zero_smul, sub_zero, hk, LinearMap.zero_apply]⟩
  have hSN : Commute S (A - S) := hc.symm.sub_right (Commute.refl S)
  have h := Module.End.genEigenspace_inf_le_add S (A - S) μ 0 ⊤ ⊤ hSN ⟨hxS, hxN⟩
  have he : S + (A - S) = A := by abel
  simpa only [he, add_zero, top_add] using h

theorem semisimple_jordan_factor_map_lie (A : L →ₗ⁅ℂ⁆ L) (S : Module.End ℂ L)
    (hS : S.IsSemisimple) (hc : Commute A.toLinearMap S)
    (hn : IsNilpotent (A.toLinearMap - S)) (x y : L) :
    S ⁅x, y⁆ = ⁅S x, S y⁆ := by
  let B := (LieAlgebra.ad ℂ L).toLinearMap
  let F : L →ₗ[ℂ] L →ₗ[ℂ] L :=
    { toFun := fun x => S.comp (B x)
      map_add' := by intros; simp [LinearMap.comp_add]
      map_smul' := by intros; simp [LinearMap.comp_smul] }
  let G : L →ₗ[ℂ] L →ₗ[ℂ] L :=
    { toFun := fun x => (B (S x)).comp S
      map_add' := by intros; simp [LinearMap.add_comp]
      map_smul' := by intros; simp [LinearMap.smul_comp] }
  have he : F = G := by
    apply semisimple_bilinear_ext S hS
    intro μ ν u v hu hv
    change S ⁅u, v⁆ = ⁅S u, S v⁆
    have huA := semisimple_factor_eigenvector_generalized A.toLinearMap S hc hn hu
    have hvA := semisimple_factor_eigenvector_generalized A.toLinearMap S hc hn hv
    have hb := lie_mem_maxGenEigenspace A μ ν huA hvA
    have heig := Module.End.apply_eq_of_mem_of_comm_of_isFinitelySemisimple_of_isNil
      hb hc hS.isFinitelySemisimple hn
    rw [heig, Module.End.mem_eigenspace_iff.mp hu, Module.End.mem_eigenspace_iff.mp hv,
      smul_lie, lie_smul, smul_smul]
  exact congrArg (fun T : L →ₗ[ℂ] L →ₗ[ℂ] L => T x y) he

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_RealJordanLieFactor
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The real semisimple Jordan factor preserves the Lie bracket -/

noncomputable section
namespace PolycyclicRecognition
open scoped TensorProduct
variable {L : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]

theorem real_semisimple_jordan_factor_map_lie (A : L ≃ₗ⁅ℝ⁆ L) (S : Module.End ℝ L)
    (hS : S.IsSemisimple) (hc : Commute A.toLinearMap S)
    (hn : IsNilpotent (A.toLinearMap - S)) (x y : L) :
    S ⁅x, y⁆ = ⁅S x, S y⁆ := by
  let f := Module.End.baseChangeHom ℝ ℂ L
  have hc' : Commute (complexifiedLieEquiv L A).toLinearMap (S.baseChange ℂ) := hc.map f
  let CA : Module.End ℂ (ℂ ⊗[ℝ] L) := (complexifiedLieEquiv L A).toLinearMap
  let CS : Module.End ℂ (ℂ ⊗[ℝ] L) := S.baseChange ℂ
  have hn' : IsNilpotent (CA - CS) := by
    obtain ⟨k, hk⟩ := hn
    refine ⟨k, ?_⟩
    change (f A.toLinearMap - f S) ^ k = 0
    rw [← map_sub, ← map_pow, hk, map_zero]
  have h := semisimple_jordan_factor_map_lie (complexifiedLieEquiv L A).toLieHom
    (S.baseChange ℂ) (complexifiedEnd_semisimple L S hS) hc' hn'
    ((1 : ℂ) ⊗ₜ[ℝ] x) ((1 : ℂ) ⊗ₜ[ℝ] y)
  apply complexificationLieHom_injective L
  change (1 : ℂ) ⊗ₜ[ℝ] S ⁅x, y⁆ = (1 : ℂ) ⊗ₜ[ℝ] ⁅S x, S y⁆
  simpa using h

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_RealLieJordanDecomposition
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Multiplicative Jordan decomposition inside real Lie automorphisms -/

noncomputable section
namespace PolycyclicRecognition
variable {L : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]

theorem real_lie_jordan_decomposition_centralizer (A : L ≃ₗ⁅ℝ⁆ L) :
    ∃ S U : L ≃ₗ⁅ℝ⁆ L, Module.End.IsSemisimple S.toLinearMap ∧
      IsNilpotent (U.toLinearMap - 1) ∧ Commute S.toLinearMap U.toLinearMap ∧
      A.toLinearMap = S.toLinearMap * U.toLinearMap ∧
      ∀ T : Module.End ℝ L, Commute A.toLinearMap T →
        Commute S.toLinearMap T ∧ Commute U.toLinearMap T := by
  obtain ⟨s, u, hs, hu, hsu, hA, _, hcom⟩ := invertible_jordan_decomposition_centralizer A.toLinearMap
    ((Module.End.isUnit_iff _).mpr A.bijective)
  have hc : Commute A.toLinearMap (s : Module.End ℝ L) := by
    rw [hA]
    exact (Commute.refl _).mul_left hsu.symm
  have hn : IsNilpotent (A.toLinearMap - (s : Module.End ℝ L)) := by
    have he : A.toLinearMap - (s : Module.End ℝ L) = (s : Module.End ℝ L) * (u - 1) := by
      rw [hA, mul_sub, mul_one]
    rw [he]
    obtain ⟨k, hk⟩ := hu
    exact ⟨k, by rw [(hsu.sub_right (Commute.one_right _)).mul_pow, hk, mul_zero]⟩
  let S : L ≃ₗ⁅ℝ⁆ L :=
    { LinearMap.GeneralLinearGroup.toLinearEquiv s with
      map_lie' := fun {x y} =>
        real_semisimple_jordan_factor_map_lie A (s : Module.End ℝ L) hs hc hn x y }
  let U : L ≃ₗ⁅ℝ⁆ L := A.trans S.symm
  have heS : S.toLinearMap = (s : Module.End ℝ L) := rfl
  have heU : U.toLinearMap = u := by
    change (s⁻¹ : (Module.End ℝ L)ˣ) * A.toLinearMap = u
    rw [hA, ← mul_assoc, Units.inv_mul, one_mul]
  refine ⟨S, U, heS.symm ▸ hs, heU.symm ▸ hu,
    by rwa [heS, heU], by rwa [heS, heU], ?_⟩
  intro T hT
  rw [heS, heU]
  exact hcom T hT

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_MultiplicativeJordanUniqueness
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniqueness of the multiplicative semisimple factor -/

namespace PolycyclicRecognition
variable {K V : Type*} [Field K] [PerfectField K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem multiplicative_jordan_semisimple_unique
    (S₁ U₁ S₂ U₂ : Module.End K V)
    (hS₁ : S₁.IsSemisimple) (hU₁ : IsNilpotent (U₁ - 1))
    (hS₂ : S₂.IsSemisimple) (hU₂ : IsNilpotent (U₂ - 1))
    (hC₁ : Commute S₁ U₁) (hC₂ : Commute S₂ U₂)
    (h : S₁ * U₁ = S₂ * U₂) : S₁ = S₂ := by
  have hc₁ : Commute S₁ (U₁ - 1) := hC₁.sub_right (Commute.one_right S₁)
  have hc₂ : Commute S₂ (U₂ - 1) := hC₂.sub_right (Commute.one_right S₂)
  have hn₁ : IsNilpotent (S₁ * (U₁ - 1)) := hc₁.isNilpotent_mul_left hU₁
  have hn₂ : IsNilpotent (S₂ * (U₂ - 1)) := hc₂.isNilpotent_mul_left hU₂
  apply (Module.End.isNilpotent_isSemisimple_unique hn₁ hS₁ hn₂ hS₂
    ((Commute.refl S₁).mul_left hc₁.symm)
    ((Commute.refl S₂).mul_left hc₂.symm) ?_).2
  simpa only [mul_sub, mul_one, sub_add_cancel] using h

omit [PerfectField K] [FiniteDimensional K V] in
theorem semisimple_conj (e : V ≃ₗ[K] V) (S : Module.End K V) (hS : S.IsSemisimple) :
    (e.conjRingEquiv S).IsSemisimple := by
  apply (e.isSemisimple_iff S (e.conjRingEquiv S) ?_).mp hS
  apply LinearMap.ext
  intro x
  simp

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_InnerTwistJordanFactor
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.JointFixedReductionData.residualLayer_normal _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.abelianRealCoordinates _root_.OAI.PolycyclicRecognition.abelianRealFiniteDimensional _root_.OAI.PolycyclicRecognition.abelianRealLieAbelian _root_.OAI.PolycyclicRecognition.abelianRealNormedLie _root_.OAI.PolycyclicRecognition.derivationLieSpaceFiniteDimensional _root_.OAI.PolycyclicRecognition.derivationLieSpaceRealNormed _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.polynomialLieIdealSubgroup_normal _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Semisimple factors in an inner coset

Changing a nilpotent-group automorphism by inner conjugation changes its
semisimple Jordan factor by inner conjugation. The conjugating element is
constructed by the global Lang transversal.
-/

noncomputable section
namespace PolycyclicRecognition
variable {L : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [C : PolynomialExponentialCoordinates L] [LieRing.IsNilpotent L]

omit [LieRing.IsNilpotent L] in
theorem inner_normal_form_semisimple_factor (A S T V W : L ≃ₗ⁅ℝ⁆ L)
    (hS : Module.End.IsSemisimple S.toLinearMap) (u v : L)
    (hW : IsNilpotent (W.toLinearMap - 1))
    (hSW : Commute S.toLinearMap W.toLinearMap)
    (hv : ∀ x : L, v * (u * A (v⁻¹ * x * v) * u⁻¹) * v⁻¹ = S (W x))
    (hT : Module.End.IsSemisimple T.toLinearMap)
    (hV : IsNilpotent (V.toLinearMap - 1))
    (hTV : Commute T.toLinearMap V.toLinearMap)
    (hu : (polynomialInnerLieEquiv u).toLinearMap * A.toLinearMap =
      T.toLinearMap * V.toLinearMap) :
    (polynomialInnerLieEquiv v).toLinearEquiv.conjRingEquiv T.toLinearMap = S.toLinearMap := by
  let e := (polynomialInnerLieEquiv v).toLinearEquiv
  have he (x : L) : e x = v * x * v⁻¹ := polynomialInnerLieEquiv_apply v x
  have hei (x : L) : e.symm x = v⁻¹ * x * v := by
    apply e.injective
    rw [e.apply_symm_apply, he]
    group
  have hh : e.conjRingEquiv ((polynomialInnerLieEquiv u).toLinearMap * A.toLinearMap) =
      S.toLinearMap * W.toLinearMap := by
    apply LinearMap.ext
    intro x
    change e (polynomialInnerLieEquiv u (A (e.symm x))) = S (W x)
    rw [he, hei, polynomialInnerLieEquiv_apply]
    exact hv x
  have hV' : IsNilpotent (e.conjRingEquiv V.toLinearMap - 1) := by
    have h := hV.map e.conjRingEquiv
    simpa only [map_sub, map_one] using h
  have hTV' : Commute (e.conjRingEquiv T.toLinearMap) (e.conjRingEquiv V.toLinearMap) :=
    hTV.map e.conjRingEquiv.toMonoidHom
  have hprod : e.conjRingEquiv T.toLinearMap * e.conjRingEquiv V.toLinearMap =
      S.toLinearMap * W.toLinearMap := by
    rw [← map_mul, ← hu]
    exact hh
  exact multiplicative_jordan_semisimple_unique _ _ _ _
    (semisimple_conj e T.toLinearMap hT) hV' hS hW hTV' hSW hprod

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_EquivariantLangTransversal
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.JointFixedReductionData.residualLayer_normal _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.abelianRealCoordinates _root_.OAI.PolycyclicRecognition.abelianRealFiniteDimensional _root_.OAI.PolycyclicRecognition.abelianRealLieAbelian _root_.OAI.PolycyclicRecognition.abelianRealNormedLie _root_.OAI.PolycyclicRecognition.derivationLieSpaceFiniteDimensional _root_.OAI.PolycyclicRecognition.derivationLieSpaceRealNormed _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.polynomialLieIdealSubgroup_normal _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Lang decomposition preserves commuting symmetries

Uniqueness of the finite-filtration inverse ensures that a correction of a
fixed element can be chosen fixed by every commuting symmetry already imposed.
-/

noncomputable section
namespace PolycyclicRecognition
variable {L : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [C : PolynomialExponentialCoordinates L]

theorem polynomial_transversal_equivariant (A T : L ≃ₗ⁅ℝ⁆ L) (P : Module.End ℝ L)
    (hTP : Commute T.toLinearMap P) (hTA : Commute T.toLinearMap A.toLinearMap) (x : L) :
    (T x - P (T x))⁻¹ * P (T x) * A (T x - P (T x)) =
      T ((x - P x)⁻¹ * P x * A (x - P x)) := by
  have hp : P (T x) = T (P x) := (LinearMap.congr_fun hTP.eq x).symm
  have hq : T x - P (T x) = T (x - P x) := by rw [hp, map_sub]
  have ha : A (T (x - P x)) = T (A (x - P x)) :=
    (LinearMap.congr_fun hTA.eq _).symm
  rw [hq, hp, ha]
  let t := PolynomialExponentialCoordinates.groupAutomorphism (P := C) T
  change (t (x - P x))⁻¹ * t (P x) * t (A (x - P x)) =
    t ((x - P x)⁻¹ * P x * A (x - P x))
  rw [map_mul, map_mul, map_inv]

variable [LieRing.IsNilpotent L]

theorem jordan_lang_decomposition_fixed_family {ι : Type*}
    (A S U : L ≃ₗ⁅ℝ⁆ L) (T : ι → L ≃ₗ⁅ℝ⁆ L)
    (hS : Module.End.IsSemisimple S.toLinearMap)
    (hU : IsNilpotent (U.toLinearMap - 1))
    (hSU : Commute S.toLinearMap U.toLinearMap)
    (hA : A.toLinearMap = S.toLinearMap * U.toLinearMap)
    (hTS : ∀ i, Commute (T i).toLinearMap S.toLinearMap)
    (hTA : ∀ i, Commute (T i).toLinearMap A.toLinearMap) (u : L) (htu : ∀ i, T i u = u) :
    ∃ v w : L, S w = w ∧ (∀ i, T i v = v) ∧ (∀ i, T i w = w) ∧
      u = v⁻¹ * w * A v := by
  let B : Module.End ℝ L := S.toLinearMap - 1
  have hB : B.IsSemisimple := semisimple_sub_one S.toLinearMap hS
  let P := semisimpleKernelProjection B hB
  have hTP (i : ι) : Commute (T i).toLinearMap P :=
    (semisimpleKernelProjection_commute B (T i).toLinearMap hB
      ((hTS i).symm.sub_left (Commute.one_left _))).symm
  let f := fun x : L => (x - P x)⁻¹ * P x * A (x - P x)
  have hf : Function.Bijective f := jordan_lang_transversal_bijective A S U hS hU hSU hA
  obtain ⟨x, hx⟩ := hf.surjective u
  have htx (i : ι) : T i x = x := hf.injective (by
    change (T i x - P (T i x))⁻¹ * P (T i x) * A (T i x - P (T i x)) = f x
    rw [polynomial_transversal_equivariant A (T i) P (hTP i) (hTA i)]
    change T i (f x) = f x
    rw [hx, htu i])
  have hp (i : ι) : T i (P x) = P x := by
    have hh : T i (P x) = P (T i x) := LinearMap.congr_fun (hTP i).eq x
    rwa [htx] at hh
  exact ⟨x - P x, P x, sub_eq_zero.mp (semisimpleKernelProjection_mem B hB x),
    fun i => by rw [map_sub, htx, hp], hp, hx.symm⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_RelativeJordanInnerTwist
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.JointFixedReductionData.residualLayer_normal _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.abelianRealCoordinates _root_.OAI.PolycyclicRecognition.abelianRealFiniteDimensional _root_.OAI.PolycyclicRecognition.abelianRealLieAbelian _root_.OAI.PolycyclicRecognition.abelianRealNormedLie _root_.OAI.PolycyclicRecognition.derivationLieSpaceFiniteDimensional _root_.OAI.PolycyclicRecognition.derivationLieSpaceRealNormed _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.polynomialLieIdealSubgroup_normal _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Inner correction while preserving a previously chosen symmetry family -/

noncomputable section
namespace PolycyclicRecognition
variable {L : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [C : PolynomialExponentialCoordinates L] [LieRing.IsNilpotent L]

theorem jordan_inner_twist_normal_form_fixed {ι : Type*}
    (A S U : L ≃ₗ⁅ℝ⁆ L) (T : ι → L ≃ₗ⁅ℝ⁆ L)
    (hS : Module.End.IsSemisimple S.toLinearMap)
    (hU : IsNilpotent (U.toLinearMap - 1))
    (hSU : Commute S.toLinearMap U.toLinearMap)
    (hA : A.toLinearMap = S.toLinearMap * U.toLinearMap)
    (hTS : ∀ i, Commute (T i).toLinearMap S.toLinearMap)
    (hTU : ∀ i, Commute (T i).toLinearMap U.toLinearMap)
    (u : L) (htu : ∀ i, T i u = u) :
    ∃ (v : L) (W : L ≃ₗ⁅ℝ⁆ L), IsNilpotent (W.toLinearMap - 1) ∧
      Commute S.toLinearMap W.toLinearMap ∧ (∀ i, T i v = v) ∧
      (∀ i, Commute (T i).toLinearMap W.toLinearMap) ∧
      ∀ x : L, v * (u * A (v⁻¹ * x * v) * u⁻¹) * v⁻¹ = S (W x) := by
  have hTA (i : ι) : Commute (T i).toLinearMap A.toLinearMap := by
    rw [hA]
    exact (hTS i).mul_right (hTU i)
  obtain ⟨v, w, hSw, hTv, hTw, hu⟩ :=
    jordan_lang_decomposition_fixed_family A S U T hS hU hSU hA hTS hTA u htu
  let W := U.trans (polynomialInnerLieEquiv w)
  have hW (x : L) : W x = w * U x * w⁻¹ := polynomialInnerLieEquiv_apply w (U x)
  have hcomm (R : L ≃ₗ⁅ℝ⁆ L) (hw : R w = w)
      (hRU : Commute R.toLinearMap U.toLinearMap) : Commute R.toLinearMap W.toLinearMap := by
    apply LinearMap.ext
    intro x
    change R (W x) = W (R x)
    rw [hW, hW]
    let r := PolynomialExponentialCoordinates.groupAutomorphism (P := C) R
    change r (w * U x * w⁻¹) = w * U (R x) * w⁻¹
    rw [map_mul, map_mul, map_inv]
    change R w * R (U x) * (R w)⁻¹ = w * U (R x) * w⁻¹
    rw [hw]
    have hh : R (U x) = U (R x) := LinearMap.congr_fun hRU.eq x
    rw [hh]
  refine ⟨v, W, polynomial_inner_mul_unipotent U hU w, hcomm S hSw hSU,
    hTv, fun i => hcomm (T i) (hTw i) (hTU i), ?_⟩
  intro x
  let a := PolynomialExponentialCoordinates.groupAutomorphism (P := C) A
  have hr : v * (u * A (v⁻¹ * x * v) * u⁻¹) * v⁻¹ = w * A x * w⁻¹ := by
    change v * (u * a (v⁻¹ * x * v) * u⁻¹) * v⁻¹ = w * a x * w⁻¹
    change u = v⁻¹ * w * a v at hu
    rw [hu]
    simp only [map_mul, map_inv]
    group
  rw [hr, hW]
  have hAx : A x = S (U x) := LinearMap.congr_fun hA x
  rw [hAx]
  let s := PolynomialExponentialCoordinates.groupAutomorphism (P := C) S
  change w * S (U x) * w⁻¹ = s (w * U x * w⁻¹)
  rw [map_mul, map_mul, map_inv]
  change w * S (U x) * w⁻¹ = S w * S (U x) * (S w)⁻¹
  rw [hSw]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_RelativeSemisimpleCorrection
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.JointFixedReductionData.residualLayer_normal _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.abelianRealCoordinates _root_.OAI.PolycyclicRecognition.abelianRealFiniteDimensional _root_.OAI.PolycyclicRecognition.abelianRealLieAbelian _root_.OAI.PolycyclicRecognition.abelianRealNormedLie _root_.OAI.PolycyclicRecognition.derivationLieSpaceFiniteDimensional _root_.OAI.PolycyclicRecognition.derivationLieSpaceRealNormed _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.polynomialLieIdealSubgroup_normal _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Semisimple centralizer corrections preserving a commuting family -/

noncomputable section
namespace PolycyclicRecognition
variable {L : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [C : PolynomialExponentialCoordinates L] [LieRing.IsNilpotent L]

theorem semisimple_centralizer_inner_correction_fixed {ι : Type*}
    (A S U B : L ≃ₗ⁅ℝ⁆ L) (T : ι → L ≃ₗ⁅ℝ⁆ L)
    (hS : Module.End.IsSemisimple S.toLinearMap)
    (hU : IsNilpotent (U.toLinearMap - 1))
    (hSU : Commute S.toLinearMap U.toLinearMap)
    (hA : A.toLinearMap = S.toLinearMap * U.toLinearMap)
    (hTS : ∀ i, Commute (T i).toLinearMap S.toLinearMap)
    (hTU : ∀ i, Commute (T i).toLinearMap U.toLinearMap)
    (u : L) (htu : ∀ i, T i u = u)
    (hu : (polynomialInnerLieEquiv u).toLinearMap * A.toLinearMap =
      B.toLinearEquiv.conjRingEquiv A.toLinearMap) :
    ∃ v : L, (∀ i, T i v = v) ∧
      Commute ((polynomialInnerLieEquiv v).toLinearMap * B.toLinearMap) S.toLinearMap := by
  obtain ⟨v, W, hW, hSW, hTv, _, hv⟩ :=
    jordan_inner_twist_normal_form_fixed A S U T hS hU hSU hA hTS hTU u htu
  let J := B.symm.trans (S.trans B)
  let V := B.symm.trans (U.trans B)
  have hJ : J.toLinearMap = B.toLinearEquiv.conjRingEquiv S.toLinearMap := rfl
  have hV : V.toLinearMap = B.toLinearEquiv.conjRingEquiv U.toLinearMap := rfl
  have hVnil : IsNilpotent (V.toLinearMap - 1) := by
    rw [hV]
    have hh := hU.map B.toLinearEquiv.conjRingEquiv
    simpa only [map_sub, map_one] using hh
  have hJV : Commute J.toLinearMap V.toLinearMap := by
    rw [hJ, hV]
    exact hSU.map B.toLinearEquiv.conjRingEquiv.toMonoidHom
  have hprod : (polynomialInnerLieEquiv u).toLinearMap * A.toLinearMap =
      J.toLinearMap * V.toLinearMap := by
    rw [hu, hJ, hV, ← map_mul, ← hA]
  have hj := inner_normal_form_semisimple_factor A S J V W hS u v hW hSW hv
    (by rw [hJ]; exact semisimple_conj B.toLinearEquiv S.toLinearMap hS) hVnil hJV hprod
  let e := (polynomialInnerLieEquiv v).toLinearEquiv
  have hpoint (x : L) : e (B (S (B.symm (e.symm x)))) = S x := LinearMap.congr_fun hj x
  refine ⟨v, hTv, ?_⟩
  apply LinearMap.ext
  intro x
  have hh := hpoint (e (B x))
  rw [e.symm_apply_apply, B.symm_apply_apply] at hh
  exact hh

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_CommutingSemisimpleCorrection
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.JointFixedReductionData.residualLayer_normal _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.abelianRealCoordinates _root_.OAI.PolycyclicRecognition.abelianRealFiniteDimensional _root_.OAI.PolycyclicRecognition.abelianRealLieAbelian _root_.OAI.PolycyclicRecognition.abelianRealNormedLie _root_.OAI.PolycyclicRecognition.derivationLieSpaceFiniteDimensional _root_.OAI.PolycyclicRecognition.derivationLieSpaceRealNormed _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.polynomialLieIdealSubgroup_normal _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Successive semisimple corrections preserve all earlier centralizers -/

noncomputable section
namespace PolycyclicRecognition
variable {L : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [C : PolynomialExponentialCoordinates L] [LieRing.IsNilpotent L]

theorem semisimple_centralizer_correction_preserving_family
    (A S U B : L ≃ₗ⁅ℝ⁆ L) (ss : List (L ≃ₗ⁅ℝ⁆ L))
    (hS : Module.End.IsSemisimple S.toLinearMap)
    (hU : IsNilpotent (U.toLinearMap - 1))
    (hSU : Commute S.toLinearMap U.toLinearMap)
    (hA : A.toLinearMap = S.toLinearMap * U.toLinearMap)
    (hss : ∀ T ∈ ss, Module.End.IsSemisimple T.toLinearMap)
    (hpair : ∀ T ∈ ss, ∀ R ∈ ss, Commute T.toLinearMap R.toLinearMap)
    (hTS : ∀ T ∈ ss, Commute T.toLinearMap S.toLinearMap)
    (hTU : ∀ T ∈ ss, Commute T.toLinearMap U.toLinearMap)
    (hTB : ∀ T ∈ ss, Commute T.toLinearMap B.toLinearMap)
    (u : L) (hu : (polynomialInnerLieEquiv u).toLinearMap * A.toLinearMap =
      B.toLinearEquiv.conjRingEquiv A.toLinearMap) :
    ∃ v : L, (∀ T ∈ ss, T v = v) ∧
      Commute ((polynomialInnerLieEquiv v).toLinearMap * B.toLinearMap) S.toLinearMap := by
  have hTA (T : L ≃ₗ⁅ℝ⁆ L) (ht : T ∈ ss) : Commute T.toLinearMap A.toLinearMap := by
    rw [hA]
    exact (hTS T ht).mul_right (hTU T ht)
  have hTi (T : L ≃ₗ⁅ℝ⁆ L) (ht : T ∈ ss) :
      Commute T.toLinearMap (polynomialInnerLieEquiv u).toLinearMap := by
    apply linear_commute_of_mul_equiv_right _ _ A.toLinearEquiv (hTA T ht)
    change Commute T.toLinearMap
      ((polynomialInnerLieEquiv u).toLinearMap * A.toLinearMap)
    rw [hu]
    exact linear_commute_conj B.toLinearEquiv T.toLinearMap A.toLinearMap (hTB T ht) (hTA T ht)
  obtain ⟨w, hw, hiw, _⟩ := commuting_semisimple_inner_fixed_representative ss hss hpair u hTi
  have huw : (polynomialInnerLieEquiv w).toLinearMap * A.toLinearMap =
      B.toLinearEquiv.conjRingEquiv A.toLinearMap := by rw [hiw]; exact hu
  let I := {T : L ≃ₗ⁅ℝ⁆ L // T ∈ ss}
  obtain ⟨v, hv, hc⟩ := semisimple_centralizer_inner_correction_fixed A S U B
    (fun t : I => t.val) hS hU hSU hA
    (fun t => hTS t.val t.property) (fun t => hTU t.val t.property) w
    (fun t => hw t.val t.property) huw
  exact ⟨v, fun T ht => hv ⟨T, ht⟩, hc⟩

/-- The next Jordan factor can be chosen in the common commutant. Corrections
of every further outer-centralizing element preserve the whole earlier family. -/
theorem exists_semisimple_factor_with_preserving_corrections
    (A : L ≃ₗ⁅ℝ⁆ L) (ss : List (L ≃ₗ⁅ℝ⁆ L))
    (hss : ∀ T ∈ ss, Module.End.IsSemisimple T.toLinearMap)
    (hpair : ∀ T ∈ ss, ∀ R ∈ ss, Commute T.toLinearMap R.toLinearMap)
    (hTA : ∀ T ∈ ss, Commute T.toLinearMap A.toLinearMap) :
    ∃ S U : L ≃ₗ⁅ℝ⁆ L, Module.End.IsSemisimple S.toLinearMap ∧
      IsNilpotent (U.toLinearMap - 1) ∧ Commute S.toLinearMap U.toLinearMap ∧
      A.toLinearMap = S.toLinearMap * U.toLinearMap ∧
      (∀ T ∈ ss, Commute T.toLinearMap S.toLinearMap) ∧
      ∀ B : L ≃ₗ⁅ℝ⁆ L, (∀ T ∈ ss, Commute T.toLinearMap B.toLinearMap) →
        ∀ u : L, (polynomialInnerLieEquiv u).toLinearMap * A.toLinearMap =
          B.toLinearEquiv.conjRingEquiv A.toLinearMap →
          ∃ v : L, (∀ T ∈ ss, T v = v) ∧
            Commute ((polynomialInnerLieEquiv v).toLinearMap * B.toLinearMap) S.toLinearMap := by
  obtain ⟨S, U, hS, hU, hSU, hA, hcentral⟩ := real_lie_jordan_decomposition_centralizer A
  have hTS (T : L ≃ₗ⁅ℝ⁆ L) (ht : T ∈ ss) : Commute T.toLinearMap S.toLinearMap :=
    (hcentral T.toLinearMap (hTA T ht).symm).1.symm
  have hTU (T : L ≃ₗ⁅ℝ⁆ L) (ht : T ∈ ss) : Commute T.toLinearMap U.toLinearMap :=
    (hcentral T.toLinearMap (hTA T ht).symm).2.symm
  exact ⟨S, U, hS, hU, hSU, hA, hTS, fun B hTB u hu =>
    semisimple_centralizer_correction_preserving_family A S U B ss
      hS hU hSU hA hss hpair hTS hTU hTB u hu⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_ExtensionSemisimpleCentralizer
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.JointFixedReductionData.residualLayer_normal _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.abelianRealCoordinates _root_.OAI.PolycyclicRecognition.abelianRealFiniteDimensional _root_.OAI.PolycyclicRecognition.abelianRealLieAbelian _root_.OAI.PolycyclicRecognition.abelianRealNormedLie _root_.OAI.PolycyclicRecognition.derivationLieSpaceFiniteDimensional _root_.OAI.PolycyclicRecognition.derivationLieSpaceRealNormed _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.polynomialLieIdealSubgroup_normal _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

namespace OAI

/-! # Semisimple centralizers in a smooth nilpotent-kernel extension

For an abelian quotient, every quotient element has a lift whose conjugation
on the nilpotent kernel centralizes the semisimple part of a prescribed lift.
The correcting element lies in the actual completed kernel.
-/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold ContDiff IsMulCommutative
variable {L G Q : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [C : PolynomialExponentialCoordinates L] [LieRing.IsNilpotent L]
  [Group G] [Group Q]

omit [LieRing.IsNilpotent L] in
theorem extension_conjAct_inl (E : GroupExtension L G Q) (u : L) :
    E.conjAct (E.inl u) = MulAut.conj u := by
  apply DFunLike.ext
  intro x
  apply E.inl_injective
  rw [E.inl_conjAct_comm]
  change E.inl u * E.inl x * (E.inl u)⁻¹ = E.inl (u * x * u⁻¹)
  rw [map_mul, map_mul, map_inv]

omit [LieRing.IsNilpotent L] in
theorem extension_outer_conjugation_identity [IsMulCommutative Q]
    (E : GroupExtension L G Q)
    (hsmooth : ∀ g : G, ContMDiff (𝓘(ℝ, L)) (𝓘(ℝ, L)) ∞ (E.conjAct g)) (t g : G) :
    ∃ u : L, (polynomialInnerLieEquiv u).toLinearMap *
        (polynomialModelLieEquiv (E.conjAct t) (hsmooth t)).toLinearMap =
      (polynomialModelLieEquiv (E.conjAct g) (hsmooth g)).toLinearEquiv.conjRingEquiv
        (polynomialModelLieEquiv (E.conjAct t) (hsmooth t)).toLinearMap := by
  let A := polynomialModelLieEquiv (E.conjAct t) (hsmooth t)
  let B := polynomialModelLieEquiv (E.conjAct g) (hsmooth g)
  have ha (x : L) : A x = E.conjAct t x := polynomialModelLieEquiv_apply _ _ x
  have hb (x : L) : B x = E.conjAct g x := polynomialModelLieEquiv_apply _ _ x
  have hbi (x : L) : B.symm x = (E.conjAct g)⁻¹ x := by
    apply B.injective
    change B (B.symm x) = B ((E.conjAct g)⁻¹ x)
    rw [B.apply_symm_apply, hb]
    exact ((E.conjAct g).apply_symm_apply x).symm
  have hker : g * t * g⁻¹ * t⁻¹ ∈ E.inl.range := by
    rw [E.range_inl_eq_ker_rightHom]
    change E.rightHom (g * t * g⁻¹ * t⁻¹) = 1
    simp only [map_mul, map_inv]
    rw [mul_comm (E.rightHom g) (E.rightHom t)]
    group
  obtain ⟨u, hu⟩ := hker
  have hgroup : g * t * g⁻¹ = E.inl u * t := by rw [hu]; group
  have hconj := congrArg E.conjAct hgroup
  simp only [map_mul, map_inv, extension_conjAct_inl] at hconj
  refine ⟨u, ?_⟩
  apply LinearMap.ext
  intro x
  change polynomialInnerLieEquiv u (A x) = B (A (B.symm x))
  rw [polynomialInnerLieEquiv_apply, ha, hbi, hb, ha]
  exact (congrArg (fun f : MulAut L => f x) hconj).symm


end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_CommonSemisimpleCentralizer
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.JointFixedReductionData.residualLayer_normal _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.abelianRealCoordinates _root_.OAI.PolycyclicRecognition.abelianRealFiniteDimensional _root_.OAI.PolycyclicRecognition.abelianRealLieAbelian _root_.OAI.PolycyclicRecognition.abelianRealNormedLie _root_.OAI.PolycyclicRecognition.derivationLieSpaceFiniteDimensional _root_.OAI.PolycyclicRecognition.derivationLieSpaceRealNormed _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.polynomialLieIdealSubgroup_normal _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

namespace OAI

/-! # Common semisimple centralizers in the completed extension -/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold ContDiff IsMulCommutative
variable {L G Q : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [C : PolynomialExponentialCoordinates L] [LieRing.IsNilpotent L]
  [Group G] [Group Q]

omit [LieRing.IsNilpotent L] in
theorem mem_commonSemisimpleCentralizer (E : GroupExtension L G Q)
    (ss : List (L ≃ₗ⁅ℝ⁆ L)) (g : G) :
    g ∈ commonSemisimpleCentralizer E ss ↔ ∀ T ∈ ss, g ∈ semisimpleActionCentralizer E T := by
  simp only [commonSemisimpleCentralizer, Subgroup.mem_iInf]
  exact ⟨fun h T ht => h ⟨T, ht⟩, fun h T => h T.val T.property⟩

omit [LieRing.IsNilpotent L] in
theorem inl_mem_commonSemisimpleCentralizer_of_fixed (E : GroupExtension L G Q)
    (ss : List (L ≃ₗ⁅ℝ⁆ L)) (x : L) (hx : ∀ T ∈ ss, T x = x) :
    E.inl x ∈ commonSemisimpleCentralizer E ss := by
  apply (mem_commonSemisimpleCentralizer E ss (E.inl x)).mpr
  intro T ht
  change E.conjAct (E.inl x) ∈
    Subgroup.centralizer {PolynomialExponentialCoordinates.groupAutomorphism (P := C) T}
  rw [extension_conjAct_inl]
  apply Subgroup.mem_centralizer_singleton_iff.mpr
  apply DFunLike.ext
  intro y
  let t := PolynomialExponentialCoordinates.groupAutomorphism (P := C) T
  change x * t y * x⁻¹ = t (x * y * x⁻¹)
  rw [map_mul, map_mul, map_inv]
  change x * t y * x⁻¹ = T x * t y * (T x)⁻¹
  rw [hx T ht]

theorem common_semisimpleCentralizer_step [IsMulCommutative Q]
    (E : GroupExtension L G Q)
    (hsmooth : ∀ g : G, ContMDiff (𝓘(ℝ, L)) (𝓘(ℝ, L)) ∞ (E.conjAct g))
    (ss : List (L ≃ₗ⁅ℝ⁆ L))
    (hss : ∀ T ∈ ss, Module.End.IsSemisimple T.toLinearMap)
    (hpair : ∀ T ∈ ss, ∀ R ∈ ss, Commute T.toLinearMap R.toLinearMap)
    (t : G) (ht : t ∈ commonSemisimpleCentralizer E ss) :
    ∃ S U : L ≃ₗ⁅ℝ⁆ L, Module.End.IsSemisimple S.toLinearMap ∧
      IsNilpotent (U.toLinearMap - 1) ∧ Commute S.toLinearMap U.toLinearMap ∧
      (polynomialModelLieEquiv (E.conjAct t) (hsmooth t)).toLinearMap =
        S.toLinearMap * U.toLinearMap ∧
      (∀ T ∈ ss, Commute T.toLinearMap S.toLinearMap) ∧
      ∀ g ∈ commonSemisimpleCentralizer E ss, ∃ v : L,
        (∀ T ∈ ss, T v = v) ∧ E.inl v * g ∈ commonSemisimpleCentralizer E (S :: ss) := by
  let A := polynomialModelLieEquiv (E.conjAct t) (hsmooth t)
  have hTA (T : L ≃ₗ⁅ℝ⁆ L) (hT : T ∈ ss) : Commute T.toLinearMap A.toLinearMap :=
    (mem_semisimpleActionCentralizer_iff E T t (hsmooth t)).mp
      ((mem_commonSemisimpleCentralizer E ss t).mp ht T hT)
  obtain ⟨S, U, hS, hU, hSU, hA, hTS, hcorrect⟩ :=
    exists_semisimple_factor_with_preserving_corrections A ss hss hpair hTA
  refine ⟨S, U, hS, hU, hSU, hA, hTS, ?_⟩
  intro g hg
  let B := polynomialModelLieEquiv (E.conjAct g) (hsmooth g)
  have hTB (T : L ≃ₗ⁅ℝ⁆ L) (hT : T ∈ ss) : Commute T.toLinearMap B.toLinearMap :=
    (mem_semisimpleActionCentralizer_iff E T g (hsmooth g)).mp
      ((mem_commonSemisimpleCentralizer E ss g).mp hg T hT)
  obtain ⟨u, hu⟩ := extension_outer_conjugation_identity E hsmooth t g
  obtain ⟨v, hv, hc⟩ := hcorrect B hTB u hu
  have hnew : E.inl v * g ∈ semisimpleActionCentralizer E S := by
    change E.conjAct (E.inl v * g) ∈
      Subgroup.centralizer {PolynomialExponentialCoordinates.groupAutomorphism (P := C) S}
    rw [map_mul, extension_conjAct_inl]
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    apply DFunLike.ext
    intro x
    have hh : polynomialInnerLieEquiv v (B (S x)) = S (polynomialInnerLieEquiv v (B x)) :=
      LinearMap.congr_fun hc.eq x
    change v * E.conjAct g (S x) * v⁻¹ = S (v * E.conjAct g x * v⁻¹)
    simpa only [polynomialInnerLieEquiv_apply, B, polynomialModelLieEquiv_apply] using hh
  refine ⟨v, hv, (mem_commonSemisimpleCentralizer E (S :: ss) (E.inl v * g)).mpr ?_⟩
  intro T hT
  rcases List.mem_cons.mp hT with he | hT
  · subst T
    exact hnew
  · exact (mem_commonSemisimpleCentralizer E ss (E.inl v * g)).mp
      ((commonSemisimpleCentralizer E ss).mul_mem
        (inl_mem_commonSemisimpleCentralizer_of_fixed E ss v hv) hg) T hT

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_RealMatrixSquareLogarithm
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Every squared real linear automorphism has a real logarithm

The semisimple factor uses the conjugation-compatible scalar logarithm of a
square. The unipotent factor uses its finite polynomial logarithm.
-/

noncomputable section
namespace PolycyclicRecognition

theorem commute_nilpotentLog_right {A : Type*} [Ring A] [Algebra ℚ A]
    {a b : A} (h : Commute a b) : Commute a (nilpotentLog b) := by
  unfold nilpotentLog finiteNilpotentLog
  rw [Polynomial.aeval_eq_smeval]
  exact (Polynomial.smeval_commute_left ℚ _ h.symm).symm

theorem analytic_exp_nilpotentLog {A : Type*} [NormedRing A] [NormedAlgebra ℚ A]
    (a : A) (ha : IsNilpotent a) : NormedSpace.exp (nilpotentLog a) = 1 + a := by
  rw [analytic_exp_eq_nilpotent_exp (nilpotentLog_nilpotent a ha), exp_nilpotentLog a ha]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_ComplexDerivationDescent
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Descending a conjugation-invariant complex derivation -/

noncomputable section
namespace PolycyclicRecognition
open scoped TensorProduct
variable (L : Type) [LieRing L] [LieAlgebra ℝ L]

theorem complexDerivationRealPart_embed
    (D : LieDerivation ℂ (ℂ ⊗[ℝ] L) (ℂ ⊗[ℝ] L))
    (hc : ∀ z, complexificationConjSemilinear L (D z) =
      D (complexificationConjSemilinear L z)) (x : L) :
    (1 : ℂ) ⊗ₜ[ℝ] complexDerivationRealPart L D x = D ((1 : ℂ) ⊗ₜ[ℝ] x) := by
  have hf : complexificationConjugation L (D ((1 : ℂ) ⊗ₜ[ℝ] x)) =
      D ((1 : ℂ) ⊗ₜ[ℝ] x) := by
    change complexificationConjSemilinear L (D _) = _
    rw [hc]
    simp [complexificationConjSemilinear]
  obtain ⟨y, hy⟩ := (complexification_conjugation_fixed_iff L _).mp hf
  change (1 : ℂ) ⊗ₜ[ℝ] complexificationRealPart L (D ((1 : ℂ) ⊗ₜ[ℝ] x)) = _
  rw [hy]
  simp

theorem complexDerivationRealPart_baseChange
    (D : LieDerivation ℂ (ℂ ⊗[ℝ] L) (ℂ ⊗[ℝ] L))
    (hc : ∀ z, complexificationConjSemilinear L (D z) =
      D (complexificationConjSemilinear L z)) :
    (complexDerivationRealPart L D).toLinearMap.baseChange ℂ = D.toLinearMap := by
  apply LinearMap.ext
  intro v
  induction v using OAI.tensorInductionOn with
  | tmul z x =>
    change z ⊗ₜ[ℝ] complexDerivationRealPart L D x = D (z ⊗ₜ[ℝ] x)
    have h := congrArg (fun y : ℂ ⊗[ℝ] L => z • y)
      (complexDerivationRealPart_embed L D hc x)
    simpa only [← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one] using h
  | add v w hv hw => simp only [map_add, hv, hw]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ComplexifiedOperatorExponential
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.JointFixedReductionData.residualLayer_normal _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.abelianRealFiniteDimensional _root_.OAI.PolycyclicRecognition.abelianRealLieAbelian _root_.OAI.PolycyclicRecognition.abelianRealNormedLie _root_.OAI.PolycyclicRecognition.derivationLieSpaceFiniteDimensional _root_.OAI.PolycyclicRecognition.derivationLieSpaceRealNormed _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.polynomialLieIdealSubgroup_normal _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exponentials commute with the concrete complexification of operators -/

noncomputable section
namespace PolycyclicRecognition
open scoped TensorProduct
variable (L : Type) [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]

attribute [local instance] OAI.PolycyclicRecognition.instComplexNormedLieAlgebraTensorProductRealComplex
theorem complexifiedEnd_exp (D : Module.End ℝ L) :
    ((NormedSpace.exp (LinearMap.toContinuousLinearMap D)).toLinearMap).baseChange ℂ =
      (NormedSpace.exp (LinearMap.toContinuousLinearMap (D.baseChange ℂ))).toLinearMap := by
  let := NormedAlgebra.restrictScalars ℚ ℝ (L →L[ℝ] L)
  let := NormedAlgebra.restrictScalars ℚ ℂ ((ℂ ⊗[ℝ] L) →L[ℂ] (ℂ ⊗[ℝ] L))
  have h := NormedSpace.map_exp (continuousComplexifiedEnd L)
    (continuousComplexifiedEnd L).toLinearMap.continuous_of_finiteDimensional
    (LinearMap.toContinuousLinearMap D)
  exact congrArg
    (fun T : (ℂ ⊗[ℝ] L) →L[ℂ] (ℂ ⊗[ℝ] L) => T.toLinearMap) h

omit [FiniteDimensional ℝ L] in
theorem realEnd_baseChange_injective : Function.Injective (Module.End.baseChangeHom ℝ ℂ L) := by
  intro A B h
  apply LinearMap.ext
  intro x
  apply complexificationLieHom_injective L
  exact congrArg (fun T : Module.End ℂ (ℂ ⊗[ℝ] L) => T ((1 : ℂ) ⊗ₜ[ℝ] x)) h

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_UnipotentLieFlow
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.JointFixedReductionData.residualLayer_normal _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.abelianRealFiniteDimensional _root_.OAI.PolycyclicRecognition.abelianRealLieAbelian _root_.OAI.PolycyclicRecognition.abelianRealNormedLie _root_.OAI.PolycyclicRecognition.derivationLieSpaceFiniteDimensional _root_.OAI.PolycyclicRecognition.derivationLieSpaceRealNormed _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.polynomialLieIdealSubgroup_normal _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A real Lie-automorphism flow through a given unipotent automorphism -/

noncomputable section
namespace PolycyclicRecognition
variable {L : Type*} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]

attribute [local instance] OAI.PolycyclicRecognition.unipotentFlowRationalModule
theorem exp_unipotentLieLogarithm (A : L ≃ₗ⁅ℝ⁆ L)
    (hA : IsNilpotent (A.toLinearMap - 1)) :
    IsNilpotent.exp (unipotentLieLogarithm A hA).toLinearMap = A.toLinearMap := by
  rw [unipotentLieLogarithm_toLinearMap, exp_nilpotentLog _ hA]
  abel

theorem unipotentLieFlow_one (A : L ≃ₗ⁅ℝ⁆ L) (hA : IsNilpotent (A.toLinearMap - 1)) :
    unipotentLieFlow A hA 1 = A := by
  ext x
  change IsNilpotent.exp (1 • (unipotentLieLogarithm A hA).toLinearMap) x = A x
  rw [one_smul, exp_unipotentLieLogarithm]
  rfl

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_CommutingDerivationAction
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.JointFixedReductionData.residualLayer_normal _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.abelianRealCoordinates _root_.OAI.PolycyclicRecognition.abelianRealFiniteDimensional _root_.OAI.PolycyclicRecognition.abelianRealLieAbelian _root_.OAI.PolycyclicRecognition.abelianRealNormedLie _root_.OAI.PolycyclicRecognition.derivationLieSpaceFiniteDimensional _root_.OAI.PolycyclicRecognition.derivationLieSpaceRealNormed _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.polynomialLieIdealSubgroup_normal _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.JointFixedReductionData.residualLayerProjection_equiv _root_.OAI.PolycyclicRecognition.NilpotentKernelCompletion.extendedAction_embed _root_.OAI.PolycyclicRecognition.derivationSemidirectHom_apply _root_.OAI.PolycyclicRecognition.polynomialCoordinateHom_apply _root_.OAI.PolycyclicRecognition.polynomialInnerLieEquiv_apply _root_.OAI.PolycyclicRecognition.polynomialModelLieEquiv_apply _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Smooth vector actions from commuting derivations -/

noncomputable section
namespace PolycyclicRecognition
attribute [local instance] LieRing.ofAssociativeRing
variable {L I : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L] [Fintype I]

omit [FiniteDimensional ℝ L] in
theorem derivationCombination_basis (D : I → LieDerivation ℝ L L) (i : I) :
    derivationCombination D ((Pi.basisFun ℝ I) i) = D i := by
  classical
  simp [derivationCombination, Pi.basisFun_apply]

theorem continuousLinear_derivationCombination (D : I → LieDerivation ℝ L L) (v : I → ℝ) :
    LinearMap.toContinuousLinearMap (derivationCombination D v).toLinearMap =
      ∑ i, v i • LinearMap.toContinuousLinearMap (D i).toLinearMap := by
  let f := (Module.End.toContinuousLinearMap (𝕜 := ℝ) L).toLinearMap.comp
    (LieDerivation.toLinearMapLieHom ℝ L).toLinearMap
  change f (∑ i, v i • D i) = _
  simp only [map_sum, map_smul]
  rfl

theorem contDiff_analyticDerivationCombination (D : I → LieDerivation ℝ L L) :
    ContDiff ℝ ⊤ (fun p : (I → ℝ) × L =>
      analyticDerivationExp (derivationCombination D p.1) p.2) := by
  have he : ContDiff ℝ ⊤ (NormedSpace.exp : (L →L[ℝ] L) → (L →L[ℝ] L)) :=
    contDiff_iff_contDiffAt.mpr fun x => (NormedSpace.exp_analytic (𝕂 := ℝ) x).contDiffAt
  have ht : ContDiff ℝ ⊤ (fun p : (I → ℝ) × L =>
      ∑ i, p.1 i • LinearMap.toContinuousLinearMap (D i).toLinearMap) :=
    ContDiff.sum fun i _ => ((contDiff_apply ℝ ℝ i).comp contDiff_fst).smul_const _
  simp only [analyticDerivationExp_apply, continuousLinear_derivationCombination]
  exact (he.comp ht).clm_apply contDiff_snd

namespace PolynomialExponentialCoordinates
variable [P : PolynomialExponentialCoordinates L]

theorem commutingDerivationAction_smooth (D : I → LieDerivation ℝ L L)
    (hD : ∀ i j, Commute (D i).toLinearMap (D j).toLinearMap) :
    ContDiff ℝ ⊤ (fun p : (I → ℝ) × L =>
      commutingDerivationAction (P := P) D hD (Multiplicative.ofAdd p.1) p.2) :=
  contDiff_analyticDerivationCombination D

end PolynomialExponentialCoordinates
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_CommutingNilpotentWords
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Compatibility with OpenAI's Mathlib (d13f23b): a lemma it has and ours lacks. -/

theorem List.prod_eq_pow_length {M : Type*} [Monoid M] (l : List M) (m : M) (h : ∀ x ∈ l, x = m) :
    l.prod = m ^ l.length := by
  rw [← List.prod_replicate, ← List.eq_replicate_iff.mpr ⟨rfl, h⟩]

namespace OAI

/-! # Uniform vanishing of words in finitely many commuting nilpotents -/

noncomputable section
namespace PolycyclicRecognition
variable {R : Type*} [Ring R]

theorem commuting_nilpotent_words_zero (ss : List R)
    (hpair : ∀ a ∈ ss, ∀ b ∈ ss, Commute a b) (hnil : ∀ a ∈ ss, IsNilpotent a) :
    ∃ c : ℕ, ∀ w : List R, (∀ a ∈ w, a ∈ ss) → c ≤ w.length → w.prod = 0 := by
  classical
  induction ss with
  | nil =>
    refine ⟨1, ?_⟩
    intro w hw hlen
    cases w with
    | nil => simp at hlen
    | cons x xs => exact False.elim (List.not_mem_nil (hw x (by simp)))
  | cons a ss ih =>
    obtain ⟨n, hn⟩ := hnil a (by simp)
    obtain ⟨m, hm⟩ := ih
      (fun x hx y hy => hpair x (by simp [hx]) y (by simp [hy]))
      (fun x hx => hnil x (by simp [hx]))
    refine ⟨n + m, ?_⟩
    intro w hw hlen
    let w₀ := w.filter (fun x => decide (x = a))
    let w₁ := w.filter (fun x => decide (x ≠ a))
    have hp : w.Perm (w₀ ++ w₁) := by
      simpa [w₀, w₁] using (List.filter_append_perm (fun x => decide (x = a)) w).symm
    have hc : w.Pairwise Commute := List.pairwise_of_forall_mem_list
      (fun x hx y hy => hpair x (hw x hx) y (hw y hy))
    have hprod := hp.prod_eq' hc
    rw [List.prod_append] at hprod
    have hw₀ : w₀.prod = a ^ w₀.length := List.prod_eq_pow_length _ _ (by
      intro x hx
      exact of_decide_eq_true (List.mem_filter.mp hx).2)
    rw [hw₀] at hprod
    rw [hprod]
    by_cases hlarge : n ≤ w₀.length
    · have hzero : a ^ w₀.length = 0 := by
        have he : w₀.length = n + (w₀.length - n) := by omega
        rw [he, pow_add, hn, zero_mul]
      rw [hzero, zero_mul]
    · have hlength := hp.length_eq
      rw [List.length_append] at hlength
      have hmle : m ≤ w₁.length := by omega
      have hw₁ : ∀ x ∈ w₁, x ∈ ss := by
        intro x hx
        obtain ⟨hxw, hxa⟩ := List.mem_filter.mp hx
        have hne : x ≠ a := of_decide_eq_true hxa
        exact (List.mem_cons.mp (hw x hxw)).resolve_left hne
      rw [hm w₁ hw₁ hmle, mul_zero]

theorem finite_commuting_nilpotent_action_filtration
    {K V I : Type*} [Field K] [AddCommGroup V] [Module K V] [Fintype I]
    (D : I → Module.End K V) (hcomm : ∀ i j, Commute (D i) (D j))
    (hnil : ∀ i, IsNilpotent (D i)) :
    ∃ c, linearActionFiltration D c = ⊥ := by
  classical
  let ss := (Finset.univ.toList.map D)
  have hss : ∀ x ∈ ss, ∃ i, x = D i := by
    intro x hx
    obtain ⟨i, _, hi⟩ := List.mem_map.mp hx
    exact ⟨i, hi.symm⟩
  obtain ⟨c, hc⟩ := commuting_nilpotent_words_zero ss
    (by intro x hx y hy; obtain ⟨i, rfl⟩ := hss x hx; obtain ⟨j, rfl⟩ := hss y hy; exact hcomm i j)
    (by intro x hx; obtain ⟨i, rfl⟩ := hss x hx; exact hnil i)
  refine ⟨c, linearActionFiltration_eq_bot_of_word_zero D c ?_⟩
  intro w hw
  apply hc (w.map D)
  · intro x hx
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
    exact List.mem_map.mpr ⟨i, by simp, rfl⟩
  · simpa only [List.length_map, hw] using (le_refl c)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_PolynomialProductParameters
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Transporting polynomial lattice parameters through an added real coordinate -/

noncomputable section
namespace PolycyclicRecognition
open Module

variable {U V W : Type*}
  [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  {d e k n : ℕ}

theorem IsPolynomialInBasis.add {b : Basis (Fin d) ℝ U} {c : Basis (Fin e) ℝ V}
    {f g : U → V} (hf : IsPolynomialInBasis b c f) (hg : IsPolynomialInBasis b c g) :
    IsPolynomialInBasis b c (fun x => f x + g x) := by
  simpa only [IsPolynomialInBasis, map_add] using IsCoordinatePolynomial.add hf hg

theorem IsPolynomialInBasis.prod {b : Basis (Fin d) ℝ U}
    {c : Basis (Fin e) ℝ V} {a : Basis (Fin k) ℝ W}
    (q : Basis (Fin n) ℝ (V × W))
    {f : U → V} {g : U → W}
    (hf : IsPolynomialInBasis b c f) (hg : IsPolynomialInBasis b a g) :
    IsPolynomialInBasis b q (fun x => (f x, g x)) := by
  have hl := (IsPolynomialInBasis.linear (b := c) (c := q) (LinearMap.inl ℝ V W)).comp hf
  have hr := (IsPolynomialInBasis.linear (b := a) (c := q) (LinearMap.inr ℝ V W)).comp hg
  simpa only [Function.comp_def, LinearMap.inl_apply, LinearMap.inr_apply,
    Prod.mk_add_mk, add_zero, zero_add] using hl.add hr

theorem polynomial_product_parameter (b : Basis (Fin d) ℝ V)
    (c : Basis (Fin e) ℝ (V × ℝ)) (p : V ≃ V)
    (hp : IsPolynomialInBasis b b p) :
    IsPolynomialInBasis c c (p.prodCongr (Equiv.refl ℝ)) := by
  have hf := hp.comp (IsPolynomialInBasis.linear (b := c) (c := b) (LinearMap.fst ℝ V ℝ))
  have hg := IsPolynomialInBasis.linear (b := c) (c := Module.finBasis ℝ ℝ)
    (LinearMap.snd ℝ V ℝ)
  exact hf.prod c hg

theorem polynomial_transported_product_parameter
    (b : Basis (Fin d) ℝ V) (c : Basis (Fin e) ℝ (V × ℝ))
    (a : Basis (Fin k) ℝ W)
    (p : V ≃ V) (s : W ≃ₗ[ℝ] (V × ℝ)) (E : W ≃ (V × ℝ))
    (hp : IsPolynomialInBasis b b p) (hq : IsPolynomialInBasis b b p.symm)
    (hE : IsPolynomialInBasis a c E) (hEi : IsPolynomialInBasis c a E.symm) :
    IsPolynomialInBasis a a (transportedProductParameter p s E) ∧
      IsPolynomialInBasis a a (transportedProductParameter p s E).symm := by
  constructor
  · exact (hEi.comp (polynomial_product_parameter b c p hp)).comp
      (IsPolynomialInBasis.linear s.toLinearMap)
  · exact ((IsPolynomialInBasis.linear s.symm.toLinearMap).comp
      (polynomial_product_parameter b c p.symm hq)).comp hE

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_CyclicParameterBasis
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A basis with the added time coordinate last -/

noncomputable section
namespace PolycyclicRecognition
open Module
variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] {d : ℕ}

theorem cyclicParameterBasis_integer (b : Basis (Fin d) ℝ V)
    (s : W ≃ₗ[ℝ] (V × ℝ)) (z : Fin (d + 1) → ℤ) :
    s ((cyclicParameterBasis b s).equivFun.symm (fun i => (z i : ℝ))) =
      (b.equivFun.symm (fun i => (z i.castSucc : ℝ)), (z (Fin.last d) : ℝ)) := by
  rw [cyclicParameterBasis, Basis.equivFun_ofEquivFun]
  exact s.apply_symm_apply _

theorem transportedProductParameter_integer
    (b : Basis (Fin d) ℝ V) (p : V ≃ V) (s : W ≃ₗ[ℝ] (V × ℝ))
    (E : W ≃ (V × ℝ)) (z : Fin (d + 1) → ℤ) :
    E (transportedProductParameter p s E
      ((cyclicParameterBasis b s).equivFun.symm (fun i => (z i : ℝ)))) =
      (p (b.equivFun.symm (fun i => (z i.castSucc : ℝ))), (z (Fin.last d) : ℝ)) := by
  change E (E.symm ((p.prodCongr (Equiv.refl ℝ))
    (s ((cyclicParameterBasis b s).equivFun.symm (fun i => (z i : ℝ)))))) = _
  rw [E.apply_symm_apply, cyclicParameterBasis_integer]
  rfl

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Lattices_IntegerTimeLattice
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The integer time lattice in the real one-parameter group -/

noncomputable section
namespace PolycyclicRecognition
open Set

theorem integerTimeLattice_mem (n : ℤ) :
    Multiplicative.ofAdd (n : ℝ) ∈ integerTimeLattice := by
  change (n : ℝ) ∈ AddSubgroup.zmultiples (1 : ℝ)
  exact AddSubgroup.mem_zmultiples_iff.mpr ⟨n, by simp⟩

theorem integerTimeLattice_exists {x : Multiplicative ℝ} (hx : x ∈ integerTimeLattice) :
    ∃ n : ℤ, x = Multiplicative.ofAdd (n : ℝ) := by
  change x.toAdd ∈ AddSubgroup.zmultiples (1 : ℝ) at hx
  obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.mp hx
  refine ⟨n, ?_⟩
  apply Multiplicative.ext
  simpa using hn.symm

theorem integerTimeLattice_uniform : IsUniformLattice integerTimeLattice := by
  have hd : DiscreteTopology integerTimeLattice := by
    change DiscreteTopology (AddSubgroup.zmultiples (1 : ℝ))
    infer_instance
  refine ⟨hd, Multiplicative.ofAdd '' Icc (0 : ℝ) 1,
    isCompact_Icc.image (show Continuous (Multiplicative.ofAdd : ℝ → Multiplicative ℝ)
      from continuous_id), ?_⟩
  intro x
  refine ⟨⟨Multiplicative.ofAdd (⌊x.toAdd⌋ : ℝ), integerTimeLattice_mem _⟩,
    Multiplicative.ofAdd (Int.fract x.toAdd), ?_, ?_⟩
  · exact ⟨Int.fract x.toAdd, ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩, rfl⟩
  · apply Multiplicative.ext
    change (⌊x.toAdd⌋ : ℝ) + (x.toAdd - (⌊x.toAdd⌋ : ℝ)) = x.toAdd
    abel

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Lattices_SemidirectUniformLattice
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform lattices in a semidirect product

The lattices in the two factors form a lattice whenever the acting lattice
preserves the first lattice. The compact cover uses the inverse action before
reducing the first coordinate.
-/

noncomputable section
namespace PolycyclicRecognition
open Set
variable {N D : Type*} [Group N] [Group D]
  [TopologicalSpace N] [TopologicalSpace D]
  (φ : D →* MulAut N) (Λ : Subgroup N) (Δ : Subgroup D)
  (hφ : ∀ d ∈ Δ, ∀ x ∈ Λ, φ d x ∈ Λ)

attribute [local instance] semidirectProductTopology

theorem semidirectLattice_discrete [DiscreteTopology Λ] [DiscreteTopology Δ] :
    DiscreteTopology (semidirectLattice φ Λ Δ hφ) := by
  let f : semidirectLattice φ Λ Δ hφ → Λ × Δ :=
    fun x => (⟨x.val.left, x.property.1⟩, ⟨x.val.right, x.property.2⟩)
  have hl := (continuous_semidirect_left φ).comp
    (continuous_subtype_val : Continuous (Subtype.val : semidirectLattice φ Λ Δ hφ → N ⋊[φ] D))
  have hr := (continuous_semidirect_right φ).comp
    (continuous_subtype_val : Continuous (Subtype.val : semidirectLattice φ Λ Δ hφ → N ⋊[φ] D))
  have hf : Continuous f := (hl.subtype_mk _).prodMk (hr.subtype_mk _)
  apply DiscreteTopology.of_continuous_injective hf
  intro x y h
  apply Subtype.ext
  apply SemidirectProduct.ext
  · exact congrArg (fun z : Λ × Δ => z.1.val) h
  · exact congrArg (fun z : Λ × Δ => z.2.val) h

theorem semidirectLattice_uniform (hΛ : IsUniformLattice Λ) (hΔ : IsUniformLattice Δ) :
    IsUniformLattice (semidirectLattice φ Λ Δ hφ) := by
  let := hΛ.1
  let := hΔ.1
  obtain ⟨K, hK, hcoverK⟩ := hΛ.2
  obtain ⟨F, hF, hcoverF⟩ := hΔ.2
  let e := semidirectProductHomeomorph φ
  refine ⟨semidirectLattice_discrete φ Λ Δ hφ,
    e.symm '' (K ×ˢ F), (hK.prod hF).image e.symm.continuous, ?_⟩
  intro g
  obtain ⟨δ, v, hv, hδ⟩ := hcoverF g.right
  obtain ⟨μ, u, hu, hμ⟩ := hcoverK (φ (δ.val⁻¹) g.left)
  let γ : semidirectLattice φ Λ Δ hφ :=
    ⟨⟨φ δ.val μ.val, δ.val⟩, hφ δ.val δ.property μ.val μ.property, δ.property⟩
  refine ⟨γ, ⟨u, v⟩, ⟨(u, v), ⟨hu, hv⟩, rfl⟩, ?_⟩
  apply SemidirectProduct.ext
  · change φ δ.val μ.val * φ δ.val u = g.left
    rw [← map_mul, hμ, map_inv]
    exact (φ δ.val).apply_symm_apply g.left
  · exact hδ

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Lattices_IntegerSemidirectLattice
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The integral semidirect product is the lattice in its real extension -/

noncomputable section
namespace PolycyclicRecognition
variable {H N : Type*} [Group H] [Group N]

theorem integerTimeHom_injective : Function.Injective integerTimeHom := by
  intro n m h
  apply Multiplicative.ext
  have he : (n.toAdd : ℝ) = (m.toAdd : ℝ) := congrArg Multiplicative.toAdd h
  exact_mod_cast he

theorem realIntegerSemidirectMap_injective
    (φ : Multiplicative ℝ →* MulAut N) (a : MulAut H)
    (e : H →* N) (he : ∀ x, e (a x) = φ (Multiplicative.ofAdd 1) (e x))
    (hej : Function.Injective e) : Function.Injective (realIntegerSemidirectMap φ a e he) := by
  intro x y h
  apply SemidirectProduct.ext
  · exact hej (congrArg SemidirectProduct.left h)
  · exact integerTimeHom_injective (congrArg SemidirectProduct.right h)

variable [TopologicalSpace N]
attribute [local instance] semidirectProductTopology

theorem integer_semidirect_lattice_realization_with_coordinates
    (φ : Multiplicative ℝ →* MulAut N) (a : MulAut H)
    (Λ : Subgroup N) (hΛ : IsUniformLattice Λ) (e : H ≃* Λ)
    (he : ∀ x, (e (a x) : N) = φ (Multiplicative.ofAdd 1) (e x)) :
    ∃ Γ : Subgroup (N ⋊[φ] Multiplicative ℝ), IsUniformLattice Γ ∧
      ∃ f : (H ⋊[integerPowerAction a] Multiplicative ℤ) ≃* Γ,
        ∀ x, (f x : N ⋊[φ] Multiplicative ℝ) =
          realIntegerSemidirectMap φ a (Λ.subtype.comp e.toMonoidHom) he x := by
  let j : H →* N := Λ.subtype.comp e.toMonoidHom
  have hstable : ∀ t ∈ integerTimeLattice, ∀ x ∈ Λ, φ t x ∈ Λ := by
    intro t ht x hx
    obtain ⟨n, rfl⟩ := integerTimeLattice_exists ht
    obtain ⟨y, hy⟩ := e.surjective ⟨x, hx⟩
    have hj : j y = x := congrArg Subtype.val hy
    rw [← hj, realAction_int, ← mulAut_zpow_semiconj a _ j he]
    exact (e ((a ^ n) y)).property
  let Γ := semidirectLattice φ Λ integerTimeLattice hstable
  let f := realIntegerSemidirectMap φ a j he
  have hf (x) : f x ∈ Γ := ⟨(e x.left).property, integerTimeLattice_mem x.right.toAdd⟩
  let f' : (H ⋊[integerPowerAction a] Multiplicative ℤ) →* Γ := f.codRestrict Γ hf
  have hinj : Function.Injective f' := by
    intro x y h
    exact realIntegerSemidirectMap_injective φ a j he
      (Λ.subtype_injective.comp e.injective) (congrArg Subtype.val h)
  have hsurj : Function.Surjective f' := by
    intro z
    obtain ⟨x, hx⟩ := e.surjective ⟨z.val.left, z.property.1⟩
    obtain ⟨n, hn⟩ := integerTimeLattice_exists z.property.2
    refine ⟨⟨x, Multiplicative.ofAdd n⟩, ?_⟩
    apply Subtype.ext
    apply SemidirectProduct.ext
    · exact congrArg Subtype.val hx
    · exact hn.symm
  exact ⟨Γ, semidirectLattice_uniform φ Λ integerTimeLattice hstable hΛ
    integerTimeLattice_uniform, MulEquiv.ofBijective f' ⟨hinj, hsurj⟩, fun _ => rfl⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_CyclicPowerIndex
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Compatibility with OpenAI's Mathlib (d13f23b): a lemma it has and ours lacks. -/

private theorem Subgroup.index_zpowers_zpow_p0 {G : Type*} [Group G] {g : G} (hg : Subgroup.zpowers g = ⊤)
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

/-! # Finite-index cyclic subgroups for an arbitrary positive power -/

noncomputable section
namespace PolycyclicRecognition
variable {H : Type} [Group H]

theorem integerScaleHom_range_finiteIndex {m : ℕ} (hm : 0 < m) :
    (integerScaleHom m).range.FiniteIndex := by
  let g := Multiplicative.ofAdd (1 : ℤ)
  have hg : Subgroup.zpowers g = ⊤ := by
    apply top_unique
    intro z _
    refine ⟨z.toAdd, ?_⟩
    apply Multiplicative.ext
    simp [g]
  have hr : (integerScaleHom m).range = Subgroup.zpowers (g ^ (m : ℤ)) := by
    rw [MonoidHom.range_eq_map, ← hg, MonoidHom.map_zpowers]
    congr 1
  refine ⟨?_⟩
  rw [hr, Subgroup.index_zpowers_zpow_p0 hg]
  exact ne_of_gt (Int.gcd_pos_of_ne_zero_left (orderOf g)
    (by exact_mod_cast Nat.ne_of_gt hm))

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

theorem relativeCommutatorSeries_add (K N : Subgroup G) (i j : ℕ) :
    relativeCommutatorSeries K N (i + j) =
      relativeCommutatorSeries K (relativeCommutatorSeries K N i) j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    change ⁅K, relativeCommutatorSeries K N (i + j)⁆ =
      ⁅K, relativeCommutatorSeries K (relativeCommutatorSeries K N i) j⁆
    rw [ih]

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_EndomorphismCommutatorFiltration
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The commutator-filtration bridge for linear endomorphism representations -/

noncomputable section
namespace PolycyclicRecognition
open scoped commutatorElement
variable {G V : Type} [Group G] [AddCommGroup V] [Module ℝ V]

theorem linearActionFiltration_comp_le {I J : Type*} (D : I → Module.End ℝ V)
    (f : J → I) (n : ℕ) : linearActionFiltration (D ∘ f) n ≤ linearActionFiltration D n := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    change (⨆ j, (linearActionFiltration (D ∘ f) n).map (D (f j))) ≤ _
    apply iSup_le
    intro j
    exact (Submodule.map_mono ih).trans (le_iSup
      (fun i => (linearActionFiltration D n).map (D i)) (f j))

theorem relativeCommutatorSeries_le_endFiltration
    (K N : Subgroup G) [N.Normal] (ρ : G →* Module.End ℝ V)
    (π : N →* Multiplicative V)
    (heq : ∀ g : G, ∀ a : N,
      (π (MulAut.conjNormal (H := N) g a)).toAdd = ρ g (π a).toAdd) (n : ℕ) :
    relativeCommutatorSeries K N n ≤
      (linearPreimageSubgroup π (linearActionFiltration
        (fun g : K => ρ g - 1) n)).map N.subtype := by
  let D := fun g : K => ρ g - 1
  induction n with
  | zero =>
    intro a ha
    refine ⟨⟨a, ha⟩, ?_, rfl⟩
    change (π ⟨a, ha⟩).toAdd ∈ (⊤ : Submodule ℝ V)
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

theorem relativeCommutatorSeries_le_kernel_of_endFiltration
    (K N : Subgroup G) [N.Normal] (ρ : G →* Module.End ℝ V)
    (π : N →* Multiplicative V)
    (heq : ∀ g : G, ∀ a : N,
      (π (MulAut.conjNormal (H := N) g a)).toAdd = ρ g (π a).toAdd)
    (c : ℕ) (hc : linearActionFiltration (fun g : K => ρ g - 1) c = ⊥) :
    relativeCommutatorSeries K N c ≤ π.ker.map N.subtype := by
  intro g hg
  obtain ⟨a, ha, rfl⟩ := relativeCommutatorSeries_le_endFiltration K N ρ π heq c hg
  refine ⟨a, ?_, rfl⟩
  change (π a).toAdd ∈ linearActionFiltration (fun g : K => ρ g - 1) c at ha
  rw [hc, Submodule.mem_bot] at ha
  change π a = 1
  exact Multiplicative.toAdd.injective ha

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_FactorExtensionTopology
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.JointFixedReductionData.residualLayer_normal _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Completing the kernel while retaining the discrete quotient -/

noncomputable section
namespace PolycyclicRecognition
open Filter Topology

theorem continuous_discrete_parameter {Q X Y : Type*}
    [TopologicalSpace Q] [DiscreteTopology Q] [TopologicalSpace X] [TopologicalSpace Y]
    (f : Q → X → Y) (hf : ∀ q, Continuous (f q)) :
    Continuous (fun p : Q × X => f p.1 p.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  have hq : ∀ᶠ q : Q in 𝓝 p.1, q = p.1 := by
    simp only [nhds_discrete, Filter.eventually_pure]
  have he : ∀ᶠ z : Q × X in 𝓝 p, z.1 = p.1 :=
    (continuous_fst.tendsto p).eventually hq
  apply ((hf p.1).continuousAt.comp continuous_snd.continuousAt).congr_of_eventuallyEq
  filter_upwards [he] with z hz
  rw [hz]
  rfl

variable {N Q : Type*} [Group N] [Group Q] [TopologicalSpace N] [TopologicalSpace Q]
  (S : NonabelianFactorSystem N Q)

attribute [local instance] factorExtensionTopology

theorem continuous_factor_left : Continuous (fun a : FactorExtension S => a.left) :=
  (factorExtensionHomeomorph S).continuous.fst

theorem continuous_factor_right : Continuous (fun a : FactorExtension S => a.right) :=
  (factorExtensionHomeomorph S).continuous.snd

theorem continuous_factor_inl : Continuous (FactorExtension.inl S) :=
  (factorExtensionHomeomorph S).symm.continuous.comp (continuous_id.prodMk continuous_const)

variable [IsTopologicalGroup N] [DiscreteTopology Q]

/-- Individual continuous kernel automorphisms suffice over a discrete quotient. -/
theorem factorExtensionTopologicalGroup (ha : ∀ q, Continuous (S.action q)) :
    IsTopologicalGroup (FactorExtension S) := by
  have hA : Continuous (fun p : Q × N => S.action p.1 p.2) :=
    continuous_discrete_parameter (fun q x => S.action q x) ha
  have hc : Continuous (fun p : Q × Q => S.factor p.1 p.2) := continuous_of_discreteTopology
  refine { continuous_mul := ?_, continuous_inv := ?_ }
  · apply continuous_induced_rng.2
    exact (((continuous_factor_left S).comp continuous_fst).mul
      (hA.comp (((continuous_factor_right S).comp continuous_fst).prodMk
        ((continuous_factor_left S).comp continuous_snd)))).mul
      (hc.comp (((continuous_factor_right S).comp continuous_fst).prodMk
        ((continuous_factor_right S).comp continuous_snd))) |>.prodMk
      (((continuous_factor_right S).comp continuous_fst).mul
        ((continuous_factor_right S).comp continuous_snd))
  · apply continuous_induced_rng.2
    exact ((hc.comp ((continuous_factor_right S).inv.prodMk
      (continuous_factor_right S))).inv.mul
      (hA.comp ((continuous_factor_right S).inv.prodMk
        (continuous_factor_left S).inv))).prodMk (continuous_factor_right S).inv

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_IntegralLinearExtension
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.abelianRealLatticeEquiv_apply _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Extending finite integral linear automorphisms to real coordinates -/

noncomputable section
namespace PolycyclicRecognition
open Module
variable {d e : ℕ}

theorem integerVectorMap_basis (i : Fin d) :
    integerVectorMap d ((Pi.basisFun ℤ (Fin d)) i) = (Pi.basisFun ℝ (Fin d)) i := by
  ext j
  by_cases h : i = j
  · subst j
    simp [integerVectorMap, Pi.basisFun_apply]
  · simp [integerVectorMap, Pi.basisFun_apply, Ne.symm h]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Lattices_IntegralLatticeGenerators
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.latticeNormalFlag_normal _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Coordinate generators and the standard embedding of the integral lattice -/

noncomputable section
namespace PolycyclicRecognition

theorem integralLatticeGenerator_prod (n : ℕ) (z : IntegralLatticeGroup n) :
    (∏ i, integralLatticeGenerator n i ^ z.toAdd i) = z := by
  apply Multiplicative.toAdd.injective
  simpa only [toAdd_prod, toAdd_zpow, integralLatticeGenerator, toAdd_ofAdd,
    Pi.basisFun_equivFun, LinearEquiv.refl_apply] using
    (Pi.basisFun ℤ (Fin n)).sum_equivFun z.toAdd

theorem integralLatticeGenerator_closure (n : ℕ) :
    Subgroup.closure (Set.range (integralLatticeGenerator n)) = ⊤ := by
  apply top_unique
  intro z _
  rw [← integralLatticeGenerator_prod n z]
  exact Subgroup.prod_mem _ fun i _ => Subgroup.zpow_mem _
    (Subgroup.subset_closure (Set.mem_range_self i)) _

theorem integralLattice_hom_ext {n : ℕ} {K : Type*} [Group K]
    {f g : IntegralLatticeGroup n →* K}
    (h : ∀ i, f (integralLatticeGenerator n i) = g (integralLatticeGenerator n i)) : f = g := by
  apply MonoidHom.eq_of_eqOn_dense (integralLatticeGenerator_closure n)
  rintro _ ⟨i, rfl⟩
  exact h i

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Lattices_IntegralLatticePowerIndex
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.latticeNormalFlag_normal _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
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

theorem latticePowerHom_range (n m : ℕ) :
    (latticePowerHom n m).range =
      ⨅ i, (integerScaleHom m).range.comap (latticeCoordinateHom n i) := by
  ext z
  simp only [Subgroup.mem_iInf, Subgroup.mem_comap, MonoidHom.mem_range]
  constructor
  · rintro ⟨w, rfl⟩ i
    exact ⟨Multiplicative.ofAdd (w.toAdd i), rfl⟩
  · intro h
    choose w hw using h
    refine ⟨Multiplicative.ofAdd (fun i => (w i).toAdd), ?_⟩
    apply Multiplicative.ext
    funext i
    exact congrArg Multiplicative.toAdd (hw i)

theorem latticePowerHom_finiteIndex (n : ℕ) {m : ℕ} (hm : 0 < m) :
    (latticePowerHom n m).range.FiniteIndex := by
  let := integerScaleHom_range_finiteIndex hm
  rw [latticePowerHom_range]
  apply Subgroup.finiteIndex_iInf
  intro i
  infer_instance

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_FactorSystemPullback
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.JointFixedReductionData.residualLayer_normal _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.latticeNormalFlag_normal _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Restriction of a factor system to a quotient homomorphism -/

noncomputable section
namespace PolycyclicRecognition
variable {N Q H : Type} [Group N] [Group Q] [Group H]
  (R : NonabelianFactorSystem N Q) (f : H →* Q)

theorem factorPullbackMap_injective (hf : Function.Injective f) :
    Function.Injective (factorPullbackMap R f) := by
  intro x y h
  apply FactorExtension.ext
  · exact congrArg (fun z : FactorExtension R => z.left) h
  · exact hf (congrArg (fun z : FactorExtension R => z.right) h)

theorem factorPullbackMap_range : (factorPullbackMap R f).range =
    f.range.comap (FactorExtension.projection R) := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a.right, rfl⟩
  · rintro ⟨h, hh⟩
    exact ⟨⟨x.left, h⟩, FactorExtension.ext rfl hh⟩

attribute [local instance] factorExtensionTopology
variable [TopologicalSpace N] [TopologicalSpace Q] [TopologicalSpace H]

theorem factorPullbackMap_isEmbedding (hf : Topology.IsEmbedding f) :
    Topology.IsEmbedding (factorPullbackMap R f) :=
  (factorExtensionHomeomorph R).symm.isEmbedding.comp
    ((Topology.IsEmbedding.id.prodMap hf).comp (factorExtensionHomeomorph (R.pullback f)).isEmbedding)

theorem factorPullbackMap_isClosedEmbedding (hf : Topology.IsClosedEmbedding f) :
    Topology.IsClosedEmbedding (factorPullbackMap R f) := by
  refine ⟨factorPullbackMap_isEmbedding R f hf.isEmbedding, ?_⟩
  change IsClosed ((factorPullbackMap R f).range : Set (FactorExtension R))
  rw [factorPullbackMap_range]
  exact hf.isClosed_range.preimage (continuous_factor_right R)

theorem factorPowerMap_isClosedEmbedding {n m : ℕ}
    (R : NonabelianFactorSystem N (IntegralLatticeGroup n)) (hm : 0 < m) :
    Topology.IsClosedEmbedding (factorPullbackMap R (latticePowerHom n m)) := by
  let e := MonoidHom.ofInjective (latticePowerHom_injective n hm)
  let h : IntegralLatticeGroup n ≃ₜ (latticePowerHom n m).range :=
    { e.toEquiv with
      continuous_toFun := continuous_of_discreteTopology
      continuous_invFun := continuous_of_discreteTopology }
  apply factorPullbackMap_isClosedEmbedding
  exact ⟨Topology.IsEmbedding.subtypeVal.comp h.isEmbedding, isClosed_discrete _⟩

omit [TopologicalSpace N] in
theorem factorPowerMap_finiteIndex {n m : ℕ}
    (R : NonabelianFactorSystem N (IntegralLatticeGroup n)) (hm : 0 < m) :
    (factorPullbackMap R (latticePowerHom n m)).range.FiniteIndex := by
  let := latticePowerHom_finiteIndex n hm
  rw [factorPullbackMap_range]
  infer_instance

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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_GaugeComposition
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instLocallyCompactSpaceFactorExtension _root_.OAI.PolycyclicRecognition.instT2SpaceFactorExtension _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Composing explicit section corrections -/

namespace PolycyclicRecognition
variable {N Q : Type*} [Group N] [Group Q]

theorem gauge_gauge_factor (F : NonabelianFactorSystem N Q)
    (b c : Q → N) (hb : b 1 = 1) (hc : c 1 = 1)
    (hcb : c 1 * b 1 = 1) (q r : Q) :
    ((F.gauge b hb).gauge c hc).factor q r =
      (F.gauge (fun q => c q * b q) hcb).factor q r := by
  change c q * (b q * F.action q (c r) * (b q)⁻¹) *
    (b q * F.action q (b r) * F.factor q r * (b (q * r))⁻¹) * (c (q * r))⁻¹ =
      (c q * b q) * F.action q (c r * b r) * F.factor q r * (c (q * r) * b (q * r))⁻¹
  rw [map_mul]
  group

theorem gauge_gauge_action (F : NonabelianFactorSystem N Q)
    (b c : Q → N) (hb : b 1 = 1) (hc : c 1 = 1)
    (hcb : c 1 * b 1 = 1) (q : Q) (x : N) :
    ((F.gauge b hb).gauge c hc).action q x =
      (F.gauge (fun q => c q * b q) hcb).action q x := by
  change c q * (b q * F.action q x * (b q)⁻¹) * (c q)⁻¹ =
    (c q * b q) * F.action q x * (c q * b q)⁻¹
  group

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_GaugeFactorSymmetry
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instLocallyCompactSpaceFactorExtension _root_.OAI.PolycyclicRecognition.instT2SpaceFactorExtension _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Symmetries retained when correcting a factor system -/

namespace PolycyclicRecognition
variable {N Q : Type*} [Group N] [Group Q]

theorem gauge_factor_fixed (F : NonabelianFactorSystem N Q) (b : Q → N) (hb : b 1 = 1)
    (T : N →* N) (hact : ∀ q x, T (F.action q x) = F.action q (T x))
    (hfactor : ∀ q r, T (F.factor q r) = F.factor q r) (hTb : ∀ q, T (b q) = b q)
    (q r : Q) : T ((F.gauge b hb).factor q r) = (F.gauge b hb).factor q r := by
  change T (b q * F.action q (b r) * F.factor q r * (b (q * r))⁻¹) =
    b q * F.action q (b r) * F.factor q r * (b (q * r))⁻¹
  rw [map_mul, map_mul, map_mul, map_inv, hTb, hTb, hact, hTb, hfactor]

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_FiniteSemisimpleCocycleReduction
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.JointFixedReductionData.residualLayer_normal _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.abelianRealCoordinates _root_.OAI.PolycyclicRecognition.abelianRealFiniteDimensional _root_.OAI.PolycyclicRecognition.abelianRealLieAbelian _root_.OAI.PolycyclicRecognition.abelianRealNormedLie _root_.OAI.PolycyclicRecognition.derivationLieSpaceFiniteDimensional _root_.OAI.PolycyclicRecognition.derivationLieSpaceRealNormed _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instLocallyCompactSpaceFactorExtension _root_.OAI.PolycyclicRecognition.instT2SpaceFactorExtension _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.polynomialLieIdealSubgroup_normal _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.JointFixedReductionData.residualLayerProjection_equiv _root_.OAI.PolycyclicRecognition.NilpotentKernelCompletion.extendedAction_embed _root_.OAI.PolycyclicRecognition.NilpotentLatticeCoordinates.automorphism_mul _root_.OAI.PolycyclicRecognition.NilpotentLatticeCoordinates.automorphism_on_lattice _root_.OAI.PolycyclicRecognition.NilpotentLatticeCoordinates.automorphism_one _root_.OAI.PolycyclicRecognition.PolynomialExponentialCoordinates.analyticDerivationAction_apply _root_.OAI.PolycyclicRecognition.abelianRealLatticeEquiv_apply _root_.OAI.PolycyclicRecognition.analyticDerivationExp_apply _root_.OAI.PolycyclicRecognition.derivationSemidirectHom_apply _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.polynomialCoordinateHom_apply _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

namespace OAI

/-! # Removing all moving components for a finite semisimple family

Each correction is central and fixes every component already dealt with.
Their product is one normalized gauge for the original factor system.
-/

noncomputable section
namespace PolycyclicRecognition
open scoped IsMulCommutative
variable {L Q : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L] [LieRing.IsNilpotent L]
  [Group Q] [IsMulCommutative Q]

theorem finite_semisimple_cocycle_reduction (F : NonabelianFactorSystem L Q)
    (A : Q → L ≃ₗ⁅ℝ⁆ L) (hact : ∀ q x, F.action q x = A q x)
    (ss : List (L ≃ₗ⁅ℝ⁆ L))
    (hss : ∀ S ∈ ss, Module.End.IsSemisimple S.toLinearMap)
    (hpair : ∀ S ∈ ss, ∀ T ∈ ss, Commute S.toLinearMap T.toLinearMap)
    (hcomm : ∀ S ∈ ss, ∀ q, Commute S.toLinearMap (A q).toLinearMap)
    (hlift : ∀ S ∈ ss, ∃ q₀ : Q, ∃ U : L ≃ₗ⁅ℝ⁆ L,
      IsNilpotent (U.toLinearMap - 1) ∧ Commute S.toLinearMap U.toLinearMap ∧
      (A q₀).toLinearMap = S.toLinearMap * U.toLinearMap) :
    ∃ b : Q → L, ∃ hb : b 1 = 1,
      (∀ q, b q ∈ Subgroup.center L) ∧
      (∀ q x, (F.gauge b hb).action q x = F.action q x) ∧
      ∀ S ∈ ss, ∀ q r, S ((F.gauge b hb).factor q r) = (F.gauge b hb).factor q r := by
  induction ss with
  | nil =>
    refine ⟨fun _ => 1, rfl, fun _ => (Subgroup.center L).one_mem, ?_, by simp⟩
    intro q x
    change (1 : L) * F.action q x * (1 : L)⁻¹ = F.action q x
    simp
  | cons S ss ih =>
    obtain ⟨b, hb, hbZ, hbA, hbfix⟩ := ih
      (fun T hT => hss T (List.mem_cons_of_mem S hT))
      (fun T hT R hR => hpair T (List.mem_cons_of_mem S hT) R (List.mem_cons_of_mem S hR))
      (fun T hT => hcomm T (List.mem_cons_of_mem S hT))
      (fun T hT => hlift T (List.mem_cons_of_mem S hT))
    let F₁ := F.gauge b hb
    have hA₁ : ∀ q x, F₁.action q x = A q x := fun q x => (hbA q x).trans (hact q x)
    obtain ⟨q₀, U, hU, hSU, hAU⟩ := hlift S (by simp)
    obtain ⟨c, hc, hcZ, hcA, hcS, hcT⟩ := ambient_semisimple_cocycle_reduction
      F₁ A hA₁ S (hss S (by simp)) (hcomm S (by simp)) q₀ U hU hSU hAU
    have hcb : c 1 * b 1 = 1 := by rw [hc, hb, one_mul]
    refine ⟨fun q => c q * b q, hcb, fun q => (Subgroup.center L).mul_mem (hcZ q) (hbZ q),
      ?_, ?_⟩
    · intro q x
      rw [← gauge_gauge_action F b c hb hc hcb]
      exact (hcA q x).trans (hbA q x)
    · intro T hT q r
      rw [← gauge_gauge_factor F b c hb hc hcb]
      rcases List.mem_cons.mp hT with hT | hT
      · subst T
        exact hcS q r
      · have hcfix : ∀ t, T (c t) = c t := hcT T
          (hpair S (by simp) T (List.mem_cons_of_mem S hT))
          (hcomm T (List.mem_cons_of_mem S hT)) (hbfix T hT)
        let t := PolynomialExponentialCoordinates.groupAutomorphism (P := P) T
        have hTa : ∀ q x, t (F₁.action q x) = F₁.action q (t x) := by
          intro q x
          change T (F₁.action q x) = F₁.action q (T x)
          rw [hA₁, hA₁]
          exact LinearMap.congr_fun (hcomm T (List.mem_cons_of_mem S hT) q).eq x
        exact gauge_factor_fixed F₁ c hc t.toMonoidHom hTa (hbfix T hT) hcfix q r

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_InnerCorrectedJordanFactor
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.JointFixedReductionData.residualLayer_normal _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.abelianRealCoordinates _root_.OAI.PolycyclicRecognition.abelianRealFiniteDimensional _root_.OAI.PolycyclicRecognition.abelianRealLieAbelian _root_.OAI.PolycyclicRecognition.abelianRealNormedLie _root_.OAI.PolycyclicRecognition.derivationLieSpaceFiniteDimensional _root_.OAI.PolycyclicRecognition.derivationLieSpaceRealNormed _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.polynomialLieIdealSubgroup_normal _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A correction fixed by the semisimple factor preserves that factor -/

noncomputable section
namespace PolycyclicRecognition
variable {L : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [C : PolynomialExponentialCoordinates L] [LieRing.IsNilpotent L]

theorem inner_correction_preserves_jordan_factor (A S U : L ≃ₗ⁅ℝ⁆ L)
    (hU : IsNilpotent (U.toLinearMap - 1))
    (hSU : Commute S.toLinearMap U.toLinearMap)
    (hA : A.toLinearMap = S.toLinearMap * U.toLinearMap)
    (v : L) (hSv : S v = v) :
    ∃ W : L ≃ₗ⁅ℝ⁆ L, IsNilpotent (W.toLinearMap - 1) ∧
      Commute S.toLinearMap W.toLinearMap ∧
      (polynomialInnerLieEquiv v).toLinearMap * A.toLinearMap = S.toLinearMap * W.toLinearMap := by
  let W := U.trans (polynomialInnerLieEquiv v)
  have hW (x : L) : W x = v * U x * v⁻¹ := polynomialInnerLieEquiv_apply v (U x)
  let s := PolynomialExponentialCoordinates.groupAutomorphism (P := C) S
  have hnatural (x : L) : S (v * x * v⁻¹) = v * S x * v⁻¹ := by
    change s (v * x * v⁻¹) = v * s x * v⁻¹
    rw [map_mul, map_mul, map_inv]
    change S v * S x * (S v)⁻¹ = v * S x * v⁻¹
    rw [hSv]
  refine ⟨W, polynomial_inner_mul_unipotent U hU v, ?_, ?_⟩
  · apply LinearMap.ext
    intro x
    change S (W x) = W (S x)
    rw [hW, hW, hnatural]
    have hh : S (U x) = U (S x) := LinearMap.congr_fun hSU.eq x
    rw [hh]
  · apply LinearMap.ext
    intro x
    change polynomialInnerLieEquiv v (A x) = S (W x)
    rw [hW, hnatural, polynomialInnerLieEquiv_apply]
    have hh : A x = S (U x) := LinearMap.congr_fun hA x
    rw [hh]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_FiniteSemisimpleLiftFamily
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.JointFixedReductionData.residualLayer_normal _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.abelianRealCoordinates _root_.OAI.PolycyclicRecognition.abelianRealFiniteDimensional _root_.OAI.PolycyclicRecognition.abelianRealLieAbelian _root_.OAI.PolycyclicRecognition.abelianRealNormedLie _root_.OAI.PolycyclicRecognition.derivationLieSpaceFiniteDimensional _root_.OAI.PolycyclicRecognition.derivationLieSpaceRealNormed _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.polynomialLieIdealSubgroup_normal _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.JointFixedReductionData.residualLayerProjection_equiv _root_.OAI.PolycyclicRecognition.NilpotentKernelCompletion.extendedAction_embed _root_.OAI.PolycyclicRecognition.NilpotentLatticeCoordinates.automorphism_mul _root_.OAI.PolycyclicRecognition.NilpotentLatticeCoordinates.automorphism_on_lattice _root_.OAI.PolycyclicRecognition.NilpotentLatticeCoordinates.automorphism_one _root_.OAI.PolycyclicRecognition.PolynomialExponentialCoordinates.analyticDerivationAction_apply _root_.OAI.PolycyclicRecognition.abelianRealLatticeEquiv_apply _root_.OAI.PolycyclicRecognition.analyticDerivationExp_apply _root_.OAI.PolycyclicRecognition.derivationSemidirectHom_apply _root_.OAI.PolycyclicRecognition.polynomialCoordinateHom_apply _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

namespace OAI

/-! # A finite commuting semisimple family adapted to quotient generators

Successive inner corrections preserve the earlier semisimple factors. Every
member of a finite list in the abelian quotient therefore has a lift in one
common centralizer, with its semisimple factor belonging to that family.
-/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold ContDiff IsMulCommutative
variable {L G Q : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [C : PolynomialExponentialCoordinates L] [LieRing.IsNilpotent L]
  [Group G] [Group Q]

omit [LieRing.IsNilpotent L] in
theorem extension_conjugationLinear_inl_mul (E : GroupExtension L G Q)
    (hsmooth : ∀ g : G, ContMDiff (𝓘(ℝ, L)) (𝓘(ℝ, L)) ∞ (E.conjAct g)) (v : L) (g : G) :
    (polynomialModelLieEquiv (E.conjAct (E.inl v * g)) (hsmooth _)).toLinearMap =
      (polynomialInnerLieEquiv v).toLinearMap *
        (polynomialModelLieEquiv (E.conjAct g) (hsmooth g)).toLinearMap := by
  apply LinearMap.ext
  intro x
  change polynomialModelLieEquiv (E.conjAct (E.inl v * g)) (hsmooth _) x =
    polynomialInnerLieEquiv v (polynomialModelLieEquiv (E.conjAct g) (hsmooth g) x)
  rw [polynomialModelLieEquiv_apply, polynomialModelLieEquiv_apply,
    polynomialInnerLieEquiv_apply, map_mul, extension_conjAct_inl]
  rfl

theorem HasSemisimpleLift.extend {E : GroupExtension L G Q}
    {hsmooth : ∀ g : G, ContMDiff (𝓘(ℝ, L)) (𝓘(ℝ, L)) ∞ (E.conjAct g)}
    {ss : List (L ≃ₗ⁅ℝ⁆ L)} {q : Q} (hq : HasSemisimpleLift E hsmooth ss q)
    (S : L ≃ₗ⁅ℝ⁆ L)
    (hc : ∀ g ∈ commonSemisimpleCentralizer E ss, ∃ v : L,
      (∀ T ∈ ss, T v = v) ∧ E.inl v * g ∈ commonSemisimpleCentralizer E (S :: ss)) :
    HasSemisimpleLift E hsmooth (S :: ss) q := by
  obtain ⟨g, hg, hgq, T, hT, U, hU, hTU, hA⟩ := hq
  obtain ⟨v, hv, hvg⟩ := hc g hg
  obtain ⟨W, hW, hTW, he⟩ := inner_correction_preserves_jordan_factor
    (polynomialModelLieEquiv (E.conjAct g) (hsmooth g)) T U hU hTU hA v (hv T hT)
  refine ⟨E.inl v * g, hvg, ?_, T, List.mem_cons_of_mem S hT, W, hW, hTW, ?_⟩
  · rw [map_mul, E.rightHom_inl, one_mul, hgq]
  · rw [extension_conjugationLinear_inl_mul]
    exact he

variable [IsMulCommutative Q]

theorem exists_finite_semisimple_lift_family (E : GroupExtension L G Q)
    (hsmooth : ∀ g : G, ContMDiff (𝓘(ℝ, L)) (𝓘(ℝ, L)) ∞ (E.conjAct g)) (qs : List Q) :
    ∃ ss : List (L ≃ₗ⁅ℝ⁆ L),
      (∀ T ∈ ss, Module.End.IsSemisimple T.toLinearMap) ∧
      (∀ T ∈ ss, ∀ R ∈ ss, Commute T.toLinearMap R.toLinearMap) ∧
      Function.Surjective (E.rightHom.comp (commonSemisimpleCentralizer E ss).subtype) ∧
      ∀ q ∈ qs, HasSemisimpleLift E hsmooth ss q := by
  induction qs with
  | nil =>
    refine ⟨[], by simp, by simp, ?_, by simp⟩
    intro q
    obtain ⟨g, hg⟩ := E.rightHom_surjective q
    exact ⟨⟨g, (mem_commonSemisimpleCentralizer E [] g).mpr (by simp)⟩, hg⟩
  | cons q qs ih =>
    obtain ⟨ss, hss, hpair, hsurj, hlifts⟩ := ih
    obtain ⟨t, htq⟩ := hsurj q
    obtain ⟨S, U, hS, hU, hSU, hA, hTS, hc⟩ :=
      common_semisimpleCentralizer_step E hsmooth ss hss hpair t t.property
    have hnewss : ∀ T ∈ S :: ss, Module.End.IsSemisimple T.toLinearMap := by
      intro T hT
      rcases List.mem_cons.mp hT with h | h
      · subst T; exact hS
      · exact hss T h
    have hnewpair : ∀ T ∈ S :: ss, ∀ R ∈ S :: ss, Commute T.toLinearMap R.toLinearMap := by
      intro T hT R hR
      rcases List.mem_cons.mp hT with hT | hT <;> rcases List.mem_cons.mp hR with hR | hR
      · subst T; subst R; exact Commute.refl _
      · subst T; exact (hTS R hR).symm
      · subst R; exact hTS T hT
      · exact hpair T hT R hR
    have hnewsurj : Function.Surjective
        (E.rightHom.comp (commonSemisimpleCentralizer E (S :: ss)).subtype) := by
      intro r
      obtain ⟨g, hgr⟩ := hsurj r
      obtain ⟨v, _, hv⟩ := hc g g.property
      refine ⟨⟨E.inl v * g, hv⟩, ?_⟩
      change E.rightHom (E.inl v * g) = r
      rw [map_mul, E.rightHom_inl, one_mul]
      exact hgr
    have htnew : (t : G) ∈ commonSemisimpleCentralizer E (S :: ss) := by
      apply (mem_commonSemisimpleCentralizer E (S :: ss) t).mpr
      intro T hT
      rcases List.mem_cons.mp hT with h | h
      · subst T
        apply (mem_semisimpleActionCentralizer_iff E S t (hsmooth t)).mpr
        rw [hA]
        exact (Commute.refl _).mul_right hSU
      · exact (mem_commonSemisimpleCentralizer E ss t).mp t.property T h
    refine ⟨S :: ss, hnewss, hnewpair, hnewsurj, ?_⟩
    intro r hr
    rcases List.mem_cons.mp hr with hr | hr
    · subst r
      exact ⟨t, htnew, htq, S, by simp, U, hU, hSU, hA⟩
    · exact (hlifts r hr).extend S hc

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_FixedVectorLieLogarithm
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.JointFixedReductionData.residualLayer_normal _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.abelianRealFiniteDimensional _root_.OAI.PolycyclicRecognition.abelianRealLieAbelian _root_.OAI.PolycyclicRecognition.abelianRealNormedLie _root_.OAI.PolycyclicRecognition.derivationLieSpaceFiniteDimensional _root_.OAI.PolycyclicRecognition.derivationLieSpaceRealNormed _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.polynomialLieIdealSubgroup_normal _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The chosen Lie logarithm vanishes on fixed vectors

The compatible spectral character has value zero at the identity. This
retains the quotient directions when extending the integral nilshadow action.
-/

noncomputable section
namespace PolycyclicRecognition
open scoped TensorProduct

section Complex
variable {L : Type} [ComplexNormedLieAlgebra L] [FiniteDimensional ℂ L] [CompleteSpace L]

omit [FiniteDimensional ℂ L] [CompleteSpace L] in
theorem spectralLogValue_one (S : Module.End ℂ L)
    (l : spectralUnitGroup S →* Multiplicative ℂ) : spectralLogValue S l 1 = 0 := by
  have h := spectralLogValue_unit S l (1 : spectralUnitGroup S)
  simpa only [OneMemClass.coe_one, Units.val_one, map_one, toAdd_one] using h

omit [CompleteSpace L] in
theorem spectralLieDerivation_fixed (S : L ≃ₗ⁅ℂ⁆ L)
    (hS : Module.End.IsSemisimple S.toLinearMap)
    (l : spectralUnitGroup S.toLinearMap →* Multiplicative ℂ) (x : L) (hx : S x = x) :
    spectralLieDerivation S hS l x = 0 := by
  have hx' : x ∈ Module.End.eigenspace S.toLinearMap 1 := by
    rw [Module.End.mem_eigenspace_iff, one_smul]
    exact hx
  change semisimpleSpectralOperator S.toLinearMap hS
    (spectralLogValue S.toLinearMap l) x = 0
  rw [semisimpleSpectralOperator_apply _ _ _ hx', spectralLogValue_one, zero_smul]

theorem semisimple_real_form_has_fixed_power_log (S : L ≃ₗ⁅ℂ⁆ L)
    (hS : Module.End.IsSemisimple S.toLinearMap)
    (c : L →ₗ⋆[ℂ] L) (hc : ∀ x, c (S x) = S (c x)) :
    ∃ m : ℕ, 0 < m ∧ ∃ D : LieDerivation ℂ L L,
      (NormedSpace.exp (LinearMap.toContinuousLinearMap D.toLinearMap)).toLinearMap =
        S.toLinearMap ^ m ∧ (∀ x, c (D x) = D (c x)) ∧
      (∀ T : Module.End ℂ L, Commute S.toLinearMap T → Commute D.toLinearMap T) ∧
      ∀ x, S x = x → D x = 0 := by
  obtain ⟨m, hm, l, he, hr⟩ := spectralUnitGroup_logarithm S.toLinearMap
  exact ⟨m, hm, spectralLieDerivation S hS l,
    exp_compatibleSpectralLog S.toLinearMap hS ((Module.End.isUnit_iff _).mpr S.bijective) l m he,
    compatibleSpectralLog_conjugation S.toLinearMap hS l hr c hc,
    fun T hT => semisimpleSpectralOperator_commute S.toLinearMap hS _ T hT,
    spectralLieDerivation_fixed S hS l⟩

end Complex

section Real
variable {L : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]

attribute [local instance] OAI.PolycyclicRecognition.fixedVectorLogRationalModule
local instance q145LieRatGeometryFixedVectorLieLogarithm_rf5d5e9_1 : LieAlgebra ℚ L where
  lie_smul t x y := lie_smul (algebraMap ℚ ℝ t) x y
theorem real_semisimple_has_fixed_power_log (S : L ≃ₗ⁅ℝ⁆ L)
    (hS : Module.End.IsSemisimple S.toLinearMap) :
    ∃ m : ℕ, 0 < m ∧ ∃ D : LieDerivation ℝ L L,
      (NormedSpace.exp (LinearMap.toContinuousLinearMap D.toLinearMap)).toLinearMap =
        S.toLinearMap ^ m ∧
      (∀ T : Module.End ℝ L, Commute S.toLinearMap T → Commute D.toLinearMap T) ∧
      ∀ x, S x = x → D x = 0 := by
  let : ComplexNormedLieAlgebra (ℂ ⊗[ℝ] L) := complexificationNormedLie L
  let CS := complexifiedLieEquiv L S
  obtain ⟨m, hm, D, he, hc, hcomm, hfixed⟩ := semisimple_real_form_has_fixed_power_log CS
    (complexifiedLieEquiv_semisimple L S hS) (complexificationConjSemilinear L)
    (complexifiedLieEquiv_conj L S)
  refine ⟨m, hm, complexDerivationRealPart L D, ?_, ?_, ?_⟩
  · apply realEnd_baseChange_injective L
    change ((NormedSpace.exp (LinearMap.toContinuousLinearMap
        (complexDerivationRealPart L D).toLinearMap)).toLinearMap).baseChange ℂ =
      (S.toLinearMap ^ m).baseChange ℂ
    rw [complexifiedEnd_exp, complexDerivationRealPart_baseChange L D hc, he,
      LinearMap.baseChange_pow]
    rfl
  · intro T hT
    let f := Module.End.baseChangeHom ℝ ℂ L
    have ht : Commute D.toLinearMap (T.baseChange ℂ) := hcomm _ (hT.map f)
    apply realEnd_baseChange_injective L
    change f ((complexDerivationRealPart L D).toLinearMap * T) =
      f (T * (complexDerivationRealPart L D).toLinearMap)
    simp only [map_mul]
    change (complexDerivationRealPart L D).toLinearMap.baseChange ℂ * T.baseChange ℂ =
      T.baseChange ℂ * (complexDerivationRealPart L D).toLinearMap.baseChange ℂ
    rw [complexDerivationRealPart_baseChange L D hc]
    exact ht.eq
  · intro x hx
    apply complexificationLieHom_injective L
    change (1 : ℂ) ⊗ₜ[ℝ] complexDerivationRealPart L D x = (1 : ℂ) ⊗ₜ[ℝ] (0 : L)
    rw [complexDerivationRealPart_embed L D hc, TensorProduct.tmul_zero]
    apply hfixed
    change (1 : ℂ) ⊗ₜ[ℝ] S x = (1 : ℂ) ⊗ₜ[ℝ] x
    rw [hx]

omit [FiniteDimensional ℝ L] in
theorem lie_jordan_fixed (A S U : L ≃ₗ⁅ℝ⁆ L)
    (hS : Module.End.IsSemisimple S.toLinearMap)
    (hU : IsNilpotent (U.toLinearMap - 1)) (hSU : Commute S.toLinearMap U.toLinearMap)
    (hA : A.toLinearMap = S.toLinearMap * U.toLinearMap) (x : L) (hx : A x = x) :
    S x = x ∧ U x = x := by
  have hc : Commute A.toLinearMap S.toLinearMap := by
    rw [hA]
    exact (Commute.refl _).mul_left hSU.symm
  have hn : IsNilpotent (A.toLinearMap - S.toLinearMap) := by
    rw [hA, show S.toLinearMap * U.toLinearMap - S.toLinearMap =
      S.toLinearMap * (U.toLinearMap - 1) by noncomm_ring]
    obtain ⟨k, hk⟩ := hU
    exact ⟨k, by rw [(hSU.sub_right (Commute.one_right _)).mul_pow, hk, mul_zero]⟩
  have hx' : x ∈ Module.End.genEigenspace A.toLinearMap 1 1 := by
    rw [Module.End.genEigenspace_one]
    simp only [LinearMap.mem_ker, LinearMap.sub_apply,
      one_smul, Module.End.one_apply]
    exact sub_eq_zero.mpr hx
  have hs : S x = x := by
    have h := Module.End.apply_eq_of_mem_of_comm_of_isFinitelySemisimple_of_isNil
      hx' hc hS.isFinitelySemisimple hn
    change S x = (1 : ℝ) • x at h
    simpa only [one_smul] using h
  refine ⟨hs, S.injective ?_⟩
  have ha := LinearMap.congr_fun hA x
  change A x = S (U x) at ha
  exact ha.symm.trans (hx.trans hs.symm)

theorem unipotentLieLogarithm_fixed (A : L ≃ₗ⁅ℝ⁆ L)
    (hA : IsNilpotent (A.toLinearMap - 1)) (x : L) (hx : A x = x) :
    unipotentLieLogarithm A hA x = 0 := by
  change nilpotentLog (A.toLinearMap - 1) x = 0
  unfold nilpotentLog
  rw [finiteNilpotentLog_sum]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply]
  apply Finset.sum_eq_zero
  intro i _
  have hz : (A.toLinearMap - 1) x = 0 := by
    change A x - x = 0
    rw [hx, sub_self]
  have hp : ((A.toLinearMap - 1) ^ (i.val + 1)) x = 0 := by
    rw [pow_succ, Module.End.mul_apply, hz, map_zero]
  rw [hp, smul_zero]

end Real
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_FixedPowerLogarithms
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.JointFixedReductionData.residualLayer_normal _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.abelianRealFiniteDimensional _root_.OAI.PolycyclicRecognition.abelianRealLieAbelian _root_.OAI.PolycyclicRecognition.abelianRealNormedLie _root_.OAI.PolycyclicRecognition.derivationLieSpaceFiniteDimensional _root_.OAI.PolycyclicRecognition.derivationLieSpaceRealNormed _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.polynomialLieIdealSubgroup_normal _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.JointFixedReductionData.residualLayerProjection_equiv _root_.OAI.PolycyclicRecognition.NilpotentKernelCompletion.extendedAction_embed _root_.OAI.PolycyclicRecognition.PolynomialExponentialCoordinates.analyticDerivationAction_apply _root_.OAI.PolycyclicRecognition.PolynomialExponentialCoordinates.derivationAction_apply _root_.OAI.PolycyclicRecognition.PolynomialExponentialCoordinates.groupAutomorphism_apply _root_.OAI.PolycyclicRecognition.analyticDerivationExp_apply _root_.OAI.PolycyclicRecognition.derivationSemidirectHom_apply _root_.OAI.PolycyclicRecognition.polynomialCoordinateHom_apply _root_.OAI.PolycyclicRecognition.polynomialInnerLieEquiv_apply _root_.OAI.PolycyclicRecognition.polynomialModelLieEquiv_apply _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Commuting real logarithms retaining the fixed directions -/

noncomputable section
namespace PolycyclicRecognition
variable {L : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]

attribute [local instance] OAI.PolycyclicRecognition.fixedPowerLogRationalModule
local instance q145LieRatAlgebraFixedPowerLogarithms_rf5d5e9_1 : LieAlgebra ℚ L where
  lie_smul t x y := lie_smul (algebraMap ℚ ℝ t) x y
theorem real_lie_automorphism_has_fixed_power_log (A : L ≃ₗ⁅ℝ⁆ L) :
    ∃ m : ℕ, 0 < m ∧ ∃ D : LieDerivation ℝ L L,
      (NormedSpace.exp (LinearMap.toContinuousLinearMap D.toLinearMap)).toLinearMap =
        A.toLinearMap ^ m ∧
      (∀ T : Module.End ℝ L, Commute A.toLinearMap T → Commute D.toLinearMap T) ∧
      ∀ x, A x = x → D x = 0 := by
  obtain ⟨S, U, hS, hU, hSU, hA, hcentral⟩ := real_lie_jordan_decomposition_centralizer A
  obtain ⟨m, hm, B, hB, hcomm, hfixed⟩ := real_semisimple_has_fixed_power_log S hS
  let C := unipotentLieLogarithm U hU
  let b : Module.End ℝ L := B.toLinearMap
  let c : Module.End ℝ L := C.toLinearMap
  let E := Module.End.toContinuousLinearMap (𝕜 := ℝ) L
  let := NormedAlgebra.restrictScalars ℚ ℝ (L →L[ℝ] L)
  have hBC : Commute b c :=
    commute_nilpotentLog_right ((hcomm U.toLinearMap hSU).sub_right (Commute.one_right _))
  have hEB : NormedSpace.exp (E b) = E (S.toLinearMap ^ m) := by
    apply ContinuousLinearMap.ext
    intro x
    exact DFunLike.congr_fun hB x
  have hEC : NormedSpace.exp (E c) = E U.toLinearMap := by
    have he : E c = nilpotentLog (E (U.toLinearMap - 1)) :=
      (nilpotentLog_map E.toRingHom (U.toLinearMap - 1) hU).symm
    have hn : IsNilpotent (E (U.toLinearMap - 1)) := hU.map E.toRingHom
    rw [he, analytic_exp_nilpotentLog _ hn, map_sub, map_one]
    abel
  have hc : Commute (E b) (E c) := hBC.map E.toRingHom
  refine ⟨m, hm, B + m • C, ?_, ?_, ?_⟩
  · have he : NormedSpace.exp (E b + m • E c) = E (A.toLinearMap ^ m) := by
      rw [NormedSpace.exp_add_of_commute (hc.smul_right m), NormedSpace.exp_nsmul,
        hEB, hEC, ← map_pow, ← map_mul, ← hSU.mul_pow, ← hA]
    exact congrArg (fun T : L →L[ℝ] L => T.toLinearMap) he
  · intro T hT
    obtain ⟨hST, hUT⟩ := hcentral T hT
    have hbT : Commute b T := hcomm T hST
    have hcT : Commute c T :=
      (commute_nilpotentLog_right (hUT.symm.sub_right (Commute.one_right _))).symm
    exact hbT.add_left (hcT.smul_left m)
  · intro x hx
    obtain ⟨hs, hu⟩ := lie_jordan_fixed A S U hS hU hSU hA x hx
    change B x + m • C x = 0
    rw [hfixed x hs, show C x = 0 from unipotentLieLogarithm_fixed U hU x hu]
    simp

variable {I : Type} [Fintype I]

theorem commuting_lie_automorphisms_have_fixed_power_logs (A : I → L ≃ₗ⁅ℝ⁆ L)
    (hA : ∀ i j, Commute (A i).toLinearMap (A j).toLinearMap) :
    ∃ m : ℕ, 0 < m ∧ ∃ D : I → LieDerivation ℝ L L,
      (∀ i, (NormedSpace.exp (LinearMap.toContinuousLinearMap (D i).toLinearMap)).toLinearMap =
        (A i).toLinearMap ^ m) ∧
      (∀ i j, Commute (D i).toLinearMap (D j).toLinearMap) ∧
      (∀ i T, Commute (A i).toLinearMap T → Commute (D i).toLinearMap T) ∧
      ∀ i x, A i x = x → D i x = 0 := by
  classical
  choose n hn B hB hcomm hfixed using fun i => real_lie_automorphism_has_fixed_power_log (A i)
  let m := ∏ i, n i
  have hm : 0 < m := Finset.prod_pos (fun i _ => hn i)
  have hd (i : I) : n i ∣ m := Finset.dvd_prod_of_mem (fun j => n j) (Finset.mem_univ i)
  let q := fun i => m / n i
  have hq (i : I) : n i * q i = m := Nat.mul_div_cancel' (hd i)
  let E := Module.End.toContinuousLinearMap (𝕜 := ℝ) L
  let := NormedAlgebra.restrictScalars ℚ ℝ (L →L[ℝ] L)
  refine ⟨m, hm, fun i => q i • B i, ?_, ?_, ?_, ?_⟩
  · intro i
    have he : NormedSpace.exp (E (B i).toLinearMap) = E ((A i).toLinearMap ^ n i) := by
      apply ContinuousLinearMap.ext
      intro x
      exact DFunLike.congr_fun (hB i) x
    have hep : NormedSpace.exp (q i • E (B i).toLinearMap) = E ((A i).toLinearMap ^ m) := by
      rw [NormedSpace.exp_nsmul, he, ← map_pow, ← pow_mul, hq]
    exact congrArg (fun T : L →L[ℝ] L => T.toLinearMap) hep
  · intro i j
    have hc : Commute (B i).toLinearMap (B j).toLinearMap :=
      (hcomm j _ ((hcomm i _ (hA i j)).symm)).symm
    exact (hc.smul_left (q i)).smul_right (q j)
  · intro i T hT
    exact (hcomm i T hT).smul_left (q i)
  · intro i x hx
    change q i • B i x = 0
    rw [hfixed i x hx, smul_zero]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_FixedLogQuotient
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.JointFixedReductionData.residualLayer_normal _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.abelianRealFiniteDimensional _root_.OAI.PolycyclicRecognition.abelianRealLieAbelian _root_.OAI.PolycyclicRecognition.abelianRealNormedLie _root_.OAI.PolycyclicRecognition.derivationLieSpaceFiniteDimensional _root_.OAI.PolycyclicRecognition.derivationLieSpaceRealNormed _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.polynomialLieIdealSubgroup_normal _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Fixed logarithms preserve a quotient with a fixed linear section -/

noncomputable section
namespace PolycyclicRecognition
variable {L V : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [AddCommGroup V] [Module ℝ V]

omit [FiniteDimensional ℝ L] in
theorem fixed_log_projection_zero (A : L ≃ₗ⁅ℝ⁆ L) (D : LieDerivation ℝ L L)
    (hcomm : ∀ T : Module.End ℝ L, Commute A.toLinearMap T → Commute D.toLinearMap T)
    (hfixed : ∀ x, A x = x → D x = 0)
    (p : Module.End ℝ L) (hap : ∀ x, A (p x) = p x) (hpa : ∀ x, p (A x) = p x) :
    p * D.toLinearMap = 0 := by
  have hc : Commute A.toLinearMap p := by
    apply LinearMap.ext
    intro x
    exact (hap x).trans (hpa x).symm
  have hdp : D.toLinearMap * p = 0 := by
    apply LinearMap.ext
    intro x
    exact hfixed (p x) (hap x)
  rw [← (hcomm p hc).eq, hdp]

theorem exp_preserves_projected_quotient (D p : Module.End ℝ L)
    (hpd : p * D = 0) (f : L →ₗ[ℝ] V) (hfp : ∀ x, f (p x) = f x) (x : L) :
    f (NormedSpace.exp (LinearMap.toContinuousLinearMap D) x) = f x := by
  let E := Module.End.toContinuousLinearMap (𝕜 := ℝ) L
  let := NormedAlgebra.restrictScalars ℚ ℝ (L →L[ℝ] L)
  have hc : SemiconjBy (E p) (E D) 0 := by
    change E p * E D = 0 * E p
    rw [← map_mul, hpd, map_zero, zero_mul]
  have he : E p * NormedSpace.exp (E D) = E p := by
    have h := hc.exp_right
    simpa only [SemiconjBy, NormedSpace.exp_zero, one_mul] using h
  have hx : p (NormedSpace.exp (E D) x) = p x := DFunLike.congr_fun he x
  change f (NormedSpace.exp (E D) x) = f x
  exact (hfp _).symm.trans ((congrArg f hx).trans (hfp x))

theorem exp_fixes_projection (D p : Module.End ℝ L)
    (hdp : D * p = 0) (x : L) :
    NormedSpace.exp (LinearMap.toContinuousLinearMap D) (p x) = p x := by
  let E := Module.End.toContinuousLinearMap (𝕜 := ℝ) L
  let := NormedAlgebra.restrictScalars ℚ ℝ (L →L[ℝ] L)
  have hc : SemiconjBy (E p) 0 (E D) := by
    change E p * 0 = E D * E p
    rw [← map_mul, hdp, map_zero, mul_zero]
  have he : NormedSpace.exp (E D) * E p = E p := by
    have h := hc.exp_right
    simpa only [SemiconjBy, NormedSpace.exp_zero, mul_one] using h.symm
  exact DFunLike.congr_fun he x

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_GaugeExtensionSection
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instLocallyCompactSpaceFactorExtension _root_.OAI.PolycyclicRecognition.instT2SpaceFactorExtension _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Explicit kernel corrections of an actual extension section -/

noncomputable section
namespace PolycyclicRecognition.GroupExtensionSection
variable {N G Q : Type*} [Group N] [Group G] [Group Q]

theorem gaugeSection_one (E : GroupExtension N G Q) (σ : E.Section)
    (hσ : σ 1 = 1) (b : Q → N) (hb : b 1 = 1) : gaugeSection E σ b 1 = 1 := by
  change E.inl (b 1) * σ 1 = 1
  rw [hb, hσ, map_one, one_mul]

theorem factor_gaugeSection (E : GroupExtension N G Q) (σ : E.Section)
    (hσ : σ 1 = 1) (b : Q → N) (hb : b 1 = 1) (q r : Q) :
    factor E (gaugeSection E σ b) q r = ((factorSystem E σ hσ).gauge b hb).factor q r := by
  apply E.inl_injective
  rw [inl_factor]
  change (E.inl (b q) * σ q) * (E.inl (b r) * σ r) * (E.inl (b (q * r)) * σ (q * r))⁻¹ =
    E.inl (b q * E.conjAct (σ q) (b r) * factor E σ q r * (b (q * r))⁻¹)
  simp only [map_mul, map_inv, E.inl_conjAct_comm, inl_factor]
  group

end PolycyclicRecognition.GroupExtensionSection

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_GeneratedUnipotentAction
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

namespace OAI

/-! # A finite nilpotent action filtration from unipotent abelian generators -/

noncomputable section
namespace PolycyclicRecognition
variable {V I : Type*} [AddCommGroup V] [Module ℝ V]

theorem action_filtration_preserved_of_commute (D : I → Module.End ℝ V)
    (T : Module.End ℝ V) (hT : ∀ i, Commute T (D i)) (n : ℕ) :
    ∀ x ∈ linearActionFiltration D n, T x ∈ linearActionFiltration D n := by
  induction n with
  | zero => exact fun _ _ => Submodule.mem_top
  | succ n ih =>
    have hs : linearActionFiltration D (n + 1) ≤
        (linearActionFiltration D (n + 1)).comap T := by
      change (⨆ i, (linearActionFiltration D n).map (D i)) ≤ _
      apply iSup_le
      intro i x hx
      obtain ⟨y, hy, rfl⟩ := hx
      change T (D i y) ∈ linearActionFiltration D (n + 1)
      rw [show T (D i y) = D i (T y) from LinearMap.congr_fun (hT i).eq y]
      exact (le_iSup (fun j => (linearActionFiltration D n).map (D j)) i) ⟨T y, ih y hy, rfl⟩
    exact hs

open scoped IsMulCommutative
variable {Q : Type*} [Group Q] [IsMulCommutative Q]

theorem unipotent_generated_abelian_action_filtration
    (ρ : Q →* Module.End ℝ V) (qs : List Q)
    (hgen : Subgroup.closure {q | q ∈ qs} = ⊤)
    (hnil : ∀ q ∈ qs, IsNilpotent (ρ q - 1)) :
    ∃ c, linearActionFiltration (fun q => ρ q - 1) c = ⊥ := by
  classical
  have hcomm (q r : Q) : Commute (ρ q) (ρ r) := by
    change ρ q * ρ r = ρ r * ρ q
    rw [← map_mul, ← map_mul, mul_comm]
  let D : Fin qs.length → Module.End ℝ V := fun i => ρ (qs.get i) - 1
  obtain ⟨c, hc⟩ := finite_commuting_nilpotent_action_filtration D
    (fun i j => ((hcomm _ _).sub_left (Commute.one_left _)).sub_right (Commute.one_right _))
    (fun i => hnil _ (List.get_mem qs i))
  have h0 (q : Q) : ActionDepth D 0 (ρ q) := by
    intro n x hx
    exact action_filtration_preserved_of_commute D (ρ q)
      (fun i => (hcomm _ _).sub_right (Commute.one_right _)) n x hx
  have hmul (q r : Q) : ρ (q * r) - 1 =
      (ρ q - 1) + (ρ r - 1) + (ρ q - 1) * (ρ r - 1) := by
    rw [map_mul]
    noncomm_ring
  have hinv (q : Q) : ρ q⁻¹ - 1 = -(ρ q⁻¹ * (ρ q - 1)) := by
    have he : ρ q⁻¹ * ρ q = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
    rw [mul_sub, he]
    noncomm_ring
  let H : Subgroup Q :=
    { carrier := {q | ActionDepth D 1 (ρ q - 1)}
      one_mem' := by
        change ActionDepth D 1 (ρ 1 - 1)
        rw [map_one, sub_self]
        exact ActionDepth.zero 1
      mul_mem' := by
        intro q r hq hr
        change ActionDepth D 1 (ρ (q * r) - 1)
        rw [hmul]
        exact (hq.add hr).add ((hq.mul hr).mono (by decide))
      inv_mem' := by
        intro q hq
        change ActionDepth D 1 (ρ q⁻¹ - 1)
        rw [hinv]
        exact ((h0 q⁻¹).mul hq).neg }
  have hH : H = ⊤ := by
    apply top_unique
    rw [← hgen]
    apply (Subgroup.closure_le H).mpr
    intro q hq
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hq
    change ActionDepth D 1 (ρ q - 1)
    rw [← hi]
    exact ActionDepth.generator i
  have hdepth (q : Q) : ActionDepth D 1 (ρ q - 1) := by
    have hq : q ∈ H := by rw [hH]; trivial
    exact hq
  have hle (n : ℕ) : linearActionFiltration (fun q => ρ q - 1) n ≤ linearActionFiltration D n := by
    induction n with
    | zero => exact le_rfl
    | succ n ih =>
      change (⨆ q, (linearActionFiltration (fun q => ρ q - 1) n).map (ρ q - 1)) ≤ _
      apply iSup_le
      intro q x hx
      obtain ⟨y, hy, rfl⟩ := hx
      exact hdepth q n y (ih hy)
  exact ⟨c, eq_bot_iff.mpr ((hle c).trans_eq hc)⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_InvariantLinearLayer
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Endomorphisms on an invariant subquotient

This is the concrete linear bridge used on successive lower-central factors.
Commutation modulo the smaller subspace becomes exact commutation, and
unipotence survives restriction and quotient.
-/

noncomputable section
namespace PolycyclicRecognition
variable {V : Type*} [AddCommGroup V] [Module ℝ V]

theorem invariantLayerEnd_unipotent (U W : Submodule ℝ V) (f : Module.End ℝ V)
    (hfU : ∀ x ∈ U, f x ∈ U) (hfW : ∀ x ∈ W, f x ∈ W)
    (hnil : IsNilpotent (f - 1)) :
    IsNilpotent (invariantLayerEnd U W f hfU hfW - 1) := by
  let R := W.comap U.subtype
  let d := f.restrict hfU - 1
  have hd : R ≤ R.comap d := fun x hx => W.sub_mem (hfW x hx) hx
  have hdU : ∀ x ∈ U, (f - 1) x ∈ U := fun x hx => U.sub_mem (hfU x hx) hx
  have he : d = (f - 1).restrict hdU := by
    apply LinearMap.ext
    intro x
    rfl
  have hdn : IsNilpotent d := he ▸ Module.End.isNilpotent.restrict hdU hnil
  have hq : invariantLayerEnd U W f hfU hfW - 1 = R.mapQ R d hd := by
    apply LinearMap.ext
    intro x
    refine Quotient.inductionOn' x ?_
    intro x
    rfl
  rw [hq]
  obtain ⟨n, hn⟩ := hdn
  refine ⟨n, ?_⟩
  rw [← R.mapQ_pow hd n]
  simp only [hn, Submodule.mapQ_zero]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_NilpotentAutomorphismDifference
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Iterated differences of an automorphism induced by nilpotent conjugation

No commutativity of the invariant subgroup is required. Each successive
difference lies one step deeper in the lower central series of the ambient
group.
-/

noncomputable section
namespace PolycyclicRecognition
open scoped commutatorElement
variable {G H : Type*} [Group G] [Group H]

theorem conjugation_difference_iterate_mem (t x : G) (n : ℕ) :
    (fun y => t * y * t⁻¹ * y⁻¹)^[n] x ∈
      (⊤ : Subgroup G).lowerCentralSeries n := by
  induction n with
  | zero => exact Subgroup.mem_top _
  | succ n ih =>
    rw [Function.iterate_succ_apply', Subgroup.lowerCentralSeries_succ,
      Subgroup.commutator_comm]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top t) ih

theorem conjugation_difference_iterate_one [Group.IsNilpotent G] (t x : G) :
    (fun y => t * y * t⁻¹ * y⁻¹)^[Group.nilpotencyClass G] x = 1 := by
  have h := conjugation_difference_iterate_mem t x (Group.nilpotencyClass G)
  rwa [Subgroup.lowerCentralSeries_nilpotencyClass, Subgroup.mem_bot] at h

theorem automorphism_difference_iterate_map (j : H →* G) (A : H ≃* H) (t : G)
    (hA : ∀ x, j (A x) = t * j x * t⁻¹) (n : ℕ) (x : H) :
    j ((fun y => A y * y⁻¹)^[n] x) =
      (fun y => t * y * t⁻¹ * y⁻¹)^[n] (j x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', map_mul,
      map_inv, hA, ih]

theorem automorphism_difference_iterate_one [Group.IsNilpotent G]
    (j : H →* G) (hj : Function.Injective j) (A : H ≃* H) (t : G)
    (hA : ∀ x, j (A x) = t * j x * t⁻¹) (x : H) :
    (fun y => A y * y⁻¹)^[Group.nilpotencyClass G] x = 1 := by
  apply hj
  rw [map_one, automorphism_difference_iterate_map j A t hA,
    conjugation_difference_iterate_one]

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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_SectionFactorTopology
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.JointFixedReductionData.residualLayer_normal _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.JointFixedReductionData.residualLayerProjection_equiv _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Changing the section preserves the extension topology -/

noncomputable section
namespace PolycyclicRecognition
attribute [local instance] factorExtensionTopology
variable {N Q : Type} [Group N] [Group Q] [TopologicalSpace N]
  [TopologicalSpace Q] [IsTopologicalGroup N] [DiscreteTopology Q]
  (R : NonabelianFactorSystem N Q)
  (σ : (FactorExtension.groupExtension R).Section) (hσ : σ 1 = 1)

omit [TopologicalSpace N] [TopologicalSpace Q] [IsTopologicalGroup N] [DiscreteTopology Q] in
private theorem section_coordinate_left (g : FactorExtension R) :
    GroupExtensionSection.coordinate (FactorExtension.groupExtension R) σ g =
      g.left * (σ g.right).left⁻¹ := by
  have h : FactorExtension.inl R
      (GroupExtensionSection.coordinate (FactorExtension.groupExtension R) σ g) *
      σ g.right = g := by
    have hi := GroupExtensionSection.inl_coordinate (FactorExtension.groupExtension R) σ g
    change FactorExtension.inl R _ = g * (σ g.right)⁻¹ at hi
    rw [hi, inv_mul_cancel_right]
  have hl := congrArg (fun x : FactorExtension R => x.left) h
  simp only [FactorExtension.mul_left, FactorExtension.inl, MonoidHom.coe_mk,
    OneHom.coe_mk, R.action_one, MulAut.one_apply, R.factor_one_left, mul_one] at hl
  exact (eq_mul_inv_iff_mul_eq).mpr hl

omit [TopologicalSpace N] [TopologicalSpace Q] [IsTopologicalGroup N] [DiscreteTopology Q] in
private theorem section_equiv_apply (g : FactorExtension R) :
    GroupExtensionSection.mulEquiv (FactorExtension.groupExtension R) σ hσ g =
      ⟨g.left * (σ g.right).left⁻¹, g.right⟩ := by
  apply (GroupExtensionSection.mulEquiv (FactorExtension.groupExtension R) σ hσ).symm.injective
  rw [MulEquiv.symm_apply_apply]
  change g = FactorExtension.inl R (g.left * (σ g.right).left⁻¹) * σ g.right
  rw [← section_coordinate_left R σ g]
  have hi := GroupExtensionSection.inl_coordinate (FactorExtension.groupExtension R) σ g
  change FactorExtension.inl R _ = g * (σ g.right)⁻¹ at hi
  rw [hi, inv_mul_cancel_right]

theorem sectionFactorEquiv_continuous :
    Continuous (GroupExtensionSection.mulEquiv (FactorExtension.groupExtension R) σ hσ) := by
  have hs : Continuous (fun q : Q => (σ q).left) := continuous_of_discreteTopology
  have h : Continuous (fun g : FactorExtension R =>
      (g.left * (σ g.right).left⁻¹, g.right)) :=
    ((continuous_factor_left R).mul (hs.comp (continuous_factor_right R)).inv).prodMk
      (continuous_factor_right R)
  apply continuous_induced_rng.mpr
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  funext g
  rw [Function.comp_apply, section_equiv_apply R σ hσ g]
  rfl

theorem sectionFactorEquiv_symm_continuous :
    Continuous (GroupExtensionSection.mulEquiv (FactorExtension.groupExtension R) σ hσ).symm := by
  let T := GroupExtensionSection.factorSystem (FactorExtension.groupExtension R) σ hσ
  have hs : Continuous (fun q : Q => (σ q).left) := continuous_of_discreteTopology
  have h : Continuous (fun a : FactorExtension T =>
      (a.left * (σ a.right).left, a.right)) :=
    ((continuous_factor_left T).mul (hs.comp (continuous_factor_right T))).prodMk
      (continuous_factor_right T)
  apply continuous_induced_rng.mpr
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  funext a
  change ((FactorExtension.inl R a.left * σ a.right).left,
    (FactorExtension.inl R a.left * σ a.right).right) = _
  have hr : (σ a.right).right = a.right := σ.rightHom_section a.right
  simp [FactorExtension.mul_left, FactorExtension.mul_right, FactorExtension.inl,
    R.action_one, R.factor_one_left, hr]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_NilpotentDifferenceDerivative
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Nilpotence detected by iterating a group difference map -/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem nilpotent_fderiv_of_iterate_zero (f : V → V) (hf : DifferentiableAt ℝ f 0)
    (h0 : f 0 = 0) (n : ℕ) (hn : ∀ x, f^[n] x = 0) :
    IsNilpotent (fderiv ℝ f 0) := by
  have hi := hf.hasFDerivAt.iterate h0 n
  have he : f^[n] = fun _ => 0 := funext hn
  rw [he] at hi
  exact ⟨n, hi.unique (hasFDerivAt_const 0 (0 : V))⟩

theorem nilpotent_difference_fderiv
    [Group V] [LieGroup (𝓘(ℝ, V)) ⊤ V]
    (hone : (1 : V) = 0) (f : V → V) (hf : DifferentiableAt ℝ f 0)
    (h0 : f 0 = 0) (n : ℕ)
    (hn : ∀ x, (fun y => f y * (-y))^[n] x = 0) :
    IsNilpotent (fderiv ℝ f 0 - ContinuousLinearMap.id ℝ V) := by
  have hg : HasFDerivAt (fun y : V => -y) (-ContinuousLinearMap.id ℝ V) 0 :=
    (hasFDerivAt_id (𝕜 := ℝ) (0 : V)).neg
  have hm := HasMFDerivAt.mul_at_one hf.hasFDerivAt.hasMFDerivAt
    hg.hasMFDerivAt
    (h0.trans hone.symm) (by rw [neg_zero]; exact hone.symm)
  have hd : HasFDerivAt (fun y => f y * (-y))
      (fderiv ℝ f 0 - ContinuousLinearMap.id ℝ V) 0 := by
    rw [sub_eq_add_neg]
    exact HasMFDerivAt.hasFDerivAt hm
  have hz : f 0 * (- (0 : V)) = 0 := by rw [h0, neg_zero, ← hone, one_mul]
  have hnil := nilpotent_fderiv_of_iterate_zero _ hd.differentiableAt hz n hn
  rwa [hd.fderiv] at hnil

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_PolynomialModelDifference
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.JointFixedReductionData.residualLayer_normal _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.abelianRealCoordinates _root_.OAI.PolycyclicRecognition.abelianRealFiniteDimensional _root_.OAI.PolycyclicRecognition.abelianRealLieAbelian _root_.OAI.PolycyclicRecognition.abelianRealNormedLie _root_.OAI.PolycyclicRecognition.derivationLieSpaceFiniteDimensional _root_.OAI.PolycyclicRecognition.derivationLieSpaceRealNormed _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.polynomialLieIdealSubgroup_normal _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial group differences in exponential coordinates -/

noncomputable section
namespace PolycyclicRecognition
open Module
variable {L V : Type*} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {d e : ℕ} {b : Basis (Fin d) ℝ V} {c : Basis (Fin e) ℝ L}

omit [FiniteDimensional ℝ L] P in
theorem IsPolynomialInBasis.neg {f : V → L} (hf : IsPolynomialInBasis b c f) :
    IsPolynomialInBasis b c (fun x => -f x) := by
  have h := IsCoordinatePolynomial.neg hf
  simpa only [IsPolynomialInBasis, map_neg] using h

theorem polynomial_model_difference (A : L →ₗ[ℝ] L) (b : Basis (Fin d) ℝ L) :
    IsPolynomialInBasis b b (fun x => A x * (-x)) :=
  (IsPolynomialInBasis.linear A).mul
    ((IsPolynomialInBasis.linear (LinearMap.id : L →ₗ[ℝ] L)).neg)

theorem nilpotent_linear_of_group_difference (A : L →ₗ[ℝ] L) (n : ℕ)
    (hn : ∀ x, (fun y => A y * (-y))^[n] x = 0) : IsNilpotent (A - 1) := by
  have hA := A.toContinuousLinearMap.hasFDerivAt (x := 0)
  have h := nilpotent_difference_fderiv P.one_eq_zero A
    hA.differentiableAt (map_zero A) n hn
  change IsNilpotent (fderiv ℝ A.toContinuousLinearMap 0 - ContinuousLinearMap.id ℝ L) at h
  rw [hA.fderiv] at h
  exact h.map ContinuousLinearMap.toLinearMapRingHom

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Lattices_LatticeAutomorphismUnipotent
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.JointFixedReductionData.residualLayer_normal _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.abelianRealCoordinates _root_.OAI.PolycyclicRecognition.abelianRealFiniteDimensional _root_.OAI.PolycyclicRecognition.abelianRealLieAbelian _root_.OAI.PolycyclicRecognition.abelianRealNormedLie _root_.OAI.PolycyclicRecognition.derivationLieSpaceFiniteDimensional _root_.OAI.PolycyclicRecognition.derivationLieSpaceRealNormed _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.polynomialLieIdealSubgroup_normal _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Unipotence of a lattice automorphism induced by nilpotent conjugation

A polynomial surjective coordinate parameter suffices. Its integral grid
only has to land in the lattice; no additive description of that lattice is
assumed.
-/

noncomputable section
namespace PolycyclicRecognition
open Module
variable {L G H : Type*} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L] [Group G] [Group H] [Group.IsNilpotent G]

theorem lattice_automorphism_unipotent {d : ℕ} (b : Basis (Fin d) ℝ L)
    (p : L → L) (hp : IsPolynomialInBasis b b p) (hsurj : Function.Surjective p)
    (e : H →* L)
    (hgrid : ∀ z : Fin d → ℤ, ∃ x : H,
      e x = p (b.equivFun.symm (fun i => (z i : ℝ))))
    (j : H →* G) (hj : Function.Injective j)
    (a : H ≃* H) (t : G) (ha : ∀ x, j (a x) = t * j x * t⁻¹)
    (A : L →ₗ[ℝ] L) (hA : ∀ x, A (e x) = e (a x)) :
    IsNilpotent (A - 1) := by
  let f : L → L := fun x => A x * (-x)
  let n := Group.nilpotencyClass G
  have hf : IsPolynomialInBasis b b f := polynomial_model_difference A b
  have hs : Function.Semiconj e (fun y => a y * y⁻¹) f := by
    intro x
    change e (a x * x⁻¹) = A (e x) * (-e x)
    rw [map_mul, map_inv, hA, P.inv_eq_neg]
  have hezero (x : H) : f^[n] (e x) = 0 := by
    rw [← hs.iterate_right n x, automorphism_difference_iterate_one j hj a t ha,
      map_one, P.one_eq_zero]
  have hz : IsPolynomialInBasis b b (fun _ : L => (0 : L)) := by
    simpa only [IsPolynomialInBasis, map_zero] using
      (IsCoordinatePolynomial.const (I := Fin d) (0 : Fin d → ℝ))
  have heq : f^[n] ∘ p = fun _ => (0 : L) :=
    ((hf.iterate n).comp hp).ext_integer_grid hz (by
      intro z
      obtain ⟨x, hx⟩ := hgrid z
      change f^[n] (p (b.equivFun.symm (fun i => (z i : ℝ)))) = 0
      rw [← hx]
      exact hezero x)
  apply nilpotent_linear_of_group_difference A n
  intro y
  obtain ⟨x, rfl⟩ := hsurj y
  exact congrFun heq x

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Lattices_LatticeWordExtension
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.JointFixedReductionData.residualLayer_normal _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.abelianRealCoordinates _root_.OAI.PolycyclicRecognition.abelianRealFiniteDimensional _root_.OAI.PolycyclicRecognition.abelianRealLieAbelian _root_.OAI.PolycyclicRecognition.abelianRealNormedLie _root_.OAI.PolycyclicRecognition.derivationLieSpaceFiniteDimensional _root_.OAI.PolycyclicRecognition.derivationLieSpaceRealNormed _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.polynomialLieIdealSubgroup_normal _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Extending lattice automorphisms through ordered polynomial coordinates

The extension is constructed by replacing each integral generator power by
the corresponding real one-parameter subgroup. Polynomial identities prove
both multiplicativity and the inverse identities.
-/

noncomputable section
namespace PolycyclicRecognition
open Module
open scoped Manifold ContDiff
variable {L H : Type*} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L] [Group H] {d : ℕ}
  (b : Basis (Fin d) ℝ L) (p : L ≃ L) (e : H →* L) (X : Fin d → H)

theorem contMDiff_latticeWordAut (hp : IsPolynomialInBasis b b p)
    (hq : IsPolynomialInBasis b b p.symm)
    (hparam : ∀ z : Fin d → ℤ,
      p (b.equivFun.symm (fun i => (z i : ℝ))) = e (orderedWord X z))
    (hX : Function.Surjective (orderedWord X)) (a : MulAut H) :
    ContMDiff (𝓘(ℝ, L)) (𝓘(ℝ, L)) ∞ (latticeWordAut b p e X hp hq hparam hX a) := by
  have h : ContDiff ℝ ∞ (latticeWordMap b p e X a.toMonoidHom) :=
    (latticeWordMap_polynomial b p e X hq a.toMonoidHom).contDiff.of_le le_top
  exact h.contMDiff

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Lattices_NilpotentLatticeAutomorphisms
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.JointFixedReductionData.residualLayer_normal _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.derivationLieSpaceFiniteDimensional _root_.OAI.PolycyclicRecognition.derivationLieSpaceRealNormed _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.polynomialLieIdealSubgroup_normal _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Extending the lattice automorphism group to its nilpotent Lie model

The extension respects composition. This retains arbitrary discrete actions,
without imposing unipotence on their automorphisms.
-/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold ContDiff
variable {H : Type} [Group H]

namespace NilpotentLatticeCoordinates
variable (C : NilpotentLatticeCoordinates H)

theorem automorphism_smooth (a : MulAut H) :
    ContMDiff (𝓘(ℝ, C.carrier)) (𝓘(ℝ, C.carrier)) ∞ (C.automorphism a) :=
  contMDiff_latticeWordAut C.basis C.parameter
    (C.lattice.subtype.comp C.equiv.toMonoidHom) C.generators
    C.polynomial C.polynomial_symm C.integer_parameter C.word_surjective a

end NilpotentLatticeCoordinates
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_NilpotentExtensionFactorSystem
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.JointFixedReductionData.residualLayer_normal _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.derivationLieSpaceFiniteDimensional _root_.OAI.PolycyclicRecognition.derivationLieSpaceRealNormed _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instLocallyCompactSpaceFactorExtension _root_.OAI.PolycyclicRecognition.instT2SpaceFactorExtension _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.polynomialLieIdealSubgroup_normal _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual real factor system of a nilpotent-kernel extension

Its failure to be an action is exactly the exponential of the inner Lie
derivation obtained from the section defect.
-/

noncomputable section
namespace PolycyclicRecognition.NilpotentLatticeCoordinates
variable {N G Q : Type} [Group N] [Group G] [Group Q]
  (C : NilpotentLatticeCoordinates N) (S : GroupExtension N G Q)
  (σ : S.Section) (hσ : σ 1 = 1)
open GroupExtensionSection
open scoped Manifold ContDiff

/-- Smoothness is proved from the lattice polynomial extension. -/
theorem extensionFactorSystem_smooth (q : Q) :
    ContMDiff (𝓘(ℝ, C.carrier)) (𝓘(ℝ, C.carrier)) ∞
      ((C.extensionFactorSystem S σ hσ).action q) :=
  C.automorphism_smooth _

end PolycyclicRecognition.NilpotentLatticeCoordinates

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_NilpotentExtensionEmbedding
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.JointFixedReductionData.residualLayer_normal _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.derivationLieSpaceFiniteDimensional _root_.OAI.PolycyclicRecognition.derivationLieSpaceRealNormed _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instLocallyCompactSpaceFactorExtension _root_.OAI.PolycyclicRecognition.instT2SpaceFactorExtension _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.polynomialLieIdealSubgroup_normal _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Extending a nilpotent lattice to the full nonsplit extension

Only the nilpotent kernel is completed here. The original quotient, section,
and all of its defects are retained exactly.
-/

noncomputable section
namespace PolycyclicRecognition.NilpotentLatticeCoordinates
variable {N G Q : Type} [Group N] [Group G] [Group Q]
  (C : NilpotentLatticeCoordinates N) (S : GroupExtension N G Q)
  (σ : S.Section) (hσ : σ 1 = 1)

/-- This range description retains the full quotient and only restricts the
nilpotent coordinate to its constructed lattice. -/
theorem mem_extensionEmbedding_range (a : FactorExtension (C.extensionFactorSystem S σ hσ)) :
    a ∈ (C.extensionEmbedding S σ hσ).range ↔ a.left ∈ C.lattice := by
  constructor
  · rintro ⟨g, rfl⟩
    exact (C.equiv _).property
  · intro ha
    obtain ⟨n, hn⟩ := C.equiv.surjective ⟨a.left, ha⟩
    let b : FactorExtension (GroupExtensionSection.factorSystem S σ hσ) := ⟨n, a.right⟩
    refine ⟨(GroupExtensionSection.mulEquiv S σ hσ).symm b, ?_⟩
    change C.extensionFactorMap S σ hσ
      ((GroupExtensionSection.mulEquiv S σ hσ) ((GroupExtensionSection.mulEquiv S σ hσ).symm b)) = a
    rw [MulEquiv.apply_symm_apply]
    apply FactorExtension.ext
    · exact congrArg Subtype.val hn
    · rfl

end PolycyclicRecognition.NilpotentLatticeCoordinates

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Lattices_NilpotentExtensionLattice
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.JointFixedReductionData.residualLayer_normal _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.derivationLieSpaceFiniteDimensional _root_.OAI.PolycyclicRecognition.derivationLieSpaceRealNormed _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.polynomialLieIdealSubgroup_normal _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A uniform lattice after completing only the nilpotent kernel

The quotient is still discrete. This is an intermediate construction, not a
claim that the resulting group is connected.
-/

noncomputable section
namespace PolycyclicRecognition.NilpotentLatticeCoordinates
open Set
open scoped Manifold
variable {N G Q : Type} [Group N] [Group G] [Group Q]
  [TopologicalSpace Q] [DiscreteTopology Q]
  (C : NilpotentLatticeCoordinates N) (S : GroupExtension N G Q)
  (σ : S.Section) (hσ : σ 1 = 1)
attribute [local instance] factorExtensionTopology

theorem completedExtensionLattice_discrete :
    DiscreteTopology (C.completedExtensionLattice S σ hσ) := by
  let := C.uniform.1
  let f : C.completedExtensionLattice S σ hσ → C.lattice × Q := fun a =>
    (⟨a.val.left, (C.mem_extensionEmbedding_range S σ hσ a.val).mp a.property⟩, a.val.right)
  have hl := (continuous_factor_left (C.extensionFactorSystem S σ hσ)).comp
    (continuous_subtype_val : Continuous (Subtype.val : C.completedExtensionLattice S σ hσ → _))
  have hr := (continuous_factor_right (C.extensionFactorSystem S σ hσ)).comp
    (continuous_subtype_val : Continuous (Subtype.val : C.completedExtensionLattice S σ hσ → _))
  have hf : Continuous f := (hl.subtype_mk _).prodMk hr
  apply DiscreteTopology.of_continuous_injective hf
  intro a b h
  apply Subtype.ext
  apply FactorExtension.ext
  · exact congrArg (fun z : C.lattice × Q => (z.1 : C.carrier)) h
  · exact congrArg (fun z : C.lattice × Q => z.2) h

omit [TopologicalSpace Q] [DiscreteTopology Q] in
theorem extension_action_lattice (q : Q) (x : C.lattice) :
    (C.extensionFactorSystem S σ hσ).action q x ∈ C.lattice := by
  obtain ⟨n, hn⟩ := C.equiv.surjective x
  rw [← hn]
  change C.automorphism (S.conjAct (σ q)) (C.equiv n) ∈ C.lattice
  rw [C.automorphism_on_lattice]
  exact (C.equiv _).property

/-- Compactness of the original kernel fundamental cover is retained by the
completed extension, even though its quotient may be infinite and nonsplit. -/
theorem completedExtensionLattice_uniform :
    IsUniformLattice (C.completedExtensionLattice S σ hσ) := by
  let T := C.extensionFactorSystem S σ hσ
  obtain ⟨K, hK, hcover⟩ := C.uniform.2
  refine ⟨C.completedExtensionLattice_discrete S σ hσ,
    FactorExtension.inl T '' K, hK.image (continuous_factor_inl T), ?_⟩
  intro g
  obtain ⟨μ, u, hu, heq⟩ := hcover ((T.action g.right).symm g.left)
  let γ : C.completedExtensionLattice S σ hσ :=
    ⟨⟨T.action g.right μ, g.right⟩,
      (C.mem_extensionEmbedding_range S σ hσ _).mpr
        (C.extension_action_lattice S σ hσ g.right μ)⟩
  refine ⟨γ, FactorExtension.inl T u, ⟨u, hu, rfl⟩, ?_⟩
  apply FactorExtension.ext
  · change T.action g.right μ * T.action g.right u * T.factor g.right 1 = g.left
    rw [T.factor_one_right, mul_one, ← map_mul, heq]
    exact (T.action g.right).apply_symm_apply g.left
  · exact mul_one g.right

end PolycyclicRecognition.NilpotentLatticeCoordinates

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_PolynomialSubalgebraNilpotence
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.JointFixedReductionData.residualLayer_normal _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.abelianRealCoordinates _root_.OAI.PolycyclicRecognition.abelianRealFiniteDimensional _root_.OAI.PolycyclicRecognition.abelianRealLieAbelian _root_.OAI.PolycyclicRecognition.abelianRealNormedLie _root_.OAI.PolycyclicRecognition.derivationLieSpaceFiniteDimensional _root_.OAI.PolycyclicRecognition.derivationLieSpaceRealNormed _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.JointFixedReductionData.residualLayerProjection_equiv _root_.OAI.PolycyclicRecognition.NilpotentKernelCompletion.extendedAction_embed _root_.OAI.PolycyclicRecognition.NilpotentLatticeCoordinates.automorphism_mul _root_.OAI.PolycyclicRecognition.NilpotentLatticeCoordinates.automorphism_on_lattice _root_.OAI.PolycyclicRecognition.NilpotentLatticeCoordinates.automorphism_one _root_.OAI.PolycyclicRecognition.PolynomialExponentialCoordinates.analyticDerivationAction_apply _root_.OAI.PolycyclicRecognition.abelianRealLatticeEquiv_apply _root_.OAI.PolycyclicRecognition.analyticDerivationExp_apply _root_.OAI.PolycyclicRecognition.derivationSemidirectHom_apply _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.polynomialCoordinateHom_apply _root_.OAI.PolycyclicRecognition.polynomialInnerLieEquiv_apply _root_.OAI.PolycyclicRecognition.polynomialModelLieEquiv_apply _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Group nilpotence of the concrete BCH subgroups

The intrinsic Lie lower central series is a sequence of actual subgroups.
The finite-difference formula puts every group commutator one step deeper.
-/

noncomputable section
namespace PolycyclicRecognition
open LieModule
attribute [local instance] polynomialSubalgebraGroup
variable {L : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L]

theorem polynomialSubalgebra_commutator_mem (K : LieSubalgebra ℝ L)
    (v x : K) (k : ℕ) (hx : x ∈ lowerCentralSeries ℝ K K k) :
    v * x * v⁻¹ * x⁻¹ ∈ lowerCentralSeries ℝ K K (k + 1) := by
  have hd := polynomialSubalgebra_inner_difference K v k x hx
  have hp := polynomialSubalgebra_mul_difference K (k + 1) (v * x * v⁻¹) x⁻¹ x x⁻¹ hd (by simp)
  have hone : (1 : K) = 0 := Subtype.ext P.one_eq_zero
  simp only [mul_inv_cancel, hone, sub_zero, sub_self, add_zero] at hp
  have hh := (lowerCentralSeries ℝ K K (k + 1)).add_mem
    ((antitone_lowerCentralSeries ℝ K K (Nat.le_succ (k + 1))) hp) hd
  change v * x * v⁻¹ * x⁻¹ ∈ (lowerCentralSeries ℝ K K (k + 1)).toSubmodule
  simpa only [sub_add_cancel] using hh

theorem group_lowerCentral_le_lie (K : LieSubalgebra ℝ L) (k : ℕ) :
    (⊤ : Subgroup K).lowerCentralSeries k ≤
      polynomialLieIdealSubgroup K (lowerCentralSeries ℝ K K k) := by
  induction k with
  | zero =>
    intro x _
    change x ∈ lowerCentralSeries ℝ K K 0
    simp
  | succ k ih =>
    rw [Subgroup.lowerCentralSeries_succ, Subgroup.commutator_comm]
    apply Subgroup.commutator_le.mpr
    intro v _ x hx
    change v * x * v⁻¹ * x⁻¹ ∈ lowerCentralSeries ℝ K K (k + 1)
    exact polynomialSubalgebra_commutator_mem K v x k (ih hx)

theorem polynomialSubalgebra_group_nilpotent (K : LieSubalgebra ℝ L)
    [LieRing.IsNilpotent K] : Group.IsNilpotent K := by
  obtain ⟨c, hc⟩ := (LieModule.isNilpotent_iff ℝ K K).mp
    (inferInstance : LieModule.IsNilpotent K K)
  apply Subgroup.nilpotent_iff_lowerCentralSeries.mpr
  refine ⟨c, eq_bot_iff.mpr ?_⟩
  intro x hx
  have hh := group_lowerCentral_le_lie K c hx
  change x ∈ lowerCentralSeries ℝ K K c at hh
  rw [hc] at hh
  have hx0 : x = 0 := hh
  change x = 1
  exact hx0.trans (Subtype.ext P.one_eq_zero).symm

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_PolynomialGroupNilpotence
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.JointFixedReductionData.residualLayer_normal _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.abelianRealCoordinates _root_.OAI.PolycyclicRecognition.abelianRealFiniteDimensional _root_.OAI.PolycyclicRecognition.abelianRealLieAbelian _root_.OAI.PolycyclicRecognition.abelianRealNormedLie _root_.OAI.PolycyclicRecognition.derivationLieSpaceFiniteDimensional _root_.OAI.PolycyclicRecognition.derivationLieSpaceRealNormed _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Nilpotence of the polynomial group of a nilpotent Lie algebra -/

noncomputable section
namespace PolycyclicRecognition
attribute [local instance] polynomialSubalgebraGroup
variable {L : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [PolynomialExponentialCoordinates L] [LieRing.IsNilpotent L]

theorem polynomial_group_nilpotent : Group.IsNilpotent L := by
  let K : LieSubalgebra ℝ L := ⊤
  let : LieRing.IsNilpotent K := Function.Injective.lieAlgebra_isNilpotent
    (f := K.incl) Subtype.val_injective
  let : Group.IsNilpotent K := polynomialSubalgebra_group_nilpotent K
  apply Group.nilpotent_of_surjective (polynomialSubalgebraHom K K.incl)
  intro x
  exact ⟨⟨x, trivial⟩, rfl⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_IntegralQuotientKernel
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.latticeNormalFlag_normal _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Removing one coordinate from an integral abelian quotient -/

noncomputable section
namespace PolycyclicRecognition

theorem integralQuotientLast_surjective (n : ℕ) : Function.Surjective (integralQuotientLast n) :=
  fun k => ⟨integralQuotientInsert n 1 k, integralQuotientLast_insert n 1 k⟩

variable {N G : Type} [Group N] [Group G] {n : ℕ}

theorem integralKernelExtension_conjAct
    (E : GroupExtension N G (IntegralLatticeGroup (n + 1)))
    (g : (integralLastMap E).ker) (x : N) :
    (integralKernelExtension E).conjAct g x = E.conjAct (g : G) x := by
  apply E.inl_injective
  have hh := (integralKernelExtension E).inl_conjAct_comm (e := g) (n := x)
  have he := congrArg Subtype.val hh
  exact he.trans E.inl_conjAct_comm.symm

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_NilpotentCodimensionOneCriterion
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Nilpotence in a one-dimensional derivation extension

The ideal acts nilpotently on the extension: the first bracket lands in
the ideal and all subsequent brackets are adjoint operators of the ideal.
Engel's codimension-one criterion then adjoins the nilpotent time operator.
-/

noncomputable section
namespace PolycyclicRecognition

theorem nilpotent_of_codimension_one_restriction
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (f : Module.End ℝ (V × ℝ)) (a : Module.End ℝ V)
    (ha : IsNilpotent a)
    (hzero : ∀ x, (f x).2 = 0)
    (hres : ∀ x, f (x, 0) = (a x, 0)) : IsNilpotent f := by
  obtain ⟨n, hn⟩ := ha
  have hpow (k : ℕ) (x : V) : (f ^ k) (x, 0) = ((a ^ k) x, 0) := by
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [pow_succ', Module.End.mul_apply, ih, hres, pow_succ', Module.End.mul_apply]
  refine ⟨n + 1, ?_⟩
  apply LinearMap.ext
  intro x
  rw [pow_succ, Module.End.mul_apply]
  have hx : f x = ((f x).1, 0) := Prod.ext rfl (hzero x)
  rw [hx, hpow, hn]
  rfl

theorem nilpotent_of_split_restriction
    {T V : Type*} [AddCommGroup T] [Module ℝ T] [AddCommGroup V] [Module ℝ V]
    (e : T ≃ₗ[ℝ] (V × ℝ)) (f : Module.End ℝ T) (a : Module.End ℝ V) (ha : IsNilpotent a)
      (hz : ∀ y, (e (f y)).2 = 0)
      (hr : ∀ y, e (f (e.symm (y, 0))) = (a y, 0)) : IsNilpotent f := by
  have hn : IsNilpotent (e.conjRingEquiv f) := by
    apply nilpotent_of_codimension_one_restriction _ a ha
    · intro y; exact hz (e.symm y)
    · exact hr
  obtain ⟨n, hn⟩ := hn
  refine ⟨n, e.conjRingEquiv.injective ?_⟩
  rw [map_pow, hn, map_zero]

variable {L T : Type*} [LieRing L] [LieAlgebra ℝ L]
  [LieRing.IsNilpotent L] [LieRing T] [LieAlgebra ℝ T]
  [FiniteDimensional ℝ T]

theorem nilpotent_derivation_extension
    (e : T ≃ₗ[ℝ] (L × ℝ))
    (D : L →ₗ[ℝ] L) (hD : IsNilpotent D)
    (hb : ∀ x y : T,
      e ⁅x, y⁆ = (⁅(e x).1, (e y).1⁆ + (e x).2 • D (e y).1 -
        (e y).2 • D (e x).1, 0)) : LieRing.IsNilpotent T := by
  let I : LieIdeal ℝ T :=
    { carrier := {x | (e x).2 = 0}
      zero_mem' := by change (e 0).2 = 0; rw [map_zero]; rfl
      add_mem' := by
        intro x y hx hy
        change (e (x + y)).2 = 0
        rw [map_add]
        change (e x).2 + (e y).2 = 0
        rw [hx, hy, add_zero]
      smul_mem' := by
        intro r x hx
        change (e (r • x)).2 = 0
        rw [map_smul]
        change r • (e x).2 = 0
        rw [hx, smul_zero]
      lie_mem := by intro x y _; change (e ⁅x, y⁆).2 = 0; rw [hb] }
  have hideal : LieModule.IsNilpotent I T := by
    apply (LieModule.isNilpotent_iff_forall' (R := ℝ) (L := I) (M := T)).mpr
    intro x
    have hx : (e x.val).2 = 0 := x.property
    apply nilpotent_of_split_restriction e (LieModule.toEnd ℝ I T x) (LieAlgebra.ad ℝ L (e x.val).1)
      (LieModule.isNilpotent_toEnd_of_isNilpotent ℝ L L (e x.val).1)
    · intro y
      change (e ⁅x.val, y⁆).2 = 0
      rw [hb]
    · intro y
      change e ⁅x.val, e.symm (y, 0)⁆ = (⁅(e x.val).1, y⁆, 0)
      rw [hb, e.apply_symm_apply]
      simp only [hx, zero_smul, add_zero, sub_zero]
  let t : T := e.symm (0, 1)
  have ht : e t = (0, 1) := e.apply_symm_apply _
  have htime : IsNilpotent (LieModule.toEnd ℝ T T t) := by
    apply nilpotent_of_split_restriction e _ D hD
    · intro y
      change (e ⁅t, y⁆).2 = 0
      rw [hb]
    · intro y
      change e ⁅t, e.symm (y, 0)⁆ = (D y, 0)
      rw [hb, ht, e.apply_symm_apply]
      simp only [zero_lie, one_smul, zero_smul, zero_add, sub_zero]
  have hspan : ℝ ∙ t ⊔ I.toSubmodule = ⊤ := by
    apply top_unique
    intro x _
    apply Submodule.mem_sup.mpr
    refine ⟨(e x).2 • t, Submodule.smul_mem _ _
      (Submodule.mem_span_singleton_self _), e.symm ((e x).1, 0), ?_, ?_⟩
    · change (e (e.symm ((e x).1, 0))).2 = 0
      rw [e.apply_symm_apply]
    · apply e.injective
      rw [map_add, map_smul, ht, e.apply_symm_apply]
      apply Prod.ext
      · change (e x).2 • (0 : L) + (e x).1 = (e x).1
        rw [smul_zero, zero_add]
      · change (e x).2 * 1 + 0 = (e x).2
        rw [mul_one, add_zero]
  exact LieSubmodule.isNilpotentOfIsNilpotentSpanSupEqTop
    (R := ℝ) (L := T) (M := T) (I := I) (x := t) hspan htime hideal

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_NilpotentSemidirectNilpotence
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.JointFixedReductionData.residualLayer_normal _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.abelianRealCoordinates _root_.OAI.PolycyclicRecognition.abelianRealFiniteDimensional _root_.OAI.PolycyclicRecognition.abelianRealLieAbelian _root_.OAI.PolycyclicRecognition.abelianRealNormedLie _root_.OAI.PolycyclicRecognition.derivationLieSpaceFiniteDimensional _root_.OAI.PolycyclicRecognition.derivationLieSpaceRealNormed _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.polynomialLieIdealSubgroup_normal _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Nilpotence of the constructed derivation semidirect Lie group -/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold

variable {L : Type*} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L] [LieRing.IsNilpotent L]
  (D : LieDerivation ℝ L L) (hD : IsNilpotent D.toLinearMap)

theorem derivationSemidirect_tangent_nilpotent :
    letI := derivationSemidirectGroup D hD
    letI := derivationSemidirectLieGroup D hD
    LieRing.IsNilpotent (GroupLieAlgebra (𝓘(ℝ, L × ℝ)) (L × ℝ)) := by
  let := derivationSemidirectGroup D hD
  let := derivationSemidirectLieGroup D hD
  let T := GroupLieAlgebra (𝓘(ℝ, L × ℝ)) (L × ℝ)
  let e : T ≃ₗ[ℝ] L × ℝ := LinearEquiv.refl ℝ (L × ℝ)
  apply nilpotent_derivation_extension e D.toLinearMap hD
  intro x y
  exact semidirect_tangent_bracket D hD (derivationSemidirect_one D hD)
    (derivationSemidirect_mul D hD) x.1 y.1 x.2 y.2

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_DerivationLieSpace
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.JointFixedReductionData.residualLayer_normal _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.abelianRealCoordinates _root_.OAI.PolycyclicRecognition.abelianRealFiniteDimensional _root_.OAI.PolycyclicRecognition.abelianRealLieAbelian _root_.OAI.PolycyclicRecognition.abelianRealNormedLie _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.polynomialLieIdealSubgroup_normal _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual tangent algebra of the derivation extension

The type synonym keeps exponential group coordinates distinct from the raw
semidirect group on the product vector space.
-/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold
variable {L : Type*} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L]

theorem derivationLieSpace_nilpotent [LieRing.IsNilpotent L]
    (D : LieDerivation ℝ L L) (hD : IsNilpotent D.toLinearMap) :
    LieRing.IsNilpotent (DerivationLieSpace D hD) :=
  derivationSemidirect_tangent_nilpotent D hD

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_PolynomialCoordinateEvaluation
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial maps detected by point evaluations

A finite-dimensional function space is separated by evaluations. Their span
is the whole dual, so polynomiality at every point gives polynomial coordinates.
-/

noncomputable section
namespace PolycyclicRecognition

theorem mem_multivariatePolynomialFunctions {I : Type*} {f : (I → ℝ) → ℝ} :
    f ∈ multivariatePolynomialFunctions I ↔
      ∃ p : MvPolynomial I ℝ, ∀ x, MvPolynomial.eval x p = f x := by
  change (∃ p, multivariatePolynomialEvaluation I p = f) ↔ _
  simp only [funext_iff]
  rfl

theorem coordinatePolynomial_iff_components {I J : Type*}
    {f : (I → ℝ) → (J → ℝ)} : IsCoordinatePolynomial f ↔
      ∀ j, (fun x => f x j) ∈ multivariatePolynomialFunctions I := by
  simp only [IsCoordinatePolynomial, mem_multivariatePolynomialFunctions]
  exact ⟨fun ⟨p, hp⟩ j => ⟨p j, fun x => hp x j⟩,
    fun h => by choose p hp using h; exact ⟨p, fun x j => hp j x⟩⟩

theorem IsCoordinatePolynomial.linear_pi {d : ℕ} {J : Type*}
    (A : (Fin d → ℝ) →ₗ[ℝ] (J → ℝ)) : IsCoordinatePolynomial A := by
  apply coordinatePolynomial_iff_components.mpr
  intro j
  let f : (Fin d → ℝ) →ₗ[ℝ] (Fin 1 → ℝ) :=
    LinearMap.pi (fun _ => (LinearMap.proj j).comp A)
  exact coordinatePolynomial_iff_components.mp (IsCoordinatePolynomial.linear f) 0

variable {I G V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

theorem polynomial_of_multivariate_evaluations
    (e : V →ₗ[ℝ] (G → ℝ)) (he : Function.Injective e)
    (F : (I → ℝ) → V)
    (hF : ∀ g, (fun x => e (F x) g) ∈ multivariatePolynomialFunctions I)
    (f : Module.Dual ℝ V) :
    (fun x => f (F x)) ∈ multivariatePolynomialFunctions I := by
  have hf : f ∈ Submodule.span ℝ (Set.range (coordinateEvaluation e)) := by
    rw [span_coordinateEvaluation e he]
    trivial
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨g, rfl⟩ := hf
    exact hF g
  | zero => exact (multivariatePolynomialFunctions I).zero_mem
  | add f g _ _ hf hg => exact (multivariatePolynomialFunctions I).add_mem hf hg
  | smul a f _ hf => exact (multivariatePolynomialFunctions I).smul_mem a hf

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_PolynomialMatrixFunctions
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial matrix exponentials and logarithms with uniform truncation -/

noncomputable section
namespace PolycyclicRecognition
open scoped BigOperators Matrix.Norms.Operator

theorem multivariatePolynomialFunctions_const {I : Type*} (r : ℝ) :
    (fun _ : I → ℝ => r) ∈ multivariatePolynomialFunctions I :=
  mem_multivariatePolynomialFunctions.mpr ⟨MvPolynomial.C r, fun _ => MvPolynomial.eval_C r⟩

theorem multivariatePolynomialFunctions_mul {I : Type*} {f g : (I → ℝ) → ℝ}
    (hf : f ∈ multivariatePolynomialFunctions I)
    (hg : g ∈ multivariatePolynomialFunctions I) :
    (fun x => f x * g x) ∈ multivariatePolynomialFunctions I := by
  obtain ⟨p, hp⟩ := mem_multivariatePolynomialFunctions.mp hf
  obtain ⟨q, hq⟩ := mem_multivariatePolynomialFunctions.mp hg
  exact mem_multivariatePolynomialFunctions.mpr
    ⟨p * q, fun x => by rw [map_mul, hp, hq]⟩

namespace HasPolynomialMatrixEntries
variable {I : Type*} {n : ℕ}
  {A B : (I → ℝ) → Matrix (Fin n) (Fin n) ℝ}

theorem linear {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {d : ℕ} (b : Module.Basis (Fin d) ℝ V)
    (f : V →ₗ[ℝ] Matrix (Fin n) (Fin n) ℝ) :
    HasPolynomialMatrixEntries (fun x => f (b.equivFun.symm x)) := by
  intro i j
  let a : (Fin d → ℝ) →ₗ[ℝ] ℝ := (LinearMap.proj j).comp
    ((LinearMap.proj i).comp (f.comp b.equivFun.symm.toLinearMap))
  let h : (Fin d → ℝ) →ₗ[ℝ] (Fin 1 → ℝ) := LinearMap.pi (fun _ => a)
  exact coordinatePolynomial_iff_components.mp (IsCoordinatePolynomial.linear h) 0

theorem linear_image {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {d : ℕ} (b : Module.Basis (Fin d) ℝ V)
    (f : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] V) (hA : HasPolynomialMatrixEntries A) :
    IsCoordinatePolynomial (fun x => b.equivFun (f (A x))) := by
  let e : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] ((Fin n × Fin n) → ℝ) :=
    { toFun M p := M p.1 p.2
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  have he : Function.Injective e := by
    intro M N h
    ext i j
    exact congrFun h (i, j)
  apply coordinatePolynomial_iff_components.mpr
  intro j
  exact polynomial_of_multivariate_evaluations e he A
    (fun p => hA p.1 p.2)
    ((LinearMap.proj j).comp (b.equivFun.toLinearMap.comp f))

theorem const (C : Matrix (Fin n) (Fin n) ℝ) :
    HasPolynomialMatrixEntries (fun _ : I → ℝ => C) :=
  fun i j => multivariatePolynomialFunctions_const (C i j)

theorem sub (hA : HasPolynomialMatrixEntries A) (hB : HasPolynomialMatrixEntries B) :
    HasPolynomialMatrixEntries (fun x => A x - B x) :=
  fun i j => (multivariatePolynomialFunctions I).sub_mem (hA i j) (hB i j)

theorem smul (r : ℝ) (hA : HasPolynomialMatrixEntries A) :
    HasPolynomialMatrixEntries (fun x => r • A x) :=
  fun i j => (multivariatePolynomialFunctions I).smul_mem r (hA i j)

theorem mul (hA : HasPolynomialMatrixEntries A) (hB : HasPolynomialMatrixEntries B) :
    HasPolynomialMatrixEntries (fun x => A x * B x) := by
  intro i j
  change (fun x => ∑ k, A x i k * B x k j) ∈ _
  convert (Submodule.sum_mem (multivariatePolynomialFunctions I) (t := Finset.univ)
    (fun k _ => multivariatePolynomialFunctions_mul (hA i k) (hB k j))) using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  simp only [Finset.sum_apply]

theorem pow (hA : HasPolynomialMatrixEntries A) (k : ℕ) :
    HasPolynomialMatrixEntries (fun x => A x ^ k) := by
  induction k with
  | zero => simpa only [pow_zero] using (const (I := I) (1 : Matrix (Fin n) (Fin n) ℝ))
  | succ k ih => simpa only [pow_succ] using ih.mul hA

theorem sum {K : Type*} (s : Finset K)
    (F : K → (I → ℝ) → Matrix (Fin n) (Fin n) ℝ)
    (hF : ∀ k ∈ s, HasPolynomialMatrixEntries (F k)) :
    HasPolynomialMatrixEntries (fun x => ∑ k ∈ s, F k x) := by
  intro i j
  simp only [Matrix.sum_apply]
  convert (Submodule.sum_mem (multivariatePolynomialFunctions I)
    (fun k hk => hF k hk i j)) using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  simp only [Finset.sum_apply]

theorem exp_of_pow_eq_zero (hA : HasPolynomialMatrixEntries A) (k : ℕ)
    (hk : ∀ x, A x ^ k = 0) :
    HasPolynomialMatrixEntries (fun x => NormedSpace.exp (A x)) := by
  have hp := sum (Finset.range k)
    (fun j x => ((j.factorial : ℝ)⁻¹) • A x ^ j)
    (fun j _ => (hA.pow j).smul _)
  intro i j
  have heq : (fun x => NormedSpace.exp (A x) i j) =
      (fun x => (∑ l ∈ Finset.range k, ((l.factorial : ℝ)⁻¹) • A x ^ l) i j) := by
    funext x
    exact congrArg (fun C : Matrix (Fin n) (Fin n) ℝ => C i j)
      (exp_eq_finite_sum_of_pow_eq_zero (A x) (hk x))
  rw [heq]
  exact hp i j

theorem finiteLog (hA : HasPolynomialMatrixEntries A) (k : ℕ) :
    HasPolynomialMatrixEntries (fun x => finiteNilpotentLog k (A x)) := by
  have hp := sum (Finset.range k)
    (fun j x => algebraMap ℚ (Matrix (Fin n) (Fin n) ℝ) ((PowerSeries.log ℚ).coeff j) * A x ^ j)
    (fun j _ => (const _).mul (hA.pow j))
  simpa only [finiteNilpotentLog, Polynomial.aeval_def, PowerSeries.eval₂_trunc_eq_sum_range] using hp

end HasPolynomialMatrixEntries
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_AnalyticNilpotentLogarithm
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite logarithms of analytic unipotent exponentials -/

noncomputable section
namespace PolycyclicRecognition

variable {A : Type*} [NormedRing A] [NormedAlgebra ℚ A]

theorem finiteNilpotentLog_analytic_exp (a : A) (n : ℕ) (ha : a ^ (n + 1) = 0) :
    finiteNilpotentLog (n + 1) (NormedSpace.exp a - 1) = a := by
  rw [analytic_exp_eq_nilpotent_exp ⟨n + 1, ha⟩]
  exact finiteNilpotentLog_exp a n ha

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_PolynomialExponentialChart
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial exponential charts from a faithful finite matrix model

Linear readout of the represented group gives polynomiality of the exponential.
A linear left inverse of the differential, applied to the finite matrix
logarithm, gives polynomiality of the inverse chart.
-/

noncomputable section
namespace PolycyclicRecognition
open scoped Matrix.Norms.Operator

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  {d e m : ℕ} (b : Module.Basis (Fin d) ℝ V) (c : Module.Basis (Fin e) ℝ W)

theorem polynomial_chart_of_finite_matrix_exp
    (C : V ≃ W) (ρ : W → Matrix (Fin m) (Fin m) ℝ)
    (j : V →ₗ[ℝ] Matrix (Fin m) (Fin m) ℝ) (hj : Function.Injective j)
    (R : Matrix (Fin m) (Fin m) ℝ →ₗ[ℝ] W)
    (hR : ∀ y, R (ρ y) = y)
    (hexp : ∀ x, ρ (C x) = NormedSpace.exp (j x))
    (hρ : HasPolynomialMatrixEntries (fun x => ρ (c.equivFun.symm x)))
    (k : ℕ) (hk : ∀ x, j x ^ (k + 1) = 0) :
    IsPolynomialInBasis b c C ∧ IsPolynomialInBasis c b C.symm := by
  let : NormedAlgebra ℚ (Matrix (Fin m) (Fin m) ℝ) := NormedAlgebra.restrictScalars ℚ ℝ _
  have hforward := ((HasPolynomialMatrixEntries.linear b j).exp_of_pow_eq_zero
    (k + 1) (fun x => hk (b.equivFun.symm x))).linear_image c R
  have hC (x : V) : R (NormedSpace.exp (j x)) = C x := by rw [← hexp, hR]
  have hp : IsPolynomialInBasis b c C := by
    simpa only [IsPolynomialInBasis, hC] using hforward
  obtain ⟨r, hr⟩ := j.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hj)
  have hinverse (y : W) : r (finiteNilpotentLog (k + 1) (ρ y - 1)) = C.symm y := by
    have he := hexp (C.symm y)
    rw [C.apply_symm_apply] at he
    rw [he]
    have hlog := finiteNilpotentLog_analytic_exp (j (C.symm y)) k (hk (C.symm y))
    exact (congrArg (fun A : Matrix (Fin m) (Fin m) ℝ => r A) hlog).trans
      (LinearMap.congr_fun hr _)
  have hback := ((hρ.sub (HasPolynomialMatrixEntries.const 1)).finiteLog (k + 1)).linear_image b r
  refine ⟨hp, ?_⟩
  simpa only [IsPolynomialInBasis, hinverse] using hback

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_PolynomialCoordinateAction
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial coordinate-orbit representations -/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold

variable {G Q I : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  [FiniteDimensional ℝ G] [Group G] [LieGroup (𝓘(ℝ, G)) ⊤ G]
  {m : ℕ} (q : Q → G → ℝ)
  (B : (Fin m → ℝ) ≃ₗ[ℝ] coordinateOrbitSpan q)

omit [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [LieGroup (𝓘(ℝ, G)) ⊤ G] in
theorem polynomial_coordinateAction (γ : (I → ℝ) → G)
    (hγ : ∀ a b i, (fun x => q i ((a * γ x) * b)) ∈ multivariatePolynomialFunctions I)
    (v : Fin m → ℝ) (f : Module.Dual ℝ (Fin m → ℝ)) :
    (fun x => f (smoothCoordinateAction q B (γ x) v)) ∈
      multivariatePolynomialFunctions I := by
  let e := (coordinateOrbitSpan q).subtype.comp B.toLinearMap
  apply polynomial_of_multivariate_evaluations e
    (Subtype.coe_injective.comp B.injective) _ ?_ f
  intro a
  change (fun x => (B (smoothCoordinateAction q B (γ x) v) : G → ℝ) a) ∈ _
  simp only [smoothCoordinateAction_eval]
  have hfun (u : G → ℝ) (hu : u ∈ coordinateOrbitSpan q) :
      (fun x => u (a * γ x)) ∈ multivariatePolynomialFunctions I := by
    induction hu using Submodule.span_induction with
    | mem u hu =>
      obtain ⟨⟨b, i⟩, rfl⟩ := hu
      exact hγ a b i
    | zero => exact (multivariatePolynomialFunctions I).zero_mem
    | add f g _ _ hf hg => exact (multivariatePolynomialFunctions I).add_mem hf hg
    | smul c f _ hf => exact (multivariatePolynomialFunctions I).smul_mem c hf
  exact hfun _ (B v).2

omit [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [LieGroup (𝓘(ℝ, G)) ⊤ G] in
theorem polynomial_coordinateMatrix (γ : (I → ℝ) → G)
    (hγ : ∀ a b i, (fun x => q i ((a * γ x) * b)) ∈ multivariatePolynomialFunctions I)
    (i j : Fin m) :
    (fun x => (coordinateMatrixRepresentation q B (γ x) : Matrix (Fin m) (Fin m) ℝ) i j) ∈
      multivariatePolynomialFunctions I := by
  exact polynomial_coordinateAction q B γ hγ (Pi.single j 1) (LinearMap.proj i)

omit [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [LieGroup (𝓘(ℝ, G)) ⊤ G] in
theorem coordinateMatrixReadout_apply (g : G) :
    coordinateMatrixReadout q B (coordinateMatrixRepresentation q B g) = fun i => q i g := by
  funext i
  dsimp only [coordinateMatrixReadout, LinearMap.coe_mk, AddHom.coe_mk]
  change (B (((LinearMap.toMatrixAlgEquiv' (smoothCoordinateAction q B g))).mulVec
    (B.symm ⟨q i, coordinate_mem_orbitSpan q i⟩)) : G → ℝ) 1 = q i g
  rw [← Matrix.toLin'_apply]
  change (B (Matrix.toLinAlgEquiv' (LinearMap.toMatrixAlgEquiv' (smoothCoordinateAction q B g))
    (B.symm ⟨q i, coordinate_mem_orbitSpan q i⟩)) : G → ℝ) 1 = q i g
  rw [Matrix.toLinAlgEquiv'_toMatrixAlgEquiv']
  change (B (smoothCoordinateAction q B g
    (B.symm ⟨q i, coordinate_mem_orbitSpan q i⟩)) : G → ℝ) 1 = q i g
  rw [smoothCoordinateAction_eval, B.apply_symm_apply, one_mul]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_PolynomialDerivationCoordinates
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.JointFixedReductionData.residualLayer_normal _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.abelianRealFiniteDimensional _root_.OAI.PolycyclicRecognition.abelianRealLieAbelian _root_.OAI.PolycyclicRecognition.abelianRealNormedLie _root_.OAI.PolycyclicRecognition.derivationLieSpaceFiniteDimensional _root_.OAI.PolycyclicRecognition.derivationLieSpaceRealNormed _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.polynomialLieIdealSubgroup_normal _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Joint polynomial coordinates of a nilpotent derivation flow -/

noncomputable section
namespace PolycyclicRecognition

theorem multivariatePolynomialFunctions_pow {I : Type*} {f : (I → ℝ) → ℝ}
    (hf : f ∈ multivariatePolynomialFunctions I) (k : ℕ) :
    (fun x => f x ^ k) ∈ multivariatePolynomialFunctions I := by
  obtain ⟨p, hp⟩ := mem_multivariatePolynomialFunctions.mp hf
  exact mem_multivariatePolynomialFunctions.mpr
    ⟨p ^ k, fun x => by rw [map_pow, hp]⟩

variable {I L : Type*} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  {n : ℕ} (b : Module.Basis (Fin n) ℝ L)

omit [FiniteDimensional ℝ L] in
theorem coordinatePolynomial_linear_map (A : L →ₗ[ℝ] L) (F : (I → ℝ) → L)
    (hF : IsCoordinatePolynomial (fun x => b.equivFun (F x))) :
    IsCoordinatePolynomial (fun x => b.equivFun (A (F x))) := by
  have h := IsCoordinatePolynomial.comp (IsPolynomialInBasis.linear (b := b) (c := b) A) hF
  simpa only [Function.comp_def, LinearEquiv.symm_apply_apply] using h

attribute [local instance] OAI.PolycyclicRecognition.polynomialDerivationCoordinatesRational
omit [FiniteDimensional ℝ L] in
theorem coordinatePolynomial_derivationFlow
    (D : LieDerivation ℝ L L) (hD : IsNilpotent D.toLinearMap)
    (f : (I → ℝ) → ℝ) (F : (I → ℝ) → L)
    (hf : f ∈ multivariatePolynomialFunctions I)
    (hF : IsCoordinatePolynomial (fun x => b.equivFun (F x))) :
    IsCoordinatePolynomial (fun x => b.equivFun (nilpotentDerivationFlow D hD (f x) (F x))) := by
  let k := nilpotencyClass D.toLinearMap
  have hk : D.toLinearMap ^ k = 0 := pow_nilpotencyClass hD
  apply coordinatePolynomial_iff_components.mpr
  intro j
  have heq : (fun x => b.equivFun (nilpotentDerivationFlow D hD (f x) (F x)) j) =
      ∑ i ∈ Finset.range k, (fun x => f x ^ i *
        b.equivFun (((i.factorial : ℚ)⁻¹ • D.toLinearMap ^ i) (F x)) j) := by
    funext x
    rw [nilpotentDerivationFlow_eq_sum D hD hk]
    simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [heq]
  apply Submodule.sum_mem
  intro i _
  exact multivariatePolynomialFunctions_mul (multivariatePolynomialFunctions_pow hf i)
    (coordinatePolynomial_iff_components.mp (coordinatePolynomial_linear_map b _ F hF) j)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_SemidirectPolynomialMaps
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.JointFixedReductionData.residualLayer_normal _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.abelianRealCoordinates _root_.OAI.PolycyclicRecognition.abelianRealFiniteDimensional _root_.OAI.PolycyclicRecognition.abelianRealLieAbelian _root_.OAI.PolycyclicRecognition.abelianRealNormedLie _root_.OAI.PolycyclicRecognition.derivationLieSpaceFiniteDimensional _root_.OAI.PolycyclicRecognition.derivationLieSpaceRealNormed _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.polynomialLieIdealSubgroup_normal _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Multivariate polynomial multiplication in the derivation extension -/

noncomputable section
namespace PolycyclicRecognition
variable {I L : Type*} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L] {n : ℕ}
  (b : Module.Basis (Fin n) ℝ L)

omit [FiniteDimensional ℝ L] P in
theorem polynomialSemidirectCoordinates_basis {d : ℕ}
    (c : Module.Basis (Fin d) ℝ (L × ℝ)) :
    HasPolynomialSemidirectCoordinates b (fun x => c.equivFun.symm x) :=
  IsCoordinatePolynomial.linear_pi
    ((semidirectCoordinateLinear b).comp c.equivFun.symm.toLinearMap)

omit [FiniteDimensional ℝ L] P in
theorem polynomialSemidirectCoordinates_const (v : L × ℝ) :
    HasPolynomialSemidirectCoordinates (I := I) b (fun _ => v) :=
  IsCoordinatePolynomial.const (semidirectCoordinateLinear b v)

theorem polynomialSemidirectCoordinates_mul
    (D : LieDerivation ℝ L L) (hD : IsNilpotent D.toLinearMap)
    (F H : (I → ℝ) → L × ℝ)
    (hF : HasPolynomialSemidirectCoordinates b F)
    (hH : HasPolynomialSemidirectCoordinates b H) :
    HasPolynomialSemidirectCoordinates b
      (fun x => (derivationSemidirectGroup D hD).mul (F x) (H x)) := by
  have hFl : IsCoordinatePolynomial (fun x => b.equivFun (F x).1) :=
    (IsCoordinatePolynomial.reindex (Sum.inl : Fin n → Fin n ⊕ Unit)).comp hF
  have hHl : IsCoordinatePolynomial (fun x => b.equivFun (H x).1) :=
    (IsCoordinatePolynomial.reindex (Sum.inl : Fin n → Fin n ⊕ Unit)).comp hH
  have hFr := coordinatePolynomial_iff_components.mp hF (.inr ())
  have hHr := coordinatePolynomial_iff_components.mp hH (.inr ())
  have hflow := coordinatePolynomial_derivationFlow b D hD
    (fun x => (F x).2) (fun x => (H x).1) hFr hHl
  have hprod := (coordinatePolynomial_dynkinProduct P.coefficients (basisBracket b)).comp
    (hFl.pair hflow)
  apply coordinatePolynomial_iff_components.mpr
  intro i
  cases i with
  | inl i =>
    have hp := coordinatePolynomial_iff_components.mp hprod i
    have hp' : (fun x => b.equivFun
        ((F x).1 * nilpotentDerivationFlow D hD (F x).2 (H x).1) i) ∈
        multivariatePolynomialFunctions I := by
      simpa only [Function.comp_def, Sum.elim_inl, Sum.elim_inr,
        basis_dynkinProduct, ← P.mul_eq] using hp
    simpa only [derivationSemidirect_mul, semidirectCoordinate,
      Module.Basis.equivFun_apply] using hp'
  | inr i => exact (multivariatePolynomialFunctions I).add_mem hFr hHr

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_SemidirectPolynomialRepresentation
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.JointFixedReductionData.residualLayer_normal _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.abelianRealCoordinates _root_.OAI.PolycyclicRecognition.abelianRealFiniteDimensional _root_.OAI.PolycyclicRecognition.abelianRealLieAbelian _root_.OAI.PolycyclicRecognition.abelianRealNormedLie _root_.OAI.PolycyclicRecognition.derivationLieSpaceFiniteDimensional _root_.OAI.PolycyclicRecognition.derivationLieSpaceRealNormed _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.polynomialLieIdealSubgroup_normal _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomiality and linear coordinate readout for the semidirect representation -/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold
variable {L : Type*} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L] {n m d : ℕ}
  (b : Module.Basis (Fin n) ℝ L)
  (D : LieDerivation ℝ L L) (hD : IsNilpotent D.toLinearMap)

theorem semidirectMatrixRepresentation_polynomial
    (c : Module.Basis (Fin d) ℝ (L × ℝ)) :
    letI := derivationSemidirectGroup D hD
    letI := derivationSemidirectLieGroup D hD
    ∀ B : (Fin m → ℝ) ≃ₗ[ℝ] coordinateOrbitSpan (semidirectCoordinate b),
    HasPolynomialMatrixEntries (fun x =>
      (coordinateMatrixRepresentation (semidirectCoordinate b) B (c.equivFun.symm x) :
        Matrix (Fin m) (Fin m) ℝ)) := by
  let := derivationSemidirectGroup D hD
  let := derivationSemidirectLieGroup D hD
  intro B i j
  apply polynomial_coordinateMatrix
  intro a z q
  have h := polynomialSemidirectCoordinates_mul b D hD _ _
    (polynomialSemidirectCoordinates_mul b D hD _ _
      (polynomialSemidirectCoordinates_const b a) (polynomialSemidirectCoordinates_basis b c))
    (polynomialSemidirectCoordinates_const b z)
  exact coordinatePolynomial_iff_components.mp h q

theorem semidirectMatrixReadout_apply (g : L × ℝ) :
    letI := derivationSemidirectGroup D hD
    letI := derivationSemidirectLieGroup D hD
    ∀ B : (Fin m → ℝ) ≃ₗ[ℝ] coordinateOrbitSpan (semidirectCoordinate b),
      semidirectMatrixReadout b D hD B
        (coordinateMatrixRepresentation (semidirectCoordinate b) B g) = g := by
  let := derivationSemidirectGroup D hD
  let := derivationSemidirectLieGroup D hD
  intro B
  change (semidirectCoordinateLinear b).leftInverse
    (coordinateMatrixReadout (semidirectCoordinate b) B
      (coordinateMatrixRepresentation (semidirectCoordinate b) B g)) = g
  rw [coordinateMatrixReadout_apply]
  exact LinearMap.leftInverse_apply_of_inj
    (LinearMap.ker_eq_bot.mpr (semidirectCoordinate_injective b)) g

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_SemidirectExponentialCoordinates
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.JointFixedReductionData.residualLayer_normal _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.abelianRealCoordinates _root_.OAI.PolycyclicRecognition.abelianRealFiniteDimensional _root_.OAI.PolycyclicRecognition.abelianRealLieAbelian _root_.OAI.PolycyclicRecognition.abelianRealNormedLie _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.polynomialLieIdealSubgroup_normal _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.heightRay_zero _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.CartanFactorModel.sampledProbeProfile_apply _root_.OAI.PolycyclicRecognition.JointFixedReductionData.residualLayerProjection_equiv _root_.OAI.PolycyclicRecognition.NilpotentKernelCompletion.extendedAction_embed _root_.OAI.PolycyclicRecognition.NilpotentLatticeCoordinates.automorphism_mul _root_.OAI.PolycyclicRecognition.NilpotentLatticeCoordinates.automorphism_on_lattice _root_.OAI.PolycyclicRecognition.NilpotentLatticeCoordinates.automorphism_one _root_.OAI.PolycyclicRecognition.PolynomialExponentialCoordinates.analyticDerivationAction_apply _root_.OAI.PolycyclicRecognition.abelianRealLatticeEquiv_apply _root_.OAI.PolycyclicRecognition.analyticDerivationExp_apply _root_.OAI.PolycyclicRecognition.derivationSemidirectHom_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.modelNilradicalLinearAction_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_mul _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_one _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.polynomialCoordinateHom_apply _root_.OAI.PolycyclicRecognition.polynomialInnerLieEquiv_apply _root_.OAI.PolycyclicRecognition.polynomialModelLieEquiv_apply _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial exponential coordinates for the derivation extension

The chart and its inverse are retained. Thus an ordered polynomial lattice
parameter can be transported into exponential coordinates at the next step.
-/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold ContDiff Matrix.Norms.Operator
attribute [local instance 100] LieRing.ofAssociativeRing

variable {L : Type*} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L] [LieRing.IsNilpotent L]
  (D : LieDerivation ℝ L L) (hD : IsNilpotent D.toLinearMap)

theorem exists_semidirect_polynomial_exponential_coordinates :
    letI := derivationSemidirectGroup D hD
    letI : Mul (L × ℝ) := (derivationSemidirectGroup D hD).toMul
    ∃ Q : PolynomialExponentialCoordinates (DerivationLieSpace D hD),
    letI := Q
    ∃ E : @MulEquiv (DerivationLieSpace D hD) (L × ℝ)
      Q.group.toMul (derivationSemidirectGroup D hD).toMul,
    ∀ {u v : ℕ} (a : Module.Basis (Fin u) ℝ (DerivationLieSpace D hD))
      (c : Module.Basis (Fin v) ℝ (L × ℝ)),
      IsPolynomialInBasis a c E.toEquiv ∧ IsPolynomialInBasis c a E.toEquiv.symm := by
  let := derivationSemidirectGroup D hD
  let _ : MulOneClass (L × ℝ) := (derivationSemidirectGroup D hD).toMulOneClass
  let _ : Mul (L × ℝ) := (derivationSemidirectGroup D hD).toMul
  let _ : One (L × ℝ) := (derivationSemidirectGroup D hD).toOne
  let _ : Monoid (L × ℝ) := (derivationSemidirectGroup D hD).toMonoid
  let := derivationSemidirectLieGroup D hD
  let N := derivationNilpotentLieModel D hD
  let b := Module.finBasis ℝ L
  let q := semidirectCoordinate b
  let := finiteDimensional_semidirectCoordinateOrbit b D hD
  let m := Module.finrank ℝ (coordinateOrbitSpan q)
  let B : (Fin m → ℝ) ≃ₗ[ℝ] coordinateOrbitSpan q :=
    (Module.finBasis ℝ (coordinateOrbitSpan q)).equivFun.symm
  have hq : ∀ i, ContDiff ℝ ∞ (q i) := contDiff_semidirectCoordinate b
  let ρ := coordinateMatrixRepresentation q B
  let j := coordinateMatrixDifferential q B hq
  have hi : Function.Injective ρ :=
    coordinateMatrixRepresentation_injective q B (semidirectCoordinate_injective b)
  have hj : Function.Injective j :=
    coordinateMatrixDifferential_injective q B hq (semidirectCoordinate_injective b)
  have hd := hasMFDerivAt_unitsHomLieDifferential ρ
    (contDiff_coordinateMatrixRepresentation q B hq).contMDiff
  obtain ⟨k, hk⟩ := semidirectMatrixProducts b D hD
    (derivationSemidirect_tangent_nilpotent D hD) B
  let : NormedAlgebra ℚ (Matrix (Fin m) (Fin m) ℝ) := NormedAlgebra.restrictScalars ℚ ℝ _
  have hprod (n : ℕ) (X : Fin n → GroupLieAlgebra (𝓘(ℝ, N.modelSpace)) N.carrier) :
      (List.ofFn (fun i => groupExponential (X i))).prod =
        groupExponential (finiteDynkinPolynomial (universalDynkinCoefficients k n) X) :=
    finite_bch_of_faithful_nilpotent_representation groupExponential
      groupExponential_isGroupExponential ρ hi j hd k (fun l hl => hk l hl.le) X
  obtain ⟨Q, E, hE⟩ := polynomialExponentialCoordinates_equiv_of_finite_products
    N (derivationLieSpace_nilpotent D hD) (universalDynkinCoefficients k) hprod
  let F : @MulEquiv (DerivationLieSpace D hD) (L × ℝ)
      Q.group.toMul (derivationSemidirectGroup D hD).toMul := E
  refine ⟨Q, F, ?_⟩
  intro u v a c
  let J := j.toLinearMap.comp N.equiv.toLinearMap
  refine polynomial_chart_of_finite_matrix_exp a c F.toEquiv
    (fun g => (ρ g : Matrix (Fin m) (Fin m) ℝ)) J
    (hj.comp N.equiv.injective) (semidirectMatrixReadout b D hD B)
    (fun g => semidirectMatrixReadout_apply b D hD g B) ?_ ?_ k ?_
  · intro x
    change (ρ (F.toEquiv x) : Matrix (Fin m) (Fin m) ℝ) =
      NormedSpace.exp (j (N.equiv x))
    calc
      _ = (ρ (groupExponential (E := L × ℝ) (G := L × ℝ) (N.equiv x)) :
          Matrix (Fin m) (Fin m) ℝ) :=
        congrArg (fun g : L × ℝ => (ρ g : Matrix (Fin m) (Fin m) ℝ)) (hE x)
      _ = _ := congrArg Units.val (coordinateMatrixDifferential_exp q B hq (N.equiv x))
  · exact semidirectMatrixRepresentation_polynomial b D hD c B
  · intro x
    change j (N.equiv x) ^ (k + 1) = 0
    let v : GroupLieAlgebra (𝓘(ℝ, L × ℝ)) (L × ℝ) := N.equiv x
    have h := hk (List.replicate (k + 1) v) (by simp)
    rw [List.map_replicate, List.prod_replicate] at h
    exact h

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_NilpotentLogIntertwiner
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite logarithms preserve linear intertwiners -/

noncomputable section
namespace PolycyclicRecognition
variable {𝕜 V W : Type*} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V]
  [AddCommGroup W] [Module 𝕜 W]

theorem end_polynomial_intertwiner (f : V →ₗ[𝕜] W)
    (A : Module.End 𝕜 V) (B : Module.End 𝕜 W)
    (h : ∀ x, f (A x) = B (f x)) (p : Polynomial 𝕜) (x : V) :
    f (Polynomial.aeval A p x) = Polynomial.aeval B p (f x) := by
  have hp (n : ℕ) (y : V) : f ((A ^ n) y) = (B ^ n) (f y) := by
    induction n with
    | zero => rfl
    | succ n ih => simp only [pow_succ', Module.End.mul_apply, h, ih]
  induction p using Polynomial.induction_on' with
  | add p q ihp ihq => simp only [map_add, LinearMap.add_apply, ihp, ihq]
  | monomial n r =>
    simp only [Polynomial.aeval_monomial, Module.End.mul_apply,
      Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply, Module.End.one_apply,
      map_smul, hp]

variable {V W : Type*} [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]

theorem nilpotentLog_intertwiner (f : V →ₗ[ℚ] W)
    (A : Module.End ℚ V) (B : Module.End ℚ W)
    (hA : IsNilpotent A) (hB : IsNilpotent B)
    (h : ∀ x, f (A x) = B (f x)) (x : V) :
    f (nilpotentLog A x) = nilpotentLog B (f x) := by
  let n := max (nilpotencyClass A) (nilpotencyClass B)
  have ha : A ^ (n + 1) = 0 := pow_eq_zero_of_le (by omega) (pow_nilpotencyClass hA)
  have hb : B ^ (n + 1) = 0 := pow_eq_zero_of_le (by omega) (pow_nilpotencyClass hB)
  rw [nilpotentLog_eq_of_pow A hA n ha, nilpotentLog_eq_of_pow B hB n hb]
  exact end_polynomial_intertwiner f A B h _ x

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_RealNilpotentLogIntertwiner
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Real-linear maps intertwine the canonical rational logarithm -/

noncomputable section
namespace PolycyclicRecognition
variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]

local instance realLogRationalSource_rf5d5e9_1 : Module ℚ V := Module.compHom V (algebraMap ℚ ℝ)
attribute [local instance] OAI.PolycyclicRecognition.realLogRationalTarget
local instance realLogRationalTowerV_rf5d5e9_1 : IsScalarTower ℚ ℝ V :=
  ⟨fun q r v => by change (algebraMap ℚ ℝ q * r) • v = algebraMap ℚ ℝ q • (r • v); rw [mul_smul]⟩
attribute [local instance] OAI.PolycyclicRecognition.realLogRationalTowerW
local instance realLogRationalCommV_rf5d5e9_1 : SMulCommClass ℝ ℚ V :=
  ⟨fun r q v => by change r • (algebraMap ℚ ℝ q • v) = algebraMap ℚ ℝ q • (r • v); rw [smul_comm]⟩
attribute [local instance] OAI.PolycyclicRecognition.realLogRationalCommW
theorem real_nilpotentLog_intertwiner (f : V →ₗ[ℝ] W)
    (A : Module.End ℝ V) (B : Module.End ℝ W)
    (hA : IsNilpotent A) (hB : IsNilpotent B)
    (h : ∀ x, f (A x) = B (f x)) (x : V) :
    f (nilpotentLog A x) = nilpotentLog B (f x) := by
  let rV := rationalEndRestriction V
  let rW := rationalEndRestriction W
  have hh := nilpotentLog_intertwiner (f.restrictScalars ℚ) (rV A) (rW B)
    (hA.map rV) (hB.map rW) h x
  rw [nilpotentLog_map rV A hA, nilpotentLog_map rW B hB] at hh
  exact hh

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_UnipotentConjugationFlow
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.JointFixedReductionData.residualLayer_normal _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.abelianRealCoordinates _root_.OAI.PolycyclicRecognition.abelianRealFiniteDimensional _root_.OAI.PolycyclicRecognition.abelianRealLieAbelian _root_.OAI.PolycyclicRecognition.abelianRealNormedLie _root_.OAI.PolycyclicRecognition.derivationLieSpaceFiniteDimensional _root_.OAI.PolycyclicRecognition.derivationLieSpaceRealNormed _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.polynomialLieIdealSubgroup_normal _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # An integral conjugation identity determines the real nilpotent flow -/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold ContDiff
variable {L M : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [RealNormedLieAlgebra M] [FiniteDimensional ℝ M]
  [Q : PolynomialExponentialCoordinates M] [LieRing.IsNilpotent M]

theorem unipotent_conjugation_log (A : L ≃ₗ⁅ℝ⁆ L)
    (hA : IsNilpotent (A.toLinearMap - 1)) (f : L →ₗ⁅ℝ⁆ M) (u : M)
    (h : ∀ x, f (A x) = u * f x * u⁻¹) (x : L) :
    f (unipotentLieLogarithm A hA x) = ⁅u, f x⁆ := by
  have hh := real_nilpotentLog_intertwiner f.toLinearMap
    (A.toLinearMap - 1) ((polynomialInnerLieEquiv u).toLinearMap - 1)
    hA (polynomial_inner_unipotent u) (by
      intro y
      change f (A y - y) = polynomialInnerLieEquiv u (f y) - f y
      rw [map_sub, h, polynomialInnerLieEquiv_apply]) x
  rw [polynomial_inner_log] at hh
  exact hh

theorem unipotent_conjugation_flow (A : L ≃ₗ⁅ℝ⁆ L)
    (hA : IsNilpotent (A.toLinearMap - 1)) (f : L →ₗ⁅ℝ⁆ M) (u : M)
    (h : ∀ x, f (A x) = u * f x * u⁻¹) (t : ℝ) (x : L) :
    f (unipotentLieFlow A hA t x) = (t • u) * f x * (t • u)⁻¹ := by
  have hh := derivationFlow_intrinsic_conjugation (unipotentLieLogarithm A hA)
    (unipotentLieLogarithm_nilpotent A hA)
    (fun v : GroupLieAlgebra (𝓘(ℝ, M)) M => (v : M))
    PolynomialExponentialCoordinates.isGroupExponential_identity
    (Q.tangentEquiv.toLinearMap.comp f.toLinearMap) (Q.tangentEquiv u)
    (by
      intro y
      change Q.tangentEquiv (f (unipotentLieLogarithm A hA y)) =
        ⁅Q.tangentEquiv u, Q.tangentEquiv (f y)⁆
      rw [unipotent_conjugation_log A hA f u h, Q.tangentEquiv.map_lie]) t x
  simp only [LinearMap.comp_apply, LieHom.coe_toLinearMap,
    LieEquiv.coe_toLieHom, Q.tangentEquiv_apply] at hh
  exact hh

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Lattices_NilpotentCyclicHomExtension
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.JointFixedReductionData.residualLayer_normal _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.abelianRealCoordinates _root_.OAI.PolycyclicRecognition.abelianRealFiniteDimensional _root_.OAI.PolycyclicRecognition.abelianRealLieAbelian _root_.OAI.PolycyclicRecognition.abelianRealNormedLie _root_.OAI.PolycyclicRecognition.derivationLieSpaceFiniteDimensional _root_.OAI.PolycyclicRecognition.derivationLieSpaceRealNormed _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.polynomialLieIdealSubgroup_normal _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Extending a nilpotent cyclic homomorphism to real time

The time-one conjugation relation supplies the full real action relation by
finite logarithms. No continuous extension is assumed.
-/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold ContDiff
variable {L M : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [RealNormedLieAlgebra M] [FiniteDimensional ℝ M]
  [P : PolynomialExponentialCoordinates L] [Q : PolynomialExponentialCoordinates M]
  [LieRing.IsNilpotent L] [LieRing.IsNilpotent M]

theorem nilpotent_cyclic_hom_extension (A : L ≃ₗ⁅ℝ⁆ L)
    (hA : IsNilpotent (A.toLinearMap - 1)) (f : L →ₗ⁅ℝ⁆ M) (u : M)
    (h : ∀ x, f (A x) = u * f x * u⁻¹) :
    let D := unipotentLieLogarithm A hA
    let hD := unipotentLieLogarithm_nilpotent A hA
    letI := derivationSemidirectGroup D hD
    letI : MulOneClass (L × ℝ) := (derivationSemidirectGroup D hD).toMulOneClass
    ∃ φ : (L × ℝ) →* M, ContMDiff (𝓘(ℝ, L × ℝ)) (𝓘(ℝ, M)) ∞ φ ∧
      ∀ p, φ p = f p.1 * (p.2 • u) := by
  let D := unipotentLieLogarithm A hA
  let hD := unipotentLieLogarithm_nilpotent A hA
  let := derivationSemidirectGroup D hD
  let : MulOneClass (L × ℝ) := (derivationSemidirectGroup D hD).toMulOneClass
  obtain ⟨k, hk, hkexp⟩ := integrate_polynomial_nilpotent
    (fun v : GroupLieAlgebra (𝓘(ℝ, M)) M => (v : M))
    PolynomialExponentialCoordinates.isGroupExponential_identity L
    (inferInstance : LieRing.IsNilpotent L) (Q.tangentEquiv.toLieHom.comp f)
  have hkf (x : L) : k x = f x := (hkexp x).trans (Q.tangentEquiv_apply (f x))
  have hact (t : ℝ) (x : L) :
      k (nilpotentDerivationFlow D hD t x) =
        (t • u) * k x * (t • u)⁻¹ := by
    rw [hkf, hkf]
    exact unipotent_conjugation_flow A hA f u h t x
  have hexp (t : ℝ) : (show M from t • Q.tangentEquiv u) = t • u :=
    (Q.tangentEquiv.map_smul t u).symm.trans (Q.tangentEquiv_apply (t • u))
  let φ := derivationSemidirectHom D hD
    (fun v : GroupLieAlgebra (𝓘(ℝ, M)) M => (v : M))
    PolynomialExponentialCoordinates.isGroupExponential_identity k (Q.tangentEquiv u)
    (by
      intro t x
      exact (hact t x).trans
        (congrArg (fun v : M => v * k x * v⁻¹) (hexp t).symm))
  refine ⟨φ, ?_, ?_⟩
  · exact contMDiff_derivationSemidirectHom D hD _ _ k _ _ hk
  · intro p
    change k p.1 * (show M from p.2 • Q.tangentEquiv u) = _
    rw [hkf, hexp]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Lattices_KernelCompletionCyclicHom
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.JointFixedReductionData.residualLayer_normal _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.abelianRealCoordinates _root_.OAI.PolycyclicRecognition.abelianRealFiniteDimensional _root_.OAI.PolycyclicRecognition.abelianRealLieAbelian _root_.OAI.PolycyclicRecognition.abelianRealNormedLie _root_.OAI.PolycyclicRecognition.derivationLieSpaceFiniteDimensional _root_.OAI.PolycyclicRecognition.derivationLieSpaceRealNormed _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.polynomialLieIdealSubgroup_normal _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.JointFixedReductionData.residualLayerProjection_equiv _root_.OAI.PolycyclicRecognition.NilpotentKernelCompletion.extendedAction_embed _root_.OAI.PolycyclicRecognition.NilpotentLatticeCoordinates.automorphism_mul _root_.OAI.PolycyclicRecognition.NilpotentLatticeCoordinates.automorphism_on_lattice _root_.OAI.PolycyclicRecognition.NilpotentLatticeCoordinates.automorphism_one _root_.OAI.PolycyclicRecognition.PolynomialExponentialCoordinates.analyticDerivationAction_apply _root_.OAI.PolycyclicRecognition.abelianRealLatticeEquiv_apply _root_.OAI.PolycyclicRecognition.analyticDerivationExp_apply _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Extending homomorphisms after one cyclic completion step -/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold ContDiff
variable {K H M : Type} [RealNormedLieAlgebra K] [FiniteDimensional ℝ K]
  [PK : PolynomialExponentialCoordinates K] [Group H]
  [RealNormedLieAlgebra M] [FiniteDimensional ℝ M]
  [PM : PolynomialExponentialCoordinates M] [LieRing.IsNilpotent M]
  {i : K →* H} (C : NilpotentKernelCompletion i)

theorem kernelCompletion_cyclic_hom (a : MulAut H)
    (A : C.carrier ≃ₗ⁅ℝ⁆ C.carrier) (hA : IsNilpotent (A.toLinearMap - 1))
    (hAe : ∀ h, A (C.embed h) = C.embed (a h))
    (F : (H ⋊[integerPowerAction a] Multiplicative ℤ) →* M)
    (hF : ContMDiff (𝓘(ℝ, K)) (𝓘(ℝ, M)) ∞ ((F.comp SemidirectProduct.inl).comp i)) :
    let D := unipotentLieLogarithm A hA
    let hD := unipotentLieLogarithm_nilpotent A hA
    letI := derivationSemidirectGroup D hD
    letI : MulOneClass (C.carrier × ℝ) := (derivationSemidirectGroup D hD).toMulOneClass
    ∃ φ : (C.carrier × ℝ) →* M,
      ContMDiff (𝓘(ℝ, C.carrier × ℝ)) (𝓘(ℝ, M)) ∞ φ ∧
      ∀ (h : H) (n : ℤ), φ (C.embed h, (n : ℝ)) = F ⟨h, Multiplicative.ofAdd n⟩ := by
  obtain ⟨f, hf, hfe⟩ := C.extend M (F.comp SemidirectProduct.inl) hF
  simp only [MonoidHom.comp_apply] at hfe
  let t : H ⋊[integerPowerAction a] Multiplicative ℤ :=
    SemidirectProduct.inr (Multiplicative.ofAdd (1 : ℤ))
  let u := F t
  have hconj (h : H) : F (SemidirectProduct.inl (a h)) =
      u * F (SemidirectProduct.inl h) * u⁻¹ := by
    have hh := SemidirectProduct.inl_aut (φ := integerPowerAction a)
      (Multiplicative.ofAdd (1 : ℤ)) h
    rw [map_inv] at hh
    change SemidirectProduct.inl ((a ^ (1 : ℤ)) h) = t * SemidirectProduct.inl h * t⁻¹ at hh
    simpa only [zpow_one, map_mul, map_inv] using congrArg F hh
  let B := PolynomialExponentialCoordinates.groupAutomorphism A
  have hb : ContMDiff (𝓘(ℝ, C.carrier)) (𝓘(ℝ, C.carrier)) ∞ B :=
    A.toLinearMap.toContinuousLinearMap.contDiff.contMDiff
  have hu : ContMDiff (𝓘(ℝ, M)) (𝓘(ℝ, M)) ∞ (MulAut.conj u) :=
    (contMDiff_conjugation u).of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have heq : f.comp B.toMonoidHom = (MulAut.conj u).toMonoidHom.comp f := by
    apply C.hom_ext M (f.comp B.toMonoidHom) ((MulAut.conj u).toMonoidHom.comp f)
      (hf.comp hb) (hu.comp hf)
    intro h
    change f (A (C.embed h)) = u * f (C.embed h) * u⁻¹
    rw [hAe, hfe, hfe]
    exact hconj h
  let fL := polynomialModelLieHom f hf
  have hL (x : C.carrier) : fL (A x) = u * fL x * u⁻¹ := by
    rw [polynomialModelLieHom_apply, polynomialModelLieHom_apply]
    exact DFunLike.congr_fun heq x
  obtain ⟨φ, hφ, hφx⟩ := nilpotent_cyclic_hom_extension A hA fL u hL
  refine ⟨φ, hφ, ?_⟩
  intro h n
  rw [hφx, polynomialModelLieHom_apply, hfe, ← model_zpow, ← map_zpow, ← map_mul]
  congr 1
  have ht : t ^ n = SemidirectProduct.inr (Multiplicative.ofAdd n) := by
    rw [← map_zpow]
    congr 1
    apply Multiplicative.ext
    change n • (1 : ℤ) = n
    simp
  rw [ht]
  exact (SemidirectProduct.mk_eq_inl_mul_inr _ _).symm

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Lattices_KernelCompletionCyclicStep
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.JointFixedReductionData.residualLayer_normal _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.abelianRealCoordinates _root_.OAI.PolycyclicRecognition.abelianRealFiniteDimensional _root_.OAI.PolycyclicRecognition.abelianRealLieAbelian _root_.OAI.PolycyclicRecognition.abelianRealNormedLie _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.polynomialLieIdealSubgroup_normal _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.JointFixedReductionData.residualLayerProjection_equiv _root_.OAI.PolycyclicRecognition.NilpotentKernelCompletion.extendedAction_embed _root_.OAI.PolycyclicRecognition.NilpotentLatticeCoordinates.automorphism_mul _root_.OAI.PolycyclicRecognition.NilpotentLatticeCoordinates.automorphism_on_lattice _root_.OAI.PolycyclicRecognition.NilpotentLatticeCoordinates.automorphism_one _root_.OAI.PolycyclicRecognition.PolynomialExponentialCoordinates.analyticDerivationAction_apply _root_.OAI.PolycyclicRecognition.abelianRealLatticeEquiv_apply _root_.OAI.PolycyclicRecognition.analyticDerivationExp_apply _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A cyclic step in completing a nilpotent extension with a real kernel

This constructs the next polynomial model, its faithful embedding, its integer
grid and its homomorphism extension property. No lattice in the kernel is
required.
-/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold ContDiff
variable {K H : Type} [RealNormedLieAlgebra K] [FiniteDimensional ℝ K]
  [PK : PolynomialExponentialCoordinates K] [Group H]
  {i : K →* H} (C : NilpotentKernelCompletion i)

namespace NilpotentKernelCompletion

theorem cyclic_step_with_dimension (a : MulAut H) (A : C.carrier ≃ₗ⁅ℝ⁆ C.carrier)
    (hA : IsNilpotent (A.toLinearMap - 1))
    (hAe : ∀ h, A (C.embed h) = C.embed (a h)) :
    ∃ C' : NilpotentKernelCompletion
      ((SemidirectProduct.inl : H →* H ⋊[integerPowerAction a] Multiplicative ℤ).comp i),
      C'.dimension = C.dimension + 1 := by
  let L := C.carrier
  let D := unipotentLieLogarithm A hA
  let hD := unipotentLieLogarithm_nilpotent A hA
  let φ := PolynomialExponentialCoordinates.derivationAction D hD
  have hstep (h : H) : C.embed (a h) = φ (Multiplicative.ofAdd 1) (C.embed h) := by
    change C.embed (a h) = unipotentLieFlow A hA 1 (C.embed h)
    rw [unipotentLieFlow_one, hAe]
  let I := realIntegerSemidirectMap φ a C.embed hstep
  have hI : Function.Injective I := realIntegerSemidirectMap_injective φ a C.embed hstep C.injective
  let := derivationSemidirectGroup D hD
  let : Mul (L × ℝ) := (derivationSemidirectGroup D hD).toMul
  let : MulOneClass (L × ℝ) := (derivationSemidirectGroup D hD).toMulOneClass
  let e : (L × ℝ) ≃* (L ⋊[φ] Multiplicative ℝ) :=
    { derivationSemidirectEquiv D hD with map_mul' := fun _ _ => rfl }
  let jR := e.symm.toMonoidHom.comp I
  have hjR (z : H ⋊[integerPowerAction a] Multiplicative ℤ) :
      jR z = (C.embed z.left, (z.right.toAdd : ℝ)) := rfl
  obtain ⟨Q, E, hE⟩ := exists_semidirect_polynomial_exponential_coordinates D hD
  let := Q
  let T := DerivationLieSpace D hD
  let : Group T := Q.group
  let : Mul T := Q.group.toMul
  let j := E.symm.toMonoidHom.comp jR
  have hj (z : H ⋊[integerPowerAction a] Multiplicative ℤ) :
      E (j z) = (C.embed z.left, (z.right.toAdd : ℝ)) := by
    change E (E.symm (jR z)) = _
    rw [E.apply_symm_apply, hjR]
  let s := derivationLieSpaceSplit D hD
  let b := cyclicParameterBasis C.basis s
  let c := Module.finBasis ℝ (L × ℝ)
  let p := transportedProductParameter C.parameter s E.toEquiv
  have hp := polynomial_transported_product_parameter C.basis c b
    C.parameter s E.toEquiv C.polynomial C.polynomial_symm (hE b c).1 (hE b c).2
  have hEinv : ContMDiff (𝓘(ℝ, L × ℝ)) (𝓘(ℝ, T)) ∞ E.symm :=
    ((hE b c).2.contDiff.of_le le_top).contMDiff
  have hEfor : ContMDiff (𝓘(ℝ, T)) (𝓘(ℝ, L × ℝ)) ∞ E :=
    ((hE b c).1.contDiff.of_le le_top).contMDiff
  refine ⟨{
    carrier := T
    nilpotent := derivationLieSpace_nilpotent D hD
    embed := j
    injective := E.symm.injective.comp (e.symm.injective.comp hI)
    kernel_smooth := ?_
    dimension := C.dimension + 1
    basis := b
    parameter := p
    polynomial := hp.1
    polynomial_symm := hp.2
    integer_grid := ?_
    extend := ?_ }, rfl⟩
  · have heq : (j.comp ((SemidirectProduct.inl : H →*
        H ⋊[integerPowerAction a] Multiplicative ℤ).comp i) : K → T) =
        fun x => E.symm (C.embed (i x), 0) := by
      funext x
      apply E.injective
      rw [E.apply_symm_apply]
      change E (j (SemidirectProduct.inl (i x))) = (C.embed (i x), 0)
      rw [hj]
      simp
    rw [heq]
    exact hEinv.comp (C.kernel_smooth.prodMk_space contMDiff_const)
  · intro z
    obtain ⟨h, hh⟩ := C.integer_grid (fun k => z k.castSucc)
    refine ⟨⟨h, Multiplicative.ofAdd (z (Fin.last C.dimension))⟩, ?_⟩
    apply E.injective
    rw [hj]
    have hparam := transportedProductParameter_integer C.basis C.parameter s E.toEquiv z
    change E (p (b.equivFun.symm (fun k => (z k : ℝ)))) =
      (C.parameter (C.basis.equivFun.symm (fun k => (z k.castSucc : ℝ))),
        (z (Fin.last C.dimension) : ℝ)) at hparam
    rw [hparam, hh]
    rfl
  · intro M _ _ PM hnil F hF
    obtain ⟨r, hr, hre⟩ := kernelCompletion_cyclic_hom C a A hA hAe F hF
    let f := r.comp E.toMonoidHom
    refine ⟨f, hr.comp hEfor, ?_⟩
    intro z
    change r (E (j z)) = F z
    rw [hj]
    exact hre z.left z.right.toAdd

end NilpotentKernelCompletion
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Lattices_KernelCompletionTransport
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.JointFixedReductionData.residualLayer_normal _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.abelianRealCoordinates _root_.OAI.PolycyclicRecognition.abelianRealFiniteDimensional _root_.OAI.PolycyclicRecognition.abelianRealLieAbelian _root_.OAI.PolycyclicRecognition.abelianRealNormedLie _root_.OAI.PolycyclicRecognition.derivationLieSpaceFiniteDimensional _root_.OAI.PolycyclicRecognition.derivationLieSpaceRealNormed _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.polynomialLieIdealSubgroup_normal _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Transporting a constructed completion across an exact group isomorphism -/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold ContDiff
variable {K H J : Type} [RealNormedLieAlgebra K] [FiniteDimensional ℝ K]
  [PK : PolynomialExponentialCoordinates K] [Group H] [Group J]
  {i : K →* H}

namespace NilpotentKernelCompletion

theorem exists_of_bijective_kernel_with_dimension [LieRing.IsNilpotent K]
    (i : K →* H) (hi : Function.Bijective i) :
    ∃ C : NilpotentKernelCompletion i, C.dimension = Module.finrank ℝ K := by
  let e := MulEquiv.ofBijective i hi
  have he : e.toMonoidHom.comp (MonoidHom.id K) = i := by ext x; rfl
  rw [← he]
  exact ⟨of_equiv of_polynomial_kernel e, rfl⟩

end NilpotentKernelCompletion
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Lattices_KernelCompletionUnipotentLift
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.JointFixedReductionData.residualLayer_normal _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.abelianRealCoordinates _root_.OAI.PolycyclicRecognition.abelianRealFiniteDimensional _root_.OAI.PolycyclicRecognition.abelianRealLieAbelian _root_.OAI.PolycyclicRecognition.abelianRealNormedLie _root_.OAI.PolycyclicRecognition.derivationLieSpaceFiniteDimensional _root_.OAI.PolycyclicRecognition.derivationLieSpaceRealNormed _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.polynomialLieIdealSubgroup_normal _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Nilpotent ambient conjugations extend as unipotent Lie automorphisms -/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold ContDiff
variable {K H G : Type} [RealNormedLieAlgebra K] [FiniteDimensional ℝ K]
  [PK : PolynomialExponentialCoordinates K] [Group H] [Group G] [Group.IsNilpotent G]
  {i : K →* H} (C : NilpotentKernelCompletion i)

namespace NilpotentKernelCompletion

theorem unipotent_conjugation_extension (j : H →* G) (hj : Function.Injective j)
    (a : MulAut H) (t : G) (hconj : ∀ h, j (a h) = t * j h * t⁻¹)
    (ha : ContMDiff (𝓘(ℝ, K)) (𝓘(ℝ, C.carrier)) ∞
      ((C.embed.comp a.toMonoidHom).comp i))
    (hai : ContMDiff (𝓘(ℝ, K)) (𝓘(ℝ, C.carrier)) ∞
      ((C.embed.comp a.symm.toMonoidHom).comp i)) :
    ∃ A : C.carrier ≃ₗ⁅ℝ⁆ C.carrier,
      IsNilpotent (A.toLinearMap - 1) ∧ ∀ h, A (C.embed h) = C.embed (a h) := by
  obtain ⟨B, hB, _, hBe⟩ := C.automorphism_extension a ha hai
  let A := polynomialModelLieEquiv B hB
  have hAe (h : H) : A (C.embed h) = C.embed (a h) := by
    rw [polynomialModelLieEquiv_apply]
    exact hBe h
  refine ⟨A, ?_, hAe⟩
  exact lattice_automorphism_unipotent C.basis C.parameter C.polynomial
    C.parameter.surjective C.embed C.integer_grid j hj a t hconj A.toLinearMap hAe

end NilpotentKernelCompletion
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Lattices_NilpotentCyclicKernelCompletion
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.JointFixedReductionData.residualLayer_normal _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.abelianRealCoordinates _root_.OAI.PolycyclicRecognition.abelianRealFiniteDimensional _root_.OAI.PolycyclicRecognition.abelianRealLieAbelian _root_.OAI.PolycyclicRecognition.abelianRealNormedLie _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.polynomialLieIdealSubgroup_normal _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.JointFixedReductionData.residualLayerProjection_equiv _root_.OAI.PolycyclicRecognition.NilpotentKernelCompletion.extendedAction_embed _root_.OAI.PolycyclicRecognition.NilpotentLatticeCoordinates.automorphism_mul _root_.OAI.PolycyclicRecognition.NilpotentLatticeCoordinates.automorphism_on_lattice _root_.OAI.PolycyclicRecognition.NilpotentLatticeCoordinates.automorphism_one _root_.OAI.PolycyclicRecognition.PolynomialExponentialCoordinates.analyticDerivationAction_apply _root_.OAI.PolycyclicRecognition.abelianRealLatticeEquiv_apply _root_.OAI.PolycyclicRecognition.analyticDerivationExp_apply _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Completing a nilpotent group across an actual cyclic quotient -/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold ContDiff
variable {K G : Type} [RealNormedLieAlgebra K] [FiniteDimensional ℝ K]
  [PK : PolynomialExponentialCoordinates K] [Group G] [Group.IsNilpotent G]

theorem nilpotent_cyclic_kernel_completion_with_dimension (q : G →* Multiplicative ℤ)
    (t : G) (ht : q t = Multiplicative.ofAdd 1)
    (i : K →* q.ker) (C : NilpotentKernelCompletion i)
    (ha : ContMDiff (𝓘(ℝ, K)) (𝓘(ℝ, C.carrier)) ∞
      ((C.embed.comp (MulAut.conjNormal (H := q.ker) t).toMonoidHom).comp i))
    (hai : ContMDiff (𝓘(ℝ, K)) (𝓘(ℝ, C.carrier)) ∞
      ((C.embed.comp (MulAut.conjNormal (H := q.ker) t).symm.toMonoidHom).comp i)) :
    ∃ D : NilpotentKernelCompletion (q.ker.subtype.comp i),
      D.dimension = C.dimension + 1 := by
  let a := MulAut.conjNormal (H := q.ker) t
  obtain ⟨A, hA, hAe⟩ := C.unipotent_conjugation_extension q.ker.subtype
    Subtype.val_injective a t (fun _ => rfl) ha hai
  obtain ⟨D, hD⟩ := C.cyclic_step_with_dimension a A hA hAe
  let e := cyclicKernelEquiv q t ht
  have he : e.toMonoidHom.comp ((SemidirectProduct.inl : q.ker →*
        q.ker ⋊[integerPowerAction a] Multiplicative ℤ).comp i) = q.ker.subtype.comp i := by
    ext x
    change (i x : G) * t ^ (1 : Multiplicative ℤ).toAdd = (i x : G)
    simp
  rw [← he]
  exact ⟨D.of_equiv e, hD⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Lattices_NilpotentIntegralKernelCompletion
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.JointFixedReductionData.residualLayer_normal _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.abelianRealCoordinates _root_.OAI.PolycyclicRecognition.abelianRealFiniteDimensional _root_.OAI.PolycyclicRecognition.abelianRealLieAbelian _root_.OAI.PolycyclicRecognition.abelianRealNormedLie _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.latticeNormalFlag_normal _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.polynomialLieIdealSubgroup_normal _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Completing every nilpotent extension of a real kernel by an integral lattice

The quotient rank induction removes an actual coordinate, completes its
kernel, and constructs the next real cyclic direction. The section relations
and all maps are retained through the group isomorphisms.
-/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold ContDiff
variable {K G : Type} [RealNormedLieAlgebra K] [FiniteDimensional ℝ K]
  [PK : PolynomialExponentialCoordinates K] [LieRing.IsNilpotent K]
  [Group G] [Group.IsNilpotent G]

theorem nilpotent_integral_kernel_completion_with_dimension {n : ℕ}
    (E : GroupExtension K G (IntegralLatticeGroup n))
    (hsmooth : ∀ g : G, ContMDiff (𝓘(ℝ, K)) (𝓘(ℝ, K)) ∞ (E.conjAct g)) :
    ∃ C : NilpotentKernelCompletion E.inl, C.dimension = Module.finrank ℝ K + n := by
  have main : ∀ m : ℕ, ∀ (H : Type) [Group H] [Group.IsNilpotent H],
      ∀ (S : GroupExtension K H (IntegralLatticeGroup m)),
      (∀ h : H, ContMDiff (𝓘(ℝ, K)) (𝓘(ℝ, K)) ∞ (S.conjAct h)) →
      ∃ C : NilpotentKernelCompletion S.inl, C.dimension = Module.finrank ℝ K + m := by
    intro m
    induction m with
    | zero =>
      intro H _ _ S _
      simpa only [Nat.add_zero] using
        NilpotentKernelCompletion.exists_of_bijective_kernel_with_dimension S.inl (by
          refine ⟨S.inl_injective, ?_⟩
          intro h
          have hh : h ∈ S.inl.range := by
            rw [S.range_inl_eq_ker_rightHom]
            change S.rightHom h = 1
            exact Subsingleton.elim _ _
          exact hh)
    | succ m ih =>
      intro H _ _ S hS
      let q := integralLastMap S
      let T := integralKernelExtension S
      have hT (h : q.ker) : ContMDiff (𝓘(ℝ, K)) (𝓘(ℝ, K)) ∞ (T.conjAct h) := by
        convert hS (h : H) using 1
        all_goals try with_reducible_and_instances rfl
        ext x
        exact integralKernelExtension_conjAct S h x
      obtain ⟨C, hC⟩ := ih q.ker T hT
      have hq : Function.Surjective q := (integralQuotientLast_surjective m).comp S.rightHom_surjective
      obtain ⟨t, ht⟩ := hq (Multiplicative.ofAdd 1)
      have hnormal (g : H) (x : K) :
          MulAut.conjNormal (H := q.ker) g (T.inl x) = T.inl (S.conjAct g x) := by
        apply Subtype.ext
        exact (S.inl_conjAct_comm (e := g) (n := x)).symm
      have hact (g : H) : ContMDiff (𝓘(ℝ, K)) (𝓘(ℝ, C.carrier)) ∞
          ((C.embed.comp (MulAut.conjNormal (H := q.ker) g).toMonoidHom).comp T.inl) := by
        have heq : ((C.embed.comp (MulAut.conjNormal (H := q.ker) g).toMonoidHom).comp
            T.inl : K → C.carrier) = fun x => C.embed (T.inl (S.conjAct g x)) := by
          funext x
          exact congrArg C.embed (hnormal g x)
        rw [heq]
        exact C.kernel_smooth.comp (hS g)
      have hai : ContMDiff (𝓘(ℝ, K)) (𝓘(ℝ, C.carrier)) ∞
          ((C.embed.comp (MulAut.conjNormal (H := q.ker) t).symm.toMonoidHom).comp T.inl) := by
        have hi : (MulAut.conjNormal (H := q.ker) t).symm =
            MulAut.conjNormal (H := q.ker) t⁻¹ := (map_inv _ t).symm
        rw [hi]
        exact hact t⁻¹
      obtain ⟨D, hD⟩ := nilpotent_cyclic_kernel_completion_with_dimension q t ht T.inl C (hact t) hai
      change NilpotentKernelCompletion S.inl at D
      exact ⟨D, hD.trans (by rw [hC, Nat.add_assoc])⟩
  exact main n G E hsmooth

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Lattices_KernelCompletionHeight
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.JointFixedReductionData.residualLayer_normal _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.latticeNormalFlag_normal _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.polynomialLieIdealSubgroup_normal _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.JointFixedReductionData.residualLayerProjection_equiv _root_.OAI.PolycyclicRecognition.NilpotentKernelCompletion.extendedAction_embed _root_.OAI.PolycyclicRecognition.NilpotentLatticeCoordinates.automorphism_mul _root_.OAI.PolycyclicRecognition.NilpotentLatticeCoordinates.automorphism_on_lattice _root_.OAI.PolycyclicRecognition.NilpotentLatticeCoordinates.automorphism_one _root_.OAI.PolycyclicRecognition.PolynomialExponentialCoordinates.analyticDerivationAction_apply _root_.OAI.PolycyclicRecognition.analyticDerivationExp_apply _root_.OAI.PolycyclicRecognition.commutingIntegralHom_generator _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The real quotient of a nilpotent kernel completion

The quotient homomorphism extends to the constructed completion. Its kernel
is exactly the original real kernel, by the dimension retained in the cyclic
construction. No exactness property is postulated for the completion.
-/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold ContDiff
variable {K G : Type} [RealNormedLieAlgebra K] [FiniteDimensional ℝ K]
  [PK : PolynomialExponentialCoordinates K] [Group G] {n : ℕ}

namespace NilpotentKernelCompletion
variable (E : GroupExtension K G (IntegralLatticeGroup n))
  (C : NilpotentKernelCompletion E.inl)

variable (π : C.carrier →* AbelianRealSpace n)
  (hπ : ContMDiff (𝓘(ℝ, C.carrier)) (𝓘(ℝ, AbelianRealSpace n)) ∞ π)
  (he : ∀ g, π (C.embed g) = integralRealHeight (E.rightHom g))

include hπ he in
theorem height_surjective : Function.Surjective π := by
  let f := (polynomialModelLieHom π hπ).toLinearMap
  have hr : LinearMap.range f = ⊤ := by
    apply top_unique
    have hb : Submodule.span ℝ (Set.range (Pi.basisFun ℝ (Fin n))) =
        (⊤ : Submodule ℝ (AbelianRealSpace n)) := (Pi.basisFun ℝ (Fin n)).span_eq
    rw [← hb]
    apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    obtain ⟨g, hg⟩ := E.rightHom_surjective (integralLatticeGenerator n j)
    refine ⟨C.embed g, ?_⟩
    change polynomialModelLieHom π hπ (C.embed g) = _
    rw [polynomialModelLieHom_apply, he, hg]
    exact integerVectorMap_basis j
  intro x
  obtain ⟨y, hy⟩ := (LinearMap.range_eq_top.mp hr) x
  exact ⟨y, (polynomialModelLieHom_apply π hπ y).symm.trans hy⟩

include hπ he in
theorem height_kernel_eq
    (hdim : C.dimension = Module.finrank ℝ K + n) :
    π.ker = (C.embed.comp E.inl).range := by
  let f := (polynomialModelLieHom π hπ).toLinearMap
  let k := (polynomialModelLieHom (C.embed.comp E.inl) C.kernel_smooth).toLinearMap
  have hk : Function.Injective k := by
    intro x y h
    apply E.inl_injective
    apply C.injective
    exact (polynomialModelLieHom_apply _ C.kernel_smooth x).symm.trans
      (h.trans (polynomialModelLieHom_apply _ C.kernel_smooth y))
  have hle : LinearMap.range k ≤ LinearMap.ker f := by
    rintro _ ⟨x, rfl⟩
    change polynomialModelLieHom π hπ (polynomialModelLieHom _ C.kernel_smooth x) = 0
    rw [polynomialModelLieHom_apply, polynomialModelLieHom_apply]
    change π (C.embed (E.inl x)) = 0
    rw [he, E.rightHom_inl, map_one]
    rfl
  have hfdim : Module.finrank ℝ (LinearMap.ker f) = Module.finrank ℝ K := by
    have hsurj : Function.Surjective f := by
      intro x
      obtain ⟨y, hy⟩ := C.height_surjective E π hπ he x
      exact ⟨y, (polynomialModelLieHom_apply π hπ y).trans hy⟩
    have hr := LinearMap.finrank_range_add_finrank_ker f
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top] at hr
    have hn : Module.finrank ℝ (AbelianRealSpace n) = n := by
      change Module.finrank ℝ (Fin n → ℝ) = n
      simp
    have hc : Module.finrank ℝ C.carrier = C.dimension := by
      simpa only [Fintype.card_fin] using Module.finrank_eq_card_basis C.basis
    rw [hn, hc, hdim] at hr
    omega
  have hkr : LinearMap.range k = LinearMap.ker f :=
    Submodule.eq_of_le_of_finrank_eq hle
      ((LinearMap.finrank_range_of_inj hk).trans hfdim.symm)
  ext y
  change π y = 1 ↔ ∃ x, C.embed (E.inl x) = y
  constructor
  · intro hy
    have hy' : y ∈ LinearMap.ker f := by
      change polynomialModelLieHom π hπ y = 0
      rw [polynomialModelLieHom_apply, hy]
      rfl
    rw [← hkr] at hy'
    obtain ⟨x, hx⟩ := hy'
    exact ⟨x, (polynomialModelLieHom_apply _ C.kernel_smooth x).symm.trans hx⟩
  · rintro ⟨x, rfl⟩
    rw [he, E.rightHom_inl, map_one]

end NilpotentKernelCompletion
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_ScaledIntegralCover
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.JointFixedReductionData.residualLayer_normal _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.latticeNormalFlag_normal _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.polynomialLieIdealSubgroup_normal _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A compact vector cover for a finite-power integer lattice -/

noncomputable section
namespace PolycyclicRecognition

theorem integralRealHeight_power (n m : ℕ) (z : IntegralLatticeGroup n) :
    integralRealHeight (latticePowerHom n m z) = (m : ℝ) • integralRealHeight z := by
  change integralRealHeight (z ^ m) = _
  rw [map_pow]
  exact (Nat.cast_smul_eq_nsmul ℝ m (integralRealHeight z)).symm

theorem scaledIntegral_compact_cover (n : ℕ) {m : ℕ} (hm : 0 < m) :
    ∃ K : Set (AbelianRealSpace n), IsCompact K ∧
      ∀ v : AbelianRealSpace n, ∃ (z : IntegralLatticeGroup n) (k : AbelianRealSpace n),
        k ∈ K ∧ integralRealHeight (latticePowerHom n m z) + k = v := by
  obtain ⟨K, hK, hc⟩ := (abelianRealLattice_uniform n).2
  refine ⟨(fun x : AbelianRealSpace n => (m : ℝ) • x) '' K,
    hK.image (((m : ℝ) • LinearMap.id :
      AbelianRealSpace n →ₗ[ℝ] AbelianRealSpace n).toContinuousLinearMap.continuous), ?_⟩
  intro v
  obtain ⟨a, u, hu, he⟩ := hc ((m : ℝ)⁻¹ • v)
  obtain ⟨z, hz⟩ := (abelianRealLatticeEquiv n).surjective a
  have hza : integralRealHeight z = (a : AbelianRealSpace n) := congrArg Subtype.val hz
  refine ⟨z, (m : ℝ) • u, ⟨u, hu, rfl⟩, ?_⟩
  rw [integralRealHeight_power, hza, ← smul_add]
  change (m : ℝ) • ((a : AbelianRealSpace n) + u) = v
  change (a : AbelianRealSpace n) + u = (m : ℝ)⁻¹ • v at he
  rw [he, smul_smul, mul_inv_cancel₀, one_smul]
  exact_mod_cast Nat.ne_of_gt hm

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Lattices_KernelCompletionEmbedding
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.JointFixedReductionData.residualLayer_normal _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.latticeNormalFlag_normal _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.polynomialLieIdealSubgroup_normal _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The completion embeds the original topology

The integer quotient is recovered continuously from the real height. On each
fiber a continuous linear left inverse recovers the original kernel coordinate.
-/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold ContDiff
attribute [local instance] factorExtensionTopology
variable {L : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L] {n : ℕ}
  (R : NonabelianFactorSystem L (IntegralLatticeGroup n))
  (C : NilpotentKernelCompletion (FactorExtension.inl R))
  (π : C.carrier →* AbelianRealSpace n)
  (hπ : ContMDiff (𝓘(ℝ, C.carrier)) (𝓘(ℝ, AbelianRealSpace n)) ∞ π)
  (he : ∀ a, π (C.embed a) = integralRealHeight a.right)

local instance completionEmbeddingTopologicalGroup : IsTopologicalGroup C.carrier :=
  topologicalGroup_of_lieGroup (𝓘(ℝ, C.carrier)) ⊤

theorem completion_factorization (a : FactorExtension R) :
    C.embed a = C.embed (FactorExtension.inl R a.left) *
      C.embed (⟨1, a.right⟩ : FactorExtension R) := by
  rw [← map_mul]
  apply congrArg C.embed
  apply FactorExtension.ext
  · change a.left = a.left * R.action 1 1 * R.factor 1 a.right
    rw [map_one, R.factor_one_left, mul_one, mul_one]
  · exact (one_mul _).symm

theorem kernelCompletion_continuous : Continuous C.embed := by
  have hs : Continuous (fun q : IntegralLatticeGroup n => C.embed (⟨1, q⟩ : FactorExtension R)) :=
    continuous_of_discreteTopology
  have hc := (C.kernel_smooth.continuous.comp (continuous_factor_left R)).mul
    (hs.comp (continuous_factor_right R))
  exact hc.congr (fun a => (completion_factorization R C a).symm)

include hπ he in
theorem kernelCompletion_isEmbedding : Topology.IsEmbedding C.embed := by
  let j := (polynomialModelLieHom (C.embed.comp (FactorExtension.inl R)) C.kernel_smooth).toLinearMap
  have hj (x : L) : j x = C.embed (FactorExtension.inl R x) :=
    polynomialModelLieHom_apply _ C.kernel_smooth x
  have hji : Function.Injective j := by
    intro x y h
    apply FactorExtension.inl_injective R
    apply C.injective
    exact (hj x).symm.trans (h.trans (hj y))
  obtain ⟨l, hl⟩ := j.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hji)
  let e : FactorExtension R ≃* C.embed.range := MonoidHom.ofInjective C.injective
  have hlat (x : C.embed.range) : π x.val ∈ abelianRealLattice n := by
    obtain ⟨a, ha⟩ := x.property
    rw [← ha, he]
    exact integerVectorMap_mem n a.right.toAdd
  let q : C.embed.range → IntegralLatticeGroup n := fun x =>
    (abelianRealLatticeEquiv n).symm ⟨π x.val, hlat x⟩
  have hq (a : FactorExtension R) : q (e a) = a.right := by
    apply (abelianRealLatticeEquiv n).injective
    apply Subtype.ext
    change ((abelianRealLatticeEquiv n) ((abelianRealLatticeEquiv n).symm
      ⟨π (C.embed a), hlat (e a)⟩) : AbelianRealSpace n) = _
    rw [MulEquiv.apply_symm_apply]
    exact he a
  have hqc : Continuous q := by
    let := (abelianRealLattice_uniform n).1
    exact (continuous_of_discreteTopology : Continuous (abelianRealLatticeEquiv n).symm).comp
      ((hπ.continuous.comp continuous_subtype_val).subtype_mk hlat)
  let r : C.embed.range → L := fun x => l
    (x.val * (C.embed (⟨1, q x⟩ : FactorExtension R))⁻¹)
  have hr (a : FactorExtension R) : r (e a) = a.left := by
    change l (C.embed a * (C.embed (⟨1, q (e a)⟩ : FactorExtension R))⁻¹) = a.left
    rw [hq, completion_factorization R C a, mul_inv_cancel_right, ← hj]
    exact LinearMap.congr_fun hl a.left
  have hrc : Continuous r := by
    have hs : Continuous (fun q : IntegralLatticeGroup n => C.embed (⟨1, q⟩ : FactorExtension R)) :=
      continuous_of_discreteTopology
    exact l.toContinuousLinearMap.continuous.comp
      (continuous_subtype_val.mul (hs.comp hqc).inv)
  have hinv : (e.symm : C.embed.range → FactorExtension R) = fun x => ⟨r x, q x⟩ := by
    funext x
    obtain ⟨a, rfl⟩ := e.surjective x
    rw [e.symm_apply_apply, hr, hq]
  have hei : Continuous e.symm := by
    rw [hinv]
    exact (factorExtensionHomeomorph R).symm.continuous.comp (hrc.prodMk hqc)
  let homeo : FactorExtension R ≃ₜ C.embed.range :=
    { e.toEquiv with
      continuous_toFun := (kernelCompletion_continuous R C).subtype_mk _
      continuous_invFun := hei }
  exact Topology.IsEmbedding.subtypeVal.comp homeo.isEmbedding

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_InvariantGraphLieModel
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.JointFixedReductionData.residualLayer_normal _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.abelianRealCoordinates _root_.OAI.PolycyclicRecognition.abelianRealFiniteDimensional _root_.OAI.PolycyclicRecognition.abelianRealLieAbelian _root_.OAI.PolycyclicRecognition.abelianRealNormedLie _root_.OAI.PolycyclicRecognition.derivationLieSpaceFiniteDimensional _root_.OAI.PolycyclicRecognition.derivationLieSpaceRealNormed _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.polynomialLieIdealSubgroup_normal _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The analytic solvable model on an invariant graph

The graph uses the original vector-space chart. Its operations are analytic,
and its dimension is the dimension of the nilpotent group alone.
-/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold ContDiff
attribute [local instance] semidirectProductTopology
variable {L V : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L] [Group.IsSolvable L]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  (φ : Multiplicative V →* MulAut L) (τ : L →* Multiplicative V)
  (hinv : ∀ v x, τ (φ v x) = τ x)
  (hφ : ContDiff ℝ ⊤ (fun p : V × L => φ (Multiplicative.ofAdd p.1) p.2))
  (hτ : ContDiff ℝ ⊤ (fun x => (τ x).toAdd))

omit [FiniteDimensional ℝ V] in
theorem invariantGraphModelEquiv_continuous : Continuous (invariantGraphModelEquiv φ τ hinv hφ hτ) :=
  (rotationalTwistHomeomorph φ τ hinv hτ.continuous).symm.continuous

omit [FiniteDimensional ℝ V] in
theorem invariantGraphModelEquiv_symm_continuous :
    Continuous (invariantGraphModelEquiv φ τ hinv hφ hτ).symm :=
  (rotationalTwistHomeomorph φ τ hinv hτ.continuous).continuous

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_RelativeNilpotentExtension
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Compatibility with OpenAI's Mathlib (d13f23b): one-sided `commutator_mono`. -/

private theorem Subgroup.commutator_mono_right_p2 {G : Type*} [Group G] {H K₁ K₂ : Subgroup G} (h : K₁ ≤ K₂) :
    ⁅H, K₁⁆ ≤ ⁅H, K₂⁆ :=
  Subgroup.commutator_mono le_rfl h
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

namespace OAI

/-! # Nilpotence from a terminating relative kernel series -/

namespace PolycyclicRecognition
open scoped commutatorElement IsMulCommutative
variable {N G Q : Type} [Group N] [Group G] [Group Q] [IsMulCommutative Q]

theorem nilpotent_of_relative_kernel_series (E : GroupExtension N G Q)
    (c : ℕ) (hc : relativeCommutatorSeries ⊤ E.inl.range c = ⊥) :
    Group.IsNilpotent G := by
  have hbase : (⊤ : Subgroup G).lowerCentralSeries 1 ≤ E.inl.range := by
    rw [E.range_inl_eq_ker_rightHom, Subgroup.lowerCentralSeries_succ,
      Subgroup.lowerCentralSeries_zero]
    apply Subgroup.commutator_le.mpr
    intro g _ h _
    change E.rightHom ⁅g, h⁆ = 1
    simp only [commutatorElement_def, map_mul, map_inv]
    rw [mul_comm (E.rightHom g) (E.rightHom h)]
    group
  have hbound (n : ℕ) : (⊤ : Subgroup G).lowerCentralSeries (n + 1) ≤
      relativeCommutatorSeries ⊤ E.inl.range n := by
    induction n with
    | zero => exact hbase
    | succ n ih =>
      rw [Subgroup.lowerCentralSeries_succ, Subgroup.commutator_comm]
      exact Subgroup.commutator_mono_right_p2 ih
  apply Subgroup.nilpotent_iff_lowerCentralSeries.mpr
  exact ⟨c + 1, eq_bot_iff.mpr (hc ▸ hbound c)⟩

theorem relative_series_descends_finite_layers {H : Type} [Group H]
    (K : Subgroup H) (F : ℕ → Subgroup H)
    (hstep : ∀ i, ∃ c, relativeCommutatorSeries K (F i) c ≤ F (i + 1)) (k : ℕ) :
    ∃ c, relativeCommutatorSeries K (F 0) c ≤ F k := by
  induction k with
  | zero => exact ⟨0, le_rfl⟩
  | succ k ih =>
    obtain ⟨a, ha⟩ := ih
    obtain ⟨b, hb⟩ := hstep k
    refine ⟨a + b, ?_⟩
    rw [relativeCommutatorSeries_add]
    exact (relativeCommutatorSeries_mono K ha b).trans hb

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_PolynomialLowerCentralProjection
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.JointFixedReductionData.residualLayer_normal _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.abelianRealCoordinates _root_.OAI.PolycyclicRecognition.abelianRealFiniteDimensional _root_.OAI.PolycyclicRecognition.abelianRealLieAbelian _root_.OAI.PolycyclicRecognition.abelianRealNormedLie _root_.OAI.PolycyclicRecognition.derivationLieSpaceFiniteDimensional _root_.OAI.PolycyclicRecognition.derivationLieSpaceRealNormed _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Additive coordinates on the polynomial group's lower-central layers -/

noncomputable section
namespace PolycyclicRecognition
open LieModule
attribute [local instance] polynomialSubalgebraGroup
variable {L : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L]

theorem polynomialLowerCentralProjection_eq_one_iff (K : LieSubalgebra ℝ L) (k : ℕ)
    (x : polynomialLieIdealSubgroup K (lowerCentralSeries ℝ K K k)) :
    polynomialLowerCentralProjection K k x = 1 ↔
      (x : K) ∈ lowerCentralSeries ℝ K K (k + 1) := by
  let U := (lowerCentralSeries ℝ K K k).toSubmodule
  let W := (lowerCentralSeries ℝ K K (k + 1)).toSubmodule.comap U.subtype
  change Multiplicative.ofAdd (Submodule.Quotient.mk
    (⟨x.val, x.property⟩ : U) : U ⧸ W) =
      Multiplicative.ofAdd 0 ↔ _
  constructor
  · intro h
    exact (Submodule.Quotient.mk_eq_zero W).mp (congrArg Multiplicative.toAdd h)
  · intro h
    apply Multiplicative.ext
    exact (Submodule.Quotient.mk_eq_zero W).mpr h

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_SubgroupExtensionSection
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Normalized extension sections with values in a surjective subgroup -/

noncomputable section
namespace PolycyclicRecognition
variable {N G Q : Type*} [Group N] [Group G] [Group Q]

theorem exists_normalized_section_in_subgroup (E : GroupExtension N G Q) (H : Subgroup G)
    (hs : Function.Surjective (E.rightHom.comp H.subtype)) :
    ∃ σ : E.Section, σ 1 = 1 ∧ ∀ q, σ q ∈ H := by
  classical
  let f : Q → H := Function.surjInv hs
  have hf : ∀ q, E.rightHom (f q) = q := Function.surjInv_eq hs
  let σ : E.Section :=
    { toFun q := if q = 1 then 1 else (f q : G)
      rightInverse_rightHom q := by
        change E.rightHom (if q = 1 then 1 else (f q : G)) = q
        split_ifs with h
        · simp only [h, map_one]
        · exact hf q }
  refine ⟨σ, ?_, ?_⟩
  · change (if (1 : Q) = 1 then (1 : G) else (f 1 : G)) = 1
    simp
  · intro q
    change (if q = 1 then (1 : G) else (f q : G)) ∈ H
    split_ifs
    · exact H.one_mem
    · exact (f q).property

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_SemisimpleCentralizerExtension
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.JointFixedReductionData.residualLayer_normal _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.abelianRealCoordinates _root_.OAI.PolycyclicRecognition.abelianRealFiniteDimensional _root_.OAI.PolycyclicRecognition.abelianRealLieAbelian _root_.OAI.PolycyclicRecognition.abelianRealNormedLie _root_.OAI.PolycyclicRecognition.derivationLieSpaceFiniteDimensional _root_.OAI.PolycyclicRecognition.derivationLieSpaceRealNormed _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.polynomialLieIdealSubgroup_normal _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact extension carried by a semisimple centralizer -/

noncomputable section
namespace PolycyclicRecognition
attribute [local instance] polynomialSubalgebraGroup
variable {L G Q : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L] [LieRing.IsNilpotent L]
  [Group G] [Group Q]

theorem inl_mem_semisimpleCentralizer_iff (E : GroupExtension L G Q)
    (S : L ≃ₗ⁅ℝ⁆ L) (x : L) :
    E.inl x ∈ semisimpleActionCentralizer E S ↔ x ∈ innerCentralizerLieSubalgebra S := by
  rw [mem_innerCentralizerLieSubalgebra_iff]
  change E.conjAct (E.inl x) ∈
    Subgroup.centralizer {PolynomialExponentialCoordinates.groupAutomorphism (P := P) S} ↔ _
  rw [extension_conjAct_inl, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    apply LinearMap.ext
    intro y
    have hh := congrArg (fun f : MulAut L => f y) h
    change x * S y * x⁻¹ = S (x * y * x⁻¹) at hh
    change S (polynomialInnerLieEquiv x y) = polynomialInnerLieEquiv x (S y)
    simpa only [polynomialInnerLieEquiv_apply] using hh.symm
  · intro h
    apply DFunLike.ext
    intro y
    have hh : S (polynomialInnerLieEquiv x y) = polynomialInnerLieEquiv x (S y) :=
      LinearMap.congr_fun h.eq y
    change x * S y * x⁻¹ = S (x * y * x⁻¹)
    simpa only [polynomialInnerLieEquiv_apply] using hh.symm

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CentralizerLiftJordanFactor
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.JointFixedReductionData.residualLayer_normal _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.abelianRealCoordinates _root_.OAI.PolycyclicRecognition.abelianRealFiniteDimensional _root_.OAI.PolycyclicRecognition.abelianRealLieAbelian _root_.OAI.PolycyclicRecognition.abelianRealNormedLie _root_.OAI.PolycyclicRecognition.derivationLieSpaceFiniteDimensional _root_.OAI.PolycyclicRecognition.derivationLieSpaceRealNormed _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.polynomialLieIdealSubgroup_normal _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # All lifts in a centralizer fiber retain the same semisimple factor -/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold ContDiff
variable {L G Q : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L] [LieRing.IsNilpotent L]
  [Group G] [Group Q]

theorem inner_centralizer_preserves_jordan_factor (A S U : L ≃ₗ⁅ℝ⁆ L)
    (hU : IsNilpotent (U.toLinearMap - 1))
    (hSU : Commute S.toLinearMap U.toLinearMap)
    (hA : A.toLinearMap = S.toLinearMap * U.toLinearMap)
    (v : L) (hv : Commute S.toLinearMap (polynomialInnerLieEquiv v).toLinearMap) :
    ∃ W : L ≃ₗ⁅ℝ⁆ L, IsNilpotent (W.toLinearMap - 1) ∧
      Commute S.toLinearMap W.toLinearMap ∧
      (polynomialInnerLieEquiv v).toLinearMap * A.toLinearMap = S.toLinearMap * W.toLinearMap := by
  let W := U.trans (polynomialInnerLieEquiv v)
  have hW : W.toLinearMap = (polynomialInnerLieEquiv v).toLinearMap * U.toLinearMap := rfl
  refine ⟨W, polynomial_inner_mul_unipotent U hU v, ?_, ?_⟩
  · rw [hW]
    exact hv.mul_right hSU
  · rw [hA, hW, ← mul_assoc, hv.symm.eq, mul_assoc]

theorem centralizer_same_fiber_jordan_factor (E : GroupExtension L G Q)
    (hsmooth : ∀ g : G, ContMDiff (𝓘(ℝ, L)) (𝓘(ℝ, L)) ∞ (E.conjAct g))
    (S U : L ≃ₗ⁅ℝ⁆ L) (t g : G)
    (ht : t ∈ semisimpleActionCentralizer E S)
    (hg : g ∈ semisimpleActionCentralizer E S)
    (hgt : E.rightHom g = E.rightHom t)
    (hU : IsNilpotent (U.toLinearMap - 1))
    (hSU : Commute S.toLinearMap U.toLinearMap)
    (hA : (polynomialModelLieEquiv (E.conjAct t) (hsmooth t)).toLinearMap =
      S.toLinearMap * U.toLinearMap) :
    ∃ W : L ≃ₗ⁅ℝ⁆ L, IsNilpotent (W.toLinearMap - 1) ∧
      Commute S.toLinearMap W.toLinearMap ∧
      (polynomialModelLieEquiv (E.conjAct g) (hsmooth g)).toLinearMap =
        S.toLinearMap * W.toLinearMap := by
  have hn : g * t⁻¹ ∈ E.inl.range := by
    rw [E.range_inl_eq_ker_rightHom]
    change E.rightHom (g * t⁻¹) = 1
    rw [map_mul, map_inv, hgt, mul_inv_cancel]
  obtain ⟨v, hv⟩ := hn
  have hvm : v ∈ innerCentralizerLieSubalgebra S :=
    (inl_mem_semisimpleCentralizer_iff E S v).mp (by
      rw [hv]
      exact (semisimpleActionCentralizer E S).mul_mem hg
        ((semisimpleActionCentralizer E S).inv_mem ht))
  obtain ⟨W, hW, hSW, he⟩ := inner_centralizer_preserves_jordan_factor
    (polynomialModelLieEquiv (E.conjAct t) (hsmooth t)) S U hU hSU hA v
    ((mem_innerCentralizerLieSubalgebra_iff S v).mp hvm)
  refine ⟨W, hW, hSW, ?_⟩
  have hvg : E.inl v * t = g := by rw [hv]; group
  rw [← hvg, extension_conjugationLinear_inl_mul]
  exact he

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Lattices_FiniteFixedCocycleSection
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.JointFixedReductionData.residualLayer_normal _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.abelianRealCoordinates _root_.OAI.PolycyclicRecognition.abelianRealFiniteDimensional _root_.OAI.PolycyclicRecognition.abelianRealLieAbelian _root_.OAI.PolycyclicRecognition.abelianRealNormedLie _root_.OAI.PolycyclicRecognition.derivationLieSpaceFiniteDimensional _root_.OAI.PolycyclicRecognition.derivationLieSpaceRealNormed _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instLocallyCompactSpaceFactorExtension _root_.OAI.PolycyclicRecognition.instT2SpaceFactorExtension _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.polynomialLieIdealSubgroup_normal _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

namespace OAI

/-! # Simultaneously fixed section factors for finitely many quotient lifts

The original extension has a normalized section centralizing a finite
commuting semisimple family. All its factors are fixed by that entire family,
and the specified quotient elements retain their semisimple Jordan factors.
-/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold ContDiff IsMulCommutative
variable {L G Q : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L] [LieRing.IsNilpotent L]
  [Group G] [Group Q] [IsMulCommutative Q]

omit [LieRing.IsNilpotent L] [IsMulCommutative Q] in
theorem inl_mem_semisimpleCentralizer_of_center (E : GroupExtension L G Q)
    (S : L ≃ₗ⁅ℝ⁆ L) (x : L) (hx : x ∈ Subgroup.center L) :
    E.inl x ∈ semisimpleActionCentralizer E S := by
  have hi : MulAut.conj x = 1 := by
    apply DFunLike.ext
    intro y
    change x * y * x⁻¹ = y
    rw [← Subgroup.mem_center_iff.mp hx y]
    group
  change E.conjAct (E.inl x) ∈
    Subgroup.centralizer {PolynomialExponentialCoordinates.groupAutomorphism (P := P) S}
  rw [extension_conjAct_inl, hi]
  exact Subgroup.one_mem _

theorem exists_finite_fixed_cocycle_section (E : GroupExtension L G Q)
    (hsmooth : ∀ g : G, ContMDiff (𝓘(ℝ, L)) (𝓘(ℝ, L)) ∞ (E.conjAct g)) (qs : List Q) :
    ∃ ss : List (L ≃ₗ⁅ℝ⁆ L),
      (∀ S ∈ ss, Module.End.IsSemisimple S.toLinearMap) ∧
      (∀ S ∈ ss, ∀ T ∈ ss, Commute S.toLinearMap T.toLinearMap) ∧
      ∃ σ : E.Section, σ 1 = 1 ∧
        (∀ S ∈ ss, ∀ q, σ q ∈ semisimpleActionCentralizer E S) ∧
        (∀ S ∈ ss, ∀ q r, S (GroupExtensionSection.factor E σ q r) =
          GroupExtensionSection.factor E σ q r) ∧
        ∀ q ∈ qs, ∃ S ∈ ss, ∃ U : L ≃ₗ⁅ℝ⁆ L,
          IsNilpotent (U.toLinearMap - 1) ∧ Commute S.toLinearMap U.toLinearMap ∧
          (polynomialModelLieEquiv (E.conjAct (σ q)) (hsmooth (σ q))).toLinearMap =
            S.toLinearMap * U.toLinearMap := by
  classical
  obtain ⟨ss₀, hss₀, hpair₀, hsurj, hlifts⟩ := exists_finite_semisimple_lift_family E hsmooth qs
  have hh : ∀ q : {q : Q // q ∈ qs}, ∃ g : G,
      g ∈ commonSemisimpleCentralizer E ss₀ ∧ E.rightHom g = (q : Q) ∧
      ∃ S ∈ ss₀, ∃ U : L ≃ₗ⁅ℝ⁆ L, IsNilpotent (U.toLinearMap - 1) ∧
        Commute S.toLinearMap U.toLinearMap ∧
        (polynomialModelLieEquiv (E.conjAct g) (hsmooth g)).toLinearMap =
          S.toLinearMap * U.toLinearMap := fun q => hlifts q q.property
  choose g hg hgq s hs u hu hsu hgu using hh
  let ss := qs.attach.map s
  have hmem (S : L ≃ₗ⁅ℝ⁆ L) (hS : S ∈ ss) : S ∈ ss₀ := by
    obtain ⟨q, _, hq⟩ := List.mem_map.mp hS
    rw [← hq]
    exact hs q
  obtain ⟨σ, hσ, hσH⟩ := exists_normalized_section_in_subgroup E
    (commonSemisimpleCentralizer E ss₀) hsurj
  have hσS : ∀ S ∈ ss₀, ∀ q, σ q ∈ semisimpleActionCentralizer E S :=
    fun S hS q => (mem_commonSemisimpleCentralizer E ss₀ (σ q)).mp (hσH q) S hS
  let F := GroupExtensionSection.factorSystem E σ hσ
  let A := fun q => polynomialModelLieEquiv (E.conjAct (σ q)) (hsmooth (σ q))
  have hact : ∀ q x, F.action q x = A q x :=
    fun _ _ => (polynomialModelLieEquiv_apply _ _ _).symm
  have hcomm : ∀ S ∈ ss, ∀ q, Commute S.toLinearMap (A q).toLinearMap := by
    intro S hS q
    exact (mem_semisimpleActionCentralizer_iff E S (σ q) (hsmooth (σ q))).mp
      (hσS S (hmem S hS) q)
  have hpair : ∀ S ∈ ss, ∀ T ∈ ss, Commute S.toLinearMap T.toLinearMap :=
    fun S hS T hT => hpair₀ S (hmem S hS) T (hmem T hT)
  have hsemisimple : ∀ S ∈ ss, Module.End.IsSemisimple S.toLinearMap :=
    fun S hS => hss₀ S (hmem S hS)
  have hlift : ∀ S ∈ ss, ∃ q₀ : Q, ∃ U : L ≃ₗ⁅ℝ⁆ L,
      IsNilpotent (U.toLinearMap - 1) ∧ Commute S.toLinearMap U.toLinearMap ∧
      (A q₀).toLinearMap = S.toLinearMap * U.toLinearMap := by
    intro S hS
    obtain ⟨q, _, hq⟩ := List.mem_map.mp hS
    subst S
    obtain ⟨W, hW, hsW, he⟩ := centralizer_same_fiber_jordan_factor E hsmooth (s q) (u q)
      (g q) (σ q) ((mem_commonSemisimpleCentralizer E ss₀ _).mp (hg q) _ (hs q))
      (hσS _ (hs q) q) ((σ.rightHom_section q).trans (hgq q).symm) (hu q) (hsu q) (hgu q)
    exact ⟨q, W, hW, hsW, he⟩
  obtain ⟨b, hb, hbZ, _, hfixed⟩ := finite_semisimple_cocycle_reduction F A hact ss
    hsemisimple hpair hcomm hlift
  let θ := GroupExtensionSection.gaugeSection E σ b
  have hθS : ∀ S ∈ ss, ∀ q, θ q ∈ semisimpleActionCentralizer E S := by
    intro S hS q
    exact (semisimpleActionCentralizer E S).mul_mem
      (inl_mem_semisimpleCentralizer_of_center E S (b q) (hbZ q)) (hσS S (hmem S hS) q)
  refine ⟨ss, hsemisimple, hpair, θ, GroupExtensionSection.gaugeSection_one E σ hσ b hb,
    hθS, ?_, ?_⟩
  · intro S hS q r
    rw [GroupExtensionSection.factor_gaugeSection E σ hσ b hb]
    exact hfixed S hS q r
  · intro q hq
    let i : {q : Q // q ∈ qs} := ⟨q, hq⟩
    have hi : s i ∈ ss := List.mem_map.mpr ⟨i, List.mem_attach _ _, rfl⟩
    obtain ⟨W, hW, hsW, he⟩ := centralizer_same_fiber_jordan_factor E hsmooth (s i) (u i)
      (g i) (θ q) ((mem_commonSemisimpleCentralizer E ss₀ _).mp (hg i) _ (hs i))
      (hθS _ hi q) ((θ.rightHom_section q).trans (hgq i).symm) (hu i) (hsu i) (hgu i)
    exact ⟨s i, hi, W, hW, hsW, he⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Lattices_JointFixedSubalgebra
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.JointFixedReductionData.residualLayer_normal _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.abelianRealFiniteDimensional _root_.OAI.PolycyclicRecognition.abelianRealLieAbelian _root_.OAI.PolycyclicRecognition.abelianRealNormedLie _root_.OAI.PolycyclicRecognition.derivationLieSpaceFiniteDimensional _root_.OAI.PolycyclicRecognition.derivationLieSpaceRealNormed _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.polynomialLieIdealSubgroup_normal _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The joint fixed algebra and its unipotent quotient-lift actions -/

noncomputable section
namespace PolycyclicRecognition
attribute [local instance] polynomialSubalgebraGroup
variable {L : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]

omit [FiniteDimensional ℝ L] in
theorem jointFixedLinearAction_unipotent (ss : List (L ≃ₗ⁅ℝ⁆ L))
    (S U T : L ≃ₗ⁅ℝ⁆ L) (hS : S ∈ ss)
    (hT : ∀ R ∈ ss, Commute R.toLinearMap T.toLinearMap)
    (hU : IsNilpotent (U.toLinearMap - 1)) (hSU : Commute S.toLinearMap U.toLinearMap)
    (hTU : T.toLinearMap = S.toLinearMap * U.toLinearMap) :
    IsNilpotent (jointFixedLinearAction ss T hT - 1) := by
  have hUx (x : L) (hx : x ∈ jointFixedLieSubalgebra ss) : T x = U x := by
    have hh : T x = S (U x) := LinearMap.congr_fun hTU x
    have hc : S (U x) = U (S x) := LinearMap.congr_fun hSU.eq x
    rw [hh, hc, (mem_jointFixedLieSubalgebra ss x).mp hx S hS]
  have hUp : ∀ x ∈ (jointFixedLieSubalgebra ss).toSubmodule, U x ∈ jointFixedLieSubalgebra ss := by
    intro x hx
    rw [← hUx x hx]
    exact commuting_lieEquiv_preserves_jointFixed ss T hT x hx
  have hdiffp : ∀ x ∈ (jointFixedLieSubalgebra ss).toSubmodule,
      (U.toLinearMap - 1) x ∈ jointFixedLieSubalgebra ss := by
    intro x hx
    exact (jointFixedLieSubalgebra ss).sub_mem (hUp x hx) hx
  have hn := Module.End.isNilpotent.restrict hdiffp hU
  have he : jointFixedLinearAction ss T hT - 1 = (U.toLinearMap - 1).restrict hdiffp := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change T x - (x : L) = U x - (x : L)
    rw [hUx x x.property]
  rwa [he]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Lattices_JointFixedReductionData
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.JointFixedReductionData.residualLayer_normal _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.abelianRealCoordinates _root_.OAI.PolycyclicRecognition.abelianRealFiniteDimensional _root_.OAI.PolycyclicRecognition.abelianRealLieAbelian _root_.OAI.PolycyclicRecognition.abelianRealNormedLie _root_.OAI.PolycyclicRecognition.derivationLieSpaceFiniteDimensional _root_.OAI.PolycyclicRecognition.derivationLieSpaceRealNormed _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

namespace OAI

/-! # Constructed joint-fixed residual data for an actual extension

The residual group is defined by the actual section factors and embeds in the
original extension. The prescribed quotient lifts act unipotently on its
kernel Lie algebra.
-/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold ContDiff IsMulCommutative
attribute [local instance] polynomialSubalgebraGroup
variable {L G Q : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L] [LieRing.IsNilpotent L]
  [Group G] [Group Q]

theorem exists_jointFixedReductionData [IsMulCommutative Q] (E : GroupExtension L G Q)
    (hsmooth : ∀ g : G, ContMDiff (𝓘(ℝ, L)) (𝓘(ℝ, L)) ∞ (E.conjAct g)) (qs : List Q) :
    Nonempty (JointFixedReductionData E hsmooth qs) := by
  obtain ⟨ss, hss, hpair, σ, hσ, hcent, hfixed, hlifts⟩ :=
    exists_finite_fixed_cocycle_section E hsmooth qs
  exact ⟨⟨ss, hss, hpair, σ, hσ, hcent, hfixed, hlifts⟩⟩

namespace JointFixedReductionData
variable {E : GroupExtension L G Q}
  {hsmooth : ∀ g : G, ContMDiff (𝓘(ℝ, L)) (𝓘(ℝ, L)) ∞ (E.conjAct g)} {qs : List Q}
  (D : JointFixedReductionData E hsmooth qs)

omit [LieRing.IsNilpotent L] in
theorem residual_generator_unipotent (q : Q) (hq : q ∈ qs) :
    IsNilpotent (jointFixedLinearAction D.operators (D.action q)
      (fun S hS => D.action_commutes S hS q) - 1) := by
  obtain ⟨S, hS, U, hU, hSU, hA⟩ := D.jordanLifts q hq
  exact jointFixedLinearAction_unipotent D.operators S U (D.action q) hS
    (fun T hT => D.action_commutes T hT q) hU hSU hA

end JointFixedReductionData
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Lattices_JointFixedLayerAction
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.JointFixedReductionData.residualLayer_normal _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.abelianRealCoordinates _root_.OAI.PolycyclicRecognition.abelianRealFiniteDimensional _root_.OAI.PolycyclicRecognition.abelianRealLieAbelian _root_.OAI.PolycyclicRecognition.abelianRealNormedLie _root_.OAI.PolycyclicRecognition.derivationLieSpaceFiniteDimensional _root_.OAI.PolycyclicRecognition.derivationLieSpaceRealNormed _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

namespace OAI

/-! # The abelian quotient acts on the residual lower-central layers

Inner section factors disappear on these layers, so this is an actual linear
representation of the quotient. Its selected generators are unipotent.
-/

noncomputable section
namespace PolycyclicRecognition
open LieModule
open scoped Manifold ContDiff IsMulCommutative
attribute [local instance] polynomialSubalgebraGroup
variable {L G Q : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L] [LieRing.IsNilpotent L]
  [Group G] [Group Q]
  {E : GroupExtension L G Q}
  {hsmooth : ∀ g : G, ContMDiff (𝓘(ℝ, L)) (𝓘(ℝ, L)) ∞ (E.conjAct g)} {qs : List Q}

namespace JointFixedReductionData
variable (D : JointFixedReductionData E hsmooth qs)

omit [LieRing.IsNilpotent L] in
theorem layer_generator_unipotent (k : ℕ) (q : Q) (hq : q ∈ qs) :
    IsNilpotent (D.layerAction k q - 1) :=
  invariantLayerEnd_unipotent _ _ _
    (jointFixed_action_preserves_lowerCentral D.operators (D.action q)
      (fun S hS => D.action_commutes S hS q) k)
    (jointFixed_action_preserves_lowerCentral D.operators (D.action q)
      (fun S hS => D.action_commutes S hS q) (k + 1))
    (D.residual_generator_unipotent q hq)

omit [LieRing.IsNilpotent L] in
theorem layer_action_filtration [IsMulCommutative Q]
    (hgen : Subgroup.closure {q | q ∈ qs} = ⊤) (k : ℕ) :
    ∃ c, linearActionFiltration (fun q => D.layerAction k q - 1) c = ⊥ :=
  unipotent_generated_abelian_action_filtration (D.layerAction k) qs hgen
    (D.layer_generator_unipotent k)

end JointFixedReductionData
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_ResidualLowerCentralLayers
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.abelianRealCoordinates _root_.OAI.PolycyclicRecognition.abelianRealFiniteDimensional _root_.OAI.PolycyclicRecognition.abelianRealLieAbelian _root_.OAI.PolycyclicRecognition.abelianRealNormedLie _root_.OAI.PolycyclicRecognition.derivationLieSpaceFiniteDimensional _root_.OAI.PolycyclicRecognition.derivationLieSpaceRealNormed _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instLocallyCompactSpaceFactorExtension _root_.OAI.PolycyclicRecognition.instT2SpaceFactorExtension _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

namespace OAI

/-! # Group commutators on the joint-fixed lower-central layers -/

noncomputable section
namespace PolycyclicRecognition
open LieModule
open scoped Manifold ContDiff IsMulCommutative
attribute [local instance] polynomialSubalgebraGroup
variable {L G Q : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L] [LieRing.IsNilpotent L]
  [Group G] [Group Q] [IsMulCommutative Q]
  {E : GroupExtension L G Q}
  {hsmooth : ∀ g : G, ContMDiff (𝓘(ℝ, L)) (𝓘(ℝ, L)) ∞ (E.conjAct g)} {qs : List Q}

namespace JointFixedReductionData
variable (D : JointFixedReductionData E hsmooth qs)

omit [LieRing.IsNilpotent L] [IsMulCommutative Q] in
theorem residualLayerProjection_kernel_le (k : ℕ) :
    (D.residualLayerProjection k).ker.map (D.residualLayer k).subtype ≤ D.residualLayer (k + 1) := by
  rintro _ ⟨a, ha, rfl⟩
  obtain ⟨x, rfl⟩ := (D.residualLayerEquiv k).surjective a
  have hx : (x : jointFixedLieSubalgebra D.operators) ∈ lowerCentralSeries ℝ
      (jointFixedLieSubalgebra D.operators) (jointFixedLieSubalgebra D.operators) (k + 1) := by
    apply (polynomialLowerCentralProjection_eq_one_iff _ k x).mp
    change D.residualLayerProjection k (D.residualLayerEquiv k x) = 1 at ha
    rwa [residualLayerProjection_equiv] at ha
  exact ⟨x, hx, rfl⟩

omit [LieRing.IsNilpotent L] [IsMulCommutative Q] in
theorem residualLayerProjection_equivariant (k : ℕ)
    (g : FactorExtension D.residualSystem) (a : D.residualLayer k) :
    (D.residualLayerProjection k (MulAut.conjNormal (H := D.residualLayer k) g a)).toAdd =
      D.layerAction k g.right (D.residualLayerProjection k a).toAdd := by
  obtain ⟨x, rfl⟩ := (D.residualLayerEquiv k).surjective a
  let E₀ := FactorExtension.groupExtension D.residualSystem
  let y : D.residualKernelLayer k := ⟨E₀.conjAct g x, by
    rw [FactorExtension.conjugation_inl]
    exact polynomialSubalgebra_conjugate_mem _ _ _
      (jointFixed_action_preserves_lowerCentral D.operators (D.action g.right)
        (fun S hS => D.action_commutes S hS _) k x x.property) g.left⟩
  have he : MulAut.conjNormal (H := D.residualLayer k) g (D.residualLayerEquiv k x) =
      D.residualLayerEquiv k y := by
    apply Subtype.ext
    exact E₀.inl_conjAct_comm.symm
  rw [he, residualLayerProjection_equiv, residualLayerProjection_equiv]
  apply (Submodule.Quotient.eq _).mpr
  change E₀.conjAct g x - D.residualSystem.action g.right x ∈
    lowerCentralSeries ℝ (jointFixedLieSubalgebra D.operators) _ (k + 1)
  rw [FactorExtension.conjugation_inl]
  exact polynomialSubalgebra_inner_difference _ g.left k _
    (jointFixed_action_preserves_lowerCentral D.operators (D.action g.right)
      (fun S hS => D.action_commutes S hS _) k x x.property)

omit [LieRing.IsNilpotent L] in
theorem residualLayer_commutator_bound
    (hgen : Subgroup.closure {q | q ∈ qs} = ⊤) (k : ℕ) :
    ∃ c, relativeCommutatorSeries ⊤ (D.residualLayer k) c ≤ D.residualLayer (k + 1) := by
  obtain ⟨c, hc⟩ := D.layer_action_filtration hgen k
  let ρ := (D.layerAction k).comp (FactorExtension.projection D.residualSystem)
  have hρ : linearActionFiltration
      (fun g : (⊤ : Subgroup (FactorExtension D.residualSystem)) => ρ g - 1) c = ⊥ := by
    apply eq_bot_iff.mpr
    exact (linearActionFiltration_comp_le (fun q => D.layerAction k q - 1)
      (fun g : (⊤ : Subgroup (FactorExtension D.residualSystem)) => g.val.right) c).trans
      (le_of_eq hc)
  exact ⟨c, (relativeCommutatorSeries_le_kernel_of_endFiltration ⊤ (D.residualLayer k)
    ρ (D.residualLayerProjection k) (D.residualLayerProjection_equivariant k) c hρ).trans
      (D.residualLayerProjection_kernel_le k)⟩

end JointFixedReductionData
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Lattices_JointFixedResidualNilpotent
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.abelianRealCoordinates _root_.OAI.PolycyclicRecognition.abelianRealFiniteDimensional _root_.OAI.PolycyclicRecognition.abelianRealLieAbelian _root_.OAI.PolycyclicRecognition.abelianRealNormedLie _root_.OAI.PolycyclicRecognition.derivationLieSpaceFiniteDimensional _root_.OAI.PolycyclicRecognition.derivationLieSpaceRealNormed _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instLocallyCompactSpaceFactorExtension _root_.OAI.PolycyclicRecognition.instT2SpaceFactorExtension _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.NilpotentKernelCompletion.extendedAction_embed _root_.OAI.PolycyclicRecognition.NilpotentLatticeCoordinates.automorphism_mul _root_.OAI.PolycyclicRecognition.NilpotentLatticeCoordinates.automorphism_on_lattice _root_.OAI.PolycyclicRecognition.NilpotentLatticeCoordinates.automorphism_one _root_.OAI.PolycyclicRecognition.PolynomialExponentialCoordinates.analyticDerivationAction_apply _root_.OAI.PolycyclicRecognition.abelianRealLatticeEquiv_apply _root_.OAI.PolycyclicRecognition.analyticDerivationExp_apply _root_.OAI.PolycyclicRecognition.derivationSemidirectHom_apply _root_.OAI.PolycyclicRecognition.polynomialCoordinateHom_apply _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

namespace OAI

/-! # The actual joint-fixed residual extension is nilpotent

The quotient need not split. Its unipotent action has finite length on every
intrinsic Lie lower-central layer, and the cocycle disappears on those layers.
-/

noncomputable section
namespace PolycyclicRecognition
open LieModule
open scoped Manifold ContDiff IsMulCommutative
attribute [local instance] polynomialSubalgebraGroup
variable {L G Q : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L] [LieRing.IsNilpotent L]
  [Group G] [Group Q] [IsMulCommutative Q]
  {E : GroupExtension L G Q}
  {hsmooth : ∀ g : G, ContMDiff (𝓘(ℝ, L)) (𝓘(ℝ, L)) ∞ (E.conjAct g)} {qs : List Q}

namespace JointFixedReductionData
variable (D : JointFixedReductionData E hsmooth qs)

theorem residual_nilpotent (hgen : Subgroup.closure {q | q ∈ qs} = ⊤) :
    Group.IsNilpotent (FactorExtension D.residualSystem) := by
  let K := jointFixedLieSubalgebra D.operators
  let : LieRing.IsNilpotent K := Function.Injective.lieAlgebra_isNilpotent
    (f := K.incl) Subtype.val_injective
  obtain ⟨d, hd⟩ := (LieModule.isNilpotent_iff ℝ K K).mp
    (inferInstance : LieModule.IsNilpotent K K)
  have hbot : D.residualLayer d = ⊥ := by
    have hk : D.residualKernelLayer d = ⊥ := by
      apply eq_bot_iff.mpr
      intro x hx
      change x ∈ lowerCentralSeries ℝ K K d at hx
      rw [hd] at hx
      change x = 1
      exact hx.trans (Subtype.ext P.one_eq_zero).symm
    rw [residualLayer, hk, Subgroup.map_bot]
  have hzero : D.residualLayer 0 =
      (FactorExtension.groupExtension D.residualSystem).inl.range := by
    have hk : D.residualKernelLayer 0 = ⊤ := by
      ext x
      simp only [Subgroup.mem_top, iff_true]
      change x ∈ lowerCentralSeries ℝ K K 0
      simp
    rw [residualLayer, hk, ← MonoidHom.range_eq_map]
    rfl
  obtain ⟨c, hc⟩ := relative_series_descends_finite_layers ⊤ D.residualLayer
    (D.residualLayer_commutator_bound hgen) d
  apply nilpotent_of_relative_kernel_series (FactorExtension.groupExtension D.residualSystem) c
  rw [← hzero]
  exact eq_bot_iff.mpr (hbot ▸ hc)

end JointFixedReductionData
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_UnipotentExtensionNilpotence
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.abelianRealCoordinates _root_.OAI.PolycyclicRecognition.abelianRealFiniteDimensional _root_.OAI.PolycyclicRecognition.abelianRealLieAbelian _root_.OAI.PolycyclicRecognition.abelianRealNormedLie _root_.OAI.PolycyclicRecognition.derivationLieSpaceFiniteDimensional _root_.OAI.PolycyclicRecognition.derivationLieSpaceRealNormed _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instLocallyCompactSpaceFactorExtension _root_.OAI.PolycyclicRecognition.instT2SpaceFactorExtension _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

namespace OAI

/-! # Nilpotence from unipotent quotient generators

This applies the proved lower-central-layer argument to the entire kernel:
the auxiliary fixed family consists only of the identity operator.
-/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold ContDiff IsMulCommutative
attribute [local instance] polynomialSubalgebraGroup
variable {L G Q : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L] [LieRing.IsNilpotent L]
  [Group G] [Group Q] [IsMulCommutative Q]

theorem extension_nilpotent_of_unipotent_generators (E : GroupExtension L G Q)
    (hsmooth : ∀ g : G, ContMDiff (𝓘(ℝ, L)) (𝓘(ℝ, L)) ∞ (E.conjAct g))
    (σ : E.Section) (hσ : σ 1 = 1) (qs : List Q)
    (hgen : Subgroup.closure {q | q ∈ qs} = ⊤)
    (hu : ∀ q ∈ qs,
      IsNilpotent ((polynomialModelLieEquiv (E.conjAct (σ q)) (hsmooth (σ q))).toLinearMap - 1)) :
    Group.IsNilpotent G := by
  let D : JointFixedReductionData E hsmooth qs :=
    { operators := [LieEquiv.refl]
      semisimple := by
        intro S hS
        have he : S = LieEquiv.refl := List.mem_singleton.mp hS
        subst S
        exact Module.End.isSemisimple_id
      commute := by
        intro S hS T hT
        have hS' : S = LieEquiv.refl := List.mem_singleton.mp hS
        have hT' : T = LieEquiv.refl := List.mem_singleton.mp hT
        subst S
        subst T
        exact Commute.refl _
      sectionMap := σ
      normalized := hσ
      centralizes := by
        intro S hS q
        have he : S = LieEquiv.refl := List.mem_singleton.mp hS
        subst S
        apply (mem_semisimpleActionCentralizer_iff E _ _ (hsmooth (σ q))).mpr
        exact Commute.one_left _
      factorsFixed := by
        intro S hS q r
        have he : S = LieEquiv.refl := List.mem_singleton.mp hS
        subst S
        rfl
      jordanLifts := by
        intro q hq
        refine ⟨LieEquiv.refl, List.mem_singleton_self _,
          polynomialModelLieEquiv (E.conjAct (σ q)) (hsmooth (σ q)), hu q hq,
          Commute.one_left _, ?_⟩
        exact (one_mul _).symm }
  let := D.residual_nilpotent hgen
  apply Group.nilpotent_of_surjective D.residualEmbedding
  intro g
  let a := GroupExtensionSection.mulEquiv E σ hσ g
  have hx : a.left ∈ jointFixedLieSubalgebra D.operators := by
    intro S hS
    have he : S = LieEquiv.refl := List.mem_singleton.mp hS
    subst S
    rfl
  let b : FactorExtension D.residualSystem := ⟨⟨a.left, hx⟩, a.right⟩
  refine ⟨b, ?_⟩
  change (GroupExtensionSection.mulEquiv E σ hσ).symm
    (jointFixedFactorInclusion _ D.action _ D.operators _ _ b) = g
  have hb : jointFixedFactorInclusion _ D.action _ D.operators _ _ b = a := by
    apply FactorExtension.ext <;> rfl
  rw [hb]
  exact (GroupExtensionSection.mulEquiv E σ hσ).symm_apply_apply g

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_UnipotentFactorSystem
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.abelianRealCoordinates _root_.OAI.PolycyclicRecognition.abelianRealFiniteDimensional _root_.OAI.PolycyclicRecognition.abelianRealLieAbelian _root_.OAI.PolycyclicRecognition.abelianRealNormedLie _root_.OAI.PolycyclicRecognition.derivationLieSpaceFiniteDimensional _root_.OAI.PolycyclicRecognition.derivationLieSpaceRealNormed _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instLocallyCompactSpaceFactorExtension _root_.OAI.PolycyclicRecognition.instT2SpaceFactorExtension _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

namespace OAI

/-! # Nilpotence for a smooth factor system with unipotent generators -/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold ContDiff IsMulCommutative
variable {L Q : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L] [LieRing.IsNilpotent L]
  [Group Q] [IsMulCommutative Q]

omit [LieRing.IsNilpotent L] [IsMulCommutative Q] in
theorem factorSystem_conjugation_smooth (R : NonabelianFactorSystem L Q)
    (hR : ∀ q, ContMDiff (𝓘(ℝ, L)) (𝓘(ℝ, L)) ∞ (R.action q))
    (g : FactorExtension R) :
    ContMDiff (𝓘(ℝ, L)) (𝓘(ℝ, L)) ∞ ((FactorExtension.groupExtension R).conjAct g) := by
  have he : ((FactorExtension.groupExtension R).conjAct g : L → L) =
      fun x => g.left * R.action g.right x * g.left⁻¹ :=
    funext (FactorExtension.conjugation_inl R g)
  rw [he]
  exact (contMDiff_const.mul (hR g.right)).mul contMDiff_const

theorem factorSystem_nilpotent_of_unipotent (R : NonabelianFactorSystem L Q)
    (hR : ∀ q, ContMDiff (𝓘(ℝ, L)) (𝓘(ℝ, L)) ∞ (R.action q))
    (qs : List Q) (hgen : Subgroup.closure {q | q ∈ qs} = ⊤)
    (hu : ∀ q ∈ qs, ∃ U : L ≃ₗ⁅ℝ⁆ L, IsNilpotent (U.toLinearMap - 1) ∧
      ∀ x, R.action q x = U x) :
    Group.IsNilpotent (FactorExtension R) := by
  let E := FactorExtension.groupExtension R
  let σ : E.Section :=
    { toFun := fun q => ⟨1, q⟩
      rightInverse_rightHom := fun _ => rfl }
  apply extension_nilpotent_of_unipotent_generators E
    (factorSystem_conjugation_smooth R hR) σ rfl qs hgen
  intro q hq
  obtain ⟨U, hU, he⟩ := hu q hq
  have hA : polynomialModelLieEquiv (E.conjAct (σ q))
      (factorSystem_conjugation_smooth R hR (σ q)) = U := by
    ext x
    rw [polynomialModelLieEquiv_apply]
    change E.conjAct (⟨1, q⟩ : FactorExtension R) x = U x
    rw [FactorExtension.conjugation_section]
    exact he x
  rw [hA]
  exact hU

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_CommutingIntegralHom
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.latticeNormalFlag_normal _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

namespace OAI

/-! # The homomorphism determined by commuting integral generators -/

noncomputable section
namespace PolycyclicRecognition
open scoped IsMulCommutative
variable {H : Type} [Group H] {n : ℕ}

theorem commutingIntegralHom_range_le (a : Fin n → H)
    (ha : ∀ i j, Commute (a i) (a j)) (K : Subgroup H) (hk : ∀ i, a i ∈ K) :
    (commutingIntegralHom a ha).range ≤ K := by
  have ht : (⊤ : Subgroup (IntegralLatticeGroup n)) ≤
      K.comap (commutingIntegralHom a ha) := by
    rw [← integralLatticeGenerator_closure n]
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i, rfl⟩
    change commutingIntegralHom a ha (integralLatticeGenerator n i) ∈ K
    rw [commutingIntegralHom_generator]
    exact hk i
  rintro _ ⟨z, rfl⟩
  exact ht (Subgroup.mem_top z)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_SmoothPolynomialAutomorphisms
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.JointFixedReductionData.residualLayer_normal _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.abelianRealCoordinates _root_.OAI.PolycyclicRecognition.abelianRealFiniteDimensional _root_.OAI.PolycyclicRecognition.abelianRealLieAbelian _root_.OAI.PolycyclicRecognition.abelianRealNormedLie _root_.OAI.PolycyclicRecognition.derivationLieSpaceFiniteDimensional _root_.OAI.PolycyclicRecognition.derivationLieSpaceRealNormed _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.polynomialLieIdealSubgroup_normal _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The subgroup of smooth automorphisms of a polynomial Lie group -/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold ContDiff
variable {L : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L]

theorem groupAutomorphism_mem_smooth (A : L ≃ₗ⁅ℝ⁆ L) :
    PolynomialExponentialCoordinates.groupAutomorphism (P := P) A ∈
      smoothPolynomialAutomorphisms :=
  ⟨A.toLinearEquiv.toContinuousLinearEquiv.contDiff.contMDiff,
    A.symm.toLinearEquiv.toContinuousLinearEquiv.contDiff.contMDiff⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_IntegralSemisimpleTwist
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.JointFixedReductionData.residualLayer_normal _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.abelianRealCoordinates _root_.OAI.PolycyclicRecognition.abelianRealFiniteDimensional _root_.OAI.PolycyclicRecognition.abelianRealLieAbelian _root_.OAI.PolycyclicRecognition.abelianRealNormedLie _root_.OAI.PolycyclicRecognition.derivationLieSpaceFiniteDimensional _root_.OAI.PolycyclicRecognition.derivationLieSpaceRealNormed _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instLocallyCompactSpaceFactorExtension _root_.OAI.PolycyclicRecognition.instT2SpaceFactorExtension _root_.OAI.PolycyclicRecognition.latticeNormalFlag_normal _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Removing the actual semisimple generator action

The normalized section and its commuting semisimple factors are constructed
in the original extension. Their integral action fixes the actual cocycle,
and removing it leaves unipotent actions on every quotient generator.
-/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold ContDiff
variable {L G : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L] [LieRing.IsNilpotent L] [Group G]

theorem integral_semisimple_twist {n : ℕ}
    (E : GroupExtension L G (IntegralLatticeGroup n))
    (hsmooth : ∀ g : G, ContMDiff (𝓘(ℝ, L)) (𝓘(ℝ, L)) ∞ (E.conjAct g)) :
    ∃ (σ : E.Section) (hσ : σ 1 = 1) (χ : IntegralLatticeGroup n →* MulAut L),
      let R := GroupExtensionSection.factorSystem E σ hσ
      ∃ (hc : ∀ q r, Commute (R.action q) (χ r))
        (hf : ∀ q r s, χ q (R.factor r s) = R.factor r s),
      (∀ q, ContMDiff (𝓘(ℝ, L)) (𝓘(ℝ, L)) ∞ (χ q)) ∧
      (∀ q, ContMDiff (𝓘(ℝ, L)) (𝓘(ℝ, L)) ∞ ((R.twist χ hc hf).action q)) ∧
      ∀ i : Fin n, ∃ U : L ≃ₗ⁅ℝ⁆ L, IsNilpotent (U.toLinearMap - 1) ∧
        ∀ x, (R.twist χ hc hf).action (integralLatticeGenerator n i) x = U x := by
  classical
  let qs := List.ofFn (integralLatticeGenerator n)
  obtain ⟨D⟩ := exists_jointFixedReductionData E hsmooth qs
  have hj (i : Fin n) := D.jordanLifts (integralLatticeGenerator n i)
    (List.mem_ofFn.mpr ⟨i, rfl⟩)
  choose S hS U hU hSU hA using hj
  let a := fun i => PolynomialExponentialCoordinates.groupAutomorphism (P := P) (S i)
  have ha (i j : Fin n) : Commute (a i) (a j) := by
    apply DFunLike.ext
    intro x
    exact LinearMap.congr_fun (D.commute (S i) (hS i) (S j) (hS j)).eq x
  let χ := commutingIntegralHom a ha
  let R := GroupExtensionSection.factorSystem E D.sectionMap D.normalized
  have hsym (i : Fin n) : a i ∈ factorSystemSymmetries R := by
    refine ⟨?_, ?_⟩
    · intro q
      apply DFunLike.ext
      intro x
      have h := LinearMap.congr_fun (D.action_commutes (S i) (hS i) q).eq x
      change S i (D.action q x) = D.action q (S i x) at h
      change S i (E.conjAct (D.sectionMap q) x) = E.conjAct (D.sectionMap q) (S i x)
      simpa only [JointFixedReductionData.action, polynomialModelLieEquiv_apply] using h
    · exact D.factorsFixed (S i) (hS i)
  have hχsym (q : IntegralLatticeGroup n) : χ q ∈ factorSystemSymmetries R :=
    commutingIntegralHom_range_le a ha (factorSystemSymmetries R) hsym ⟨q, rfl⟩
  have hc (q r : IntegralLatticeGroup n) : Commute (R.action q) (χ r) :=
    ((hχsym r).1 q).symm
  have hf (q r s : IntegralLatticeGroup n) : χ q (R.factor r s) = R.factor r s :=
    (hχsym q).2 r s
  have hχ (q : IntegralLatticeGroup n) : χ q ∈ smoothPolynomialAutomorphisms :=
    commutingIntegralHom_range_le a ha smoothPolynomialAutomorphisms
      (fun i => groupAutomorphism_mem_smooth (S i)) ⟨q, rfl⟩
  refine ⟨D.sectionMap, D.normalized, χ, hc, hf, fun q => (hχ q).1, ?_, ?_⟩
  · intro q
    exact (hχ q).2.comp (hsmooth (D.sectionMap q))
  · intro i
    refine ⟨U i, hU i, ?_⟩
    intro x
    have hg : χ (integralLatticeGenerator n i) = a i :=
      commutingIntegralHom_generator a ha i
    change (χ (integralLatticeGenerator n i))⁻¹
      (E.conjAct (D.sectionMap (integralLatticeGenerator n i)) x) = U i x
    rw [hg]
    have he : E.conjAct (D.sectionMap (integralLatticeGenerator n i)) x = S i (U i x) := by
      have h := LinearMap.congr_fun (hA i) x
      change polynomialModelLieEquiv _ _ x = S i (U i x) at h
      rwa [polynomialModelLieEquiv_apply] at h
    rw [he]
    exact (S i).symm_apply_apply (U i x)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Lattices_KernelCompletionAction
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.JointFixedReductionData.residualLayer_normal _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.polynomialLieIdealSubgroup_normal _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Extending an action to the nilpotent completion

Existence comes from the constructed homomorphism extension. Uniqueness on
the integer grid forces the extensions to satisfy the action law.
-/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold ContDiff
variable {K G Q : Type} [RealNormedLieAlgebra K] [FiniteDimensional ℝ K]
  [PK : PolynomialExponentialCoordinates K] [Group G] [Group Q]
  {i : K →* G} (C : NilpotentKernelCompletion i) (ρ : Q →* MulAut G)
  (hρ : ∀ q, ContMDiff (𝓘(ℝ, K)) (𝓘(ℝ, C.carrier)) ∞
    ((C.embed.comp (ρ q).toMonoidHom).comp i))

namespace NilpotentKernelCompletion

theorem extendedAction_preserves_hom {M : Type} [RealNormedLieAlgebra M]
    [FiniteDimensional ℝ M] [PM : PolynomialExponentialCoordinates M]
    (π : C.carrier →* M) (hπ : ContMDiff (𝓘(ℝ, C.carrier)) (𝓘(ℝ, M)) ∞ π)
    (hinv : ∀ q g, π (C.embed (ρ q g)) = π (C.embed g)) (q : Q) (x : C.carrier) :
    π (C.extendedAction ρ hρ q x) = π x := by
  have he : π.comp (C.extendedAction ρ hρ q).toMonoidHom = π := by
    apply C.hom_ext M (π.comp (C.extendedAction ρ hρ q).toMonoidHom) π
      (hπ.comp (C.extendedAction_smooth ρ hρ q)) hπ
    intro g
    change π (C.extendedAction ρ hρ q (C.embed g)) = π (C.embed g)
    rw [extendedAction_embed]
    exact hinv q g
  exact DFunLike.congr_fun he x

end NilpotentKernelCompletion
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Lattices_IntegralNilshadow
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instLocallyCompactSpaceFactorExtension _root_.OAI.PolycyclicRecognition.instT2SpaceFactorExtension _root_.OAI.PolycyclicRecognition.latticeNormalFlag_normal _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Constructing the nilshadow of an integral abelian extension

Both the section and the removed action are constructed from the original
extension. The twisted group has a nilpotent real completion of the correct
dimension. Its removed action extends, and the original group embeds faithfully
in the corresponding semidirect product. The quotient here is still integral.
-/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold ContDiff
variable {L G : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L] [LieRing.IsNilpotent L] [Group G] {n : ℕ}

theorem exists_integralNilshadowData (E : GroupExtension L G (IntegralLatticeGroup n))
    (hsmooth : ∀ g : G, ContMDiff (𝓘(ℝ, L)) (𝓘(ℝ, L)) ∞ (E.conjAct g)) :
    Nonempty (IntegralNilshadowData E) := by
  obtain ⟨σ, hσ, χ, hc, hf, hχ, hT, hu⟩ := integral_semisimple_twist E hsmooth
  let R := GroupExtensionSection.factorSystem E σ hσ
  let T := R.twist χ hc hf
  let qs := List.ofFn (integralLatticeGenerator n)
  have hgen : Subgroup.closure {q | q ∈ qs} = ⊤ := by
    convert integralLatticeGenerator_closure n using 2
    all_goals try with_reducible_and_instances rfl
    ext q
    exact List.mem_ofFn
  have hnil : Group.IsNilpotent (FactorExtension T) :=
    factorSystem_nilpotent_of_unipotent T hT qs hgen (by
      intro q hq
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hq
      exact hu i)
  let := hnil
  obtain ⟨C, hC⟩ := nilpotent_integral_kernel_completion_with_dimension
    (FactorExtension.groupExtension T) (factorSystem_conjugation_smooth T hT)
  exact ⟨⟨σ, hσ, χ, hc, hf, hχ, hT, hnil, C, hC⟩⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Lattices_NilshadowHeight
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instLocallyCompactSpaceFactorExtension _root_.OAI.PolycyclicRecognition.instT2SpaceFactorExtension _root_.OAI.PolycyclicRecognition.latticeNormalFlag_normal _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A fixed linear section of the nilshadow height

The section vectors are the logarithmic coordinates of the actual integral
quotient lifts. The removed action fixes them, as well as the height map.
-/

noncomputable section
namespace PolycyclicRecognition.IntegralNilshadowData
open scoped Manifold ContDiff
variable {L G : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L] [Group G] {n : ℕ}
  {E : GroupExtension L G (IntegralLatticeGroup n)} (D : IntegralNilshadowData E)

theorem heightLinear_apply (x : D.completion.carrier) : D.heightLinear x = D.height x :=
  polynomialModelLieHom_apply D.height D.height_smooth x

theorem heightLinear_section (v : AbelianRealSpace n) :
    D.heightLinear (D.quotientSection v) = v := by
  have he : D.heightLinear.comp D.quotientSection = LinearMap.id := by
    apply (quotientBasis n).ext
    intro i
    change D.heightLinear (D.quotientSection ((quotientBasis n) i)) = _
    rw [quotientSection, Module.Basis.constr_basis, heightLinear_apply, height_embed]
    exact integerVectorMap_basis i
  exact LinearMap.congr_fun he v

theorem completedLieAction_height (q : IntegralLatticeGroup n) (x : D.completion.carrier) :
    D.heightLinear (D.completedLieAction q x) = D.heightLinear x := by
  rw [heightLinear_apply, heightLinear_apply]
  change D.height (polynomialModelLieEquiv _ _ x) = D.height x
  rw [polynomialModelLieEquiv_apply]
  apply D.completion.extendedAction_preserves_hom D.integralAction
    D.integralAction_kernel_smooth D.height D.height_smooth
  intro q g
  rw [height_embed, height_embed]
  rfl

theorem completedLieAction_section (q : IntegralLatticeGroup n) (v : AbelianRealSpace n) :
    D.completedLieAction q (D.quotientSection v) = D.quotientSection v := by
  have he : (D.completedLieAction q).toLinearMap.comp D.quotientSection = D.quotientSection := by
    apply (quotientBasis n).ext
    intro i
    change D.completedLieAction q (D.quotientSection ((quotientBasis n) i)) =
      D.quotientSection ((quotientBasis n) i)
    rw [quotientSection, Module.Basis.constr_basis, completedLieAction,
      polynomialModelLieEquiv_apply]
    change D.completion.extendedAction D.integralAction D.integralAction_kernel_smooth q
      (D.completion.embed ⟨1, integralLatticeGenerator n i⟩) = _
    rw [D.completion.extendedAction_embed]
    apply congrArg D.completion.embed
    apply FactorExtension.ext
    · exact map_one (D.removed q)
    · rfl
  exact LinearMap.congr_fun he v

theorem heightLinear_projection (x : D.completion.carrier) :
    D.heightLinear (D.heightProjection x) = D.heightLinear x :=
  D.heightLinear_section _

theorem completedLieAction_projection (q : IntegralLatticeGroup n) (x : D.completion.carrier) :
    D.completedLieAction q (D.heightProjection x) = D.heightProjection x :=
  D.completedLieAction_section q _

theorem projection_completedLieAction (q : IntegralLatticeGroup n) (x : D.completion.carrier) :
    D.heightProjection (D.completedLieAction q x) = D.heightProjection x := by
  change D.quotientSection (D.heightLinear (D.completedLieAction q x)) =
    D.quotientSection (D.heightLinear x)
  rw [D.completedLieAction_height]

end PolycyclicRecognition.IntegralNilshadowData

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Lattices_NilshadowRealAction
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instLocallyCompactSpaceFactorExtension _root_.OAI.PolycyclicRecognition.instT2SpaceFactorExtension _root_.OAI.PolycyclicRecognition.latticeNormalFlag_normal _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The real nilshadow action preserves the actual height

The logarithms vanish on the fixed quotient section. Commutation with its
projection therefore forces the complete real action to preserve height,
not merely its integral-time values.
-/

noncomputable section
namespace PolycyclicRecognition.IntegralNilshadowData
open scoped Manifold ContDiff
attribute [local instance] LieRing.ofAssociativeRing
variable {L G : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L] [Group G] {n : ℕ}
  {E : GroupExtension L G (IntegralLatticeGroup n)} (D : IntegralNilshadowData E)

theorem exists_real_action :
    ∃ m : ℕ, 0 < m ∧ ∃ φ : Multiplicative (Fin n → ℝ) →* MulAut D.completion.carrier,
      ContDiff ℝ ⊤ (fun p : (Fin n → ℝ) × D.completion.carrier =>
        φ (Multiplicative.ofAdd p.1) p.2) ∧
      (∀ z x, D.completedAction (latticePowerHom n m z) x = φ (integerVectorHom n z) x) ∧
      (∀ v x, D.height (φ v x) = D.height x) ∧
      ∀ v w, φ v (D.quotientSection w) = D.quotientSection w := by
  let A := fun i : Fin n => D.completedLieAction (integralLatticeGenerator n i)
  have hA (i j : Fin n) : Commute (A i).toLinearMap (A j).toLinearMap := by
    apply LinearMap.ext
    intro x
    change A i (A j x) = A j (A i x)
    simp only [A, completedLieAction, polynomialModelLieEquiv_apply]
    exact DFunLike.congr_fun
      (((show Commute (integralLatticeGenerator n i) (integralLatticeGenerator n j)
        from Commute.all _ _).map D.completedAction).eq) x
  obtain ⟨m, hm, B, he, hc, hcomm, hfixed⟩ :=
    commuting_lie_automorphisms_have_fixed_power_logs A hA
  let φ := PolynomialExponentialCoordinates.commutingDerivationAction B hc
  have hp (i : Fin n) : D.heightProjection * (B i).toLinearMap = 0 :=
    fixed_log_projection_zero (A i) (B i) (hcomm i) (hfixed i) D.heightProjection
      (D.completedLieAction_projection _) (D.projection_completedLieAction _)
  have hbp (i : Fin n) : (B i).toLinearMap * D.heightProjection = 0 := by
    apply LinearMap.ext
    intro x
    exact hfixed i _ (D.completedLieAction_projection _ x)
  have hprod (i : Fin n) (k : ℕ) (x : D.completion.carrier) :
      ((A i).toLinearMap ^ k) x = D.completedAction ((integralLatticeGenerator n i) ^ k) x := by
    induction k generalizing x with
    | zero => simp only [pow_zero, map_one, Module.End.one_apply, MulAut.one_apply]
    | succ k ih =>
      rw [pow_succ', Module.End.mul_apply, ih, pow_succ', map_mul]
      exact polynomialModelLieEquiv_apply _ _ _
  have hhom : φ.comp (integerVectorHom n) = D.completedAction.comp (latticePowerHom n m) := by
    apply integralLattice_hom_ext
    intro i
    apply DFunLike.ext
    intro x
    change analyticDerivationExp
      (derivationCombination B (integerVectorMap n ((Pi.basisFun ℤ (Fin n)) i))) x =
        D.completedAction ((integralLatticeGenerator n i) ^ m) x
    rw [integerVectorMap_basis, derivationCombination_basis, analyticDerivationExp_apply]
    exact (DFunLike.congr_fun (he i) x).trans (hprod i m x)
  refine ⟨m, hm, φ, PolynomialExponentialCoordinates.commutingDerivationAction_smooth B hc,
    fun z x => (congrArg (fun F : IntegralLatticeGroup n →* MulAut D.completion.carrier => F z x)
      hhom).symm, ?_⟩
  constructor
  · intro v x
    have hpv : D.heightProjection * (derivationCombination B v.toAdd).toLinearMap = 0 := by
      let F := (LieDerivation.toLinearMapLieHom ℝ D.completion.carrier).toLinearMap
      change D.heightProjection * F (∑ i, v.toAdd i • B i) = 0
      simp only [map_sum, map_smul, Finset.mul_sum, mul_smul_comm]
      change (∑ i, v.toAdd i • (D.heightProjection * (B i).toLinearMap)) = 0
      simp only [hp, smul_zero, Finset.sum_const_zero]
    rw [← D.heightLinear_apply, ← D.heightLinear_apply]
    exact exp_preserves_projected_quotient _ _ hpv D.heightLinear D.heightLinear_projection x
  · intro v w
    have hpv : (derivationCombination B v.toAdd).toLinearMap * D.heightProjection = 0 := by
      let F := (LieDerivation.toLinearMapLieHom ℝ D.completion.carrier).toLinearMap
      change F (∑ i, v.toAdd i • B i) * D.heightProjection = 0
      simp only [map_sum, map_smul, Finset.sum_mul, smul_mul_assoc]
      change (∑ i, v.toAdd i • ((B i).toLinearMap * D.heightProjection)) = 0
      simp only [hbp, smul_zero, Finset.sum_const_zero]
    have hpw : D.heightProjection (D.quotientSection w) = D.quotientSection w := by
      change D.quotientSection (D.heightLinear (D.quotientSection w)) = _
      rw [D.heightLinear_section]
    have h := exp_fixes_projection _ _ hpv (D.quotientSection w)
    rw [hpw] at h
    exact h

end PolycyclicRecognition.IntegralNilshadowData

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Lattices_NilshadowPowerGraph
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.latticeNormalFlag_normal _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Embedding the finite-power extension in the real invariant graph -/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold ContDiff

namespace IntegralNilshadowData
variable {L G : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L] [Group G] {n : ℕ}
  {E : GroupExtension L G (IntegralLatticeGroup n)} (D : IntegralNilshadowData E)

theorem inverseScaledHeight_smooth (m : ℕ) :
    ContDiff ℝ ⊤ (fun x => (D.inverseScaledHeight m x).toAdd) := by
  have h : ContDiff ℝ ⊤ (fun x => -((m : ℝ)⁻¹) • D.heightLinear x) :=
    ((-((m : ℝ)⁻¹)) • D.heightLinear).toContinuousLinearMap.contDiff
  have hf : (fun x => (D.inverseScaledHeight m x).toAdd) =
      (fun x => -((m : ℝ)⁻¹) • D.heightLinear x) := by
    funext x
    exact congrArg (fun y => -((m : ℝ)⁻¹) • y) (D.heightLinear_apply x).symm
  rw [hf]
  exact h

end IntegralNilshadowData
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Lattices_NilshadowGraphTopology
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.latticeNormalFlag_normal _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original topology in the real nilshadow graph -/

noncomputable section
namespace PolycyclicRecognition.IntegralNilshadowData
open scoped Manifold ContDiff
attribute [local instance] factorExtensionTopology semidirectProductTopology
variable {L G : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L] [Group G] {n : ℕ}
  {E : GroupExtension L G (IntegralLatticeGroup n)} (D : IntegralNilshadowData E)
  {m : ℕ} (hm : 0 < m)
  (φ : Multiplicative (Fin n → ℝ) →* MulAut D.completion.carrier)
  (he : ∀ z x, D.completedAction (latticePowerHom n m z) x = φ (integerVectorHom n z) x)
  (hinv : ∀ v x, D.height (φ v x) = D.height x)

theorem powerGraphEmbedding_isEmbedding : Topology.IsEmbedding (D.powerGraphEmbedding hm φ he hinv) := by
  let hτ := (D.inverseScaledHeight_smooth m).continuous
  let e := rotationalTwistHomeomorph φ (D.inverseScaledHeight m)
    (fun v x => congrArg (scaleRealHeight n (-((m : ℝ)⁻¹))) (hinv v x)) hτ
  let c : FactorExtension (D.system.pullback (latticePowerHom n m)) ≃ₜ
      FactorExtension (D.twistedSystem.pullback (latticePowerHom n m)) :=
    (factorExtensionHomeomorph _).trans (factorExtensionHomeomorph _).symm
  have hc := kernelCompletion_isEmbedding D.twistedSystem D.completion D.height
    D.height_smooth D.height_embed
  have h := e.symm.isEmbedding.comp (hc.comp
    ((factorPowerMap_isClosedEmbedding D.twistedSystem hm).isEmbedding.comp c.isEmbedding))
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  funext a
  apply e.injective
  rfl

end PolycyclicRecognition.IntegralNilshadowData

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Lattices_NilshadowGraphCover
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.latticeNormalFlag_normal _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A compact fundamental cover for the real nilshadow graph -/

noncomputable section
namespace PolycyclicRecognition.IntegralNilshadowData
open Set
open scoped Manifold ContDiff
attribute [local instance] factorExtensionTopology semidirectProductTopology
variable {L G : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L] [Group G] {n : ℕ}
  {E : GroupExtension L G (IntegralLatticeGroup n)} (D : IntegralNilshadowData E)
  {m : ℕ} (hm : 0 < m)
  (φ : Multiplicative (Fin n → ℝ) →* MulAut D.completion.carrier)
  (he : ∀ z x, D.completedAction (latticePowerHom n m z) x = φ (integerVectorHom n z) x)
  (hinv : ∀ v x, D.height (φ v x) = D.height x)
  (hfix : ∀ v w, φ v (D.quotientSection w) = D.quotientSection w)

include hfix in
theorem powerGraph_compact_cover :
    ∃ K : Set (rotationalTwist φ (D.inverseScaledHeight m)
      (fun v x => congrArg (scaleRealHeight n (-((m : ℝ)⁻¹))) (hinv v x))),
      IsCompact K ∧ ∀ g, ∃ a k, k ∈ K ∧ D.powerGraphEmbedding hm φ he hinv a * k = g := by
  let e := rotationalTwistHomeomorph φ (D.inverseScaledHeight m)
    (fun v x => congrArg (scaleRealHeight n (-((m : ℝ)⁻¹))) (hinv v x))
    (D.inverseScaledHeight_smooth m).continuous
  obtain ⟨K, hK, hc⟩ := scaledIntegral_compact_cover n hm
  refine ⟨(fun k => e.symm (D.quotientSection k)) '' K,
    hK.image (e.symm.continuous.comp D.quotientSection.toContinuousLinearMap.continuous), ?_⟩
  intro g
  obtain ⟨z, k, hk, hzk⟩ := hc (D.height (e g))
  let b := D.completion.embed (⟨1, latticePowerHom n m z⟩ : FactorExtension D.twistedSystem)
  let u := e g * (D.quotientSection k)⁻¹ * b⁻¹
  have hs : D.height (D.quotientSection k) = k :=
    (D.heightLinear_apply _).symm.trans (D.heightLinear_section k)
  have hu : u ∈ D.height.ker := by
    change D.height (e g * (D.quotientSection k)⁻¹ * b⁻¹) = 1
    rw [map_mul, map_mul, map_inv, map_inv, hs]
    change D.height (e g) + -k + -(D.height b) = 0
    have hb : D.height b = integralRealHeight (latticePowerHom n m z) := D.height_embed _
    rw [hb, ← hzk]
    abel
  rw [D.completion.height_kernel_eq (FactorExtension.groupExtension D.twistedSystem)
    D.height D.height_smooth D.height_embed D.dimension] at hu
  obtain ⟨l, hl⟩ := hu
  let a : FactorExtension (D.system.pullback (latticePowerHom n m)) := ⟨l, z⟩
  refine ⟨a, e.symm (D.quotientSection k), ⟨k, hk, rfl⟩, ?_⟩
  apply e.injective
  change D.completion.embed (⟨l, latticePowerHom n m z⟩ : FactorExtension D.twistedSystem) *
    φ (integerVectorHom n z) (D.quotientSection k) = e g
  rw [hfix, completion_factorization D.twistedSystem D.completion]
  change D.completion.embed (FactorExtension.inl D.twistedSystem l) * b * D.quotientSection k = e g
  change D.completion.embed (FactorExtension.inl D.twistedSystem l) = u at hl
  rw [hl]
  dsimp only [u]
  group

end PolycyclicRecognition.IntegralNilshadowData

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Lattices_UniformLatticeTransport
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Transporting a compact lattice cover through a group homeomorphism -/

noncomputable section
namespace PolycyclicRecognition
variable {G H : Type*} [Group G] [Group H] [TopologicalSpace G] [TopologicalSpace H]

theorem IsUniformLattice.comap_mulEquiv (e : G ≃* H)
    (he : Continuous e) (hei : Continuous e.symm)
    {Λ : Subgroup H} (hΛ : IsUniformLattice Λ) :
    IsUniformLattice (Λ.comap e.toMonoidHom) := by
  let := hΛ.1
  let f : Λ.comap e.toMonoidHom → Λ := fun x => ⟨e x.val, x.property⟩
  have hf : Continuous f := (he.comp continuous_subtype_val).subtype_mk _
  have hdisc : DiscreteTopology (Λ.comap e.toMonoidHom) :=
    DiscreteTopology.of_continuous_injective hf (by
      intro x y h
      apply Subtype.ext
      exact e.injective (congrArg Subtype.val h))
  obtain ⟨K, hK, hc⟩ := hΛ.2
  refine ⟨hdisc, e.symm '' K, hK.image hei, ?_⟩
  intro g
  obtain ⟨a, k, hk, h⟩ := hc (e g)
  refine ⟨⟨e.symm a.val, by change e (e.symm a.val) ∈ Λ; rw [e.apply_symm_apply]; exact a.property⟩,
    e.symm k, ⟨k, hk, rfl⟩, ?_⟩
  change e.symm a.val * e.symm k = g
  rw [← map_mul, h, e.symm_apply_apply]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Lattices_UniformLatticeEmbedding
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform lattices under cocompact embeddings and finite index -/

noncomputable section
namespace PolycyclicRecognition
open Set
open scoped Pointwise

variable {G H : Type*} [Group G] [Group H] [TopologicalSpace G] [TopologicalSpace H]

/-- A topological group embedding with a compact right fundamental cover
carries uniform lattices to uniform lattices. -/
theorem IsUniformLattice.map_of_compact_cover [IsTopologicalGroup H]
    {Λ : Subgroup G} (hΛ : IsUniformLattice Λ) (f : G →* H)
    (hf : Topology.IsEmbedding f) (K : Set H) (hK : IsCompact K)
    (hcover : ∀ h : H, ∃ (g : G) (k : H), k ∈ K ∧ f g * k = h) :
    IsUniformLattice (Λ.map f) := by
  let := hΛ.1
  have hi : Topology.IsEmbedding (fun a : Λ => f a) := hf.comp .subtypeVal
  have hr : Set.range (fun a : Λ => f a) = (Λ.map f : Set H) := by
    ext h
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨a, a.property, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨⟨a, ha⟩, rfl⟩
  have hdisc : DiscreteTopology (Λ.map f) := by
    change DiscreteTopology (Λ.map f : Set H)
    rw [← hr]
    exact hi.toHomeomorph.symm.isEmbedding.discreteTopology
  obtain ⟨F, hF, hcovF⟩ := hΛ.2
  refine ⟨hdisc, (f '' F) * K, (hF.image hf.continuous).mul hK, ?_⟩
  intro h
  obtain ⟨g, k, hk, hg⟩ := hcover h
  obtain ⟨a, u, hu, ha⟩ := hcovF g
  refine ⟨⟨f a, ⟨a, a.property, rfl⟩⟩, f u * k, ⟨f u, ⟨u, hu, rfl⟩, k, hk, rfl⟩, ?_⟩
  change f a * (f u * k) = h
  rw [← mul_assoc, ← map_mul, ha, hg]

/-- A finite-index subgroup of a uniform lattice is again uniform in the
same ambient group. -/
theorem IsUniformLattice.finiteIndex [IsTopologicalGroup G]
    {Λ : Subgroup G} (hΛ : IsUniformLattice Λ) (J : Subgroup Λ) [J.FiniteIndex] :
    IsUniformLattice (J.map Λ.subtype) := by
  let := hΛ.1
  have hle : J.map Λ.subtype ≤ Λ := by
    rintro g ⟨a, _, rfl⟩
    exact a.property
  let f : J.map Λ.subtype → Λ := Subgroup.inclusion hle
  have hf : Continuous f := continuous_subtype_val.subtype_mk _
  have hdisc : DiscreteTopology (J.map Λ.subtype) :=
    DiscreteTopology.of_continuous_injective hf (Subgroup.inclusion_injective hle)
  let R := Quotient (QuotientGroup.rightRel J)
  let : Finite R := Finite.of_equiv (Λ ⧸ J)
    (QuotientGroup.quotientRightRelEquivQuotientLeftRel J).symm
  let reps : R → G := fun c => ((Quotient.out c : Λ) : G)
  obtain ⟨K, hK, hcover⟩ := hΛ.2
  refine ⟨hdisc, Set.range reps * K, (Set.finite_range reps).isCompact.mul hK, ?_⟩
  intro g
  obtain ⟨γ, k, hk, hγ⟩ := hcover g
  let c : R := Quotient.mk (QuotientGroup.rightRel J) γ
  let r : Λ := Quotient.out c
  have hj : γ * r⁻¹ ∈ J := QuotientGroup.rightRel_apply.mp
    (Quotient.exact' (Quotient.out_eq' c))
  refine ⟨⟨((γ * r⁻¹ : Λ) : G), ⟨γ * r⁻¹, hj, rfl⟩⟩, (r : G) * k,
    ⟨r, ⟨c, rfl⟩, k, hk, rfl⟩, ?_⟩
  change ((γ : G) * (r : G)⁻¹) * ((r : G) * k) = g
  rw [mul_assoc, inv_mul_cancel_left, hγ]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Lattices_UniformLatticeFiniteIndexEmbedding
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Pulling a lattice back through a closed finite-index embedding -/

noncomputable section
namespace PolycyclicRecognition
open Set
variable {G H : Type*} [Group G] [Group H] [TopologicalSpace G] [TopologicalSpace H]

/-- If a closed subgroup contains the lattice, its induced lattice is uniform. -/
theorem IsUniformLattice.comap_of_le_range
    {Γ : Subgroup G} (hΓ : IsUniformLattice Γ) (f : H →* G)
    (hf : Topology.IsClosedEmbedding f) (hle : Γ ≤ f.range) :
    IsUniformLattice (Γ.comap f) := by
  let := hΓ.1
  let g : Γ.comap f → Γ := fun x => ⟨f x, x.property⟩
  have hg : Continuous g := (hf.continuous.comp continuous_subtype_val).subtype_mk _
  have hdisc : DiscreteTopology (Γ.comap f) :=
    DiscreteTopology.of_continuous_injective hg (by
      intro x y h
      exact Subtype.ext (hf.injective (congrArg Subtype.val h)))
  obtain ⟨K, hK, hcover⟩ := hΓ.2
  refine ⟨hdisc, f ⁻¹' K, hf.isCompact_preimage hK, ?_⟩
  intro x
  obtain ⟨γ, k, hk, he⟩ := hcover (f x)
  obtain ⟨a, ha⟩ := hle γ.property
  have haΓ : a ∈ Γ.comap f := by change f a ∈ Γ; rw [ha]; exact γ.property
  have hfk : f (a⁻¹ * x) = k := by
    rw [map_mul, map_inv, ha, ← he, inv_mul_cancel_left]
  refine ⟨⟨a, haΓ⟩, a⁻¹ * x, ?_, mul_inv_cancel_left a x⟩
  change f (a⁻¹ * x) ∈ K
  rw [hfk]
  exact hk

/-- Restriction to a closed finite-index subgroup preserves a uniform lattice. -/
theorem IsUniformLattice.comap_finiteIndex [IsTopologicalGroup G]
    {Γ : Subgroup G} (hΓ : IsUniformLattice Γ) (f : H →* G)
    (hf : Topology.IsClosedEmbedding f) [f.range.FiniteIndex] :
    IsUniformLattice (Γ.comap f) := by
  let J := f.range.comap Γ.subtype
  let : J.FiniteIndex := inferInstance
  have hJ := hΓ.finiteIndex J
  have hle : J.map Γ.subtype ≤ f.range := by
    rintro x ⟨y, hy, rfl⟩
    exact hy
  have heq : (J.map Γ.subtype).comap f = Γ.comap f := by
    ext x
    constructor
    · rintro ⟨y, _, hy⟩
      change f x ∈ Γ
      rw [← hy]
      exact y.property
    · intro hx
      exact ⟨⟨f x, hx⟩, ⟨x, rfl⟩, rfl⟩
  rw [← heq]
  exact hJ.comap_of_le_range f hf hle

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Lattices_NilshadowLatticeRealization
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.latticeNormalFlag_normal _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Connected realization of lattices in the original nonsplit extension -/

noncomputable section
namespace PolycyclicRecognition.IntegralNilshadowData
open scoped Manifold ContDiff
attribute [local instance] factorExtensionTopology semidirectProductTopology
variable {L G : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L] [Group G] {n : ℕ}
  {E : GroupExtension L G (IntegralLatticeGroup n)} (D : IntegralNilshadowData E)

theorem uniform_lattice_realization
    (Γ : Subgroup (FactorExtension D.system)) (hΓ : IsUniformLattice Γ) :
    ∃ J : Subgroup Γ, J.FiniteIndex ∧ ∃ (S : SimplyConnectedSolvableLieModel)
      (Λ : Subgroup S.carrier), IsUniformLattice Λ ∧ Nonempty (J ≃* Λ) := by
  let : IsTopologicalGroup L := topologicalGroup_of_lieGroup (𝓘(ℝ, L)) ⊤
  let : IsTopologicalGroup (FactorExtension D.system) :=
    factorExtensionTopologicalGroup D.system (fun q => by
      have h := ((D.smooth q).comp (D.twist_smooth q)).continuous
      have heq : (fun x => D.removed q (D.twistedSystem.action q x)) = D.system.action q := by
        funext x
        exact (D.removed q).apply_symm_apply _
      change Continuous (fun x => D.removed q (D.twistedSystem.action q x)) at h
      rwa [heq] at h)
  let : Group.IsNilpotent D.completion.carrier := polynomial_group_nilpotent
  let : IsTopologicalGroup D.completion.carrier :=
    topologicalGroup_of_lieGroup (𝓘(ℝ, D.completion.carrier)) ⊤
  obtain ⟨m, hm, φ, hφ, he, hinv, hfix⟩ := D.exists_real_action
  let := semidirectProductTopologicalGroup φ hφ.continuous
  let F := factorPullbackMap D.system (latticePowerHom n m)
  have hFi := factorPullbackMap_injective D.system (latticePowerHom n m)
    (latticePowerHom_injective n hm)
  have hFe := factorPowerMap_isClosedEmbedding D.system hm
  let := factorPowerMap_finiteIndex D.system hm
  let Γm := Γ.comap F
  have hΓm : IsUniformLattice Γm := hΓ.comap_finiteIndex F hFe
  let J := F.range.comap Γ.subtype
  have hJ : J.FiniteIndex := inferInstance
  let f0 : Γm →* Γ := (F.comp Γm.subtype).codRestrict Γ (fun x => x.property)
  let fJ : Γm →* J := f0.codRestrict J (fun x => ⟨x.val, rfl⟩)
  have hfJ : Function.Bijective fJ := by
    constructor
    · intro a b hab
      apply Subtype.ext
      apply hFi
      exact congrArg (fun x : J => ((x : Γ) : FactorExtension D.system)) hab
    · intro j
      obtain ⟨x, hx⟩ := j.property
      have hxΓ : x ∈ Γm := by change F x ∈ Γ; rw [hx]; exact j.val.property
      refine ⟨⟨x, hxΓ⟩, ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      exact hx
  let eJ : Γm ≃* J := MulEquiv.ofBijective fJ hfJ
  let ψ := D.powerGraphEmbedding hm φ he hinv
  have hψ := D.powerGraphEmbedding_isEmbedding hm φ he hinv
  obtain ⟨K, hK, hc⟩ := D.powerGraph_compact_cover hm φ he hinv hfix
  have hΛ := hΓm.map_of_compact_cover ψ hψ K hK hc
  let τ := D.inverseScaledHeight m
  let hτ := D.inverseScaledHeight_smooth m
  let hi := fun v x => congrArg (scaleRealHeight n (-((m : ℝ)⁻¹))) (hinv v x)
  let S := invariantGraphLieModel φ τ hi hφ hτ
  let eS := invariantGraphModelEquiv φ τ hi hφ hτ
  let Λ := (Γm.map ψ).comap eS.toMonoidHom
  have hΛS : IsUniformLattice Λ := hΛ.comap_mulEquiv eS
    (invariantGraphModelEquiv_continuous φ τ hi hφ hτ)
    (invariantGraphModelEquiv_symm_continuous φ τ hi hφ hτ)
  let eψ : Γm ≃* Γm.map ψ := Γm.equivMapOfInjective ψ hψ.injective
  exact ⟨J, hJ, S, Λ, hΛS,
    ⟨eJ.symm.trans (eψ.trans (comapSubgroupEquiv eS (Γm.map ψ)).symm)⟩⟩

end PolycyclicRecognition.IntegralNilshadowData

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_NilpotentExtensionRealization
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.latticeNormalFlag_normal _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Connected realization without a splitting or a fixed-point-free action -/

noncomputable section
namespace PolycyclicRecognition.NilpotentLatticeCoordinates
open scoped Manifold ContDiff
attribute [local instance] factorExtensionTopology
variable {N G : Type} [Group N] [Group G] (C : NilpotentLatticeCoordinates N)
  {n : ℕ} (E : GroupExtension N G (IntegralLatticeGroup n))
  (σ : E.Section) (hσ : σ 1 = 1)

include C E σ hσ in
theorem extension_realization :
    ∃ K : Subgroup G, K.FiniteIndex ∧ ∃ (S : SimplyConnectedSolvableLieModel)
      (Λ : Subgroup S.carrier), IsUniformLattice Λ ∧ Nonempty (K ≃* Λ) := by
  let T := C.extensionFactorSystem E σ hσ
  let E' := FactorExtension.groupExtension T
  obtain ⟨D⟩ := exists_integralNilshadowData E'
    (factorSystem_conjugation_smooth T (C.extensionFactorSystem_smooth E σ hσ))
  let : IsTopologicalGroup C.carrier := topologicalGroup_of_lieGroup (𝓘(ℝ, C.carrier)) ⊤
  let e := GroupExtensionSection.mulEquiv E' D.sectionMap D.normalized
  let Γ := C.completedExtensionLattice E σ hσ
  let Γ' := Γ.comap e.symm.toMonoidHom
  have hΓ' : IsUniformLattice Γ' := (C.completedExtensionLattice_uniform E σ hσ).comap_mulEquiv
    e.symm (sectionFactorEquiv_symm_continuous T D.sectionMap D.normalized)
      (sectionFactorEquiv_continuous T D.sectionMap D.normalized)
  obtain ⟨J, hJ, S, Λ, hΛ, ⟨f⟩⟩ := D.uniform_lattice_realization Γ' hΓ'
  let eG : G ≃* Γ' := (C.completedExtensionLatticeEquiv E σ hσ).trans
    (comapSubgroupEquiv e.symm Γ).symm
  let K := J.comap eG.toMonoidHom
  let := hJ
  have hK : K.FiniteIndex := inferInstance
  exact ⟨K, hK, S, Λ, hΛ, ⟨(comapSubgroupEquiv eG J).trans f⟩⟩

end PolycyclicRecognition.NilpotentLatticeCoordinates

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Lattices_LatticeAutomorphismFlow
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.JointFixedReductionData.residualLayer_normal _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.abelianRealCoordinates _root_.OAI.PolycyclicRecognition.abelianRealFiniteDimensional _root_.OAI.PolycyclicRecognition.abelianRealLieAbelian _root_.OAI.PolycyclicRecognition.abelianRealNormedLie _root_.OAI.PolycyclicRecognition.derivationLieSpaceFiniteDimensional _root_.OAI.PolycyclicRecognition.derivationLieSpaceRealNormed _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.polynomialLieIdealSubgroup_normal _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Extending nilpotent lattice conjugation to a real automorphism flow -/

noncomputable section
namespace PolycyclicRecognition
open Module
open scoped Manifold ContDiff
variable {L G H : Type*} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L] [Group G] [Group H] [Group.IsNilpotent G]

theorem exists_nilpotent_lattice_automorphism_log {d : ℕ} (b : Basis (Fin d) ℝ L)
    (p : L → L) (hp : IsPolynomialInBasis b b p) (hsurj : Function.Surjective p)
    (e : H →* L)
    (hgrid : ∀ z : Fin d → ℤ, ∃ x : H,
      e x = p (b.equivFun.symm (fun i => (z i : ℝ))))
    (j : H →* G) (hj : Function.Injective j)
    (a : H ≃* H) (t : G) (ha : ∀ x, j (a x) = t * j x * t⁻¹)
    (F : L ≃* L) (hF : ContMDiff (𝓘(ℝ, L)) (𝓘(ℝ, L)) ∞ F)
    (he : ∀ x, F (e x) = e (a x)) :
    ∃ D : LieDerivation ℝ L L, ∃ hD : IsNilpotent D.toLinearMap,
      ∀ x, nilpotentDerivationFlow D hD 1 x = F x := by
  let A := polynomialModelLieEquiv F hF
  have hA : IsNilpotent (A.toLinearMap - 1) :=
    lattice_automorphism_unipotent b p hp hsurj e hgrid j hj a t ha A.toLinearMap
      (by intro x; change A (e x) = e (a x); rw [polynomialModelLieEquiv_apply]; exact he x)
  refine ⟨unipotentLieLogarithm A hA, unipotentLieLogarithm_nilpotent A hA, ?_⟩
  intro x
  change unipotentLieFlow A hA 1 x = F x
  rw [unipotentLieFlow_one, polynomialModelLieEquiv_apply]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_OrderedSemidirectWords
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Ordered integral words in an infinite cyclic extension -/

namespace PolycyclicRecognition
variable {H G : Type*} [Group H] [Group G] {d : ℕ}

theorem orderedWord_snoc (X : Fin d → G) (t : G) (z : Fin (d + 1) → ℤ) :
    orderedWord (Fin.snoc X t) z =
      orderedWord X (fun i => z i.castSucc) * t ^ z (Fin.last d) := by
  simp only [orderedWord, List.ofFn_succ', List.prod_concat, Fin.snoc_castSucc, Fin.snoc_last]

theorem cyclicExtension_orderedWord (a : MulAut H) (X : Fin d → H)
    (z : Fin (d + 1) → ℤ) :
    orderedWord (cyclicExtensionGenerators a X) z =
      SemidirectProduct.inl (orderedWord X (fun i => z i.castSucc)) *
        SemidirectProduct.inr (Multiplicative.ofAdd (z (Fin.last d))) := by
  rw [cyclicExtensionGenerators, orderedWord_snoc, orderedWord_map, ← map_zpow]
  congr 2
  change (z (Fin.last d)) • (1 : ℤ) = z (Fin.last d)
  simp

theorem cyclicExtension_orderedWord_surjective (a : MulAut H) (X : Fin d → H)
    (hX : Function.Surjective (orderedWord X)) :
    Function.Surjective (orderedWord (cyclicExtensionGenerators a X)) := by
  intro g
  obtain ⟨z, hz⟩ := hX g.left
  refine ⟨Fin.snoc z g.right.toAdd, ?_⟩
  rw [cyclicExtension_orderedWord]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, hz, ofAdd_toAdd]
  exact SemidirectProduct.inl_left_mul_inr_right g

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Lattices_DerivationSolvableModel
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.JointFixedReductionData.residualLayer_normal _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.abelianRealCoordinates _root_.OAI.PolycyclicRecognition.abelianRealFiniteDimensional _root_.OAI.PolycyclicRecognition.abelianRealLieAbelian _root_.OAI.PolycyclicRecognition.abelianRealNormedLie _root_.OAI.PolycyclicRecognition.derivationLieSpaceFiniteDimensional _root_.OAI.PolycyclicRecognition.derivationLieSpaceRealNormed _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.polynomialLieIdealSubgroup_normal _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The solvable real model of a nilpotent derivation extension -/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold
variable {L : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L] [Group.IsSolvable L]
  (D : LieDerivation ℝ L L) (hD : IsNilpotent D.toLinearMap)

attribute [local instance] semidirectProductTopology

theorem continuous_derivationModelEquiv : Continuous (derivationModelEquiv D hD) := by
  change Continuous ((semidirectProductHomeomorph (P.derivationAction D hD)).symm ∘
    (fun p : L × ℝ => (p.1, Multiplicative.ofAdd p.2)))
  exact (semidirectProductHomeomorph _).symm.continuous.comp continuous_id

theorem continuous_derivationModelEquiv_symm : Continuous (derivationModelEquiv D hD).symm := by
  change Continuous ((fun p : L × Multiplicative ℝ => (p.1, p.2.toAdd)) ∘
    (semidirectProductHomeomorph (P.derivationAction D hD)))
  exact continuous_id.comp (semidirectProductHomeomorph _).continuous

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Lattices_NilpotentLatticeDerivationExtension
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.JointFixedReductionData.residualLayer_normal _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.polynomialLieIdealSubgroup_normal _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.JointFixedReductionData.residualLayerProjection_equiv _root_.OAI.PolycyclicRecognition.NilpotentKernelCompletion.extendedAction_embed _root_.OAI.PolycyclicRecognition.NilpotentLatticeCoordinates.automorphism_mul _root_.OAI.PolycyclicRecognition.NilpotentLatticeCoordinates.automorphism_on_lattice _root_.OAI.PolycyclicRecognition.NilpotentLatticeCoordinates.automorphism_one _root_.OAI.PolycyclicRecognition.PolynomialExponentialCoordinates.analyticDerivationAction_apply _root_.OAI.PolycyclicRecognition.analyticDerivationExp_apply _root_.OAI.PolycyclicRecognition.derivationSemidirectHom_apply _root_.OAI.PolycyclicRecognition.polynomialCoordinateHom_apply _root_.OAI.PolycyclicRecognition.polynomialInnerLieEquiv_apply _root_.OAI.PolycyclicRecognition.polynomialModelLieEquiv_apply _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Retaining the integral parameter in the real derivation extension -/

noncomputable section
namespace PolycyclicRecognition
open Module
attribute [local instance] semidirectProductTopology

variable {H : Type} [Group H]

theorem NilpotentLatticeCoordinates.derivation_extension
    (C : NilpotentLatticeCoordinates H) (a : MulAut H)
    (D : LieDerivation ℝ C.carrier C.carrier) (hD : IsNilpotent D.toLinearMap)
    (hstep : ∀ x, (C.equiv (a x) : C.carrier) =
      nilpotentDerivationFlow D hD 1 (C.equiv x)) :
    Nonempty (NilpotentLatticeCoordinates
      (H ⋊[integerPowerAction a] Multiplicative ℤ)) := by
  let L := C.carrier
  let φ := C.coordinates.derivationAction D hD
  obtain ⟨Γ, hΓ, f, hf⟩ := integer_semidirect_lattice_realization_with_coordinates
    φ a C.lattice C.uniform C.equiv hstep
  let := derivationSemidirectGroup D hD
  let _ : Mul (L × ℝ) := (derivationSemidirectGroup D hD).toMul
  obtain ⟨Q, E, hE⟩ := exists_semidirect_polynomial_exponential_coordinates D hD
  let := Q
  let T := DerivationLieSpace D hD
  let _ : Group T := Q.group
  let _ : Mul T := Q.group.toMul
  let F : T ≃* (L ⋊[φ] Multiplicative ℝ) := E.trans
    { derivationSemidirectEquiv D hD with map_mul' := fun _ _ => rfl }
  let : Group.IsSolvable (L ⋊[φ] Multiplicative ℝ) := semidirect_solvable φ
  let : Group.IsSolvable T :=
    Group.isSolvable_of_isSolvable_injective (f := F.toMonoidHom) F.injective
  let s := derivationLieSpaceSplit D hD
  let b := cyclicParameterBasis C.basis s
  let c := Module.finBasis ℝ (L × ℝ)
  let p := transportedProductParameter C.parameter s E.toEquiv
  have hpoly := polynomial_transported_product_parameter C.basis c b
    C.parameter s E.toEquiv C.polynomial C.polynomial_symm (hE b c).1 (hE b c).2
  have hF : Continuous F := by
    exact (continuous_derivationModelEquiv D hD).comp ((hE b c).1.contDiff.continuous)
  have hFi : Continuous F.symm := by
    exact (hE b c).2.contDiff.continuous.comp (continuous_derivationModelEquiv_symm D hD)
  let Λ := Γ.comap F.toMonoidHom
  let e : (H ⋊[integerPowerAction a] Multiplicative ℤ) ≃* Λ :=
    f.trans (comapSubgroupEquiv F Γ).symm
  refine ⟨{
    carrier := T
    lieNilpotent := derivationLieSpace_nilpotent D hD
    dimension := C.dimension + 1
    basis := b
    parameter := p
    polynomial := hpoly.1
    polynomial_symm := hpoly.2
    lattice := Λ
    uniform := hΓ.comap_mulEquiv F hF hFi
    equiv := e
    generators := cyclicExtensionGenerators a C.generators
    word_surjective := cyclicExtension_orderedWord_surjective a C.generators C.word_surjective
    integer_parameter := ?_ }⟩
  intro z
  apply F.injective
  change F (p (b.equivFun.symm (fun i => (z i : ℝ)))) =
    F (F.symm (f (orderedWord (cyclicExtensionGenerators a C.generators) z)))
  rw [F.apply_symm_apply, hf]
  have hp := transportedProductParameter_integer C.basis C.parameter s E.toEquiv z
  change E (p (b.equivFun.symm (fun i => (z i : ℝ)))) =
    (C.parameter (C.basis.equivFun.symm (fun i => (z i.castSucc : ℝ))),
      (z (Fin.last C.dimension) : ℝ)) at hp
  rw [cyclicExtension_orderedWord]
  apply SemidirectProduct.ext
  · change (E (p (b.equivFun.symm (fun i => (z i : ℝ))))).1 = _
    simpa [realIntegerSemidirectMap] using
      (congrArg Prod.fst hp).trans (C.integer_parameter _)
  · change Multiplicative.ofAdd (E (p (b.equivFun.symm (fun i => (z i : ℝ))))).2 = _
    simpa [realIntegerSemidirectMap, integerTimeHom] using
      congrArg Multiplicative.ofAdd (congrArg Prod.snd hp)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Lattices_NilpotentLatticeCyclicExtension
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.JointFixedReductionData.residualLayer_normal _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.polynomialLieIdealSubgroup_normal _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The iterative nilpotent lattice step

Ordered real generator powers extend conjugation; the finite logarithm of
its differential supplies the flow. The output retains the lattice parameter.
-/

noncomputable section
namespace PolycyclicRecognition
variable {H : Type} [Group H]

theorem NilpotentLatticeCoordinates.cyclic_extension
    (C : NilpotentLatticeCoordinates H) (a : MulAut H)
    [Group.IsNilpotent (H ⋊[integerPowerAction a] Multiplicative ℤ)] :
    Nonempty (NilpotentLatticeCoordinates
      (H ⋊[integerPowerAction a] Multiplicative ℤ)) := by
  let G := H ⋊[integerPowerAction a] Multiplicative ℤ
  let j : H →* G := SemidirectProduct.inl
  let t : G := SemidirectProduct.inr (Multiplicative.ofAdd (1 : ℤ))
  have ha (x : H) : j (a x) = t * j x * t⁻¹ := by
    have h := SemidirectProduct.inl_aut (φ := integerPowerAction a)
      (Multiplicative.ofAdd (1 : ℤ)) x
    rw [map_inv] at h
    change j ((a ^ (1 : ℤ)) x) = t * j x * t⁻¹ at h
    simpa only [zpow_one] using h
  let q := C.lattice.subtype.comp C.equiv.toMonoidHom
  let F := latticeWordAut C.basis C.parameter q C.generators
    C.polynomial C.polynomial_symm C.integer_parameter C.word_surjective a
  obtain ⟨D, hD, htime⟩ := exists_nilpotent_lattice_automorphism_log
    C.basis C.parameter C.polynomial C.parameter.surjective q
    (fun z => ⟨orderedWord C.generators z, (C.integer_parameter z).symm⟩)
    j SemidirectProduct.inl_injective a t ha F
    (contMDiff_latticeWordAut C.basis C.parameter q C.generators
      C.polynomial C.polynomial_symm C.integer_parameter C.word_surjective a)
    (latticeWordAut_on_lattice C.basis C.parameter q C.generators
      C.polynomial C.polynomial_symm C.integer_parameter C.word_surjective a)
  apply C.derivation_extension a D hD
  intro x
  rw [htime]
  exact (latticeWordAut_on_lattice C.basis C.parameter q C.generators
    C.polynomial C.polynomial_symm C.integer_parameter C.word_surjective a x).symm

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Lattices_NilpotentLatticeInduction
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Realizing an arbitrary finitely generated torsion-free nilpotent group

The induction follows an actual torsion-free cyclic series. Its successive
integer normal forms are retained as polynomial parameters at every stage.
-/

noncomputable section
namespace PolycyclicRecognition
variable {G : Type} [Group G] [Group.IsNilpotent G]

theorem nilpotent_lattice_coordinates_of_cyclic_quotient
    (N : Subgroup G) [N.Normal] [IsCyclic (G ⧸ N)]
    (C : NilpotentLatticeCoordinates N)
    (hQ : HasNoNontrivialTorsion (G ⧸ N)) :
    Nonempty (NilpotentLatticeCoordinates G) := by
  cases finite_or_infinite (G ⧸ N) with
  | inl h =>
    let := h
    let := subsingleton_of_finite_torsionFree (G ⧸ N) hQ
    have htop : N = ⊤ := by
      apply top_unique
      intro g _
      exact (QuotientGroup.eq_one_iff g).mp (Subsingleton.elim _ _)
    subst N
    exact ⟨C.of_equiv Subgroup.topEquiv⟩
  | inr h =>
    let := h
    let E : Multiplicative ℤ ≃* G ⧸ N := intCyclicMulEquiv
    let q : G →* Multiplicative ℤ := E.symm.toMonoidHom.comp (QuotientGroup.mk' N)
    have hker : q.ker = N := by
      ext g
      change E.symm (QuotientGroup.mk' N g) = 1 ↔ g ∈ N
      rw [← E.symm.map_one, E.symm.injective.eq_iff]
      exact QuotientGroup.eq_one_iff g
    obtain ⟨t, ht⟩ := QuotientGroup.mk'_surjective N (E (Multiplicative.ofAdd 1))
    have hqt : q t = Multiplicative.ofAdd 1 := by
      change E.symm (QuotientGroup.mk' N t) = _
      rw [ht, E.symm_apply_apply]
    let e := cyclicKernelEquiv q t hqt
    let : Group.IsNilpotent
        (q.ker ⋊[integerPowerAction (MulAut.conjNormal t)] Multiplicative ℤ) :=
      (Group.isNilpotent_congr e).mpr inferInstance
    let C' := C.of_equiv (MulEquiv.subgroupCongr hker.symm)
    obtain ⟨D⟩ := C'.cyclic_extension (MulAut.conjNormal t)
    exact ⟨D.of_equiv e⟩

theorem nilpotent_lattice_coordinates_of_polyZ (hG : IsPolyZ G) :
    Nonempty (NilpotentLatticeCoordinates G) := by
  obtain ⟨n, c, hc⟩ := hG
  have hm : ∀ i, i ≤ n → Nonempty (NilpotentLatticeCoordinates (c.group i)) := by
    intro i
    induction i with
    | zero =>
      intro _
      rw [c.first]
      exact ⟨NilpotentLatticeCoordinates.of_subsingleton⟩
    | succ i ih =>
      intro hi
      let s := c.step i (by omega)
      let := s.normal
      let := s.cyclic
      let e := (Subgroup.subgroupOfEquivOfLe s.le).symm
      obtain ⟨C⟩ := ih (by omega)
      exact nilpotent_lattice_coordinates_of_cyclic_quotient
        ((c.group i).subgroupOf (c.group (i + 1))) (C.of_equiv e) (hc i (by omega))
  obtain ⟨C⟩ := hm n le_rfl
  rw [c.last] at C
  exact ⟨C.of_equiv Subgroup.topEquiv⟩

theorem nilpotent_lattice_coordinates [Group.FG G]
    (hG : HasNoNontrivialTorsion G) : Nonempty (NilpotentLatticeCoordinates G) :=
  nilpotent_lattice_coordinates_of_polyZ
    (nilpotent_polyZ_of_finitelyGenerated_torsionFree hG)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Lattices_LatticeRealizationFiniteIndex
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.latticeNormalFlag_normal _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
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

theorem nilpotent_integer_extension_realization {n : ℕ}
    (q : G →* IntegralLatticeGroup n) (hq : Function.Surjective q)
    [Group.FG q.ker] [Group.IsNilpotent q.ker] (ht : HasNoNontrivialTorsion q.ker) :
    ∃ K : Subgroup G, K.FiniteIndex ∧ ∃ (S : SimplyConnectedSolvableLieModel)
      (Λ : Subgroup S.carrier), IsUniformLattice Λ ∧ Nonempty (K ≃* Λ) := by
  let E : GroupExtension q.ker G (IntegralLatticeGroup n) :=
    { inl := q.ker.subtype
      rightHom := q
      inl_injective := Subtype.val_injective
      range_inl_eq_ker_rightHom := Subgroup.range_subtype _
      rightHom_surjective := hq }
  obtain ⟨C⟩ := nilpotent_lattice_coordinates ht
  exact C.extension_realization E (normalizedExtensionSection E) (normalizedExtensionSection_one E)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_NilpotentByAbelianRealization
attribute [-instance] _root_.GeneratesNS.rho_g_FG _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.latticeNormalFlag_normal _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

namespace OAI

/-! # Nonsplit nilpotent-by-abelian groups of polycyclic type -/

noncomputable section
namespace PolycyclicRecognition
open scoped IsMulCommutative
variable {G : Type} [Group G]

theorem nilpotent_by_abelian_uniform_lattice_oai (hG : IsPolycyclic G)
    (ht : HasNoNontrivialTorsion G) (N : Subgroup G) [N.Normal]
    [Group.IsNilpotent N] [IsMulCommutative (G ⧸ N)] :
    ∃ K : Subgroup G, K.FiniteIndex ∧ ∃ (S : SimplyConnectedSolvableLieModel)
      (Λ : Subgroup S.carrier), IsUniformLattice Λ ∧ Nonempty (K ≃* Λ) := by
  let : Group.FG G := hG.finitelyGenerated
  let : CommGroup (G ⧸ N) := inferInstance
  have hQ : IsPolycyclic (G ⧸ N) := hG.of_surjective (QuotientGroup.mk' N)
    (QuotientGroup.mk'_surjective N)
  obtain ⟨U, hU, htf⟩ := hQ.exists_torsionFree_finiteIndex
  let := hU
  let : Group.FG U := inferInstance
  obtain ⟨n, ⟨e⟩⟩ := exists_integralLattice_equiv (A := U) htf
  let π := QuotientGroup.mk' N
  let H := U.comap π
  let : H.FiniteIndex := inferInstance
  let f : H →* U := (π.comp H.subtype).codRestrict U (fun x => x.property)
  have hf : Function.Surjective f := by
    intro u
    obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective N (u : G ⧸ N)
    have hgH : g ∈ H := by change π g ∈ U; rw [hg]; exact u.property
    exact ⟨⟨g, hgH⟩, Subtype.ext hg⟩
  let q := e.symm.toMonoidHom.comp f
  have hq : Function.Surjective q := e.symm.surjective.comp hf
  have hk (a : q.ker) : ((a : H) : G) ∈ N := by
    have ha : q (a : H) = 1 := a.property
    have hfa : f (a : H) = 1 := e.symm.injective
      (ha.trans (map_one e.symm.toMonoidHom).symm)
    have hh := congrArg (fun u : U => (u : G ⧸ N)) hfa
    exact (QuotientGroup.eq_one_iff _).mp hh
  let k : q.ker →* N := (H.subtype.comp q.ker.subtype).codRestrict N hk
  have hki : Function.Injective k := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun x : N => (x : G)) hab
  let : Group.IsNilpotent q.ker := nilpotent_of_injective_hom k hki
  have hi : Function.Injective (H.subtype.comp q.ker.subtype) :=
    Subtype.val_injective.comp Subtype.val_injective
  let : Group.FG q.ker := (hG.of_injective _ hi).finitelyGenerated
  have htk : HasNoNontrivialTorsion q.ker := ht.of_injective _ hi
  exact uniform_lattice_realization_of_finiteIndex H
    (nilpotent_integer_extension_realization q hq htk)

end PolycyclicRecognition

end

end OAI
end

theorem solution : type_of% @OAI.PolycyclicRecognition.nilpotent_by_abelian_uniform_lattice_oai := @OAI.PolycyclicRecognition.nilpotent_by_abelian_uniform_lattice_oai
