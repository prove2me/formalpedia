-- Prove2me | solution 1 for OAI.PolycyclicRecognition.recognition_and_lattice_of_uniform_normalized_height_proved
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-02T22:18:49.610086+00:00
-- url     : https://prove2.me/submissions/826d877c-42fa-4da1-b040-57e7aaabb2cc

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_PolycyclicRecognition
import Definitions.Def_OAIQ093D020
import Theorems.Thm_OAI_PolycyclicRecognition_TypeFPInfinity_heightKernel_virtualSolvable
import Theorems.Thm_OAI_PolycyclicRecognition_polynomialBoundedChainPacking_intrinsic
import Theorems.Thm_OAI_PolycyclicRecognition_virtuallyPolycyclic_of_coarse_rational_bounds

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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_PolycyclicFiniteGeneration
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_FiniteInduction
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesHomology _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
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
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesHomology _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_NormalizePositiveMass
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesHomology _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Normalizing a positive partition mass bounded below by one -/

namespace PolycyclicRecognition

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The cutoff partition has mass at least one. Normalizing such vectors
costs at most a factor two in their normed distance. -/
theorem norm_normalized_sub_le_two (x y : E) (hx : 1 ≤ ‖x‖) (hy : 1 ≤ ‖y‖) :
    ‖‖x‖⁻¹ • x - ‖y‖⁻¹ • y‖ ≤ 2 * ‖x - y‖ := by
  have hx0 : 0 < ‖x‖ := lt_of_lt_of_le zero_lt_one hx
  have hy0 : 0 < ‖y‖ := lt_of_lt_of_le zero_lt_one hy
  have hcoef : (‖x‖⁻¹ - ‖y‖⁻¹) * ‖y‖ = (‖y‖ - ‖x‖) / ‖x‖ := by
    field_simp
  have he : ‖(‖x‖⁻¹ - ‖y‖⁻¹) • y‖ = |‖y‖ - ‖x‖| / ‖x‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    calc
      |‖x‖⁻¹ - ‖y‖⁻¹| * ‖y‖ = |(‖x‖⁻¹ - ‖y‖⁻¹) * ‖y‖| := by
        rw [abs_mul, abs_of_nonneg (norm_nonneg y)]
      _ = |‖y‖ - ‖x‖| / ‖x‖ := by rw [hcoef, abs_div, abs_of_pos hx0]
  have hnorm : |‖y‖ - ‖x‖| ≤ ‖x - y‖ := by
    simpa only [dist_zero_right, dist_eq_norm, sub_zero, norm_sub_rev] using abs_dist_sub_le y x (0 : E)
  calc
    _ = ‖‖x‖⁻¹ • (x - y) + (‖x‖⁻¹ - ‖y‖⁻¹) • y‖ := by
      congr 1
      rw [smul_sub, sub_smul]
      abel
    _ ≤ ‖‖x‖⁻¹ • (x - y)‖ + ‖(‖x‖⁻¹ - ‖y‖⁻¹) • y‖ := norm_add_le _ _
    _ = ‖x - y‖ / ‖x‖ + |‖y‖ - ‖x‖| / ‖x‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hx0), he]
      simp only [div_eq_inv_mul]
    _ ≤ ‖x - y‖ / ‖x‖ + ‖x - y‖ / ‖x‖ :=
      add_le_add le_rfl (div_le_div_of_nonneg_right hnorm hx0.le)
    _ ≤ 2 * ‖x - y‖ := by
      have hdiv : ‖x - y‖ / ‖x‖ ≤ ‖x - y‖ :=
        (div_le_iff₀ hx0).mpr (by nlinarith only [hx, norm_nonneg (x - y)])
      linarith only [hdiv]

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_FiniteCutoffPartition
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesHomology _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The quantitative cutoff partition used by Lipschitz replacement -/

noncomputable section
namespace PolycyclicRecognition

open scoped BigOperators

variable {X I : Type*} [MetricSpace X] [Fintype I]

private theorem cutoff_difference_le (v x y : X) :
    |max 0 (2 - dist x v) - max 0 (2 - dist y v)| ≤ dist x y := by
  have hd := abs_le.mp (abs_dist_sub_le x y v)
  simp only [max_def]
  split_ifs <;> apply abs_le.mpr <;> constructor <;> linarith [dist_nonneg (x := x) (y := y)]

/-- Before normalization, at most one distance error is charged per
participating center. The application restricts to the finite local support. -/
theorem norm_cutoffMass_sub_le (v : I → X) (x y : X) :
    ‖cutoffMass v x - cutoffMass v y‖ ≤ (Fintype.card I : ℝ) * dist x y := by
  rw [PiLp.norm_eq_of_L1]
  change (∑ i, |max 0 (2 - dist x (v i)) - max 0 (2 - dist y (v i))|) ≤ _
  calc
    _ ≤ ∑ _i : I, dist x y := Finset.sum_le_sum (fun i _ => cutoff_difference_le (v i) x y)
    _ = _ := by simp

/-- The unit-ball cover gives the uniform lower bound on the denominator. -/
theorem one_le_norm_cutoffMass (v : I → X) (x : X)
    (hcover : ∃ i, dist x (v i) ≤ 1) : 1 ≤ ‖cutoffMass v x‖ := by
  obtain ⟨i, hi⟩ := hcover
  rw [PiLp.norm_eq_of_L1]
  change 1 ≤ ∑ j, ‖max 0 (2 - dist x (v j))‖
  calc
    1 ≤ max 0 (2 - dist x (v i)) := (by linarith : 1 ≤ 2 - dist x (v i)).trans (le_max_right _ _)
    _ = ‖max 0 (2 - dist x (v i))‖ := (Real.norm_of_nonneg (le_max_left _ _)).symm
    _ ≤ _ := Finset.single_le_sum (fun j _ => norm_nonneg (max 0 (2 - dist x (v j)))) (Finset.mem_univ i)

/-- Normalization costs a factor two, uniformly over points whose unit
balls contain one of the participating centers. -/
theorem norm_cutoffPartition_sub_le (v : I → X) (x y : X)
    (hx : ∃ i, dist x (v i) ≤ 1) (hy : ∃ i, dist y (v i) ≤ 1) :
    ‖cutoffPartition v x - cutoffPartition v y‖ ≤
      2 * (Fintype.card I : ℝ) * dist x y := by
  exact (norm_normalized_sub_le_two (cutoffMass v x) (cutoffMass v y)
    (one_le_norm_cutoffMass v x hx) (one_le_norm_cutoffMass v y hy)).trans
    (by nlinarith only [norm_cutoffMass_sub_le v x y])

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_FiniteRestriction
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesHomology _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_FiniteIndexRestriction
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.cyclicTopHomologyInjection_mono _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesHomology _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite integral resolutions restrict to finite-index subgroups

A finite set of coset representatives enlarges a generating set over the
ambient group ring to one over the subgroup ring.
-/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits Representation
open scoped MonoidAlgebra
attribute [local instance 2000] Rep.hV2

variable {G : Type} [Group G] (H : Subgroup G) [H.FiniteIndex]

theorem integralRepresentationFinite_restrict (A : Rep.{0} ℤ G)
    (hA : IntegralRepresentationFinite G A) :
    IntegralRepresentationFinite H (Rep.res H.subtype A) := by
  classical
  let : Module ℤ A := A.hV2
  let : Module.Finite ℤ[G] A.ρ.asModule := hA
  obtain ⟨s, hs, hspan⟩ := Submodule.fg_def.mp (Module.Finite.fg_top :
    (⊤ : Submodule ℤ[G] A.ρ.asModule).FG)
  let C := Quotient (QuotientGroup.rightRel H)
  let : Finite C := Finite.of_equiv (G ⧸ H)
    (QuotientGroup.quotientRightRelEquivQuotientLeftRel H).symm
  let : Finite s := hs.to_subtype
  let gen : C × s → (Rep.res H.subtype A).ρ.asModule := fun j =>
    (Rep.res H.subtype A).ρ.asModuleEquiv.symm
      (A.ρ (Quotient.out j.1) (A.ρ.asModuleEquiv j.2.val))
  let p : Submodule ℤ[H] (Rep.res H.subtype A).ρ.asModule :=
    Submodule.span ℤ[H] (Set.range gen)
  let pR := Subrepresentation.ofSubmodule' p
  have horbit (a : A.ρ.asModule) (ha : a ∈ s) (g : G) :
      A.ρ g (A.ρ.asModuleEquiv a) ∈ pR := by
    let c : C := Quotient.mk (QuotientGroup.rightRel H) g
    let r : G := Quotient.out c
    have hn : g * r⁻¹ ∈ H := QuotientGroup.rightRel_apply.mp
      (Quotient.exact' (Quotient.out_eq' c))
    let n : H := ⟨g * r⁻¹, hn⟩
    have hg : (n : G) * r = g := by simp [n]
    have hr : A.ρ r (A.ρ.asModuleEquiv a) ∈ pR := by
      change (Rep.res H.subtype A).ρ.asModuleEquiv.symm
        (A.ρ r (A.ρ.asModuleEquiv a)) ∈ p
      exact Submodule.subset_span ⟨(c, ⟨a, ha⟩), rfl⟩
    have hm := pR.apply_mem_toSubmodule n hr
    change A.ρ (n : G) (A.ρ r (A.ρ.asModuleEquiv a)) ∈ pR at hm
    simpa only [← Module.End.mul_apply, ← map_mul, hg] using hm
  let q : Subrepresentation A.ρ :=
    { toSubmodule := ⨅ g : G, pR.toSubmodule.comap (A.ρ g)
      apply_mem_toSubmodule g a ha := by
        simp only [Submodule.mem_iInf, Submodule.mem_comap] at ha ⊢
        intro k
        simpa only [← Module.End.mul_apply, ← map_mul] using ha (k * g) }
  have hsq : s ⊆ q.asSubmodule := by
    intro a ha
    change A.ρ.asModuleEquiv a ∈ q.toSubmodule
    simp only [q, Submodule.mem_iInf, Submodule.mem_comap]
    exact horbit a ha
  have hq : q.asSubmodule = ⊤ := by
    apply top_unique
    rw [← hspan]
    exact Submodule.span_le.mpr hsq
  have hp : p = ⊤ := by
    apply top_unique
    intro a _
    have ha : A.ρ.asModuleEquiv.symm ((Rep.res H.subtype A).ρ.asModuleEquiv a) ∈
        q.asSubmodule := by rw [hq]; trivial
    change A.ρ.asModuleEquiv.symm ((Rep.res H.subtype A).ρ.asModuleEquiv a) ∈
      q.toSubmodule at ha
    change (Rep.res H.subtype A).ρ.asModuleEquiv a ∈
      (⨅ g : G, pR.toSubmodule.comap (A.ρ g)) at ha
    have h := ((Submodule.mem_iInf _).mp ha) (1 : G)
    change A.ρ 1 ((Rep.res H.subtype A).ρ.asModuleEquiv a) ∈ pR at h
    rw [map_one] at h
    exact h
  change Module.Finite ℤ[H] (Rep.res H.subtype A).ρ.asModule
  apply Module.Finite.of_fg_top
  rw [← hp]
  exact Submodule.fg_def.mpr ⟨Set.range gen, Set.finite_range gen, rfl⟩

theorem TypeFP.finiteIndex_subgroup {n : ℕ} (hG : TypeFP G n) : TypeFP H n := by
  obtain ⟨P, hP⟩ := hG
  exact ⟨subgroupResolution H P, fun i hi =>
    integralRepresentationFinite_restrict H (P.complex.X i) (hP i hi)⟩

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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_FiniteOrderUnipotent
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesHomology _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_FinitelyGeneratedLift
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesHomology _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
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

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_Packing
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesHomology _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Packing estimates and intrinsic word balls

This is the finite counting step in Lemma `height-kernel-growth` of
*Quasi-isometric recognition of virtually polycyclic groups*. A metric cover of
orbit points and a bound on the number of source points in a small target ball
give a cardinal bound on the original finite set. Applying this to intrinsic
word balls does not require the subgroup to be undistorted in an ambient group.
-/

namespace PolycyclicRecognition

universe u v

section Packing

variable {H : Type u} {X : Type v} [PseudoMetricSpace X]

/-- Count a finite set using a finite metric-ball cover and bounds on each fiber
of the cover. The balls may overlap. -/
theorem card_le_cover_mul [DecidableEq H] [DecidableEq X]
    (S : Finset H) (f : H → X) (centers : Finset X) (radius : ℝ) (M : ℕ)
    (hcover : ∀ h ∈ S, ∃ c ∈ centers, dist (f h) c ≤ radius)
    (hfiber : ∀ c ∈ centers, (S.filter fun h => dist (f h) c ≤ radius).card ≤ M) :
    S.card ≤ centers.card * M := by
  classical
  have hsubset : S ⊆ centers.biUnion (fun c => S.filter fun h => dist (f h) c ≤ radius) := by
    intro h hh
    obtain ⟨c, hc, hdist⟩ := hcover h hh
    exact Finset.mem_biUnion.mpr ⟨c, hc, Finset.mem_filter.mpr ⟨hh, hdist⟩⟩
  exact (Finset.card_le_card hsubset).trans
    (Finset.card_biUnion_le_card_mul centers _ M hfiber)

/-- A uniform bound on all finite subsets lying over a target ball can be used
for every finite source set. -/
theorem card_le_cover_mul_of_bounded_multiplicity [DecidableEq H] [DecidableEq X]
    (S : Finset H) (f : H → X) (centers : Finset X) (radius : ℝ) (M : ℕ)
    (hcover : ∀ h ∈ S, ∃ c ∈ centers, dist (f h) c ≤ radius)
    (hmultiplicity : ∀ (c : X) (A : Finset H),
      (∀ h ∈ A, dist (f h) c ≤ radius) → A.card ≤ M) :
    S.card ≤ centers.card * M := by
  apply card_le_cover_mul S f centers radius M hcover
  intro c _
  apply hmultiplicity c
  intro h hh
  exact (Finset.mem_filter.mp hh).2

end Packing

section WordBalls

variable {H : Type u} [Monoid H] [DecidableEq H]

/-- The identity is represented by the empty word at every radius. -/
theorem one_mem_wordBall (T : Finset H) (n : ℕ) : 1 ∈ wordBall T n := by
  induction n with
  | zero => simp [wordBall]
  | succ n ih => exact Finset.mem_union_left _ ih

/-- This explicit list characterization identifies the recursive finite sets
with intrinsic word balls, rather than with ambient metric balls. -/
theorem mem_wordBall_iff (T : Finset H) (n : ℕ) (h : H) :
    h ∈ wordBall T n ↔ ∃ l : List H,
      l.length ≤ n ∧ (∀ t ∈ l, t ∈ T) ∧ l.prod = h := by
  induction n generalizing h with
  | zero =>
      constructor
      · intro hh
        have hh1 : h = 1 := Finset.mem_singleton.mp hh
        exact ⟨[], by simp, by simp, by simpa using hh1.symm⟩
      · rintro ⟨l, hl, _, hprod⟩
        have hl0 : l = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hl)
        subst l
        simpa only [List.prod_nil, wordBall_zero, Finset.mem_singleton] using hprod.symm
  | succ n ih =>
      constructor
      · intro hh
        rcases Finset.mem_union.mp hh with hh | hh
        · obtain ⟨l, hl, hletters, hprod⟩ := (ih h).mp hh
          exact ⟨l, hl.trans (Nat.le_succ n), hletters, hprod⟩
        · obtain ⟨t, ht, hrest⟩ := Finset.mem_biUnion.mp hh
          obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hrest
          obtain ⟨l, hl, hletters, hprod⟩ := (ih k).mp hk
          refine ⟨t :: l, by simpa using Nat.succ_le_succ hl, ?_, ?_⟩
          · intro a ha
            rcases List.mem_cons.mp ha with rfl | ha
            · exact ht
            · exact hletters a ha
          · simp only [List.prod_cons, hprod]
      · rintro ⟨l, hl, hletters, hprod⟩
        cases l with
        | nil =>
            have hh1 : h = 1 := hprod.symm
            subst h
            exact one_mem_wordBall T (n + 1)
        | cons t l =>
            have hl' : l.length ≤ n := by simpa using hl
            have ht : t ∈ T := hletters t (List.mem_cons_self ..)
            have hletters' : ∀ a ∈ l, a ∈ T :=
              fun a ha => hletters a (List.mem_cons_of_mem t ha)
            have htail : l.prod ∈ wordBall T n := (ih l.prod).mpr ⟨l, hl', hletters', rfl⟩
            apply Finset.mem_union_right
            apply Finset.mem_biUnion.mpr
            refine ⟨t, ht, Finset.mem_image.mpr ⟨l.prod, htail, ?_⟩⟩
            simpa only [List.prod_cons] using hprod

variable {X : Type v} [PseudoMetricSpace X] [DecidableEq X]

/-- A cover of an intrinsic word ball bounds its cardinality with no hypothesis
relating intrinsic word length to an ambient word length. -/
theorem wordBall_card_le_cover_mul (T : Finset H) (f : H → X) (n : ℕ)
    (centers : Finset X) (M : ℕ)
    (hcover : ∀ h ∈ wordBall T n, ∃ c ∈ centers, dist (f h) c ≤ 1)
    (hmultiplicity : ∀ (c : X) (A : Finset H),
      (∀ h ∈ A, dist (f h) c ≤ 1) → A.card ≤ M) :
    (wordBall T n).card ≤ centers.card * M :=
  card_le_cover_mul_of_bounded_multiplicity (wordBall T n) f centers 1 M hcover hmultiplicity

/-- Polynomially many covering balls and bounded multiplicity give polynomial
intrinsic word growth. All constants are independent of the word radius. -/
theorem wordBall_polynomial_card_bound (T : Finset H) (f : H → X)
    (C b M : ℕ) (centers : ℕ → Finset X)
    (hcenters : ∀ n, (centers n).card ≤ C * (1 + n) ^ b)
    (hcover : ∀ n h, h ∈ wordBall T n → ∃ c ∈ centers n, dist (f h) c ≤ 1)
    (hmultiplicity : ∀ (c : X) (A : Finset H),
      (∀ h ∈ A, dist (f h) c ≤ 1) → A.card ≤ M) :
    ∀ n, (wordBall T n).card ≤ (C * M) * (1 + n) ^ b := by
  intro n
  calc
    (wordBall T n).card ≤ (centers n).card * M :=
      wordBall_card_le_cover_mul T f n (centers n) M (hcover n) hmultiplicity
    _ ≤ (C * (1 + n) ^ b) * M := Nat.mul_le_mul_right M (hcenters n)
    _ = (C * M) * (1 + n) ^ b := by ac_rfl

end WordBalls

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_GromovInput
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesHomology _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The polynomial-growth input in height-kernel recognition

Published input: M. Gromov, *Groups of polynomial growth and expanding maps*,
Publications Mathématiques de l'IHÉS **53** (1981), 53–78, Main Theorem, p. 54,
DOI: `10.1007/BF02698687`.

`GromovPolynomialGrowthInput J` is precisely the implication needed here: a
finite symmetric generating set with polynomially bounded intrinsic word balls
gives a nilpotent subgroup of finite index. The supporting covering-to-cardinality
argument uses concrete finite word balls, with this implication as an explicit
hypothesis.
-/

namespace PolycyclicRecognition

universe u v

variable (J : Type u) [Group J]

variable {J} [DecidableEq J]
variable {X : Type v} [PseudoMetricSpace X] [DecidableEq X]

/-- Polynomial packing and bounded multiplicity imply virtual nilpotency,
conditionally on exactly the stated polynomial-growth input of Gromov.
No undistortion condition on `J` is needed. -/
theorem virtuallyNilpotent_of_polynomial_cover
    (gromov : GromovPolynomialGrowthInput J) (T : Finset J)
    (hsymmetric : ∀ t ∈ T, t⁻¹ ∈ T)
    (hgenerates : Subgroup.closure (T : Set J) = ⊤)
    (f : J → X) (C b M : ℕ) (centers : ℕ → Finset X)
    (hcenters : ∀ n, (centers n).card ≤ C * (1 + n) ^ b)
    (hcover : ∀ n h, h ∈ wordBall T n → ∃ c ∈ centers n, dist (f h) c ≤ 1)
    (hmultiplicity : ∀ (c : X) (A : Finset J),
      (∀ h ∈ A, dist (f h) c ≤ 1) → A.card ≤ M) :
    IsVirtuallyNilpotent J := by
  apply gromov T hsymmetric hgenerates
  exact ⟨C * M, b,
    wordBall_polynomial_card_bound T f C b M centers hcenters hcover hmultiplicity⟩

/-- Finite generation supplies a finite symmetric generating set by adjoining
inverses to any finite generating set. -/
theorem exists_symmetric_finite_generating_set [Group.FG J] :
    ∃ T : Finset J, (∀ t ∈ T, t⁻¹ ∈ T) ∧ Subgroup.closure (T : Set J) = ⊤ := by
  obtain ⟨S, hS⟩ := Group.fg_def.mp (inferInstance : Group.FG J)
  refine ⟨S ∪ S.image (fun t => t⁻¹), ?_, ?_⟩
  · intro t ht
    rcases Finset.mem_union.mp ht with ht | ht
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨t, ht, rfl⟩)
    · obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp ht
      simpa only [inv_inv] using Finset.mem_union_left (S.image (fun t => t⁻¹)) hs
  · apply top_unique
    rw [← hS]
    apply Subgroup.closure_mono
    intro t ht
    exact Finset.mem_union_left _ ht

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_CyclicExtensionFiniteness
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.cyclicTopHomologyInjection_mono _root_.OAI.PolycyclicRecognition.finiteResolution_single_supported _root_.OAI.PolycyclicRecognition.finiteTruncationAugmentation_quasiIso _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesHomology _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
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
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.cyclicTopHomologyInjection_mono _root_.OAI.PolycyclicRecognition.finiteResolution_single_supported _root_.OAI.PolycyclicRecognition.finiteTruncationAugmentation_quasiIso _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesHomology _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
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
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesHomology _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
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
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesHomology _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
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
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.repCofiber_projective _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesHomology _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
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
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.cyclicTopHomologyInjection_mono _root_.OAI.PolycyclicRecognition.finiteResolution_single_supported _root_.OAI.PolycyclicRecognition.finiteTruncationAugmentation_quasiIso _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesHomology _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
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
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.booleanPartitionStage_projective _root_.OAI.PolycyclicRecognition.cyclicTopHomologyInjection_mono _root_.OAI.PolycyclicRecognition.finiteResolution_single_supported _root_.OAI.PolycyclicRecognition.finiteTruncationAugmentation_quasiIso _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.horseshoeCover_projective _root_.OAI.PolycyclicRecognition.integralRepresentationSum_projective _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.normalizedSyzygy_projective _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesHomology _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_RationalAbelianRank
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesHomology _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
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
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesHomology _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
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
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesHomology _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
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
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesHomology _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
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
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesHomology _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_FiniteProjectivePresentations
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesHomology _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
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
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesHomology _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
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
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesHomology _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_FiniteAugmentationKernel
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesHomology _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_CyclicDuality
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesHomology _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_IntegralKernelRepresentation
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesHomology _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
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
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.cyclicTopHomologyInjection_mono _root_.OAI.PolycyclicRecognition.finiteResolution_single_supported _root_.OAI.PolycyclicRecognition.finiteTruncationAugmentation_quasiIso _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesHomology _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
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
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.cyclicTopHomologyInjection_mono _root_.OAI.PolycyclicRecognition.finiteResolution_single_supported _root_.OAI.PolycyclicRecognition.finiteTruncationAugmentation_quasiIso _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesHomology _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
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
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.cyclicTopHomologyInjection_mono _root_.OAI.PolycyclicRecognition.finiteResolution_single_supported _root_.OAI.PolycyclicRecognition.finiteTruncationAugmentation_quasiIso _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesHomology _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_CoarseFiniteness
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesHomology _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
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

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_TorsionFreeCyclicExtension
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesHomology _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
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
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesHomology _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
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
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesHomology _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
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
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesHomology _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
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
attribute [-instance] _root_.GeneratesNS.rho_g_FG _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finite_templateSymmetryGroup _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteSubtypeLinearEquivRealIdMemSubgroupLinearSupportSymmetryGroup _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesHomology _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
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
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesHomology _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_PolyZNormalExtension
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesHomology _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
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
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.latticeNormalFlag_normal _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesHomology _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_NilpotentCentralRoots
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesHomology _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
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
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.latticeNormalFlag_normal _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesHomology _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
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

local instance instMulSemiringActionSubtypeMemSubgroupForallIntSubringSmallCoefficientRing_rd93261_1 : MulSemiringAction J (SmallCoefficientRing G) :=
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

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_MassFractionBounds
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesHomology _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Scalar normalization estimates for recursive interpolation -/

namespace PolycyclicRecognition

private theorem mass_fraction_left_le {A B u v : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hAB : A ≤ B)
    (hv : 0 ≤ v) (hvB : v ≤ B) :
    A * |u / A - v / B| ≤ |u - v| + |A - B| := by
  have hid : A * |u / A - v / B| = |(u * B - A * v) / B| := by
    calc
      _ = |A * (u / A - v / B)| := by rw [abs_mul, abs_of_pos hA]
      _ = _ := by congr 1; field_simp
  rw [hid, abs_of_nonpos (sub_nonpos.mpr hAB)]
  apply abs_le.mpr
  constructor
  · apply (le_div_iff₀ hB).mpr
    have ha := neg_abs_le (u - v)
    nlinarith [mul_nonneg (sub_nonneg.mpr hAB) (sub_nonneg.mpr hvB),
      mul_le_mul_of_nonneg_right ha hB.le]
  · apply (div_le_iff₀ hB).mpr
    have ha := le_abs_self (u - v)
    nlinarith [mul_nonneg (sub_nonneg.mpr hAB) hv,
      mul_le_mul_of_nonneg_right ha hB.le]

/-- Normalization of a partial mass costs at most its own change plus
the change of the total mass, after multiplication by the smaller total. -/
theorem min_mass_mul_abs_fraction_sub_le {A B u v : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hu : 0 ≤ u) (huA : u ≤ A)
    (hv : 0 ≤ v) (hvB : v ≤ B) :
    min A B * |u / A - v / B| ≤ |u - v| + |A - B| := by
  rcases le_total A B with h | h
  · rw [min_eq_left h]
    exact mass_fraction_left_le hA hB h hv hvB
  · rw [min_eq_right h]
    simpa only [abs_sub_comm] using mass_fraction_left_le hB hA h hu huA

/-- The smaller normalized partial mass, rescaled by the smaller total,
never exceeds either original partial mass. -/
theorem min_mass_mul_min_fraction_le {A B u v : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    min A B * min (u / A) (v / B) ≤ min u v := by
  have hm : 0 ≤ min A B := le_min hA.le hB.le
  apply le_min
  · calc
      _ ≤ min A B * (u / A) := mul_le_mul_of_nonneg_left (min_le_left _ _) hm
      _ ≤ A * (u / A) := mul_le_mul_of_nonneg_right (min_le_left _ _) (div_nonneg hu hA.le)
      _ = u := by field_simp
  · calc
      _ ≤ min A B * (v / B) := mul_le_mul_of_nonneg_left (min_le_right _ _) hm
      _ ≤ B * (v / B) := mul_le_mul_of_nonneg_right (min_le_right _ _) (div_nonneg hv hB.le)
      _ = v := by field_simp

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ControlledContraction
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesHomology _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform contractions about arbitrary centers -/

noncomputable section
namespace PolycyclicRecognition

open Set Metric

variable (G : Type*) [MetricSpace G]

namespace ControlledContraction

variable {G}

theorem dist_center_le (c : ControlledContraction G) {R C : ℝ}
    (hC : ∀ p z w : G, dist z p ≤ R → dist w p ≤ R →
      ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      dist (c.contract p s z) (c.contract p t w) ≤
        C * (|s - t| + min s t * dist z w))
    {p z : G} (hz : dist z p ≤ R) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    dist (c.contract p s z) p ≤ C * s := by
  have h := hC p z z hz hz s hs 0 ⟨le_rfl, zero_le_one⟩
  simpa only [c.zero, sub_zero, abs_of_nonneg hs.1, min_eq_right hs.1,
    dist_self, mul_zero, add_zero] using h

end ControlledContraction
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_OrderedInterpolation
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesHomology _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Ordered interpolation of finitely many nonnegative masses

Zero masses can be omitted. Thus one fixed order on the net gives compatible
interpolations on different finite supports without a simplicial-complex API.
-/

noncomputable section
namespace PolycyclicRecognition

variable {I G : Type*} [MetricSpace G]

theorem listMass_nonneg (a : I → ℝ) (l : List I) (ha : ∀ i ∈ l, 0 ≤ a i) :
    0 ≤ listMass a l := by
  induction l with
  | nil => exact le_rfl
  | cons i l ih => exact add_nonneg (ha i (by simp)) (ih (fun j hj => ha j (by simp [hj])))

theorem listVariation_nonneg (a b : I → ℝ) (l : List I) : 0 ≤ listVariation a b l :=
  listMass_nonneg _ _ (fun _i _ => abs_nonneg _)

theorem abs_listMass_sub_le (a b : I → ℝ) (l : List I) :
    |listMass a l - listMass b l| ≤ listVariation a b l := by
  induction l with
  | nil => simp [listMass, listVariation]
  | cons i l ih =>
    change |(a i + listMass a l) - (b i + listMass b l)| ≤ |a i - b i| + listVariation a b l
    calc
      _ = |(a i - b i) + (listMass a l - listMass b l)| := by congr 1; ring
      _ ≤ |a i - b i| + |listMass a l - listMass b l| := abs_add_le _ _
      _ ≤ _ := add_le_add le_rfl ih

theorem listMass_filter_zero (a : I → ℝ) (l : List I) :
    listMass a (l.filter (fun i => a i ≠ 0)) = listMass a l := by
  classical
  induction l with
  | nil => rfl
  | cons i l ih =>
    by_cases hi : a i = 0
    · have hd : decide (a i ≠ 0) = false := by simp only [hi, ne_eq, not_true_eq_false, decide_false]
      rw [List.filter_cons_of_neg (by rw [hd]; decide)]
      simpa only [listMass, hi, zero_add] using ih
    · have hd : decide (a i ≠ 0) = true := by exact decide_eq_true hi
      rw [List.filter_cons_of_pos (p := fun j : I => decide (a j ≠ 0)) (a := i) hd]
      simp only [listMass, ih]

theorem orderedCenter_singleton (c : ControlledContraction G) (p₀ : G)
    (v : I → G) (a : I → ℝ) (i : I) : orderedCenter c p₀ v a [i] = v i := by
  simp [orderedCenter, listMass, c.zero]

/-- Inserting a zero mass at the front does not change a positive-mass
interpolation. This is the compatibility needed at a support boundary. -/
theorem orderedCenter_zero_cons (c : ControlledContraction G) (p₀ : G)
    (v : I → G) (a : I → ℝ) (i : I) (l : List I)
    (hi : a i = 0) (hl : listMass a l ≠ 0) :
    orderedCenter c p₀ v a (i :: l) = orderedCenter c p₀ v a l := by
  simp [orderedCenter, listMass, hi, div_self hl, c.one]

/-- Erasing all zero coordinates does not change the interpolated point
when the total mass is positive. -/
theorem orderedCenter_filter_zero (c : ControlledContraction G) (p₀ : G)
    (v : I → G) (a : I → ℝ) (l : List I)
    (ha : ∀ i ∈ l, 0 ≤ a i) (hm : 0 < listMass a l) :
    orderedCenter c p₀ v a (l.filter (fun i => a i ≠ 0)) = orderedCenter c p₀ v a l := by
  classical
  induction l with
  | nil => simp [listMass] at hm
  | cons i l ih =>
    have hal : ∀ j ∈ l, 0 ≤ a j := fun j hj => ha j (by simp [hj])
    have hml := listMass_nonneg a l hal
    by_cases hi : a i = 0
    · have hpos : 0 < listMass a l := by simpa [listMass, hi] using hm
      have hd : decide (a i ≠ 0) = false := by simp only [hi, ne_eq, not_true_eq_false, decide_false]
      rw [List.filter_cons_of_neg (by rw [hd]; decide), orderedCenter_zero_cons c p₀ v a i l hi hpos.ne']
      exact ih hal hpos
    · have hd : decide (a i ≠ 0) = true := decide_eq_true hi
      rw [List.filter_cons_of_pos (p := fun j : I => decide (a j ≠ 0)) (a := i) hd]
      change c.contract (v i) (listMass a (l.filter (fun j => decide (a j ≠ 0))) /
          listMass a (i :: l.filter (fun j => decide (a j ≠ 0))))
          (orderedCenter c p₀ v a (l.filter (fun j => decide (a j ≠ 0)))) = _
      rw [listMass, listMass_filter_zero]
      by_cases hl : listMass a l = 0
      · simp [hl, orderedCenter, listMass, c.zero]
      · rw [ih hal (lt_of_le_of_ne hml (Ne.symm hl))]
        rfl

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_OrderedInterpolationRadius
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesHomology _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform radius of interpolation on a bounded number of vertices -/

namespace PolycyclicRecognition

variable {I G : Type*} [MetricSpace G]

theorem listMass_tail_fraction_mem (a : I → ℝ) (i : I) (l : List I)
    (ha : ∀ j ∈ i :: l, 0 ≤ a j) :
    listMass a l / listMass a (i :: l) ∈ Set.Icc (0 : ℝ) 1 := by
  have ht := listMass_nonneg a l (fun j hj => ha j (by simp [hj]))
  have htot := listMass_nonneg a (i :: l) ha
  refine ⟨div_nonneg ht htot, ?_⟩
  by_cases hz : listMass a (i :: l) = 0
  · simp [hz]
  · apply (div_le_one (lt_of_le_of_ne htot (Ne.symm hz))).mpr
    change listMass a l ≤ a i + listMass a l
    exact le_add_of_nonneg_left (ha i (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))

/-- With at most `n` input vertices of bounded diameter, interpolation
stays within a radius depending only on `n`, the diameter, and the contraction. -/
theorem exists_interpolation_radius (c : ControlledContraction G) {D : ℝ} (hD : 0 ≤ D) (n : ℕ) :
    ∃ R : ℝ, 0 ≤ R ∧ InterpolationRadius (I := I) c D n R := by
  induction n with
  | zero =>
    refine ⟨0, le_rfl, ?_⟩
    intro l p₀ v a hne hlen ha hdiam p hp
    have : l = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hlen)
    exact (hne this).elim
  | succ n ih =>
    obtain ⟨R, hR, hrad⟩ := ih
    obtain ⟨C, hC, hcontrol⟩ := c.bounds R hR
    have hC0 : 0 ≤ C := le_trans zero_le_one hC
    refine ⟨C + D, add_nonneg hC0 hD, ?_⟩
    intro l p₀ v a hne hlen ha hdiam p hp
    cases l with
    | nil => exact (hne rfl).elim
    | cons i l =>
      cases l with
      | nil =>
        rw [orderedCenter_singleton]
        exact (hp i (by simp)).trans (le_add_of_nonneg_left hC0)
      | cons j tail =>
        have htlen : (j :: tail).length ≤ n := by simpa only [List.length_cons, Nat.add_le_add_iff_right] using hlen
        have hat : ∀ k ∈ j :: tail, 0 ≤ a k := fun k hk => ha k (List.mem_cons_of_mem i hk)
        have hdiamt : ∀ k ∈ j :: tail, ∀ m ∈ j :: tail, dist (v k) (v m) ≤ D :=
          fun k hk m hm => hdiam k (List.mem_cons_of_mem i hk) m (List.mem_cons_of_mem i hm)
        have hi : ∀ k ∈ j :: tail, dist (v k) (v i) ≤ D :=
          fun k hk => hdiam k (List.mem_cons_of_mem i hk) i (by simp)
        have hr := hrad (j :: tail) p₀ v a (by simp) htlen hat hdiamt (v i) hi
        have hs := listMass_tail_fraction_mem a i (j :: tail) ha
        have hb := c.dist_center_le hcontrol hr hs
        change dist (c.contract (v i) (listMass a (j :: tail) / listMass a (i :: j :: tail))
          (orderedCenter c p₀ v a (j :: tail))) p ≤ C + D
        exact (dist_triangle _ (v i) p).trans (add_le_add
          (hb.trans (mul_le_of_le_one_right hC0 hs.2)) (hp i (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)))

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_LipschitzInversePairBounds
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesHomology _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Lower quasi-isometry bounds from Lipschitz coarse inverses -/

namespace PolycyclicRecognition

open scoped NNReal

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

/-- A Lipschitz inverse with bounded composition error supplies the lower
inequality, with the same enlarged constant used by the compact pair space. -/
theorem coarse_lower_of_lipschitz_inverse
    {Λ : ℝ≥0} (hΛ : 2 ≤ (Λ : ℝ)) (f : X → Y) (g : Y → X)
    (hg : LipschitzWith Λ g) (hinv : ∀ x, dist (g (f x)) x ≤ Λ) (x y : X) :
    (Λ : ℝ)⁻¹ * dist x y - Λ ≤ dist (f x) (f y) := by
  have hpos : 0 < (Λ : ℝ) := lt_of_lt_of_le (by norm_num) hΛ
  have hd : dist x y ≤ (Λ : ℝ) + Λ * dist (f x) (f y) + Λ := by
    calc
      dist x y ≤ dist x (g (f x)) + dist (g (f x)) (g (f y)) + dist (g (f y)) y :=
        dist_triangle4 _ _ _ _
      _ ≤ (Λ : ℝ) + Λ * dist (f x) (f y) + Λ :=
        add_le_add (add_le_add (by simpa only [dist_comm] using hinv x)
          (hg.dist_le_mul _ _)) (hinv y)
  have hdiv : (Λ : ℝ)⁻¹ * dist x y ≤ dist (f x) (f y) + 2 := by
    rw [← div_eq_inv_mul, div_le_iff₀ hpos]
    nlinarith only [hd]
  linarith only [hdiv, hΛ]

variable {G : Type*} [Group G] [MetricSpace G]

omit [Group G] in
/-- No separate lower-bound hypothesis is needed once the two Lipschitz
representatives have controlled inverse errors. -/
theorem lipschitzPairBounds_of_inverse_bounds
    {Λ : ℝ≥0} (hΛ : 2 ≤ (Λ : ℝ)) (p : C(G, G) × C(G, G))
    (hf : LipschitzWith Λ p.1) (hg : LipschitzWith Λ p.2)
    (hgf : ∀ x, dist (p.2 (p.1 x)) x ≤ Λ)
    (hfg : ∀ x, dist (p.1 (p.2 x)) x ≤ Λ) :
    LipschitzPairBounds G Λ p :=
  ⟨hf, hg, coarse_lower_of_lipschitz_inverse hΛ p.1 p.2 hg hgf,
    coarse_lower_of_lipschitz_inverse hΛ p.2 p.1 hf hfg, hgf, hfg⟩

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_PerturbedInversePairs
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesHomology _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Quantitative inverse bounds for bounded Lipschitz replacements -/

namespace PolycyclicRecognition

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

/-- Perturbing a coarse inverse pair preserves its inverse error with a
constant determined only by the original controls and perturbation radii. -/
theorem inverse_error_of_bounded_perturbations
    (f f' : X → Y) (g g' : Y → X)
    {Kg Cg Df Dg E : ℝ} (hKg : 0 ≤ Kg)
    (hg : ∀ y z, dist (g y) (g z) ≤ Kg * dist y z + Cg)
    (hfclose : ∀ x, dist (f' x) (f x) ≤ Df)
    (hgclose : ∀ y, dist (g' y) (g y) ≤ Dg)
    (hinv : ∀ x, dist (g (f x)) x ≤ E) (x : X) :
    dist (g' (f' x)) x ≤ Dg + (Kg * Df + Cg) + E := by
  calc
    dist (g' (f' x)) x ≤ dist (g' (f' x)) (g (f' x)) +
        dist (g (f' x)) (g (f x)) + dist (g (f x)) x := dist_triangle4 _ _ _ _
    _ ≤ Dg + (Kg * Df + Cg) + E := by
      exact add_le_add (add_le_add (hgclose _) ((hg _ _).trans
        (add_le_add (mul_le_mul_of_nonneg_left (hfclose x) hKg) le_rfl))) (hinv x)

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Lattices_UniformLatticeQuotient
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesHomology _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
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

/-- In a locally compact group, a compact coset quotient admits a compact
fundamental cover. The finite subcover consists of images of relatively
compact neighborhoods. -/
theorem isUniformLattice_of_compact_quotient [LocallyCompactSpace G]
    (Λ : Subgroup G) [DiscreteTopology Λ] [CompactSpace (G ⧸ Λ)] :
    IsUniformLattice Λ := by
  let q : G → G ⧸ Λ := QuotientGroup.mk
  choose K hK hneigh using fun x : G => exists_compact_mem_nhds x
  have hxK (x : G) : x ∈ interior (K x) := mem_interior_iff_mem_nhds.mpr (hneigh x)
  have hcover : (univ : Set (G ⧸ Λ)) ⊆ ⋃ x : G, q '' interior (K x) := by
    intro y _
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    exact mem_iUnion.mpr ⟨x, ⟨x, hxK x, rfl⟩⟩
  obtain ⟨F, hF⟩ := isCompact_univ.elim_finite_subcover
    (fun x : G => q '' interior (K x))
    (fun x => QuotientGroup.isOpenMap_coe _ isOpen_interior) hcover
  let L : Set G := ⋃ x ∈ F, K x
  have hL : IsCompact L := F.isCompact_biUnion (fun x _ => hK x)
  refine ⟨inferInstance, Inv.inv '' L, hL.image continuous_inv, ?_⟩
  intro g
  obtain ⟨x, hx, k, hk, hkg⟩ := mem_iUnion₂.mp (hF (mem_univ (q g⁻¹)))
  have hrel : k⁻¹ * g⁻¹ ∈ Λ := QuotientGroup.eq.mp hkg
  refine ⟨⟨g * k, ?_⟩, k⁻¹, ⟨k, ?_, rfl⟩, ?_⟩
  · simpa only [mul_inv_rev, inv_inv] using Λ.inv_mem hrel
  · exact mem_iUnion₂.mpr ⟨x, hx, interior_subset hk⟩
  · simp [mul_assoc]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Lattices_SolvableLatticeModel
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesHomology _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Solvable-lattice realization

K. Dekimpe, *Solvable Lie Algebras, Lie Groups and Polynomial Structures*,
Compositio Mathematica 121 (2000), 183–204, Theorem 4.1, p.199,
DOI 10.1023/A:1001738932743, gives a finite-index subgroup of a
polycyclic-by-finite group as a uniform lattice in a connected simply
connected solvable Lie group. We use only this consequence, omitting the
additional equality with the Fitting subgroup and omitting normality.

The realization predicate specifies a finite-dimensional smooth Lie structure
and a discrete lattice with compact coset quotient.
-/

noncomputable section

namespace PolycyclicRecognition

open scoped Manifold

attribute [instance] SimplyConnectedSolvableLieModel.normedAddCommGroup
  SimplyConnectedSolvableLieModel.normedSpace SimplyConnectedSolvableLieModel.finiteDimensional
  SimplyConnectedSolvableLieModel.topologicalSpace SimplyConnectedSolvableLieModel.chartedSpace
  SimplyConnectedSolvableLieModel.group SimplyConnectedSolvableLieModel.lieGroup
  SimplyConnectedSolvableLieModel.t2Space SimplyConnectedSolvableLieModel.simplyConnectedSpace
  SimplyConnectedSolvableLieModel.secondCountableTopology
  SimplyConnectedSolvableLieModel.solvable

/-- Restate the published realization using the equivalent compact-cover
definition used by the metric lattice lemmas. -/
theorem exists_uniform_solvable_lattice_of_virtuallyPolycyclic
    (dekimpe : DekimpeLatticeRealizationInput)
    (P : Type) [Group P] (hP : IsVirtuallyPolycyclic P) :
    ∃ Γ : Subgroup P, Γ.FiniteIndex ∧
      ∃ (S : SimplyConnectedSolvableLieModel) (Λ : Subgroup S.carrier),
        IsUniformLattice Λ ∧ Nonempty (Γ ≃* Λ) := by
  obtain ⟨Γ, hΓ, S, Λ, hdisc, hcompact, e⟩ := dekimpe P hP
  let := hdisc
  let := hcompact
  let : IsTopologicalGroup S.carrier :=
    topologicalGroup_of_lieGroup (𝓘(ℝ, S.modelSpace)) ⊤
  let : LocallyCompactSpace S.carrier :=
    Manifold.locallyCompact_of_finiteDimensional (𝓘(ℝ, S.modelSpace))
  exact ⟨Γ, hΓ, S, Λ, isUniformLattice_of_compact_quotient Λ, e⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_VirtualPolycyclicDuality
attribute [-instance] _root_.GeneratesNS.rho_g_FG _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesHomology _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_HeightKernelRecognition
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

namespace OAI

/-! # The finiteness and duality endgame for the actual height extension -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory ThompsonNonamenability
open scoped IsMulCommutative
variable {P G : Type} [Group P] [Group G] [Group.FG P] [Group.FG G]

theorem TypeFPInfinity.heightKernel_virtuallyPolycyclic
    (hG : TypeFPInfinity G) (e : GroupCoarseEquivalence P G)
    (hP : IsVirtuallyPolycyclic P) (M : InvariantMean G)
    (N : Subgroup G) [N.Normal] [IsMulCommutative (G ⧸ N)]
    (hQ : HasFiniteIntegralCohomologicalDimension (G ⧸ N))
    (hN : ∀ J : Subgroup G, J ≤ N → J.FG → Group.IsVirtuallyNilpotent J) :
    IsVirtuallyPolycyclic G := by
  let : Countable G := countable_of_group_fg G
  obtain ⟨d, hd⟩ := hG.heightKernel_rationalCoefficient_finite_dimension M N hQ hN
  exact virtuallyPolycyclic_of_coarse_rational_bounds e hP d
    (rationalGroup_dimension_le_of_integral_rational d hd)
    (hG.heightKernel_boundedFiniteSubgroupOrders M N hQ hN)
    (hG.heightKernel_virtualSolvable M N hQ hN)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_CoarseMultiplicity
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesHomology _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Uniform multiplicity of a coarse embedding

The recognition proof counts points in an intrinsic subgroup word ball using
the ambient group's fixed word metric. Its lower quasi-isometry bound gives a
uniform bound for the number of points mapping into a fixed-radius target ball.
No undistortion of the subgroup is used.
-/

namespace PolycyclicRecognition

theorem exists_uniform_ball_multiplicity
    {H X : Type*} [Group H] [MetricSpace H] [PseudoMetricSpace X]
    [IsIsometricSMul H H] (f : H → X)
    (hfinite : ∀ R : ℝ, (Metric.closedBall (1 : H) R).Finite)
    {K C r : ℝ} (hK : 0 ≤ K)
    (hlower : ∀ x y, dist x y ≤ K * dist (f x) (f y) + C) :
    ∃ M : ℕ, ∀ (c : X) (A : Finset H),
      (∀ h ∈ A, dist (f h) c ≤ r) → A.card ≤ M := by
  classical
  let R := K * (r + r) + C
  let ball := (hfinite R).toFinset
  refine ⟨ball.card, fun c A hA => ?_⟩
  by_cases hne : A.Nonempty
  · obtain ⟨a, ha⟩ := hne
    have hinj : Function.Injective (fun h : H => a⁻¹ * h) := fun _ _ h => mul_left_cancel h
    have himage : A.image (fun h => a⁻¹ * h) ⊆ ball := by
      intro h hh
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hh
      apply (hfinite R).mem_toFinset.mpr
      change dist (a⁻¹ * b) 1 ≤ R
      have hd : dist (f a) (f b) ≤ r + r := by
        exact (dist_triangle (f a) c (f b)).trans
          (add_le_add (hA a ha) (by simpa only [dist_comm] using hA b hb))
      have hs := (hlower a b).trans
        (add_le_add (mul_le_mul_of_nonneg_left hd hK) le_rfl)
      have heq : dist (a⁻¹ * b) 1 = dist a b := by
        rw [dist_comm]
        simpa only [mul_one, mul_inv_cancel_left] using
          (dist_mul_left a (1 : H) (a⁻¹ * b)).symm
      rwa [heq]
    simpa only [Finset.card_image_of_injective A hinj] using Finset.card_le_card himage
  · simp only [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.card_empty, Nat.zero_le]

/-- The same multiplicity constant works on any injectively parametrized
subset, in particular on a subgroup equipped with its intrinsic word metric. -/
theorem ball_multiplicity_comp_injective
    {H J X : Type*} [PseudoMetricSpace X] [DecidableEq H]
    (f : H → X) (ι : J → H) (hι : Function.Injective ι) (M : ℕ) (r : ℝ)
    (hM : ∀ (c : X) (A : Finset H),
      (∀ h ∈ A, dist (f h) c ≤ r) → A.card ≤ M) :
    ∀ (c : X) (A : Finset J), (∀ j ∈ A, dist (f (ι j)) c ≤ r) → A.card ≤ M := by
  intro c A hA
  have h := hM c (A.image ι) (by
    intro h hh
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hh
    exact hA j hj)
  simpa only [Finset.card_image_of_injective A hι] using h

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_BoundedPathGrowth
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesHomology _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# From bounded-height word paths to polynomial growth

Word chains and a uniform metric multiplicity bound turn polynomial packing
of bounded-height chains into polynomial growth. Gromov's theorem then gives
virtual nilpotence of the subgroup.
-/

namespace PolycyclicRecognition

variable {X W : Type*} [PseudoMetricSpace X] [NormedAddCommGroup W]

theorem boundedHeightChain_of_word {J : Type*} [Monoid J]
    (f : J → X) (π : X → W) (T : Finset J) {L M : ℝ}
    (hheight : ∀ j, ‖π (f j)‖ ≤ M)
    (hstep : ∀ j t, t ∈ T → dist (f j) (f (j * t)) ≤ L)
    (l : List J) (hl : ∀ t ∈ l, t ∈ T) (j : J) :
    BoundedHeightChain π L M l.length (f j) (f (j * l.prod)) := by
  induction l generalizing j with
  | nil => simpa using BoundedHeightChain.nil (L := L) (f j) (hheight j)
  | cons t l ih =>
    have ht := hl t (by simp)
    have htail : ∀ a ∈ l, a ∈ T := fun a ha => hl a (by simp [ha])
    simpa only [List.length_cons, List.prod_cons, mul_assoc] using
      BoundedHeightChain.cons (hheight j) (hstep j t ht) (ih htail (j * t))

theorem boundedHeightChain_of_mem_wordBall {J : Type*} [Monoid J] [DecidableEq J]
    (f : J → X) (π : X → W) (T : Finset J) {L M : ℝ}
    (hheight : ∀ j, ‖π (f j)‖ ≤ M)
    (hstep : ∀ j t, t ∈ T → dist (f j) (f (j * t)) ≤ L)
    {n : ℕ} {j : J} (hj : j ∈ wordBall T n) :
    ∃ m ≤ n, BoundedHeightChain π L M m (f 1) (f j) := by
  obtain ⟨l, hlen, hl, rfl⟩ := (mem_wordBall_iff T n j).mp hj
  exact ⟨l.length, hlen, by simpa using boundedHeightChain_of_word f π T hheight hstep l hl 1⟩

/-- A generating set, bounded steps and bounded multiplicity suffice for the
intrinsic growth argument. No metric or undistortion hypothesis on the domain
is required. -/
theorem virtuallyNilpotent_of_boundedHeight_steps
    {J : Type*} [Group J] [DecidableEq J] [DecidableEq X]
    (gromov : GromovPolynomialGrowthInput J)
    (f : J → X) (π : X → W) (packing : PolynomialBoundedChainPacking π)
    (T : Finset J) (hsymm : ∀ t ∈ T, t⁻¹ ∈ T)
    (hgen : Subgroup.closure (T : Set J) = ⊤)
    {L M : ℝ} (hL : 0 ≤ L) (hM : 0 ≤ M)
    (hheight : ∀ j, ‖π (f j)‖ ≤ M)
    (hstep : ∀ j t, t ∈ T → dist (f j) (f (j * t)) ≤ L)
    (N : ℕ) (hN : ∀ (c : X) (A : Finset J),
      (∀ j ∈ A, dist (f j) c ≤ 1) → A.card ≤ N) :
    Group.IsVirtuallyNilpotent J := by
  obtain ⟨A, b, centers, hcard, hcover⟩ := packing (f 1) L M hL hM
  apply virtuallyNilpotent_of_polynomial_cover gromov T hsymm hgen f A b N centers hcard
  · intro n j hj
    obtain ⟨m, hm, hchain⟩ := boundedHeightChain_of_mem_wordBall f π T hheight hstep hj
    exact hcover n m hm (f j) hchain
  · exact hN

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_TransferredAction
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesHomology _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Transferring translations across a coarse inverse pair

For maps `f : H → X` and `r : X → H`, the maps `x ↦ f (h * r x)` form the
uniform quasi-action used in Proposition `recognition-from-height` of the
manuscript. These estimates retain the errors of the coarse inverse pair and
require only the stated metric inequalities.
-/

namespace PolycyclicRecognition

universe u v

variable {H : Type u} [Group H]
variable {X : Type v}

variable [PseudoMetricSpace X]

/-- The transferred identity has the same error as `f ∘ r`. -/
theorem transferredMap_one_close (f : H → X) (r : X → H) (E' : ℝ)
    (hfr : ∀ x, dist (f (r x)) x ≤ E') (x : X) :
    dist (transferredMap f r 1 x) x ≤ E' := by
  simpa only [transferredMap, one_mul] using hfr x

variable [PseudoMetricSpace H]

/-- Both coarse upper inequalities give one upper inequality for every
transferred translation. The constants do not depend on the translating element. -/
theorem transferredMap_coarse_upper (f : H → X) (r : X → H)
    (hleft : ∀ h a b : H, dist (h * a) (h * b) = dist a b)
    (Kf Cf Kr Cr : ℝ) (hKf : 0 ≤ Kf)
    (hf : ∀ a b, dist (f a) (f b) ≤ Kf * dist a b + Cf)
    (hr : ∀ x y, dist (r x) (r y) ≤ Kr * dist x y + Cr)
    (h : H) (x y : X) :
    dist (transferredMap f r h x) (transferredMap f r h y) ≤
      (Kf * Kr) * dist x y + (Kf * Cr + Cf) := by
  calc
    dist (transferredMap f r h x) (transferredMap f r h y) ≤
        Kf * dist (h * r x) (h * r y) + Cf := hf _ _
    _ = Kf * dist (r x) (r y) + Cf := by rw [hleft]
    _ ≤ Kf * (Kr * dist x y + Cr) + Cf :=
      add_le_add (mul_le_mul_of_nonneg_left (hr x y) hKf) le_rfl
    _ = (Kf * Kr) * dist x y + (Kf * Cr + Cf) := by ring

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_AffineAction
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesHomology _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Exact linear parts of a uniformly affine height quasi-action

A bounded error on a surjective real height quotient forces the linear parts
of a quasi-action to multiply exactly. This is the algebraic argument in
Proposition `prop:recognition-from-height` of *Quasi-isometric recognition of
virtually polycyclic groups*, Section 11.
-/

noncomputable section

namespace PolycyclicRecognition

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

variable {H X : Type*} [Group H]

namespace HeightQuasiAction

variable (Q : HeightQuasiAction H X W)

/-- When only finitely many linear parts occur, the subgroup with trivial
linear part has finite index, as required in the recognition argument. -/
theorem finiteIndex_linear_kernel (hfinite : Set.Finite (Set.range Q.linear)) :
    Q.linearHom.ker.FiniteIndex := by
  have hrange : Finite Q.linearHom.range := by
    exact hfinite.to_subtype
  exact Subgroup.finiteIndex_ker Q.linearHom

/-- Restricting the height shifts to the subgroup with trivial linear part gives
an additive map up to a uniformly bounded error. -/
theorem translation_defect_le (h k : Q.linearHom.ker) :
    ‖Q.shift (h * k) - Q.shift h - Q.shift k‖ ≤ Q.translationDefect := by
  obtain ⟨x, hx⟩ := Q.height_surjective 0
  have hh : Q.linear (h : H) = 1 := h.property
  have hb := Q.affine_composition_bound (h : H) (k : H) x
  rw [hx, map_zero, map_zero, map_zero, hh] at hb
  change ‖Q.shift (h : H) + Q.shift (k : H) - Q.shift ((h : H) * k) + 0 - 0‖ ≤ _ at hb
  have heq : Q.shift (h * k) - Q.shift h - Q.shift k =
      -(Q.shift (h : H) + Q.shift (k : H) - Q.shift ((h : H) * k) + 0 - 0) := by
    abel
  rw [heq, norm_neg]
  exact hb

end HeightQuasiAction

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_AmenableCorrection
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesHomology _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.kernelAverage_one _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.smallCoefficientRealCoinvariantMean_one _root_.OAI.PolycyclicRecognition.smallCoefficientRealMean_one _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Correcting bounded height defects with an invariant mean

This is the averaging step in Proposition `recognition-from-height` of the
manuscript *Quasi-isometric recognition of virtually polycyclic groups*.
The mean is on the actual space of all bounded real functions. Neither the
height function itself nor its corrected homomorphism has to be bounded.
-/

noncomputable section

namespace PolycyclicRecognition

open ThompsonNonamenability
open scoped ENNReal

universe u v

variable {G : Type u} [Group G]

/-- Positivity of the mean preserves the uniform defect bound exactly. -/
theorem meanCorrection_dist_le (M : InvariantMean G) (s : G → ℝ) (D : ℝ)
    (hD : ∀ h k, |s (h * k) - s h - s k| ≤ D) (h : G) :
    |meanCorrection M s D hD h - s h| ≤ D := by
  have hlo := M.mono
    (f := (s h - D) • (1 : BoundedReal G))
    (g := boundedIncrement s D hD h) (fun x => by
      simp only [BoundedReal.smul_one_apply, boundedIncrement_apply]
      have hx := (abs_le.mp (hD h x)).1
      linarith)
  have hhi := M.mono
    (f := boundedIncrement s D hD h)
    (g := (s h + D) • (1 : BoundedReal G)) (fun x => by
      simp only [BoundedReal.smul_one_apply, boundedIncrement_apply]
      have hx := (abs_le.mp (hD h x)).2
      linarith)
  rw [M.map_const] at hlo hhi
  exact abs_le.mpr ⟨by unfold meanCorrection; linarith,
    by unfold meanCorrection; linarith⟩

/-- The correction remains within the original defect bound in the supremum norm. -/
theorem vectorMeanCorrection_dist_le {ι : Type v} [Fintype ι]
    (M : InvariantMean G) (s : G → ι → ℝ) (D : ℝ)
    (hD : ∀ h k, ‖s (h * k) - s h - s k‖ ≤ D) (h : G) :
    ‖vectorMeanCorrection M s D hD h - s h‖ ≤ D := by
  have hnonneg : 0 ≤ D := (norm_nonneg _).trans (hD 1 1)
  apply (pi_norm_le_iff_of_nonneg hnonneg).2
  intro i
  simpa only [Pi.sub_apply, Real.norm_eq_abs, vectorMeanCorrection] using
    meanCorrection_dist_le M (fun k => s k i) D (coordinate_defect_le s D hD i) h

/-- A height map of uniformly bounded additive defect on an amenable group is uniformly
close to a homomorphism to a finite-dimensional real vector space. -/
theorem exists_correctedHom {ι : Type v} [Fintype ι]
    (M : InvariantMean G) (s : G → ι → ℝ) (D : ℝ)
    (hD : ∀ h k, ‖s (h * k) - s h - s k‖ ≤ D) :
    ∃ τ : G →* Multiplicative (ι → ℝ), ∀ h, ‖(τ h).toAdd - s h‖ ≤ D :=
  ⟨correctedHom M s D hD, vectorMeanCorrection_dist_le M s D hD⟩

/-- Transfer the finite-coordinate correction through a continuous linear equivalence.
The resulting bound records the change of norm explicitly. -/
theorem exists_correctedHom_of_equiv {W : Type*} [NormedAddCommGroup W]
    [NormedSpace ℝ W] {ι : Type v} [Fintype ι]
    (e : W ≃L[ℝ] (ι → ℝ)) (M : InvariantMean G) (s : G → W) (D : ℝ)
    (hD : ∀ h k, ‖s (h * k) - s h - s k‖ ≤ D) :
    ∃ τ : G →* Multiplicative W,
      ∀ h, ‖(τ h).toAdd - s h‖ ≤
        ‖e.symm.toContinuousLinearMap‖ * (‖e.toContinuousLinearMap‖ * D) := by
  have heD : ∀ h k, ‖e (s (h * k)) - e (s h) - e (s k)‖ ≤
      ‖e.toContinuousLinearMap‖ * D := by
    intro h k
    calc
      ‖e (s (h * k)) - e (s h) - e (s k)‖ =
          ‖e (s (h * k) - s h - s k)‖ := by rw [map_sub, map_sub]
      _ ≤ ‖e.toContinuousLinearMap‖ * ‖s (h * k) - s h - s k‖ :=
        e.toContinuousLinearMap.le_opNorm _
      _ ≤ ‖e.toContinuousLinearMap‖ * D :=
        mul_le_mul_of_nonneg_left (hD h k) (norm_nonneg _)
  obtain ⟨τ', hτ'⟩ := exists_correctedHom M (fun h => e (s h))
    (‖e.toContinuousLinearMap‖ * D) heD
  let τ : G →* Multiplicative W :=
    { toFun := fun h => Multiplicative.ofAdd (e.symm (τ' h).toAdd)
      map_one' := by simp
      map_mul' := fun h k => by
        change e.symm (τ' (h * k)).toAdd = e.symm (τ' h).toAdd + e.symm (τ' k).toAdd
        rw [map_mul]
        exact map_add e.symm _ _ }
  refine ⟨τ, fun h => ?_⟩
  change ‖e.symm (τ' h).toAdd - s h‖ ≤ _
  calc
    ‖e.symm (τ' h).toAdd - s h‖ = ‖e.symm ((τ' h).toAdd - e (s h))‖ := by
      rw [map_sub, e.symm_apply_apply]
    _ ≤ ‖e.symm.toContinuousLinearMap‖ * ‖(τ' h).toAdd - e (s h)‖ :=
      e.symm.toContinuousLinearMap.le_opNorm _
    _ ≤ ‖e.symm.toContinuousLinearMap‖ * (‖e.toContinuousLinearMap‖ * D) :=
      mul_le_mul_of_nonneg_left (hτ' h) (norm_nonneg _)

/-- On any finite-dimensional real normed space, a height map of uniformly
bounded additive defect is uniformly close to a homomorphism. -/
theorem exists_finiteDimensional_correctedHom {W : Type*} [NormedAddCommGroup W]
    [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    (M : InvariantMean G) (s : G → W) (D : ℝ)
    (hD : ∀ h k, ‖s (h * k) - s h - s k‖ ≤ D) :
    ∃ (τ : G →* Multiplicative W) (B : ℝ), 0 ≤ B ∧
      ∀ h, ‖(τ h).toAdd - s h‖ ≤ B := by
  let e := (Module.finBasis ℝ W).equivFunL
  obtain ⟨τ, hτ⟩ := exists_correctedHom_of_equiv e M s D hD
  have hD0 : 0 ≤ D := (norm_nonneg _).trans (hD 1 1)
  exact ⟨τ, ‖e.symm.toContinuousLinearMap‖ * (‖e.toContinuousLinearMap‖ * D),
    mul_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg _) hD0), hτ⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_HeightHomomorphism
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesHomology _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The corrected height homomorphism

An amenable group acting with bounded height error and finitely many linear
height parts has a normal finite-index subgroup with a genuine homomorphism
to the height space at bounded distance from the height shifts. In particular
the shifts are uniformly bounded on the kernel. The construction combines
the exact linear action with an invariant-mean correction.
-/

noncomputable section

namespace PolycyclicRecognition

open ThompsonNonamenability

variable {H X W : Type*} [Group H] [NormedAddCommGroup W] [NormedSpace ℝ W]

namespace HeightQuasiAction

/-- The affine shifts restricted to the linear kernel are at bounded distance
from an actual height homomorphism. Amenability is expressed by an invariant
mean on all bounded functions on the original group. -/
theorem exists_correctedHeight [FiniteDimensional ℝ W] (Q : HeightQuasiAction H X W) (M : InvariantMean H) :
    ∃ (τ : Q.linearHom.ker →* Multiplicative W) (B : ℝ),
      0 ≤ B ∧ ∀ h, ‖(τ h).toAdd - Q.shift h‖ ≤ B := by
  exact exists_finiteDimensional_correctedHom
    (subgroupInvariantMean M Q.linearHom.ker) (fun h => Q.shift h)
    Q.translationDefect Q.translation_defect_le

/-- On the kernel of any such correction, the original height shifts are bounded.
The kernel is not assumed to be finitely generated. -/
theorem shift_bounded_on_kernel (Q : HeightQuasiAction H X W)
    (τ : Q.linearHom.ker →* Multiplicative W) (B : ℝ)
    (hτ : ∀ h, ‖(τ h).toAdd - Q.shift h‖ ≤ B)
    (h : τ.ker) : ‖Q.shift (h : Q.linearHom.ker)‖ ≤ B := by
  have hh : τ (h : Q.linearHom.ker) = 1 := h.property
  have hb := hτ (h : Q.linearHom.ker)
  rw [hh] at hb
  change ‖(0 : W) - Q.shift (h : Q.linearHom.ker)‖ ≤ B at hb
  simpa only [zero_sub, norm_neg] using hb

/-- The finite-index, normal-subgroup and bounded-kernel conclusions of the
algebraic part of the recognition argument. -/
theorem exists_normal_finiteIndex_height [FiniteDimensional ℝ W] (Q : HeightQuasiAction H X W)
    (M : InvariantMean H) (hfinite : Set.Finite (Set.range Q.linear)) :
    ∃ (H₀ : Subgroup H), H₀.Normal ∧ H₀.FiniteIndex ∧
      ∃ (τ : H₀ →* Multiplicative W) (B : ℝ), 0 ≤ B ∧
        (∀ h : H₀, ‖(τ h).toAdd - Q.shift h‖ ≤ B) ∧
        (∀ h : τ.ker, ‖Q.shift (h : H₀)‖ ≤ B) := by
  obtain ⟨τ, B, hB, hτ⟩ := Q.exists_correctedHeight M
  refine ⟨Q.linearHom.ker, inferInstance, Q.finiteIndex_linear_kernel hfinite,
    τ, B, hB, hτ, ?_⟩
  exact Q.shift_bounded_on_kernel τ B hτ

end HeightQuasiAction

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_TransferredHeight
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesHomology _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A height homomorphism from the transferred translation action

Coarse maps and a Lipschitz height map define a height quasi-action. An affine
height bound permits invariant-mean correction to a genuine homomorphism.
-/

noncomputable section

namespace PolycyclicRecognition
namespace TransferredHeight

open ThompsonNonamenability

universe u v w

variable {H : Type u} [Group H] [PseudoMetricSpace H]
variable {X : Type v} [PseudoMetricSpace X]
variable {W : Type w} [NormedAddCommGroup W]

variable [NormedSpace ℝ W]

/-- Amenability and finitely many affine linear parts produce a normal subgroup
of finite index and a genuine height homomorphism. Its kernel has uniformly
bounded original height. The geometric affine estimate is still a hypothesis. -/
theorem exists_normal_finiteIndex_height [FiniteDimensional ℝ W]
    (f : H → X) (r : X → H) (π : X → W)
    (A : H → W ≃L[ℝ] W) (hπsurj : Function.Surjective π)
    (hleft : ∀ h a b : H, dist (h * a) (h * b) = dist a b)
    (L K C E B : ℝ) (hL : 0 ≤ L) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hE : 0 ≤ E) (hB : 0 ≤ B)
    (hπ : ∀ x y, ‖π x - π y‖ ≤ L * dist x y)
    (hf : ∀ a b, dist (f a) (f b) ≤ K * dist a b + C)
    (hrf : ∀ a, dist (r (f a)) a ≤ E)
    (haffine : ∀ h x, ‖π (transferredMap f r h x) - (π (f h) + A h (π x))‖ ≤ B)
    (M : InvariantMean H) (hfinite : Set.Finite (Set.range A)) :
    ∃ (H₀ : Subgroup H), H₀.Normal ∧ H₀.FiniteIndex ∧
      ∃ (τ : H₀ →* Multiplicative W) (D : ℝ), 0 ≤ D ∧
        (∀ h : H₀, ‖(τ h).toAdd - π (f h)‖ ≤ D) ∧
        (∀ h : τ.ker, ‖π (f (h : H₀))‖ ≤ D) := by
  let Q := quasiAction f r π A hπsurj hleft L K C E B hL hK hC hE hB hπ hf hrf haffine
  exact Q.exists_normal_finiteIndex_height M hfinite

end TransferredHeight
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_RecognitionFromHeight
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesHomology _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Recognition from a geometric height estimate

Corrected height bounds control intrinsic word growth of finitely generated
subgroups of its kernel. Polynomial bounded-height chain packing gives
elementary amenability, to which the finiteness and duality theorems apply.
-/

noncomputable section

namespace PolycyclicRecognition

universe u v

variable {H : Type u} [Group H] [MetricSpace H] [IsIsometricSMul H H]
variable {X : Type v} [PseudoMetricSpace X]
variable {W : Type u} [NormedAddCommGroup W]

/-- Intrinsic polynomial growth for an injectively parametrized subgroup of the
ambient coarse source. All metric estimates use the ambient source metric. -/
theorem virtuallyNilpotent_of_injective_boundedHeight
    {J : Type u} [Group J] [Group.FG J] [DecidableEq J] [DecidableEq X]
    (gromov : GromovPolynomialGrowthInput J)
    (ι : J →* H) (hι : Function.Injective ι)
    (f : H → X) (π : X → W) (packing : PolynomialBoundedChainPacking π)
    (hfinite : ∀ R : ℝ, (Metric.closedBall (1 : H) R).Finite)
    {K C K' C' M : ℝ} (hK : 0 ≤ K) (hC : 0 ≤ C) (hK' : 0 ≤ K') (hM : 0 ≤ M)
    (hupper : ∀ x y, dist (f x) (f y) ≤ K * dist x y + C)
    (hlower : ∀ x y, dist x y ≤ K' * dist (f x) (f y) + C')
    (hheight : ∀ j, ‖π (f (ι j))‖ ≤ M) : Group.IsVirtuallyNilpotent J := by
  classical
  obtain ⟨T, hsymm, hgen⟩ := exists_symmetric_finite_generating_set (J := J)
  let R : ℝ := ∑ t ∈ T, dist (1 : H) (ι t)
  have hR : 0 ≤ R := Finset.sum_nonneg fun _ _ => dist_nonneg
  have hRbound (t : J) (ht : t ∈ T) : dist (1 : H) (ι t) ≤ R :=
    Finset.single_le_sum (f := fun t : J => dist 1 (ι t)) (fun _ _ => dist_nonneg) ht
  have hstep (j t : J) (ht : t ∈ T) :
      dist (f (ι j)) (f (ι (j * t))) ≤ K * R + C := by
    apply (hupper (ι j) (ι (j * t))).trans
    have hd : dist (ι j) (ι (j * t)) = dist (1 : H) (ι t) := by
      rw [map_mul]
      simpa only [mul_one] using dist_mul_left (ι j) (1 : H) (ι t)
    rw [hd]
    exact add_le_add (mul_le_mul_of_nonneg_left (hRbound t ht) hK) le_rfl
  obtain ⟨N, hN⟩ := exists_uniform_ball_multiplicity (r := 1) f hfinite hK' hlower
  exact virtuallyNilpotent_of_boundedHeight_steps gromov (f ∘ ι) π packing T hsymm hgen
    (add_nonneg (mul_nonneg hK hR) hC) hM hheight hstep N
    (ball_multiplicity_comp_injective f ι hι N 1 hN)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CorrectedHeightRecognition
attribute [-instance] _root_.GeneratesNS.rho_g_FG _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

namespace OAI

/-! # Corrected-height recognition without the KMN input -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory ThompsonNonamenability
open scoped IsMulCommutative

instance height_quotient_commutative
    {G W : Type} [Group G] [AddCommGroup W] (τ : G →* Multiplicative W) :
    IsMulCommutative (G ⧸ τ.ker) := by
  let f : (G ⧸ τ.ker) →* Multiplicative W :=
    τ.range.subtype.comp (QuotientGroup.quotientKerEquivRange τ).toMonoidHom
  have hf : Function.Injective f :=
    Subtype.val_injective.comp (QuotientGroup.quotientKerEquivRange τ).injective
  exact ⟨⟨fun a b => hf (by simp only [map_mul, mul_comm])⟩⟩

theorem height_quotient_finiteDimension
    {G W : Type} [Group G] [Group.FG G]
    [NormedAddCommGroup W] [NormedSpace ℝ W] (τ : G →* Multiplicative W) :
    HasFiniteIntegralCohomologicalDimension (G ⧸ τ.ker) := by
  let f : (G ⧸ τ.ker) →* Multiplicative W :=
    τ.range.subtype.comp (QuotientGroup.quotientKerEquivRange τ).toMonoidHom
  have hf : Function.Injective f :=
    Subtype.val_injective.comp (QuotientGroup.quotientKerEquivRange τ).injective
  let : IsAddTorsionFree W := IsAddTorsionFree.of_isTorsionFree ℝ W
  have ht : HasNoNontrivialTorsion (Multiplicative W) := by
    intro a n hn ha
    exact (pow_left_injective hn) (ha.trans (one_pow n).symm)
  obtain ⟨n, hn⟩ := nilpotent_poincareDuality_of_finitelyGenerated_torsionFree
    (ht.of_injective f hf)
  exact hn.finiteCohomologicalDimension _

theorem virtuallyPolycyclic_of_corrected_height_proved
    {P G X W : Type} [Group P] [Group G] [Group.FG P] [Group.FG G]
    [MetricSpace G] [IsIsometricSMul G G] [PseudoMetricSpace X] [DecidableEq X]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (e : GroupCoarseEquivalence P G) (hP : IsVirtuallyPolycyclic P)
    (M : InvariantMean G)
    (H : Subgroup G) [H.FiniteIndex] (τ : H →* Multiplicative W)
    (gromov : ∀ (J : Subgroup τ.ker) [DecidableEq J], GromovPolynomialGrowthInput J)
    (f : G → X) (π : X → W) (packing : PolynomialBoundedChainPacking π)
    (hfinite : ∀ R : ℝ, (Metric.closedBall (1 : G) R).Finite)
    {K C K' C' D : ℝ} (hK : 0 ≤ K) (hC : 0 ≤ C) (hK' : 0 ≤ K') (hD : 0 ≤ D)
    (hupper : ∀ x y, dist (f x) (f y) ≤ K * dist x y + C)
    (hlower : ∀ x y, dist x y ≤ K' * dist (f x) (f y) + C')
    (hheight : ∀ h : H, ‖(τ h).toAdd - π (f h)‖ ≤ D) :
    IsVirtuallyPolycyclic G := by
  classical
  obtain ⟨K₀, Γ, _, _, hΓ, ⟨eΓ⟩, n, hΓPD⟩ :=
    exists_coarse_poincareDuality_comparison_proved P G hP e
  let := hΓ
  have hG : TypeFPInfinity G :=
    fun i => liFinitenessInput Γ G eΓ i (hΓPD.typeFPInfinity Γ i)
  have hH : TypeFPInfinity H := fun i => (hG i).finiteIndex_subgroup H
  have hlocal : ∀ J : Subgroup H, J ≤ τ.ker → J.FG → Group.IsVirtuallyNilpotent J := by
    intro J hJ hfg
    let A := J.subgroupOf τ.ker
    let j := Subgroup.subgroupOfEquivOfLe hJ
    let : Group.FG A := @Group.fg_of_surjective _ _ _ _
      ((Group.fg_iff_subgroup_fg J).mpr hfg) j.symm.toMonoidHom j.symm.surjective
    let ι : A →* G := H.subtype.comp (τ.ker.subtype.comp A.subtype)
    have hι : Function.Injective ι :=
      Subtype.val_injective.comp (Subtype.val_injective.comp Subtype.val_injective)
    have hA : Group.IsVirtuallyNilpotent A := by
      apply virtuallyNilpotent_of_injective_boundedHeight (gromov A) ι hι f π packing
        hfinite hK hC hK' hD hupper hlower
      intro a
      have he := hheight a.val.val
      rw [a.val.property] at he
      change ‖(0 : W) - π (f (ι a))‖ ≤ D at he
      simpa only [zero_sub, norm_neg] using he
    exact virtuallyNilpotent_of_mulEquiv j hA
  have hpoly : IsVirtuallyPolycyclic H := hH.heightKernel_virtuallyPolycyclic
    (e.trans (finiteIndexCoarseEquivalence H).symm) hP (subgroupInvariantMean M H)
    τ.ker (height_quotient_finiteDimension τ) hlocal
  obtain ⟨V, hVi, hVpoly⟩ := hpoly
  let := hVi
  exact ⟨V.map H.subtype, ⟨by
    rw [Subgroup.index_map_subtype]
    exact mul_ne_zero hVi.index_ne_zero (Subgroup.FiniteIndex.index_ne_zero (H := H))⟩,
    hVpoly.of_surjective (V.equivMapOfInjective H.subtype Subtype.val_injective).toMonoidHom
      (V.equivMapOfInjective H.subtype Subtype.val_injective).surjective⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_MeasurePacking
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.height_quotient_commutative _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesHomology _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Counting separated endpoints using Haar volume

Disjoint fixed-radius balls around separated endpoints have the same positive
Haar mass. A polynomial-volume region containing their thickening therefore
gives a polynomial cardinal bound. This is the counting step of the path
packing lemma, separated from its Lie-coordinate estimate.
-/

namespace PolycyclicRecognition

open MeasureTheory MeasureTheory.Measure Metric Set
open scoped ENNReal

variable {G : Type*} [Group G] [MetricSpace G] [MeasurableSpace G]
  [BorelSpace G] [MeasurableMul G] [IsIsometricSMul G G]

omit [BorelSpace G] in
theorem measure_ball_eq_identity (μ : Measure G) [IsMulLeftInvariant μ]
    (x : G) (r : ℝ) : μ (ball x r) = μ (ball (1 : G) r) := by
  have h := measure_preimage_mul μ x (ball x r)
  rw [preimage_mul_left_ball, inv_mul_cancel] at h
  exact h.symm

/-- The Haar volume of a thickening bounds the number of separated centers. -/
theorem separated_card_mul_ball_le (μ : Measure G) [IsMulLeftInvariant μ]
    (s : Finset G) (r : ℝ) (region : Set G)
    (hsep : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → r + r ≤ dist x y)
    (hthick : ∀ x ∈ s, ball x r ⊆ region) :
    (s.card : ℝ≥0∞) * μ (ball (1 : G) r) ≤ μ region := by
  classical
  have hd : Set.Pairwise (s : Set G) (fun x y => Disjoint (ball x r) (ball y r)) := by
    intro x hx y hy hxy
    exact ball_disjoint_ball (hsep x hx y hy hxy)
  calc
    (s.card : ℝ≥0∞) * μ (ball (1 : G) r) = μ (⋃ x ∈ s, ball x r) := by
      rw [measure_biUnion_finset hd (fun x _ => measurableSet_ball)]
      simp only [measure_ball_eq_identity, Finset.sum_const, nsmul_eq_mul]
    _ ≤ μ region := measure_mono (iUnion₂_subset hthick)

/-- The same maximal-packing argument applies to arbitrary endpoint sets. A
bound on their finite separated subsets already supplies a finite net; no
measurability or compactness of the endpoint set is needed. -/
theorem finite_separated_cover_set_of_bound {X : Type*} [PseudoMetricSpace X]
    (S : Set X) {r : ℝ} (hr : 0 ≤ r) (N : ℕ)
    (hbound : ∀ t : Finset X, (↑t : Set X) ⊆ S →
      (∀ x ∈ t, ∀ y ∈ t, x ≠ y → r < dist x y) → t.card ≤ N) :
    ∃ t : Finset X, (↑t : Set X) ⊆ S ∧
      (∀ x ∈ t, ∀ y ∈ t, x ≠ y → r < dist x y) ∧ t.card ≤ N ∧
      ∀ x ∈ S, ∃ y ∈ t, dist x y ≤ r := by
  classical
  let P (k : ℕ) := ∃ t : Finset X, (↑t : Set X) ⊆ S ∧
    (∀ x ∈ t, ∀ y ∈ t, x ≠ y → r < dist x y) ∧ t.card = k
  have hP0 : P 0 := ⟨∅, by simp, by simp, by simp⟩
  obtain ⟨t, hts, hsep, hcard⟩ := Nat.findGreatest_spec (Nat.zero_le N) hP0
  have hmax (u : Finset X) (hu : (↑u : Set X) ⊆ S)
      (husep : ∀ x ∈ u, ∀ y ∈ u, x ≠ y → r < dist x y) : u.card ≤ t.card := by
    rw [hcard]
    exact Nat.le_findGreatest (hbound u hu husep) ⟨u, hu, husep, rfl⟩
  refine ⟨t, hts, hsep, hbound t hts hsep, ?_⟩
  intro x hx
  by_contra hno
  have hfar : ∀ y ∈ t, r < dist x y := by
    intro y hy
    exact lt_of_not_ge (fun h => hno ⟨y, hy, h⟩)
  have hxt : x ∉ t := by
    intro hxt
    exact (not_lt_of_ge hr) (by simpa only [dist_self] using hfar x hxt)
  have hins : (↑(insert x t) : Set X) ⊆ S := by
    intro y hy
    rcases Finset.mem_insert.mp hy with hxy | hyt
    · exact hxy ▸ hx
    · exact hts hyt
  have hsepins : ∀ a ∈ insert x t, ∀ b ∈ insert x t, a ≠ b → r < dist a b := by
    intro a ha b hb hab
    rcases Finset.mem_insert.mp ha with hax | hat
    · subst a
      rcases Finset.mem_insert.mp hb with hbx | hbt
      · exact (hab hbx.symm).elim
      · exact hfar b hbt
    · rcases Finset.mem_insert.mp hb with hbx | hbt
      · subst b
        simpa only [dist_comm] using hfar a hat
      · exact hsep a hat b hbt hab
  have h := hmax (insert x t) hins hsepins
  rw [Finset.card_insert_of_notMem hxt] at h
  omega

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ExponentialHeightKernel
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.height_quotient_commutative _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesHomology _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The group height kernel from exponential coordinates

A representation strictly upper triangular on the canonical Lie kernel is
unipotent on the group height kernel. Thus the already proved chain-packing
theorem applies without a separate group-kernel hypothesis.
-/

noncomputable section

namespace PolycyclicRecognition

open PositiveTriangular
open scoped Matrix.Norms.Operator

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L]
  {a : ℕ} (T : TriangularAdjoint L a)
  {G W : Type*} [Group G] [NormedAddCommGroup W] [NormedSpace ℝ W]
  (q : HeightSpace T.character ≃ₗ[ℝ] W)
  (Exp : L → G) (π : G →* Multiplicative W)
  (hπExp : ∀ x, (π (Exp x)).toAdd = q (heightProjection T.character x))

include T q Exp hπExp

theorem integrated_height_surjective : Function.Surjective π := by
  intro w
  obtain ⟨x, hx⟩ := heightProjection_surjective T.character (q.symm w.toAdd)
  refine ⟨Exp x, ?_⟩
  apply Multiplicative.ext
  rw [hπExp, hx, q.apply_symm_apply]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_ApproximateInvariantMean
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.height_quotient_commutative _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesHomology _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.boundedFunctionPull_apply _root_.OAI.PolycyclicRecognition.boundedFunctionPull_one _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.kernelAverage_one _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.smallCoefficientBoundedReal_one _root_.OAI.PolycyclicRecognition.subgroupFunctionExtension_apply _root_.OAI.PolycyclicRecognition.subgroupFunctionExtension_one _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Constructing an invariant mean from approximate finite averages

Compactness is applied to the actual bounded-function space. The conclusion
is the invariant mean used by the height-correction argument, not a separate
amenability predicate.
-/

noncomputable section

namespace PolycyclicRecognition

open ThompsonNonamenability Filter Set
open scoped Topology ENNReal

variable {G : Type*} [Group G]

omit [Group G] in
/-- Positivity and normalization control every bounded real function. -/
theorem positive_normalized_bound
    (L : BoundedReal G →ₗ[ℝ] ℝ)
    (hpos : ∀ f, (∀ g, 0 ≤ f g) → 0 ≤ L f) (hone : L 1 = 1)
    (f : BoundedReal G) : |L f| ≤ ‖f‖ := by
  have hmono {a b : BoundedReal G} (h : ∀ g, a g ≤ b g) : L a ≤ L b := by
    have hh := hpos (b - a) (fun g => sub_nonneg.mpr (h g))
    rw [map_sub] at hh
    exact sub_nonneg.mp hh
  have hlo := hmono (a := (-‖f‖) • (1 : BoundedReal G)) (b := f) (fun g => by
    have hh := lp.norm_apply_le_norm ENNReal.top_ne_zero f g
    simp only [BoundedReal.smul_one_apply]
    exact (abs_le.mp (by simpa only [Real.norm_eq_abs] using hh)).1)
  have hhi := hmono (a := f) (b := ‖f‖ • (1 : BoundedReal G)) (fun g => by
    have hh := lp.norm_apply_le_norm ENNReal.top_ne_zero f g
    simp only [BoundedReal.smul_one_apply]
    exact (abs_le.mp (by simpa only [Real.norm_eq_abs] using hh)).2)
  simp only [map_smul, smul_eq_mul, hone, mul_one] at hlo hhi
  exact abs_le.mpr ⟨hlo, hhi⟩

/-- Compactness simultaneously preserves positivity, normalization and
vanishing translation defects for any prescribed set of group elements. -/
theorem exists_partially_invariantMean_of_approximate
    {ι : Type*} {l : Filter ι} [l.NeBot]
    (L : ι → BoundedReal G →ₗ[ℝ] ℝ)
    (hpos : ∀ i f, (∀ g, 0 ≤ f g) → 0 ≤ L i f)
    (hone : ∀ i, L i 1 = 1)
    (S : Set G)
    (hdefect : ∀ g ∈ S, ∀ f, Tendsto (fun i => L i (leftPull g f) - L i f) l (𝓝 0)) :
    ∃ M : BoundedReal G →ₗ[ℝ] ℝ,
      (∀ f, (∀ g, 0 ≤ f g) → 0 ≤ M f) ∧ M 1 = 1 ∧
        ∀ g ∈ S, ∀ f, M (leftPull g f) = M f := by
  let K (f : BoundedReal G) := Icc (-‖f‖) ‖f‖
  have (f : BoundedReal G) : CompactSpace (K f) :=
    isCompact_iff_compactSpace.mp (isCompact_Icc : IsCompact (K f))
  let Z := (f : BoundedReal G) → K f
  let p : ι → Z := fun i f => ⟨L i f,
    abs_le.mp (positive_normalized_bound (L i) (hpos i) (hone i) f)⟩
  obtain ⟨z, _, hz⟩ := (isCompact_univ : IsCompact (univ : Set Z)).exists_mapClusterPt
    (show Filter.map p l ≤ 𝓟 univ by simp)
  obtain ⟨u, hul, huz⟩ := mapClusterPt_iff_ultrafilter.mp hz
  have hlim (f : BoundedReal G) : Tendsto (fun i => L i f) u (𝓝 (z f).val) := by
    exact (continuous_subtype_val.comp (continuous_apply f)).tendsto z |>.comp huz
  let M : BoundedReal G →ₗ[ℝ] ℝ :=
    { toFun := fun f => (z f).val
      map_add' := by
        intro f g
        apply tendsto_nhds_unique (hlim (f + g))
        simpa only [map_add] using (hlim f).add (hlim g)
      map_smul' := by
        intro r f
        apply tendsto_nhds_unique (hlim (r • f))
        simpa only [map_smul, smul_eq_mul, RingHom.id_apply] using (hlim f).const_mul r }
  refine ⟨M, ?_, ?_, ?_⟩
  · intro f hf
    exact ge_of_tendsto (hlim f) (Eventually.of_forall (fun i => hpos i f hf))
  · change (z 1).val = 1
    apply tendsto_nhds_unique (hlim 1)
    simpa only [hone] using (tendsto_const_nhds : Tendsto (fun _ : ι => (1 : ℝ)) u (𝓝 1))
  · intro g hg f
    change (z (leftPull g f)).val = (z f).val
    apply sub_eq_zero.mp
    exact tendsto_nhds_unique ((hlim (leftPull g f)).sub (hlim f))
      ((hdefect g hg f).mono_left hul)

/-- A nontrivial net of positive normalized linear averages whose translation
defects tend to zero yields the actual invariant mean used for height correction. -/
theorem exists_invariantMean_of_approximate
    {ι : Type*} {l : Filter ι} [l.NeBot]
    (L : ι → BoundedReal G →ₗ[ℝ] ℝ)
    (hpos : ∀ i f, (∀ g, 0 ≤ f g) → 0 ≤ L i f)
    (hone : ∀ i, L i 1 = 1)
    (hdefect : ∀ g f, Tendsto (fun i => L i (leftPull g f) - L i f) l (𝓝 0)) :
    Nonempty (InvariantMean G) := by
  obtain ⟨M, hM, hMone, hMinv⟩ := exists_partially_invariantMean_of_approximate
    (l := l) L hpos hone univ (fun g _ => hdefect g)
  exact ⟨⟨M, hM, hMone, fun g => hMinv g (mem_univ g)⟩⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.Thompson_FiniteAverage
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.height_quotient_commutative _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesHomology _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Real finite averages and left-translation cancellation

These are literal finite sums. The translation estimate cancels the common
intersection of the two finite sets, and the function bound is global. No
invariant mean, support assumption, or limiting average is used.
-/

noncomputable section

universe uα uι uG

namespace ThompsonNonamenability

open scoped BigOperators symmDiff

variable {α : Type uα} {ι : Type uι}

theorem realAvg_eq_sum_div (A : Finset α) (f : α → ℝ) :
    realAvg A f = (∑ x ∈ A, f x) / (A.card : ℝ) := by
  simp only [realAvg, div_eq_mul_inv, mul_comm]

theorem realAvg_sub (A : Finset α) (f g : α → ℝ) :
    realAvg A (fun x => f x - g x) = realAvg A f - realAvg A g := by
  simp only [realAvg, Finset.sum_sub_distrib, mul_sub]

theorem realAvg_mul_const (A : Finset α) (f : α → ℝ) (c : ℝ) :
    realAvg A (fun x => f x * c) = realAvg A f * c := by
  simp only [realAvg, ← Finset.sum_mul, mul_assoc]

section Cancellation

variable [DecidableEq α]

/-- The exact common-intersection cancellation, before any estimate. -/
theorem sum_sub_eq_sdiff_sub (U V : Finset α) (f : α → ℝ) :
    (∑ x ∈ U, f x) - ∑ x ∈ V, f x =
      (∑ x ∈ U \ V, f x) - ∑ x ∈ V \ U, f x :=
  (Finset.sum_sdiff_sub_sum_sdiff (s₁ := V) (s₂ := U) (f := f)).symm

theorem card_symmDiff_eq_sdiff_add (U V : Finset α) :
    (U ∆ V).card = (U \ V).card + (V \ U).card := by
  change ((U \ V) ∪ (V \ U)).card = _
  exact Finset.card_union_of_disjoint disjoint_sdiff_sdiff

omit [DecidableEq α] in
theorem abs_sum_le_card [DecidableEq α] (A : Finset α) (f : α → ℝ) (hf : ∀ x, |f x| ≤ 1) :
    |∑ x ∈ A, f x| ≤ (A.card : ℝ) := by
  calc
    |∑ x ∈ A, f x| ≤ ∑ x ∈ A, |f x| := Finset.abs_sum_le_sum_abs f A
    _ ≤ ∑ _x ∈ A, (1 : ℝ) := Finset.sum_le_sum (fun x _ => hf x)
    _ = (A.card : ℝ) := by simp

/-- The full symmetric difference counts both residual pieces exactly once. -/
theorem abs_sum_sub_le_card_symmDiff (U V : Finset α) (f : α → ℝ)
    (hf : ∀ x, |f x| ≤ 1) :
    |(∑ x ∈ U, f x) - ∑ x ∈ V, f x| ≤ ((U ∆ V).card : ℝ) := by
  rw [sum_sub_eq_sdiff_sub]
  calc
    |(∑ x ∈ U \ V, f x) - ∑ x ∈ V \ U, f x| ≤
        |∑ x ∈ U \ V, f x| + |∑ x ∈ V \ U, f x| := by
      simpa only [sub_eq_add_neg, abs_neg] using
        abs_add_le (∑ x ∈ U \ V, f x) (-(∑ x ∈ V \ U, f x))
    _ ≤ ((U \ V).card : ℝ) + ((V \ U).card : ℝ) :=
      add_le_add (abs_sum_le_card (U \ V) f hf) (abs_sum_le_card (V \ U) f hf)
    _ = ((U ∆ V).card : ℝ) := by rw [card_symmDiff_eq_sdiff_add, Nat.cast_add]

end Cancellation

section Translation

variable {G : Type uG} [Group G] [DecidableEq G]

theorem sum_leftTranslate (h : G) (A : Finset G) (f : G → ℝ) :
    (∑ g ∈ A, f (h * g)) = ∑ x ∈ leftTranslate h A, f x := by
  unfold leftTranslate
  exact (Finset.sum_image (fun _ _ _ _ hxy => mul_left_cancel hxy)).symm

theorem boundaryRatio_nonneg (A : Finset G) (h : G) : 0 ≤ boundaryRatio A h :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem abs_sum_translate_sub_le (A : Finset G) (h : G) (f : G → ℝ)
    (hf : ∀ g, |f g| ≤ 1) :
    |(∑ g ∈ A, f (h * g)) - ∑ g ∈ A, f g| ≤
      ((leftTranslate h A ∆ A).card : ℝ) := by
  rw [sum_leftTranslate]
  exact abs_sum_sub_le_card_symmDiff (leftTranslate h A) A f hf

/-- The finite-translation inequality for every globally unit-bounded function. -/
theorem abs_realAvg_translate_sub_le (A : Finset G) (hA : A.Nonempty)
    (h : G) (f : G → ℝ) (hf : ∀ g, |f g| ≤ 1) :
    |realAvg A (fun g => f (h * g)) - realAvg A f| ≤ boundaryRatio A h := by
  have hc : 0 < (A.card : ℝ) := Nat.cast_pos.mpr (Finset.card_pos.mpr hA)
  rw [realAvg_eq_sum_div, realAvg_eq_sum_div, ← sub_div, abs_div, abs_of_pos hc]
  exact div_le_div_of_nonneg_right (abs_sum_translate_sub_le A h f hf) hc.le

end Translation

end ThompsonNonamenability

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_FolnerInvariantMean
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.height_quotient_commutative _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesHomology _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.boundedFunctionPull_apply _root_.OAI.PolycyclicRecognition.boundedFunctionPull_one _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.kernelAverage_one _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.smallCoefficientBoundedReal_one _root_.OAI.PolycyclicRecognition.subgroupFunctionExtension_apply _root_.OAI.PolycyclicRecognition.subgroupFunctionExtension_one _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite Følner averages yield the invariant mean for height correction -/

noncomputable section

namespace PolycyclicRecognition

open ThompsonNonamenability Filter
open scoped Topology ENNReal

variable {G : Type*} [Group G] [DecidableEq G]

/-- The translation defect is bounded by the actual symmetric-difference
ratio times the norm of the bounded function. -/
theorem finiteMeanState_translation_bound (A : Finset G) (hA : A.Nonempty)
    (g : G) (f : BoundedReal G) :
    |finiteMeanState A (leftPull g f) - finiteMeanState A f| ≤
      boundaryRatio A g * ‖f‖ := by
  by_cases hf : ‖f‖ = 0
  · have hfzero : f = 0 := norm_eq_zero.mp hf
    simp [hfzero, finiteMeanState]
  · have hnorm : 0 < ‖f‖ := lt_of_le_of_ne (norm_nonneg f) (Ne.symm hf)
    have hu : ∀ x, |f x / ‖f‖| ≤ 1 := by
      intro x
      rw [abs_div, abs_of_pos hnorm]
      apply (div_le_one hnorm).mpr
      simpa only [Real.norm_eq_abs] using lp.norm_apply_le_norm ENNReal.top_ne_zero f x
    have hh := abs_realAvg_translate_sub_le A hA g (fun x => f x / ‖f‖) hu
    simp only [div_eq_mul_inv, realAvg_mul_const, ← sub_mul, abs_mul, abs_inv,
      abs_of_pos hnorm] at hh
    have hh' : |realAvg A (fun x => f (g * x)) - realAvg A f| / ‖f‖ ≤
        boundaryRatio A g := by simpa only [div_eq_mul_inv] using hh
    exact (div_le_iff₀ hnorm).mp hh'

/-- No countability or finite-generation assumption is required for this
compactness step; each group translation has its own vanishing boundary ratio. -/
theorem exists_invariantMean_of_folner_net
    {ι : Type*} {l : Filter ι} [l.NeBot]
    (A : ι → Finset G) (hA : ∀ i, (A i).Nonempty)
    (hboundary : ∀ g, Tendsto (fun i => boundaryRatio (A i) g) l (𝓝 0)) :
    Nonempty (InvariantMean G) := by
  apply exists_invariantMean_of_approximate (l := l) (fun i => finiteMeanState (A i))
    (fun i => finiteMeanState_positive (A i)) (fun i => finiteMeanState_one (A i) (hA i))
  intro g f
  apply squeeze_zero_norm
    (fun i => by simpa only [Real.norm_eq_abs] using
      finiteMeanState_translation_bound (A i) (hA i) g f)
  simpa only [zero_mul] using (hboundary g).mul_const ‖f‖

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_InvariantMeanGenerators
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.height_quotient_commutative _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesHomology _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # It suffices to make a mean invariant under a generating set -/

noncomputable section

namespace PolycyclicRecognition

open ThompsonNonamenability Filter Set
open scoped Topology

variable {G : Type*} [Group G]

/-- Approximate invariance need only be checked on generators; the limiting
functional is invariant under their whole algebraic closure. -/
theorem exists_invariantMean_of_approximate_generators
    {ι : Type*} {l : Filter ι} [l.NeBot]
    (L : ι → BoundedReal G →ₗ[ℝ] ℝ)
    (hpos : ∀ i f, (∀ g, 0 ≤ f g) → 0 ≤ L i f)
    (hone : ∀ i, L i 1 = 1) (S : Set G) (hS : Subgroup.closure S = ⊤)
    (hdefect : ∀ g ∈ S, ∀ f, Tendsto (fun i => L i (leftPull g f) - L i f) l (𝓝 0)) :
    Nonempty (InvariantMean G) := by
  obtain ⟨M, hM, hMone, hMinv⟩ := exists_partially_invariantMean_of_approximate
    (l := l) L hpos hone S hdefect
  have hc : Subgroup.closure S ≤ meanStabilizer M := by
    rw [Subgroup.closure_le]
    exact hMinv
  rw [hS] at hc
  exact ⟨⟨M, hM, hMone, fun g f => hc (Subgroup.mem_top g) f⟩⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_CyclicInvariantMean
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instNonemptyBases _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.height_quotient_commutative _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesHomology _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Invariant means on cyclic groups from literal power averages -/

noncomputable section

namespace PolycyclicRecognition

open ThompsonNonamenability Filter Set
open scoped Topology BigOperators ENNReal

variable {G : Type*} [Group G]

theorem cyclicMeanState_positive (a : G) (n : ℕ) (f : BoundedReal G)
    (hf : ∀ g, 0 ≤ f g) : 0 ≤ cyclicMeanState a n f :=
  realAvg_nonneg _ (fun k _ => hf (a ^ k))

theorem cyclicMeanState_one (a : G) (n : ℕ) : cyclicMeanState a n 1 = 1 :=
  realAvg_const _ (Finset.nonempty_range_iff.mpr (Nat.succ_ne_zero n)) 1

/-- The generator defect telescopes without any injectivity assumption on
the powers. The same averages work for finite and infinite cyclic groups. -/
theorem cyclicMeanState_generator_defect (a : G) (n : ℕ) (f : BoundedReal G) :
    cyclicMeanState a n (leftPull a f) - cyclicMeanState a n f =
      (f (a ^ (n + 1)) - f 1) / ((n : ℝ) + 1) := by
  have havg (v : ℕ → ℝ) :
      realAvg (Finset.range (n + 1)) (fun k => v (k + 1) - v k) =
        (v (n + 1) - v 0) / ((n : ℝ) + 1) := by
    rw [realAvg, Finset.sum_range_sub]
    simp only [Finset.card_range, Nat.cast_add, Nat.cast_one, div_eq_mul_inv, mul_comm]
  have hpull : (fun k : ℕ => leftPull a f (a ^ k)) =
      (fun k : ℕ => f (a ^ (k + 1))) := by
    funext k
    rw [leftPull_apply, pow_succ']
  change realAvg (Finset.range (n + 1)) (fun k => leftPull a f (a ^ k)) -
    realAvg (Finset.range (n + 1)) (fun k => f (a ^ k)) = _
  rw [hpull, ← realAvg_sub]
  simpa only [pow_zero] using havg (fun k => f (a ^ k))

theorem invariantMean_of_zpowers_eq_top (a : G) (ha : Subgroup.zpowers a = ⊤) :
    Nonempty (InvariantMean G) := by
  apply exists_invariantMean_of_approximate_generators (l := atTop)
    (cyclicMeanState a) (cyclicMeanState_positive a) (cyclicMeanState_one a) {a}
    (by rwa [← Subgroup.zpowers_eq_closure])
  intro g hg f
  have hga : g = a := mem_singleton_iff.mp hg
  subst g
  have hbound (n : ℕ) :
      ‖cyclicMeanState a n (leftPull a f) - cyclicMeanState a n f‖ ≤
        (2 * ‖f‖) / ((n : ℝ) + 1) := by
    rw [Real.norm_eq_abs, cyclicMeanState_generator_defect, abs_div,
      abs_of_pos (show 0 < (n : ℝ) + 1 by positivity)]
    apply div_le_div_of_nonneg_right _ (by positivity)
    have h₁ := lp.norm_apply_le_norm ENNReal.top_ne_zero f (a ^ (n + 1))
    have h₂ := lp.norm_apply_le_norm ENNReal.top_ne_zero f 1
    have hsub := abs_sub (f (a ^ (n + 1))) (f 1)
    simp only [Real.norm_eq_abs] at h₁ h₂
    linarith
  apply squeeze_zero_norm hbound
  simpa only [div_eq_mul_inv, one_mul, mul_zero, mul_assoc] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (2 * ‖f‖)

theorem invariantMean_of_isCyclic [IsCyclic G] : Nonempty (InvariantMean G) := by
  obtain ⟨a, ha⟩ := isCyclic_iff_exists_zpowers_eq_top.mp (inferInstance : IsCyclic G)
  exact invariantMean_of_zpowers_eq_top a ha

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_ExtensionInvariantMean
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.height_quotient_commutative _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesHomology _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Invariant means on extensions

Average first on each kernel coset and then on the quotient. All averages
act on the actual bounded real functions used in the height correction.
-/

noncomputable section

namespace PolycyclicRecognition

open ThompsonNonamenability
open scoped ENNReal

variable {G Q : Type*} [Group G] [Group Q]

theorem invariantMean_of_extension (φ : G →* Q) (hφ : Function.Surjective φ)
    (hN : Nonempty (InvariantMean φ.ker)) (hQ : Nonempty (InvariantMean Q)) :
    Nonempty (InvariantMean G) := by
  choose s hs using hφ
  exact ⟨extensionInvariantMean φ s hs hN.some hQ.some⟩

theorem invariantMean_of_normal_subgroup (N : Subgroup G) [N.Normal]
    (hN : Nonempty (InvariantMean N)) (hQ : Nonempty (InvariantMean (G ⧸ N))) :
    Nonempty (InvariantMean G) := by
  apply invariantMean_of_extension (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
    _ hQ
  rw [QuotientGroup.ker_mk']
  exact hN

/-- No normality assumption is needed for a finite extension: restrict to
the normal core, then average over its finite quotient. -/
theorem invariantMean_of_finiteIndex (K : Subgroup G) [K.FiniteIndex]
    (hK : Nonempty (InvariantMean K)) : Nonempty (InvariantMean G) := by
  let N := K.normalCore
  let i : N →* K := Subgroup.inclusion K.normalCore_le
  let MN := subgroupInvariantMean hK.some i.range
  let e : N ≃* i.range := MonoidHom.ofInjective (Subgroup.inclusion_injective _)
  have hN : Nonempty (InvariantMean N) :=
    ⟨imageInvariantMean e.symm.toMonoidHom e.symm.surjective MN⟩
  exact invariantMean_of_normal_subgroup N hN ⟨finiteInvariantMean⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.Thompson_FiniteLevels
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.height_quotient_commutative _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesHomology _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite scalar levels

The distinct values of a nonnegative function on a finite set, together with
zero, give a finite subdivision. Its positive gaps reconstruct every value
and every absolute difference by strict superlevel indicators. These are
finite sums, including when the only level is zero.
-/

open scoped BigOperators

universe uG

namespace ThompsonNonamenability

variable {G : Type uG}

namespace FiniteLevelChain

theorem exists_chain (K : Finset G) (p : G → ℝ)
    (hp : ∀ x ∈ K, 0 ≤ p x) : Nonempty (FiniteLevelChain K p) :=
  ⟨ofNonneg K p hp⟩

variable {K : Finset G} {p : G → ℝ} (c : FiniteLevelChain K p)

theorem gap_pos (i : Fin c.n) : 0 < c.gap i := by
  apply sub_pos.mpr
  exact c.strictMono_value (show i.castSucc < i.succ from Nat.lt_succ_self i.val)

/-- Telescoping below any selected value of a strictly increasing finite list. -/
private theorem telescope : ∀ (n : ℕ) (f : Fin (n + 1) → ℝ),
    StrictMono f → ∀ k : Fin (n + 1),
      f k - f 0 = ∑ i : Fin n,
        (f i.succ - f i.castSucc) * (if f i.castSucc < f k then 1 else 0) := by
  intro n
  induction n with
  | zero =>
      intro f hf k
      have hk : k = 0 := by
        apply Fin.ext
        have hklt := k.isLt
        omega
      subst k
      simp
  | succ n ih =>
      intro f hf k
      refine Fin.cases ?_ (fun k => ?_) k
      · have hnot : ∀ i : Fin (n + 1), ¬ f i.castSucc < f 0 := by
          intro i
          exact not_lt_of_ge (hf.monotone (Fin.zero_le i.castSucc))
        simp [hnot]
      · have hs := ih (fun j : Fin (n + 1) => f j.succ)
          (by intro a b hab; exact hf (Nat.succ_lt_succ hab)) k
        have hfirst : f 0 < f k.succ := hf (Fin.succ_pos k)
        rw [Fin.sum_univ_succ]
        change f k.succ - f 0 =
          (f (0 : Fin (n + 1)).succ - f 0) * (if f 0 < f k.succ then 1 else 0) +
            ∑ i : Fin n, (f i.succ.succ - f i.castSucc.succ) *
              (if f i.castSucc.succ < f k.succ then 1 else 0)
        rw [ite_eq_left hfirst, mul_one, ← hs]
        ring

/-- The finite layer decomposition of each value in the actual level set. -/
theorem reconstruct (a : ℝ) (ha : a ∈ insert 0 (K.image p)) :
    a = ∑ i : Fin c.n, c.gap i *
      (if c.value i.castSucc < a then (1 : ℝ) else 0) := by
  classical
  have ha' : a ∈ Finset.univ.image c.value := by
    rw [c.image_value_eq]
    exact ha
  rcases Finset.mem_image.mp ha' with ⟨k, _, rfl⟩
  simpa only [gap, c.value_zero, sub_zero] using
    telescope c.n c.value c.strictMono_value k

private theorem abs_sub_eq_sum_of_le (a b : ℝ)
    (ha : a ∈ insert 0 (K.image p)) (hb : b ∈ insert 0 (K.image p))
    (hab : a ≤ b) :
    |a - b| = ∑ i : Fin c.n, c.gap i *
      |(if c.value i.castSucc < a then (1 : ℝ) else 0) -
        (if c.value i.castSucc < b then (1 : ℝ) else 0)| := by
  classical
  have hi : ∀ i : Fin c.n,
      (if c.value i.castSucc < a then (1 : ℝ) else 0) ≤
        (if c.value i.castSucc < b then (1 : ℝ) else 0) := by
    intro i
    by_cases hai : c.value i.castSucc < a
    · have hbi : c.value i.castSucc < b := lt_of_lt_of_le hai hab
      simp [hai, hbi]
    · simp only [ite_eq_right hai]
      by_cases hbi : c.value i.castSucc < b <;> simp [hbi]
  calc
    |a - b| = b - a := by rw [abs_of_nonpos (sub_nonpos.mpr hab)]; ring
    _ = (∑ i : Fin c.n, c.gap i * (if c.value i.castSucc < b then (1 : ℝ) else 0)) -
        (∑ i : Fin c.n, c.gap i * (if c.value i.castSucc < a then (1 : ℝ) else 0)) :=
      congrArg₂ (fun x y : ℝ => x - y) (c.reconstruct b hb) (c.reconstruct a ha)
    _ = ∑ i : Fin c.n, c.gap i *
        |(if c.value i.castSucc < a then (1 : ℝ) else 0) -
          (if c.value i.castSucc < b then (1 : ℝ) else 0)| := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [abs_of_nonpos (sub_nonpos.mpr (hi i))]
      ring

/-- The finite coarea identity for a scalar absolute difference. -/
theorem abs_sub_eq_sum (a b : ℝ)
    (ha : a ∈ insert 0 (K.image p)) (hb : b ∈ insert 0 (K.image p)) :
    |a - b| = ∑ i : Fin c.n, c.gap i *
      |(if c.value i.castSucc < a then (1 : ℝ) else 0) -
        (if c.value i.castSucc < b then (1 : ℝ) else 0)| := by
  rcases le_total a b with hab | hba
  · exact c.abs_sub_eq_sum_of_le a b ha hb hab
  · simpa only [abs_sub_comm] using c.abs_sub_eq_sum_of_le b a hb ha hba

end FiniteLevelChain

end ThompsonNonamenability

end OAI
end

section
-- module Solutions.OAIQ093_PR.Thompson_FiniteCoarea
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.height_quotient_commutative _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesHomology _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

universe uG

namespace ThompsonNonamenability

open scoped BigOperators symmDiff

variable {G : Type uG} [DecidableEq G]

private theorem sum_indicator_eq_card (A C : Finset G) (hAC : A ⊆ C) :
    (∑ x ∈ C, if x ∈ A then (1 : ℝ) else 0) = (A.card : ℝ) := by
  classical
  have hfilter : C.filter (fun x => x ∈ A) = A := by
    ext x
    simp only [Finset.mem_filter]
    exact ⟨And.right, fun hx => ⟨hAC hx, hx⟩⟩
  rw [← Finset.sum_filter, hfilter]
  simp

private theorem sum_abs_indicators_eq_card_symmDiff
    (A B C : Finset G) (hAC : A ⊆ C) (hBC : B ⊆ C) :
    (∑ x ∈ C,
      |(if x ∈ A then (1 : ℝ) else 0) -
        (if x ∈ B then (1 : ℝ) else 0)|) = ((A ∆ B).card : ℝ) := by
  classical
  have hsub : A ∆ B ⊆ C := by
    intro x hx
    rcases Finset.mem_symmDiff.mp hx with hx | hx
    · exact hAC hx.1
    · exact hBC hx.1
  calc
    _ = ∑ x ∈ C, if x ∈ A ∆ B then (1 : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro x hx
      by_cases hA : x ∈ A <;> by_cases hB : x ∈ B <;>
        simp [hA, hB, Finset.mem_symmDiff]
    _ = _ := sum_indicator_eq_card (A ∆ B) C hsub

private theorem finite_value_mem {K : Finset G} {p : G → ℝ}
    (hpK : ∀ x, x ∉ K → p x = 0) (x : G) :
    p x ∈ insert 0 (K.image p) := by
  classical
  by_cases hx : x ∈ K
  · exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem p hx)
  · rw [hpK x hx]
    exact Finset.mem_insert_self _ _

namespace FiniteLevelChain

variable {K : Finset G} {p : G → ℝ}

omit [DecidableEq G] in
theorem levelSet_subset [DecidableEq G] (c : FiniteLevelChain K p) (i : Fin c.n) :
    c.levelSet i ⊆ K := Finset.filter_subset _ _

/-- The finite carrier restriction does not change positive-threshold membership. -/
theorem mem_levelSet (c : FiniteLevelChain K p)
    (hpK : ∀ x, x ∉ K → p x = 0) (i : Fin c.n) (x : G) :
    x ∈ c.levelSet i ↔ c.value i.castSucc < p x := by
  classical
  have hv : 0 ≤ c.value i.castSucc := by
    simpa only [c.value_zero] using
      c.strictMono_value.monotone (Fin.zero_le i.castSucc)
  constructor
  · intro hx
    exact (Finset.mem_filter.mp hx).2
  · intro hx
    apply Finset.mem_filter.mpr
    refine ⟨?_, hx⟩
    by_contra hxK
    rw [hpK x hxK] at hx
    exact (not_lt_of_ge hv) hx

omit [DecidableEq G] in
theorem levelSet_nonempty [DecidableEq G] (c : FiniteLevelChain K p) (i : Fin c.n) :
    (c.levelSet i).Nonempty := by
  classical
  have hlt : c.value i.castSucc < c.value i.succ :=
    c.strictMono_value (by
      change i.val < i.val + 1
      exact Nat.lt_succ_self i.val)
  have hv : 0 ≤ c.value i.castSucc := by
    simpa only [c.value_zero] using
      c.strictMono_value.monotone (Fin.zero_le i.castSucc)
  have hpos : 0 < c.value i.succ := lt_of_le_of_lt hv hlt
  have hmem : c.value i.succ ∈ insert 0 (K.image p) := by
    rw [← c.image_value_eq]
    exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
  have himage : c.value i.succ ∈ K.image p :=
    (Finset.mem_insert.mp hmem).resolve_left (ne_of_gt hpos)
  obtain ⟨x, hxK, hpx⟩ := Finset.mem_image.mp himage
  refine ⟨x, Finset.mem_filter.mpr ⟨hxK, ?_⟩⟩
  rw [hpx]
  exact hlt

/-- Exact finite layer-cake identity for the mass. -/
theorem coarea_mass (c : FiniteLevelChain K p)
    (hpK : ∀ x, x ∉ K → p x = 0) :
    (∑ x ∈ K, p x) =
      ∑ i : Fin c.n, c.gap i * ((c.levelSet i).card : ℝ) := by
  classical
  calc
    _ = ∑ x ∈ K, ∑ i : Fin c.n, c.gap i *
        (if c.value i.castSucc < p x then (1 : ℝ) else 0) := by
      apply Finset.sum_congr rfl
      intro x hx
      exact c.reconstruct (p x) (finite_value_mem hpK x)
    _ = ∑ i : Fin c.n, ∑ x ∈ K, c.gap i *
        (if c.value i.castSucc < p x then (1 : ℝ) else 0) :=
      Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [← Finset.mul_sum]
      congr 1
      calc
        _ = ∑ x ∈ K, if x ∈ c.levelSet i then (1 : ℝ) else 0 := by
          apply Finset.sum_congr rfl
          intro x hx
          simp only [c.mem_levelSet hpK i x]
        _ = _ := sum_indicator_eq_card _ K (c.levelSet_subset i)

end FiniteLevelChain

section Translation

variable [Group G]

theorem mem_leftTranslate_iff (h : G) (A : Finset G) (x : G) :
    x ∈ leftTranslate h A ↔ h⁻¹ * x ∈ A := by
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    simpa using hy
  · intro hx
    exact Finset.mem_image.mpr ⟨h⁻¹ * x, hx, by simp⟩

namespace FiniteLevelChain

variable {K : Finset G} {p : G → ℝ}

/-- Exact coarea identity for one left translation, over its finite support carrier. -/
theorem coarea_translation (c : FiniteLevelChain K p)
    (hpK : ∀ x, x ∉ K → p x = 0) (h : G) :
    (∑ x ∈ K ∪ leftTranslate h K, |p (h⁻¹ * x) - p x|) =
      ∑ i : Fin c.n, c.gap i *
        ((leftTranslate h (c.levelSet i) ∆ c.levelSet i).card : ℝ) := by
  classical
  calc
    _ = ∑ x ∈ K ∪ leftTranslate h K, ∑ i : Fin c.n, c.gap i *
        |(if c.value i.castSucc < p (h⁻¹ * x) then (1 : ℝ) else 0) -
          (if c.value i.castSucc < p x then (1 : ℝ) else 0)| := by
      apply Finset.sum_congr rfl
      intro x hx
      exact c.abs_sub_eq_sum (p (h⁻¹ * x)) (p x)
        (finite_value_mem hpK _) (finite_value_mem hpK _)
    _ = ∑ i : Fin c.n, ∑ x ∈ K ∪ leftTranslate h K, c.gap i *
        |(if c.value i.castSucc < p (h⁻¹ * x) then (1 : ℝ) else 0) -
          (if c.value i.castSucc < p x then (1 : ℝ) else 0)| :=
      Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [← Finset.mul_sum]
      congr 1
      have hleft : leftTranslate h (c.levelSet i) ⊆ K ∪ leftTranslate h K := by
        intro x hx
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
        exact Finset.mem_union_right _
          (Finset.mem_image_of_mem (fun y => h * y) (c.levelSet_subset i hy))
      have hright : c.levelSet i ⊆ K ∪ leftTranslate h K := by
        intro x hx
        exact Finset.mem_union_left _ (c.levelSet_subset i hx)
      calc
        _ = ∑ x ∈ K ∪ leftTranslate h K,
            |(if x ∈ leftTranslate h (c.levelSet i) then (1 : ℝ) else 0) -
              (if x ∈ c.levelSet i then (1 : ℝ) else 0)| := by
          apply Finset.sum_congr rfl
          intro x hx
          simp only [mem_leftTranslate_iff, c.mem_levelSet hpK]
        _ = _ := sum_abs_indicators_eq_card_symmDiff _ _ _ hleft hright

/-- Summing the exact translation identities introduces no cardinality factor. -/
theorem coarea_sum (c : FiniteLevelChain K p)
    (hpK : ∀ x, x ∉ K → p x = 0) (S : Finset G) :
    (∑ h ∈ S, ∑ x ∈ K ∪ leftTranslate h K, |p (h⁻¹ * x) - p x|) =
      ∑ i : Fin c.n, c.gap i *
        (∑ h ∈ S, ((leftTranslate h (c.levelSet i) ∆ c.levelSet i).card : ℝ)) := by
  calc
    _ = ∑ h ∈ S, ∑ i : Fin c.n, c.gap i *
        ((leftTranslate h (c.levelSet i) ∆ c.levelSet i).card : ℝ) :=
      Finset.sum_congr rfl (fun h _ => c.coarea_translation hpK h)
    _ = _ := by
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]

end FiniteLevelChain

/-- A nonempty level inside the supplied finite support has small total boundary. -/
theorem finite_folner_of_small_defect_subset
    {K S : Finset G} {p : G → ℝ} {ε : ℝ}
    (hp0 : ∀ g, 0 ≤ p g)
    (hpK : ∀ g, g ∉ K → p g = 0)
    (mass : ∑ g ∈ K, p g = 1)
    (hdef : (∑ h ∈ S, ∑ x ∈ K ∪ leftTranslate h K,
      |p (h⁻¹ * x) - p x|) < ε) :
    ∃ A : Finset G, A ⊆ K ∧ A.Nonempty ∧
      (∑ h ∈ S, ((leftTranslate h A ∆ A).card : ℝ)) < ε * (A.card : ℝ) := by
  classical
  obtain ⟨c⟩ := FiniteLevelChain.exists_chain K p (fun g _ => hp0 g)
  have hmass : (∑ i : Fin c.n, c.gap i * ((c.levelSet i).card : ℝ)) = 1 :=
    (c.coarea_mass hpK).symm.trans mass
  have hex : ∃ i : Fin c.n,
      (∑ h ∈ S, ((leftTranslate h (c.levelSet i) ∆ c.levelSet i).card : ℝ)) <
        ε * ((c.levelSet i).card : ℝ) := by
    by_contra hnone
    have hfail : ∀ i : Fin c.n, ε * ((c.levelSet i).card : ℝ) ≤
        ∑ h ∈ S, ((leftTranslate h (c.levelSet i) ∆ c.levelSet i).card : ℝ) :=
      fun i => le_of_not_gt (fun hi => hnone ⟨i, hi⟩)
    have hle : ε ≤ ∑ h ∈ S, ∑ x ∈ K ∪ leftTranslate h K,
        |p (h⁻¹ * x) - p x| := by
      calc
        ε = ε * ∑ i : Fin c.n, c.gap i * ((c.levelSet i).card : ℝ) := by
          rw [hmass, mul_one]
        _ = ∑ i : Fin c.n, c.gap i * (ε * ((c.levelSet i).card : ℝ)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          ring
        _ ≤ ∑ i : Fin c.n, c.gap i *
            (∑ h ∈ S, ((leftTranslate h (c.levelSet i) ∆ c.levelSet i).card : ℝ)) :=
          Finset.sum_le_sum (fun i _ =>
            mul_le_mul_of_nonneg_left (hfail i) (c.gap_pos i).le)
        _ = _ := (c.coarea_sum hpK S).symm
    exact (not_lt_of_ge hle) hdef
  obtain ⟨i, hi⟩ := hex
  exact ⟨c.levelSet i, c.levelSet_subset i, c.levelSet_nonempty i, hi⟩

/-- Finite probability with small total translation defect yields a finite Følner set. -/
theorem finite_folner_of_small_defect
    {K S : Finset G} {p : G → ℝ} {ε : ℝ}
    (hp0 : ∀ g, 0 ≤ p g)
    (hpK : ∀ g, g ∉ K → p g = 0)
    (mass : ∑ g ∈ K, p g = 1)
    (hdef : (∑ h ∈ S, ∑ x ∈ K ∪ leftTranslate h K,
      |p (h⁻¹ * x) - p x|) < ε) :
    ∃ A : Finset G, A.Nonempty ∧
      (∑ h ∈ S, ((leftTranslate h A ∆ A).card : ℝ)) < ε * (A.card : ℝ) := by
  obtain ⟨A, _, hA, hsmall⟩ := finite_folner_of_small_defect_subset hp0 hpK mass hdef
  exact ⟨A, hA, hsmall⟩

end Translation

end ThompsonNonamenability

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.Thompson_ProbabilityDefects
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.height_quotient_commutative _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesHomology _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.OAI.ThompsonNonamenability.separatorCoordinate_apply _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite probabilities and their simultaneous translation defects

One ℓ¹ space on `S × G` carries the sum of all translation defects.  In
particular its norm is the exact finite sum, without a factor depending on
`S.card`.  This is the finite-probability input to the separation argument.
-/

noncomputable section

open scoped BigOperators Classical

universe uG uι

namespace ThompsonNonamenability

variable {G : Type uG}

theorem isProbabilityWeights_single (g : G) :
    IsProbabilityWeights (Finsupp.single g (1 : ℝ)) := by
  refine ⟨?_, mass_single g 1⟩
  intro x
  simp only [Finsupp.single_apply]
  split_ifs
  · exact zero_le_one
  · exact le_rfl

theorem convex_probabilityWeights :
    Convex ℝ {p : G →₀ ℝ | IsProbabilityWeights p} := by
  intro p hp q hq a b ha hb hab
  refine ⟨?_, ?_⟩
  · intro g
    change 0 ≤ a * p g + b * q g
    exact add_nonneg (mul_nonneg ha (hp.1 g)) (mul_nonneg hb (hq.1 g))
  · rw [map_add, map_smul, map_smul, hp.2, hq.2]
    simpa using hab

variable [Group G]

private theorem single_apply_real {ι : Type uι} [DecidableEq ι] (i j : ι) (a : ℝ) :
    (lp.single 1 i a : lp (fun _ : ι => ℝ) 1) j = if i = j then a else 0 := by
  by_cases hij : i = j
  · subst j
    simp
  · rw [lp.single_apply_ne (E := fun _ : ι => ℝ) 1 i a (Ne.symm hij), ite_eq_right hij]

/-- Coordinate computation for a single point probability. -/
theorem diracDefect_apply (S : Finset G) (g : G) (h : S) (x : G) :
    diracDefect S g (h, x) =
      (Finsupp.single g (1 : ℝ)) (h.val⁻¹ * x) - (Finsupp.single g (1 : ℝ)) x := by
  have hmul : h.val * g = x ↔ g = h.val⁻¹ * x := by
    constructor
    · intro heq
      simpa [mul_assoc] using congrArg (fun y => h.val⁻¹ * y) heq
    · intro heq
      simpa [mul_assoc] using congrArg (fun y => h.val * y) heq
  unfold diracDefect
  rw [lp.coeFn_sum, Finset.sum_apply, Finset.sum_eq_single h]
  · simp only [lp.coeFn_sub, Pi.sub_apply]
    rw [single_apply_real, single_apply_real]
    simp only [Prod.mk.injEq, true_and, hmul,
      Finsupp.single_apply]
  · intro k _ hkh
    simp [Prod.mk.injEq, hkh]
  · simp

/-- The product coordinate is exactly the left translation difference. -/
theorem defectMap_apply (S : Finset G) (p : G →₀ ℝ) (h : S) (x : G) :
    defectMap S p (h, x) = p (h.val⁻¹ * x) - p x := by
  induction p using Finsupp.induction_linear with
  | zero => simp
  | add p q hp hq =>
      simp only [map_add, lp.coeFn_add, Pi.add_apply, Finsupp.add_apply, hp, hq]
      ring
  | single g a =>
      rw [defectMap_single, lp.coeFn_smul, Pi.smul_apply, diracDefect_apply]
      simp only [smul_eq_mul, Finsupp.single_apply, mul_sub, mul_ite, mul_one, mul_zero]

/-- Each translation difference vanishes outside its exact finite support bound. -/
theorem translation_difference_eq_zero_of_not_mem (p : G →₀ ℝ) (h x : G)
    (hx : x ∉ p.support ∪ p.support.image (fun g => h * g)) :
    p (h⁻¹ * x) - p x = 0 := by
  have hx₀ : x ∉ p.support := fun hmem => hx (Finset.mem_union_left _ hmem)
  have hx₁ : h⁻¹ * x ∉ p.support := by
    intro hmem
    apply hx
    apply Finset.mem_union_right
    exact Finset.mem_image.mpr ⟨h⁻¹ * x, hmem, by simp⟩
  simp [Finsupp.notMem_support_iff.mp hx₀, Finsupp.notMem_support_iff.mp hx₁]

/-- Exact ℓ¹ norm of the simultaneous defect, with no `S.card` loss. -/
theorem norm_defectMap (S : Finset G) (p : G →₀ ℝ) :
    ‖defectMap S p‖ =
      ∑ h ∈ S, ∑ x ∈ p.support ∪ p.support.image (fun g => h * g),
        |p (h⁻¹ * x) - p x| := by
  have hsum : HasSum (fun z : S × G => ‖defectMap S p z‖) ‖defectMap S p‖ := by
    simpa only [ENNReal.toReal_one, Real.rpow_one] using
      (lp.hasSum_norm (p := 1) (by simp) (defectMap S p))
  calc
    ‖defectMap S p‖ = ∑' z : S × G, ‖defectMap S p z‖ := hsum.tsum_eq.symm
    _ = ∑ h : S, ∑' x : G, ‖defectMap S p (h, x)‖ := by
      rw [hsum.summable.tsum_prod, tsum_fintype]
    _ = ∑ h : S, ∑ x ∈ p.support ∪ p.support.image (fun g => h.val * g),
        |p (h.val⁻¹ * x) - p x| := by
      apply Finset.sum_congr rfl
      intro h _
      simp only [defectMap_apply, Real.norm_eq_abs]
      apply tsum_eq_sum
      intro x hx
      rw [translation_difference_eq_zero_of_not_mem p h.val x hx, abs_zero]
    _ = ∑ h ∈ S, ∑ x ∈ p.support ∪ p.support.image (fun g => h * g),
        |p (h⁻¹ * x) - p x| :=
      Finset.sum_coe_sort S (fun h : G =>
        ∑ x ∈ p.support ∪ p.support.image (fun g => h * g),
          |p (h⁻¹ * x) - p x|)

theorem convex_defectSet (S : Finset G) : Convex ℝ (defectSet S) :=
  convex_probabilityWeights.linear_image (defectMap S)

theorem diracDefect_mem_defectSet (S : Finset G) (g : G) :
    diracDefect S g ∈ defectSet S := by
  refine ⟨Finsupp.single g 1, isProbabilityWeights_single g, ?_⟩
  simp

end ThompsonNonamenability

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.Thompson_MeanApproximation
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.height_quotient_commutative _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesHomology _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite probabilities approximately invariant under a finite set

The usual positive normalized invariant mean forces zero to lie in the
closure of the actual finite-probability defect set. The separation argument
uses bounded coordinate functions of a continuous linear functional on ℓ¹;
no identification of the full dual of ℓ¹ is assumed.
-/

noncomputable section

open scoped ENNReal BigOperators

universe uG

namespace ThompsonNonamenability

variable {G : Type uG} [Group G] [DecidableEq G]

attribute [local instance] OAI.ThompsonNonamenability.instFactLeENNRealOfNat_solutions
theorem separatorDefect_apply {S : Finset G} (ell : DefectSpace S →L[ℝ] ℝ)
    (g : G) : separatorDefect ell g = ell (diracDefect S g) := by
  classical
  cases Subsingleton.elim (inferInstance : DecidableEq G) (Classical.decEq G)
  simp only [separatorDefect, lp.coeFn_sum, Finset.sum_apply,
    lp.coeFn_sub, Pi.sub_apply, leftPull_apply, separatorCoordinate_apply,
    diracDefect, map_sum, map_sub]

theorem InvariantMean.separatorDefect_eq_zero (M : InvariantMean G)
    {S : Finset G} (ell : DefectSpace S →L[ℝ] ℝ) : M (separatorDefect ell) = 0 := by
  classical
  change M.toLinearMap (∑ h : {h : G // h ∈ S},
    (leftPull h.val (separatorCoordinate ell h) - separatorCoordinate ell h)) = 0
  simp only [map_sum, map_sub, M.left_invariant, sub_self, Finset.sum_const_zero]

/-- Separation contradicts the existence of a positive normalized invariant mean. -/
theorem InvariantMean.zero_mem_closure_defectSet (M : InvariantMean G)
    (S : Finset G) : (0 : DefectSpace S) ∈ closure (defectSet S) := by
  classical
  by_contra hout
  obtain ⟨ell, c, hc, hsep⟩ := geometric_hahn_banach_point_closed
    (convex_defectSet S).closure isClosed_closure hout
  have hcpos : 0 < c := by simpa only [ell.map_zero] using hc
  have hpoint (g : G) : c ≤ separatorDefect ell g := by
    rw [separatorDefect_apply]
    apply le_of_lt
    apply hsep
    apply subset_closure
    exact diracDefect_mem_defectSet S g
  have hmean : c ≤ M (separatorDefect ell) := by
    simpa only [InvariantMean.map_const] using
      M.mono (f := c • (1 : BoundedReal G)) (g := separatorDefect ell)
        (fun g => by simpa only [BoundedReal.smul_one_apply] using hpoint g)
  rw [M.separatorDefect_eq_zero] at hmean
  exact (not_le_of_gt hcpos) hmean

/-- Actual nonnegative finite probabilities with arbitrarily small total defect. -/
theorem InvariantMean.exists_probability_small_defect (M : InvariantMean G)
    (S : Finset G) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : G →₀ ℝ, IsProbabilityWeights p ∧ ‖defectMap S p‖ < ε := by
  classical
  obtain ⟨v, hv, hvsmall⟩ := Metric.mem_closure_iff.mp
    (M.zero_mem_closure_defectSet S) ε hε
  obtain ⟨p, hp, rfl⟩ := hv
  refine ⟨p, hp, ?_⟩
  simpa only [dist_zero_left] using hvsmall

end ThompsonNonamenability

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.Thompson_MeanToFolner
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.height_quotient_commutative _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesHomology _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators symmDiff

universe uG

namespace ThompsonNonamenability

variable {G : Type uG} [Group G] [DecidableEq G]

/-- A standard invariant mean yields a finite set with small total boundary. -/
theorem InvariantMean.exists_folner_total (M : InvariantMean G)
    (S : Finset G) {ε : ℝ} (hε : 0 < ε) :
    ∃ A : Finset G, A.Nonempty ∧
      (∑ h ∈ S, ((leftTranslate h A ∆ A).card : ℝ)) < ε * A.card := by
  classical
  cases Subsingleton.elim (inferInstance : DecidableEq G) (Classical.decEq G)
  obtain ⟨p, hp, hsmall⟩ := M.exists_probability_small_defect S hε
  have hmass : ∑ g ∈ p.support, p g = 1 := by
    simpa only [mass_apply] using hp.2
  have hdef : (∑ h ∈ S, ∑ x ∈ p.support ∪ leftTranslate h p.support,
      |p (h⁻¹ * x) - p x|) < ε := by
    simpa only [norm_defectMap, leftTranslate] using hsmall
  exact finite_folner_of_small_defect (p := fun g => p g) (K := p.support)
    (S := S) hp.1 (fun g hg => Finsupp.notMem_support_iff.mp hg) hmass hdef

end ThompsonNonamenability

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_PolycyclicInvariantMean
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finite_templateSymmetryGroup _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.height_quotient_commutative _root_.OAI.PolycyclicRecognition.instFiniteSubtypeLinearEquivRealIdMemSubgroupLinearSupportSymmetryGroup _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesHomology _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Concrete invariant means for virtually polycyclic groups

The finite cyclic subnormal series gives the mean by successive kernel and
quotient averages. Thus amenability in the model reduction is proved from
polycyclicity, rather than retained as an extra premise.
-/

noncomputable section

namespace PolycyclicRecognition

open ThompsonNonamenability ChromaticCyclic

variable {G : Type*} [Group G]

theorem invariantMean_of_cyclicStep {H K : Subgroup G} (s : CyclicStep H K)
    (hH : Nonempty (InvariantMean H)) : Nonempty (InvariantMean K) := by
  let := s.normal
  let := s.cyclic
  let e := (Subgroup.subgroupOfEquivOfLe s.le).symm
  exact invariantMean_of_normal_subgroup (H.subgroupOf K)
    ⟨imageInvariantMean e.toMonoidHom e.surjective hH.some⟩ invariantMean_of_isCyclic

theorem invariantMean_of_cyclicSeries {H K : Subgroup G} {n : ℕ}
    (c : CyclicSeries H K n) (hH : Nonempty (InvariantMean H)) :
    Nonempty (InvariantMean K) := by
  have hm : ∀ i, i ≤ n → Nonempty (InvariantMean (c.group i)) := by
    intro i
    induction i with
    | zero => intro _; rw [c.first]; exact hH
    | succ i ih =>
      intro hi
      exact invariantMean_of_cyclicStep (c.step i (by omega)) (ih (by omega))
  rw [← c.last]
  exact hm n le_rfl

theorem invariantMean_of_isPolycyclic (hG : IsPolycyclic G) :
    Nonempty (InvariantMean G) := by
  obtain ⟨n, ⟨c⟩⟩ := hG
  have htop := invariantMean_of_cyclicSeries c ⟨finiteInvariantMean⟩
  exact ⟨imageInvariantMean (⊤ : Subgroup G).subtype
    (by intro g; exact ⟨⟨g, trivial⟩, rfl⟩) htop.some⟩

theorem invariantMean_of_isVirtuallyPolycyclic (hG : IsVirtuallyPolycyclic G) :
    Nonempty (InvariantMean G) := by
  obtain ⟨K, hindex, hK⟩ := hG
  let := hindex
  exact invariantMean_of_finiteIndex K (invariantMean_of_isPolycyclic hK)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_RightFolnerExpansion
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.height_quotient_commutative _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesHomology _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.meanCorrection_one _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.smallCoefficientRealCoinvariantMean_one _root_.OAI.PolycyclicRecognition.smallCoefficientRealMean_one _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.OAI.PolycyclicRecognition.vectorMeanCorrection_one _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Right finite expansions and metric Følner sets in the source group

Left-invariant metrics use right expansions of finite sets. Inversion
converts the left Følner sets supplied by an invariant mean into these sets.
-/

noncomputable section

namespace PolycyclicRecognition

open ThompsonNonamenability
open scoped symmDiff

variable {G : Type*} [Group G] [DecidableEq G]

theorem exists_small_rightExpansion (M : InvariantMean G) (S : Finset G)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ E : Finset G, E.Nonempty ∧
      ((rightFiniteExpansion E S \ E).card : ℝ) < ε * E.card := by
  obtain ⟨A, hA, hsmall⟩ := M.exists_folner_total (S.image Inv.inv) hε
  let E := A.image Inv.inv
  have hE : E.card = A.card := Finset.card_image_of_injective A inv_injective
  have hbound (g : G) : ((E.image (· * g) \ E).card : ℝ) ≤
      ((_root_.OAI.ThompsonNonamenability.leftTranslate g⁻¹ A ∆ A).card : ℝ) := by
    have hs : (E.image (· * g) \ E).image Inv.inv ⊆ _root_.OAI.ThompsonNonamenability.leftTranslate g⁻¹ A ∆ A := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨hy, hyE⟩ := Finset.mem_sdiff.mp hy
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hz
      apply Finset.mem_symmDiff.mpr
      left
      refine ⟨?_, ?_⟩
      · apply Finset.mem_image.mpr
        exact ⟨a, ha, by simp⟩
      · intro hin
        apply hyE
        apply Finset.mem_image.mpr
        exact ⟨(a⁻¹ * g)⁻¹, hin, inv_inv _⟩
    have hc := Finset.card_le_card hs
    rw [Finset.card_image_of_injective _
      (inv_injective : Function.Injective (fun g : G => g⁻¹))] at hc
    exact_mod_cast hc
  have hs : rightFiniteExpansion E S \ E ⊆
      S.biUnion (fun g => E.image (· * g) \ E) := by
    intro x hx
    obtain ⟨hx, hxE⟩ := Finset.mem_sdiff.mp hx
    obtain ⟨g, hg, hxg⟩ := Finset.mem_biUnion.mp hx
    exact Finset.mem_biUnion.mpr ⟨g, hg, Finset.mem_sdiff.mpr ⟨hxg, hxE⟩⟩
  have hcard : ((rightFiniteExpansion E S \ E).card : ℝ) ≤
      ∑ g ∈ S, ((E.image (· * g) \ E).card : ℝ) := by
    exact_mod_cast (Finset.card_le_card hs).trans Finset.card_biUnion_le
  have hsum : (∑ g ∈ S, ((_root_.OAI.ThompsonNonamenability.leftTranslate g⁻¹ A ∆ A).card : ℝ)) < ε * E.card := by
    rw [hE]
    convert hsmall using 1
    all_goals try with_reducible_and_instances rfl
    rw [Finset.sum_image]
    intro a _ b _ hab
    exact inv_injective hab
  exact ⟨E, hA.image Inv.inv, (hcard.trans (Finset.sum_le_sum (fun g _ => hbound g))).trans_lt hsum⟩

variable [MetricSpace G] [IsIsometricSMul G G]

theorem mem_finiteMetricNeighborhood
    (hfinite : ∀ R : ℝ, (Metric.closedBall (1 : G) R).Finite)
    (E : Finset G) (R : ℝ) (x : G) :
    x ∈ finiteMetricNeighborhood hfinite E R ↔ ∃ p ∈ E, dist x p ≤ R := by
  constructor
  · intro hx
    obtain ⟨g, hg, hxg⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hxg
    refine ⟨p, hp, ?_⟩
    have hg' : dist g 1 ≤ R := (hfinite R).mem_toFinset.mp hg
    simpa only [mul_one] using (dist_mul_left p g (1 : G)).trans_le hg'
  · rintro ⟨p, hp, hd⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨p⁻¹ * x, (hfinite R).mem_toFinset.mpr ?_, ?_⟩
    · change dist (p⁻¹ * x) 1 ≤ R
      have he : dist (p⁻¹ * x) 1 = dist x p := by
        simpa only [mul_one, mul_inv_cancel_left] using
          (dist_mul_left p (p⁻¹ * x) (1 : G)).symm
      rw [he]
      exact hd
    · exact Finset.mem_image.mpr ⟨p, hp, mul_inv_cancel_left p x⟩

omit [IsIsometricSMul G G] in
theorem exists_small_metricNeighborhood (M : InvariantMean G)
    (hfinite : ∀ R : ℝ, (Metric.closedBall (1 : G) R).Finite)
    (R : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ E : Finset G, E.Nonempty ∧
      ((finiteMetricNeighborhood hfinite E R \ E).card : ℝ) < ε * E.card :=
  exists_small_rightExpansion M _ hε

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_SourceMetricFolner
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.height_quotient_commutative _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesHomology _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One source Følner sequence works for every metric radius -/

noncomputable section

namespace PolycyclicRecognition

open ThompsonNonamenability Filter Metric
open scoped Topology

variable {G : Type*} [Group G] [MetricSpace G] [IsIsometricSMul G G] [DecidableEq G]

theorem finiteMetricNeighborhood_mono
    (hfinite : ∀ R : ℝ, (closedBall (1 : G) R).Finite)
    (E : Finset G) {R S : ℝ} (hRS : R ≤ S) :
    finiteMetricNeighborhood hfinite E R ⊆ finiteMetricNeighborhood hfinite E S := by
  intro x hx
  obtain ⟨p, hp, hd⟩ := (mem_finiteMetricNeighborhood hfinite E R x).mp hx
  exact (mem_finiteMetricNeighborhood hfinite E S x).mpr ⟨p, hp, hd.trans hRS⟩

theorem exists_sourceMetricFolner_sequence (M : InvariantMean G)
    (hfinite : ∀ R : ℝ, (closedBall (1 : G) R).Finite) :
    ∃ E : ℕ → Finset G, (∀ n, (E n).Nonempty) ∧
      ∀ R : ℝ, Tendsto
        (fun n => ((finiteMetricNeighborhood hfinite (E n) R \ E n).card : ℝ) / (E n).card)
        atTop (𝓝 0) := by
  have hex (n : ℕ) : ∃ E : Finset G, E.Nonempty ∧
      ((finiteMetricNeighborhood hfinite E n \ E).card : ℝ) <
        (1 / ((n : ℝ) + 1)) * E.card :=
    exists_small_metricNeighborhood M hfinite n (by positivity)
  choose E hE hsmall using hex
  refine ⟨E, hE, fun R => ?_⟩
  obtain ⟨N, hN⟩ := exists_nat_ge R
  have hupper : ∀ᶠ n : ℕ in atTop,
      ((finiteMetricNeighborhood hfinite (E n) R \ E n).card : ℝ) / (E n).card ≤
        1 / ((n : ℝ) + 1) := by
    filter_upwards [eventually_ge_atTop N] with n hn
    have hRn : R ≤ (n : ℝ) := hN.trans (by exact_mod_cast hn)
    have hc : (finiteMetricNeighborhood hfinite (E n) R \ E n).card ≤
        (finiteMetricNeighborhood hfinite (E n) n \ E n).card :=
      Finset.card_le_card (by
        intro x hx
        obtain ⟨hx, hxE⟩ := Finset.mem_sdiff.mp hx
        exact Finset.mem_sdiff.mpr
          ⟨finiteMetricNeighborhood_mono hfinite (E n) hRn hx, hxE⟩)
    apply (div_le_iff₀ (by exact_mod_cast (hE n).card_pos)).mpr
    have hcr : ((finiteMetricNeighborhood hfinite (E n) R \ E n).card : ℝ) ≤
        (finiteMetricNeighborhood hfinite (E n) n \ E n).card := by exact_mod_cast hc
    exact hcr.trans (hsmall n).le
  exact squeeze_zero' (Eventually.of_forall (fun _ => by positivity)) hupper
    tendsto_one_div_add_atTop_nhds_zero_nat

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_MetricFolnerMean
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instNonemptyBases _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.height_quotient_commutative _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesHomology _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A discrete metric Følner sequence gives the height-correction mean -/

noncomputable section

namespace PolycyclicRecognition

open ThompsonNonamenability Metric Filter
open scoped Topology symmDiff

variable {G : Type*} [Group G] [MetricSpace G] [IsIsometricSMul G G] [DecidableEq G]

theorem inverse_boundaryRatio_le_metricBoundary
    (hfinite : ∀ R : ℝ, (closedBall (1 : G) R).Finite)
    (E : Finset G) (g : G) :
    boundaryRatio (E.image Inv.inv) g ≤
      2 * (((finiteMetricNeighborhood hfinite E (dist (1 : G) g⁻¹) \ E).card : ℝ) / E.card) := by
  let F := E.image (· * g⁻¹)
  let N := finiteMetricNeighborhood hfinite E (dist (1 : G) g⁻¹)
  have hFcard : F.card = E.card :=
    Finset.card_image_of_injective E (fun _ _ h => mul_right_cancel h)
  have hFN : F ⊆ N := by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
    apply (mem_finiteMetricNeighborhood hfinite E _ _).mpr
    refine ⟨p, hp, ?_⟩
    have he := dist_mul_left p g⁻¹ (1 : G)
    simpa only [mul_one, dist_comm] using he.le
  have hd : (F \ E).card ≤ (N \ E).card := Finset.card_le_card (by
    intro x hx
    obtain ⟨hx, hxE⟩ := Finset.mem_sdiff.mp hx
    exact Finset.mem_sdiff.mpr ⟨hFN hx, hxE⟩)
  have heq : (F \ E).card = (E \ F).card := Finset.card_sdiff_comm hFcard
  have hc : (F ∆ E).card ≤ 2 * (N \ E).card := by
    have hu : (F ∆ E).card ≤ (F \ E).card + (E \ F).card := Finset.card_union_le _ _
    omega
  have hleft : (_root_.OAI.ThompsonNonamenability.leftTranslate g (E.image Inv.inv)).image Inv.inv = F := by
    simp only [_root_.OAI.ThompsonNonamenability.leftTranslate, Finset.image_image, Function.comp_def, mul_inv_rev, inv_inv, F]
  have hinv : (E.image Inv.inv).image Inv.inv = E := by
    ext x
    simp
  have hcs : (_root_.OAI.ThompsonNonamenability.leftTranslate g (E.image Inv.inv) ∆ E.image Inv.inv).card = (F ∆ E).card := by
    rw [← Finset.card_image_of_injective _
      (inv_injective : Function.Injective (fun x : G => x⁻¹)),
      Finset.image_symmDiff _ _ inv_injective, hleft, hinv]
  unfold boundaryRatio
  rw [hcs, Finset.card_image_of_injective E inv_injective]
  have hcr : ((F ∆ E).card : ℝ) ≤ 2 * ((N \ E).card : ℝ) := by exact_mod_cast hc
  calc
    ((F ∆ E).card : ℝ) / E.card ≤ (2 * ((N \ E).card : ℝ)) / E.card := by
      exact div_le_div_of_nonneg_right hcr (Nat.cast_nonneg _)
    _ = 2 * (((N \ E).card : ℝ) / E.card) := by ring

theorem invariantMean_of_metricBoundary_sequence
    (hfinite : ∀ R : ℝ, (closedBall (1 : G) R).Finite)
    (E : ℕ → Finset G) (hE : ∀ n, (E n).Nonempty)
    (hlim : ∀ R : ℝ, 0 ≤ R → Tendsto
      (fun n => ((finiteMetricNeighborhood hfinite (E n) R \ E n).card : ℝ) / (E n).card)
      atTop (𝓝 0)) : Nonempty (InvariantMean G) := by
  apply exists_invariantMean_of_folner_net (l := atTop) (fun n => (E n).image Inv.inv)
    (fun n => (hE n).image Inv.inv)
  intro g
  apply squeeze_zero (fun n => boundaryRatio_nonneg ((E n).image Inv.inv) g)
    (fun n => inverse_boundaryRatio_le_metricBoundary hfinite (E n) g)
  simpa only [mul_zero] using (hlim (dist (1 : G) g⁻¹) dist_nonneg).const_mul 2

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_MetricFolnerCount
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.height_quotient_commutative _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesHomology _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.meanCorrection_one _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.smallCoefficientRealCoinvariantMean_one _root_.OAI.PolycyclicRecognition.smallCoefficientRealMean_one _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.OAI.PolycyclicRecognition.vectorMeanCorrection_one _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Counting measure converts metric Følner sets to invariant means -/

noncomputable section

namespace PolycyclicRecognition

open ThompsonNonamenability Metric MeasureTheory Filter Set
open scoped Topology ENNReal

variable {G : Type*} [Group G] [MetricSpace G] [IsIsometricSMul G G] [DecidableEq G]

theorem coe_finiteMetricNeighborhood
    (hfinite : ∀ R : ℝ, (closedBall (1 : G) R).Finite)
    (E : Finset G) {R : ℝ} (hR : 0 ≤ R) :
    (↑(finiteMetricNeighborhood hfinite E R) : Set G) = cthickening R (E : Set G) := by
  rw [E.finite_toSet.isCompact.cthickening_eq_biUnion_closedBall hR]
  ext x
  simp only [Finset.mem_coe, mem_finiteMetricNeighborhood, Set.mem_iUnion, mem_closedBall,
    exists_prop]

variable [MeasurableSpace G] [BorelSpace G]

theorem invariantMean_of_countMetricFolner
    (hfinite : ∀ R : ℝ, (closedBall (1 : G) R).Finite)
    (A : ℕ → Set G) (hzero : ∀ n, Measure.count (A n) ≠ 0)
    (hfin : ∀ n, Measure.count (A n) ≠ ∞)
    (hratio : ∀ R : ℝ, 0 ≤ R →
      Tendsto (fun n => Measure.count (cthickening R (A n)) / Measure.count (A n))
        atTop (𝓝 1)) : Nonempty (InvariantMean G) := by
  have hA (n : ℕ) : (A n).Finite :=
    Measure.count_apply_lt_top.mp (lt_top_iff_ne_top.mpr (hfin n))
  let E := fun n => (hA n).toFinset
  have hEset (n : ℕ) : (↑(E n) : Set G) = A n := (hA n).coe_toFinset
  have hE (n : ℕ) : (E n).Nonempty := by
    apply Finset.coe_nonempty.mp
    rw [hEset]
    exact Measure.count_ne_zero_iff.mp (hzero n)
  apply invariantMean_of_metricBoundary_sequence hfinite E hE
  intro R hR
  let N := fun n => finiteMetricNeighborhood hfinite (E n) R
  have hNset (n : ℕ) : (↑(N n) : Set G) = cthickening R (A n) := by
    rw [← hEset n]
    exact coe_finiteMetricNeighborhood hfinite (E n) hR
  have hN (n : ℕ) : E n ⊆ N n := by
    intro p hp
    exact (mem_finiteMetricNeighborhood hfinite (E n) R p).mpr ⟨p, hp, by simpa using hR⟩
  have heq (n : ℕ) :
      (Measure.count (cthickening R (A n)) / Measure.count (A n)).toReal =
        ((N n).card : ℝ) / (E n).card := by
    rw [← hNset n, ← hEset n, Measure.count_apply_finset, Measure.count_apply_finset,
      ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_natCast]
  have ht : Tendsto (fun n => ((N n).card : ℝ) / (E n).card) atTop (𝓝 1) := by
    have h := (ENNReal.tendsto_toReal (by simp : (1 : ℝ≥0∞) ≠ ∞)).comp (hratio R hR)
    simpa only [Function.comp_def, heq, ENNReal.toReal_one] using h
  have hdiff (n : ℕ) : ((N n \ E n).card : ℝ) / (E n).card =
      ((N n).card : ℝ) / (E n).card - 1 := by
    have hc : ((N n \ E n).card : ℝ) + (E n).card = (N n).card := by
      exact_mod_cast Finset.card_sdiff_add_card_eq_card (hN n)
    have hne : ((E n).card : ℝ) ≠ 0 := (Nat.cast_pos.mpr (hE n).card_pos).ne'
    field_simp [hne]
    linarith
  simpa only [← hdiff, sub_self] using ht.sub_const 1

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_FolnerRatio
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.height_quotient_commutative _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesHomology _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Passing from a boundary estimate to a volume ratio -/

namespace PolycyclicRecognition

open Filter
open scoped Topology

theorem tendsto_ratio_one_of_boundary
    {ι : Type*} {l : Filter ι} (A N s b : ι → ℝ) {α β : ℝ}
    (hα : 0 < α) (hβ : 0 ≤ β)
    (hs : ∀ i, 0 < s i) (hb : ∀ i, 0 ≤ b i)
    (hlower : ∀ i, α * s i ≤ A i)
    (hmono : ∀ i, A i ≤ N i) (hupper : ∀ i, N i ≤ A i + β * b i)
    (hlim : Tendsto (fun i => b i / s i) l (𝓝 0)) :
    Tendsto (fun i => N i / A i) l (𝓝 1) := by
  have hA (i : ι) : 0 < A i := (mul_pos hα (hs i)).trans_le (hlower i)
  have hbound (i : ι) : N i / A i - 1 ≤ (β / α) * (b i / s i) := by
    calc
      N i / A i - 1 = (N i - A i) / A i := by field_simp [(hA i).ne']
      _ ≤ (β * b i) / A i :=
        div_le_div_of_nonneg_right (by linarith [hupper i]) (hA i).le
      _ ≤ (β * b i) / (α * s i) :=
        div_le_div_of_nonneg_left (mul_nonneg hβ (hb i)) (mul_pos hα (hs i)) (hlower i)
      _ = (β / α) * (b i / s i) := by ring
  have hz : Tendsto (fun i => N i / A i - 1) l (𝓝 0) := by
    apply squeeze_zero (fun i => sub_nonneg.mpr ((one_le_div (hA i)).mpr (hmono i))) hbound
    simpa only [mul_zero] using hlim.const_mul (β / α)
  simpa only [sub_add_cancel, zero_add] using hz.add_const 1

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_LowerPacking
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.height_quotient_commutative _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesHomology _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Lower packing bounds from Haar volume

A totally bounded endpoint set has a finite separated net. Its volume is
at most the cardinality of that net times the mass of a fixed-radius ball.
This is the lower packing estimate used after stationary mesh selection.
-/

noncomputable section

open Metric Set MeasureTheory
open scoped ENNReal

namespace PolycyclicRecognition

/-- A totally bounded set admits a finite separated net with its centers
inside the set. The set itself need not be closed or measurable. -/
theorem exists_separated_net_of_totallyBounded
    {X : Type*} [PseudoMetricSpace X] {S : Set X} (hS : TotallyBounded S)
    {r : ℝ} (hr : 0 < r) :
    ∃ t : Finset X, (↑t : Set X) ⊆ S ∧
      (∀ x ∈ t, ∀ y ∈ t, x ≠ y → r < dist x y) ∧
      ∀ x ∈ S, ∃ y ∈ t, dist x y ≤ r := by
  classical
  obtain ⟨U, _hUS, hUfin, hUcover⟩ := finite_approx_of_totallyBounded hS (r / 3) (by positivity)
  let u := hUfin.toFinset
  have hbound (t : Finset X) (ht : (↑t : Set X) ⊆ S)
      (hsep : ∀ x ∈ t, ∀ y ∈ t, x ≠ y → r < dist x y) : t.card ≤ u.card := by
    have hchoice (x : {x // x ∈ t}) : ∃ y : {y // y ∈ u}, dist x.val y.val < r / 3 := by
      obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (hUcover (ht x.property))
      exact ⟨⟨y, hUfin.mem_toFinset.mpr hy⟩, Metric.mem_ball.mp hxy⟩
    choose c hc using hchoice
    have hinj : Function.Injective c := by
      intro x y hxy
      apply Subtype.ext
      by_contra hne
      have hdist : dist x.val y.val < r := by
        calc
          dist x.val y.val ≤ dist x.val (c x).val + dist (c x).val y.val := dist_triangle _ _ _
          _ = dist x.val (c x).val + dist y.val (c y).val := by rw [hxy, dist_comm (c y).val]
          _ < r := by linarith [hc x, hc y]
      exact (not_lt_of_ge hdist.le) (hsep x.val x.property y.val y.property hne)
    simpa only [Fintype.card_coe] using Fintype.card_le_of_injective c hinj
  obtain ⟨t, ht, hsep, _hcard, hcover⟩ :=
    finite_separated_cover_set_of_bound S hr.le u.card hbound
  exact ⟨t, ht, hsep, hcover⟩

variable {G : Type*} [Group G] [MetricSpace G] [MeasurableSpace G]
  [BorelSpace G] [MeasurableMul G] [IsIsometricSMul G G]

omit [BorelSpace G] in
/-- Haar mass of a closed ball is independent of its center. -/
theorem measure_closedBall_eq_identity (μ : Measure G) [μ.IsMulLeftInvariant]
    (x : G) (r : ℝ) : μ (closedBall x r) = μ (closedBall (1 : G) r) := by
  have h := measure_preimage_mul μ x (closedBall x r)
  rw [preimage_mul_left_closedBall, inv_mul_cancel] at h
  exact h.symm

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_MetricFolnerVolume
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.height_quotient_commutative _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesHomology _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The volume estimates in metric Følner transfer

A finite union of fixed-radius target balls has mass bounded below by its
source cardinality, using a separated net and bounded coarse multiplicity.
Its metric boundary is covered by balls indexed by the source boundary.
-/

noncomputable section

namespace PolycyclicRecognition

open Metric Set MeasureTheory
open scoped ENNReal

theorem metricFolnerSet_measurable {X Y : Type*} [PseudoMetricSpace Y]
    [MeasurableSpace Y] [BorelSpace Y] (u : X → Y) (E : Finset X) (a : ℝ) :
    MeasurableSet (metricFolnerSet u E a) :=
  E.finite_toSet.measurableSet_biUnion (fun _ _ => measurableSet_ball)

theorem metricFolnerSet_volume_lower
    {X Y : Type*} [Group Y] [MetricSpace Y] [MeasurableSpace Y]
    [BorelSpace Y] [MeasurableMul Y] [IsIsometricSMul Y Y]
    (μ : Measure Y) [μ.IsMulLeftInvariant] (u : X → Y) (E : Finset X)
    {a : ℝ} (ha : 0 < a) (M : ℕ)
    (hmult : ∀ (y : Y) (A : Finset X),
      (∀ x ∈ A, dist (u x) y ≤ a + a) → A.card ≤ M) :
    (E.card : ℝ≥0∞) * μ (ball (1 : Y) a) ≤
      (M : ℝ≥0∞) * μ (metricFolnerSet u E a) := by
  classical
  obtain ⟨t, ht, hsep, hcover⟩ := exists_separated_net_of_totallyBounded
    (E.image u).finite_toSet.isCompact.totallyBounded (add_pos ha ha)
  have hc : E.card ≤ t.card * M :=
    card_le_cover_mul_of_bounded_multiplicity E u t (a + a) M
      (fun x hx => hcover (u x) (Finset.mem_image.mpr ⟨x, hx, rfl⟩)) hmult
  have hv : (t.card : ℝ≥0∞) * μ (ball (1 : Y) a) ≤ μ (metricFolnerSet u E a) := by
    apply separated_card_mul_ball_le μ t a _
      (fun x hx y hy hxy => (hsep x hx y hy hxy).le)
    intro y hy z hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp (ht hy)
    exact Set.mem_iUnion₂.mpr ⟨x, hx, hz⟩
  have hc' : (E.card : ℝ≥0∞) ≤ (t.card : ℝ≥0∞) * M := by exact_mod_cast hc
  calc
    (E.card : ℝ≥0∞) * μ (ball (1 : Y) a) ≤
        ((t.card : ℝ≥0∞) * M) * μ (ball (1 : Y) a) := by gcongr
    _ = (M : ℝ≥0∞) * ((t.card : ℝ≥0∞) * μ (ball (1 : Y) a)) := by ac_rfl
    _ ≤ _ := by gcongr

theorem metricFolnerSet_boundary_subset
    {X Y : Type*} [Group X] [MetricSpace X] [IsIsometricSMul X X]
    [PseudoMetricSpace Y] [DecidableEq X]
    (hfinite : ∀ R : ℝ, (closedBall (1 : X) R).Finite)
    (u : X → Y) (E : Finset X) {a c K C R : ℝ}
    (hca : c < a) (hK : 0 ≤ K) (hR : 0 ≤ R)
    (hsurj : ∀ y, ∃ q, dist y (u q) ≤ c)
    (hlower : ∀ x y, dist x y ≤ K * dist (u x) (u y) + C) :
    cthickening R (metricFolnerSet u E a) \ metricFolnerSet u E a ⊆
      ⋃ q ∈ finiteMetricNeighborhood hfinite E (K * (c + (R + 1) + a) + C) \ E,
        closedBall (u q) c := by
  rintro y ⟨hy, hyout⟩
  have hy' : y ∈ thickening (R + 1) (metricFolnerSet u E a) :=
    cthickening_subset_thickening' (by linarith) (by linarith) _ hy
  obtain ⟨z, hz, hyz⟩ := mem_thickening_iff.mp hy'
  obtain ⟨p, hp, hzp⟩ := Set.mem_iUnion₂.mp hz
  obtain ⟨q, hyq⟩ := hsurj y
  have hqnot : q ∉ E := by
    intro hq
    apply hyout
    exact Set.mem_iUnion₂.mpr ⟨q, hq, lt_of_le_of_lt hyq hca⟩
  have hqp : dist q p ≤ K * (c + (R + 1) + a) + C := by
    apply (hlower q p).trans
    apply add_le_add (mul_le_mul_of_nonneg_left _ hK) le_rfl
    calc
      dist (u q) (u p) ≤ dist (u q) y + dist y (u p) := dist_triangle _ _ _
      _ ≤ dist (u q) y + (dist y z + dist z (u p)) := by
        gcongr
        exact dist_triangle _ _ _
      _ ≤ c + (R + 1) + a := by
        rw [dist_comm (u q) y]
        have hzp' : dist z (u p) < a := hzp
        linarith
  exact Set.mem_iUnion₂.mpr ⟨q,
    Finset.mem_sdiff.mpr ⟨(mem_finiteMetricNeighborhood hfinite E _ q).mpr ⟨p, hp, hqp⟩,
      hqnot⟩, hyq⟩

theorem metricFolnerSet_boundary_volume
    {X Y : Type*} [Group X] [MetricSpace X] [IsIsometricSMul X X]
    [Group Y] [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    [MeasurableMul Y] [IsIsometricSMul Y Y] [DecidableEq X]
    (μ : Measure Y) [μ.IsMulLeftInvariant]
    (hfinite : ∀ R : ℝ, (closedBall (1 : X) R).Finite)
    (u : X → Y) (E : Finset X) {a c K C R : ℝ}
    (hca : c < a) (hK : 0 ≤ K) (hR : 0 ≤ R)
    (hsurj : ∀ y, ∃ q, dist y (u q) ≤ c)
    (hlower : ∀ x y, dist x y ≤ K * dist (u x) (u y) + C) :
    μ (cthickening R (metricFolnerSet u E a) \ metricFolnerSet u E a) ≤
      ((finiteMetricNeighborhood hfinite E (K * (c + (R + 1) + a) + C) \ E).card : ℝ≥0∞) *
        μ (closedBall (1 : Y) c) := by
  apply (measure_mono (metricFolnerSet_boundary_subset hfinite u E hca hK hR hsurj hlower)).trans
  apply (measure_biUnion_finset_le _ _).trans
  simp only [measure_closedBall_eq_identity, Finset.sum_const, nsmul_eq_mul, le_refl]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_MetricFolnerTransfer
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.height_quotient_commutative _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesHomology _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.meanCorrection_one _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.smallCoefficientRealCoinvariantMean_one _root_.OAI.PolycyclicRecognition.smallCoefficientRealMean_one _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.OAI.PolycyclicRecognition.vectorMeanCorrection_one _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual metric Følner transfer to a coarsely equivalent measured group -/

noncomputable section

namespace PolycyclicRecognition

open ThompsonNonamenability Metric MeasureTheory Filter Set
open scoped Topology ENNReal

variable {X Y : Type*} [Group X] [MetricSpace X] [IsIsometricSMul X X]
  [DecidableEq X] [Group Y] [MetricSpace Y] [ProperSpace Y]
  [MeasurableSpace Y] [BorelSpace Y] [MeasurableMul Y] [IsIsometricSMul Y Y]

theorem exists_metricFolner_sequence
    (M : InvariantMean X) (hfinite : ∀ R : ℝ, (closedBall (1 : X) R).Finite)
    (μ : Measure Y) [μ.IsMulLeftInvariant] [μ.IsOpenPosMeasure] [IsFiniteMeasureOnCompacts μ]
    (u : X → Y) {c K C : ℝ} (hc : 0 ≤ c) (hK : 0 ≤ K)
    (hsurj : ∀ y, ∃ q, dist y (u q) ≤ c)
    (hlower : ∀ x y, dist x y ≤ K * dist (u x) (u y) + C) :
    ∃ A : ℕ → Set Y,
      (∀ n, MeasurableSet (A n)) ∧ (∀ n, μ (A n) ≠ 0) ∧ (∀ n, μ (A n) ≠ ∞) ∧
      ∀ R : ℝ, 0 ≤ R → Tendsto (fun n => μ (cthickening R (A n)) / μ (A n))
        atTop (𝓝 1) := by
  classical
  let a := c + 1
  have ha : 0 < a := by dsimp [a] <;> linarith
  have hca : c < a := by dsimp [a] <;> linarith
  obtain ⟨E, hE, hlim⟩ := exists_sourceMetricFolner_sequence M hfinite
  obtain ⟨m, hm⟩ := exists_uniform_ball_multiplicity (r := a + a) u hfinite hK hlower
  let m' := m + 1
  have hmpos : 0 < (m' : ℝ) := by dsimp [m'] <;> positivity
  have hm' : ∀ (y : Y) (F : Finset X),
      (∀ x ∈ F, dist (u x) y ≤ a + a) → F.card ≤ m' :=
    fun y F hF => (hm y F hF).trans (Nat.le_succ m)
  let A := fun n => metricFolnerSet u (E n) a
  have hAfin (n : ℕ) : μ (A n) ≠ ∞ := by
    exact measure_biUnion_ne_top (E n).finite_toSet (fun _ _ => measure_ball_ne_top)
  have hApos (n : ℕ) : 0 < μ (A n) := by
    obtain ⟨p, hp⟩ := hE n
    exact (measure_ball_pos μ (u p) ha).trans_le (measure_mono (by
      intro y hy
      exact Set.mem_iUnion₂.mpr ⟨p, hp, hy⟩))
  have hameas (n : ℕ) : MeasurableSet (A n) := metricFolnerSet_measurable u (E n) a
  let b := μ.real (ball (1 : Y) a)
  have hbpos : 0 < b :=
    ENNReal.toReal_pos (measure_ball_pos μ 1 ha).ne' measure_ball_ne_top
  have hlowerA (n : ℕ) : (b / m') * (E n).card ≤ μ.real (A n) := by
    have hv := metricFolnerSet_volume_lower μ u (E n) ha m' hm'
    have hr := ENNReal.toReal_mono (ENNReal.mul_ne_top (by simp) (hAfin n)) hv
    simp only [ENNReal.toReal_mul, ENNReal.toReal_natCast] at hr
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hmpos).mpr
    simpa only [b, Measure.real, mul_comm] using hr
  refine ⟨A, hameas, fun n => (hApos n).ne', hAfin, fun R hR => ?_⟩
  let S := K * (c + (R + 1) + a) + C
  let B := fun n => finiteMetricNeighborhood hfinite (E n) S \ E n
  let β := μ.real (closedBall (1 : Y) c)
  have hbound (n : ℕ) : μ (cthickening R (A n) \ A n) ≤
      ((B n).card : ℝ≥0∞) * μ (closedBall (1 : Y) c) :=
    metricFolnerSet_boundary_volume μ hfinite u (E n) hca hK hR hsurj hlower
  have hbdFin (n : ℕ) : μ (cthickening R (A n) \ A n) ≠ ∞ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) measure_closedBall_lt_top.ne) (hbound n)
  have hsplit (n : ℕ) : μ (cthickening R (A n)) =
      μ (cthickening R (A n) \ A n) + μ (A n) := by
    have h := measure_sdiff_add_inter (μ := μ) (cthickening R (A n)) (hameas n)
    rw [Set.inter_eq_right.mpr (self_subset_cthickening (A n))] at h
    exact h.symm
  have hNfin (n : ℕ) : μ (cthickening R (A n)) ≠ ∞ := by
    rw [hsplit n]
    exact ENNReal.add_ne_top.mpr ⟨hbdFin n, hAfin n⟩
  have hupper (n : ℕ) : μ.real (cthickening R (A n)) ≤
      μ.real (A n) + β * (B n).card := by
    have hr := ENNReal.toReal_mono
      (ENNReal.mul_ne_top (by simp) measure_closedBall_lt_top.ne) (hbound n)
    simp only [ENNReal.toReal_mul, ENNReal.toReal_natCast] at hr
    change (μ (cthickening R (A n))).toReal ≤ _
    rw [hsplit n, ENNReal.toReal_add (hbdFin n) (hAfin n)]
    dsimp only [Measure.real, β]
    linarith
  have hreal : Tendsto (fun n => μ.real (cthickening R (A n)) / μ.real (A n))
      atTop (𝓝 1) := by
    apply tendsto_ratio_one_of_boundary _ _ (fun n => ((E n).card : ℝ))
      (fun n => ((B n).card : ℝ)) (div_pos hbpos hmpos) ENNReal.toReal_nonneg
      (fun n => by exact_mod_cast (hE n).card_pos) (fun _ => Nat.cast_nonneg _)
      hlowerA _ hupper (hlim S)
    intro n
    exact measureReal_mono (self_subset_cthickening (A n)) (hNfin n)
  have heq (n : ℕ) : ENNReal.ofReal (μ.real (cthickening R (A n)) / μ.real (A n)) =
      μ (cthickening R (A n)) / μ (A n) := by
    change ENNReal.ofReal ((μ (cthickening R (A n))).toReal / (μ (A n)).toReal) = _
    rw [ENNReal.ofReal_div_of_pos (ENNReal.toReal_pos (hApos n).ne' (hAfin n))]
    rw [ENNReal.ofReal_toReal (hNfin n), ENNReal.ofReal_toReal (hAfin n)]
  simpa only [Function.comp_def, heq, ENNReal.ofReal_one] using
    ENNReal.continuous_ofReal.continuousAt.tendsto.comp hreal

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_CoarseModelMean
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.height_quotient_commutative _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesHomology _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Amenability of the discrete group in the recognition argument -/

noncomputable section

namespace PolycyclicRecognition

open ThompsonNonamenability Metric MeasureTheory

theorem invariantMean_of_coarse_virtualPolycyclic
    {P H : Type*} [Group P] [MetricSpace P] [IsIsometricSMul P P] [DecidableEq P]
    [Group H] [MetricSpace H] [DiscreteTopology H] [IsIsometricSMul H H]
    [ProperSpace H] [MeasurableSpace H] [BorelSpace H] [MeasurableMul H] [DecidableEq H]
    (hP : IsVirtuallyPolycyclic P)
    (hfinite : ∀ R : ℝ, (closedBall (1 : P) R).Finite)
    (u : P → H) {c K C : ℝ} (hc : 0 ≤ c) (hK : 0 ≤ K)
    (hsurj : ∀ y, ∃ p, dist y (u p) ≤ c)
    (hlower : ∀ x y, dist x y ≤ K * dist (u x) (u y) + C) :
    Nonempty (InvariantMean H) := by
  let : (Measure.count : Measure H).IsOpenPosMeasure :=
    ⟨fun _ _ hU => Measure.count_ne_zero hU⟩
  let : IsFiniteMeasureOnCompacts (Measure.count : Measure H) :=
    ⟨by intro K hK; exact Measure.count_apply_lt_top.mpr hK.finite_of_discrete⟩
  obtain ⟨A, _hA, hzero, hfin, hratio⟩ := exists_metricFolner_sequence
    (invariantMean_of_isVirtuallyPolycyclic hP).some hfinite Measure.count u hc hK hsurj hlower
  exact invariantMean_of_countMetricFolner
    (fun R => (isCompact_closedBall (1 : H) R).finite_of_discrete)
    A hzero hfin hratio

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_MetricQuasiEquivalence
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.height_quotient_commutative _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesHomology _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Composing the metric comparisons in a Lie-model reduction

The proper cocompact homomorphism reduction has arrows in both directions.
We keep actual coarse inverse maps and their affine bounds, so that the
three-arrow zigzag can be composed without assuming a recognition result.
-/

noncomputable section

namespace PolycyclicRecognition

namespace MetricQuasiEquivalence

variable {X Y Z : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y] [PseudoMetricSpace Z]

/-- Recover the usual inequalities from actual coarse inverse maps. -/
theorem quasiIsometry_toFun (e : MetricQuasiEquivalence X Y) :
    ∃ K C K' C' E : ℝ, 0 ≤ K ∧ 0 ≤ C ∧ 0 ≤ K' ∧ 0 ≤ C' ∧ 0 ≤ E ∧
      (∀ x y, dist (e.toFun x) (e.toFun y) ≤ K * dist x y + C) ∧
      (∀ x y, dist x y ≤ K' * dist (e.toFun x) (e.toFun y) + C') ∧
      (∀ y, ∃ x, dist y (e.toFun x) ≤ E) := by
  obtain ⟨K, C, hK, hC, hf⟩ := e.toFun_control
  obtain ⟨K', C', hK', hC', hr⟩ := e.invFun_control
  obtain ⟨L, hL, hl⟩ := e.left_close
  obtain ⟨E, hE, he⟩ := e.right_close
  refine ⟨K, C, K', C' + (L + L), E, hK, hC, hK',
    add_nonneg hC' (add_nonneg hL hL), hE, hf, ?_, fun y => ⟨e.invFun y, he y⟩⟩
  intro x y
  calc
    dist x y ≤ dist x (e.invFun (e.toFun x)) +
        dist (e.invFun (e.toFun x)) (e.invFun (e.toFun y)) +
          dist (e.invFun (e.toFun y)) y := dist_triangle4 _ _ _ _
    _ ≤ L + (K' * dist (e.toFun x) (e.toFun y) + C') + L := by
      exact add_le_add (add_le_add (hl x) (hr _ _)) ((dist_comm _ _).trans_le (hl y))
    _ = K' * dist (e.toFun x) (e.toFun y) + (C' + (L + L)) := by ring

end MetricQuasiEquivalence

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Lattices_RecognitionLatticeAssembly
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.height_quotient_commutative _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesHomology _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Recognition from bounded-height hypotheses

Metric comparison with the virtually polycyclic group supplies the invariant
mean and the cohomological coarse comparison.

The conditional recognition theorems retain polynomial bounded-height packing
and a uniform affine height estimate as explicit geometric hypotheses.
-/

noncomputable section

namespace PolycyclicRecognition

namespace MetricQuasiEquivalence

variable {P H : Type} [Group P] [Group H] [MetricSpace P] [MetricSpace H]
  [IsIsometricSMul P P] [IsIsometricSMul H H]

/-- Amenability is derived from the original comparison group and the
actual metric comparison, rather than assumed for the recognized group. -/
theorem invariantMean_of_virtuallyPolycyclic
    [DiscreteTopology H] [ProperSpace H]
    [MeasurableSpace H] [BorelSpace H] [MeasurableMul H]
    (e : MetricQuasiEquivalence P H) (hP : IsVirtuallyPolycyclic P)
    (hPfinite : ∀ R : ℝ, (Metric.closedBall (1 : P) R).Finite) :
    Nonempty (ThompsonNonamenability.InvariantMean H) := by
  classical
  obtain ⟨_, _, K', _, E, _, _, hK', _, hE, _, hlower, hsurj⟩ :=
    e.quasiIsometry_toFun
  exact invariantMean_of_coarse_virtualPolycyclic hP hPfinite e.toFun hE hK'
    hsurj hlower

end MetricQuasiEquivalence

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_NormalizedPairHeightTransfer
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.height_quotient_commutative _root_.OAI.PolycyclicRecognition.instFiniteRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.instNonemptyRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.inversePairCoupling_finiteOnCompacts _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.normalizedPair_polishSpace _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesHomology _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Passing bounded height from normalized representatives to coarse maps -/

noncomputable section
namespace PolycyclicRecognition

open scoped NNReal

variable {G W P I B₀ : Type*} [Group G] [MetricSpace G] [ProperSpace G]
  [IsTopologicalGroup G] [IsIsometricSMul G G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  [Fintype I] [Fintype B₀] [Nonempty B₀]

omit [ProperSpace G] in
/-- Bounded perturbations of both evaluation points cost at most twice
the height-Lipschitz constant times the perturbation radius. No continuity
of the original coarse maps is used. -/
theorem uniform_affine_height_of_bounded_pair_representatives
    (D : SupportDatum W I B₀) (π : G →* Multiplicative W)
    {L : ℝ} (hL : 0 ≤ L)
    (hπ : ∀ x y, ‖(π x).toAdd - (π y).toAdd‖ ≤ L * dist x y)
    {Λ : ℝ≥0} (label : NormalizedPair G Λ → templateSymmetryGroup D)
    {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ p x, ‖(π (p.val.1 x)).toAdd - (label p).val (π x).toAdd‖ ≤ K)
    (f : P → G → G) (rep : P → C(G, G) × C(G, G))
    (hrep : ∀ p, LipschitzPairBounds G Λ (rep p))
    {E : ℝ} (hE : 0 ≤ E) (hclose : ∀ p x, dist ((rep p).1 x) (f p x) ≤ E) :
    ∃ (A : P → templateSymmetryGroup D) (B : ℝ), 0 ≤ B ∧ ∀ p x,
      ‖(π (f p x)).toAdd - ((π (f p 1)).toAdd + (A p).val (π x).toAdd)‖ ≤ B := by
  let q := fun p => normalizePair (rep p) (hrep p)
  let A := fun p => label (q p)
  have hb (p : P) (x : G) :
      ‖(π ((rep p).1 x)).toAdd - (π ((rep p).1 1)).toAdd -
        (A p).val (π x).toAdd‖ ≤ K := by
    have h := hbound (q p) x
    change ‖(π (((rep p).1 1)⁻¹ * (rep p).1 (1 * x))).toAdd -
      (A p).val (π x).toAdd‖ ≤ K at h
    simpa only [one_mul, map_mul, map_inv, toAdd_mul, toAdd_inv, neg_add_eq_sub] using h
  refine ⟨A, K + 2 * L * E, by positivity, ?_⟩
  intro p x
  have hx : ‖(π (f p x)).toAdd - (π ((rep p).1 x)).toAdd‖ ≤ L * E := by
    exact (hπ _ _).trans (mul_le_mul_of_nonneg_left
      (by simpa only [dist_comm] using hclose p x) hL)
  have h1 : ‖(π ((rep p).1 1)).toAdd - (π (f p 1)).toAdd‖ ≤ L * E :=
    (hπ _ _).trans (mul_le_mul_of_nonneg_left (hclose p 1) hL)
  calc
    _ = ‖((π (f p x)).toAdd - (π ((rep p).1 x)).toAdd) +
        ((π ((rep p).1 x)).toAdd - (π ((rep p).1 1)).toAdd - (A p).val (π x).toAdd) +
        ((π ((rep p).1 1)).toAdd - (π (f p 1)).toAdd)‖ := by congr 1; abel
    _ ≤ (‖(π (f p x)).toAdd - (π ((rep p).1 x)).toAdd‖ +
        ‖(π ((rep p).1 x)).toAdd - (π ((rep p).1 1)).toAdd - (A p).val (π x).toAdd‖) +
        ‖(π ((rep p).1 1)).toAdd - (π (f p 1)).toAdd‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ (L * E + K) + L * E := add_le_add (add_le_add hx (hb p x)) h1
    _ = K + 2 * L * E := by ring

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_UnitSeparatedNet
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.height_quotient_commutative _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesHomology _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The locally finite unit net used for Lipschitz replacement -/

noncomputable section
namespace PolycyclicRecognition

open Set Metric

variable {X : Type*} [MetricSpace X]

/-- A maximal unit-separated set covers the whole metric space by closed
unit balls. No measure or geometric input is required for this step. -/
theorem exists_unit_separated_net :
    ∃ V : Set X, V.Pairwise (fun x y => 1 < dist x y) ∧
      ∀ x : X, ∃ v ∈ V, dist x v ≤ 1 := by
  classical
  obtain ⟨V, hV⟩ := zorn_subset {V : Set X | V.Pairwise (fun x y => 1 < dist x y)}
    (by
      intro C hC hc
      exact ⟨⋃₀ C, hc.pairwise_sUnion.mpr (fun s hs => hC hs), fun s hs => subset_sUnion_of_mem hs⟩)
  refine ⟨V, hV.1, ?_⟩
  intro x
  by_contra hn
  have hfar : ∀ v ∈ V, 1 < dist x v := by
    intro v hv
    exact lt_of_not_ge (fun h => hn ⟨v, hv, h⟩)
  have hi : (insert x V).Pairwise (fun y z => 1 < dist y z) := by
    rw [Set.pairwise_insert]
    exact ⟨hV.1, fun y hy _ => ⟨hfar y hy, by simpa only [dist_comm] using hfar y hy⟩⟩
  have hx : x ∈ V := hV.2 hi (subset_insert x V) (mem_insert x V)
  exact hn ⟨x, hx, by simp⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_UniformUnitNetBound
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.height_quotient_commutative _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesHomology _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform multiplicity of the unit-net cover

A finite cover of a compact ball at the identity bounds the number of
separated centers at every translate. This proves the multiplicity estimate
without needing a Haar-volume comparison.
-/

noncomputable section
namespace PolycyclicRecognition

open Set Metric

variable {G : Type*} [Group G] [MetricSpace G] [ProperSpace G]
  [IsIsometricSMul G G]

theorem exists_uniform_unit_net_card (R : ℝ) :
    ∃ M : ℕ, ∀ V : Set G, V.Pairwise (fun x y => 1 < dist x y) →
      ∀ x : G, (V ∩ closedBall x R).ncard ≤ M := by
  classical
  obtain ⟨C, hC, hcover⟩ := Metric.totallyBounded_iff.mp
    (isCompact_closedBall (1 : G) R).totallyBounded (1 / 3 : ℝ) (by norm_num)
  refine ⟨C.ncard, ?_⟩
  intro V hV x
  let U := V ∩ closedBall x R
  have hc (v : U) : ∃ c : C, dist (x⁻¹ * (v : G)) c < 1 / 3 := by
    have hv : x⁻¹ * (v : G) ∈ closedBall (1 : G) R := by
      change dist (x⁻¹ * (v : G)) 1 ≤ R
      calc
        _ = dist (v : G) x := by
          simpa only [inv_mul_cancel] using dist_mul_left x⁻¹ (v : G) x
        _ ≤ R := v.property.2
    rcases mem_iUnion.mp (hcover hv) with ⟨c, hc⟩
    rcases mem_iUnion.mp hc with ⟨hc, hv⟩
    exact ⟨⟨c, hc⟩, mem_ball.mp hv⟩
  choose c hc using hc
  have hinj : Function.Injective c := by
    intro v w he
    apply Subtype.ext
    by_contra hne
    have hsep := hV v.property.1 w.property.1 hne
    have ht := dist_triangle (x⁻¹ * (v : G)) (c v : G) (x⁻¹ * (w : G))
    have hv := hc v
    have hw := hc w
    rw [← he] at hw
    rw [dist_comm (c v : G) (x⁻¹ * (w : G)), dist_mul_left] at ht
    linarith
  let : Finite C := hC.to_subtype
  have hcard := Nat.card_le_card_of_injective c hinj
  simpa only [Nat.card_coe_set_eq] using hcard

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_UnitNetPartition
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.height_quotient_commutative _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesHomology _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finitely supported cutoff weights on the infinite unit net -/

noncomputable section
namespace PolycyclicRecognition

open Set Metric
open scoped BigOperators

variable {X : Type*} [MetricSpace X] [ProperSpace X]
  {V : Set X} (hV : V.Pairwise (fun x y => 1 < dist x y))

theorem mem_support_unitNetMass_iff (x : X) (v : V) :
    v ∈ (unitNetMass hV x).support ↔ dist x v < 2 := by
  rw [Finsupp.mem_support_iff, unitNetMass_apply]
  constructor
  · intro h
    by_contra hn
    exact h (max_eq_left (by linarith))
  · intro h he
    have := le_max_right (0 : ℝ) (2 - dist x v)
    rw [he] at this
    linarith

theorem unitNetMass_nonneg (x : X) (v : V) : 0 ≤ unitNetMass hV x v :=
  le_max_left _ _

theorem one_le_unitNetTotal (hcover : ∀ x : X, ∃ v ∈ V, dist x v ≤ 1) (x : X) :
    1 ≤ unitNetTotal hV x := by
  obtain ⟨v, hv, hd⟩ := hcover x
  have hp : 1 ≤ unitNetMass hV x ⟨v, hv⟩ := by
    exact (by linarith : 1 ≤ 2 - dist x v).trans (le_max_right _ _)
  have hm : (⟨v, hv⟩ : V) ∈ (unitNetMass hV x).support := by
    apply Finsupp.mem_support_iff.mpr
    linarith
  exact hp.trans (Finset.single_le_sum (fun i _ => unitNetMass_nonneg hV x i) hm)

theorem unitNetPartition_nonneg (x : X) (v : V) : 0 ≤ unitNetPartition hV x v :=
  mul_nonneg (inv_nonneg.mpr (Finset.sum_nonneg (fun i _ => unitNetMass_nonneg hV x i)))
    (unitNetMass_nonneg hV x v)

theorem unitNetPartition_total (hcover : ∀ x : X, ∃ v ∈ V, dist x v ≤ 1) (x : X) :
    (unitNetPartition hV x).sum (fun _ a => a) = 1 := by
  have ht : unitNetTotal hV x ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (one_le_unitNetTotal hV hcover x))
  rw [unitNetPartition, Finsupp.sum_smul_index' (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)]
  change (∑ i ∈ (unitNetMass hV x).support, (unitNetTotal hV x)⁻¹ * unitNetMass hV x i) = 1
  rw [← Finset.mul_sum]
  change (unitNetTotal hV x)⁻¹ * unitNetTotal hV x = 1
  exact inv_mul_cancel₀ ht

theorem unitNetTotal_eq_sum (x : X) (s : Finset V)
    (hs : (unitNetMass hV x).support ⊆ s) :
    unitNetTotal hV x = ∑ v ∈ s, max 0 (2 - dist x v) := by
  exact Finsupp.sum_of_support_subset _ hs _ (by simp)

/-- On any finite set containing the support, the global partition agrees
with the finite-dimensional cutoff partition. -/
theorem cutoffPartition_eq_unitNetPartition (x : X) (s : Finset V)
    (hs : (unitNetMass hV x).support ⊆ s) (v : s) :
    cutoffPartition (fun u : s => (u.val : X)) x v = unitNetPartition hV x v.val := by
  have he : ‖cutoffMass (fun u : s => (u.val : X)) x‖ = unitNetTotal hV x := by
    rw [PiLp.norm_eq_of_L1, unitNetTotal_eq_sum hV x s hs]
    change (∑ u : s, ‖max 0 (2 - dist x (u.val : X))‖) = _
    simp only [Real.norm_of_nonneg (le_max_left (0 : ℝ) _)]
    exact Finset.sum_coe_sort s (fun u : V => max 0 (2 - dist x u))
  change ‖cutoffMass (fun u : s => (u.val : X)) x‖⁻¹ * max 0 (2 - dist x (v.val : X)) = _
  rw [he]
  rfl

theorem unitNetPartition_variation_on_finset
    (hcover : ∀ x : X, ∃ v ∈ V, dist x v ≤ 1) (x y : X) (s : Finset V)
    (hx : (unitNetMass hV x).support ⊆ s)
    (hy : (unitNetMass hV y).support ⊆ s) :
    (∑ v ∈ s, |unitNetPartition hV x v - unitNetPartition hV y v|) ≤
      2 * (s.card : ℝ) * dist x y := by
  have cover (z : X) (hz : (unitNetMass hV z).support ⊆ s) :
      ∃ u : s, dist z (u.val : X) ≤ 1 := by
    obtain ⟨v, hv, hd⟩ := hcover z
    have hm := (mem_support_unitNetMass_iff hV z ⟨v, hv⟩).mpr (by linarith)
    exact ⟨⟨⟨v, hv⟩, hz hm⟩, hd⟩
  have h := norm_cutoffPartition_sub_le (fun u : s => (u.val : X)) x y (cover x hx) (cover y hy)
  rw [PiLp.norm_eq_of_L1] at h
  simp only [PiLp.sub_apply, Real.norm_eq_abs, cutoffPartition_eq_unitNetPartition hV x s hx,
    cutoffPartition_eq_unitNetPartition hV y s hy, Fintype.card_coe] at h
  calc
    _ = ∑ v : s, |unitNetPartition hV x v.val - unitNetPartition hV y v.val| :=
      (Finset.sum_coe_sort s (fun v : V => |unitNetPartition hV x v - unitNetPartition hV y v|)).symm
    _ ≤ _ := h

theorem unitNetMass_support_card_le {M : ℕ}
    (hM : ∀ x : X, (V ∩ closedBall x 2).ncard ≤ M) (x : X) :
    (unitNetMass hV x).support.card ≤ M := by
  classical
  let B := V ∩ closedBall x 2
  let : Finite B := (finite_unit_net_ball hV x 2).to_subtype
  let j : (unitNetMass hV x).support → B := fun v =>
    ⟨v.val.val, v.val.property, by
      rw [mem_closedBall, dist_comm]
      exact ((mem_support_unitNetMass_iff hV x v.val).mp v.property).le⟩
  have hj : Function.Injective j := by
    intro v w he
    have he' : v.val.val = w.val.val := congrArg (fun z : B => z.val) he
    exact Subtype.ext (Subtype.ext he')
  have h := Nat.card_le_card_of_injective j hj
  simp only [Nat.card_eq_finsetCard, Nat.card_coe_set_eq] at h
  exact h.trans (hM x)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_OrderedInterpolationWeights
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.height_quotient_commutative _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesHomology _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Stability of ordered interpolation under changes of mass -/

namespace PolycyclicRecognition

variable {I G : Type*} [MetricSpace G]

/-- On lists of bounded length and bounded image diameter, ordered
interpolation is uniformly Lipschitz on probability weights. The stronger
weighted estimate also covers vanishing tail masses in the recursion. -/
theorem exists_interpolation_weight_control (c : ControlledContraction G)
    {D : ℝ} (hD : 0 ≤ D) (n : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ InterpolationWeightControl (I := I) c D n K := by
  induction n with
  | zero =>
    refine ⟨0, le_rfl, ?_⟩
    intro l p₀ v a b hlen ha hb hdiam
    have hl : l = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hlen)
    simp [hl, listMass, listVariation]
  | succ n ih =>
    obtain ⟨K, hK, hweight⟩ := ih
    obtain ⟨R, hR, hrad⟩ := exists_interpolation_radius (I := I) c hD n
    obtain ⟨C, hC, hcontrol⟩ := c.bounds R hR
    have hC0 : 0 ≤ C := le_trans zero_le_one hC
    refine ⟨C * (2 + K), mul_nonneg hC0 (by linarith), ?_⟩
    intro l p₀ v a b hlen ha hb hdiam
    cases l with
    | nil => simp [listMass, listVariation]
    | cons i l =>
      cases l with
      | nil =>
        simp only [orderedCenter_singleton, dist_self, mul_zero]
        exact mul_nonneg (mul_nonneg hC0 (by linarith)) (listVariation_nonneg a b [i])
      | cons j tail =>
        let l := j :: tail
        have hlt : l.length ≤ n := by
          change (j :: tail).length ≤ n
          simpa only [List.length_cons, Nat.add_le_add_iff_right] using hlen
        have hat : ∀ k ∈ l, 0 ≤ a k := fun k hk => ha k (List.mem_cons_of_mem i hk)
        have hbt : ∀ k ∈ l, 0 ≤ b k := fun k hk => hb k (List.mem_cons_of_mem i hk)
        have hdiamt : ∀ k ∈ l, ∀ m ∈ l, dist (v k) (v m) ≤ D :=
          fun k hk m hm => hdiam k (List.mem_cons_of_mem i hk) m (List.mem_cons_of_mem i hm)
        have hi : ∀ k ∈ l, dist (v k) (v i) ≤ D :=
          fun k hk => hdiam k (List.mem_cons_of_mem i hk) i (by simp)
        have hra := hrad l p₀ v a (by simp [l]) hlt hat hdiamt (v i) hi
        have hrb := hrad l p₀ v b (by simp [l]) hlt hbt hdiamt (v i) hi
        have hA := listMass_nonneg a (i :: l) ha
        have hB := listMass_nonneg b (i :: l) hb
        have hU := listMass_nonneg a l hat
        have hV := listMass_nonneg b l hbt
        have hδ := listVariation_nonneg a b (i :: l)
        change min (listMass a (i :: l)) (listMass b (i :: l)) *
          dist (orderedCenter c p₀ v a (i :: l)) (orderedCenter c p₀ v b (i :: l)) ≤ _
        by_cases hAz : listMass a (i :: l) = 0
        · rw [hAz, min_eq_left hB, zero_mul]
          exact mul_nonneg (mul_nonneg hC0 (by linarith)) hδ
        by_cases hBz : listMass b (i :: l) = 0
        · rw [hBz, min_eq_right hA, zero_mul]
          exact mul_nonneg (mul_nonneg hC0 (by linarith)) hδ
        have hAp : 0 < listMass a (i :: l) := lt_of_le_of_ne hA (Ne.symm hAz)
        have hBp : 0 < listMass b (i :: l) := lt_of_le_of_ne hB (Ne.symm hBz)
        have huA : listMass a l ≤ listMass a (i :: l) := by
          change _ ≤ a i + listMass a l
          exact le_add_of_nonneg_left (ha i (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
        have hvB : listMass b l ≤ listMass b (i :: l) := by
          change _ ≤ b i + listMass b l
          exact le_add_of_nonneg_left (hb i (by simp))
        have hsa := listMass_tail_fraction_mem a i l ha
        have hsb := listMass_tail_fraction_mem b i l hb
        have hc := hcontrol (v i) (orderedCenter c p₀ v a l) (orderedCenter c p₀ v b l)
          hra hrb _ hsa _ hsb
        have hm : 0 ≤ min (listMass a (i :: l)) (listMass b (i :: l)) := le_min hA hB
        have htime := min_mass_mul_abs_fraction_sub_le hAp hBp hU huA hV hvB
        have htime' : min (listMass a (i :: l)) (listMass b (i :: l)) *
            |listMass a l / listMass a (i :: l) - listMass b l / listMass b (i :: l)| ≤
            2 * listVariation a b (i :: l) := by
          have h₁ := abs_listMass_sub_le a b l
          have h₂ := abs_listMass_sub_le a b (i :: l)
          have htail : listVariation a b l ≤ listVariation a b (i :: l) := by
            change _ ≤ |a i - b i| + listVariation a b l
            exact le_add_of_nonneg_left (abs_nonneg _)
          linarith
        have hspace := min_mass_mul_min_fraction_le hAp hBp hU hV
        have hspace' : min (listMass a (i :: l)) (listMass b (i :: l)) *
            min (listMass a l / listMass a (i :: l)) (listMass b l / listMass b (i :: l)) *
              dist (orderedCenter c p₀ v a l) (orderedCenter c p₀ v b l) ≤
            K * listVariation a b l := by
          exact (mul_le_mul_of_nonneg_right hspace dist_nonneg).trans
            (hweight l p₀ v a b hlt hat hbt hdiamt)
        have htail : listVariation a b l ≤ listVariation a b (i :: l) := by
          change _ ≤ |a i - b i| + listVariation a b l
          exact le_add_of_nonneg_left (abs_nonneg _)
        have hc' := mul_le_mul_of_nonneg_left hc hm
        change min (listMass a (i :: l)) (listMass b (i :: l)) *
          dist (c.contract (v i) _ _) (c.contract (v i) _ _) ≤ _
        calc
          _ ≤ C * (2 * listVariation a b (i :: l) + K * listVariation a b l) := by
            nlinarith only [hc', mul_le_mul_of_nonneg_left htime' hC0,
              mul_le_mul_of_nonneg_left hspace' hC0]
          _ ≤ C * (2 + K) * listVariation a b (i :: l) := by
            nlinarith only [mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left htail hK) hC0]

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_FiniteSupportInterpolation
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.height_quotient_commutative _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesHomology _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Compatible interpolation on finite supports -/

noncomputable section
namespace PolycyclicRecognition

open scoped BigOperators

variable {I G : Type*} [LinearOrder I] [MetricSpace G]

omit [LinearOrder I] in
theorem listMass_eq_list_sum (a : I → ℝ) (l : List I) :
    listMass a l = (l.map a).sum := by
  induction l with
  | nil => rfl
  | cons i l ih => simpa only [listMass, List.map_cons, List.sum_cons] using congrArg (a i + ·) ih

theorem listMass_sort (a : I → ℝ) (s : Finset I) :
    listMass a (s.sort (· ≤ ·)) = ∑ i ∈ s, a i := by
  rw [listMass_eq_list_sum]
  change Multiset.sum (Multiset.map a (s.sort (· ≤ ·) : Multiset I)) = _
  rw [Finset.sort_eq]
  rfl

theorem filter_sort_support (a : I →₀ ℝ) (s : Finset I) (hs : a.support ⊆ s) :
    (s.sort (· ≤ ·)).filter (fun i => a i ≠ 0) = a.support.sort (· ≤ ·) := by
  classical
  let l := (s.sort (· ≤ ·)).filter (fun i => a i ≠ 0)
  have hl : l.toFinset = a.support := by
    ext i
    simp only [l, List.mem_toFinset, List.mem_filter, Finset.mem_sort, decide_eq_true_eq,
      Finsupp.mem_support_iff]
    exact ⟨fun h => h.2, fun h => ⟨hs (Finsupp.mem_support_iff.mpr h), h⟩⟩
  have hp : l.Pairwise (· ≤ ·) := (s.pairwise_sort (· ≤ ·)).filter _
  have hn : l.Nodup := (s.sort_nodup (· ≤ ·)).filter _
  have h := (List.toFinset_sort (r := (· ≤ ·)) hn).mpr hp
  rw [hl] at h
  exact h.symm

theorem finiteSupportCenter_eq_on_superset (c : ControlledContraction G) (p₀ : G)
    (v : I → G) (a : I →₀ ℝ) (s : Finset I) (hs : a.support ⊆ s)
    (ha : ∀ i, 0 ≤ a i) (hm : 0 < a.sum (fun _ r => r)) :
    finiteSupportCenter c p₀ v a = orderedCenter c p₀ v a (s.sort (· ≤ ·)) := by
  have hsum : listMass a (s.sort (· ≤ ·)) = a.sum (fun _ r => r) := by
    rw [listMass_sort, Finsupp.sum_of_support_subset _ hs _ (by simp)]
  have h := orderedCenter_filter_zero c p₀ v a (s.sort (· ≤ ·)) (fun i _ => ha i) (hsum.symm ▸ hm)
  rw [filter_sort_support a s hs] at h
  exact h

/-- A common finite support allows the list stability estimate to compare
two probability vectors, even when some coordinates vanish in just one. -/
theorem finiteSupportCenter_dist_le (c : ControlledContraction G) {D K : ℝ} {n : ℕ}
    (hK : InterpolationWeightControl (I := I) c D n K) (p₀ : G) (v : I → G)
    (a b : I →₀ ℝ) (s : Finset I)
    (has : a.support ⊆ s) (hbs : b.support ⊆ s) (hs : s.card ≤ n)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i)
    (ham : a.sum (fun _ r => r) = 1) (hbm : b.sum (fun _ r => r) = 1)
    (hdiam : ∀ i ∈ s, ∀ j ∈ s, dist (v i) (v j) ≤ D) :
    dist (finiteSupportCenter c p₀ v a) (finiteSupportCenter c p₀ v b) ≤
      K * (∑ i ∈ s, |a i - b i|) := by
  have hm (u : I →₀ ℝ) (hu : u.support ⊆ s) (hut : u.sum (fun _ r => r) = 1) :
      listMass u (s.sort (· ≤ ·)) = 1 := by
    rw [listMass_sort, ← Finsupp.sum_of_support_subset u hu (fun _ (r : ℝ) => r) (by simp), hut]
  rw [finiteSupportCenter_eq_on_superset c p₀ v a s has ha (by rw [ham]; norm_num),
    finiteSupportCenter_eq_on_superset c p₀ v b s hbs hb (by rw [hbm]; norm_num)]
  have h := hK (s.sort (· ≤ ·)) p₀ v a b (by simpa using hs)
    (fun i _ => ha i) (fun i _ => hb i)
    (fun i hi j hj => hdiam i ((Finset.mem_sort (· ≤ ·)).mp hi) j ((Finset.mem_sort (· ≤ ·)).mp hj))
  rw [hm a has ham, hm b hbs hbm, min_self, one_mul] at h
  simpa only [listVariation, listMass_sort] using h

theorem finiteSupportCenter_dist_anchor_le (c : ControlledContraction G) {D R : ℝ} {n : ℕ}
    (hR : InterpolationRadius (I := I) c D n R) (p₀ : G) (v : I → G) (a : I →₀ ℝ)
    (ha : ∀ i, 0 ≤ a i) (ham : a.sum (fun _ r => r) = 1) (hcard : a.support.card ≤ n)
    (hdiam : ∀ i ∈ a.support, ∀ j ∈ a.support, dist (v i) (v j) ≤ D)
    (p : G) (hp : ∀ i ∈ a.support, dist (v i) p ≤ D) :
    dist (finiteSupportCenter c p₀ v a) p ≤ R := by
  have hsum : listMass a (a.support.sort (· ≤ ·)) = 1 := by
    rw [listMass_sort]
    exact ham
  have hne : a.support.sort (· ≤ ·) ≠ [] := by
    intro hn
    rw [hn] at hsum
    norm_num [listMass] at hsum
  exact hR _ p₀ v a hne (by simpa using hcard) (fun i _ => ha i)
    (fun i hi j hj => hdiam i ((Finset.mem_sort (· ≤ ·)).mp hi) j ((Finset.mem_sort (· ≤ ·)).mp hj))
    p (fun i hi => hp i ((Finset.mem_sort (· ≤ ·)).mp hi))

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_LocalLipschitzMinimizing
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.height_quotient_commutative _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesHomology _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # From a fixed-radius Lipschitz bound to the global bound -/

namespace PolycyclicRecognition

open Set
open scoped NNReal

theorem lipschitzWith_of_unit_local_bound
    {G Y : Type*} [Group G] [MetricSpace G] [IsIsometricSMul G G] [MetricSpace Y]
    (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
        dist (γ t) (γ u) ≤ dist 1 g * |t - u|)
    {K : ℝ≥0} (f : G → Y)
    (hf : ∀ x y, dist x y ≤ 1 → dist (f x) (f y) ≤ K * dist x y) :
    LipschitzWith K f := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  obtain ⟨γ, h0, h1, hγ⟩ := hpath (x⁻¹ * y)
  let D := dist 1 (x⁻¹ * y)
  let n := ⌊D⌋₊ + 1
  have hn : 0 < n := Nat.succ_pos _
  have hnr : 0 < (n : ℝ) := by exact_mod_cast hn
  have hDn : D ≤ (n : ℝ) := by simpa [n] using (Nat.lt_floor_add_one D).le
  let p : ℕ → G := fun k => x * γ ((k : ℝ) / n)
  have hp0 : p 0 = x := by simp [p, h0]
  have hpn : p n = y := by simp [p, h1, hnr.ne']
  have hp (k : ℕ) (hk : k < n) : dist (p k) (p (k + 1)) ≤ D / (n : ℝ) := by
    have ht : (k : ℝ) / n ∈ Icc (0 : ℝ) 1 :=
      ⟨by positivity, (div_le_one hnr).mpr (by exact_mod_cast hk.le)⟩
    have hu : ((k + 1 : ℕ) : ℝ) / n ∈ Icc (0 : ℝ) 1 :=
      ⟨by positivity, (div_le_one hnr).mpr (by exact_mod_cast hk)⟩
    have hd : |(k : ℝ) / n - ((k + 1 : ℕ) : ℝ) / n| = 1 / n := by
      rw [abs_of_nonpos (sub_nonpos.mpr (div_le_div_of_nonneg_right (by simp) hnr.le))]
      push_cast
      ring
    change dist (x * γ _) (x * γ _) ≤ _
    rw [dist_mul_left]
    simpa only [hd, mul_one_div] using hγ _ ht _ hu
  have hstep (k : ℕ) (hk : k < n) : dist (f (p k)) (f (p (k + 1))) ≤ K * (D / (n : ℝ)) :=
    (hf _ _ ((hp k hk).trans ((div_le_one hnr).mpr hDn))).trans
      (mul_le_mul_of_nonneg_left (hp k hk) K.2)
  calc
    dist (f x) (f y) = dist (f (p 0)) (f (p n)) := by rw [hp0, hpn]
    _ ≤ ∑ k ∈ Finset.range n, K * (D / (n : ℝ)) :=
      dist_le_range_sum_of_dist_le (f := fun k => f (p k)) n (fun {k} hk => hstep k hk)
    _ = K * D := by simp; field_simp
    _ = K * dist x y := by rw [show D = dist x y from dist_one_groupDifference x y]

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_NetSmoothing
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.height_quotient_commutative _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesHomology _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniformly close Lipschitz interpolation of coarse maps -/

noncomputable section
namespace PolycyclicRecognition

open Set Metric
open scoped NNReal BigOperators

variable {X Y : Type*} [Group X] [MetricSpace X] [ProperSpace X]
  [IsIsometricSMul X X] [MetricSpace Y]
  {V : Set X} (hV : V.Pairwise (fun x y => 1 < dist x y)) [LinearOrder V]

omit [Group X] [IsIsometricSMul X X] in
theorem net_union_support_diameter {x y : X} (hxy : dist x y ≤ 1)
    {v w : V}
    (hv : v ∈ (unitNetMass hV x).support ∪ (unitNetMass hV y).support)
    (hw : w ∈ (unitNetMass hV x).support ∪ (unitNetMass hV y).support) :
    dist (v : X) (w : X) ≤ 6 := by
  have hb (u : V) (hu : u ∈ (unitNetMass hV x).support ∪ (unitNetMass hV y).support) :
      dist x (u : X) ≤ 3 := by
    rcases Finset.mem_union.mp hu with hu | hu
    · have h := (mem_support_unitNetMass_iff hV x u).mp hu
      linarith
    · have h := (mem_support_unitNetMass_iff hV y u).mp hu
      have ht := dist_triangle x y (u : X)
      linarith
  have hv' := hb v hv
  have hw' := hb w hw
  have ht := dist_triangle (v : X) x (w : X)
  rw [dist_comm (v : X) x] at ht
  linarith

/-- The same constants work for every map with the prescribed coarse
upper bound. All interpolation data are constructed from the fixed net. -/
theorem exists_uniform_net_smoothing (c : ControlledContraction Y) (p₀ : Y)
    (hcover : ∀ x : X, ∃ v ∈ V, dist x v ≤ 1)
    (hpath : ∀ g : X, ∃ γ : ℝ → X, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
        dist (γ t) (γ u) ≤ dist 1 g * |t - u|)
    {K C : ℝ} (hK : 0 ≤ K) (hC : 0 ≤ C) :
    ∃ L : ℝ≥0, ∃ E : ℝ, 0 ≤ E ∧ ∀ f : X → Y,
      (∀ x y, dist (f x) (f y) ≤ K * dist x y + C) →
      LipschitzWith L (netSmoothedMap hV c p₀ f) ∧
        ∀ x, dist (netSmoothedMap hV c p₀ f x) (f x) ≤ E := by
  obtain ⟨M, hM⟩ := exists_uniform_unit_net_card (G := X) 2
  have hMv := hM V hV
  let D := 6 * K + C
  have hD : 0 ≤ D := by dsimp [D] <;> positivity
  obtain ⟨R, hR, hrad⟩ := exists_interpolation_radius (I := V) c hD (2 * M)
  obtain ⟨Q, hQ, hweight⟩ := exists_interpolation_weight_control (I := V) c hD (2 * M)
  let L : ℝ≥0 := ⟨Q * (4 * (M : ℝ)), mul_nonneg hQ (by positivity)⟩
  refine ⟨L, R, hR, ?_⟩
  intro f hf
  constructor
  · apply lipschitzWith_of_unit_local_bound hpath
    intro x y hxy
    let s := (unitNetMass hV x).support ∪ (unitNetMass hV y).support
    have hs : s.card ≤ 2 * M := by
      have h := (Finset.card_union_le (unitNetMass hV x).support (unitNetMass hV y).support).trans
        (Nat.add_le_add (unitNetMass_support_card_le hV hMv x) (unitNetMass_support_card_le hV hMv y))
      simpa only [two_mul] using h
    have hx : (unitNetMass hV x).support ⊆ s := Finset.subset_union_left
    have hy : (unitNetMass hV y).support ⊆ s := Finset.subset_union_right
    have hpx : (unitNetPartition hV x).support ⊆ s := Finset.Subset.trans Finsupp.support_smul hx
    have hpy : (unitNetPartition hV y).support ⊆ s := Finset.Subset.trans Finsupp.support_smul hy
    have hd : ∀ v ∈ s, ∀ w ∈ s, dist (f (v : X)) (f (w : X)) ≤ D := by
      intro v hv w hw
      exact (hf v w).trans (by dsimp [D]; nlinarith only [net_union_support_diameter hV hxy hv hw, hK])
    have h := finiteSupportCenter_dist_le c hweight p₀ (fun v : V => f v)
      (unitNetPartition hV x) (unitNetPartition hV y) s hpx hpy hs
      (unitNetPartition_nonneg hV x) (unitNetPartition_nonneg hV y)
      (unitNetPartition_total hV hcover x) (unitNetPartition_total hV hcover y) hd
    have hv := unitNetPartition_variation_on_finset hV hcover x y s hx hy
    have hsr : (s.card : ℝ) ≤ 2 * M := by exact_mod_cast hs
    change dist (finiteSupportCenter c p₀ _ _) (finiteSupportCenter c p₀ _ _) ≤ _
    apply h.trans
    have hv' : (∑ v ∈ s, |unitNetPartition hV x v - unitNetPartition hV y v|) ≤
        4 * (M : ℝ) * dist x y := by
      nlinarith only [hv, mul_le_mul_of_nonneg_right hsr (dist_nonneg (x := x) (y := y))]
    exact (mul_le_mul_of_nonneg_left hv' hQ).trans_eq (by change _ = (Q * (4 * (M : ℝ))) * dist x y; ring)
  · intro x
    have hs : (unitNetPartition hV x).support ⊆ (unitNetMass hV x).support := Finsupp.support_smul
    have hcard : (unitNetPartition hV x).support.card ≤ 2 * M :=
      (Finset.card_le_card hs).trans ((unitNetMass_support_card_le hV hMv x).trans (by omega))
    have hd : ∀ v ∈ (unitNetPartition hV x).support,
        ∀ w ∈ (unitNetPartition hV x).support, dist (f (v : X)) (f (w : X)) ≤ D := by
      intro v hv w hw
      have h := net_union_support_diameter hV (x := x) (y := x) (by simp)
        (Finset.mem_union_left _ (hs hv)) (Finset.mem_union_left _ (hs hw))
      exact (hf v w).trans (by dsimp [D]; nlinarith only [h, hK])
    apply finiteSupportCenter_dist_anchor_le c hrad p₀ (fun v : V => f v)
      (unitNetPartition hV x) (unitNetPartition_nonneg hV x)
      (unitNetPartition_total hV hcover x) hcard hd (f x)
    intro v hv
    have h := ((mem_support_unitNetMass_iff hV x v).mp (hs hv)).le
    rw [dist_comm x (v : X)] at h
    exact (hf v x).trans (by dsimp [D]; nlinarith only [h, hK])

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_LipschitzReplacement
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.height_quotient_commutative _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesHomology _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Lipschitz replacement with all net choices internal -/

noncomputable section
namespace PolycyclicRecognition

open Set
open scoped NNReal

/-- Construct a uniformly close Lipschitz representative of every map
with the given coarse upper bound. The net and its order are chosen here. -/
theorem exists_lipschitz_replacement_constants
    {X Y : Type*} [Group X] [MetricSpace X] [ProperSpace X]
    [IsIsometricSMul X X] [MetricSpace Y]
    (c : ControlledContraction Y) (p₀ : Y)
    (hpath : ∀ g : X, ∃ γ : ℝ → X, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
        dist (γ t) (γ u) ≤ dist 1 g * |t - u|)
    {K C : ℝ} (hK : 0 ≤ K) (hC : 0 ≤ C) :
    ∃ L : ℝ≥0, ∃ E : ℝ, 0 ≤ E ∧ ∀ f : X → Y,
      (∀ x y, dist (f x) (f y) ≤ K * dist x y + C) →
      ∃ f' : C(X, Y), LipschitzWith L f' ∧ ∀ x, dist (f' x) (f x) ≤ E := by
  classical
  obtain ⟨V, hV, hcover⟩ := exists_unit_separated_net (X := X)
  let : LinearOrder V := linearOrderOfSTO WellOrderingRel
  obtain ⟨L, E, hE, hsmooth⟩ := exists_uniform_net_smoothing hV c p₀ hcover hpath hK hC
  refine ⟨L, E, hE, ?_⟩
  intro f hf
  obtain ⟨hLip, hclose⟩ := hsmooth f hf
  exact ⟨⟨netSmoothedMap hV c p₀ f, hLip.continuous⟩, hLip, hclose⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_LipschitzPairReplacement
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.height_quotient_commutative _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesHomology _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform Lipschitz replacement of coarse inverse pairs -/

noncomputable section
namespace PolycyclicRecognition

open Set
open scoped NNReal

theorem exists_lipschitz_pair_replacement_constants
    {G : Type*} [Group G] [MetricSpace G] [ProperSpace G] [IsIsometricSMul G G]
    (c : ControlledContraction G)
    (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
        dist (γ t) (γ u) ≤ dist 1 g * |t - u|)
    {K C A : ℝ} (hK : 0 ≤ K) (hC : 0 ≤ C) :
    ∃ Λ : ℝ≥0, 2 ≤ (Λ : ℝ) ∧ ∃ E : ℝ, 0 ≤ E ∧
      ∀ f g : G → G,
        (∀ x y, dist (f x) (f y) ≤ K * dist x y + C) →
        (∀ x y, dist (g x) (g y) ≤ K * dist x y + C) →
        (∀ x, dist (g (f x)) x ≤ A) → (∀ x, dist (f (g x)) x ≤ A) →
        ∃ p : C(G, G) × C(G, G), LipschitzPairBounds G Λ p ∧
          (∀ x, dist (p.1 x) (f x) ≤ E) ∧ (∀ x, dist (p.2 x) (g x) ≤ E) := by
  obtain ⟨L, E, hE, hrep⟩ := exists_lipschitz_replacement_constants c (1 : G) hpath hK hC
  let B := E + (K * E + C) + A
  let Λ : ℝ≥0 := ⟨max 2 (max (L : ℝ) B), le_trans (by norm_num) (le_max_left _ _)⟩
  have hΛ : 2 ≤ (Λ : ℝ) := le_max_left _ _
  have hLΛ : L ≤ Λ := (le_max_left (L : ℝ) B).trans (le_max_right _ _)
  have hBΛ : B ≤ (Λ : ℝ) := (le_max_right (L : ℝ) B).trans (le_max_right _ _)
  refine ⟨Λ, hΛ, E, hE, ?_⟩
  intro f g hf hg hgf hfg
  obtain ⟨f', hf', hff'⟩ := hrep f hf
  obtain ⟨g', hg', hgg'⟩ := hrep g hg
  have hgf' : ∀ x, dist (g' (f' x)) x ≤ Λ := fun x =>
    (inverse_error_of_bounded_perturbations f f' g g' hK hg hff' hgg' hgf x).trans hBΛ
  have hfg' : ∀ x, dist (f' (g' x)) x ≤ Λ := fun x =>
    (inverse_error_of_bounded_perturbations g g' f f' hK hf hgg' hff' hfg x).trans hBΛ
  exact ⟨(f', g'), lipschitzPairBounds_of_inverse_bounds hΛ (f', g')
    (hf'.weaken hLΛ) (hg'.weaken hLΛ) hgf' hfg', hff', hgg'⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_TransferredPairRepresentatives
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.height_quotient_commutative _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesHomology _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Constructed Lipschitz pairs for the transferred action -/

noncomputable section
namespace PolycyclicRecognition

open Set
open scoped NNReal

theorem MetricQuasiEquivalence.exists_transferred_pair_representatives
    {J G : Type*} [Group J] [MetricSpace J] [IsIsometricSMul J J]
    [Group G] [MetricSpace G] [ProperSpace G] [IsIsometricSMul G G]
    (u : MetricQuasiEquivalence J G) (c : ControlledContraction G)
    (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1,
        dist (γ t) (γ s) ≤ dist 1 g * |t - s|) :
    ∃ Λ : ℝ≥0, 2 ≤ (Λ : ℝ) ∧ ∃ E : ℝ, 0 ≤ E ∧
      ∃ rep : J → C(G, G) × C(G, G),
        (∀ h, LipschitzPairBounds G Λ (rep h)) ∧
        (∀ h x, dist ((rep h).1 x) (transferredMap u.toFun u.invFun h x) ≤ E) ∧
        (∀ h x, dist ((rep h).2 x) (transferredMap u.toFun u.invFun h⁻¹ x) ≤ E) := by
  obtain ⟨Kf, Cf, hKf, hCf, hf⟩ := u.toFun_control
  obtain ⟨Kr, Cr, hKr, hCr, hr⟩ := u.invFun_control
  obtain ⟨A, hA, ha⟩ := u.left_close
  obtain ⟨B, hB, hb⟩ := u.right_close
  let F := transferredMap u.toFun u.invFun
  have hu : ∀ h x y, dist (F h x) (F h y) ≤ (Kf * Kr) * dist x y + (Kf * Cr + Cf) :=
    transferredMap_coarse_upper u.toFun u.invFun (fun h x y => dist_mul_left h x y)
      Kf Cf Kr Cr hKf hf hr
  have hcomp : ∀ h k x, dist (F h (F k x)) (F (h * k) x) ≤ Kf * A + Cf := by
    intro h k x
    exact transferredMap_mul_close u.toFun u.invFun (fun h x y => dist_mul_left h x y)
      Kf Cf A hKf hf (fun j => by simpa only [dist_comm] using ha j) h k x
  have hidentity : ∀ x, dist (F 1 x) x ≤ B := by
    intro x
    exact transferredMap_one_close u.toFun u.invFun B (fun x => by simpa only [dist_comm] using hb x) x
  have hinv : ∀ h x, dist (F h⁻¹ (F h x)) x ≤ Kf * A + Cf + B := by
    intro h x
    have he := hcomp h⁻¹ h x
    rw [inv_mul_cancel] at he
    exact (dist_triangle _ (F 1 x) x).trans (add_le_add he (hidentity x))
  obtain ⟨Λ, hΛ, E, hE, hreplace⟩ := exists_lipschitz_pair_replacement_constants c hpath
    (A := Kf * A + Cf + B) (mul_nonneg hKf hKr) (add_nonneg (mul_nonneg hKf hCr) hCf)
  have hex (h : J) : ∃ p : C(G, G) × C(G, G), LipschitzPairBounds G Λ p ∧
      (∀ x, dist (p.1 x) (F h x) ≤ E) ∧ (∀ x, dist (p.2 x) (F h⁻¹ x) ≤ E) := by
    apply hreplace (F h) (F h⁻¹) (hu h) (hu h⁻¹) (hinv h)
    simpa only [inv_inv] using hinv h⁻¹
  choose rep hrep hforward hbackward using hex
  exact ⟨Λ, hΛ, E, hE, rep, hrep, hforward, hbackward⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_RecognitionWithoutKMN
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.instFiniteRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.instNonemptyRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.inversePairCoupling_finiteOnCompacts _root_.OAI.PolycyclicRecognition.normalizedPair_polishSpace _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The geometric recognition assembly without the KMN hypothesis

Rational dimension, bounded finite subgroup orders, and duality after removing
a finite normal subgroup give recognition with polynomial-growth recognition
as an explicit hypothesis.
-/
noncomputable section
namespace PolycyclicRecognition
open Set
open scoped Manifold NNReal

theorem recognition_and_lattice_of_affine_height_proved
    (dekimpe : DekimpeLatticeRealizationInput)
    {P H : Type} [Group P] [Group H] [MetricSpace P] [MetricSpace H]
    [IsIsometricSMul P P] [IsIsometricSMul H H] [Group.FG P] [Group.FG H]
    [DiscreteTopology H] [ProperSpace H]
    [MeasurableSpace H] [BorelSpace H] [MeasurableMul H]
    (e : MetricQuasiEquivalence P H) (hP : IsVirtuallyPolycyclic P)
    (hPfinite : ∀ R : ℝ, (Metric.closedBall (1 : P) R).Finite)
    {X W : Type} [PseudoMetricSpace X] [DecidableEq X]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    (u : MetricQuasiEquivalence H X) (π : X → W)
    (packing : PolynomialBoundedChainPacking π)
    (gromov : ∀ (J : Type) [Group J] [DecidableEq J], GromovPolynomialGrowthInput J)
    (A : H → W ≃L[ℝ] W) (hA : Set.Finite (Set.range A))
    (hπsurj : Function.Surjective π)
    {L B : ℝ} (hL : 0 ≤ L) (hB : 0 ≤ B)
    (hπ : ∀ x y, ‖π x - π y‖ ≤ L * dist x y)
    (haffine : ∀ h x,
      ‖π (transferredMap u.toFun u.invFun h x) -
        (π (u.toFun h) + A h (π x))‖ ≤ B) :
    IsVirtuallyPolycyclic H ∧
      ∃ Γ : Subgroup H, Γ.FiniteIndex ∧
        ∃ (S : SimplyConnectedSolvableLieModel) (Λ : Subgroup S.carrier),
          IsUniformLattice Λ ∧ Nonempty (Γ ≃* Λ) := by
  classical
  obtain ⟨M⟩ := e.invariantMean_of_virtuallyPolycyclic hP hPfinite
  obtain ⟨K, C, K', C', _, hK, hC, hK', _, _, hupper, hlower, _⟩ :=
    u.quasiIsometry_toFun
  obtain ⟨E, hE, hleft⟩ := u.left_close
  have hfinite (R : ℝ) : (Metric.closedBall (1 : H) R).Finite :=
    (isCompact_closedBall (1 : H) R).finite_of_discrete
  obtain ⟨H₀, _, hindex, τ, D, hD, hheight, _⟩ :=
    TransferredHeight.exists_normal_finiteIndex_height u.toFun u.invFun π A hπsurj
      (fun h a b => dist_mul_left h a b) L K C E B hL hK hC hE hB hπ hupper
      (fun h => (dist_comm _ _).trans_le (hleft h)) haffine M hA
  let := hindex
  have hH := virtuallyPolycyclic_of_corrected_height_proved
    (e.groupCoarseEquivalence hPfinite hfinite) hP M H₀ τ (fun J => gromov J)
    u.toFun π packing hfinite hK hC hK' hD hupper hlower hheight
  exact ⟨hH, exists_uniform_solvable_lattice_of_virtuallyPolycyclic dekimpe H hH⟩

theorem recognition_and_lattice_of_canonical_affine_height_proved
    (dekimpe : DekimpeLatticeRealizationInput)
    {P J : Type} [Group P] [Group J] [MetricSpace P] [MetricSpace J]
    [IsIsometricSMul P P] [IsIsometricSMul J J] [Group.FG P] [Group.FG J]
    [DiscreteTopology J] [ProperSpace J]
    [MeasurableSpace J] [BorelSpace J] [MeasurableMul J]
    (e : MetricQuasiEquivalence P J) (hP : IsVirtuallyPolycyclic P)
    (hPfinite : ∀ R : ℝ, (Metric.closedBall (1 : P) R).Finite)
    {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MetricSpace G] [ChartedSpace E G] [Group G] [LieGroup (𝓘(ℝ, E)) ⊤ G]
    [SimplyConnectedSpace G] [IsIsometricSMul G G] [ProperSpace G] [DecidableEq G]
    {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, E)) G) a)
    (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    (q : HeightSpace T.character ≃ₗ[ℝ] W) (π : G →* Multiplicative W)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
    (hπExp : ∀ x, (π (Exp x)).toAdd = q (heightProjection T.character x))
    (u : MetricQuasiEquivalence J G)
    (gromov : ∀ (K : Type) [Group K] [DecidableEq K], GromovPolynomialGrowthInput K)
    (A : J → W ≃L[ℝ] W) (hA : Set.Finite (Set.range A))
    {L : ℝ≥0} (hπ : LipschitzWith L (fun g => (π g).toAdd))
    {B : ℝ} (hB : 0 ≤ B)
    (haffine : ∀ h x,
      ‖(π (transferredMap u.toFun u.invFun h x)).toAdd -
        ((π (u.toFun h)).toAdd + A h (π x).toAdd)‖ ≤ B) :
    IsVirtuallyPolycyclic J ∧
      ∃ Γ : Subgroup J, Γ.FiniteIndex ∧
        ∃ (S : SimplyConnectedSolvableLieModel) (Λ : Subgroup S.carrier),
          IsUniformLattice Λ ∧ Nonempty (Γ ≃* Λ) := by
  have hsurj : Function.Surjective (fun g => (π g).toAdd) := by
    intro w
    obtain ⟨g, hg⟩ := integrated_height_surjective T q Exp π hπExp (Multiplicative.ofAdd w)
    exact ⟨g, congrArg Multiplicative.toAdd hg⟩
  exact recognition_and_lattice_of_affine_height_proved dekimpe
    e hP hPfinite u (fun g => (π g).toAdd)
    (polynomialBoundedChainPacking_intrinsic T Exp hExp q π hπExp)
    gromov A hA hsurj L.coe_nonneg hB (fun x y => by
      simpa only [dist_eq_norm] using hπ.dist_le_mul x y) haffine

theorem recognition_and_lattice_of_template_affine_height_proved
    (dekimpe : DekimpeLatticeRealizationInput)
    {P J : Type} [Group P] [Group J] [MetricSpace P] [MetricSpace J]
    [IsIsometricSMul P P] [IsIsometricSMul J J] [Group.FG P] [Group.FG J]
    [DiscreteTopology J] [ProperSpace J]
    [MeasurableSpace J] [BorelSpace J] [MeasurableMul J]
    (e : MetricQuasiEquivalence P J) (hP : IsVirtuallyPolycyclic P)
    (hPfinite : ∀ R : ℝ, (Metric.closedBall (1 : P) R).Finite)
    {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MetricSpace G] [ChartedSpace E G] [Group G] [LieGroup (𝓘(ℝ, E)) ⊤ G]
    [SimplyConnectedSpace G] [IsIsometricSMul G G] [ProperSpace G] [DecidableEq G]
    {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, E)) G) a)
    (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    (q : HeightSpace T.character ≃ₗ[ℝ] W) (π : G →* Multiplicative W)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
    (hπExp : ∀ x, (π (Exp x)).toAdd = q (heightProjection T.character x))
    (u : MetricQuasiEquivalence J G)
    (gromov : ∀ (K : Type) [Group K] [DecidableEq K], GromovPolynomialGrowthInput K)
    {I B₀ : Type*} [Fintype I] [Fintype B₀] [Nonempty B₀]
    (D : SupportDatum W I B₀) (A : J → templateSymmetryGroup D)
    {L : ℝ≥0} (hπ : LipschitzWith L (fun g => (π g).toAdd))
    {B : ℝ} (hB : 0 ≤ B)
    (haffine : ∀ h x,
      ‖(π (transferredMap u.toFun u.invFun h x)).toAdd -
        ((π (u.toFun h)).toAdd + (A h).val (π x).toAdd)‖ ≤ B) :
    IsVirtuallyPolycyclic J ∧
      ∃ Γ : Subgroup J, Γ.FiniteIndex ∧
        ∃ (S : SimplyConnectedSolvableLieModel) (Λ : Subgroup S.carrier),
          IsUniformLattice Λ ∧ Nonempty (Γ ≃* Λ) := by
  let Ac : J → W ≃L[ℝ] W := fun h => (A h).val.toContinuousLinearEquiv
  have hAc : Set.Finite (Set.range Ac) := by
    apply (Set.finite_range (fun f : templateSymmetryGroup D =>
      f.val.toContinuousLinearEquiv)).subset
    rintro _ ⟨h, rfl⟩
    exact ⟨A h, rfl⟩
  exact recognition_and_lattice_of_canonical_affine_height_proved dekimpe e hP hPfinite T W q π Exp hExp hπExp u gromov
    Ac hAc hπ hB haffine

theorem recognition_and_lattice_of_pair_representatives_proved
    (dekimpe : DekimpeLatticeRealizationInput)
    {P J : Type} [Group P] [Group J] [MetricSpace P] [MetricSpace J]
    [IsIsometricSMul P P] [IsIsometricSMul J J] [Group.FG P] [Group.FG J]
    [DiscreteTopology J] [ProperSpace J]
    [MeasurableSpace J] [BorelSpace J] [MeasurableMul J]
    (e : MetricQuasiEquivalence P J) (hP : IsVirtuallyPolycyclic P)
    (hPfinite : ∀ R : ℝ, (Metric.closedBall (1 : P) R).Finite)
    {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MetricSpace G] [ChartedSpace E G] [Group G] [LieGroup (𝓘(ℝ, E)) ⊤ G]
    [SimplyConnectedSpace G] [IsTopologicalGroup G] [IsIsometricSMul G G] [ProperSpace G] [DecidableEq G]
    {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, E)) G) a)
    (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    (q : HeightSpace T.character ≃ₗ[ℝ] W) (π : G →* Multiplicative W)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
    (hπExp : ∀ x, (π (Exp x)).toAdd = q (heightProjection T.character x))
    (u : MetricQuasiEquivalence J G)
    (gromov : ∀ (K : Type) [Group K] [DecidableEq K], GromovPolynomialGrowthInput K)
    {I B₀ : Type*} [Fintype I] [Fintype B₀] [Nonempty B₀]
    (D : SupportDatum W I B₀)
    {L : ℝ≥0} (hπ : LipschitzWith L (fun g => (π g).toAdd))
    {Λ : ℝ≥0} (label : NormalizedPair G Λ → templateSymmetryGroup D)
    {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ p x, ‖(π (p.val.1 x)).toAdd - (label p).val (π x).toAdd‖ ≤ B)
    (rep : J → C(G, G) × C(G, G)) (hrep : ∀ h, LipschitzPairBounds G Λ (rep h))
    {Eclose : ℝ} (hEclose : 0 ≤ Eclose)
    (hclose : ∀ h x, dist ((rep h).1 x) (transferredMap u.toFun u.invFun h x) ≤ Eclose) :
    IsVirtuallyPolycyclic J ∧
      ∃ Γ : Subgroup J, Γ.FiniteIndex ∧
        ∃ (S : SimplyConnectedSolvableLieModel) (Λ : Subgroup S.carrier),
          IsUniformLattice Λ ∧ Nonempty (Γ ≃* Λ) := by
  obtain ⟨A, K, hK, hc⟩ := uniform_affine_height_of_bounded_pair_representatives
    D π L.coe_nonneg
    (fun x y => by simpa only [dist_eq_norm] using hπ.dist_le_mul x y)
    label hB hbound (transferredMap u.toFun u.invFun) rep hrep hEclose hclose
  obtain ⟨Ku, Cu, hKu, hCu, hu⟩ := u.toFun_control
  let Cbase := (L : ℝ) * (Ku * dist (u.invFun 1) 1 + Cu)
  have hCbase : 0 ≤ Cbase :=
    mul_nonneg L.coe_nonneg (add_nonneg (mul_nonneg hKu dist_nonneg) hCu)
  have hbase (h : J) :
      ‖(π (transferredMap u.toFun u.invFun h 1)).toAdd - (π (u.toFun h)).toAdd‖ ≤ Cbase := by
    have hd : dist (u.toFun (h * u.invFun 1)) (u.toFun h) ≤
        Ku * dist (u.invFun 1) 1 + Cu := by
      have hcontrol := hu (h * u.invFun 1) (h * 1)
      rw [dist_mul_left] at hcontrol
      simpa only [mul_one] using hcontrol
    exact (show ‖(π (transferredMap u.toFun u.invFun h 1)).toAdd - (π (u.toFun h)).toAdd‖ ≤
        (L : ℝ) * dist (u.toFun (h * u.invFun 1)) (u.toFun h) by
      simpa only [transferredMap, dist_eq_norm] using
        hπ.dist_le_mul (u.toFun (h * u.invFun 1)) (u.toFun h)).trans
      (mul_le_mul_of_nonneg_left hd L.coe_nonneg)
  apply recognition_and_lattice_of_template_affine_height_proved dekimpe e hP hPfinite T W q π Exp hExp hπExp u gromov D A hπ
    (add_nonneg hK hCbase)
  intro h x
  calc
    _ = ‖((π (transferredMap u.toFun u.invFun h x)).toAdd -
          ((π (transferredMap u.toFun u.invFun h 1)).toAdd + (A h).val (π x).toAdd)) +
        ((π (transferredMap u.toFun u.invFun h 1)).toAdd - (π (u.toFun h)).toAdd)‖ := by
      congr 1
      abel
    _ ≤ _ := norm_add_le _ _
    _ ≤ K + Cbase := add_le_add (hc h x) (hbase h)

theorem recognition_and_lattice_of_uniform_normalized_height_proved_oai
    (dekimpe : DekimpeLatticeRealizationInput)
    {P J : Type} [Group P] [Group J] [MetricSpace P] [MetricSpace J]
    [IsIsometricSMul P P] [IsIsometricSMul J J] [Group.FG P] [Group.FG J]
    [DiscreteTopology J] [ProperSpace J]
    [MeasurableSpace J] [BorelSpace J] [MeasurableMul J]
    (e : MetricQuasiEquivalence P J) (hP : IsVirtuallyPolycyclic P)
    (hPfinite : ∀ R : ℝ, (Metric.closedBall (1 : P) R).Finite)
    {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MetricSpace G] [ChartedSpace E G] [Group G] [LieGroup (𝓘(ℝ, E)) ⊤ G]
    [SimplyConnectedSpace G] [IsTopologicalGroup G] [IsIsometricSMul G G] [ProperSpace G] [DecidableEq G]
    {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, E)) G) a)
    (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    (q : HeightSpace T.character ≃ₗ[ℝ] W) (π : G →* Multiplicative W)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
    (hπExp : ∀ x, (π (Exp x)).toAdd = q (heightProjection T.character x))
    (u : MetricQuasiEquivalence J G)
    (gromov : ∀ (K : Type) [Group K] [DecidableEq K], GromovPolynomialGrowthInput K)
    {I B₀ : Type*} [Fintype I] [Fintype B₀] [Nonempty B₀]
    (D : SupportDatum W I B₀)
    {L : ℝ≥0} (hπ : LipschitzWith L (fun g => (π g).toAdd))
    (c : ControlledContraction G)
    (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1,
        dist (γ t) (γ s) ≤ dist 1 g * |t - s|)
    (hheight : ∀ Λ : ℝ≥0, 2 ≤ (Λ : ℝ) →
      ∃ label : NormalizedPair G Λ → templateSymmetryGroup D,
        ∃ B : ℝ, 0 ≤ B ∧
          ∀ p x, ‖(π (p.val.1 x)).toAdd - (label p).val (π x).toAdd‖ ≤ B) :
    IsVirtuallyPolycyclic J ∧
      ∃ Γ : Subgroup J, Γ.FiniteIndex ∧
        ∃ (S : SimplyConnectedSolvableLieModel) (Λ : Subgroup S.carrier),
          IsUniformLattice Λ ∧ Nonempty (Γ ≃* Λ) := by
  obtain ⟨Λ, hΛ, Eclose, hEclose, rep, hrep, hclose, _⟩ :=
    u.exists_transferred_pair_representatives c hpath
  obtain ⟨label, B, hB, hbound⟩ := hheight Λ hΛ
  exact recognition_and_lattice_of_pair_representatives_proved dekimpe e hP hPfinite T W q π Exp hExp hπExp u gromov D hπ
    label hB hbound rep hrep hEclose hclose

end PolycyclicRecognition

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.PolycyclicRecognition.recognition_and_lattice_of_uniform_normalized_height_proved_oai.{u_1, u_2} := @OAI.PolycyclicRecognition.recognition_and_lattice_of_uniform_normalized_height_proved_oai.{u_1, u_2}
