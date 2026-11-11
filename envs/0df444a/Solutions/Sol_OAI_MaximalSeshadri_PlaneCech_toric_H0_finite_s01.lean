-- Prove2me | solution 1 for OAI.MaximalSeshadri.PlaneCech.toric_H0_finite_s01
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T15:17:14.141133+00:00
-- url     : https://prove2.me/submissions/8b66340b-f56c-47e2-9668-cbeada9e6029

import Mathlib
import Definitions.Def_Q223SES005
import Definitions.Def_Q223SES006
import Theorems.Thm_OAI_MaximalSeshadri_PlaneCech_kernel_H1_finite_s01

section
-- module Solutions.Q223_SES.Seshadri_Cohomology_CechPresentation
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                          
section

namespace MaximalSeshadri.PlaneCech
noncomputable section
variable {K M P : Type*} [Field K] [AddCommGroup M] [Module K M]
  [AddCommGroup P] [Module K P]

theorem finite_quotient_of_kernel_le {V W : Type*} [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [Module.Finite K W]
    (f : V →ₗ[K] W) (B : Submodule K V) (h : LinearMap.ker f ≤ B) :
    Module.Finite K (V ⧸ B) := by
  let : Module.Finite K (V ⧸ LinearMap.ker f) := Module.Finite.equiv f.quotKerEquivRange.symm
  let q : (V ⧸ LinearMap.ker f) →ₗ[K] (V ⧸ B) :=
    Submodule.mapQ (LinearMap.ker f) B LinearMap.id h
  apply Module.Finite.of_surjective q
  intro x
  obtain ⟨v,rfl⟩ := B.mkQ_surjective x
  exact ⟨(LinearMap.ker f).mkQ v,rfl⟩

end
end MaximalSeshadri.PlaneCech

end


end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Cohomology_CechH0
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                
section

namespace MaximalSeshadri.PlaneCech
noncomputable section
variable {K M P : Type*} [Field K] [AddCommGroup M] [Module K M]
  [AddCommGroup P] [Module K P]

private theorem presentationConnectingMap_exact
    (projection : P →ₗ[K] M) (sourceA sourceB sourceC : Submodule K P)
    (target : Submodule K M)
    (liftAB : target →ₗ[K] ↥(sourceA ⊓ sourceB))
    (liftAC : target →ₗ[K] ↥(sourceA ⊓ sourceC))
    (liftBC : target →ₗ[K] ↥(sourceB ⊓ sourceC))
    (mapAB : ∀ sectionValue, projection (liftAB sectionValue) = sectionValue)
    (mapAC : ∀ sectionValue, projection (liftAC sectionValue) = sectionValue)
    (mapBC : ∀ sectionValue, projection (liftBC sectionValue) = sectionValue)
    (sectionValue : target)
    (boundary : presentationConnectingMap projection sourceA sourceB sourceC target
      liftAB liftAC liftBC mapAB mapAC mapBC sectionValue ∈
        fullBoundaries (sourceA.comap projection.ker.subtype)
          (sourceB.comap projection.ker.subtype) (sourceC.comap projection.ker.subtype)) :
    ∃ liftValue : ↥((sourceA ⊓ sourceB) ⊓ sourceC),
      projection liftValue = sectionValue := by
  let kernelA := sourceA.comap projection.ker.subtype
  let kernelB := sourceB.comap projection.ker.subtype
  let kernelC := sourceC.comap projection.ker.subtype
  obtain ⟨sumAB, hsumAB, valueC, hvalueC, sum_eq⟩ := Submodule.mem_sup.mp boundary
  obtain ⟨valueA, hvalueA, valueB, hvalueB, sumAB_eq⟩ := Submodule.mem_sup.mp hsumAB
  obtain ⟨boundaryAB, rfl⟩ := hvalueA
  obtain ⟨boundaryAC, rfl⟩ := hvalueB
  obtain ⟨boundaryBC, rfl⟩ := hvalueC
  have cycle_eq : edgeAB kernelA kernelB kernelC boundaryAB +
      edgeAC kernelA kernelB kernelC boundaryAC + edgeBC kernelA kernelB kernelC boundaryBC =
      presentationConnectingMap projection sourceA sourceB sourceC target
        liftAB liftAC liftBC mapAB mapAC mapBC sectionValue := by
    rw [sumAB_eq]
    exact sum_eq
  have component_eq : -(boundaryAB.val.val : P) + boundaryBC.val.val =
      (liftBC sectionValue : P) - liftAB sectionValue := by
    have equality := congrArg (fun cycle : cycles kernelA kernelB kernelC =>
      (cycle.val.2.1.val.val : P)) cycle_eq
    change -(boundaryAB.val.val : P) + 0 + boundaryBC.val.val =
      (liftBC sectionValue : P) - liftAB sectionValue at equality
    simpa only [add_zero] using equality
  have lift_eq : (liftAB sectionValue : P) - boundaryAB.val.val =
      (liftBC sectionValue : P) - boundaryBC.val.val := by
    calc
      _ = (liftBC sectionValue : P) - ((liftBC sectionValue : P) -
        liftAB sectionValue) - boundaryAB.val.val := by abel
      _ = _ := by rw [← component_eq]; abel
  have lift_mem : (liftAB sectionValue : P) - boundaryAB.val.val ∈
      (sourceA ⊓ sourceB) ⊓ sourceC := by
    refine ⟨⟨sourceA.sub_mem (liftAB sectionValue).2.1 boundaryAB.2.1,
      sourceB.sub_mem (liftAB sectionValue).2.2 boundaryAB.2.2⟩, ?_⟩
    rw [lift_eq]
    exact sourceC.sub_mem (liftBC sectionValue).2.2 boundaryBC.2.2
  refine ⟨⟨(liftAB sectionValue : P) - boundaryAB.val.val, lift_mem⟩, ?_⟩
  change projection ((liftAB sectionValue : P) - boundaryAB.val.val) = (sectionValue : M)
  rw [map_sub, mapAB, show projection (boundaryAB.val.val : P) = 0 from boundaryAB.val.2,
    sub_zero]

private theorem exists_presentationLift
    (projection : P →ₗ[K] M) (source : Submodule K P) (target common : Submodule K M)
    (map_mem : ∀ value ∈ source, projection value ∈ target)
    (surjective : ∀ value ∈ target, ∃ liftValue ∈ source, projection liftValue = value)
    (common_le : common ≤ target) :
    ∃ liftMap : common →ₗ[K] source, ∀ value, projection (liftMap value) = value := by
  let restricted : source →ₗ[K] target :=
    (projection.domRestrict source).codRestrict target (fun value => map_mem value value.2)
  have restricted_surjective : Function.Surjective restricted := by
    rintro ⟨value, value_mem⟩
    obtain ⟨liftValue, lift_mem, lift_eq⟩ := surjective value value_mem
    exact ⟨⟨liftValue, lift_mem⟩, Subtype.ext lift_eq⟩
  obtain ⟨inverse, inverse_eq⟩ := restricted.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr restricted_surjective)
  refine ⟨inverse.comp (Submodule.inclusion common_le), fun value => ?_⟩
  exact congrArg Subtype.val
    (LinearMap.congr_fun inverse_eq ⟨value, common_le value.2⟩)

private theorem finite_of_boundary_lift
    {source target middle : Type*}
    [AddCommGroup source] [Module K source] [Module.Finite K source]
    [AddCommGroup target] [Module K target] [AddCommGroup middle] [Module K middle]
    (boundary : Submodule K middle) [Module.Finite K (middle ⧸ boundary)]
    (connecting : target →ₗ[K] middle) (globalMap : source →ₗ[K] target)
    (exactness : ∀ sectionValue, connecting sectionValue ∈ boundary →
      sectionValue ∈ globalMap.range) : Module.Finite K target := by
  let : Module.Finite K (target ⧸ globalMap.range) := by
    apply finite_quotient_of_kernel_le (boundary.mkQ.comp connecting) globalMap.range
    intro sectionValue kernel_mem
    exact exactness sectionValue ((Submodule.Quotient.mk_eq_zero boundary).mp kernel_mem)
  exact Module.Finite.of_submodule_quotient globalMap.range

private theorem finite_presentationTarget
    (projection : P →ₗ[K] M) (sourceA sourceB sourceC : Submodule K P)
    (target : Submodule K M)
    (liftAB : target →ₗ[K] ↥(sourceA ⊓ sourceB))
    (liftAC : target →ₗ[K] ↥(sourceA ⊓ sourceC))
    (liftBC : target →ₗ[K] ↥(sourceB ⊓ sourceC))
    (mapAB : ∀ sectionValue, projection (liftAB sectionValue) = sectionValue)
    (mapAC : ∀ sectionValue, projection (liftAC sectionValue) = sectionValue)
    (mapBC : ∀ sectionValue, projection (liftBC sectionValue) = sectionValue)
    (globalMap : ↥((sourceA ⊓ sourceB) ⊓ sourceC) →ₗ[K] target)
    (globalMap_eq : ∀ sectionValue, (globalMap sectionValue : M) = projection sectionValue)
    [Module.Finite K ↥((sourceA ⊓ sourceB) ⊓ sourceC)]
    [Module.Finite K (@HasQuotient.Quotient _ _
      (Submodule.hasQuotient (R := K) (M := cycles (sourceA.comap projection.ker.subtype)
        (sourceB.comap projection.ker.subtype) (sourceC.comap projection.ker.subtype)))
      (fullBoundaries (sourceA.comap projection.ker.subtype)
        (sourceB.comap projection.ker.subtype) (sourceC.comap projection.ker.subtype)))] :
    Module.Finite K target := by
  let kernelA := sourceA.comap projection.ker.subtype
  let kernelB := sourceB.comap projection.ker.subtype
  let kernelC := sourceC.comap projection.ker.subtype
  let connecting : target →ₗ[K] cycles kernelA kernelB kernelC :=
    presentationConnectingMap projection sourceA sourceB sourceC target
      liftAB liftAC liftBC mapAB mapAC mapBC
  let boundary := fullBoundaries kernelA kernelB kernelC
  apply finite_of_boundary_lift (source := ↥((sourceA ⊓ sourceB) ⊓ sourceC))
    (target := target) (middle := cycles kernelA kernelB kernelC) boundary connecting globalMap
  intro sectionValue boundary_mem
  obtain ⟨liftValue, lift_eq⟩ := presentationConnectingMap_exact
    projection sourceA sourceB sourceC target liftAB liftAC liftBC
      mapAB mapAC mapBC sectionValue boundary_mem
  exact ⟨liftValue, Subtype.ext ((globalMap_eq liftValue).trans lift_eq)⟩

theorem finite_H0_of_presentation
    (f : P →ₗ[K] M) (A B C : Submodule K P) (V : Fin 3 → Submodule K M)
    (h0 : ∀ x ∈ A ⊓ B, f x ∈ V 0) (h1 : ∀ x ∈ A ⊓ C, f x ∈ V 1)
    (h2 : ∀ x ∈ B ⊓ C, f x ∈ V 2)
    (sur0 : ∀ x ∈ V 0, ∃ y ∈ A ⊓ B, f y = x)
    (sur1 : ∀ x ∈ V 1, ∃ y ∈ A ⊓ C, f y = x)
    (sur2 : ∀ x ∈ V 2, ∃ y ∈ B ⊓ C, f y = x)
    [Module.Finite K ↥((A ⊓ B) ⊓ C)]
    [Module.Finite K (@HasQuotient.Quotient _ _
      (Submodule.hasQuotient (R := K) (M := cycles (A.comap f.ker.subtype)
        (B.comap f.ker.subtype) (C.comap f.ker.subtype)))
      (fullBoundaries (K := K) (A.comap f.ker.subtype)
        (B.comap f.ker.subtype) (C.comap f.ker.subtype)))] :
    Module.Finite K ↥((V 0 ⊓ V 1) ⊓ V 2) := by
  let Z := (V 0 ⊓ V 1) ⊓ V 2
  obtain ⟨l0, e0⟩ := exists_presentationLift f (A ⊓ B) (V 0) Z h0 sur0
    (inf_le_left.trans inf_le_left)
  obtain ⟨l1, e1⟩ := exists_presentationLift f (A ⊓ C) (V 1) Z h1 sur1
    (inf_le_left.trans inf_le_right)
  obtain ⟨l2, e2⟩ := exists_presentationLift f (B ⊓ C) (V 2) Z h2 sur2 inf_le_right
  let f0 : ↥((A ⊓ B) ⊓ C) →ₗ[K] Z :=
    (f.domRestrict _).codRestrict Z (fun x =>
      ⟨⟨h0 x x.2.1,h1 x ⟨x.2.1.1,x.2.2⟩⟩,h2 x ⟨x.2.1.2,x.2.2⟩⟩)
  exact finite_presentationTarget f A B C Z l0 l1 l2 e0 e1 e2 f0 (fun _ => rfl)
end
end MaximalSeshadri.PlaneCech

end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Cohomology_PlaneFreeCech
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                       
section

namespace MaximalSeshadri.PlaneCech
noncomputable section
variable {K : Type*} [Field K]

lemma triangle_finite (d : ℤ) : (coneA ∩ coneB ∩ coneC d).Finite := by
  apply (Set.finite_Icc (0,0) (d,d)).subset
  rintro ⟨a,b⟩ ⟨⟨ha,hb⟩,hc⟩
  change 0 ≤ b at ha
  change 0 ≤ a at hb
  change a+b ≤ d at hc
  exact ⟨⟨hb,ha⟩,⟨by omega,by omega⟩⟩

theorem free_H0_finite (ι : Type*) [Finite ι] (d : ℤ) :
    Module.Finite K ↥((freeA (K := K) ι ⊓ freeB ι) ⊓ freeC ι d) := by
  let := Fintype.ofFinite ι
  let Q := Finsupp.supported K K (coneA ∩ coneB ∩ coneC d)
  let : Finite ↥(coneA ∩ coneB ∩ coneC d) := (triangle_finite d).to_subtype
  let : Module.Finite K Q := Module.Finite.equiv
    (Finsupp.supportedEquivFinsupp (M := K) (R := K) (coneA ∩ coneB ∩ coneC d)).symm
  let F : ↥((freeA (K := K) ι ⊓ freeB ι) ⊓ freeC ι d) →ₗ[K] (ι → Q) :=
    { toFun := fun m i => ⟨(m.1 i).coeff, by
        change _ ∈ Finsupp.supported K K (coneA ∩ coneB ∩ coneC d)
        rw [Finsupp.supported_inter,Finsupp.supported_inter]
        exact ⟨⟨m.2.1.1 i (Set.mem_univ i),m.2.1.2 i (Set.mem_univ i)⟩,
          m.2.2 i (Set.mem_univ i)⟩⟩
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  let : Module.Finite K (ι → Q) := inferInstance
  let : IsNoetherian K (ι → Q) := isNoetherian_of_isNoetherianRing_of_finite K (ι → Q)
  apply Module.Finite.of_injective F
  intro m n h
  apply Subtype.ext
  exact funext fun i => (AddMonoidAlgebra.coeffLinearEquiv K).injective
    (congrArg Subtype.val (congrFun h i))

end
end MaximalSeshadri.PlaneCech

end


end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Cohomology_ToricFreeMap
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                      
section

namespace MaximalSeshadri.PlaneCech
noncomputable section
open LaurentPlane
variable {K M : Type*} [Field K] [AddCommGroup M]
  [Module K M] [Module (LaurentPlane.Ring K) M] [IsScalarTower K (LaurentPlane.Ring K) M]

lemma smul_supported_mem (V : Submodule K M) (S : Set (ℤ × ℤ)) (e : M)
    (h : ∀ z ∈ S, T (K := K) z • e ∈ V)
    (r : LaurentPlane.Ring K) (hr : r ∈ laurentSupported S) : r • e ∈ V := by
  rw [laurentSupported_eq_span] at hr
  induction hr using Submodule.span_induction with
  | mem r hr => obtain ⟨z,hz,rfl⟩ := hr; exact h z hz
  | zero => simp
  | add r s hr hs ih ih' => simpa only [add_smul] using V.add_mem ih ih'
  | smul a r hr ih => simpa only [smul_assoc] using V.smul_mem a ih

lemma freeMap_supported {ι : Type*} [Fintype ι] (e : ι → M) (S : Set (ℤ × ℤ))
    (V : Submodule K M) (he : ∀ i z, z ∈ S → T (K := K) z • e i ∈ V)
    (m : ι → LaurentPlane.Ring K)
    (hm : ∀ i, m i ∈ laurentSupported S) : freeMap e m ∈ V := by
  apply Submodule.sum_mem
  intro i hi
  exact smul_supported_mem V S (e i) (he i) (m i) (hm i)

omit [Module K M] [IsScalarTower K (LaurentPlane.Ring K) M] in
lemma freeMap_single {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : ι → M) (i : ι) (r : LaurentPlane.Ring K) :
    freeMap e (Pi.single i r) = r • e i := by
  simp [freeMap,Pi.single_apply]

lemma single_monomial_mem {ι : Type*} [DecidableEq ι] (S : Set (ℤ × ℤ))
    (i : ι) (z : ℤ × ℤ) (hz : z ∈ S) :
    Pi.single i (T (K := K) z) ∈ Submodule.pi Set.univ (fun _ => laurentSupported S) := by
  intro j hj
  by_cases h : j=i
  · subst j
    simp only [Pi.single_eq_same]
    rw [laurentSupported_eq_span]
    exact Submodule.subset_span ⟨z,hz,rfl⟩
  · simp [Pi.single_eq_of_ne h]

end
end MaximalSeshadri.PlaneCech

end


end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Cohomology_ToricPresentation
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section

namespace MaximalSeshadri.PlaneCech
noncomputable section
open LaurentPlane
variable {K M : Type*} [Field K] [AddCommGroup M]
  [Module K M] [Module (LaurentPlane.Ring K) M]

lemma clearing_monotone (V : Fin 3 → Submodule K M)
    (stable : ∀ i z, z ∈ vertexCone i → ∀ x ∈ V i, T (K := K) z • x ∈ V i)
    (i j : Fin 3) (x : M) {n d : ℕ} (hd : d ≤ n)
    (hx : T (K := K) (d • (weight j-weight i)) • x ∈ V i) :
    T (K := K) (n • (weight j-weight i)) • x ∈ V i := by
  have he : n • (weight j-weight i) = (n-d) • (weight j-weight i) + d • (weight j-weight i) := by
    rw [← add_nsmul,Nat.sub_add_cancel hd]
  rw [he,T_add,mul_smul]
  exact stable i _ (direction_mem i j (n-d)) _ hx

theorem exists_standard_generators (V : Fin 3 → Submodule K M)
    (stable : ∀ i z, z ∈ vertexCone i → ∀ x ∈ V i, T (K := K) z • x ∈ V i)
    {ι : Fin 3 → Type*} [∀ i, Fintype (ι i)] (g : ∀ i, ι i → M)
    (hg : ∀ i a, g i a ∈ V i)
    (clear : ∀ i j (x : M), x ∈ V j →
      ∃ d : ℕ, T (K := K) (d • (weight j-weight i)) • x ∈ V i) :
    ∃ n : ℕ, ∀ (j : Fin 3) (a : ι j) (i : Fin 3),
      T (K := K) (-(n • weight i)) • (T (K := K) (n • weight j) • g j a) ∈ V i := by
  classical
  choose d hd using fun (i j : Fin 3) (a : ι j) => clear i j (g j a) (hg j a)
  let n := Finset.univ.sup (fun p : (Fin 3) × (Σ j, ι j) => d p.1 p.2.1 p.2.2)
  refine ⟨n,?_⟩
  intro j a i
  have hle : d i j a ≤ n := Finset.le_sup (f := fun p : (Fin 3) × (Σ j, ι j) => d p.1 p.2.1 p.2.2)
    (Finset.mem_univ (i,⟨j,a⟩))
  have he : -(n • weight i) + n • weight j = n • (weight j-weight i) := by
    rw [nsmul_sub]; abel
  rw [← mul_smul,← T_add,he]
  exact clearing_monotone V stable i j (g j a) hle (hd i j a)

end
end MaximalSeshadri.PlaneCech

end


end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Cohomology_ToricH1
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                 
section

namespace MaximalSeshadri.PlaneCech
noncomputable section
open LaurentPlane
variable {K M : Type*} [Field K] [AddCommGroup M]
  [Module K M]

lemma laurentSupported_inter (S U : Set (ℤ × ℤ)) :
    laurentSupported (K := K) (S ∩ U) = laurentSupported S ⊓ laurentSupported U := by
  simp only [laurentSupported,Finsupp.supported_inter,Submodule.comap_inf]

end
end MaximalSeshadri.PlaneCech

end


end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Cohomology_FreeVertices
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                      
section

namespace MaximalSeshadri.PlaneCech
noncomputable section
open LaurentPlane
variable {K : Type*} [Field K]

lemma freeVertex_zero (ι : Type*) (d : ℤ) : freeVertex (K := K) ι d 0 = freeA ι ⊓ freeB ι := by
  have he : twistCone d 0 = coneA ∩ coneB := by
    ext z
    simp [twistCone,weight,vertexCone,coneA,coneB]
  ext m
  simp only [freeVertex,freeA,freeB,he,laurentSupported_inter,Submodule.mem_inf,Submodule.mem_pi]
  aesop
lemma freeVertex_one (ι : Type*) (d : ℤ) : freeVertex (K := K) ι d 1 = freeA ι ⊓ freeC ι d := by
  have he : twistCone d 1 = coneA ∩ coneC d := by
    ext z
    simp [twistCone,weight,vertexCone,coneA,coneC]
    omega
  ext m
  simp only [freeVertex,freeA,freeC,he,laurentSupported_inter,Submodule.mem_inf,Submodule.mem_pi]
  aesop
lemma freeVertex_two (ι : Type*) (d : ℤ) : freeVertex (K := K) ι d 2 = freeB ι ⊓ freeC ι d := by
  have he : twistCone d 2 = coneB ∩ coneC d := by
    ext z
    simp [twistCone,weight,vertexCone,coneB,coneC]
    omega
  ext m
  simp only [freeVertex,freeB,freeC,he,laurentSupported_inter,Submodule.mem_inf,Submodule.mem_pi]
  aesop

end
end MaximalSeshadri.PlaneCech

end


end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Cohomology_ToricVertexPresentation
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                 
section

namespace MaximalSeshadri.PlaneCech
noncomputable section
open LaurentPlane
variable {K M : Type*} [Field K] [AddCommGroup M]
  [Module K M] [Module (LaurentPlane.Ring K) M] [IsScalarTower K (LaurentPlane.Ring K) M]

lemma freeMap_vertex {ι : Type*} [Fintype ι]
    (V : Fin 3 → Submodule K M)
    (stable : ∀ i z, z ∈ vertexCone i → ∀ x ∈ V i, T (K := K) z • x ∈ V i)
    (n : ℕ) (e : ι → M) (he : ∀ a, StandardGenerator V n (e a))
    (i : Fin 3) (x : ι → LaurentPlane.Ring K) (hx : x ∈ freeVertex ι (-(n : ℤ)) i) :
    freeMap (K := K) e x ∈ V i := by
  apply freeMap_supported e (twistCone (-(n : ℤ)) i) (V i)
  · intro a z hz
    have hcone : z + n • weight i ∈ vertexCone i := by
      simpa [twistCone] using hz
    have h := stable i (z + n • weight i) hcone _ (he a i)
    rw [← mul_smul,← T_add,add_neg_cancel_right] at h
    exact h
  · exact fun a => hx a (Set.mem_univ a)

theorem toric_free_presentation
    (V : Fin 3 → Submodule K M)
    (stable : ∀ i z, z ∈ vertexCone i → ∀ x ∈ V i, T (K := K) z • x ∈ V i)
    {ι : Fin 3 → Type*} [∀ i, Fintype (ι i)] (g : ∀ i, ι i → M)
    (hg : ∀ i a, g i a ∈ V i)
    (hgen : ∀ i, V i = monomialSpan (K := K) (vertexCone i) (g i))
    (clear : ∀ i j (x : M), x ∈ V j →
      ∃ d : ℕ, T (K := K) (d • (weight j-weight i)) • x ∈ V i) :
    ∃ n : ℕ, ∃ e : (Σ i, ι i) → M,
      (∀ i x, x ∈ freeVertex (K := K) (Σ i, ι i) (-(n : ℤ)) i → freeMap (K := K) e x ∈ V i) ∧
      ∀ i x, x ∈ V i → ∃ y ∈ freeVertex (K := K) (Σ i, ι i) (-(n : ℤ)) i, freeMap (K := K) e y = x := by
  classical
  obtain ⟨n,hn⟩ := exists_standard_generators V stable g hg clear
  let e : (Σ i, ι i) → M := fun a => T (K := K) (n • weight a.1) • g a.1 a.2
  have he (a : Σ i, ι i) : StandardGenerator V n (e a) := hn a.1 a.2
  refine ⟨n,e,freeMap_vertex V stable n e he,?_⟩
  intro i x hx
  have hs : V i ≤ (freeVertex (K := K) (Σ i, ι i) (-(n : ℤ)) i).map
      ((freeMap (K := K) e).restrictScalars K) := by
    rw [hgen i]
    change Submodule.span K _ ≤ _
    apply Submodule.span_le.mpr
    rintro _ ⟨a,z,hz,rfl⟩
    refine Submodule.mem_map.mpr
      ⟨Pi.single (⟨i,a⟩ : Σ vertex, ι vertex) (T (z-n • weight i)),?_,?_⟩
    · apply single_monomial_mem
      change z-n • weight i - (-(n : ℤ)) • weight i ∈ vertexCone i
      simpa using hz
    · rw [LinearMap.restrictScalars_apply,freeMap_single]
      change T (K := K) (z-n • weight i) • (T (n • weight i) • g i a) = _
      rw [← mul_smul,← T_add,sub_add_cancel]
  exact Submodule.mem_map.mp (hs hx)
end
end MaximalSeshadri.PlaneCech

end


end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Cohomology_ToricH0
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.jetIndexFinite _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                 
section

namespace MaximalSeshadri.PlaneCech
noncomputable section
open LaurentPlane
variable {K M : Type*} [Field K] [AddCommGroup M]
  [Module K M] [Module (LaurentPlane.Ring K) M] [IsScalarTower K (LaurentPlane.Ring K) M]

theorem toric_H0_finite_s01_oai (V : Fin 3 → Submodule K M)
    (stable : ∀ i z, z ∈ vertexCone i → ∀ x ∈ V i, T (K := K) z • x ∈ V i)
    {ι : Fin 3 → Type*} [∀ i, Fintype (ι i)] (g : ∀ i, ι i → M)
    (hg : ∀ i a, g i a ∈ V i)
    (hgen : ∀ i, V i = monomialSpan (K := K) (vertexCone i) (g i))
    (clear : ∀ i j (x : M), x ∈ V j →
      ∃ d : ℕ, T (K := K) (d • (weight j-weight i)) • x ∈ V i) :
    Module.Finite K ↥((V 0 ⊓ V 1) ⊓ V 2) := by
  classical
  obtain ⟨n,e,hv,hs⟩ := toric_free_presentation V stable g hg hgen clear
  let N := (freeMap (K := K) e).ker
  let := free_H0_finite (K := K) (Σ i, ι i) (-(n : ℤ))
  let f := (freeMap (K := K) e).restrictScalars K
  let NA := (freeA (K := K) (Σ i, ι i)).comap f.ker.subtype
  let NB := (freeB (K := K) (Σ i, ι i)).comap f.ker.subtype
  let NC := (freeC (K := K) (Σ i, ι i) (-(n : ℤ))).comap f.ker.subtype
  let : AddCommGroup (cycles NA NB NC) := by
    let group := Submodule.addCommGroup (R := K) (M := NA × NB × NC) (cycles NA NB NC)
    exact group
  let : Module K (cycles NA NB NC) := by
    let moduleStructure := Submodule.module (R := K) (M := NA × NB × NC) (cycles NA NB NC)
    exact moduleStructure
  let : Module.Finite K (@HasQuotient.Quotient _ _
      (Submodule.hasQuotient (R := K) (M := cycles NA NB NC))
      (fullBoundaries NA NB NC)) :=
    kernel_H1_finite_s01 N (-(n : ℤ))
  apply finite_H0_of_presentation f
    (freeA _) (freeB _) (freeC _ (-(n : ℤ))) V
  · intro x hx
    exact hv 0 x (by rwa [freeVertex_zero])
  · intro x hx
    exact hv 1 x (by rwa [freeVertex_one])
  · intro x hx
    exact hv 2 x (by rwa [freeVertex_two])
  · intro x hx
    obtain ⟨y,hy,he⟩ := hs 0 x hx
    exact ⟨y,by rwa [freeVertex_zero] at hy,he⟩
  · intro x hx
    obtain ⟨y,hy,he⟩ := hs 1 x hx
    exact ⟨y,by rwa [freeVertex_one] at hy,he⟩
  · intro x hx
    obtain ⟨y,hy,he⟩ := hs 2 x hx
    exact ⟨y,by rwa [freeVertex_two] at hy,he⟩
end
end MaximalSeshadri.PlaneCech

end

end OAI
end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.MaximalSeshadri.PlaneCech.toric_H0_finite_s01_oai.{u_1, u_2, u_3} := @OAI.MaximalSeshadri.PlaneCech.toric_H0_finite_s01_oai.{u_1, u_2, u_3}
