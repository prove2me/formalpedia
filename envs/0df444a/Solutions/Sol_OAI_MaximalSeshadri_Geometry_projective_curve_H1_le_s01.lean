-- Prove2me | solution 1 for OAI.MaximalSeshadri.Geometry.projective_curve_H1_le_s01
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T15:16:28.569966+00:00
-- url     : https://prove2.me/submissions/f6982c74-cf0d-4a06-b600-7d49f1ceeb6f

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_Q223SES009
import Theorems.Thm_OAI_MaximalSeshadri_Geometry_projective_curve_cohomology_finite_s01

section
-- module Solutions.Q223_SES.Seshadri_Sheaves_SupportedSheaf
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.BaseSections.instAddCommGroupCarrierSections _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.instAddCommGroupCarrierOpenSections _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                        
section

namespace MaximalSeshadri.FiniteSupport
noncomputable section
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry

variable {X : TopCat.{0}}

lemma finite_closed_support_restriction_surjective
    (F : X.Sheaf AddCommGrpCat.{0}) (S : Set X) (hfin : S.Finite)
    (hclosed : ∀ x ∈ S, IsClosed ({x} : Set X))
    (hsupp : ∀ x ∉ S, Subsingleton (F.presheaf.stalk x))
    {U V : Opens X} (i : V ⟶ U) : Function.Surjective (F.obj.map i.op) := by
  classical
  intro s
  have hcS : IsClosed (S ∩ V) := by
    rw [← Set.biUnion_of_singleton (S ∩ (V : Set X))]
    exact (hfin.subset Set.inter_subset_left).isClosed_biUnion
      (fun x hx => hclosed x hx.1)
  let W : Opens X := U ⊓ ⟨(S ∩ V)ᶜ,hcS.isOpen_compl⟩
  let D : Bool → Opens X := fun b => if b then V else W
  let e : ∀ b, D b ⟶ U := fun b => homOfLE (by
    cases b
    · exact inf_le_left
    · exact i.le)
  have hcover : U ≤ ⨆ b, D b := by
    intro x hx
    by_cases hv : x ∈ V
    · exact Opens.mem_iSup.mpr ⟨true,hv⟩
    · exact Opens.mem_iSup.mpr ⟨false,hx,fun h => hv h.2⟩
  let t : ∀ b, F.obj.obj (op (D b)) := fun b => match b with
    | true => s
    | false => 0
  have hz : ∀ b c, b ≠ c → Subsingleton (F.obj.obj (op (D b ⊓ D c))) := by
    intro b c hbc
    apply sections_subsingleton_of_stalks
    intro x hx
    apply hsupp
    intro hs
    cases b <;> cases c
    · exact hbc rfl
    · exact hx.1.2 ⟨hs,hx.2⟩
    · exact hx.2.2 ⟨hs,hx.1⟩
    · exact hbc rfl
  have hcomp : TopCat.Presheaf.IsCompatible F.obj D t := by
    intro b c
    by_cases he : b = c
    · subst c; rfl
    · let := hz b c he
      exact Subsingleton.elim _ _
  obtain ⟨a,ha,_⟩ := F.existsUnique_gluing' D U e hcover t hcomp
  exact ⟨a,ha true⟩

lemma finite_closed_support_flasque (F : X.Sheaf AddCommGrpCat.{0})
    (S : Set X) (hfin : S.Finite)
    (hclosed : ∀ x ∈ S, IsClosed ({x} : Set X))
    (hsupp : ∀ x ∉ S, Subsingleton (F.presheaf.stalk x)) : F.IsFlasque where
  epi i := (AddCommGrpCat.epi_iff_surjective _).mpr
    (finite_closed_support_restriction_surjective F S hfin hclosed hsupp i.unop)

end
end MaximalSeshadri.FiniteSupport
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Divisors_SectionCokernel
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.BaseSections.instAddCommGroupCarrierSections _root_.OAI.MaximalSeshadri.Geometry.LineBundle.finitePresentation _root_.OAI.MaximalSeshadri.Geometry.LineBundle.localGenerators_locallyFree _root_.OAI.MaximalSeshadri.Geometry.LineBundle.locallyFree _root_.OAI.MaximalSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.instAddCommGroupCarrierOpenSections _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.line_isIso _root_.OAI.MaximalSeshadri.PullbackTensor.unit_isIso _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.TensorPure.tensorSection_isIso
attribute [-simp] _root_.OAI.MaximalSeshadri.Frames.endUnit_val _root_.OAI.MaximalSeshadri.Projective.ratioOn_full _root_.OAI.MaximalSeshadri.Projective.ratioOn_self _root_.OAI.MaximalSeshadri.Projective.ratioUnitOn_val _root_.OAI.MaximalSeshadri.Projective.scalarEnd_one _root_.OAI.MaximalSeshadri.Projective.scalarEnd_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                         
section

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open MaximalSeshadri.Frames MaximalSeshadri.SectionOpens

variable {X : Scheme.{0}}

theorem LineBundle.cokernel_flasque [IsIntegral X] [IsNoetherian X]
    (hd : topologicalKrullDim X ≤ 1) (L : LineBundle X)
    (s : O X ⟶ L.sheaf) (hs : s ≠ 0) :
    TopCat.Sheaf.IsFlasque ((SheafOfModules.toSheaf X.ringCatSheaf).obj (cokernel s)) := by
  let S : Set X := (isoOpen s : Set X)ᶜ
  have hfin : S.Finite := L.cokernel_support_finite hd s hs
  have hclosed : ∀ x ∈ S, IsClosed ({x} : Set X) := by
    intro x hx
    have hc : closure ({x} : Set X) ⊆ S :=
      closure_minimal (Set.singleton_subset_iff.mpr hx) (isoOpen s).isOpen.isClosed_compl
    have hsub : (closure ({x} : Set X)).Subsingleton := by
      apply proper_irreducible_closed_subsingleton hd isClosed_closure
        isIrreducible_singleton.closure
      intro he
      have hb : S = Set.univ := Set.eq_univ_of_univ_subset (he ▸ hc)
      exact L.isoOpen_ne_bot s hs (SetLike.coe_injective (by simpa [S] using hb))
    have he : closure ({x} : Set X) = {x} := by
      apply Set.Subset.antisymm
      · intro y hy
        exact hsub hy (subset_closure (Set.mem_singleton x))
      · exact subset_closure
    exact he ▸ isClosed_closure
  apply FiniteSupport.finite_closed_support_flasque _ S hfin hclosed
  intro x hx
  apply cokernel_stalk_subsingleton s x
  exact not_not.mp hx

end
end MaximalSeshadri.Geometry
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Intersection_SectionEuler
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.line_isIso _root_.OAI.MaximalSeshadri.PullbackTensor.unit_isIso _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.TensorPure.tensorSection_isIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                      
section

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open MaximalSeshadri.Projective MaximalSeshadri.Frames

variable {X : Scheme.{0}} [IsIntegral X] [IsNoetherian X]

lemma LineBundle.cokernel_ext_zero (hd : topologicalKrullDim X ≤ 1)
    (L : LineBundle X) (s : O X ⟶ L.sheaf) (hs : s ≠ 0)
    (n : ℕ) (z : cohomology (cokernel s) (n+1)) : z = 0 := by
  let := L.cokernel_flasque hd s hs
  exact FlasqueCohomology.flasque_ext_zero X.ringCatSheaf n (cokernel s) z

end
end MaximalSeshadri.Geometry
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Geometry_SurfaceTopGrowth
attribute [-instance] _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                          
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.Projective

variable {X : Scheme.{0}}
local instance instHasExtModules_solutions_1 : HasExt.{1} X.Modules := schemeHasExt

theorem cohomologyDimension_le_of_shortExact (p : X ⟶ Spec (CommRingCat.of ℂ))
    {T : ShortComplex X.Modules} (hT : T.ShortExact) (n : ℕ)
    (hf : letI := Module.compHom (cohomology T.X₁ n) (baseScalars p)
      Module.Finite ℂ (cohomology T.X₁ n))
    [Subsingleton (cohomology T.X₃ n)] :
    cohomologyDimension p T.X₂ n ≤ cohomologyDimension p T.X₁ n := by
  let := Module.compHom (cohomology T.X₁ n) (baseScalars p)
  let := Module.compHom (cohomology T.X₂ n) (baseScalars p)
  let := hf
  let g := (Ext.mk₀ T.f).postcompOfLinear Γ(X,⊤) (O X) (add_zero n)
  let g' : cohomology T.X₁ n →ₗ[ℂ] cohomology T.X₂ n :=
    { toFun := g
      map_add' := g.map_add
      map_smul' := fun r x => g.map_smul (baseScalars p r) x }
  apply LinearMap.finrank_le_finrank_of_surjective (f := g')
  intro x
  exact Ext.covariant_sequence_exact₂ (structureSheaf X) hT x (Subsingleton.elim _ _)

end
end MaximalSeshadri.Geometry

end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Cohomology_CurveH1Bound
attribute [-instance] _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                      
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.Projective

variable {X : Scheme.{0}} [IsIntegral X] [IsNoetherian X]

omit [IsIntegral X] [AlgebraicGeometry.IsNoetherian X] in
lemma curve_euler_expansion (p : X ⟶ Spec (CommRingCat.of ℂ)) (M : X.Modules) :
    eulerCharacteristic p 1 M =
      (cohomologyDimension p M 0 : ℤ) - (cohomologyDimension p M 1 : ℤ) := by
  simp [eulerCharacteristic,Finset.sum_range_succ,sub_eq_add_neg]

theorem projective_curve_H1_le_s01_oai {σ : Type} [Fintype σ]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (hd : topologicalKrullDim X = 1) {A : X.Modules}
    (a : σ → (O X ⟶ A)) (ha : (⨆ i, SectionOpens.isoOpen (a i)) = ⊤)
    [IsClosedImmersion (sectionsMorphism (baseScalars p) a ha)]
    (M : LineBundle X)
    (hdeg : 0 ≤ eulerCharacteristic p 1 M.sheaf - eulerCharacteristic p 1 (O X)) :
    cohomologyDimension p M.sheaf 1 ≤ cohomologyDimension p (O X) 1 := by
  classical
  have : IsClosedImmersion (sectionsMorphism
    (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom) a ha) :=
      inferInstanceAs (IsClosedImmersion (sectionsMorphism (baseScalars p) a ha))
  by_cases h : ∃ s : O X ⟶ M.sheaf, s ≠ 0
  · obtain ⟨s,hs⟩ := h
    have : Subsingleton (cohomology (cokernel s) 1) := ⟨fun x y =>
      (M.cokernel_ext_zero hd.le s hs 0 x).trans (M.cokernel_ext_zero hd.le s hs 0 y).symm⟩
    let B : LineBundle X := ⟨O X, fun x =>
      ⟨⊤,trivial,⟨Scheme.Modules.restrictUnitIso (⊤ : X.Opens).ι⟩⟩⟩
    exact cohomologyDimension_le_of_shortExact p (M.section_shortExact s hs) 1
      (projective_curve_cohomology_finite_s01 p hd a ha B 1)
  · have hz : cohomologyDimension p M.sheaf 0 = 0 := by
      let := Module.compHom (cohomology M.sheaf 0) (baseScalars p)
      have : Subsingleton (cohomology M.sheaf 0) := ⟨fun x y => by
        apply (Ext.linearEquiv₀ (R := Γ(X,⊤))).injective
        apply Eq.trans (not_exists.mp h _ |> not_not.mp)
        exact (not_exists.mp h _ |> not_not.mp).symm⟩
      exact Module.finrank_zero_of_subsingleton
    rw [curve_euler_expansion,curve_euler_expansion,hz] at hdeg
    have h0 : (0 : ℤ) ≤ cohomologyDimension p (O X) 0 := Nat.cast_nonneg _
    exact_mod_cast (show (cohomologyDimension p M.sheaf 1 : ℤ) ≤
      cohomologyDimension p (O X) 1 by omega)

end
end MaximalSeshadri.Geometry

end

end OAI
end

theorem solution : type_of% @OAI.MaximalSeshadri.Geometry.projective_curve_H1_le_s01_oai := @OAI.MaximalSeshadri.Geometry.projective_curve_H1_le_s01_oai
