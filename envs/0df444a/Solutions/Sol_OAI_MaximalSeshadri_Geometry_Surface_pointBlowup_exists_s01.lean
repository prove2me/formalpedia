-- Prove2me | solution 1 for OAI.MaximalSeshadri.Geometry.Surface.pointBlowup_exists_s01
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T15:15:54.704207+00:00
-- url     : https://prove2.me/submissions/3753faf0-d06a-4e74-8442-14892758cd54

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_Q223SES009
import Theorems.Thm_OAI_MaximalSeshadri_FinitePointBlowup_smooth_finite_point_blowup_s01
import Theorems.Thm_OAI_MaximalSeshadri_Geometry_IsBlowup_ample_exceptional_twist_s01
import Theorems.Thm_OAI_MaximalSeshadri_Geometry_LineBundle_power_section_embedding_s01
import Theorems.Thm_OAI_MaximalSeshadri_Geometry_local_powerSection_coefficient_s01

section
-- module Solutions.Q223_SES.Seshadri_Sheaves_TensorFrames
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.unit_isIso _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TensorPure.tensorSection_isIso _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
noncomputable section
open CategoryTheory
open CategoryTheory.Category CategoryTheory.Functor
universe v u v₁ v₂ u₁ u₂

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry
open MaximalSeshadri.Frames
variable {X : Scheme}

lemma local_powerSection_coefficient_unit (U : X.Opens) (n : ℕ) :
    IsUnit (endValue (powerRestrictionUnit U n).hom) := by
  have h : IsIso (powerRestrictionUnit U n).hom := inferInstance
  exact (end_isIso_iff (powerRestrictionUnit U n).hom).mp h

end
end MaximalSeshadri.Geometry


end
end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Sheaves_SectionOpens
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.LineBundle.finitePresentation _root_.OAI.MaximalSeshadri.Geometry.LineBundle.localGenerators_locallyFree _root_.OAI.MaximalSeshadri.Geometry.LineBundle.locallyFree _root_.OAI.MaximalSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.line_isIso _root_.OAI.MaximalSeshadri.PullbackTensor.unit_isIso _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TensorPure.tensorSection_isIso _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
noncomputable section
open CategoryTheory
open CategoryTheory.Category CategoryTheory.Functor
universe v u v₁ v₂ u₁ u₂

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry
open MaximalSeshadri.Frames
variable {X : Scheme}

theorem LineBundle.sectionOpen_power (L : LineBundle X) (s : GlobalSections X L.sheaf)
    {n : ℕ} (hn : 0 < n) :
    sectionOpen X (powerSection s n) = sectionOpen X s := by
  have hlocal (U : X.Opens) (e : L.sheaf.restrict U.ι ≅ structureSheaf U.toScheme) :
      U.ι ⁻¹ᵁ sectionOpen X (powerSection s n) = U.ι ⁻¹ᵁ sectionOpen X s := by
    change U.ι ⁻¹ᵁ SectionOpens.isoOpen (powerSection s n) =
      U.ι ⁻¹ᵁ SectionOpens.isoOpen s
    calc
      _ = U.toScheme.basicOpen (coefficient (localPowerFrame U e n)
          (restrictSection U.ι (powerSection s n))) :=
        preimage_isoOpen (powerSection s n) U.ι (localPowerFrame U e n)
      _ = U.toScheme.basicOpen (endValue (powerRestrictionUnit U n).hom *
          coefficient e (restrictSection U.ι s) ^ n) :=
        congrArg U.toScheme.basicOpen (local_powerSection_coefficient_s01 U e s n)
      _ = U.toScheme.basicOpen (coefficient e (restrictSection U.ι s)) := by
        rw [Scheme.basicOpen_mul,
          Scheme.basicOpen_of_isUnit _ (local_powerSection_coefficient_unit U n),
          top_inf_eq]
        exact U.toScheme.basicOpen_pow (coefficient e (restrictSection U.ι s)) hn
      _ = _ := (preimage_isoOpen s U.ι e).symm
  ext x
  obtain ⟨U, hxU, ⟨e⟩⟩ := L.locallyRankOne x
  have h := congrArg (fun V : U.toScheme.Opens => (⟨x, hxU⟩ : U.toScheme) ∈ V) (hlocal U e)
  exact Iff.of_eq h

end
end MaximalSeshadri.Geometry


end
end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Sheaves_PowerExtension
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.LineBundle.finitePresentation _root_.OAI.MaximalSeshadri.Geometry.LineBundle.localGenerators_locallyFree _root_.OAI.MaximalSeshadri.Geometry.LineBundle.locallyFree _root_.OAI.MaximalSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.line_isIso _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
noncomputable section
open CategoryTheory
open CategoryTheory.Category CategoryTheory.Functor
universe v u v₁ v₂ u₁ u₂

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace TopologicalSpace.Opens
open scoped AlgebraicGeometry
variable {X : Scheme}

theorem LineBundle.common_degree (L : LineBundle X) {ι : Type} [Fintype ι]
    (d : ι → ℕ) (hd : ∀ i, 0 < d i)
    (s : ∀ i, GlobalSections X (modulePow X L.sheaf (d i))) :
    ∃ n : ℕ, 0 < n ∧ ∃ t : ι → GlobalSections X (modulePow X L.sheaf n),
      ∀ i, sectionOpen X (t i) = sectionOpen X (s i) := by
  classical
  let n := ∏ i, d i
  have hn : 0 < n := Finset.prod_pos (fun i _ => hd i)
  have hdiv (i : ι) : d i ∣ n := Finset.dvd_prod_of_mem d (Finset.mem_univ i)
  have heq (i : ι) : d i * (n / d i) = n := Nat.mul_div_cancel' (hdiv i)
  let e (i : ι) : modulePow X (modulePow X L.sheaf (d i)) (n / d i) ≅
      modulePow X L.sheaf n :=
    linePowerMul L (d i) (n / d i) ≪≫ eqToIso (congrArg (modulePow X L.sheaf) (heq i))
  refine ⟨n, hn, fun i => powerSection (s i) (n / d i) ≫ (e i).hom, ?_⟩
  intro i
  change SectionOpens.isoOpen (powerSection (s i) (n / d i) ≫ (e i).hom) = _
  rw [SectionOpens.isoOpen_postcomp]
  exact (L.pow (d i)).sectionOpen_power (s i)
    (Nat.div_pos (Nat.le_of_dvd hn (hdiv i)) (hd i))

theorem LineBundle.ample_common_degree_cover [CompactSpace X] (L : LineBundle X)
    (hL : LineBundle.IsAmple X L) :
    ∃ n : ℕ, 0 < n ∧ ∃ l : ℕ,
      ∃ s : Fin l → GlobalSections X (modulePow X L.sheaf n),
        (⨆ i, sectionOpen X (s i)) = ⊤ ∧
        (∀ i, IsAffineOpen (sectionOpen X (s i))) ∧
        (∀ i, (sectionOpen X (s i) : Set X).Nonempty) := by
  classical
  have hex (x : X) := hL x ⊤ (by trivial)
  choose d hd s hs hst ha using hex
  obtain ⟨I, hI⟩ := isCompact_univ.elim_finite_subcover
    (fun x => (sectionOpen X (s x) : Set X)) (fun x => (sectionOpen X (s x)).isOpen)
    (by intro x _; exact Set.mem_iUnion.mpr ⟨x, hs x⟩)
  obtain ⟨n, hn, t, ht⟩ := L.common_degree (fun i : I => d i.val)
    (fun i => hd i.val) (fun i => s i.val)
  let e := (Fintype.equivFin I).symm
  refine ⟨n, hn, Fintype.card I, fun i => t (e i), ?_, ?_, ?_⟩
  · apply top_unique
    intro x _
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hI (show x ∈ Set.univ from trivial))
    obtain ⟨hi, hx⟩ := Set.mem_iUnion.mp hi
    apply Opens.mem_iSup.mpr
    refine ⟨e.symm ⟨i, hi⟩, ?_⟩
    change x ∈ sectionOpen X (t (e (e.symm ⟨i, hi⟩)))
    rw [Equiv.apply_symm_apply, ht]
    exact hx
  · intro i
    rw [ht]
    exact ha (e i).val
  · intro i
    rw [ht]
    exact ⟨(e i).val, hs (e i).val⟩

end
end MaximalSeshadri.Geometry


end
end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Blowup_LocalUniversal
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.LineBundle.finitePresentation _root_.OAI.MaximalSeshadri.Geometry.LineBundle.localGenerators_locallyFree _root_.OAI.MaximalSeshadri.Geometry.LineBundle.locallyFree _root_.OAI.MaximalSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.line_isIso _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section

namespace MaximalSeshadri.InvertibleLocal

noncomputable section
open CategoryTheory AlgebraicGeometry
open MaximalSeshadri.Geometry
variable {X Y Z : Scheme}

lemma invertible_of_cover (I : X.IdealSheafData) (f : Y ⟶ X) (C : Y.OpenCover)
    (hf : ∀ i, InvertiblePullbackIdeal I (C.f i ≫ f)) :
    InvertiblePullbackIdeal I f := by
  let J : LineBundle Y := {
    sheaf := IdealModule.closedModule (I.comap f)
    locallyRankOne y := by
      let i := C.idx y
      obtain ⟨z, hz⟩ := C.covers y
      obtain ⟨U, hzU, r, hr, hIr⟩ := local_equations (hf i) z
      let j := U.1.ι ≫ C.f i
      have he : ((I.comap f).comap j).ideal ⟨⊤, isAffineOpen_top U.1.toScheme⟩ =
          Ideal.span {r} := by
        simpa only [j, Scheme.IdealSheafData.comap_comp] using hIr
      obtain ⟨e⟩ := IdealModule.frame_restriction (I.comap f) j r he hr.1
      refine ⟨j.opensRange, ?_, ⟨IdealModule.frameOnRange _ j e⟩⟩
      exact ⟨⟨z, hzU⟩, hz⟩ }
  have : Mono (IdealModule.closedInclusion (I.comap f)) :=
    inferInstanceAs (Mono (IdealModule.inclusion (I.comap f).subschemeι))
  refine ⟨J, IdealModule.closedInclusion (I.comap f), this, ?_⟩
  intro U V e
  change ((IdealModule.closedInclusion (I.comap f)).val.app (Opposite.op U.1)).hom.range = _
  rw [IdealModule.closed_image]
  exact IdealPullback.comap_ideal I f U V e

end
end MaximalSeshadri.InvertibleLocal


end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Blowup_Gluing
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.BlowupGluing.scheme_isReduced _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.instIsOpenImmersionComplementLift _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MaximalSeshadri.BlowupGluing
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MaximalSeshadri.Geometry

variable {X : Scheme.{0}} (I : X.IdealSheafData)

lemma local_pullback (U : X.AffineZariskiSite) :
    IsPullback (localProjection I U) ((cover I).f U) U.toOpens.ι (projection I) :=
  (gluing I).isPullback_natTrans_ι_toBase U

end

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MaximalSeshadri.Geometry

variable {X : Scheme.{0}} (I : X.IdealSheafData)

lemma projection_invertible : InvertiblePullbackIdeal I (projection I) := by
  apply InvertibleLocal.invertible_of_cover I (projection I) (cover I)
  intro U
  apply (congrArg (InvertiblePullbackIdeal I) (cover_projection I U)).mpr
  apply (InvertibleLocal.invertible_congr
    (Scheme.IdealSheafData.comap_comp I (localProjection I U) U.toOpens.ι)).mpr
  exact (local_isBlowup I U).1

lemma test_invertible {Y : Scheme.{0}} (f : Y ⟶ X)
    (hf : InvertiblePullbackIdeal I f) (U : X.AffineZariskiSite) :
    InvertiblePullbackIdeal (localCentre I U) (pullback.snd f U.toOpens.ι) := by
  apply (InvertibleLocal.invertible_congr (I' := I)
    (f' := pullback.fst f U.toOpens.ι ≫ f) ?_).mpr
  · exact InvertibleLocal.invertible_restrict_general I f hf (pullback.fst f U.toOpens.ι)
  · change ((I.comap U.toOpens.ι).comap (pullback.snd f U.toOpens.ι)) = _
    rw [← Scheme.IdealSheafData.comap_comp, pullback.condition]

lemma hom_ext {Y : Scheme.{0}} (f : Y ⟶ X) (hf : InvertiblePullbackIdeal I f)
    (g h : Y ⟶ scheme I) (hg : g ≫ projection I = f) (hh : h ≫ projection I = f) : g = h := by
  let C : Y.OpenCover := (baseCover I).pullback₁ f
  apply C.hom_ext
  intro U
  let s := pullback.snd f U.toOpens.ι
  let t := pullback.fst f U.toOpens.ι
  have eg : s ≫ U.toOpens.ι = (t ≫ g) ≫ projection I := by
    rw [Category.assoc, hg]
    exact (pullback.condition (f := f) (g := U.toOpens.ι)).symm
  have eh : s ≫ U.toOpens.ι = (t ≫ h) ≫ projection I := by
    rw [Category.assoc, hh]
    exact (pullback.condition (f := f) (g := U.toOpens.ι)).symm
  let g' := (local_pullback I U).lift s (t ≫ g) eg
  let h' := (local_pullback I U).lift s (t ≫ h) eh
  have he : g' = h' := (local_isBlowup I U).hom_ext s (test_invertible I f hf U)
    ((local_pullback I U).lift_fst _ _ _) ((local_pullback I U).lift_fst _ _ _)
  have he' := congrArg (fun k => k ≫ (cover I).f U) he
  change t ≫ g = t ≫ h
  exact ((local_pullback I U).lift_snd s (t ≫ g) eg).symm.trans
    (he'.trans ((local_pullback I U).lift_snd s (t ≫ h) eh))

theorem universal {Y : Scheme.{0}} (f : Y ⟶ X) (hf : InvertiblePullbackIdeal I f) :
    ∃! h : Y ⟶ scheme I, h ≫ projection I = f := by
  classical
  let C : Y.OpenCover := (baseCover I).pullback₁ f
  let l (U : X.AffineZariskiSite) : C.X U ⟶ localScheme I U :=
    ((local_isBlowup I U).2 _ _ (test_invertible I f hf U)).choose
  have hl (U : X.AffineZariskiSite) : l U ≫ localProjection I U = pullback.snd f U.toOpens.ι :=
    ((local_isBlowup I U).2 _ _ (test_invertible I f hf U)).choose_spec.1
  let g (U : C.I₀) : C.X U ⟶ scheme I := l U ≫ (cover I).f U
  have hg (U : C.I₀) : g U ≫ projection I = C.f U ≫ f := by
    exact (Category.assoc (l U) ((cover I).f U) (projection I)).trans
      ((congrArg (l U ≫ ·) (cover_projection I U)).trans
        ((Category.assoc (l U) (localProjection I U) U.toOpens.ι).symm.trans
          ((congrArg (· ≫ U.toOpens.ι) (hl U)).trans
            (pullback.condition (f := f) (g := U.toOpens.ι)).symm)))
  have hcompat (U V : C.I₀) : pullback.fst (C.f U) (C.f V) ≫ g U =
      pullback.snd (C.f U) (C.f V) ≫ g V := by
    let j := pullback.fst (C.f U) (C.f V) ≫ C.f U
    apply hom_ext I (j ≫ f)
    · exact InvertibleLocal.invertible_restrict_general I f hf j
    · rw [Category.assoc, hg]
      rfl
    · rw [Category.assoc, hg]
      exact (pullback.condition_assoc f).symm
  refine ⟨C.glueMorphisms g hcompat, ?_, ?_⟩
  · apply C.hom_ext
    intro U
    rw [← Category.assoc, Scheme.Cover.ι_glueMorphisms C]
    exact hg U
  · intro h hh
    apply hom_ext I f hf h _ hh
    apply C.hom_ext
    intro U
    rw [← Category.assoc, Scheme.Cover.ι_glueMorphisms C]
    exact hg U

theorem isBlowup : IsBlowup I (projection I) :=
  ⟨projection_invertible I, fun _ f hf => universal I f hf⟩

end
end MaximalSeshadri.BlowupGluing


end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Geometry_GeneratedEtaleCoordinates
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.jetIndexFinite _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.instIsScalarTowerSubtypePolynomialMemSubalgebraReesAlgebraSubmodulePieceOfNatNat _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                              

namespace MaximalSeshadri.AlgebraicJets
noncomputable section
open KaehlerDifferential

section CoordinateBasis
variable {R S ι : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [Algebra (MvPolynomial ι R) S] [IsScalarTower R (MvPolynomial ι R) S]

theorem formallyUnramified_polynomial_of_basis
    (b : Module.Basis ι S Ω[S⁄R])
    (hb : ∀ i, b i = D R S (algebraMap (MvPolynomial ι R) S (MvPolynomial.X i))) :
    Algebra.FormallyUnramified (MvPolynomial ι R) S := by
  have hz : KaehlerDifferential.map R (MvPolynomial ι R) S S = 0 := by
    apply b.ext
    intro i
    rw [hb, KaehlerDifferential.map_D]
    change D (MvPolynomial ι R) S
      (algebraMap (MvPolynomial ι R) S (MvPolynomial.X i)) = 0
    exact Derivation.map_algebraMap _ _
  constructor
  constructor
  intro x y
  obtain ⟨x, rfl⟩ := KaehlerDifferential.map_surjective R (MvPolynomial ι R) S x
  obtain ⟨y, rfl⟩ := KaehlerDifferential.map_surjective R (MvPolynomial ι R) S y
  rw [hz]
  rfl

theorem formallySmooth_polynomial_of_basis [Algebra.FormallySmooth R S]
    (b : Module.Basis ι S Ω[S⁄R])
    (hb : ∀ i, b i = D R S (algebraMap (MvPolynomial ι R) S (MvPolynomial.X i))) :
    Algebra.FormallySmooth (MvPolynomial ι R) S := by
  classical
  apply Algebra.FormallySmooth.of_comp_surjective
  intro B _ _ I hI f
  let : Algebra R B := Algebra.compHom B (algebraMap R (MvPolynomial ι R))
  let : IsScalarTower R (MvPolynomial ι R) B := IsScalarTower.of_algebraMap_eq' rfl
  obtain ⟨g, hg⟩ := Algebra.FormallySmooth.comp_surjective R S I hI (f.restrictScalars R)
  let : Algebra S B := g.toRingHom.toAlgebra
  let : IsScalarTower R S B := IsScalarTower.of_algebraMap_eq' g.comp_algebraMap.symm
  let correction (i : ι) : I := ⟨algebraMap (MvPolynomial ι R) B (MvPolynomial.X i) -
      g (algebraMap (MvPolynomial ι R) S (MvPolynomial.X i)), by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_sub, sub_eq_zero]
    change _ = (Ideal.Quotient.mkₐ R I) (g _)
    rw [← AlgHom.comp_apply, hg]
    exact (f.commutes _).symm⟩
  let d : Derivation R S I := (b.constr S correction).compDer (D R S)
  let g' : S →ₐ[R] B := liftOfDerivationToSquareZero I hI d
  have hcoords (i : ι) : g' (algebraMap (MvPolynomial ι R) S (MvPolynomial.X i)) =
      algebraMap (MvPolynomial ι R) B (MvPolynomial.X i) := by
    change ((b.constr S correction) (D R S (algebraMap _ _ (MvPolynomial.X i))) : B) +
      g (algebraMap _ _ (MvPolynomial.X i)) = _
    rw [← hb, b.constr_basis]
    exact sub_add_cancel _ _
  have hcomm : g'.comp (IsScalarTower.toAlgHom R (MvPolynomial ι R) S) =
      IsScalarTower.toAlgHom R (MvPolynomial ι R) B := by
    apply MvPolynomial.algHom_ext
    exact hcoords
  let lift : S →ₐ[MvPolynomial ι R] B :=
    { g'.toRingHom with commutes' := fun p => AlgHom.congr_fun hcomm p }
  refine ⟨lift, ?_⟩
  ext s
  change Ideal.Quotient.mk I (g' s) = f s
  rw [liftOfDerivationToSquareZero_mk_apply]
  exact AlgHom.congr_fun hg s

theorem formallyEtale_polynomial_of_basis [Algebra.FormallySmooth R S]
    (b : Module.Basis ι S Ω[S⁄R])
    (hb : ∀ i, b i = D R S (algebraMap (MvPolynomial ι R) S (MvPolynomial.X i))) :
    Algebra.FormallyEtale (MvPolynomial ι R) S := by
  let := formallySmooth_polynomial_of_basis b hb
  let := formallyUnramified_polynomial_of_basis b hb
  constructor <;> infer_instance

end CoordinateBasis

variable {R S ι : Type*} [CommRing R] [CommRing S] [Algebra R S]

theorem presentation_coordinate_formallyEtale {σ : Type*} [Finite σ] [Finite ι]
    (P : Algebra.SubmersivePresentation R S ι σ) :
    (MvPolynomial.aeval (R := R) (fun i : ((Set.range P.map)ᶜ : Set ι) => P.val i)).toRingHom.FormallyEtale := by
  let φ := MvPolynomial.aeval (R := R) (fun i : ((Set.range P.map)ᶜ : Set ι) => P.val i)
  let : Algebra (MvPolynomial ((Set.range P.map)ᶜ : Set ι) R) S := φ.toRingHom.toAlgebra
  let : IsScalarTower R (MvPolynomial ((Set.range P.map)ᶜ : Set ι) R) S :=
    IsScalarTower.of_algebraMap_eq' φ.comp_algebraMap.symm
  let := P.isStandardSmooth
  change Algebra.FormallyEtale (MvPolynomial ((Set.range P.map)ᶜ : Set ι) R) S
  apply formallyEtale_polynomial_of_basis P.basisKaehler
  intro i
  rw [P.basisKaehler_apply]
  change D R S (P.val i) = D R S (φ (MvPolynomial.X i))
  simp only [φ, MvPolynomial.aeval_X]

end

noncomputable section
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

theorem presentation_coordinate_etale {ι σ : Type*} [Finite σ] [Finite ι]
    (P : Algebra.SubmersivePresentation R S ι σ) :
    (MvPolynomial.aeval (R := R)
      (fun i : ((Set.range P.map)ᶜ : Set ι) => P.val i)).toRingHom.Etale := by
  let φ := MvPolynomial.aeval (R := R)
    (fun i : ((Set.range P.map)ᶜ : Set ι) => P.val i)
  have hφ := presentation_coordinate_formallyEtale P
  let : Algebra (MvPolynomial ((Set.range P.map)ᶜ : Set ι) R) S := φ.toRingHom.toAlgebra
  let : IsScalarTower R (MvPolynomial ((Set.range P.map)ᶜ : Set ι) R) S :=
    IsScalarTower.of_algebraMap_eq' φ.comp_algebraMap.symm
  let : Algebra.FinitePresentation R S := P.finitePresentation_of_isFinite
  let : Algebra.FinitePresentation (MvPolynomial ((Set.range P.map)ᶜ : Set ι) R) S :=
    Algebra.FinitePresentation.of_restrict_scalars_finitePresentation R _ S
  let : Algebra.FormallyEtale (MvPolynomial ((Set.range P.map)ᶜ : Set ι) R) S := hφ
  change Algebra.Etale (MvPolynomial ((Set.range P.map)ᶜ : Set ι) R) S
  constructor <;> infer_instance

theorem exists_etale_coordinates (n : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension n R S] :
    ∃ (κ : Type) (_ : Finite κ) (x : κ → S), Nat.card κ = n ∧
      (MvPolynomial.aeval (R := R) x).toRingHom.Etale := by
  classical
  obtain ⟨κ, σ, hσ, hκ, P, hP⟩ :=
    Algebra.IsStandardSmoothOfRelativeDimension.out (n := n) (R := R) (S := S)
  let : Fintype κ := Fintype.ofFinite κ
  let : Fintype σ := Fintype.ofFinite σ
  refine ⟨((Set.range P.map)ᶜ : Set κ), inferInstance, (fun i => P.val i), ?_,
    presentation_coordinate_etale P⟩
  rw [← hP]
  simp only [Algebra.Presentation.dimension, Nat.card_eq_fintype_card,
    Fintype.card_compl_set, Set.card_range_of_injective P.map_inj]

end

end MaximalSeshadri.AlgebraicJets


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Geometry_EtalePointChart
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                         
section

namespace MaximalSeshadri.AlgebraicJets
noncomputable section
open MvPolynomial
variable {K S : Type} [Field K] [CommRing S] [Algebra K S]

lemma etale_aeval_reindex {ι κ : Type} (x : ι → S) (h : (aeval (R := K) x).toRingHom.Etale)
    (e : κ ≃ ι) : (aeval (R := K) (fun i => x (e i))).toRingHom.Etale := by
  have he := RingHom.Etale.respectsIso.2 (aeval (R := K) x).toRingHom
    (renameEquiv K e).toRingEquiv h
  convert he using 1
  all_goals try with_reducible_and_instances rfl
  apply RingHom.ext
  intro p
  change aeval (fun i => x (e i)) p = aeval x (rename e p)
  exact (aeval_rename e x p).symm

lemma etale_aeval_center {ι : Type} (x : ι → S)
    (h : (aeval (R := K) x).toRingHom.Etale) (ρ : S →ₐ[K] K) :
    (aeval (R := K) (fun i => x i - algebraMap K S (ρ (x i)))).toRingHom.Etale := by
  have he := RingHom.Etale.respectsIso.2 (aeval (R := K) x).toRingHom
    (polynomialTranslate (fun i => ρ (x i))).symm.toRingEquiv h
  convert he using 1
  all_goals try with_reducible_and_instances rfl
  apply ringHom_ext
  · intro c; simp [polynomialTranslate]
  · intro i; simp [polynomialTranslate]

theorem exists_centered_etale_coordinates (n : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension n K S] (ρ : S →ₐ[K] K) :
    ∃ x : Fin n → S, (∀ i, ρ (x i) = 0) ∧
      (aeval (R := K) x).toRingHom.Etale := by
  obtain ⟨κ, hκ, x, hcard, hx⟩ := exists_etale_coordinates (R := K) (S := S) n
  let : Fintype κ := Fintype.ofFinite κ
  let e : κ ≃ Fin n := Fintype.equivFinOfCardEq (by simpa using hcard)
  let y := fun i : Fin n => x (e.symm i)
  refine ⟨fun i => y i - algebraMap K S (ρ (y i)), ?_,
    etale_aeval_center y (etale_aeval_reindex x hx e.symm) ρ⟩
  intro i
  simp

end

end MaximalSeshadri.AlgebraicJets

end


end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Blowup_BlowupIntegral
attribute [-instance] _root_.OAI.MaximalSeshadri.AffineBlowup.projection_proper _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                        
section

namespace MaximalSeshadri.ProjectiveGeometry
noncomputable section
open AlgebraicGeometry
universe u v
variable {A : Type u} {σ : Type v} [CommRing A]
  [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]

lemma genericPoint_dense [IsDomain A] [Nonempty (Proj 𝒜)] :
    closure ({genericPoint 𝒜} : Set (ProjectiveSpectrum 𝒜)) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  exact (ProjectiveSpectrum.le_iff_mem_closure 𝒜 _ _).mp
    (show (genericPoint 𝒜).asHomogeneousIdeal ≤ x.asHomogeneousIdeal from bot_le)

instance proj_irreducible [IsDomain A] [Nonempty (Proj 𝒜)] :
    IrreducibleSpace (Proj 𝒜) := by
  apply (irreducibleSpace_def _).mpr
  change IsIrreducible (Set.univ : Set (ProjectiveSpectrum 𝒜))
  rw [← genericPoint_dense 𝒜]
  exact (isIrreducible_singleton).closure

instance proj_isIntegral [IsDomain A] [Nonempty (Proj 𝒜)] : IsIntegral (Proj 𝒜) :=
  (isIntegral_iff_irreducibleSpace_and_isReduced _).mpr ⟨inferInstance, inferInstance⟩

end
end MaximalSeshadri.ProjectiveGeometry

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
variable {X B : Scheme.{0}} {I : X.IdealSheafData} {π : B ⟶ X}

lemma complement_nonempty (hI : I.support ≠ ⊤) : Nonempty (centreComplement I).toScheme := by
  by_contra h
  apply hI
  ext x
  change x ∈ I.support ↔ True
  rw [iff_true]
  by_contra hx
  exact h ⟨⟨x, hx⟩⟩

lemma IsBlowup.complementLift_range (hπ : IsBlowup I π) :
    Set.range hπ.complementLift = π ⁻¹' (centreComplement I : Set X) := by
  let := hπ.isIso_over_complement
  change Set.range ((pullback.snd (centreComplement I).ι π) ∘
    (inv (pullback.fst (centreComplement I).ι π))) = _
  rw [Set.range_comp]
  rw [(inv (pullback.fst (centreComplement I).ι π)).surjective.range_eq,
    Set.image_univ, Scheme.Pullback.range_snd]
  simp

lemma IsBlowup.nonempty_of_support_ne_top (hπ : IsBlowup I π) (hI : I.support ≠ ⊤) :
    Nonempty B :=
  (complement_nonempty hI).map hπ.complementLift

end
end MaximalSeshadri.Geometry

namespace MaximalSeshadri.ReesGrading
noncomputable section
open AlgebraicGeometry Polynomial
variable {R : Type} [CommRing R] (I : Ideal R)

instance affineBlowup_isIntegral [IsDomain R] [Nonempty (affineBlowup I)] :
    IsIntegral (affineBlowup I) := by
  let : IsDomain (reesAlgebra I) :=
    Function.Injective.isDomain (reesAlgebra I).val Subtype.val_injective
  let : Nonempty (Proj (piece I)) := ‹Nonempty (affineBlowup I)›
  exact ProjectiveGeometry.proj_isIntegral (piece I)

end
end MaximalSeshadri.ReesGrading

namespace MaximalSeshadri.AffineBlowup
noncomputable section
open AlgebraicGeometry
variable {X : Scheme.{0}} [IsAffine X] (I : X.IdealSheafData)

instance scheme_isIntegral [IsIntegral X] [Nonempty (scheme I)] : IsIntegral (scheme I) := by
  dsimp only [scheme]
  infer_instance

end
end MaximalSeshadri.AffineBlowup

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry TopologicalSpace
variable {X Y : Scheme.{0}} [IrreducibleSpace X] (I : X.IdealSheafData)

lemma support_comap_ne_top_of_open (hI : I.support ≠ ⊤) (j : Y ⟶ X)
    [IsOpenImmersion j] [Nonempty Y] : (I.comap j).support ≠ ⊤ := by
  have hc : (centreComplement I : Set X).Nonempty := by
    obtain ⟨x⟩ := complement_nonempty hI
    exact ⟨x.val, x.property⟩
  obtain ⟨_, ⟨y, rfl⟩, hy⟩ := nonempty_preirreducible_inter
    j.isOpenEmbedding.isOpen_range (centreComplement I).isOpen (Set.range_nonempty j) hc
  intro he
  have hyn : y ∈ (I.comap j).support := by rw [he]; trivial
  rw [Scheme.IdealSheafData.support_comap] at hyn
  exact hy hyn

end
end MaximalSeshadri.Geometry

namespace MaximalSeshadri.BlowupGluing
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace MaximalSeshadri.Geometry
variable {X : Scheme.{0}} [IsIntegral X] (I : X.IdealSheafData)

lemma localScheme_isIntegral (hI : I.support ≠ ⊤) (U : X.AffineZariskiSite)
    [Nonempty U.toOpens.toScheme] : IsIntegral (localScheme I U) := by
  let : IsIntegral U.toOpens.toScheme := isIntegral_of_isOpenImmersion U.toOpens.ι
  let : Nonempty (localScheme I U) := (local_isBlowup I U).nonempty_of_support_ne_top
    (support_comap_ne_top_of_open I hI U.toOpens.ι)
  infer_instance

omit [IsIntegral X] in
lemma cover_range (U : X.AffineZariskiSite) :
    Set.range ((cover I).f U) = projection I ⁻¹' (U.toOpens : Set X) := by
  have h := ((gluing I).preimage_toBase_eq_range_ι U).symm
  change Set.range ((cover I).f U) = projection I ⁻¹' Set.range U.toOpens.ι at h
  simpa only [Scheme.Opens.range_ι] using h

lemma complement_dense (hI : I.support ≠ ⊤) :
    Dense (projection I ⁻¹' (centreComplement I : Set X)) := by
  rw [dense_iff_inter_open]
  intro V hV ⟨y, hyV⟩
  obtain ⟨U, z, rfl⟩ := (cover I).exists_eq y
  let : Nonempty U.toOpens.toScheme := ⟨localProjection I U z⟩
  let : IsIntegral ((cover I).X U) := localScheme_isIntegral I hI U
  have hc : (centreComplement I : Set X).Nonempty := by
    obtain ⟨x⟩ := complement_nonempty hI
    exact ⟨x.val, x.property⟩
  have hU : (U.toOpens : Set X).Nonempty := by
    obtain ⟨x⟩ := ‹Nonempty U.toOpens.toScheme›
    exact ⟨x.val, x.property⟩
  obtain ⟨x, hxU, hxc⟩ := nonempty_preirreducible_inter
    U.toOpens.isOpen (centreComplement I).isOpen hU hc
  let b : scheme I := (isBlowup I).complementLift ⟨x, hxc⟩
  have hpb : projection I b = x :=
    congrArg (fun f : (centreComplement I).toScheme ⟶ X => f ⟨x, hxc⟩)
      (isBlowup I).complementLift_comp
  have hbr : b ∈ Set.range ((cover I).f U) := by
    rw [cover_range I U]
    change projection I b ∈ U.toOpens
    rwa [hpb]
  obtain ⟨w, hw⟩ := hbr
  have hwc : (cover I).f U w ∈ projection I ⁻¹' (centreComplement I : Set X) := by
    change projection I ((cover I).f U w) ∈ centreComplement I
    rwa [hw, hpb]
  obtain ⟨q, hqV, hqc⟩ := nonempty_preirreducible_inter
    (hV.preimage ((cover I).f U).continuous)
    (((centreComplement I).isOpen.preimage (projection I).continuous).preimage
      ((cover I).f U).continuous) ⟨z, hyV⟩ ⟨w, hwc⟩
  exact ⟨(cover I).f U q, hqV, hqc⟩

lemma scheme_isIntegral (hI : I.support ≠ ⊤) : IsIntegral (scheme I) := by
  let : Nonempty (centreComplement I).toScheme := complement_nonempty hI
  let : IsIntegral (centreComplement I).toScheme :=
    isIntegral_of_isOpenImmersion (centreComplement I).ι
  have hi : IsIrreducible (Set.range (isBlowup I).complementLift) := by
    simpa only [Set.image_univ] using
      (IrreducibleSpace.isIrreducible_univ (X := (centreComplement I).toScheme)).image
        (isBlowup I).complementLift (isBlowup I).complementLift.continuous.continuousOn
  have hd : Dense (Set.range (isBlowup I).complementLift) := by
    rw [Geometry.IsBlowup.complementLift_range]
    exact complement_dense I hI
  let : IrreducibleSpace (scheme I) := (irreducibleSpace_def _).mpr (by
    change IsIrreducible (Set.univ : Set (scheme I))
    rw [← hd.closure_eq]
    exact hi.closure)
  exact isIntegral_of_irreducibleSpace_of_isReduced _

end
end MaximalSeshadri.BlowupGluing

end


end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Blowup_BlowupProper
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.BlowupGluing.scheme_isReduced _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                      
section

namespace MaximalSeshadri
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

instance BlowupGluing.projection_proper {X : Scheme.{0}} [IsLocallyNoetherian X]
    (I : X.IdealSheafData) : IsProper (BlowupGluing.projection I) := by
  apply IsZariskiLocalAtTarget.of_openCover (P := @IsProper) (BlowupGluing.baseCover I)
  intro U
  let he := (BlowupGluing.local_pullback I U).flip.isoPullback
  have hh : he.hom ≫ pullback.snd (BlowupGluing.projection I) U.toOpens.ι =
      BlowupGluing.localProjection I U := by
    exact (BlowupGluing.local_pullback I U).flip.isoPullback_hom_snd
  have h : IsProper (BlowupGluing.localProjection I U) := by infer_instance
  rw [← hh] at h
  exact (MorphismProperty.cancel_left_of_respectsIso (@IsProper) he.hom _).mp h

end
end MaximalSeshadri

end


end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Blowup_FiniteCenters
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.instIsOpenImmersionComplementLift _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MaximalSeshadri.FinitePointBlowup
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open MaximalSeshadri.Geometry
variable {K : Type} [Field K] {X B : Scheme.{0}}

lemma comap_mul_open {Y : Scheme.{0}} (I J : X.IdealSheafData)
    (f : Y ⟶ X) [IsOpenImmersion f] :
    (I * J).comap f = I.comap f * J.comap f := by
  ext U : 2
  let V : X.affineOpens := ⟨f ''ᵁ U.1, U.2.image_of_isOpenImmersion f⟩
  have e : U.1 ≤ f ⁻¹ᵁ V.1 := fun x hx => ⟨x, hx, rfl⟩
  rw [IdealPullback.comap_ideal _ f U V e]
  change ((I.ideal V) * (J.ideal V)).map _ = _
  rw [Ideal.map_mul]
  simp only [Scheme.IdealSheafData.ideal_mul, Pi.mul_apply,
    IdealPullback.comap_ideal _ f U V e]

lemma comap_prod_open {Y : Scheme.{0}} {α : Type} (s : Finset α)
    (I : α → X.IdealSheafData) (f : Y ⟶ X) [IsOpenImmersion f] :
    (∏ i ∈ s, I i).comap f = ∏ i ∈ s, (I i).comap f := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp only [Finset.prod_insert ha, comap_mul_open, ih]

lemma comap_eq_top_of_disjoint (I : X.IdealSheafData) (U : X.Opens)
    (h : Disjoint (I.support : Set X) U) : I.comap U.ι = ⊤ := by
  apply (Scheme.IdealSheafData.support_eq_bot_iff _).mp
  rw [Scheme.IdealSheafData.support_comap]
  ext x
  change x.val ∈ I.support ↔ False
  exact iff_false_intro (fun hx => Set.disjoint_left.mp h hx x.property)

variable {α : Type} [Fintype α]
variable (p : α → (Spec (.of K) ⟶ X))

omit [Fintype α] in
lemma pointOpen_comap_other (i j : α) (hji : j ≠ i) :
    (p j).ker.comap (pointOpen p i).ι = ⊤ := by
  apply comap_eq_top_of_disjoint
  apply Set.disjoint_left.mpr
  intro x hx hxU
  exact hxU (show x ∈ (⨆ j : {j : α // j ≠ i}, (p j).ker.support) from
    (le_iSup (fun j : {j : α // j ≠ i} => (p j).ker.support) ⟨j, hji⟩) hx)

lemma pointOpen_comap_centre (i : α) :
    (pointCentre p).comap (pointOpen p i).ι = (p i).ker.comap (pointOpen p i).ι := by
  classical
  rw [pointCentre, comap_prod_open]
  exact Finset.prod_eq_single i (fun j _ hji => by
    simpa only [Scheme.IdealSheafData.one_eq_top] using pointOpen_comap_other p i j hji)
    (by simp)

variable (f : X ⟶ Spec (.of K)) (hp : ∀ i, p i ≫ f = 𝟙 _)

include hp

variable (hd : Function.Injective (fun i =>
  p i (⟨⊥, Ideal.isPrime_bot⟩ : Spec (.of K))))

include hd

theorem exceptional_invertible (π : B ⟶ X) (hπ : IsBlowup (pointCentre p) π) (i : α) :
    InvertiblePullbackIdeal (p i).ker π := by
  let C := pointCover p f hp hd
  apply InvertibleLocal.invertible_of_cover (p i).ker π (C.pullback₁ π)
  change ∀ a : Option α, InvertiblePullbackIdeal (p i).ker
    (pullback.fst π (C.f a) ≫ π)
  intro a
  have : IsOpenImmersion (C.f a) := C.map_prop a
  have hInv : InvertiblePullbackIdeal (pointCentre p) (pullback.fst π (C.f a) ≫ π) :=
    InvertibleLocal.invertible_restrict_general _ π hπ.1 (pullback.fst π (C.f a))
  cases a with
  | none =>
    change InvertiblePullbackIdeal (p i).ker (pullback.fst π (outsideOpen p).ι ≫ π)
    have he : (p i).ker.comap (outsideOpen p).ι = ⊤ := by
      apply comap_eq_top_of_disjoint
      apply Set.disjoint_left.mpr
      intro x hx hxU
      exact hxU ((mem_centre_support p x).mpr ⟨i, hx⟩)
    apply (InvertibleLocal.invertible_congr (I' := ⊤)
      (f' := pullback.fst π (outsideOpen p).ι ≫ π) ?_).mpr
      (invertible_top _)
    rw [pullback.condition, Scheme.IdealSheafData.comap_comp, he]
    simp
  | some j =>
    change InvertiblePullbackIdeal (p i).ker (pullback.fst π (pointOpen p j).ι ≫ π)
    by_cases hij : i = j
    · subst j
      apply (InvertibleLocal.invertible_congr (I' := pointCentre p)
        (f' := pullback.fst π (pointOpen p i).ι ≫ π) ?_).mpr hInv
      rw [pullback.condition, Scheme.IdealSheafData.comap_comp,
        Scheme.IdealSheafData.comap_comp, pointOpen_comap_centre]
    · apply (InvertibleLocal.invertible_congr (I' := ⊤)
        (f' := pullback.fst π (pointOpen p j).ι ≫ π) ?_).mpr
        (invertible_top _)
      rw [pullback.condition, Scheme.IdealSheafData.comap_comp,
        pointOpen_comap_other p j i hij]
      simp

end
end MaximalSeshadri.FinitePointBlowup

end



end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Projective_SectionMaps
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.unit_isIso _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TensorPure.tensorSection_isIso _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
noncomputable section
open CategoryTheory
open CategoryTheory.Category CategoryTheory.Functor
universe v u v₁ v₂ u₁ u₂
namespace MaximalSeshadri.Projective

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial TopologicalSpace
variable {K σ : Type u} [CommRing K]
attribute [local instance] MvPolynomial.gradedAlgebra

lemma coordinatesMap_preimage (X : Scheme.{u}) (k : K →+* Γ(X, ⊤))
    (a : σ → Γ(X, ⊤)) (i : σ) (hi : a i = 1) (j : σ) :
    coordinatesMap X k a i hi ⁻¹ᵁ
      Proj.basicOpen (homogeneousSubmodule σ K) (MvPolynomial.X j) = X.basicOpen (a j) := by
  rw [coordinatesMap, Scheme.Hom.comp_preimage,
    fromUnitCoordinate_preimage _ (coordinates_X_mem (K := K) i) _
      (by simpa only [eval₂Hom_X'] using hi) (by decide) (coordinates_X_mem (K := K) j),
    eval₂Hom_X', Scheme.toSpecΓ_preimage_basicOpen]

end

end MaximalSeshadri.Projective

namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry
open MaximalSeshadri.Frames
variable {K σ : Type u} [CommRing K] {X : Scheme.{u}}
attribute [local instance] MvPolynomial.gradedAlgebra

theorem sectionsMorphism_preimage {M : X.Modules} (k : K →+* Γ(X, ⊤))
    (s : σ → (O X ⟶ M)) (hcover : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤) (j : σ) :
    sectionsMorphism k s hcover ⁻¹ᵁ
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule σ K) (MvPolynomial.X j) =
      SectionOpens.isoOpen (s j) := by
  ext x
  have hx : x ∈ ⨆ i, SectionOpens.isoOpen (s i) := by rw [hcover]; trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
  let U := SectionOpens.isoOpen (s i)
  have H : U.ι ⁻¹ᵁ (sectionsMorphism k s hcover ⁻¹ᵁ
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule σ K) (MvPolynomial.X j)) =
      U.ι ⁻¹ᵁ SectionOpens.isoOpen (s j) := by
    rw [← Scheme.Hom.comp_preimage, sectionsMorphism_local,
      coordinatesMap_preimage, preimage_isoOpen (s j) U.ι (sectionFrame (s i))]
  exact Set.ext_iff.mp (congrArg SetLike.coe H) (⟨x, hi⟩ : U.toScheme)

end
end MaximalSeshadri.Projective

end
end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Projective_ClosedEmbedding
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.unit_isIso _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TensorPure.tensorSection_isIso _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
noncomputable section
open CategoryTheory
open CategoryTheory.Category CategoryTheory.Functor
universe v u v₁ v₂ u₁ u₂
namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped AlgebraicGeometry
open MvPolynomial HomogeneousLocalization
variable {K σ R : Type u} [CommRing K] [CommRing R]
attribute [local instance] MvPolynomial.gradedAlgebra

lemma normalized_evalAway_surjective (k : K →+* R) (a : σ → R)
    (i : σ) (hi : a i = 1) (h : Function.Surjective (eval₂Hom k a)) :
    Function.Surjective (evalAway (𝒜 := homogeneousSubmodule σ K) (eval₂Hom k a)
      (X i) (by simpa only [eval₂Hom_X', hi] using (isUnit_one : IsUnit (1 : R)))) := by
  let F := evalAway (𝒜 := homogeneousSubmodule σ K) (eval₂Hom k a)
    (X i) (by simpa only [eval₂Hom_X', hi] using (isUnit_one : IsUnit (1 : R)))
  have hC (r : K) : C r ∈ homogeneousSubmodule σ K (0 • 1) := by simp
  have hX (j : σ) : X j ∈ homogeneousSubmodule σ K (1 • 1) := by
    simpa using isHomogeneous_X K j
  let c : K →+* Away (homogeneousSubmodule σ K) (X i) :=
    (HomogeneousLocalization.fromZeroRingHom _ _).comp
      { toFun := fun r => ⟨C r, isHomogeneous_C _ _⟩
        map_one' := Subtype.ext C_1
        map_mul' := fun _ _ => Subtype.ext C_mul
        map_zero' := Subtype.ext C_0
        map_add' := fun _ _ => Subtype.ext C_add }
  let b (j : σ) := Away.mk _ (isHomogeneous_X K i) 1 (X j) (hX j)
  have hc (r : K) : F (c r) = k r := by
    change F (Away.mk _ (isHomogeneous_X K i) 0 (C r) (hC r)) = k r
    have H := evalAway_mk_clear (eval₂Hom k a) (isHomogeneous_X K i)
      (show IsUnit ((eval₂Hom k a) (X i)) by simpa only [eval₂Hom_X', hi] using
        (isUnit_one : IsUnit (1 : R))) 0 (C r) (hC r)
    simpa only [F, eval₂Hom_C, eval₂Hom_X', pow_zero, mul_one] using H
  have hb (j : σ) : F (b j) = a j := by
    have H := evalAway_mk_clear (eval₂Hom k a) (isHomogeneous_X K i)
      (show IsUnit ((eval₂Hom k a) (X i)) by simpa only [eval₂Hom_X', hi] using
        (isUnit_one : IsUnit (1 : R))) 1 (X j) (hX j)
    simpa only [F, b, eval₂Hom_X', hi, one_pow, mul_one] using H
  have H : F.comp (eval₂Hom c b) = eval₂Hom k a := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simpa only [RingHom.comp_apply, eval₂Hom_C] using hc r
    · intro j
      simpa only [RingHom.comp_apply, eval₂Hom_X'] using hb j
  intro r
  obtain ⟨p, hp⟩ := h r
  exact ⟨eval₂Hom c b p, (RingHom.congr_fun H p).trans hp⟩

lemma normalized_coordinates_closed {X : Scheme.{u}} [IsAffine X]
    (k : K →+* Γ(X, ⊤)) (a : σ → Γ(X, ⊤)) (i : σ) (hi : a i = 1)
    (h : Function.Surjective (eval₂Hom k a)) :
    IsClosedImmersion (X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom
      (evalAway (𝒜 := homogeneousSubmodule σ K) (eval₂Hom k a) (MvPolynomial.X i)
        (by simpa only [eval₂Hom_X', hi] using (isUnit_one : IsUnit (1 : Γ(X, ⊤))))))) := by
  have := IsClosedImmersion.spec_of_surjective
    (CommRingCat.ofHom (evalAway (𝒜 := homogeneousSubmodule σ K) (eval₂Hom k a)
      (MvPolynomial.X i) (by simpa only [eval₂Hom_X', hi] using
        (isUnit_one : IsUnit (1 : Γ(X, ⊤))))))
    (normalized_evalAway_surjective k a i hi h)
  infer_instance

end
end MaximalSeshadri.Projective
namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped AlgebraicGeometry
open MaximalSeshadri.Frames MvPolynomial
variable {K σ : Type u} [CommRing K] {X : Scheme.{u}}
attribute [local instance] MvPolynomial.gradedAlgebra

theorem sectionsMorphism_isClosedImmersion {M : X.Modules} (k : K →+* Γ(X, ⊤))
    (s : σ → (O X ⟶ M)) (hcover : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    (haff : ∀ i, IsAffine (SectionOpens.isoOpen (s i)).toScheme)
    (hgen : ∀ i, Function.Surjective
      (eval₂Hom (((SectionOpens.isoOpen (s i)).ι.appTop.hom).comp k)
        (fun j => coefficient (sectionFrame (s i))
          (restrictSection (SectionOpens.isoOpen (s i)).ι (s j))))) :
    IsClosedImmersion (sectionsMorphism k s hcover) := by
  let V := projectiveCoordinateCover (K := K) (σ := σ)
  apply IsZariskiLocalAtTarget.of_openCover (P := @IsClosedImmersion) V.openCover
  intro i
  change σ at i
  let U := SectionOpens.isoOpen (s i)
  let : IsAffine U.toScheme := haff i
  let k' := U.ι.appTop.hom.comp k
  let a : σ → Γ(U.toScheme, ⊤) := fun j => coefficient (sectionFrame (s i)) (restrictSection U.ι (s j))
  have hi : a i = 1 := sectionFrame_normalized (s i)
  let g := U.toScheme.toSpecΓ ≫ Spec.map (CommRingCat.ofHom
    (evalAway (𝒜 := homogeneousSubmodule σ K) (eval₂Hom k' a) (MvPolynomial.X i)
      (by simpa only [eval₂Hom_X', hi] using (isUnit_one : IsUnit (1 : Γ(U.toScheme, ⊤))))))
  have hg : IsClosedImmersion g := normalized_coordinates_closed k' a i hi (hgen i)
  let chart := Proj.awayι (homogeneousSubmodule σ K) (MvPolynomial.X i)
    (isHomogeneous_X K i) (show 0 < 1 by decide)
  have : IsOpenImmersion chart := V.map_prop i
  have H : IsPullback g U.ι chart (sectionsMorphism k s hcover) := by
    apply IsOpenImmersion.isPullback
    · exact (sectionsMorphism_local k s hcover i).trans (Category.assoc _ _ _).symm
    · have hrange : chart.opensRange =
          Proj.basicOpen (homogeneousSubmodule σ K) (MvPolynomial.X i) :=
        Proj.opensRange_awayι _ _ (isHomogeneous_X K i) (show 0 < 1 by decide)
      rw [hrange, sectionsMorphism_preimage, Scheme.Opens.opensRange_ι]
  change IsClosedImmersion (pullback.snd (sectionsMorphism k s hcover) chart)
  rw [← H.flip.isoPullback_inv_snd]
  infer_instance

end
end MaximalSeshadri.Projective

namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory HomogeneousLocalization MvPolynomial
open scoped AlgebraicGeometry
variable {K σ : Type u} [CommRing K]
attribute [local instance] MvPolynomial.gradedAlgebra

lemma evalAway_constants {R : Type u} [CommRing R] (k : K →+* R) (a : σ → R)
    (i : σ) (hi : a i = 1) :
    (evalAway (𝒜 := homogeneousSubmodule σ K) (eval₂Hom k a) (X i)
      (by simpa only [eval₂Hom_X', hi] using (isUnit_one : IsUnit (1 : R)))).comp
      ((fromZeroRingHom (homogeneousSubmodule σ K) (.powers (X i))).comp
        projectiveConstants) = k := by
  apply RingHom.ext
  intro c
  change IsLocalization.Away.lift (X i)
    (by simpa only [eval₂Hom_X', hi] using (isUnit_one : IsUnit (1 : R)))
    (HomogeneousLocalization.fromZeroRingHom (homogeneousSubmodule σ K)
      (.powers (X i)) (projectiveConstants c)).val = k c
  change IsLocalization.Away.lift (X i)
    (by simpa only [eval₂Hom_X', hi] using (isUnit_one : IsUnit (1 : R)))
    (algebraMap (MvPolynomial σ K) (Localization.Away (X i)) (C c)) = k c
  rw [IsLocalization.Away.lift_eq, eval₂Hom_C]

@[reassoc]
theorem coordinatesMap_over {X : Scheme.{u}} (k : K →+* Γ(X, ⊤))
    (a : σ → Γ(X, ⊤)) (i : σ) (hi : a i = 1) :
    coordinatesMap X k a i hi ≫ projectiveBase =
      X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom k) := by
  simp only [coordinatesMap, fromUnitCoordinate, projectiveBase, Category.assoc,
    Proj.awayι_toSpecZero_assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  exact congrArg CommRingCat.ofHom (evalAway_constants k a i hi)

@[reassoc]
theorem sectionsMorphism_over {X : Scheme.{u}} {M : X.Modules}
    (k : K →+* Γ(X, ⊤)) (s : σ → (MaximalSeshadri.Frames.O X ⟶ M))
    (hcover : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤) :
    sectionsMorphism k s hcover ≫ projectiveBase =
      X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom k) := by
  apply (X.openCoverOfIsOpenCover (fun i => SectionOpens.isoOpen (s i)) hcover).hom_ext
  intro i
  change σ at i
  change (SectionOpens.isoOpen (s i)).ι ≫ _ = _
  rw [← Category.assoc, sectionsMorphism_local, coordinatesMap_over]
  change _ = (SectionOpens.isoOpen (s i)).ι ≫ X.toSpecΓ ≫ _
  rw [← Category.assoc, Scheme.toSpecΓ_naturality, Category.assoc, ← Spec.map_comp]
  rfl

end
end MaximalSeshadri.Projective

namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial
open scoped AlgebraicGeometry
open MaximalSeshadri.Frames
variable {K σ : Type u} [CommRing K] {X : Scheme.{u}}
attribute [local instance] MvPolynomial.gradedAlgebra

instance sectionsMorphism_proper {M : X.Modules} (k : K →+* Γ(X, ⊤))
    (s : σ → (O X ⟶ M)) (hcover : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    [IsProper (X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom k))] :
    IsProper (sectionsMorphism k s hcover) := by
  have : IsProper (sectionsMorphism k s hcover ≫ projectiveBase) := by
    rw [sectionsMorphism_over]
    infer_instance
  exact IsProper.of_comp _ projectiveBase

end
end MaximalSeshadri.Projective


end
end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Geometry_SmoothAffineRefinement
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.Projective.boolChartUnique _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                           

namespace MaximalSeshadri.ProjectiveBertini
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
variable {K : Type u} [Field K] {X : Scheme.{u}}

theorem exists_standard_smooth_affine_inside
    (g : X ⟶ Spec (CommRingCat.of K)) (n : ℕ) [SmoothOfRelativeDimension n g]
    (W : X.Opens) (x : X) (hx : x ∈ W) :
    ∃ U : X.affineOpens, x ∈ U.1 ∧ U.1 ≤ W ∧
      RingHom.IsStandardSmoothOfRelativeDimension n (openScalars g U.1) := by
  obtain ⟨B, hB, V, hV, hxV, e, hg⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension
      (n := n) (f := g) x
  have hBtop : B = ⊤ := by
    apply top_unique
    intro y _
    have hy : y = g x := Subsingleton.elim _ _
    rw [hy]
    exact e hxV
  subst B
  let e₀ : K ≃+* Γ(Spec (CommRingCat.of K), ⊤) :=
    RingEquiv.ofBijective (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of K)).inv)
  have hstd : RingHom.IsStandardSmoothOfRelativeDimension n (openScalars g V) := by
    convert hg.comp (RingHom.IsStandardSmoothOfRelativeDimension.equiv e₀) using 1
    all_goals try with_reducible_and_instances rfl
    rfl
  obtain ⟨f, hfW, hxf⟩ := hV.exists_basicOpen_le ⟨x, hx⟩ hxV
  refine ⟨⟨X.basicOpen f, hV.basicOpen f⟩, hxf, hfW, ?_⟩
  let : IsLocalization.Away f Γ(X, X.basicOpen f) := hV.isLocalization_basicOpen f
  have hs := (RingHom.isStandardSmoothOfRelativeDimension_stableUnderCompositionWithLocalizationAway n).right
    (Γ(X, X.basicOpen f)) f (openScalars g V) hstd
  convert hs using 1
  all_goals try with_reducible_and_instances rfl
  exact (openScalars_restrict g (X.basicOpen_le f)).symm

end
end MaximalSeshadri.ProjectiveBertini


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Projective_FramedMaps
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.unit_isIso _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TensorPure.tensorSection_isIso _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
noncomputable section
open CategoryTheory
open CategoryTheory.Category CategoryTheory.Functor
universe v u v₁ v₂ u₁ u₂
namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial
open scoped AlgebraicGeometry
open MaximalSeshadri.Frames
variable {K σ ι : Type u} [CommRing K] {X : Scheme.{u}} {M : X.Modules}
attribute [local instance] MvPolynomial.gradedAlgebra

variable (k : K →+* Γ(X, ⊤)) (s : σ → (O X ⟶ M))
  (U : ι → X.Opens) (hc : (⨆ i, U i) = ⊤)
  (e : ∀ i, M.restrict (U i).ι ≅ O (U i).toScheme) (a : ι → σ)
  (hnorm : ∀ i, coefficient (e i) (restrictSection (U i).ι (s (a i))) = 1)

@[reassoc]
theorem framedSectionsMorphism_over :
    framedSectionsMorphism k s U hc e a hnorm ≫ projectiveBase =
      X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom k) := by
  apply (X.openCoverOfIsOpenCover U hc).hom_ext
  intro i
  change ι at i
  change (U i).ι ≫ _ = (U i).ι ≫ _
  rw [← Category.assoc, framedSectionsMorphism_local, coordinatesMap_over,
    ← Category.assoc, Scheme.toSpecΓ_naturality, Category.assoc, ← Spec.map_comp]
  rfl

instance framedSectionsMorphism_proper
    [IsProper (X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom k))] :
    IsProper (framedSectionsMorphism k s U hc e a hnorm) := by
  have : IsProper (framedSectionsMorphism k s U hc e a hnorm ≫ projectiveBase) := by
    rw [framedSectionsMorphism_over]
    infer_instance
  exact IsProper.of_comp _ projectiveBase

end
end MaximalSeshadri.Projective

namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial
open scoped AlgebraicGeometry
open MaximalSeshadri.Frames
variable {K σ ι κ : Type u} [CommRing K] {X : Scheme.{u}} {M : X.Modules}
attribute [local instance] MvPolynomial.gradedAlgebra

theorem framedSectionsMorphism_eq (k : K →+* Γ(X, ⊤)) (s : σ → (O X ⟶ M))
    (U : ι → X.Opens) (hc : (⨆ i, U i) = ⊤)
    (e : ∀ i, M.restrict (U i).ι ≅ O (U i).toScheme) (a : ι → σ)
    (hnorm : ∀ i, coefficient (e i) (restrictSection (U i).ι (s (a i))) = 1)
    (V : κ → X.Opens) (hd : (⨆ i, V i) = ⊤)
    (d : ∀ i, M.restrict (V i).ι ≅ O (V i).toScheme) (b : κ → σ)
    (hnorm' : ∀ i, coefficient (d i) (restrictSection (V i).ι (s (b i))) = 1) :
    framedSectionsMorphism k s U hc e a hnorm =
      framedSectionsMorphism k s V hd d b hnorm' := by
  let W : ι ⊕ κ → X.Opens := Sum.elim U V
  have hw : (⨆ i, W i) = ⊤ := by
    apply top_unique
    rw [← hc]
    apply iSup_le
    intro i
    exact le_iSup W (Sum.inl i)
  let E : ∀ i, M.restrict (W i).ι ≅ O (W i).toScheme :=
    fun i => match i with | Sum.inl j => e j | Sum.inr j => d j
  let A : ι ⊕ κ → σ := Sum.elim a b
  have hN : ∀ i, coefficient (E i) (restrictSection (W i).ι (s (A i))) = 1 := by
    rintro (i | i)
    · exact hnorm i
    · exact hnorm' i
  let F := framedSectionsMorphism k s W hw E A hN
  have hleft : framedSectionsMorphism k s U hc e a hnorm = F := by
    apply (X.openCoverOfIsOpenCover U hc).hom_ext
    intro i
    change ι at i
    change (U i).ι ≫ _ = (U i).ι ≫ F
    rw [framedSectionsMorphism_local]
    exact (framedSectionsMorphism_local k s W hw E A hN (Sum.inl i)).symm
  have hright : framedSectionsMorphism k s V hd d b hnorm' = F := by
    apply (X.openCoverOfIsOpenCover V hd).hom_ext
    intro i
    change κ at i
    change (V i).ι ≫ _ = (V i).ι ≫ F
    rw [framedSectionsMorphism_local]
    exact (framedSectionsMorphism_local k s W hw E A hN (Sum.inr i)).symm
  exact hleft.trans hright.symm

lemma framedSectionsMorphism_eq_sectionsMorphism (k : K →+* Γ(X, ⊤))
    (s : σ → (O X ⟶ M)) (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    (U : ι → X.Opens) (hc : (⨆ i, U i) = ⊤)
    (e : ∀ i, M.restrict (U i).ι ≅ O (U i).toScheme) (a : ι → σ)
    (hnorm : ∀ i, coefficient (e i) (restrictSection (U i).ι (s (a i))) = 1) :
    framedSectionsMorphism k s U hc e a hnorm = sectionsMorphism k s hs :=
  framedSectionsMorphism_eq k s U hc e a hnorm
    (fun i => SectionOpens.isoOpen (s i)) hs (fun i => sectionFrame (s i)) id
    (fun i => sectionFrame_normalized (s i))

end
end MaximalSeshadri.Projective

namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial
open scoped AlgebraicGeometry
open MaximalSeshadri.Frames
variable {K σ : Type u} [CommRing K] {X : Scheme.{u}} {M N : X.Modules}
attribute [local instance] MvPolynomial.gradedAlgebra

lemma coefficient_postcomp (f : M ≅ N) (φ : X.Opens)
    (e : M.restrict φ.ι ≅ O φ.toScheme) (s : O X ⟶ M) :
    coefficient ((Scheme.Modules.restrictFunctor φ.ι).mapIso f.symm ≪≫ e)
      (restrictSection φ.ι (s ≫ f.hom)) = coefficient e (restrictSection φ.ι s) := by
  change endValue
    (((Scheme.Modules.restrictUnitIso φ.ι).inv ≫
      (Scheme.Modules.restrictFunctor φ.ι).map (s ≫ f.hom)) ≫
      (Scheme.Modules.restrictFunctor φ.ι).map f.inv ≫ e.hom) = _
  erw [Functor.map_comp]
  erw [Category.assoc, Category.assoc,
    ((Scheme.Modules.restrictFunctor φ.ι).mapIso f).hom_inv_id_assoc]
  exact congrArg endValue (Category.assoc _ _ _).symm

theorem sectionsMorphism_transport (k : K →+* Γ(X, ⊤))
    (s : σ → (O X ⟶ M)) (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    (f : M ≅ N) (ht : (⨆ i, SectionOpens.isoOpen (s i ≫ f.hom)) = ⊤) :
    sectionsMorphism k (fun i => s i ≫ f.hom) ht = sectionsMorphism k s hs := by
  let U (i : σ) := SectionOpens.isoOpen (s i)
  let e (i : σ) := (Scheme.Modules.restrictFunctor (U i).ι).mapIso f.symm ≪≫ sectionFrame (s i)
  have he (i j : σ) : coefficient (e i) (restrictSection (U i).ι (s j ≫ f.hom)) =
      coefficient (sectionFrame (s i)) (restrictSection (U i).ι (s j)) :=
    coefficient_postcomp f (U i) (sectionFrame (s i)) (s j)
  have hn (i : σ) : coefficient (e i) (restrictSection (U i).ι (s i ≫ f.hom)) = 1 := by
    rw [he]
    exact sectionFrame_normalized (s i)
  rw [← framedSectionsMorphism_eq_sectionsMorphism k (fun i => s i ≫ f.hom) ht U hs e id hn]
  apply (X.openCoverOfIsOpenCover U hs).hom_ext
  intro i
  change σ at i
  change (U i).ι ≫ _ = (U i).ι ≫ _
  rw [framedSectionsMorphism_local, sectionsMorphism_local]
  congr 1
  funext j
  exact he i j

end
end MaximalSeshadri.Projective


end
end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Projective_AmpleEmbedding
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.LineBundle.finitePresentation _root_.OAI.MaximalSeshadri.Geometry.LineBundle.localGenerators_locallyFree _root_.OAI.MaximalSeshadri.Geometry.LineBundle.locallyFree _root_.OAI.MaximalSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.line_isIso _root_.OAI.MaximalSeshadri.PullbackTensor.unit_isIso _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TensorPure.tensorSection_isIso _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
noncomputable section
open CategoryTheory
open CategoryTheory.Category CategoryTheory.Functor
universe v u v₁ v₂ u₁ u₂
namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry
open MaximalSeshadri.Frames MaximalSeshadri.Projective
variable {X : Scheme} {K : Type} [CommRing K]

theorem LineBundle.ample_projective_sections [IsIntegral X] [CompactSpace X]
    (p : X ⟶ Spec (CommRingCat.of K)) [IsProper p]
    (L : LineBundle X) (hL : LineBundle.IsAmple X L) :
    ∃ n : ℕ, 0 < n ∧ ∃ σ : Type, ∃ _ : Fintype σ,
      ∃ t : σ → GlobalSections X (modulePow X L.sheaf n),
      ∃ ht : (⨆ i, SectionOpens.isoOpen (t i)) = ⊤,
        IsClosedImmersion (sectionsMorphism
          (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom) t ht) := by
  obtain ⟨d, hd, l, s, hc, ha, hn⟩ := L.ample_common_degree_cover hL
  obtain ⟨n, hn', σ, hσ, t, ht, he⟩ := (L.pow d).power_section_embedding_s01 p s hc ha hn
  let e := linePowerMul L d n
  let T : σ → GlobalSections X (modulePow X L.sheaf (d*n)) := fun i => t i ≫ e.hom
  have hT : (⨆ i, SectionOpens.isoOpen (T i)) = ⊤ := by
    calc
      (⨆ i, SectionOpens.isoOpen (T i)) = ⨆ i, SectionOpens.isoOpen (t i) :=
        iSup_congr fun i => SectionOpens.isoOpen_postcomp (t i) e
      _ = ⊤ := ht
  refine ⟨d*n, Nat.mul_pos hd hn', σ, hσ, T, hT, ?_⟩
  dsimp only [T]
  erw [sectionsMorphism_transport _ t ht e hT]
  exact he

end
end MaximalSeshadri.Geometry

namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace MvPolynomial
open HomogeneousLocalization MaximalSeshadri.Frames
open scoped AlgebraicGeometry
variable {K R σ : Type u} [CommRing K] [CommRing R]
attribute [local instance] MvPolynomial.gradedAlgebra

lemma normalized_eval₂_of_evalAway (k : K →+* R) (a : σ → R) (i : σ) (hi : a i = 1)
    (h : Function.Surjective (evalAway (𝒜 := homogeneousSubmodule σ K)
      (eval₂Hom k a) (MvPolynomial.X i)
        (by simpa only [eval₂Hom_X', hi] using (isUnit_one : IsUnit (1 : R))))) :
    Function.Surjective (eval₂Hom k a) := by
  intro r
  obtain ⟨x, hx⟩ := h r
  obtain ⟨n, q, hq, rfl⟩ := Away.mk_surjective (homogeneousSubmodule σ K)
    (isHomogeneous_X K i) x
  refine ⟨q, ?_⟩
  have he := evalAway_mk_clear (eval₂Hom k a) (isHomogeneous_X K i)
    (by simpa only [eval₂Hom_X', hi] using (isUnit_one : IsUnit (1 : R))) n q hq
  simpa only [hx, eval₂Hom_X', hi, one_pow, mul_one] using he.symm

lemma affine_evaluation_surjective {Y : Scheme.{u}} (f : R →+* Γ(Y, ⊤))
    [IsClosedImmersion (Y.toSpecΓ ≫ Spec.map (CommRingCat.ofHom f))] :
    Function.Surjective f := by
  let g := Y.toSpecΓ ≫ Spec.map (CommRingCat.ofHom f)
  have hg := (IsClosedImmersion.isAffine_surjective_of_isAffine g).2
  have hEq : (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ g.appTop = CommRingCat.ofHom f := by
    simp only [g, Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop,
      ← Scheme.ΓSpecIso_inv_naturality_assoc, Iso.inv_hom_id, Category.comp_id]
  have hh := hg.comp (ConcreteCategory.bijective_of_isIso
    (Scheme.ΓSpecIso (CommRingCat.of R)).inv).surjective
  change Function.Surjective ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ g.appTop).hom at hh
  simpa only [hEq, CommRingCat.hom_ofHom] using hh

theorem sectionsMorphism_chart_generators {X : Scheme.{u}} {M : X.Modules}
    (k : K →+* Γ(X, ⊤)) (s : σ → (O X ⟶ M))
    (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    [IsClosedImmersion (sectionsMorphism k s hs)] (i : σ) :
    IsAffine (SectionOpens.isoOpen (s i)).toScheme ∧ Function.Surjective
      (eval₂Hom ((SectionOpens.isoOpen (s i)).ι.appTop.hom.comp k)
        (fun j => coefficient (sectionFrame (s i))
          (restrictSection (SectionOpens.isoOpen (s i)).ι (s j)))) := by
  let V := projectiveCoordinateCover (K := K) (σ := σ)
  let U := SectionOpens.isoOpen (s i)
  let k' := U.ι.appTop.hom.comp k
  let a : σ → Γ(U.toScheme, ⊤) := fun j => coefficient (sectionFrame (s i)) (restrictSection U.ι (s j))
  have hi : a i = 1 := sectionFrame_normalized (s i)
  let f := evalAway (𝒜 := homogeneousSubmodule σ K) (eval₂Hom k' a) (MvPolynomial.X i)
    (by simpa only [eval₂Hom_X', hi] using (isUnit_one : IsUnit (1 : Γ(U.toScheme, ⊤))))
  let g := U.toScheme.toSpecΓ ≫ Spec.map (CommRingCat.ofHom f)
  have H : IsPullback g U.ι (V.f i) (sectionsMorphism k s hs) := by
    refine @IsOpenImmersion.isPullback _ _ _ _ g U.ι (V.f i)
      (sectionsMorphism k s hs) inferInstance (V.map_prop i) ?_ ?_
    · exact (sectionsMorphism_local k s hs i).trans (Category.assoc _ _ _).symm
    · change _ ⁻¹ᵁ (Proj.awayι (homogeneousSubmodule σ K) (MvPolynomial.X i) _ _).opensRange = _
      erw [Proj.opensRange_awayι, sectionsMorphism_preimage, Scheme.Opens.opensRange_ι]
  have hg : IsClosedImmersion g := MorphismProperty.of_isPullback H.flip inferInstance
  refine ⟨(IsClosedImmersion.isAffine_surjective_of_isAffine g).1, ?_⟩
  exact normalized_eval₂_of_evalAway k' a i hi
    (@affine_evaluation_surjective _ _ U.toScheme f hg)

end
end MaximalSeshadri.Projective

namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial
open MaximalSeshadri.Frames
open scoped AlgebraicGeometry
variable {K σ τ : Type u} [CommRing K] {X : Scheme.{u}} {M : X.Modules}
attribute [local instance] MvPolynomial.gradedAlgebra

lemma eval₂_surjective_reindex {R : Type u} [CommRing R] (k : K →+* R)
    (a : σ → R) (e : τ ≃ σ) (h : Function.Surjective (eval₂Hom k a)) :
    Function.Surjective (eval₂Hom k (a ∘ e)) := by
  intro r
  obtain ⟨p, hp⟩ := h r
  refine ⟨rename e.symm p, ?_⟩
  change eval₂ k (a ∘ e) (rename e.symm p) = r
  rw [MvPolynomial.eval₂_rename]
  change eval₂ k a p = r at hp
  simpa only [Function.comp_assoc, Equiv.self_comp_symm, Function.comp_id] using hp

theorem sectionsMorphism_reindex_closed (k : K →+* Γ(X, ⊤))
    (s : σ → (O X ⟶ M)) (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    [IsClosedImmersion (sectionsMorphism k s hs)] (e : τ ≃ σ)
    (ht : (⨆ i, SectionOpens.isoOpen (s (e i))) = ⊤) :
    IsClosedImmersion (sectionsMorphism k (s ∘ e) ht) := by
  apply sectionsMorphism_isClosedImmersion
  · intro i
    exact (sectionsMorphism_chart_generators k s hs (e i)).1
  · intro i
    let U := SectionOpens.isoOpen (s (e i))
    let k' : K →+* Γ(U.toScheme, ⊤) := U.ι.appTop.hom.comp k
    let a : σ → Γ(U.toScheme, ⊤) := fun j =>
      coefficient (sectionFrame (s (e i))) (restrictSection U.ι (s j))
    have h : Function.Surjective (eval₂Hom k' a) :=
      (sectionsMorphism_chart_generators k s hs (e i)).2
    change Function.Surjective (eval₂Hom k' (a ∘ e))
    exact eval₂_surjective_reindex k' a e h

end
end MaximalSeshadri.Projective

end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Configurations_SmoothRationalPoints
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                          
section

namespace MaximalSeshadri
noncomputable section
open Cardinal

theorem algebraic_of_countable_presentation
    {F E σ : Type} [Field F] [Uncountable F] [Field E] [Algebra F E]
    [Countable σ] (φ : MvPolynomial σ F →ₐ[F] E) (hφ : Function.Surjective φ) :
    Algebra.IsAlgebraic F E := by
  constructor
  intro x
  by_contra hx
  have hLI := (show Transcendental F x from hx).linearIndependent_sub_inv
  have hrank : Module.rank F E ≤ ℵ₀ := by
    calc
      _ ≤ Module.rank F (MvPolynomial σ F) :=
        LinearMap.rank_le_of_surjective φ.toLinearMap hφ
      _ = #(σ →₀ ℕ) := MvPolynomial.rank_eq
      _ ≤ ℵ₀ := Cardinal.mk_le_aleph0
  exact (not_le_of_gt (Cardinal.aleph0_lt_mk (α := F)))
    (hLI.cardinal_le_rank.trans hrank)

theorem point_of_countable_presentation
    {F A σ : Type} [Field F] [IsAlgClosed F] [Uncountable F]
    [CommRing A] [Nontrivial A] [Algebra F A] [Countable σ]
    (φ : MvPolynomial σ F →ₐ[F] A) (hφ : Function.Surjective φ) :
    Nonempty (A →ₐ[F] F) := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal A
  let : m.IsMaximal := hm
  let : Field (A ⧸ m) := Ideal.Quotient.field m
  let q : A →ₐ[F] A ⧸ m := Ideal.Quotient.mkₐ F m
  let ψ : MvPolynomial σ F →ₐ[F] A ⧸ m := q.comp φ
  have hψ : Function.Surjective ψ :=
    (Ideal.Quotient.mk_surjective).comp hφ
  let : Algebra.IsAlgebraic F (A ⧸ m) :=
    algebraic_of_countable_presentation ψ hψ
  exact ⟨(IsAlgClosed.lift : (A ⧸ m) →ₐ[F] F).comp q⟩

theorem point_avoiding_sequence_of_countable_presentation
    {F A σ : Type} [Field F] [IsAlgClosed F] [Uncountable F]
    [CommRing A] [IsDomain A] [Algebra F A] [Countable σ]
    (φ : MvPolynomial σ F →ₐ[F] A) (hφ : Function.Surjective φ)
    (a : ℕ → A) (ha : ∀ n, a n ≠ 0) :
    ∃ f : A →ₐ[F] F, ∀ n, f (a n) ≠ 0 := by
  classical
  let S : Submonoid A := Submonoid.closure (Set.range a)
  have hcount : (S : Set A).Countable := by
    change ((Submonoid.closure (Set.range a) : Submonoid A) : Set A).Countable
    rw [← FreeMonoid.mrange_lift, MonoidHom.coe_mrange]
    exact Set.countable_range _
  let : Countable S := hcount.to_subtype
  have hden : S ≤ nonZeroDivisors A := by
    apply Submonoid.closure_le.mpr
    rintro b ⟨n, rfl⟩
    exact mem_nonZeroDivisors_iff_ne_zero.mpr (ha n)
  let B := Localization S
  let : IsDomain B := IsLocalization.isDomain_localization hden
  let j : A →ₐ[F] B := IsScalarTower.toAlgHom F A B
  let vals : σ ⊕ S → B := Sum.elim (fun i => j (φ (MvPolynomial.X i)))
    (fun s => IsLocalization.mk' B 1 s)
  let ψ : MvPolynomial (σ ⊕ S) F →ₐ[F] B := MvPolynomial.aeval vals
  have hre : ψ.comp (MvPolynomial.rename Sum.inl) = j.comp φ := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [ψ, vals]
  have hψ : Function.Surjective ψ := by
    intro z
    obtain ⟨b, s, rfl⟩ := IsLocalization.exists_mk'_eq S z
    obtain ⟨p, rfl⟩ := hφ b
    refine ⟨MvPolynomial.rename Sum.inl p * MvPolynomial.X (Sum.inr s), ?_⟩
    rw [map_mul]
    have he := DFunLike.congr_fun hre p
    change ψ (MvPolynomial.rename Sum.inl p) = j (φ p) at he
    rw [he]
    simp only [ψ, MvPolynomial.aeval_X, vals, Sum.elim_inr]
    exact (IsLocalization.mk'_eq_mul_mk'_one _ _).symm
  obtain ⟨g⟩ := point_of_countable_presentation ψ hψ
  refine ⟨g.comp j, fun n => ?_⟩
  let s : S := ⟨a n, Submonoid.subset_closure ⟨n, rfl⟩⟩
  exact ((IsLocalization.map_units B s).map g.toMonoidHom).ne_zero

theorem point_avoiding_sequence
    {F A : Type} [Field F] [IsAlgClosed F] [Uncountable F]
    [CommRing A] [IsDomain A] [Algebra F A] [Algebra.FiniteType F A]
    (a : ℕ → A) (ha : ∀ n, a n ≠ 0) :
    ∃ f : A →ₐ[F] F, ∀ n, f (a n) ≠ 0 := by
  obtain ⟨n, φ, hφ⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
    (inferInstance : Algebra.FiniteType F A)
  exact point_avoiding_sequence_of_countable_presentation φ hφ a ha

end

end MaximalSeshadri

end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Geometry_SmoothSurfaceDimension
attribute [-instance] _root_.OAI.MaximalSeshadri.AffineBlowup.scheme_isIntegral _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.IntegralCurve.noetherian _root_.OAI.MaximalSeshadri.Geometry.IntegralCurve.proper _root_.OAI.MaximalSeshadri.Geometry.Surface.compact _root_.OAI.MaximalSeshadri.Geometry.Surface.locallyNoetherian _root_.OAI.MaximalSeshadri.Geometry.Surface.noetherian _root_.OAI.MaximalSeshadri.Geometry.Surface.proper _root_.OAI.MaximalSeshadri.Geometry.Surface.separated _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.nonemptyAffineCover_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                
section

namespace MaximalSeshadri.LocalCurve
noncomputable section

open MvPolynomial
open MaximalSeshadri.AlgebraicJets

theorem two_le_dimension_of_standard_smooth {K S : Type} [Field K] [CommRing S]
    [Algebra K S] [Algebra.IsStandardSmoothOfRelativeDimension 2 K S]
    (ρ : S →ₐ[K] K) : 2 ≤ ringKrullDim S := by
  obtain ⟨x,hx,he⟩ := exists_centered_etale_coordinates 2 ρ
  let φ := aeval (R := K) x
  let : Algebra (MvPolynomial (Fin 2) K) S := φ.toRingHom.toAlgebra
  let : IsScalarTower K (MvPolynomial (Fin 2) K) S :=
    IsScalarTower.of_algebraMap_eq' φ.comp_algebraMap.symm
  let : Algebra.Etale (MvPolynomial (Fin 2) K) S := he
  let q := RingHom.ker ρ
  have : q.IsPrime := RingHom.ker_isPrime ρ
  have hq : q.under (MvPolynomial (Fin 2) K) = idealOfVars (Fin 2) K := by
    rw [idealOfVars_eq_ker_constantCoeff]
    have hc : ρ.toRingHom.comp φ.toRingHom = constantCoeff := by
      apply ringHom_ext
      · intro c; simp [φ]
      · intro i; simpa [φ] using hx i
    change RingHom.ker (ρ.toRingHom.comp φ.toRingHom) = _
    rw [hc]
  let : (idealOfVars (Fin 2) K).IsPrime := by
    rw [idealOfVars_eq_ker_constantCoeff]
    exact RingHom.ker_isPrime _
  let : q.LiesOver (idealOfVars (Fin 2) K) := ⟨hq.symm⟩
  let P : Ideal (MvPolynomial (Fin 2) K) := Ideal.span {X (0 : Fin 2)}
  let : P.IsPrime := (Ideal.span_singleton_prime (X_ne_zero 0)).mpr X_prime
  have hP : P < idealOfVars (Fin 2) K := by
    refine lt_of_le_of_ne (Ideal.span_le.mpr (by
      rintro _ rfl
      exact Ideal.subset_span ⟨0,rfl⟩)) ?_
    intro H
    have h1 : X (1 : Fin 2) ∈ P := H ▸ Ideal.subset_span ⟨1,rfl⟩
    have hd : (X (0 : Fin 2) : MvPolynomial (Fin 2) K) ∣ X 1 :=
      Ideal.mem_span_singleton.mp h1
    have := X_dvd_X.mp hd
    norm_num at this
  obtain ⟨Q,hQ,hQP,hQL⟩ := Ideal.exists_ideal_lt_liesOver_of_lt q hP
  have := hQP
  have := hQL
  have hbot : (⊥ : Ideal (MvPolynomial (Fin 2) K)) < P := by
    apply bot_lt_iff_ne_bot.mpr
    intro H
    have h0 : X (0 : Fin 2) ∈ P := Ideal.subset_span (by simp)
    rw [H,Ideal.mem_bot] at h0
    exact X_ne_zero 0 h0
  obtain ⟨Q₀,hQ₀,hQ₀P,hQ₀L⟩ := Ideal.exists_ideal_lt_liesOver_of_lt Q hbot
  let l : LTSeries (PrimeSpectrum S) :=
    ((RelSeries.singleton {(a,b) : PrimeSpectrum S × PrimeSpectrum S | a < b} (⟨Q₀,hQ₀P⟩ : PrimeSpectrum S)).snoc
      (⟨Q,hQP⟩ : PrimeSpectrum S) hQ₀).snoc (⟨q,inferInstance⟩ : PrimeSpectrum S) hQ
  simpa only [show l.length = 2 from rfl, Nat.cast_ofNat, ringKrullDim] using
    Order.LTSeries.length_le_krullDim l
end
end MaximalSeshadri.LocalCurve

namespace MaximalSeshadri.Geometry
noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.ProjectiveBertini

lemma Surface.two_le_dimension (S : Surface) : 2 ≤ topologicalKrullDim S.scheme := by
  obtain ⟨U,hxU,hU,hstd⟩ := exists_standard_smooth_affine_inside S.structureMap 2
    ⊤ (Classical.ofNonempty : S.scheme) (by trivial)
  let : Nonempty U.1 := ⟨⟨_,hxU⟩⟩
  let := (openScalars S.structureMap U.1).toAlgebra
  let : Algebra.IsStandardSmoothOfRelativeDimension 2 ℂ Γ(S.scheme,U.1) := hstd
  let : Algebra.IsStandardSmooth ℂ Γ(S.scheme,U.1) :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth 2
  have : Uncountable ℂ := by
    rw [← Cardinal.aleph0_lt_mk_iff, Cardinal.mk_complex]
    exact Cardinal.aleph0_lt_continuum
  obtain ⟨ρ,-⟩ := point_avoiding_sequence (F := ℂ) (A := Γ(S.scheme,U.1))
    (fun _ => 1) (fun _ => one_ne_zero)
  have hd := LocalCurve.two_le_dimension_of_standard_smooth ρ
  have : IsOpenImmersion U.2.fromSpec :=
    IsAffineOpen.isOpenImmersion_fromSpec U.2
  have he := U.2.fromSpec.isOpenEmbedding.isEmbedding.isInducing.topologicalKrullDim_le
  change topologicalKrullDim (PrimeSpectrum Γ(S.scheme,U.1)) ≤ _ at he
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim] at he
  exact hd.trans he
end
end MaximalSeshadri.Geometry

end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Blowup_PointBlowupExistence
attribute [-instance] _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.Surface.separated _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.projectiveSpaceToSpec_separated _root_.OAI.MaximalSeshadri.PullbackTensor.line_isIso _root_.OAI.MaximalSeshadri.nonemptyAffineCover_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                              
section

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.Projective MaximalSeshadri.SectionOpens

lemma Surface.centre_support_ne_top (S : Surface) (r : ℕ) (p : Configuration S r) :
    (centreIdeal S r p).support ≠ ⊤ := by
  classical
  intro h
  let q : Fin r → (Spec (.of ℂ) ⟶ S.scheme) := fun i => (p.val i).left
  let f : Fin r → Set S.scheme := fun i => ((q i).ker.support : Set S.scheme)
  have hc : ∀ i, IsClosed (f i) := fun i => ((q i).ker.support).isClosed
  have hu : Set.univ ⊆ ⋃₀ (↑(Finset.univ.image f) : Set (Set S.scheme)) := by
    intro x _
    have hx : x ∈ (centreIdeal S r p).support := by rw [h]; trivial
    obtain ⟨i,hi⟩ := (FinitePointBlowup.mem_centre_support q x).mp hx
    exact Set.mem_sUnion.mpr ⟨f i,Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩,hi⟩
  obtain ⟨z,hz,huz⟩ := isIrreducible_iff_sUnion_isClosed.mp
    (IrreducibleSpace.isIrreducible_univ S.scheme : IsIrreducible (Set.univ : Set S.scheme))
    (Finset.univ.image f) (by
      intro z hz
      obtain ⟨i,-,rfl⟩ := Finset.mem_image.mp hz
      exact hc i) hu
  obtain ⟨i,-,rfl⟩ := Finset.mem_image.mp hz
  have hs := FinitePointBlowup.point_support q
    S.structureMap (fun i => (p.val i).w) i
  let : Subsingleton S.scheme := ⟨fun x y => by
    have hx := huz (show x ∈ Set.univ from trivial)
    have hy := huz (show y ∈ Set.univ from trivial)
    change x ∈ ((q i).ker.support : Set S.scheme) at hx
    change y ∈ ((q i).ker.support : Set S.scheme) at hy
    rw [hs] at hx hy
    exact hx.trans hy.symm⟩
  have hd := topologicalKrullDim_zero_of_discreteTopology S.scheme
  have h2 := S.two_le_dimension
  exact (by norm_num : ¬ (2 : WithBot ℕ∞) ≤ 0) (h2.trans hd)

theorem LineBundle.projective_embedding {X : Scheme.{0}} [IsIntegral X] [CompactSpace X]
    (p : X ⟶ Spec (.of ℂ)) [IsProper p] (L : LineBundle X) (hL : L.IsAmple) :
    ∃ N : ℕ, ∃ e : X ⟶ complexProjectiveSpace N,
      IsClosedImmersion e ∧ e ≫ projectiveSpaceToSpec N = p := by
  classical
  obtain ⟨n,hn,σ,hσ,s,hs,hc⟩ := L.ample_projective_sections p hL
  have hne : Nonempty σ := by
    obtain ⟨x⟩ := (inferInstance : Nonempty X)
    have hx : x ∈ ⨆ i, isoOpen (s i) := by rw [hs]; trivial
    obtain ⟨i,-⟩ := Opens.mem_iSup.mp hx
    exact ⟨i⟩
  have hpos := Fintype.card_pos_iff.mpr hne
  obtain ⟨N,hN⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hpos)
  let e : Fin (N+1) ≃ σ := ((Fintype.equivFin σ).trans (finCongr hN)).symm
  have ht : (⨆ i,isoOpen (s (e i))) = ⊤ := (e.iSup_comp (g := fun j => isoOpen (s j))).trans hs
  let k := p.appTop.hom.comp (Scheme.ΓSpecIso (.of ℂ)).inv.hom
  refine ⟨N,sectionsMorphism k (s ∘ e) ht,sectionsMorphism_reindex_closed _ s hs e ht,?_⟩
  change sectionsMorphism k (s ∘ e) ht ≫ projectiveBase = p
  exact (sectionsMorphism_over k (s ∘ e) ht).trans (SpecMaps.factor p)

theorem Surface.pointBlowup_exists_s01_oai (S : Surface) (L : LineBundle S.scheme)
    (hL : L.IsAmple) (r : ℕ) (p : Configuration S r) :
    Nonempty (PointBlowup S r p) := by
  classical
  let I := centreIdeal S r p
  let B := BlowupGluing.scheme I
  let π : B ⟶ S.scheme := BlowupGluing.projection I
  have hπ : IsBlowup I π := BlowupGluing.isBlowup I
  let : IsIntegral B := BlowupGluing.scheme_isIntegral I (S.centre_support_ne_top r p)
  let : IsProper π := BlowupGluing.projection_proper I
  let : IsProper (π ≫ S.structureMap) := inferInstance
  let : CompactSpace B := QuasiCompact.compactSpace_of_compactSpace π
  let q : Fin r → (Spec (.of ℂ) ⟶ S.scheme) := fun i => (p.val i).left
  have hq : ∀ i, q i ≫ S.structureMap = 𝟙 _ := fun i => (p.val i).w
  have hd : Function.Injective (fun i => q i (⟨⊥,Ideal.isPrime_bot⟩ : Spec (.of ℂ))) :=
    p.property
  let : SmoothOfRelativeDimension 2 (π ≫ S.structureMap) :=
    FinitePointBlowup.smooth_finite_point_blowup_s01 q S.structureMap hq hd π hπ
  obtain ⟨J,ι,hJ⟩ := hπ.1
  obtain ⟨a,n,ha,hn,hA⟩ := hπ.ample_exceptional_twist_s01 L hL J ι hJ
  obtain ⟨N,e,he,hep⟩ := ((((L.pow a).pullback π).pow n).tensor J).projective_embedding
    (π ≫ S.structureMap) hA
  let T : Surface := ⟨B,π ≫ S.structureMap,inferInstance,inferInstance,N,e,he,hep⟩
  have hE i : InvertiblePullbackIdeal (q i).ker π :=
    FinitePointBlowup.exceptional_invertible q S.structureMap hq hd π hπ i
  choose E j hj using hE
  exact ⟨⟨T,π,rfl,hπ,E,j,hj⟩⟩

end
end MaximalSeshadri.Geometry

end

end OAI
end

theorem solution : type_of% @OAI.MaximalSeshadri.Geometry.Surface.pointBlowup_exists_s01_oai := @OAI.MaximalSeshadri.Geometry.Surface.pointBlowup_exists_s01_oai
