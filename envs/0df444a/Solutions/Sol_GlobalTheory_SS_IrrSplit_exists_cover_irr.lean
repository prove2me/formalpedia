-- Prove2me | solution 1 for GlobalTheory.SS.IrrSplit.exists_cover_irr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:52:36.904375+00:00
-- url     : https://prove2.me/submissions/16108dec-6944-4e1a-a9f6-327cfae870f7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsReducedIsNormalSchemeIsLocallyNoetherianOfSmoo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsCoverModelIrreducibleSpecialFibre
import Theorems.Thm_GlobalTheory_SS_IrrSplit_restrictModel_j
import Theorems.Thm_GlobalTheory_isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.IrrSplit
namespace GlobalTheory.SS.IrrSplit
theorem _root_.solution : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] (A : Over (Sp K)) (M : Model R A), ∃ (n : ℕ) (N : Fin n → Model R A) (g : ∀ i, (N i).Y ⟶ M.Y), (∀ i, (N i).Irr ∧ IsOpenImmersion (g i).left ∧ (N i).j ≫ (g i).left = M.j) ∧ ∀ y ∈ M.sp, ∃ i, y ∈ Set.range (g i).left := by
  intro R K _ _ _ _ _ _ A M
  have := M.smooth
  have := M.qc
  let f : M.Y.left ⟶ Sp R := M.Y.hom
  let c : Sp R := IsLocalRing.closedPoint R
  have : IsLocallyNoetherian M.Y.left := LocallyOfFiniteType.isLocallyNoetherian f
  have hf : Smooth f := M.smooth
  have hf' : QuasiCompact f := M.qc
  have hs : Smooth (f.fiberToSpecResidueField c) :=
    inferInstanceAs (Smooth (pullback.snd f ((Sp R).fromSpecResidueField c)))
  obtain ⟨-, hn, hl⟩ := GlobalTheory.isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field
    ((Sp R).residueField c) (f.fiber c) (f.fiberToSpecResidueField c) hs
  have hn' : GlobalTheory.IsNormalScheme (f.fiber c) := GlobalTheory.IsNormalScheme.of_pred hn
  have : CompactSpace (f.fiber c) := inferInstance
  have : IsNoetherian (f.fiber c) := {}
  have hfin : (irreducibleComponents (f.fiber c)).Finite :=
    TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
  have hr : Set.range (f.fiberι c) = M.sp := f.range_fiberι c
  have hcl : Topology.IsClosedEmbedding (f.fiberι c) := by
    refine ⟨(f.fiberι c).isEmbedding, ?_⟩
    rw [f.range_fiberι]
    exact (IsLocalRing.isClosed_singleton_closedPoint R).preimage f.continuous
  have : Finite (irreducibleComponents (f.fiber c)) := hfin
  obtain ⟨n, ⟨σ⟩⟩ := Finite.exists_equiv_fin (irreducibleComponents (f.fiber c))
  let U : Fin n → M.Y.left.Opens := fun i => ⟨(f.fiberι c '' (σ.symm i).1ᶜ)ᶜ,
    (hcl.isClosedMap _ (GlobalTheory.IsNormalScheme.isOpen_of_mem_irreducibleComponents
      (σ.symm i).2).isClosed_compl).isOpen_compl⟩
  have hU : ∀ i, Set.range (pullback.fst M.Y.hom (spMap (algebraMap R K))) ⊆ Set.range (U i).ι := by
    rintro i _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    rintro ⟨z, -, hz⟩
    have h1 : pullback.fst M.Y.hom (spMap (algebraMap R K)) x ∈ M.sp := hr ▸ ⟨z, hz⟩
    have h2 : M.Y.hom (pullback.fst M.Y.hom (spMap (algebraMap R K)) x) =
        spMap (algebraMap R K) (pullback.snd M.Y.hom (spMap (algebraMap R K)) x) := by
      rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
    have h3 := h2.symm.trans h1
    generalize pullback.snd M.Y.hom (spMap (algebraMap R K)) x = p at h3
    have h4 : Ideal.comap (algebraMap R K) p.asIdeal = IsLocalRing.maximalIdeal R :=
      congrArg PrimeSpectrum.asIdeal h3
    have h5 : p.asIdeal = ⊥ := (Ideal.eq_bot_or_top (K := K) p.asIdeal).resolve_right p.isPrime.ne_top
    rw [h5, Ideal.comap_bot_of_injective _ (IsFractionRing.injective R K)] at h4
    exact IsDiscreteValuationRing.not_a_field R h4.symm
  have hmem : ∀ i z, f.fiberι c z ∈ U i ↔ z ∈ (σ.symm i).1 := by
    intro i z
    show f.fiberι c z ∉ f.fiberι c '' (σ.symm i).1ᶜ ↔ _
    rw [hcl.injective.mem_set_image]
    simp
  refine ⟨n, fun i => restrictModel M (U i) (hU i), fun i => Over.homMk (U i).ι rfl,
    fun i => ⟨?_, inferInstanceAs (IsOpenImmersion (U i).ι), restrictModel_j M (U i) (hU i)⟩, ?_⟩
  · have hi : IsIrreducible (f.fiberι c '' (σ.symm i).1) :=
      (σ.symm i).2.1.image _ (f.fiberι c).continuous.continuousOn
    have he : (restrictModel M (U i) (hU i)).sp = (U i).ι ⁻¹' (f.fiberι c '' (σ.symm i).1) := by
      ext y
      constructor
      · intro hy
        have : (U i).ι y ∈ M.sp := hy
        rw [← hr] at this
        obtain ⟨z, hz⟩ := this
        refine ⟨z, (hmem i z).1 ?_, hz⟩
        rw [hz]; exact y.2
      · rintro ⟨z, -, hz⟩
        have : (U i).ι y ∈ M.sp := hr ▸ ⟨z, hz⟩
        exact this
    show IsIrreducible _
    rw [he]
    refine ⟨?_, hi.2.preimage (U i).ι.isOpenEmbedding⟩
    obtain ⟨z, hz⟩ := (σ.symm i).2.1.1
    exact ⟨⟨_, (hmem i z).2 hz⟩, z, hz, rfl⟩
  · intro y hy
    rw [← hr] at hy
    obtain ⟨z, rfl⟩ := hy
    refine ⟨σ ⟨_, irreducibleComponent_mem_irreducibleComponents z⟩, ⟨_, (hmem _ z).2 ?_⟩, rfl⟩
    rw [Equiv.symm_apply_apply]
    exact mem_irreducibleComponent
end GlobalTheory.SS.IrrSplit
