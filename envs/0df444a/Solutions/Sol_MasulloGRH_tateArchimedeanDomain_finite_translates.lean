-- Prove2me | solution 1 for MasulloGRH.tateArchimedeanDomain_finite_translates
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T12:43:50.530982+00:00
-- url     : https://prove2.me/submissions/046768df-d3c8-4c63-b485-30c481c5d728

import Mathlib
import Definitions.Def_MasulloGRH_TateArchimedeanDomain
import Theorems.Thm_MasulloGRH_tateArchimedeanDomain_relCompact_and_interior_nonempty

open NumberField

set_option autoImplicit false
set_option maxSynthPendingDepth 8

namespace Sol_MasulloGRH_tateArchimedeanDomain_finite_translates

open NumberField.InfinitePlace.Completion

variable (F : Type*) [Field F]

/-- The coordinate change `∏_{v ∣ ∞} F_v ≃ ℝ^{r₁} × ℂ^{r₂}` of Mathlib is continuous. -/
theorem continuous_ringEquiv_mixedSpace :
    Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F) := by
  change Continuous (fun x ↦ InfiniteAdeleRing.ringEquiv_mixedSpace F x)
  simp only [InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
  exact (continuous_pi fun v ↦ (isometry_extensionEmbeddingOfIsReal v.2).continuous.comp
    (continuous_apply v.val)).prodMk
    (continuous_pi fun v ↦ (isometry_extensionEmbedding v.val).continuous.comp
      (continuous_apply v.val))

/-- In the coordinates `ℝ^{r₁} × ℂ^{r₂}`, the diagonal image of a unit `u` is the mixed embedding
of `u`. -/
theorem ringEquiv_mixedSpace_unitsToInfiniteIdeles (u : (𝓞 F)ˣ) :
    InfiniteAdeleRing.ringEquiv_mixedSpace F
        ((MasulloGRH.unitsToInfiniteIdeles F u : (InfiniteAdeleRing F)ˣ) : InfiniteAdeleRing F) =
      mixedEmbedding F (algebraMap (𝓞 F) F u.val) := by
  rw [InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]
  rfl

variable [NumberField F]

/-- The image of the ring of integers under the mixed embedding is a closed subset of
`ℝ^{r₁} × ℂ^{r₂}`, since it is a discrete additive subgroup. -/
theorem isClosed_integerLattice :
    IsClosed ((mixedEmbedding.integerLattice F : Submodule ℤ (mixedEmbedding.mixedSpace F)) :
      Set (mixedEmbedding.mixedSpace F)) := by
  have : DiscreteTopology (mixedEmbedding.integerLattice F).toAddSubgroup :=
    inferInstanceAs (DiscreteTopology (mixedEmbedding.integerLattice F))
  rw [← Submodule.coe_toAddSubgroup]
  exact AddSubgroup.isClosed_of_discrete

/-- The image of the ring of integers under the mixed embedding is a discrete subset of
`ℝ^{r₁} × ℂ^{r₂}`. -/
theorem isDiscrete_integerLattice :
    IsDiscrete ((mixedEmbedding.integerLattice F : Submodule ℤ (mixedEmbedding.mixedSpace F)) :
      Set (mixedEmbedding.mixedSpace F)) :=
  isDiscrete_iff_discreteTopology.mpr
    (inferInstanceAs (DiscreteTopology (mixedEmbedding.integerLattice F)))

end Sol_MasulloGRH_tateArchimedeanDomain_finite_translates

open MasulloGRH Sol_MasulloGRH_tateArchimedeanDomain_finite_translates

theorem solution
    (F : Type*) [Field F] [NumberField F]
    (b : Module.Basis (Fin (Units.rank F)) ℤ (Additive ((𝓞 F)ˣ ⧸ Units.torsion F)))
    (v₀ : InfinitePlace F) (σ : ℂ ≃ₐ[ℝ] ℂ)
    (K : Set (MonoidHom.ker (RiemannMasullo.infiniteIdeleNorm F))) (hK : IsCompact K) :
    {u : (𝓞 F)ˣ | ∃ e ∈ closure (tateArchimedeanDomain F b v₀ σ), ∃ k ∈ K,
      (k : (InfiniteAdeleRing F)ˣ) =
        unitsToInfiniteIdeles F u * (e : (InfiniteAdeleRing F)ˣ)}.Finite := by
  -- the compact set `K × closure E₀`
  have hE : IsCompact (closure (tateArchimedeanDomain F b v₀ σ)) :=
    (tateArchimedeanDomain_relCompact_and_interior_nonempty F b v₀ σ).1
  let D : Set (MonoidHom.ker (RiemannMasullo.infiniteIdeleNorm F) ×
      MonoidHom.ker (RiemannMasullo.infiniteIdeleNorm F)) :=
    K ×ˢ closure (tateArchimedeanDomain F b v₀ σ)
  have hD : IsCompact D := hK.prod hE
  -- the quotient map `(k, e) ↦ k / e`, read in the coordinates `ℝ^{r₁} × ℂ^{r₂}`
  let q : MonoidHom.ker (RiemannMasullo.infiniteIdeleNorm F) ×
      MonoidHom.ker (RiemannMasullo.infiniteIdeleNorm F) → mixedEmbedding.mixedSpace F :=
    fun p ↦ InfiniteAdeleRing.ringEquiv_mixedSpace F
      (((p.1 : (InfiniteAdeleRing F)ˣ) / (p.2 : (InfiniteAdeleRing F)ˣ) :
        (InfiniteAdeleRing F)ˣ) : InfiniteAdeleRing F)
  have hval : Continuous (fun x : (InfiniteAdeleRing F)ˣ ↦ (x : InfiniteAdeleRing F)) :=
    Units.continuous_val
  have hq : Continuous q :=
    (continuous_ringEquiv_mixedSpace F).comp (hval.comp
      ((continuous_subtype_val.comp continuous_fst).div'
        (continuous_subtype_val.comp continuous_snd)))
  have hC : IsCompact (q '' D) := hD.image hq
  -- a compact set meets the closed discrete lattice in a finite set
  have hfin : (q '' D ∩
      ((mixedEmbedding.integerLattice F : Submodule ℤ (mixedEmbedding.mixedSpace F)) :
        Set (mixedEmbedding.mixedSpace F))).Finite :=
    (hC.inter_right (isClosed_integerLattice F)).finite
      ((isDiscrete_integerLattice F).mono Set.inter_subset_right)
  -- the units embed injectively in the mixed space
  let f : (𝓞 F)ˣ → mixedEmbedding.mixedSpace F :=
    fun u ↦ mixedEmbedding F (algebraMap (𝓞 F) F u.val)
  have hf : Function.Injective f :=
    (mixedEmbedding_injective F).comp (RingOfIntegers.coe_injective.comp Units.val_injective)
  refine (hfin.preimage hf.injOn).subset ?_
  rintro u ⟨e, he, k, hk, hke⟩
  have hquot : (k : (InfiniteAdeleRing F)ˣ) / (e : (InfiniteAdeleRing F)ˣ) =
      unitsToInfiniteIdeles F u := div_eq_iff_eq_mul.mpr hke
  refine ⟨⟨(k, e), ⟨hk, he⟩, ?_⟩, ⟨u.val, rfl⟩⟩
  change InfiniteAdeleRing.ringEquiv_mixedSpace F
      (((k : (InfiniteAdeleRing F)ˣ) / (e : (InfiniteAdeleRing F)ˣ) :
        (InfiniteAdeleRing F)ˣ) : InfiniteAdeleRing F) =
    mixedEmbedding F (algebraMap (𝓞 F) F u.val)
  rw [hquot]
  exact ringEquiv_mixedSpace_unitsToInfiniteIdeles F u
