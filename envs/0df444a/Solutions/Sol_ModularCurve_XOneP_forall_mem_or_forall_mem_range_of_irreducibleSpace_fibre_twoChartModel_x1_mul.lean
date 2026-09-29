-- Prove2me | solution 1 for ModularCurve.XOneP.forall_mem_or_forall_mem_range_of_irreducibleSpace_fibre_twoChartModel_x1_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/1d281a04-cf14-51da-916b-8a421e3688cd

import Mathlib
import Definitions.Def_ModularCurve_TwoChartModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardChartSections
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_JacJ1Iface
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_RelPicardPullback

import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XOneP_forall_mem_or_forall_mem_range_of_irreducibleSpace_fibre_twoChartModel_x1_mul

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve NeronModelInfra GoodReductionJacobian TensorProduct"

theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (u u' : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j)) (huu' : u * u' = (p : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j)) ^ 12)
    (k : Type) [Field k] (φ : A →+* k) (hφ : ¬ Function.Injective φ)
    {C : Scheme.{0}} [IrreducibleSpace ↥C] (i : C ⟶ pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom φ))) :
    (∀ z ∈ Set.range i.base, ∀ 𝔮 : ↥(ModularCurve.TwoChart.XFin A (↥K) j),
        (pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom φ))).base z = (ModularCurve.TwoChart.ιFin A (↥K) j).base 𝔮 → u ∈ 𝔮.asIdeal) ∨
    (∀ z ∈ Set.range i.base, ∀ 𝔮 : ↥(ModularCurve.TwoChart.XFin A (↥K) j),
        (pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom φ))).base z = (ModularCurve.TwoChart.ιFin A (↥K) j).base 𝔮 → u' ∈ 𝔮.asIdeal) := by
  classical
  have hker : RingHom.ker φ = IsLocalRing.maximalIdeal A := by
    have hne : RingHom.ker φ ≠ ⊥ := fun h => hφ ((RingHom.injective_iff_ker_eq_bot φ).mpr h)
    exact IsLocalRing.eq_maximalIdeal (Ring.DimensionLEOne.maximalOfPrime hne (RingHom.ker_isPrime φ))

  have hq : ∀ (z : ↥(pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom φ)))) (𝔮 : ↥(ModularCurve.TwoChart.XFin A (↥K) j)),
      (pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom φ))).base z = (ModularCurve.TwoChart.ιFin A (↥K) j).base 𝔮 → u ∈ 𝔮.asIdeal ∨ u' ∈ 𝔮.asIdeal := by
    intro z 𝔮 hz
    have h1 : (ModularCurve.TwoChart.modelTo A (↥K) j).base ((ModularCurve.TwoChart.ιFin A (↥K) j).base 𝔮) = IsLocalRing.closedPoint A := by
      rw [← hz, ← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
      apply PrimeSpectrum.ext
      rw [Spec.map_apply]
      show Ideal.comap φ _ = IsLocalRing.maximalIdeal A
      rw [show ((pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom φ))).base z).asIdeal = ⊥ from
          (IsLocalRing.isField_iff_maximalIdeal_eq.mp (Field.toIsField k)) ▸
            (PrimeSpectrum.ext_iff.mp (Subsingleton.elim _ (IsLocalRing.closedPoint k))),
        ← RingHom.ker_eq_comap_bot, hker]
    have h2 : (ModularCurve.TwoChart.modelTo A (↥K) j).base ((ModularCurve.TwoChart.ιFin A (↥K) j).base 𝔮) =
        (Spec.map (CommRingCat.ofHom (algebraMap A ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j)))).base 𝔮 := by
      rw [← Scheme.Hom.comp_apply, ModularCurve.TwoChart.ιFin_modelTo]
    have hcomap : Ideal.comap (algebraMap A ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j)) 𝔮.asIdeal = IsLocalRing.maximalIdeal A := by
      have h3 := h2.symm.trans h1
      rw [Spec.map_apply] at h3
      exact congrArg PrimeSpectrum.asIdeal h3
    have hp𝔮 : (p : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j)) ∈ 𝔮.asIdeal := by
      have : algebraMap A ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) p ∈ 𝔮.asIdeal := by rw [← Ideal.mem_comap, hcomap]; exact hAp
      rwa [map_natCast] at this
    have hmul : u * u' ∈ 𝔮.asIdeal := by
      rw [huu']
      exact Ideal.pow_mem_of_mem _ hp𝔮 12 (by norm_num)
    exact 𝔮.2.mem_or_mem hmul

  let Lv : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) → Set ↥(pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom φ))) := fun v =>
    {z | ∀ 𝔮 : ↥(ModularCurve.TwoChart.XFin A (↥K) j), (pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom φ))).base z = (ModularCurve.TwoChart.ιFin A (↥K) j).base 𝔮 → v ∈ 𝔮.asIdeal}
  have hLv : ∀ v, Lv v = (pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom φ))).base ⁻¹'
      ((ModularCurve.TwoChart.ιFin A (↥K) j).base '' {𝔮 : ↥(ModularCurve.TwoChart.XFin A (↥K) j) | v ∉ 𝔮.asIdeal})ᶜ := by
    intro v
    ext z
    simp only [Lv, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_compl_iff, Set.mem_image, not_exists, not_and]
    constructor
    · intro h 𝔮 hv h𝔮
      exact hv (h 𝔮 h𝔮.symm)
    · intro h 𝔮 hz
      by_contra hv
      exact h 𝔮 hv hz.symm
  have hclosed : ∀ v, IsClosed (Lv v) := by
    intro v
    rw [hLv]
    refine IsClosed.preimage (pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom φ))).continuous ?_
    rw [isClosed_compl_iff]
    apply (ModularCurve.TwoChart.ιFin A (↥K) j).isOpenEmbedding.isOpenMap
    have : {𝔮 : ↥(ModularCurve.TwoChart.XFin A (↥K) j) | v ∉ 𝔮.asIdeal} =
        ((PrimeSpectrum.basicOpen v : TopologicalSpace.Opens (PrimeSpectrum ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j))) : Set (PrimeSpectrum ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j))) := by
      ext 𝔮
      exact Iff.rfl
    rw [this]
    exact (PrimeSpectrum.basicOpen v).isOpen
  have hcov : (Set.univ : Set ↥C) ⊆ i.base ⁻¹' Lv u ∪ i.base ⁻¹' Lv u' := by
    intro c _
    by_cases hex : ∃ 𝔮 : ↥(ModularCurve.TwoChart.XFin A (↥K) j), (pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom φ))).base (i.base c) = (ModularCurve.TwoChart.ιFin A (↥K) j).base 𝔮
    · obtain ⟨𝔮₀, h𝔮₀⟩ := hex
      have huniq : ∀ 𝔮 : ↥(ModularCurve.TwoChart.XFin A (↥K) j), (pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom φ))).base (i.base c) = (ModularCurve.TwoChart.ιFin A (↥K) j).base 𝔮 → 𝔮 = 𝔮₀ :=
        fun 𝔮 h => (ModularCurve.TwoChart.ιFin A (↥K) j).isOpenEmbedding.injective (h.symm.trans h𝔮₀)
      rcases hq _ 𝔮₀ h𝔮₀ with h | h
      · left; intro 𝔮 h𝔮; rw [huniq 𝔮 h𝔮]; exact h
      · right; intro 𝔮 h𝔮; rw [huniq 𝔮 h𝔮]; exact h
    · left
      intro 𝔮 h𝔮
      exact (hex ⟨𝔮, h𝔮⟩).elim
  rcases isPreirreducible_iff_isClosed_union_isClosed.mp (IrreducibleSpace.isIrreducible_univ ↥C).2 _ _
      ((hclosed u).preimage i.continuous) ((hclosed u').preimage i.continuous) hcov with h | h
  · left
    rintro _ ⟨c, rfl⟩ 𝔮 h𝔮
    exact h (Set.mem_univ c) 𝔮 h𝔮
  · right
    rintro _ ⟨c, rfl⟩ 𝔮 h𝔮
    exact h (Set.mem_univ c) 𝔮 h𝔮

end S_ModularCurve_XOneP_forall_mem_or_forall_mem_range_of_irreducibleSpace_fibre_twoChartModel_x1_mul
end P2MW
export P2MW.S_ModularCurve_XOneP_forall_mem_or_forall_mem_range_of_irreducibleSpace_fibre_twoChartModel_x1_mul (solution)
