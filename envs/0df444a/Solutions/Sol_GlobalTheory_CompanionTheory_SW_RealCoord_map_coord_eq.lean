-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.RealCoord.map_coord_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:26:26.14696+00:00
-- url     : https://prove2.me/submissions/e8058c99-ccc4-4d1f-9337-b46252a65380

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_InfiniteAdeleHaarMapEqScaledVolume
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RealCoord_isHomeomorph_coord
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RealCoord_toMixed_add
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RealCoord_toMixed_injective
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RealCoord_toMixed_coord_algebraMap
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RealCoord_measurePreserving_toMixed
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RealCoord_coord_measurable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.RealCoord
open InfinitePlace InfinitePlace.Completion
variable (F : Type) [Field F] [NumberField F] [IsTotallyReal F]
open scoped Classical
namespace GlobalTheory.CompanionTheory.SW.RealCoord
theorem _root_.solution (lam : Measure (Ainf F)) (hl : IsStdInf lam) :
    lam.map (coord F) = ENNReal.ofReal (Real.sqrt |(discr F : ℝ)|)⁻¹ • (volume : Measure (InfinitePlace F → ℝ)) := by
  obtain ⟨hH, D, hD, hD1⟩ := hl
  haveI := hH
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  haveI : (lam.map (coord F)).IsAddHaarMeasure :=
    AddEquiv.isAddHaarMeasure_map lam (coord F).toAddEquiv (isHomeomorph_coord F).continuous
      (coordHomeo F).symm.continuous
  obtain ⟨c, hc⟩ : ∃ c : ℝ≥0, lam.map (coord F) = c • (volume : Measure (InfinitePlace F → ℝ)) :=
    ⟨_, Measure.isAddLeftInvariant_eq_smul _ _⟩
  set P := ZSpan.fundamentalDomain (mixedEmbedding.latticeBasis F) with hP
  have hmp := measurePreserving_toMixed F
  have hPm : MeasurableSet P := ZSpan.fundamentalDomain_measurableSet _
  set Λ := mixedEmbedding.integerLattice F with hΛdef
  set Γ : AddSubgroup (Ainf F) :=
    ((algebraMap F (Ainf F)).comp (algebraMap (𝓞 F) F)).toAddMonoidHom.range with hΓ
  let Ψ : Ainf F → mixedEmbedding.mixedSpace F := fun y => toMixed F (coord F y)
  have hΨadd : ∀ x y, Ψ (x + y) = Ψ x + Ψ y := fun x y => by
    simp only [Ψ, map_add, toMixed_add]
  have hΨinj : Function.Injective Ψ := (toMixed_injective F).comp (coord F).injective
  have hΨalg : ∀ a : 𝓞 F, Ψ (algebraMap F (Ainf F) (algebraMap (𝓞 F) F a)) =
      mixedEmbedding F (algebraMap (𝓞 F) F a) := fun a => toMixed_coord_algebraMap F _
  have hΛmem : ∀ g : Λ, ∃ a : 𝓞 F, (g : mixedEmbedding.mixedSpace F) =
      mixedEmbedding F (algebraMap (𝓞 F) F a) := by
    rintro ⟨_, a, rfl⟩
    exact ⟨a, rfl⟩
  have hΛmem' : ∀ a : 𝓞 F, mixedEmbedding F (algebraMap (𝓞 F) F a) ∈ Λ :=
    fun a => ⟨a, rfl⟩
  choose a ha using hΛmem
  let m : Λ → Γ := fun g => ⟨algebraMap F (Ainf F) (algebraMap (𝓞 F) F (a g)), ⟨a g, rfl⟩⟩
  have hmΨ : ∀ g : Λ, Ψ (m g : Ainf F) = g := fun g => by
    rw [ha g]; exact hΨalg _
  have hmbij : Function.Bijective m := by
    refine ⟨fun g g' h => ?_, ?_⟩
    · apply Subtype.ext
      rw [← hmΨ g, ← hmΨ g', h]
    · rintro ⟨_, b, rfl⟩
      refine ⟨⟨_, hΛmem' b⟩, Subtype.ext (hΨinj ?_)⟩
      rw [hmΨ]
      exact (hΨalg b).symm
  have hq : Measure.QuasiMeasurePreserving Ψ lam volume := by
    refine hmp.quasiMeasurePreserving.comp ⟨coord_measurable F, ?_⟩
    rw [hc]
    intro s hs
    simp [hs]
  have hFD : IsAddFundamentalDomain Γ (Ψ ⁻¹' P) lam :=
    (mixedEmbedding.fundamentalDomain_integerLattice F).preimage_of_equiv hq hmbij (fun g x => by
      change Ψ ((m g : Ainf F) + x) = (g : mixedEmbedding.mixedSpace F) + Ψ x
      rw [hΨadd, hmΨ])
  haveI : Countable Γ := hmbij.surjective.countable
  have h1 : lam (Ψ ⁻¹' P) = 1 := by
    rw [← hD1]
    exact hFD.measure_eq hD
  have hQm : MeasurableSet (toMixed F ⁻¹' P) := hmp.measurable hPm
  have h2 : (c : ℝ≥0∞) * volume (toMixed F ⁻¹' P) = 1 := by
    have := Measure.map_apply (μ := lam) (coord_measurable F) hQm
    rw [hc] at this
    have e : Ψ ⁻¹' P = coord F ⁻¹' (toMixed F ⁻¹' P) := rfl
    rw [← h1, e]
    simpa using this
  have h3 : volume (toMixed F ⁻¹' P) = ENNReal.ofReal (Real.sqrt |(discr F : ℝ)|) := by
    rw [hmp.measure_preimage hPm.nullMeasurableSet, hP, mixedEmbedding.volume_fundamentalDomain_latticeBasis,
      IsTotallyReal.nrComplexPlaces_eq_zero, pow_zero, one_mul,
      ← ENNReal.ofReal_coe_nnreal, Real.coe_sqrt, coe_nnnorm, Int.norm_eq_abs]
  have hd : 0 < Real.sqrt |(discr F : ℝ)| := by
    have : (discr F : ℝ) ≠ 0 := by exact_mod_cast discr_ne_zero F
    positivity
  rw [h3] at h2
  have h4 : (c : ℝ≥0∞) = ENNReal.ofReal (Real.sqrt |(discr F : ℝ)|)⁻¹ := by
    rw [ENNReal.ofReal_inv_of_pos hd]
    exact ENNReal.eq_inv_of_mul_eq_one_left h2
  rw [hc, ← h4]
  rfl
end GlobalTheory.CompanionTheory.SW.RealCoord
