-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.NullV.null_nonunits
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:00:57.445703+00:00
-- url     : https://prove2.me/submissions/590eb392-3b23-43ed-af3e-53f2389471e6

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianNondegRepresentsNonzeroScalar
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_CompletionIsLocalRing
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRing
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_HaarMeasureNonunitsNull
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_NullV_null_of_overlap
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_NullV_card_le_two
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_NullV_qR_line
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_NullV_qR_rat
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_NullV_nhdsNE_Fv
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_NullV_exists_seq_Fv
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_HermRep_exists_repr
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_LocFv_isLocR_Fv
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_TopK_topTens_props
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
noncomputable section
open scoped Pointwise
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.NullV
namespace GlobalTheory.CompanionTheory.SW.NullV
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 1 ≤ M → ∀ (v : HeightOneSpectrum (𝓞 F)) (μ : Measure (Fin 1 → Fin M → Fv F v ⊗[F] E)) (ν : Measure (Fv F v)), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → ν {c | ¬ IsUnit c} = 0 ∧ μ {X | ¬ IsUnit ((fun X : Fin 1 → Fin M → Fv F v ⊗[F] E => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR (Fv F v) σ J (X 0)) X)} = 0 := by
  intro F E _ _ _ _ _ σ hσ M J hJ hM v μ ν hμ hν
  obtain ⟨h1, h2, h3, h4, -⟩ := GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
  haveI := h1
  haveI := h2
  haveI := h3
  haveI := h4
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  haveI : (𝓝[≠] (0 : Fv F v)).NeBot := nhdsNE_Fv F v
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ (Fv F v)
  haveI := a1
  haveI := a2
  haveI := a3
  haveI := a4
  haveI := a8 1 M
  constructor
  · have : {c : Fv F v | ¬ IsUnit c} = {0} := by
      ext c
      simp [isUnit_iff_ne_zero]
    rw [this]
    exact measure_singleton 0
  · obtain ⟨n, rfl⟩ : ∃ n, M = n + 1 := ⟨M - 1, by omega⟩
    obtain ⟨β, y, hβ, hy⟩ := GlobalTheory.CompanionTheory.SW.HermRep.exists_repr F E σ hσ n J hJ
    haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
    have b : Module.Basis (Fin 2) F E := Module.finBasisOfFinrankEq F E hσ.2.2.1
    haveI := GlobalTheory.CompanionTheory.SW.TopK.isModTop (F := F) (E := E) (Fv F v)
    haveI : ContinuousSMul (Fv F v) (Fv F v ⊗[F] E) := IsModuleTopology.toContinuousSMul (Fv F v) _
    obtain ⟨t, ht, htt⟩ := exists_seq_Fv F v
    let w : Fin (n + 1) → Fv F v ⊗[F] E := fun j => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (Fv F v) (y j)
    have hq : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR (Fv F v) σ J w = algebraMap F (Fv F v) β :=
      qR_rat (Fv F v) σ J b y β hy
    have hq0 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR (Fv F v) σ J w ≠ 0 := by
      rw [hq]
      exact (map_ne_zero _).2 hβ
    let φ : Fv F v → (Fin 1 → Fin (n + 1) → Fv F v ⊗[F] E) :=
      fun c _ j => algebraMap (Fv F v) (Fv F v ⊗[F] E) c * w j
    have hφ : Continuous φ := by
      refine continuous_pi fun _ => continuous_pi fun j => ?_
      exact (continuous_algebraMap (Fv F v) (Fv F v ⊗[F] E)).mul continuous_const
    have hφ0 : φ 0 = 0 := by
      funext _ j
      simp [φ]
    have hu : Filter.Tendsto (fun i => φ (t i)) Filter.atTop (𝓝 0) := by
      have := (hφ.tendsto 0).comp htt
      rwa [hφ0] at this
    have hQ : Continuous fun X : Fin 1 → Fin (n + 1) → Fv F v ⊗[F] E =>
        Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR (Fv F v) σ J (X 0) := by
      have : Continuous fun X : Fin 1 → Fin (n + 1) → Fv F v ⊗[F] E =>
          HeckeCharacterZeroLocus.SiegelWeilU.gramR (Fv F v) σ J X 0 0 := (a10 1 (n + 1) J).matrix_elem 0 0
      exact continuous_const.mul (a6.comp this)
    have hZ : MeasurableSet {X : Fin 1 → Fin (n + 1) → Fv F v ⊗[F] E |
        ¬ IsUnit (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR (Fv F v) σ J (X 0))} := by
      have : {X : Fin 1 → Fin (n + 1) → Fv F v ⊗[F] E |
          ¬ IsUnit (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR (Fv F v) σ J (X 0))} =
          (fun X : Fin 1 → Fin (n + 1) → Fv F v ⊗[F] E =>
            Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR (Fv F v) σ J (X 0)) ⁻¹' {0} := by
        ext X
        simp [isUnit_iff_ne_zero]
      rw [this]
      exact (isClosed_singleton.preimage hQ).measurableSet
    refine null_of_overlap μ hZ (fun i => φ (t i)) hu ?_
    intro X s hs
    refine card_le_two (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR (Fv F v) σ J (X 0))
      (algebraMap F (Fv F v) (1 / 2) * Algebra.trace (Fv F v) (Fv F v ⊗[F] E)
        (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hR (Fv F v) σ J (X 0) w + Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hR (Fv F v) σ J w (X 0)))
      (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR (Fv F v) σ J w) hq0 (fun i => - t i)
      (fun i j e => ht (neg_injective e)) s ?_
    intro i hi
    have h := hs i hi
    have h' : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR (Fv F v) σ J ((X - φ (t i)) 0) = 0 := by
      by_contra hne
      exact h (isUnit_iff_ne_zero.2 hne)
    have e : (X - φ (t i)) 0 = fun j => X 0 j + algebraMap (Fv F v) (Fv F v ⊗[F] E) (- t i) * w j := by
      funext j
      change X 0 j - algebraMap (Fv F v) (Fv F v ⊗[F] E) (t i) * w j = _
      rw [map_neg, neg_mul, sub_eq_add_neg]
    rw [e, qR_line] at h'
    exact h'
end GlobalTheory.CompanionTheory.SW.NullV
