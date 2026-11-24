-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.isFibreFamily_length
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:30:08.233631+00:00
-- url     : https://prove2.me/submissions/998bdeca-f115-4561-b1a0-c2ebfe929ebb

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ContinuousHermScal
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRing
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IsFibreFamilyLength
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_LenFib_qR_of_gram
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_LenFib_isUnit_det_hermScal
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_LenFib_isUnit_det_gramR
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_LenFib_continuous_qR
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_LenFib_exists_bump

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
open GlobalTheory.CompanionTheory.SW.LenFib
namespace GlobalTheory.CompanionTheory.SW
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (μ : Measure (Fin 1 → Fin M → R ⊗[F] E)) (ν : Measure R), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → ν {c | ¬ IsUnit c} = 0 → μ {X | ¬ IsUnit ((fun X : Fin 1 → Fin M → R ⊗[F] E => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR (R) σ J (X 0)) X)} = 0 → ∀ m, IsGramFib R σ J 1 μ (ν.map (hermScal R σ)) m → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ (fun X : Fin 1 → Fin M → R ⊗[F] E => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR (R) σ J (X 0)) id Set.univ ν {c | IsUnit c} (fun c => m (hermScal R σ c)) := by
  intro F E _ _ _ _ _ σ hσ M J hJ R _ _ _ _ _ hLoc μ ν _ _ _ hμ0 m hm
  obtain ⟨hTR, hLC, hSC, hT2, -, -, hOE, -⟩ := hLoc
  haveI := hTR
  haveI := hLC
  haveI := hSC
  haveI := hT2
  haveI : BorelSpace (HermR R σ 1) := ⟨rfl⟩
  obtain ⟨hfib, hint, hcont⟩ := hm
  set q : (Fin 1 → Fin M → R ⊗[F] E) → R := fun X => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR R σ J (X 0) with hq
  have hqc : Continuous q := continuous_qR R hσ J
  have hUo : IsOpen {c : R | IsUnit c} := by
    have h := hOE.isOpen_range
    have he : Set.range (Units.val : Rˣ → R) = {c : R | IsUnit c} := by
      ext c
      exact Iff.rfl
    rwa [he] at h
  have hemb : MeasurableEmbedding (hermScal R σ) := (OneHerm.hermHomeo R hσ).measurableEmbedding
  have hsub : ∀ X, IsUnit (q X) → IsUnit (gramR R σ J X).det := fun X h =>
    isUnit_det_gramR R hσ hJ h
  have hres : μ.restrict {X | IsUnit (gramR R σ J X).det} = μ := by
    refine Measure.restrict_eq_self_of_ae_mem ?_
    refine measure_mono_null ?_ hμ0
    intro X hX hXq
    exact hX (hsub X hXq)
  have hae : ∀ c, ∀ᵐ X ∂(m (hermScal R σ c)), q X = c := by
    intro c
    refine measure_mono_null ?_ (hfib (hermScal R σ c))
    intro X hX hXm
    exact hX (qR_of_gram R hσ hJ hXm.1)
  refine ⟨?_, ?_, ?_⟩
  · intro c
    refine measure_mono_null ?_ (hae c)
    intro X hX hXq
    exact hX ⟨hXq, Set.mem_univ X⟩
  · intro φ hφ
    have h := hint φ hφ
    rw [hres, hemb.lintegral_map] at h
    rw [Measure.restrict_univ, h]
  · intro φ hφc hφs _
    have key : ∀ c₀, IsUnit c₀ → Integrable φ (m (hermScal R σ c₀)) ∧
        ContinuousWithinAt (fun c => ∫ v, φ v ∂(m (hermScal R σ c))) {c | IsUnit c} c₀ := by
      intro c₀ hc₀
      obtain ⟨χ, hχc, hχs, hχ1⟩ := exists_bump R hUo hc₀
      have hφ'c : Continuous fun X => φ X * χ (q X) := hφc.mul (hχc.comp hqc)
      have hφ's : HasCompactSupport fun X => φ X * χ (q X) := HasCompactSupport.mul_right hφs
      have hφ't : tsupport (fun X => φ X * χ (q X)) ⊆ {X | IsUnit (gramR R σ J X).det} := by
        intro X hX
        have h1 : X ∈ tsupport (χ ∘ q) := tsupport_mul_subset_right hX
        exact hsub X (hχs (tsupport_comp_subset_preimage χ hqc h1))
      obtain ⟨hI, hC⟩ := hcont _ hφ'c hφ's hφ't
      have heq : ∀ c, χ c = 1 → (fun X => φ X * χ (q X)) =ᵐ[m (hermScal R σ c)] φ := by
        intro c hc
        filter_upwards [hae c] with X hX
        rw [hX, hc, mul_one]
      have hmaps : Set.MapsTo (hermScal R σ) {c : R | IsUnit c}
          {S : HermR R σ 1 | IsUnit (S : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)).det} :=
        fun c hc => isUnit_det_hermScal R σ hc
      have hC' : ContinuousOn (fun c => ∫ v, φ v * χ (q v) ∂(m (hermScal R σ c))) {c | IsUnit c} :=
        hC.comp (OneHerm.continuous_hermScal R σ).continuousOn hmaps
      refine ⟨(hI _ (hmaps hc₀)).congr (heq c₀ hχ1.self_of_nhds), ?_⟩
      refine (hC' c₀ hc₀).congr_of_eventuallyEq ?_ ?_
      · filter_upwards [mem_nhdsWithin_of_mem_nhds hχ1] with c hc
        exact (integral_congr_ae (heq c hc)).symm
      · exact (integral_congr_ae (heq c₀ hχ1.self_of_nhds)).symm
    exact ⟨fun c hc => (key c hc).1, fun c hc => (key c hc).2⟩
end GlobalTheory.CompanionTheory.SW
