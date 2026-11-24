-- Prove2me | solution 1 for GlobalTheory.JR.WeilQuad.GaussTrans.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:19:57.913064+00:00
-- url     : https://prove2.me/submissions/0e30f64a-a3e8-4dba-90ac-ad0333eda59f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsStableGauss
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NonemptyMeasAndReps
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_StableQuadraticGaussIntegralMulNorm
import Theorems.Thm_GlobalTheory_JR_EtMeas_absK_unit
import Theorems.Thm_GlobalTheory_JR_EtMeas_finite_L
import Theorems.Thm_GlobalTheory_JR_EtMeas_top_facts
import Theorems.Thm_GlobalTheory_JR_Et_quadratic_structure
import Theorems.Thm_GlobalTheory_JR_ModuleNorm_distribHaarChar_eq_norm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology
open scoped Pointwise ENNReal NNReal
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.WeilQuad GlobalTheory.JR.WeilQuad.GaussTrans
namespace GlobalTheory.JR.WeilQuad.GaussTrans
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.Kˣ) (μ : Measure A.L) (ω : A.K → ℂ), Hyp A ψ x μ ω → ∀ (t s : A.Kˣ), (∃ ℓ : A.L, A.NL ℓ = s) → ∀ G : ℂ, IsStableGauss A ψ x μ t G → IsStableGauss A ψ x μ ((t * s : A.Kˣ) : A.K) (G * ((A.absK s : ℂ))⁻¹) := by
  intro F E _ _ _ _ U A ψ x μ ω hH t s ⟨ℓ, hℓ⟩ G ⟨Λ₀, ho₀, hc₀, hG⟩
  have := U.charZero; have := U.ultraF; have := U.lcF
  have : ProperSpace F := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace F
  have := EtMeas.finite_L A
  obtain ⟨⟨b⟩, hinj, hN, -, -⟩ := GlobalTheory.JR.Et.quadratic_structure F E A
  obtain ⟨_, _, _, _, -⟩ := EtMeas.top_facts F A.K
  obtain ⟨_, _, _, _, -⟩ := EtMeas.top_facts F A.L
  have : IsTopologicalRing A.L := IsModuleTopology.isTopologicalRing F A.L
  have : ContinuousStar A.L := ⟨IsModuleTopology.continuous_of_linearMap (EtMeas.starF A)⟩
  have hμ : μ.IsAddHaarMeasure := hH.2.2.2.1.1
  have hs' : algebraMap A.K A.L (s : A.K) = ℓ * star ℓ := by rw [← hℓ, hN]
  have hu : IsUnit ℓ := isUnit_of_mul_isUnit_left (hs' ▸ (s.isUnit.map (algebraMap A.K A.L)))
  set u : A.Lˣ := hu.unit with hu_def
  have hul : (u : A.L) = ℓ := hu.unit_spec
  have hmod : distribHaarChar A.L u = distribHaarChar A.K s :=
    GlobalTheory.JR.ModuleNorm.distribHaarChar_eq_norm A.K A.L b.equivFun.symm
      (IsModuleTopology.continuous_of_linearMap (b.equivFun.symm.toLinearMap.restrictScalars F))
      (IsModuleTopology.continuous_of_linearMap (b.equivFun.toLinearMap.restrictScalars F)) u s
      (by rw [hul]; exact hs')
  have hmap : μ.map (fun y => u • y) = (distribHaarChar A.L u⁻¹ : ℝ≥0∞) • μ := by
    ext S hS
    rw [Measure.map_apply (measurable_const_smul u) hS, Set.preimage_smul, Measure.smul_apply, smul_eq_mul,
      distribHaarChar_mul]
  have hemb : MeasurableEmbedding (fun y : A.L => u • y) :=
    (Homeomorph.smul u).measurableEmbedding
  have key : ∀ Λ : AddSubgroup A.L, gaussInt A ψ x μ ((t * s : A.Kˣ) : A.K) Λ =
      ((A.absK s : ℂ))⁻¹ * gaussInt A ψ x μ t (u • Λ : AddSubgroup A.L) := by
    intro Λ
    have h1 : gaussInt A ψ x μ ((t * s : A.Kˣ) : A.K) Λ =
        ∫ y in (Λ : Set A.L), A.psiK ψ ((t : A.K) * x * A.NL (u • y)) ∂μ := by
      unfold gaussInt
      refine integral_congr_ae (Eventually.of_forall fun y => ?_)
      have hNm : A.NL (u • y) = s * A.NL y := by
        rw [Units.smul_def, hul, smul_eq_mul]
        unfold Et.NL
        rw [map_mul]
        exact congrArg (· * _) hℓ
      simp only
      rw [hNm]
      push_cast; ring_nf
    have h2 := hemb.setIntegral_map (μ := μ) (fun z => A.psiK ψ ((t : A.K) * x * A.NL z)) ((u • Λ : AddSubgroup A.L) : Set A.L)
    have hpre : (fun y => u • y) ⁻¹' ((u • Λ : AddSubgroup A.L) : Set A.L) = Λ := by
      ext y
      simp only [Set.mem_preimage, SetLike.mem_coe]
      exact ⟨fun h => by simpa using (AddSubgroup.mem_pointwise_smul_iff_inv_smul_mem.1 h),
        fun h => AddSubgroup.smul_mem_pointwise_smul _ _ _ h⟩
    rw [hpre, hmap, Measure.restrict_smul, integral_smul_measure] at h2
    rw [h1, ← h2]
    unfold gaussInt
    rw [Complex.real_smul, EtMeas.absK_unit, ENNReal.coe_toReal, map_inv, hmod]
    congr 1
    push_cast
    rfl
  have hcoe : ∀ (v : A.Lˣ) (M : AddSubgroup A.L), ((v • M : AddSubgroup A.L) : Set A.L) = v • (M : Set A.L) :=
    fun v M => AddSubgroup.coe_pointwise_smul v M
  refine ⟨u⁻¹ • Λ₀, ?_, ?_, fun Λ hoΛ hcΛ hle => ?_⟩
  · rw [hcoe]; exact ho₀.smul _
  · rw [hcoe]; exact hc₀.smul _
  · rw [key, hG (u • Λ) (by rw [hcoe]; exact hoΛ.smul _) (by rw [hcoe]; exact hcΛ.smul _) ?_, mul_comm]
    intro z hz
    have : u⁻¹ • z ∈ Λ := hle (AddSubgroup.smul_mem_pointwise_smul _ _ _ hz)
    exact AddSubgroup.mem_pointwise_smul_iff_inv_smul_mem.2 this
end GlobalTheory.JR.WeilQuad.GaussTrans
