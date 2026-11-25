-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.LocGauss.fibre_rapid_eq_density
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:26:02.654847+00:00
-- url     : https://prove2.me/submissions/ac7e2ce0-17e8-42bb-a0cf-f3b5f7505eec

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ContinuousDensitiesEqOfIntegralsOnCompacts
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_DisintegrationDensityUnique
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramRightActionIdentities
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianMatricesLocallyCompactBorel
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ExistsSizeMulLe
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_InfiniteAdelesLocalRingTotallyRealStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_UnitsOpenEmbeddingLocalTensorStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberMeasuresIntegralFormulaStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianLocalContinuousCongruenceSectionStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_SizeFunctionRapidDecayIntegrableStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ArchimedeanGramFiberContinuousDensity
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_LocGauss_fibre_lintegral_eq_density
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_LocGauss_ofReal_inv_pow_le
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_GramAlg_gram_algebra
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_HermTop_herm_top
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_bd_succ_succ
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_bd_succ_zero
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_bd_zero_succ
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_bd_zero_zero
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_uni_succ_succ
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_uni_succ_zero
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_uni_zero_succ
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_uni_zero_zero
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_SizeScale_size_rmul_le
import Theorems.Thm_GlobalTheory_T_gram_fiber_measures_gl_equivariant
import Theorems.Thm_GlobalTheory_T_hermitian_local_continuous_congruence_section
import Theorems.Thm_GlobalTheory_T_infinite_adeles_local_ring_totally_real
import Theorems.Thm_GlobalTheory_T_size_function_rapid_decay_integrable
import Theorems.Thm_GlobalTheory_T_tensor_locally_compact_ring
import Theorems.Thm_GlobalTheory_T_units_open_embedding_local_tensor
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CompanionTheory.SW.RingDiag.bd_succ_succ
attribute [local simp] GlobalTheory.CompanionTheory.SW.RingDiag.bd_succ_zero
attribute [local simp] GlobalTheory.CompanionTheory.SW.RingDiag.bd_zero_succ
attribute [local simp] GlobalTheory.CompanionTheory.SW.RingDiag.bd_zero_zero
attribute [local simp] GlobalTheory.CompanionTheory.SW.RingDiag.uni_succ_succ
attribute [local simp] GlobalTheory.CompanionTheory.SW.RingDiag.uni_succ_zero
attribute [local simp] GlobalTheory.CompanionTheory.SW.RingDiag.uni_zero_succ
attribute [local simp] GlobalTheory.CompanionTheory.SW.RingDiag.uni_zero_zero



set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.LocGauss
set_option maxHeartbeats 400000
namespace GlobalTheory.CompanionTheory.SW.LocGauss
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (μ : Measure (Fin 1 → Fin M → Ainf F ⊗[F] E)) (ν : Measure (HermR (Ainf F) σ 1)) m, μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → IsGramFib (Ainf F) σ J 1 μ ν m → ∀ φ : (Fin 1 → Fin M → Ainf F ⊗[F] E) → ℝ, Continuous φ → (∀ X, 0 ≤ φ X) → RapidDecay b (fun X => (φ X : ℂ)) → ∀ D : HermR (Ainf F) σ 1 → ℝ, Continuous D → (∀ U : Set (HermR (Ainf F) σ 1), MeasurableSet U → ∫⁻ X in gramR (Ainf F) σ J ⁻¹' (Subtype.val '' U), ENNReal.ofReal (φ X) ∂μ = ∫⁻ S in U, ENNReal.ofReal (D S) ∂ν) → ∀ S : HermR (Ainf F) σ 1, IsUnit (S : Matrix (Fin 1) (Fin 1) (Ainf F ⊗[F] E)).det → ∫⁻ X, ENNReal.ofReal (φ X) ∂(m S) = ENNReal.ofReal (D S) := by
  intro F E _ _ _ _ _ σ hσ M J hJ d b μ ν m hμ hν hfib φ hφc hφ0 hφr D hDc hD S hS
  have hLoc : IsLocR (Ainf F) := GlobalTheory.T.infinite_adeles_local_ring_totally_real F hσ.1
  obtain ⟨hTR, hLC, hSC, hT2, -, -, -, -⟩ := id hLoc
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  obtain ⟨hKr, hKl, hKs, hK2, -, -, -, hVb, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hσ (Ainf F)
  haveI := hKr
  haveI := hKl
  haveI := hKs
  haveI := hK2
  haveI := hVb 1 M
  obtain ⟨hXl, hXs, hX2, hXb, hlift⟩ := GlobalTheory.CompanionTheory.SW.HermTop.herm_top F E σ hσ (Ainf F) 1
  haveI := hXl
  haveI := hXs
  haveI := hX2
  haveI := hXb
  obtain ⟨g, hgc, hgf⟩ := hlift M J hJ
  have hKU := GlobalTheory.T.units_open_embedding_local_tensor F E σ hσ (Ainf F) hLoc

  set B : Set (HermR (Ainf F) σ 1) :=
    {S | IsUnit (S : Matrix (Fin 1) (Fin 1) (Ainf F ⊗[F] E)).det} with hBdef
  have hB : IsOpen B := by
    have hdet : Continuous fun S : HermR (Ainf F) σ 1 =>
        (S : Matrix (Fin 1) (Fin 1) (Ainf F ⊗[F] E)).det :=
      Continuous.matrix_det continuous_subtype_val
    have : B = (fun S : HermR (Ainf F) σ 1 =>
        (S : Matrix (Fin 1) (Fin 1) (Ainf F ⊗[F] E)).det) ⁻¹' Set.range Units.val := by
      ext S
      simp [hBdef, IsUnit]
    rw [this]
    exact hKU.isOpen_range.preimage hdet
  have hfib' : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ (gramR (Ainf F) σ J) Subtype.val (g ⁻¹' B) ν B m := by
    have e : g ⁻¹' B = {X | IsUnit (gramR (Ainf F) σ J X).det} := by
      ext X
      simp [hBdef, hgf]
    rw [e]
    exact hfib
  obtain ⟨B₁, s, hB₁, hSB₁, hsc, hs1, hsS⟩ := GlobalTheory.T.hermitian_local_continuous_congruence_section F E σ hσ (Ainf F) hLoc 1 S hS
  obtain ⟨κ, hκc, hκ0, -, hκ⟩ := GlobalTheory.T.gram_fiber_measures_gl_equivariant F E σ hσ M J hJ (Ainf F) hLoc 1 μ ν m hμ hν hfib
  obtain ⟨-, hsz0, N, hN⟩ := GlobalTheory.T.size_function_rapid_decay_integrable F E σ hσ d b 1 M μ hμ
  have hszc : Continuous (sizeTup b : (Fin 1 → Fin M → Ainf F ⊗[F] E) → ℝ) :=
    (GlobalTheory.T.size_function_rapid_decay_integrable F E σ hσ d b 1 M μ hμ).1
  obtain ⟨hg1, hg2, hg3, -, -⟩ := GlobalTheory.CompanionTheory.SW.GramAlg.gram_algebra F E σ hσ M J hJ (Ainf F) 1
  set w : (Fin 1 → Fin M → Ainf F ⊗[F] E) → ℝ≥0∞ :=
    fun X => ENNReal.ofReal (((1 + sizeTup b X) ^ N)⁻¹) with hw
  have hwm : Measurable w := by
    refine ENNReal.measurable_ofReal.comp (Continuous.measurable ?_)
    refine Continuous.inv₀ ((continuous_const.add hszc).pow N) fun X => ?_
    have := hsz0 X
    positivity
  obtain ⟨C₀, hC₀⟩ := hφr N
  have huw : ∀ X, ENNReal.ofReal (φ X) ≤ (C₀.toNNReal : ℝ≥0∞) * w X := by
    intro X
    have h1 : 0 < (1 + sizeTup b X) ^ N := by
      have := hsz0 X
      positivity
    have h2 := hC₀ X
    rw [Complex.norm_real, Real.norm_of_nonneg (hφ0 X)] at h2
    have h3 : φ X ≤ C₀.toNNReal * ((1 + sizeTup b X) ^ N)⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ h1]
      exact h2.trans (Real.le_coe_toNNReal _)
    calc ENNReal.ofReal (φ X) ≤ ENNReal.ofReal (C₀.toNNReal * ((1 + sizeTup b X) ^ N)⁻¹) :=
          ENNReal.ofReal_le_ofReal h3
      _ = _ := by
        rw [ENNReal.ofReal_mul (NNReal.coe_nonneg _), ENNReal.ofReal_coe_nnreal]
  have hrmulc : Continuous fun q : (Fin 1 → Fin M → Ainf F ⊗[F] E) ×
      Matrix (Fin 1) (Fin 1) (Ainf F ⊗[F] E) => rmul (Ainf F) q.1 q.2 := by
    refine continuous_pi fun a => continuous_pi fun i => ?_
    refine continuous_finset_sum _ fun c _ => ?_
    refine Continuous.mul ?_ ?_
    · exact (continuous_apply i).comp ((continuous_apply c).comp continuous_fst)
    · exact continuous_snd.matrix_elem c a
  have hvalc : ContinuousOn (fun S' => ((s S' : GL (Fin 1) (Ainf F ⊗[F] E)) :
      Matrix (Fin 1) (Fin 1) (Ainf F ⊗[F] E))) B₁ := Units.continuous_val.comp_continuousOn hsc
  have hinvc : ContinuousOn (fun S' => (((s S')⁻¹ : GL (Fin 1) (Ainf F ⊗[F] E)) :
      Matrix (Fin 1) (Fin 1) (Ainf F ⊗[F] E))) B₁ :=
    Units.continuous_val.comp_continuousOn (continuous_inv.comp_continuousOn hsc)
  refine fibre_lintegral_eq_density μ ν (gramR (Ainf F) σ J) g Subtype.val Subtype.val_injective
    hgc hgf B m hfib' S (B₁ ∩ B) (hB₁.inter hB) Set.inter_subset_right ⟨hSB₁, hS⟩
    (fun S' X => rmul (Ainf F) X (s S' : GL (Fin 1) (Ainf F ⊗[F] E)))
    (fun S' => κ (s S')) ?_ ?_ ?_ ?_ w (fun X => ENNReal.ofReal (φ X)) hwm
    (ENNReal.continuous_ofReal.comp hφc) hN C₀.toNNReal huw ?_
    (fun S' => ENNReal.ofReal (D S')) (ENNReal.continuous_ofReal.comp hDc).continuousOn ?_
  · refine hrmulc.comp_continuousOn (continuous_snd.continuousOn.prodMk ?_)
    exact hvalc.comp (continuous_fst.continuousOn) fun p hp => hp.1.1
  · exact hκc.comp_continuousOn (hsc.mono Set.inter_subset_left)
  · exact fun S' _ => hκ0 _
  · exact fun S' hS' => hκ _ S S' (hsS S' hS'.1)
  · intro L hL hLO
    have hLB₁ : L ⊆ B₁ := hLO.trans Set.inter_subset_left
    have hC : IsCompact ((fun S' => ((s S' : GL (Fin 1) (Ainf F ⊗[F] E)) :
        Matrix (Fin 1) (Fin 1) (Ainf F ⊗[F] E))) '' L ∪
        (fun S' => (((s S')⁻¹ : GL (Fin 1) (Ainf F ⊗[F] E)) :
        Matrix (Fin 1) (Fin 1) (Ainf F ⊗[F] E))) '' L) :=
      (hL.image_of_continuousOn (hvalc.mono hLB₁)).union
        (hL.image_of_continuousOn (hinvc.mono hLB₁))
    obtain ⟨c, hc0, hc⟩ := GlobalTheory.CompanionTheory.SW.SizeScale.size_rmul_le F E σ hσ d b 1 M _ hC
    have h1c : ∀ X Y : Fin 1 → Fin M → Ainf F ⊗[F] E, sizeTup b Y ≤ c * sizeTup b X →
        1 + sizeTup b Y ≤ max c 1 * (1 + sizeTup b X) := by
      intro X Y h
      have hX := hsz0 X
      have h1 : c ≤ max c 1 := le_max_left _ _
      have h2 : 1 ≤ max c 1 := le_max_right _ _
      nlinarith
    refine ⟨((max c 1) ^ N).toNNReal, fun S' hS' X => ?_⟩
    have hup := hc _ (Or.inl ⟨S', hS', rfl⟩) X
    have hdown := hc _ (Or.inr ⟨S', hS', rfl⟩)
      (rmul (Ainf F) X (s S' : GL (Fin 1) (Ainf F ⊗[F] E)))
    have hcancel : rmul (Ainf F) (rmul (Ainf F) X (s S' : GL (Fin 1) (Ainf F ⊗[F] E)))
        (((s S')⁻¹ : GL (Fin 1) (Ainf F ⊗[F] E)) : Matrix (Fin 1) (Fin 1) (Ainf F ⊗[F] E)) = X := by
      rw [hg2, ← Units.val_mul, mul_inv_cancel, Units.val_one, hg3]
    rw [hcancel] at hdown
    have p1 : 0 < 1 + sizeTup b X := by
      have := hsz0 X
      positivity
    have p2 : 0 < 1 + sizeTup b (rmul (Ainf F) X (s S' : GL (Fin 1) (Ainf F ⊗[F] E))) := by
      have := hsz0 (rmul (Ainf F) X (s S' : GL (Fin 1) (Ainf F ⊗[F] E)))
      positivity
    have hm0 : 0 ≤ max c 1 := hc0.le.trans (le_max_left _ _)
    exact ⟨ofReal_inv_pow_le p1 p2 hm0 (h1c _ _ hdown) N,
      ofReal_inv_pow_le p2 p1 hm0 (h1c _ _ hup) N⟩
  · intro L hL hLO
    have e : gramR (Ainf F) σ J ⁻¹' (Subtype.val '' L) = g ⁻¹' L := by
      ext X
      simp only [Set.mem_preimage, Set.mem_image, hgf]
      constructor
      · rintro ⟨x, hx, hxv⟩
        exact Subtype.val_injective hxv ▸ hx
      · exact fun hv => ⟨g X, hv, rfl⟩
    rw [← e]
    exact hD L hL.measurableSet
end GlobalTheory.CompanionTheory.SW.LocGauss
