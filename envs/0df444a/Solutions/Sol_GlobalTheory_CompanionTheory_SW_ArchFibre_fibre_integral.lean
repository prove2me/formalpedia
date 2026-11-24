-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.ArchFibre.fibre_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:14:01.634048+00:00
-- url     : https://prove2.me/submissions/b2070459-132e-42dc-9891-5c64060566c0

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_BinaryMassMeans_MeanVal
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_InfiniteAdelesLocalRingTotallyReal
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_CoordinateHaarMeasure
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_UnitsOpenEmbeddingLocalTensorStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianMatricesLocallyCompactBorel
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ArchimedeanBinaryGramDensity
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_ArchFibre_qR_hermScal
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_ArchFibre_hermScal_qR
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_ArchFibre_continuous_hermScal
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_ArchFibre_continuous_qR
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_ArchFibre_coordHerm_eq_map
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_ArchFibre_measurableEmbedding_hermScal
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_HermTop_herm_top
import Theorems.Thm_GlobalTheory_T_tensor_locally_compact_ring
import Theorems.Thm_GlobalTheory_T_units_open_embedding_local_tensor


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.Rg.Mass
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter
open scoped TensorProduct ENNReal NNReal
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.ArchFibre
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E}
namespace GlobalTheory.CompanionTheory.SW.ArchFibre
theorem _root_.solution (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R]
    [BorelSpace R] (hloc : IsLocR R) (h : IsCMExt F E σ) (hJ : IsHermND σ J)
    {d : ℕ} (b : Module.Basis (Fin d) F E) (lam : Measure R) (hlam : lam.IsAddHaarMeasure)
    (m : HermR R σ 1 → Measure (Fin 1 → Fin M → R ⊗[F] E))
    (hfib : IsGramFib R σ J 1 (coordW R b lam 1 M) (coordHerm R σ b lam 1) m)
    (φ : (Fin 1 → Fin M → R ⊗[F] E) → ℝ) (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (hφ0 : ∀ X, 0 ≤ φ X) (hφU : tsupport φ ⊆ {X | IsUnit (gramR R σ J X).det}) :
    Continuous (fun s : R => ∫ X, φ X ∂(m (hermScal R σ s))) ∧
    HasCompactSupport (fun s : R => ∫ X, φ X ∂(m (hermScal R σ s))) ∧
    (∀ s : R, ∫⁻ X, ENNReal.ofReal (φ X) ∂(m (hermScal R σ s)) =
      ENNReal.ofReal (∫ X, φ X ∂(m (hermScal R σ s)))) ∧
    ENNReal.ofReal (∫ s, (∫ X, φ X ∂(m (hermScal R σ s))) ∂lam) =
      ∫⁻ X, ENNReal.ofReal (φ X) ∂(coordW R b lam 1 M) := by
  obtain ⟨h1, h2, h3, h4, -⟩ := id hloc
  haveI := h1
  haveI := h2
  haveI := h3
  haveI := h4
  haveI := hlam
  obtain ⟨iTR, iLC, iSC, iT2, -, htr, -, iB, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ h R
  haveI := iB 1 M
  haveI := iTR
  haveI := iLC
  haveI := iSC
  haveI := iT2
  obtain ⟨jLC, jSC, jT2, jB, hlift⟩ := GlobalTheory.CompanionTheory.SW.HermTop.herm_top F E σ h R 1
  haveI := jB
  obtain ⟨g, hg, hgram⟩ := hlift M J hJ
  have hunits : IsOpenEmbedding (Units.val : (R ⊗[F] E)ˣ → R ⊗[F] E) := GlobalTheory.T.units_open_embedding_local_tensor F E σ h R hloc
  set B : Set (HermR R σ 1) := {S | IsUnit (S : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)).det} with hBdef
  set U : Set (Fin 1 → Fin M → R ⊗[F] E) := {X | IsUnit (gramR R σ J X).det} with hUdef
  have hB : IsOpen B := by
    have hdet : Continuous fun S : HermR R σ 1 => (S : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)).det :=
      Continuous.matrix_det continuous_subtype_val
    have hset : B = (fun S : HermR R σ 1 => (S : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)).det) ⁻¹'
        Set.range (Units.val : (R ⊗[F] E)ˣ → R ⊗[F] E) := by
      ext S
      simp [B, IsUnit]
    rw [hset]
    exact hunits.isOpen_range.preimage hdet
  have hUo : IsOpen U := by
    have hpre : U = g ⁻¹' B := by
      ext X
      simp [U, B, hgram X]
    rw [hpre]
    exact hB.preimage hg
  obtain ⟨hf1, hf2, hf3⟩ := hfib
  obtain ⟨hint, hcont⟩ := hf3 φ hφ hφc hφU
  have hcs : Continuous (hermScal R σ (F := F) (E := E)) := continuous_hermScal R
  set I : R → ℝ := fun s => ∫ X, φ X ∂(m (hermScal R σ s)) with hI
  set K : Set R := (fun X => qR R σ (g X)) '' tsupport φ with hKdef
  have hK : IsCompact K := hφc.isCompact.image ((continuous_qR R htr).comp hg)
  have hzero : ∀ s, s ∉ K → I s = 0 := by
    intro s hs
    refine integral_eq_zero_of_ae ?_
    filter_upwards [mem_ae_iff.mpr (hf1 (hermScal R σ s))] with X hX
    by_contra hne
    apply hs
    refine ⟨X, subset_tsupport _ (Function.mem_support.mpr hne), ?_⟩
    have e : g X = hermScal R σ s := Subtype.ext ((hgram X).symm.trans hX.1)
    show qR R σ (g X) = s
    rw [e, qR_hermScal R h]
  have hKB : ∀ s ∈ K, hermScal R σ s ∈ B := by
    rintro _ ⟨X, hX, rfl⟩
    have e : hermScal R σ (qR R σ (g X)) = g X := hermScal_qR R h (g X)
    show hermScal R σ (qR R σ (g X)) ∈ B
    rw [e]
    show IsUnit (g X : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)).det
    rw [← hgram X]
    exact hφU hX
  have hcontI : Continuous I := by
    rw [continuous_iff_continuousAt]
    intro s
    by_cases hs : s ∈ K
    · have hD : IsOpen (hermScal R σ ⁻¹' B) := hB.preimage hcs
      have hon : ContinuousOn I (hermScal R σ ⁻¹' B) :=
        hcont.comp hcs.continuousOn (fun _ hx => hx)
      exact hon.continuousAt (hD.mem_nhds (hKB s hs))
    · have hev : I =ᶠ[𝓝 s] fun _ => (0 : ℝ) :=
        Filter.eventually_of_mem (hK.isClosed.isOpen_compl.mem_nhds hs) fun t ht => hzero t ht
      exact continuousAt_const.congr hev.symm
  have hcsI : HasCompactSupport I := HasCompactSupport.intro hK hzero
  have hintAll : ∀ S, Integrable φ (m S) := by
    intro S
    by_cases hS : S ∈ B
    · exact hint S hS
    · have hu : (gramR R σ J ⁻¹' {(S : Matrix (Fin 1) (Fin 1) (R ⊗[F] E))} ∩ U)ᶜ = Set.univ := by
        rw [Set.compl_univ_iff, Set.eq_empty_iff_forall_notMem]
        rintro X ⟨hX1, hX2⟩
        apply hS
        show IsUnit (S : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)).det
        have hX1' : gramR R σ J X = (S : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) := hX1
        rw [← hX1']
        exact hX2
      have h0 : m S = 0 := by
        have := hf1 S
        rw [show (Subtype.val S) = (S : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) from rfl, hu] at this
        exact Measure.measure_univ_eq_zero.mp this
      rw [h0]
      exact integrable_zero_measure
  have hthird : ∀ s : R, ∫⁻ X, ENNReal.ofReal (φ X) ∂(m (hermScal R σ s)) = ENNReal.ofReal (I s) :=
    fun s => (ofReal_integral_eq_lintegral_ofReal (hintAll _) (Eventually.of_forall hφ0)).symm
  refine ⟨hcontI, hcsI, hthird, ?_⟩
  have hΦ : Measurable fun X => ENNReal.ofReal (φ X) := hφ.measurable.ennreal_ofReal
  have key := hf2 _ hΦ
  have hU : ∫⁻ X in U, ENNReal.ofReal (φ X) ∂(coordW R b lam 1 M) =
      ∫⁻ X, ENNReal.ofReal (φ X) ∂(coordW R b lam 1 M) := by
    rw [← lintegral_indicator hUo.measurableSet]
    congr 1
    refine Set.indicator_eq_self.mpr fun X hX => hφU (subset_tsupport _ ?_)
    intro h0
    apply hX
    simp [h0]
  rw [hU, coordHerm_eq_map R h htr b lam, (measurableEmbedding_hermScal R h htr).lintegral_map] at key
  rw [key, ofReal_integral_eq_lintegral_ofReal (hcontI.integrable_of_hasCompactSupport hcsI)
    (Eventually.of_forall fun s => integral_nonneg fun X => hφ0 X)]
  exact lintegral_congr fun s => (hthird s).symm
end GlobalTheory.CompanionTheory.SW.ArchFibre
