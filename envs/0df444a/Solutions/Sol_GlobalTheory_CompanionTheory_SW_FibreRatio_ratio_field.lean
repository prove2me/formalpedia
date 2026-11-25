-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.FibreRatio.ratio_field
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:54:33.022775+00:00
-- url     : https://prove2.me/submissions/39eb6966-f05f-462c-b32f-a8e8dfcb0144

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_CompletionIsLocalRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_CoordinateHaarMeasureStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberMeasuresContinuityStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberMeasuresTransitivityStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_LocalGramFiberRankOneSetFormula
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_FibreRatio_hermScal_qS
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_FibreRatio_isUnit_tmul
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_FibreRatio_continuous_hermScal
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_FibreRatio_continuous_qS
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_FibreRatio_coordHerm_qS
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_FibreRatio_mass_eq_lintegral
import Theorems.Thm_Formalism_FrobeniusOrbits_Final_real
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_FibreFam_BumpFamily_lt_top
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_bd_succ_succ
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_bd_succ_zero
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_bd_zero_succ
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_bd_zero_zero
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_uni_succ_succ
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_uni_succ_zero
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_uni_zero_succ
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_uni_zero_zero
import Theorems.Thm_GlobalTheory_T_coordinate_haar_measure
import Theorems.Thm_GlobalTheory_T_gram_fiber_integral_isContDensityOn
import Theorems.Thm_GlobalTheory_T_gram_fiber_measure_locallyFinite_and_ne_zero_of_isOpen
import Theorems.Thm_GlobalTheory_T_tensor_locally_compact_ring
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
attribute [local simp] GlobalTheory.CompanionTheory.SW.RingDiag.bd_succ_succ
attribute [local simp] GlobalTheory.CompanionTheory.SW.RingDiag.bd_succ_zero
attribute [local simp] GlobalTheory.CompanionTheory.SW.RingDiag.bd_zero_succ
attribute [local simp] GlobalTheory.CompanionTheory.SW.RingDiag.bd_zero_zero
attribute [local simp] GlobalTheory.CompanionTheory.SW.RingDiag.uni_succ_succ
attribute [local simp] GlobalTheory.CompanionTheory.SW.RingDiag.uni_succ_zero
attribute [local simp] GlobalTheory.CompanionTheory.SW.RingDiag.uni_zero_succ
attribute [local simp] GlobalTheory.CompanionTheory.SW.RingDiag.uni_zero_zero



set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.FibreRatio
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E}
namespace GlobalTheory.CompanionTheory.SW.FibreRatio
theorem _root_.solution (R : Type) [Field R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R]
    [BorelSpace R] (hloc : IsLocR R) (h : IsCMExt F E σ) (hJ : IsHermND σ J)
    {d : ℕ} (b : Module.Basis (Fin d) F E) (lam : Measure R) (hlam : lam.IsAddHaarMeasure)
    (m : HermR R σ 1 → Measure (Fin 1 → Fin M → R ⊗[F] E))
    (hfib : IsGramFib R σ J 1 (coordW R b lam 1 M) (coordHerm R σ b lam 1) m)
    (A : Set (Fin 1 → Fin M → R ⊗[F] E)) (hAc : IsCompact A) (hAo : IsOpen A)
    (s : R) (hs : s ≠ 0) (ε : ℝ) (hε : 0 < ε) :
    ∃ U ∈ 𝓝 s, ∀ V : Set R, MeasurableSet V → V ⊆ U →
      |(coordW R b lam 1 M (A ∩ {X | algebraMap F R (1 / 2) *
          Algebra.trace R (R ⊗[F] E) (gramR R σ J X 0 0) ∈ V})).toReal -
        (m (hermScal R σ s) A).toReal * (lam V).toReal| ≤ ε * (lam V).toReal := by
  obtain ⟨h1, h2, h3, h4, -⟩ := id hloc
  haveI := h1
  haveI := h2
  haveI := h3
  haveI := h4
  obtain ⟨-, -, -, hT2, -, htr, -, hBor, -, hgr⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ h R
  haveI := hT2
  haveI := hBor 1 M
  haveI : BorelSpace (HermR R σ 1) := ⟨rfl⟩
  have hHaar := GlobalTheory.T.coordinate_haar_measure F E σ h R d b lam hlam
  have hμ := hHaar.2.1 1 M
  have hν := hHaar.2.2 1
  have hAm : MeasurableSet A := hAo.measurableSet
  set φ : (Fin 1 → Fin M → R ⊗[F] E) → ℂ := A.indicator fun _ => 1 with hφ
  have hAclopen : IsClopen A := ⟨hAc.isClosed, hAo⟩
  have hφc : Continuous φ :=
    continuous_indicator (by simp [hAclopen.frontier_eq]) continuousOn_const
  have hφs : HasCompactSupport φ :=
    HasCompactSupport.intro hAc fun x hx => Set.indicator_of_notMem hx _
  obtain ⟨⟨hg, -⟩, -⟩ := GlobalTheory.T.gram_fiber_integral_isContDensityOn F E σ h M J hJ R hloc 1 _ _ m hμ hν hfib φ hφc hφs
  have hfin : ∀ S, m S A < ⊤ := fun S => by
    haveI := (GlobalTheory.T.gram_fiber_measure_locallyFinite_and_ne_zero_of_isOpen F E σ h M J hJ R hloc 1 _ _ m hμ hν hfib S).1
    exact hAc.measure_lt_top
  have hint : ∀ S, ∫ X, φ X ∂(m S) = (((m S A).toReal : ℝ) : ℂ) := fun S => by
    rw [hφ, integral_indicator_const _ hAm]
    simp [Measure.real]
  have hunit : hermScal R σ s ∈ {S : HermR R σ 1 | IsUnit (S : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)).det} := by
    show IsUnit (Matrix.det _)
    rw [Matrix.det_fin_one]
    exact isUnit_tmul R hs
  have hne : ∀ᶠ t in 𝓝 s, t ≠ 0 := isOpen_ne.mem_nhds hs
  have hcs : Continuous (hermScal R σ (F := F) (E := E)) := continuous_hermScal R
  have htend : Filter.Tendsto (hermScal R σ) (𝓝 s)
      (𝓝[{S : HermR R σ 1 | IsUnit (S : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)).det}] (hermScal R σ s)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨hcs.tendsto s, hne.mono fun t ht => ?_⟩
    show IsUnit (Matrix.det _)
    rw [Matrix.det_fin_one]
    exact isUnit_tmul R ht
  have hlim : Filter.Tendsto (fun t => (m (hermScal R σ t) A).toReal) (𝓝 s)
      (𝓝 (m (hermScal R σ s) A).toReal) := by
    have := (Complex.continuous_re.tendsto _).comp ((hg _ hunit).tendsto.comp htend)
    simpa [Function.comp_def, hint] using this
  obtain ⟨W, hW, hWfin⟩ := lam.finiteAt_nhds s
  set c := (m (hermScal R σ s) A).toReal with hc
  have hnear : ∀ᶠ t in 𝓝 s, |(m (hermScal R σ t) A).toReal - c| < ε := by
    have := (Metric.tendsto_nhds.mp hlim) ε hε
    simpa [Real.dist_eq] using this
  refine ⟨W ∩ {t | t ≠ 0 ∧ |(m (hermScal R σ t) A).toReal - c| < ε},
    Filter.inter_mem hW (hne.and hnear), fun V hV hVU => ?_⟩
  have hV0 : (0 : R) ∉ V := fun h0 => (hVU h0).2.1 rfl
  have hLfin : lam V ≠ ⊤ := ((measure_mono fun x hx => (hVU hx).1).trans_lt hWfin).ne
  have hP : MeasurableSet {S | qS R σ S ∈ V} := (continuous_qS R htr).measurable hV
  have hQ : MeasurableSet {X : Fin 1 → Fin M → R ⊗[F] E |
      algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) (gramR R σ J X 0 0) ∈ V} := by
    have hcq : Continuous fun X : Fin 1 → Fin M → R ⊗[F] E =>
        algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) (gramR R σ J X 0 0) :=
      continuous_const.mul (htr.comp ((hgr 1 M J).matrix_elem 0 0))
    exact hcq.measurable hV
  have hνP : coordHerm R σ b lam 1 {S | qS R σ S ∈ V} = lam V := coordHerm_qS R h htr b lam hV
  have heq := mass_eq_lintegral R h hJ hfib hAm hV0 hQ hP
  set I := coordW R b lam 1 M (A ∩ {X | algebraMap F R (1 / 2) *
          Algebra.trace R (R ⊗[F] E) (gramR R σ J X 0 0) ∈ V}) with hI
  have hbd : ∀ S ∈ {S | qS R σ S ∈ V}, |(m S A).toReal - c| < ε := by
    intro S hS
    have := (hVU hS).2.2
    rwa [hermScal_qS R h S] at this
  have hup : I ≤ ENNReal.ofReal (c + ε) * lam V := by
    rw [heq, ← hνP, ← setLIntegral_const]
    refine setLIntegral_mono' hP fun S hS => ?_
    rw [← ENNReal.ofReal_toReal (hfin S).ne]
    exact ENNReal.ofReal_le_ofReal (by linarith [(abs_lt.mp (hbd S hS)).2])
  have hlo : ENNReal.ofReal (c - ε) * lam V ≤ I := by
    rw [heq, ← hνP, ← setLIntegral_const]
    refine setLIntegral_mono' hP fun S hS => ?_
    rw [← ENNReal.ofReal_toReal (hfin S).ne]
    exact ENNReal.ofReal_le_ofReal (by linarith [(abs_lt.mp (hbd S hS)).1])
  have hc0 : 0 ≤ c := ENNReal.toReal_nonneg
  have hL0 : 0 ≤ (lam V).toReal := ENNReal.toReal_nonneg
  have hIfin : I ≠ ⊤ := (hup.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hLfin.lt_top)).ne
  have hup' : I.toReal ≤ (c + ε) * (lam V).toReal := by
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hLfin) hup
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith)] at this
  have hlo' : (c - ε) * (lam V).toReal ≤ I.toReal := by
    have := ENNReal.toReal_mono hIfin hlo
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal'] at this
    exact (mul_le_mul_of_nonneg_right (le_max_left _ _) hL0).trans this
  rw [abs_le]
  constructor <;> nlinarith
end GlobalTheory.CompanionTheory.SW.FibreRatio
