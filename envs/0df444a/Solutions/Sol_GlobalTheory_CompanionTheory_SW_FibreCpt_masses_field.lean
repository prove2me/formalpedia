-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.FibreCpt.masses_field
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:18:44.258926+00:00
-- url     : https://prove2.me/submissions/e3b90088-e735-4895-bb1e-acc0580120a9

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_BinaryMassMeans_MeanVal
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_LocalGramFiberRankOneSetFormula
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRingStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LocalBinaryGramIntegral
import Theorems.Thm_Formalism_FrobeniusOrbits_Final_real
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_FibreRatio_continuous_hermScal
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_FibreRatio_continuous_qS
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_FibreRatio_coordHerm_qS
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_FibreRatio_gram_entry
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_FibreRatio_half_trace_tmul
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_FibreRatio_hermScal_qS
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_FibreRatio_isUnit_tmul
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_FibreRatio_mass_eq_lintegral
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_FibreRatio_qS_hermScal
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_HaarCoord_half_trace_tmul
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_bd_succ_succ
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_bd_succ_zero
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_bd_zero_succ
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_bd_zero_zero
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_uni_succ_succ
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_uni_succ_zero
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_uni_zero_succ
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_uni_zero_zero
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_half_trace_tmul
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
open PositivityTheory.Rg.Mass
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter
open scoped TensorProduct ENNReal NNReal
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.FibreCpt
open GlobalTheory.CompanionTheory.SW.FibreRatio
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E}
namespace GlobalTheory.CompanionTheory.SW.FibreCpt
theorem _root_.solution (R : Type) [Field R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R]
    [BorelSpace R] (hloc : IsLocR R) (h : IsCMExt F E σ) (hJ : IsHermND σ J)
    {d : ℕ} (b : Module.Basis (Fin d) F E) (lam : Measure R) (hlam : lam.IsAddHaarMeasure)
    (m : HermR R σ 1 → Measure (Fin 1 → Fin M → R ⊗[F] E))
    (hfib : IsGramFib R σ J 1 (coordW R b lam 1 M) (coordHerm R σ b lam 1) m)
    (A : Set (Fin 1 → Fin M → R ⊗[F] E)) (hAc : IsCompact A) (hAo : IsOpen A)
    (hAU : A ⊆ {X | IsUnit (gramR R σ J X).det}) :
    Continuous (fun s : R => (m (hermScal R σ s) A).toReal) ∧
    HasCompactSupport (fun s : R => (m (hermScal R σ s) A).toReal) ∧
    ENNReal.ofReal (∫ s, (m (hermScal R σ s) A).toReal ∂lam) = coordW R b lam 1 M A := by
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
  have hcs : Continuous (hermScal R σ (F := F) (E := E)) := continuous_hermScal R

  have hqc : Continuous fun X : Fin 1 → Fin M → R ⊗[F] E =>
      algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) (gramR R σ J X 0 0) :=
    continuous_const.mul (htr.comp ((hgr 1 M J).matrix_elem 0 0))
  set K : Set R := (fun X : Fin 1 → Fin M → R ⊗[F] E =>
      algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) (gramR R σ J X 0 0)) '' A with hKdef
  have hKc : IsCompact K := hAc.image hqc
  haveI : Nontrivial (R ⊗[F] E) := ⟨1, 0, fun e => by
    have h3 := GlobalTheory.CompanionTheory.SW.FibreRatio.half_trace_tmul (F := F) (E := E) R h (1 : R)
    rw [← Algebra.TensorProduct.one_def, e, map_zero, mul_zero] at h3
    exact zero_ne_one h3⟩
  have hK0 : (0 : R) ∉ K := by
    rintro ⟨X, hX, h0⟩
    have hu : IsUnit (gramR R σ J X).det := hAU hX
    rw [Matrix.det_fin_one, gram_entry R h hJ X] at hu
    simp only at h0
    rw [h0, TensorProduct.zero_tmul] at hu
    exact not_isUnit_zero hu
  have hzero : ∀ s, s ∉ K → m (hermScal R σ s) A = 0 := by
    intro s hs
    refine measure_mono_null ?_ (hfib.1 (hermScal R σ s))
    intro X hX hXG
    apply hs
    refine ⟨X, hX, ?_⟩
    have e : gramR R σ J X = (hermScal R σ s : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) := hXG.1
    show algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) (gramR R σ J X 0 0) = s
    rw [e]
    exact qS_hermScal R h s
  have hcont : Continuous (fun s : R => (m (hermScal R σ s) A).toReal) := by
    rw [continuous_iff_continuousAt]
    intro s
    by_cases hs : s = 0
    · subst hs
      have hev : (fun _ : R => (0 : ℝ)) =ᶠ[𝓝 0] fun t : R => (m (hermScal R σ t) A).toReal := by
        filter_upwards [hKc.isClosed.isOpen_compl.mem_nhds hK0] with t ht
        simp [hzero t ht]
      exact continuousAt_const.congr hev
    · have hunit : hermScal R σ s ∈
          {S : HermR R σ 1 | IsUnit (S : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)).det} := by
        show IsUnit (Matrix.det _)
        rw [Matrix.det_fin_one]
        exact isUnit_tmul R hs
      have hne : ∀ᶠ t in 𝓝 s, t ≠ 0 := isOpen_ne.mem_nhds hs
      have htend : Filter.Tendsto (hermScal R σ) (𝓝 s)
          (𝓝[{S : HermR R σ 1 | IsUnit (S : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)).det}]
            (hermScal R σ s)) := by
        refine tendsto_nhdsWithin_iff.mpr ⟨hcs.tendsto s, hne.mono fun t ht => ?_⟩
        show IsUnit (Matrix.det _)
        rw [Matrix.det_fin_one]
        exact isUnit_tmul R ht
      have := (Complex.continuous_re.tendsto _).comp ((hg _ hunit).tendsto.comp htend)
      simpa [ContinuousAt, Function.comp_def, hint] using this
  have hsupp : HasCompactSupport (fun s : R => (m (hermScal R σ s) A).toReal) :=
    HasCompactSupport.intro hKc fun s hs => by simp [hzero s hs]
  refine ⟨hcont, hsupp, ?_⟩
  have hνeq : coordHerm R σ b lam 1 = Measure.map (hermScal R σ) lam := by
    ext T hT
    rw [Measure.map_apply hcs.measurable hT,
      ← coordHerm_qS R h htr b lam (hcs.measurable hT : MeasurableSet (hermScal R σ ⁻¹' T))]
    congr 1
    ext S
    simp [hermScal_qS R h S]
  have hgS : ∀ S, m S A = ENNReal.ofReal ((m (hermScal R σ (qS R σ S)) A).toReal) := fun S => by
    rw [hermScal_qS R h S, ENNReal.ofReal_toReal (hfin S).ne]
  have hgm : Measurable fun S : HermR R σ 1 => m S A := by
    have e : (fun S : HermR R σ 1 => m S A) =
        fun S => ENNReal.ofReal ((m (hermScal R σ (qS R σ S)) A).toReal) := funext hgS
    rw [e]
    exact ENNReal.measurable_ofReal.comp (hcont.comp (continuous_qS R htr)).measurable
  have hV : MeasurableSet ({0}ᶜ : Set R) := (measurableSet_singleton 0).compl
  have hP : MeasurableSet {S : HermR R σ 1 | qS R σ S ∈ ({0}ᶜ : Set R)} :=
    (continuous_qS R htr).measurable hV
  have hQ : MeasurableSet {X : Fin 1 → Fin M → R ⊗[F] E |
      algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) (gramR R σ J X 0 0) ∈ ({0}ᶜ : Set R)} :=
    hqc.measurable hV
  have heq := mass_eq_lintegral R h hJ hfib hAm (V := {0}ᶜ) (by simp) hQ hP
  have hAQ : A ∩ {X : Fin 1 → Fin M → R ⊗[F] E |
      algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) (gramR R σ J X 0 0) ∈ ({0}ᶜ : Set R)} = A := by
    refine Set.inter_eq_left.mpr fun X hX e => hK0 ⟨X, hX, e⟩
  rw [hAQ, ← lintegral_indicator hP] at heq
  have hind : {S : HermR R σ 1 | qS R σ S ∈ ({0}ᶜ : Set R)}.indicator (fun S => m S A) =
      fun S => m S A := by
    funext S
    by_cases hS : S ∈ {S : HermR R σ 1 | qS R σ S ∈ ({0}ᶜ : Set R)}
    · exact Set.indicator_of_mem hS _
    · rw [Set.indicator_of_notMem hS]
      have h0 : qS R σ S = 0 := by simpa using hS
      have e : S = hermScal R σ 0 := by rw [← h0, hermScal_qS R h S]
      rw [e, hzero 0 hK0]
  rw [hind, hνeq, lintegral_map hgm hcs.measurable] at heq
  rw [ofReal_integral_eq_lintegral_ofReal (hcont.integrable_of_hasCompactSupport hsupp)
    (ae_of_all _ fun _ => ENNReal.toReal_nonneg), heq]
  exact lintegral_congr fun s => ENNReal.ofReal_toReal (hfin _).ne
end GlobalTheory.CompanionTheory.SW.FibreCpt
