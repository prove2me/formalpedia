-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.exists_mem_gl3CyclicSubspace_forall_torusShellAverage_eq_apply
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/efe038a8-5310-5e15-af55-87c1eaf97943

import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_AutomorphicForm_SmoothingKernel
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Mathlib
import Theorems.Thm_LanglandsTunnell_TateLocal_hasSum_setIntegral_shell_comap_val_mulMeasure_and_modulus_eq_of_valued_eq
import Theorems.Thm_AdelicDock_isCompact_localLevelOne
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_forall_torusShellAverage_eq_apply
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions"

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory LanglandsTunnell.TateLocal UnramifiedWhittaker LanglandsTunnell.CubicInduction

open scoped nonZeroDivisors

noncomputable section

namespace TAvg

open Topology

variable {v : HeightOneSpectrum (𝓞 ℚ)}

local notation "Kv" => (HeightOneSpectrum.adicCompletion ℚ v)
local notation "G₂" => (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v))
local notation "G₃" => (GL (Fin 3) (HeightOneSpectrum.adicCompletion ℚ v))

theorem continuous_embedMat2 :
    Continuous (embedMat2 : Matrix (Fin 2) (Fin 2) Kv → Matrix (Fin 3) (Fin 3) Kv) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  fin_cases i <;> fin_cases j <;> simp [embedMat2] <;> fun_prop

theorem continuous_iotaGL : Continuous (iotaGL : G₂ → G₃) := by
  refine Units.continuous_iff.mpr ⟨continuous_embedMat2.comp Units.continuous_val, ?_⟩
  change Continuous fun h : G₂ => embedMat2 (((h⁻¹ : G₂)) : Matrix (Fin 2) (Fin 2) Kv)
  exact continuous_embedMat2.comp Units.continuous_coe_inv

theorem continuous_diag_of {f : Kvˣ → Kv} (hf : Continuous f) :
    Continuous fun u : Kvˣ => (!![f u, 0; 0, 1] : Matrix (Fin 2) (Fin 2) Kv) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  fin_cases i <;> fin_cases j <;> simp <;> first | exact hf | fun_prop

theorem continuous_diagUnitGL2 : Continuous (diagUnitGL2 : Kvˣ → G₂) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · change Continuous fun u : Kvˣ => (!![(u : Kv), 0; 0, 1] : Matrix (Fin 2) (Fin 2) Kv)
    exact continuous_diag_of Units.continuous_val
  · change Continuous fun u : Kvˣ => (!![((u⁻¹ : Kvˣ) : Kv), 0; 0, 1] : Matrix (Fin 2) (Fin 2) Kv)
    exact continuous_diag_of Units.continuous_coe_inv

theorem continuous_transposeInvN : Continuous (AutomorphicForm.transposeInvN (Fin 2) : G₂ → G₂) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · change Continuous fun g : G₂ => (((g⁻¹ : G₂) : Matrix (Fin 2) (Fin 2) Kv)).transpose
    exact Units.continuous_coe_inv.matrix_transpose
  · change Continuous fun g : G₂ => ((g : Matrix (Fin 2) (Fin 2) Kv)).transpose
    exact Units.continuous_val.matrix_transpose

theorem transposeInv3_mul (g k : G₃) : transposeInv3 (g * k) = transposeInv3 g * transposeInv3 k := by
  apply Units.ext
  simp [transposeInv3, Matrix.transpose_mul, mul_inv_rev]

theorem continuous_transposeInv3 : Continuous (transposeInv3 : G₃ → G₃) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · change Continuous fun g : G₃ => (((g⁻¹ : G₃) : Matrix (Fin 3) (Fin 3) Kv)).transpose
    exact Units.continuous_coe_inv.matrix_transpose
  · change Continuous fun g : G₃ => ((g : Matrix (Fin 3) (Fin 3) Kv)).transpose
    exact Units.continuous_val.matrix_transpose

theorem v_lt_one_iff (x : Kv) : Valued.v.restrict x < 1 ↔ Valued.v x < 1 := by
  constructor <;> intro h <;> simpa using h

theorem isOpen_lt_one : IsOpen {x : Kv | Valued.v x < 1} := by
  convert Valued.isOpen_ball Kv 1 using 1
  ext x
  exact (v_lt_one_iff x).symm

theorem isOpen_le_one : IsOpen {x : Kv | Valued.v x ≤ 1} := by
  convert Valued.isOpen_valuationSubring Kv using 1
  rfl

theorem v_zpow_uniformizer {ϖ : Kv} (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) (n : ℤ) :
    Valued.v (ϖ ^ n) = WithZero.exp (-n) := by
  rw [map_zpow₀, hϖ, ← WithZero.exp_zsmul]
  congr 1
  simp

theorem range_val : Set.range (Units.val : Kvˣ → Kv) = {x | x ≠ 0} := by
  ext x
  constructor
  · rintro ⟨u, rfl⟩; exact u.ne_zero
  · intro hx; exact ⟨Units.mk0 x hx, rfl⟩

theorem isOpenMap_val : IsOpenMap (Units.val : Kvˣ → Kv) := by
  refine (Units.isEmbedding_val₀ (G₀ := Kv)).isInducing.isOpenMap ?_
  rw [range_val]
  exact isOpen_compl_singleton

theorem isCompact_sphereK : IsCompact {x : Kv | Valued.v x = 1} := by
  have hO : IsCompact ((v.adicCompletionIntegers ℚ : Set Kv)) :=
    isCompact_iff_compactSpace.2 (NumberField.AdelicHaar.compactSpace_adicCompletionIntegers (𝓞 ℚ) ℚ v)
  have hcl : IsClosed {x : Kv | Valued.v x < 1}ᶜ := isOpen_lt_one.isClosed_compl
  have : {x : Kv | Valued.v x = 1} = (v.adicCompletionIntegers ℚ : Set Kv) ∩ {x : Kv | Valued.v x < 1}ᶜ := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, SetLike.mem_coe,
      HeightOneSpectrum.mem_adicCompletionIntegers, Set.mem_compl_iff, not_lt]
    constructor
    · intro h; exact ⟨h.le, h.ge⟩
    · rintro ⟨h1, h2⟩; exact le_antisymm h1 h2
  rw [this]
  exact hO.inter_right hcl

theorem isCompact_sph : IsCompact {u : Kvˣ | Valued.v (u : Kv) = 1} := by
  refine ((Units.isEmbedding_val₀ (G₀ := Kv)).isInducing.isCompact_iff).mpr ?_
  have : (Units.val : Kvˣ → Kv) '' {u : Kvˣ | Valued.v (u : Kv) = 1} = {x : Kv | Valued.v x = 1} := by
    ext x
    simp only [Set.mem_image, Set.mem_setOf_eq]
    constructor
    · rintro ⟨u, hu, rfl⟩; exact hu
    · intro hx
      have hx0 : x ≠ 0 := fun h => by rw [h, map_zero] at hx; exact zero_ne_one hx
      exact ⟨Units.mk0 x hx0, hx, rfl⟩
  rw [this]
  exact isCompact_sphereK

theorem higherUnitsAt_mem_nhds {π : Kv} (hπ : Valued.v π = WithZero.exp (-1 : ℤ)) (c : ℕ) :
    higherUnitsAt ℚ v c ∈ 𝓝 (1 : Kvˣ) := by
  have hπ0 : π ≠ 0 := fun h => by rw [h, map_zero] at hπ; exact WithZero.exp_ne_zero hπ.symm
  set V : Set Kv := (fun y => π ^ (-((c : ℤ) + 1)) * (y - 1)) ⁻¹' {x : Kv | Valued.v x ≤ 1} with hV
  have hVo : IsOpen V := isOpen_le_one.preimage (by fun_prop)
  have h1V : (1 : Kv) ∈ V := by simp [hV]
  have hVn : (Units.val : Kvˣ → Kv) ⁻¹' V ∈ 𝓝 (1 : Kvˣ) :=
    Units.continuous_val.continuousAt.preimage_mem_nhds (hVo.mem_nhds (by simpa using h1V))
  refine Filter.mem_of_superset hVn fun u hu => ?_
  have h : WithZero.exp ((c : ℤ) + 1) * Valued.v ((u : Kv) - 1) ≤ 1 := by
    have h' : Valued.v (π ^ (-((c : ℤ) + 1)) * ((u : Kv) - 1)) ≤ 1 := hu
    rwa [map_mul, v_zpow_uniformizer hπ, neg_neg] at h'
  have hle : Valued.v ((u : Kv) - 1) ≤ WithZero.exp (-((c : ℤ) + 1)) := by
    have key : Valued.v ((u : Kv) - 1) =
        WithZero.exp (-((c : ℤ) + 1)) * (WithZero.exp ((c : ℤ) + 1) * Valued.v ((u : Kv) - 1)) := by
      rw [← mul_assoc, ← WithZero.exp_add]; simp
    calc Valued.v ((u : Kv) - 1)
        = WithZero.exp (-((c : ℤ) + 1)) * (WithZero.exp ((c : ℤ) + 1) * Valued.v ((u : Kv) - 1)) := key
      _ ≤ WithZero.exp (-((c : ℤ) + 1)) * 1 := mul_le_mul_right h _
      _ = WithZero.exp (-((c : ℤ) + 1)) := mul_one _
  have hlt1 : Valued.v ((u : Kv) - 1) < 1 :=
    lt_of_le_of_lt hle (by rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega)
  have hv1 : Valued.v (u : Kv) = 1 := by
    have := Valuation.map_one_add_of_lt Valued.v hlt1
    rwa [add_sub_cancel] at this
  exact ⟨hv1, Or.inr (hle.trans (WithZero.exp_le_exp.mpr (by omega)))⟩

theorem continuous_char {π : Kv} (hπ : Valued.v π = WithZero.exp (-1 : ℤ))
    {η : Kvˣ →* ℂˣ} {c : ℕ} (hη : HasConductorExponentAt ℚ v η c) :
    Continuous fun u : Kvˣ => ((η u : ℂˣ) : ℂ) := by
  refine continuous_iff_continuousAt.mpr fun u₀ => ?_
  refine (Filter.EventuallyEq.continuousAt (y := ((η u₀ : ℂˣ) : ℂ)) ?_)
  have hN : (fun u => u₀⁻¹ * u) ⁻¹' higherUnitsAt ℚ v c ∈ 𝓝 u₀ := by
    refine (continuous_const.mul continuous_id).continuousAt.preimage_mem_nhds ?_
    simpa using higherUnitsAt_mem_nhds (v := v) hπ c
  refine Filter.mem_of_superset hN fun u hu => ?_
  simp only [Set.mem_preimage] at hu
  show ((η u : ℂˣ) : ℂ) = ((η u₀ : ℂˣ) : ℂ)
  have : u = u₀ * (u₀⁻¹ * u) := by group
  rw [this, map_mul, hη.1 _ hu, mul_one]

theorem opensMeasurableSpace_units [MeasurableSpace Kv] [BorelSpace Kv] : OpensMeasurableSpace Kvˣ := by
  refine ⟨MeasurableSpace.generateFrom_le fun O (hO : IsOpen O) => ?_⟩
  rw [MeasurableSpace.measurableSet_comap]
  refine ⟨Units.val '' O, (isOpenMap_val O hO).measurableSet, ?_⟩
  exact Units.val_injective.preimage_image O

scoped instance : SecondCountableTopology (Matrix (Fin 2) (Fin 2) Kv) :=
  inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → Kv))

scoped instance : SecondCountableTopology (Matrix (Fin 2) (Fin 2) Kv)ᵐᵒᵖ :=
  MulOpposite.opHomeomorph.symm.secondCountableTopology

scoped instance secondCountable_G₂ : SecondCountableTopology G₂ :=
  Units.isEmbedding_embedProduct.isInducing.secondCountableTopology

theorem exists_finset_cosets (Uv : Subgroup G₃) (hU : IsOpen (Uv : Set G₃)) {C : Set G₃} (hC : IsCompact C) :
    ∃ Q : Finset (G₃ ⧸ Uv), ∀ h ∈ C, (QuotientGroup.mk h : G₃ ⧸ Uv) ∈ Q := by
  haveI := QuotientGroup.discreteTopology hU
  have hfin : ((QuotientGroup.mk : G₃ → G₃ ⧸ Uv) '' C).Finite :=
    (hC.image continuous_quotient_mk').finite_of_discrete
  refine ⟨hfin.toFinset, fun h hh => ?_⟩
  rw [Set.Finite.mem_toFinset]
  exact ⟨h, hh, rfl⟩

theorem main [MeasurableSpace Kv] [BorelSpace Kv] [MeasurableSpace G₂] [BorelSpace G₂]
    (W : G₃ → ℂ) (Uv : Subgroup G₃) (hUo : IsOpen (Uv : Set G₃)) (hUW : ∀ k ∈ Uv, ∀ g : G₃, W (g * k) = W g)
    (τ : G₂ → G₂) (hτ : Continuous τ) (g : G₃) (k₀ : G₂)
    (η : Kvˣ →* ℂˣ) (hη : Continuous fun u : Kvˣ => ((η u : ℂˣ) : ℂ))
    (μ₂ : Measure G₂) [μ₂.IsHaarMeasure] (b : ℕ)
    (μS : Measure Kvˣ) (hSm : MeasurableSet {u : Kvˣ | Valued.v (u : Kv) = 1})
    (hSf : μS {u : Kvˣ | Valued.v (u : Kv) = 1} < ⊤) :
    ∃ Φ : G₃ → ℂ, Φ ∈ gl3CyclicSubspace W ∧
      (∃ U : Subgroup G₃, IsOpen (U : Set G₃) ∧ ∀ k ∈ U, ∀ x : G₃, Φ (x * k) = Φ x) ∧
      ∀ x : G₃,
        ∫ u in {u : Kvˣ | Valued.v (u : Kv) = 1}, (∫ k in ((AdelicDock.localLevelOne (𝓞 ℚ) ℚ v (v.asIdeal ^ b) : Subgroup G₂) : Set G₂),
            W (x * iotaGL (diagUnitGL2 u * (k₀ * τ k)) * g) ∂μ₂) * ((η u : ℂˣ) : ℂ) ∂μS = Φ x := by
  classical
  haveI : OpensMeasurableSpace Kvˣ := opensMeasurableSpace_units

  set S : Set Kvˣ := {u : Kvˣ | Valued.v (u : Kv) = 1} with hSdef
  set K : Set G₂ := ((AdelicDock.localLevelOne (𝓞 ℚ) ℚ v (v.asIdeal ^ b) : Subgroup G₂) : Set G₂) with hKdef
  have hKc : IsCompact K := AdelicDock.isCompact_localLevelOne (𝓞 ℚ) ℚ v (v.asIdeal ^ b)
  have hKm : MeasurableSet K := hKc.isClosed.measurableSet
  have hKf : μ₂ K < ⊤ := hKc.measure_lt_top
  haveI hfinK : IsFiniteMeasure (μ₂.restrict K) := isFiniteMeasure_restrict.mpr hKf.ne
  haveI hfinS : IsFiniteMeasure (μS.restrict S) := isFiniteMeasure_restrict.mpr hSf.ne
  have hSc : IsCompact S := isCompact_sph

  set P : Kvˣ × G₂ → G₃ := fun p => iotaGL (diagUnitGL2 p.1 * (k₀ * τ p.2)) * g with hPdef
  have hPc : Continuous P := by
    refine Continuous.mul ?_ continuous_const
    refine continuous_iotaGL.comp ?_
    exact (continuous_diagUnitGL2.comp continuous_fst).mul (continuous_const.mul (hτ.comp continuous_snd))
  have hCc : IsCompact (P '' (S ×ˢ K)) := (hSc.prod hKc).image hPc
  obtain ⟨Q, hQ⟩ := exists_finset_cosets Uv hUo hCc

  set r : G₃ ⧸ Uv → G₃ := fun q => Quotient.out q with hrdef
  have hr : ∀ q : G₃ ⧸ Uv, (QuotientGroup.mk (r q) : G₃ ⧸ Uv) = q := fun q => QuotientGroup.out_eq' q
  have hWr : ∀ (x h : G₃), W (x * h) = W (x * r (QuotientGroup.mk h)) := by
    intro x h
    have hmem : (r (QuotientGroup.mk h))⁻¹ * h ∈ Uv := QuotientGroup.eq.mp (hr _)
    conv_lhs => rw [show x * h = x * r (QuotientGroup.mk h) * ((r (QuotientGroup.mk h))⁻¹ * h) by group]
    exact hUW _ hmem _

  set E : G₃ ⧸ Uv → Set (Kvˣ × G₂) := fun q => P ⁻¹' ((QuotientGroup.mk : G₃ → G₃ ⧸ Uv) ⁻¹' {q}) with hEdef
  have hEo : ∀ q, IsOpen (E q) := by
    intro q
    haveI := QuotientGroup.discreteTopology hUo
    exact ((isOpen_discrete {q}).preimage QuotientGroup.continuous_mk).preimage hPc
  have hEm : ∀ q, MeasurableSet (E q) := fun q => (hEo q).measurableSet
  have hEu_open : ∀ q (u : Kvˣ), IsOpen (Prod.mk u ⁻¹' E q) := fun q u =>
    (hEo q).preimage (Continuous.prodMk_right u)

  have hmemE : ∀ q p, p ∈ E q ↔ (QuotientGroup.mk (P p) : G₃ ⧸ Uv) = q := fun q p => by
    simp [hEdef]
  have hpt : ∀ x : G₃, ∀ p ∈ S ×ˢ K,
      W (x * P p) = ∑ q ∈ Q, if p ∈ E q then W (x * r q) else 0 := by
    intro x p hp
    have hq : (QuotientGroup.mk (P p) : G₃ ⧸ Uv) ∈ Q := hQ _ ⟨p, hp, rfl⟩
    simp_rw [hmemE]
    rw [Finset.sum_ite_eq, if_pos hq]
    exact hWr x (P p)

  set m : G₃ ⧸ Uv → Kvˣ → ℝ := fun q u => (μ₂.restrict K).real (Prod.mk u ⁻¹' E q) with hmdef
  have hm_meas : ∀ q, Measurable (m q) := by
    intro q
    have := measurable_measure_prodMk_left (ν := μ₂.restrict K) (hEm q)
    simpa [hmdef, measureReal_def] using this.ennreal_toReal
  have hm_bdd : ∀ q u, ‖m q u‖ ≤ (μ₂.restrict K).real Set.univ := by
    intro q u
    rw [Real.norm_of_nonneg measureReal_nonneg]
    exact measureReal_mono (Set.subset_univ _) (measure_ne_top _ _)

  have hinner : ∀ x : G₃, ∀ u ∈ S,
      ∫ k in K, W (x * iotaGL (diagUnitGL2 u * (k₀ * τ k)) * g) ∂μ₂ = ∑ q ∈ Q, (m q u : ℂ) * W (x * r q) := by
    intro x u hu
    have h1 : ∫ k in K, W (x * iotaGL (diagUnitGL2 u * (k₀ * τ k)) * g) ∂μ₂ =
        ∫ k in K, ∑ q ∈ Q, (Prod.mk u ⁻¹' E q).indicator (fun _ => W (x * r q)) k ∂μ₂ := by
      refine setIntegral_congr_fun hKm fun k hk => ?_
      have := hpt x (u, k) ⟨hu, hk⟩
      simp only [Set.indicator_apply, Set.mem_preimage]
      simpa only [hPdef, mul_assoc] using this
    rw [h1, integral_finsetSum]
    · refine Finset.sum_congr rfl fun q _ => ?_
      rw [integral_indicator_const _ (hEu_open q u).measurableSet]
      simp [hmdef, Complex.real_smul]
    · intro q _
      exact (integrable_const _).indicator (hEu_open q u).measurableSet

  obtain ⟨M, hM⟩ := hSc.exists_bound_of_continuousOn hη.continuousOn

  set cq : G₃ ⧸ Uv → ℂ := fun q => ∫ u in S, (m q u : ℂ) * ((η u : ℂˣ) : ℂ) ∂μS with hcqdef
  have hint : ∀ q, Integrable (fun u => (m q u : ℂ) * ((η u : ℂˣ) : ℂ)) (μS.restrict S) := by
    intro q
    refine Integrable.of_bound ?_ ((μ₂.restrict K).real Set.univ * M) ?_
    · exact ((Complex.measurable_ofReal.comp (hm_meas q)).mul hη.measurable).aestronglyMeasurable
    · rw [ae_restrict_iff' hSm]
      refine Filter.Eventually.of_forall fun u hu => ?_
      rw [norm_mul, Complex.norm_real]
      exact mul_le_mul (hm_bdd q u) (hM u hu) (norm_nonneg _) measureReal_nonneg

  refine ⟨fun x => ∑ q ∈ Q, cq q * W (x * r q), ?_, ?_, ?_⟩
  ·
    have : (fun x => ∑ q ∈ Q, cq q * W (x * r q)) =
        ∑ q ∈ Q, cq q • gl3AmbientRightTranslate (R := ℂ) (r q) W := by
      funext x; simp [Finset.sum_apply, gl3AmbientRightTranslate_apply, smul_eq_mul]
    rw [this]
    exact Submodule.sum_mem _ fun q _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨r q, rfl⟩)
  ·
    let U : Subgroup G₃ :=
      { carrier := {k | ∀ q ∈ Q, (r q)⁻¹ * k * r q ∈ Uv}
        mul_mem' := by
          intro a b' ha hb
          simp only [Set.mem_setOf_eq] at ha hb ⊢
          intro q hq
          have : (r q)⁻¹ * (a * b') * r q = ((r q)⁻¹ * a * r q) * ((r q)⁻¹ * b' * r q) := by group
          rw [this]; exact Uv.mul_mem (ha q hq) (hb q hq)
        one_mem' := by
          simp only [Set.mem_setOf_eq]
          intro q _; simpa using Uv.one_mem
        inv_mem' := by
          intro a ha
          simp only [Set.mem_setOf_eq] at ha ⊢
          intro q hq
          have : (r q)⁻¹ * a⁻¹ * r q = ((r q)⁻¹ * a * r q)⁻¹ := by group
          rw [this]; exact Uv.inv_mem (ha q hq) }
    refine ⟨U, ?_, ?_⟩
    · show IsOpen {k : G₃ | ∀ q ∈ Q, (r q)⁻¹ * k * r q ∈ Uv}
      have : {k : G₃ | ∀ q ∈ Q, (r q)⁻¹ * k * r q ∈ Uv} = ⋂ q ∈ Q, (fun k => (r q)⁻¹ * k * r q) ⁻¹' (Uv : Set G₃) := by
        ext k; simp
      rw [this]
      exact isOpen_biInter_finset fun q _ => hUo.preimage ((continuous_const.mul continuous_id).mul continuous_const)
    · intro k hk x
      refine Finset.sum_congr rfl fun q hq => ?_
      have : x * k * r q = x * r q * ((r q)⁻¹ * k * r q) := by group
      rw [this, hUW _ (hk q hq)]
  ·
    intro x
    have h1 : ∫ u in S, (∫ k in K, W (x * iotaGL (diagUnitGL2 u * (k₀ * τ k)) * g) ∂μ₂) * ((η u : ℂˣ) : ℂ) ∂μS =
        ∫ u in S, ∑ q ∈ Q, ((m q u : ℂ) * ((η u : ℂˣ) : ℂ)) * W (x * r q) ∂μS := by
      refine setIntegral_congr_fun hSm fun u hu => ?_
      rw [hinner x u hu, Finset.sum_mul]
      refine Finset.sum_congr rfl fun q _ => ?_
      ring
    rw [h1, integral_finsetSum]
    · refine Finset.sum_congr rfl fun q _ => ?_
      rw [integral_mul_const]
    · intro q _
      exact (hint q).mul_const _

end TAvg
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_forall_torusShellAverage_eq_apply.TAvg"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_forall_torusShellAverage_eq_apply.TAvg"

open TAvg in
theorem solution
    (v : HeightOneSpectrum (𝓞 ℚ))
    (W : LocalGL3 v → ℂ)
    (hsm : ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 v, W (g * k) = W g)
    {ϖ : v.adicCompletionIntegers ℚ}
    (hπ : algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ))
    (b : ℕ) :
    ∀ (g₃ : LocalGL3 v) (k₀ : GL (Fin 2) (v.adicCompletion ℚ)) (η : (v.adicCompletion ℚ)ˣ →* ℂˣ) (c : ℕ),
      LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ v η c → c ≤ b →
      letI := localBorel ℚ v
      letI := localGLBorel ℚ v
      haveI := borelSpace_localGLBorel ℚ v
      ∀ (μ₂ : Measure (GL (Fin 2) (v.adicCompletion ℚ))) [μ₂.IsHaarMeasure],
        let A : ℤ × ℤ → ℂ := fun n =>
          ∫ u in {u : (v.adicCompletion ℚ)ˣ | Valued.v (u : v.adicCompletion ℚ) = 1},
            (∫ k in ((AdelicDock.localLevelOne (𝓞 ℚ) ℚ v (v.asIdeal ^ b) :
                  Subgroup (GL (Fin 2) (v.adicCompletion ℚ))) : Set (GL (Fin 2) (v.adicCompletion ℚ))),
                W (iotaGL (UnramifiedWhittaker.scalarPi
                      (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n.2 *
                    diagUnitGL2 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ
                      ^ n.1 * u) * (k₀ * k)) * g₃) ∂μ₂) * ((η u : ℂˣ) : ℂ)
          ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))
        let Ad : ℤ × ℤ → ℂ := fun n =>
          ∫ u in {u : (v.adicCompletion ℚ)ˣ | Valued.v (u : v.adicCompletion ℚ) = 1},
            (∫ k in ((AdelicDock.localLevelOne (𝓞 ℚ) ℚ v (v.asIdeal ^ b) :
                  Subgroup (GL (Fin 2) (v.adicCompletion ℚ))) : Set (GL (Fin 2) (v.adicCompletion ℚ))),
                dualWhittakerFn3 (fun x => W (x * g₃)) (iotaGL (UnramifiedWhittaker.scalarPi
                      (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n.2 *
                    diagUnitGL2 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ
                      ^ n.1 * u) * (k₀ * AutomorphicForm.transposeInvN (Fin 2) k))) ∂μ₂) * ((η u : ℂˣ) : ℂ)
          ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))
        (∃ Φ : LocalGL3 v → ℂ, Φ ∈ gl3CyclicSubspace W ∧
          (∃ U : Subgroup (LocalGL3 v), IsOpen (U : Set (LocalGL3 v)) ∧ ∀ k ∈ U, ∀ g : LocalGL3 v, Φ (g * k) = Φ g) ∧
          ∀ n : ℤ × ℤ, A n = Φ (iotaGL (UnramifiedWhittaker.scalarPi
                (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n.2 *
              diagUnitGL2 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n.1)))) ∧
        (∃ Φd : LocalGL3 v → ℂ, Φd ∈ gl3CyclicSubspace (dualWhittakerFn3 (fun x => W (x * g₃))) ∧
          (∃ U : Subgroup (LocalGL3 v), IsOpen (U : Set (LocalGL3 v)) ∧ ∀ k ∈ U, ∀ g : LocalGL3 v, Φd (g * k) = Φd g) ∧
          ∀ n : ℤ × ℤ, Ad n = Φd (iotaGL (UnramifiedWhittaker.scalarPi
                (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n.2 *
              diagUnitGL2 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n.1)))) := by
  intro g₃ k₀ η c hηc hcb
  letI : MeasurableSpace (v.adicCompletion ℚ) := localBorel ℚ v
  haveI : BorelSpace (v.adicCompletion ℚ) := ⟨rfl⟩
  letI : MeasurableSpace (GL (Fin 2) (v.adicCompletion ℚ)) := localGLBorel ℚ v
  haveI : BorelSpace (GL (Fin 2) (v.adicCompletion ℚ)) := borelSpace_localGLBorel ℚ v
  intro μ₂ _ A Ad
  obtain ⟨Uv, hUo, hUW⟩ := hsm
  have hshell := LanglandsTunnell.TateLocal.hasSum_setIntegral_shell_comap_val_mulMeasure_and_modulus_eq_of_valued_eq v
  have hSm : MeasurableSet {u : (v.adicCompletion ℚ)ˣ | Valued.v (u : v.adicCompletion ℚ) = 1} := by
    simpa using hshell.1 0
  have hSf : (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))
      {u : (v.adicCompletion ℚ)ˣ | Valued.v (u : v.adicCompletion ℚ) = 1} < ⊤ := by
    simpa using (hshell.2.2.1 0).2.2
  have hηc' := continuous_char hϖ hηc
  set ϖ' : v.adicCompletion ℚ := algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ with hϖ'
  have hdmul : ∀ (a u : (v.adicCompletion ℚ)ˣ), diagUnitGL2 (a * u) = diagUnitGL2 a * diagUnitGL2 u :=
    fun a u => by simpa [diagHom_apply] using (diagHom (A := v.adicCompletion ℚ)).map_mul a u
  constructor
  · obtain ⟨Φ, hΦmem, hΦsm, hΦ⟩ := main W Uv hUo hUW id continuous_id g₃ k₀ η hηc' μ₂ b _ hSm hSf
    refine ⟨Φ, hΦmem, hΦsm, fun n => ?_⟩
    rw [← hΦ]
    simp only [A, id, hdmul, map_mul, mul_assoc]
  ·
    set W' : LocalGL3 v → ℂ := dualWhittakerFn3 (fun x => W (x * g₃)) with hW'
    let U' : Subgroup (LocalGL3 v) :=
      { carrier := {k | g₃⁻¹ * transposeInv3 k * g₃ ∈ Uv}
        mul_mem' := by
          intro a b' ha hb
          simp only [Set.mem_setOf_eq, transposeInv3_mul] at ha hb ⊢
          have : g₃⁻¹ * (transposeInv3 a * transposeInv3 b') * g₃ =
              (g₃⁻¹ * transposeInv3 a * g₃) * (g₃⁻¹ * transposeInv3 b' * g₃) := by group
          rw [this]; exact Uv.mul_mem ha hb
        one_mem' := by
          simp only [Set.mem_setOf_eq]
          have : transposeInv3 (1 : LocalGL3 v) = 1 := Units.ext (by simp [transposeInv3])
          rw [this]; simpa using Uv.one_mem
        inv_mem' := by
          intro a ha
          simp only [Set.mem_setOf_eq] at ha ⊢
          have h1 : transposeInv3 a⁻¹ * transposeInv3 a = 1 := by
            rw [← transposeInv3_mul, inv_mul_cancel]; exact Units.ext (by simp [transposeInv3])
          have : transposeInv3 a⁻¹ = (transposeInv3 a)⁻¹ := eq_inv_of_mul_eq_one_left h1
          rw [this, show g₃⁻¹ * (transposeInv3 a)⁻¹ * g₃ = (g₃⁻¹ * transposeInv3 a * g₃)⁻¹ by group]
          exact Uv.inv_mem ha }
    have hU'o : IsOpen (U' : Set (LocalGL3 v)) := by
      show IsOpen {k : LocalGL3 v | g₃⁻¹ * transposeInv3 k * g₃ ∈ Uv}
      exact hUo.preimage ((continuous_const.mul continuous_transposeInv3).mul continuous_const)
    have hU'W : ∀ k ∈ U', ∀ x : LocalGL3 v, W' (x * k) = W' x := by
      intro k hk x
      simp only [hW', dualWhittakerFn3_apply, transposeInv3_mul]
      have : longWeyl3 * (transposeInv3 x * transposeInv3 k) * g₃ =
          longWeyl3 * transposeInv3 x * g₃ * (g₃⁻¹ * transposeInv3 k * g₃) := by group
      rw [this, hUW _ hk]
    obtain ⟨Φ, hΦmem, hΦsm, hΦ⟩ := main W' U' hU'o hU'W (AutomorphicForm.transposeInvN (Fin 2))
      continuous_transposeInvN 1 k₀ η hηc' μ₂ b _ hSm hSf
    refine ⟨Φ, hΦmem, hΦsm, fun n => ?_⟩
    rw [← hΦ]
    simp only [Ad, hW', hdmul, map_mul, mul_assoc, mul_one]

end S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_forall_torusShellAverage_eq_apply
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_forall_torusShellAverage_eq_apply (solution)
