-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.exists_forall_integrable_and_godementZeta2_transposeInv_matFourier22_eq_mul_twoVarZeta_fourierSlice_of_mem_principalSeries2
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/530faf4e-1efb-5461-9f8d-a49ba6ba4168

import Definitions.Def_LanglandsTunnell_CubicInduction_CellBumps
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_AutomorphicForm_SmoothingKernel
import Definitions.Def_LanglandsTunnell_LambdaSquared
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler

import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_LanglandsTunnell_CubicInduction_Congruence
import Definitions.Def_LanglandsTunnell_CubicInduction_GodementSection
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2
import Theorems.Thm_LanglandsTunnell_CubicInduction_conj_transposeInvN_mem_principalSeries2
import Theorems.Thm_LanglandsTunnell_CubicInduction_matFourier22_comp_mul_right_eq
import Theorems.Thm_LanglandsTunnell_CubicInduction_matFourier22_comp_inv_mul_eq
import Theorems.Thm_LanglandsTunnell_CubicInduction_isSchwartzBruhat_matFourier22
import Theorems.Thm_AutomorphicForm_map_transposeInvN_eq_self_of_isHaarMeasure_fin_two
import Theorems.Thm_Matrix_GeneralLinearGroup_isMulRightInvariant_of_isHaarMeasure_fin_two
import Theorems.Thm_AutomorphicForm_secondCountableTopology_and_locallyCompactSpace_gl_two_and_isClosed_range_unipotentGL2Hom
import Theorems.Thm_AdelicDock_isCompact_and_isOpen_localLevelOne
import Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_eq_one_of_mem_integers
import Theorems.Thm_LanglandsTunnell_TateLocal_forall_eq_one_and_exists_ne_one_of_addCharLevel
import Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_ne_one
import Theorems.Thm_LanglandsTunnell_TateLocal_addCharLevel_psiLocal_rat
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Theorems.Thm_LanglandsTunnell_TateLocal_isHaarMeasure_comap_val_mulMeasure
import Theorems.Thm_NumberField_StandardAddChar_psiLocal_rat_eq_psiV
import Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_forall_integrable_and_godementZeta2_eq_mul_twoVarZeta_slice_of_mem_principalSeries2
import Theorems.Thm_LanglandsTunnell_CubicInduction_integral_matFourier22_lowerTriangular_eq_integral_integral_upperTriangular_mul_psiLocal
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_integrable_and_godementZeta2_transposeInv_matFourier22_eq_mul_twoVarZeta_fourierSlice_of_mem_principalSeries2

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker LanglandsTunnell.Converse LanglandsTunnell.CubicInduction

open scoped nonZeroDivisors
open NumberField.AdelicLevel (diagOne)

open scoped Classical

noncomputable section

namespace U2Dual

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => (HeightOneSpectrum.adicCompletion ℚ p)
local notation "O" => (HeightOneSpectrum.adicCompletionIntegers ℚ p)
local notation "G" => (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))
local notation "Mat" => (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))
local notation "K0" => (AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ : Set (GL (Fin 2) (p.adicCompletion ℚ)))
local notation "ψp" => (NumberField.StandardAddChar.psiLocal ℚ p)

scoped instance charZero_Fp : CharZero (p.adicCompletion ℚ) :=
  charZero_of_injective_algebraMap (algebraMap ℚ (p.adicCompletion ℚ)).injective

scoped instance : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) :=
  inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → p.adicCompletion ℚ))
scoped instance : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ))ᵐᵒᵖ :=
  MulOpposite.opHomeomorph.symm.secondCountableTopology

theorem secondCountableTopology_localGL : SecondCountableTopology (GL (Fin 2) (p.adicCompletion ℚ)) :=
  Units.isEmbedding_embedProduct.isInducing.secondCountableTopology

theorem secondCountableTopology_units : SecondCountableTopology (p.adicCompletion ℚ)ˣ :=
  (Units.isEmbedding_val₀ (G₀ := p.adicCompletion ℚ)).secondCountableTopology

theorem borelSpace_units [MeasurableSpace (p.adicCompletion ℚ)] [BorelSpace (p.adicCompletion ℚ)] :
    BorelSpace (p.adicCompletion ℚ)ˣ :=
  ⟨by
    rw [(Units.isEmbedding_val₀ (G₀ := p.adicCompletion ℚ)).isInducing.eq_induced, borel_comap,
      ← BorelSpace.measurable_eq (α := p.adicCompletion ℚ)]
    rfl⟩

theorem isAddHaarMeasure_selfDualHaarAt :
    letI := localBorel ℚ p
    (selfDualHaarAt ℚ p).IsAddHaarMeasure := by
  letI := localBorel ℚ p
  haveI : BorelSpace (p.adicCompletion ℚ) := borelSpace_localBorel ℚ p
  set c : NNReal := (Ideal.absNorm p.asIdeal : NNReal) ^ (-(addCharLevel (NumberField.StandardAddChar.psiLocal ℚ p) : ℝ) / 2)
    with hc
  have hc0 : c ≠ 0 := by
    rw [hc]
    exact (NNReal.rpow_pos
      (by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr p.ne_bot))).ne'
  have hdef : selfDualHaarAt ℚ p = (c : ENNReal) • Measure.addHaarMeasure (integersPositiveCompacts ℚ p) := rfl
  rw [hdef]
  exact Measure.IsAddHaarMeasure.smul _ (by exact_mod_cast hc0) ENNReal.coe_ne_top

theorem sigmaFinite_mulHaar :
    letI := localBorel ℚ p
    SigmaFinite (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)) : Measure (p.adicCompletion ℚ)ˣ) := by
  letI := localBorel ℚ p
  haveI : BorelSpace (p.adicCompletion ℚ) := borelSpace_localBorel ℚ p
  haveI := secondCountableTopology_units p
  haveI : BorelSpace (p.adicCompletion ℚ)ˣ := borelSpace_units p
  haveI := isAddHaarMeasure_selfDualHaarAt p
  haveI : (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)) : Measure (p.adicCompletion ℚ)ˣ).IsHaarMeasure :=
    LanglandsTunnell.TateLocal.isHaarMeasure_comap_val_mulMeasure ℚ p (selfDualHaarAt ℚ p)
  haveI : SigmaCompactSpace (p.adicCompletion ℚ)ˣ := sigmaCompactSpace_of_locallyCompact_secondCountable
  infer_instance

theorem level_zero :
    (∀ x : F, Valued.v x ≤ WithZero.exp (0 : ℤ) → ψp x = 1) ∧
      ∃ x : F, Valued.v x ≤ WithZero.exp ((0 : ℤ) + 1) ∧ ψp x ≠ 1 := by
  have hk : ∃ k : ℤ, ∀ x : F, Valued.v x ≤ WithZero.exp k → ψp x = 1 := by
    refine ⟨0, fun x hx => LanglandsTunnell.TateLocal.psiLocal_eq_one_of_mem_integers ℚ p x ?_⟩
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    simpa using hx
  have h := LanglandsTunnell.TateLocal.forall_eq_one_and_exists_ne_one_of_addCharLevel ℚ p ψp hk
    (LanglandsTunnell.TateLocal.psiLocal_ne_one ℚ p)
  rwa [LanglandsTunnell.TateLocal.addCharLevel_psiLocal_rat p] at h

def w0 : G := ⟨!![0, 1; 1, 0], !![0, 1; 1, 0],
  by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two],
  by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

theorem w0_coe : ((w0 p : G) : Mat) = !![0, 1; 1, 0] := rfl
theorem w0_mul_w0 : w0 p * w0 p = 1 := Units.ext (by
  rw [Units.val_mul, w0_coe, Units.val_one]; ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two])
theorem w0_inv : (w0 p)⁻¹ = w0 p := inv_eq_of_mul_eq_one_right (w0_mul_w0 p)
theorem w0_coe_inv : (((w0 p)⁻¹ : G) : Mat) = !![0, 1; 1, 0] := by rw [w0_inv, w0_coe]
theorem w0M_transpose : (!![0, 1; 1, 0] : Mat).transpose = !![0, 1; 1, 0] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp
theorem transposeInvN_w0 : transposeInvN (Fin 2) (w0 p) = w0 p :=
  Units.ext (by rw [coe_transposeInvN, w0_coe_inv, w0_coe, w0M_transpose])
theorem det_w0 : Matrix.GeneralLinearGroup.det (w0 p) = -1 :=
  Units.ext (by rw [Matrix.GeneralLinearGroup.val_det_apply, w0_coe, Matrix.det_fin_two_of]; simp)
theorem modulus_det_w0 : modulus ((Matrix.GeneralLinearGroup.det (w0 p) : Fˣ) : F) = 1 := by
  have : ‖((Matrix.GeneralLinearGroup.det (w0 p) : Fˣ) : F)‖ = 1 := by
    rw [det_w0, Units.val_neg, Units.val_one, norm_neg, norm_one]
  rw [LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm]
  exact NNReal.eq (by rw [coe_nnnorm, NNReal.coe_one]; exact this)

def conjW (h : G) : G := w0 p * h * w0 p
theorem conjW_apply (h : G) : conjW p h = w0 p * h * w0 p := rfl
theorem conjW_conjW (h : G) : conjW p (conjW p h) = h := by
  simp only [conjW, ← mul_assoc, w0_mul_w0, one_mul]; rw [mul_assoc, w0_mul_w0, mul_one]
theorem transposeInvN_conjW (h : G) : transposeInvN (Fin 2) (conjW p h) = conjW p (transposeInvN (Fin 2) h) := by
  simp only [conjW, transposeInvN_mul, transposeInvN_w0]
theorem det_conjW (h : G) : Matrix.GeneralLinearGroup.det (conjW p h) = Matrix.GeneralLinearGroup.det h := by
  simp only [conjW, map_mul, det_w0, neg_mul, mul_neg, one_mul, mul_one, neg_neg]
theorem coe_conjW (h : G) : ((conjW p h : G) : Mat) = !![0, 1; 1, 0] * (h : Mat) * !![0, 1; 1, 0] := by
  rw [conjW, Units.val_mul, Units.val_mul, w0_coe]
theorem continuous_conjW : Continuous (conjW p) := by unfold conjW; fun_prop

def tauW (k : G) : G := conjW p (transposeInvN (Fin 2) k)
theorem tauW_tauW (k : G) : tauW p (tauW p k) = k := by
  simp only [tauW, ← transposeInvN_conjW, conjW_conjW, transposeInvN_transposeInvN]

def qR : ℝ := ((Ideal.absNorm p.asIdeal : NNReal) : ℝ)

theorem one_lt_qR : 1 < qR p := by
  have := NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal p
  unfold qR; exact_mod_cast this

theorem one_lt_qN : (1 : NNReal) < (Ideal.absNorm p.asIdeal : NNReal) :=
  NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal p

theorem norm_le_norm_iff_v_le_v (x y : F) : ‖x‖ ≤ ‖y‖ ↔ Valued.v x ≤ Valued.v y := by
  rw [NumberField.FinitePlace.norm_def, NumberField.FinitePlace.norm_def, NNReal.coe_le_coe,
    (WithZeroMulInt.toNNReal_strictMono (one_lt_qN p)).le_iff_le]

theorem norm_lt_norm_iff_v_lt_v (x y : F) : ‖x‖ < ‖y‖ ↔ Valued.v x < Valued.v y := by
  rw [NumberField.FinitePlace.norm_def, NumberField.FinitePlace.norm_def, NNReal.coe_lt_coe,
    (WithZeroMulInt.toNNReal_strictMono (one_lt_qN p)).lt_iff_lt]

theorem norm_le_one_iff_mem (x : F) : ‖x‖ ≤ 1 ↔ x ∈ (O) := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, ← (Valued.v : Valuation F _).map_one, ← norm_le_norm_iff_v_le_v p,
    norm_one]

theorem norm_add_le_max (a b : F) : ‖a + b‖ ≤ max ‖a‖ ‖b‖ := by
  rcases le_total (Valued.v a) (Valued.v b) with h | h
  · have : Valued.v (a + b) ≤ Valued.v b := le_trans (Valuation.map_add _ a b) (max_le h le_rfl)
    exact le_trans ((norm_le_norm_iff_v_le_v p _ _).2 this) (le_max_right _ _)
  · have : Valued.v (a + b) ≤ Valued.v a := le_trans (Valuation.map_add _ a b) (max_le le_rfl h)
    exact le_trans ((norm_le_norm_iff_v_le_v p _ _).2 this) (le_max_left _ _)

theorem norm_sub_le_max (a b : F) : ‖a - b‖ ≤ max ‖a‖ ‖b‖ := by
  rw [sub_eq_add_neg, ← norm_neg b]; exact norm_add_le_max p a (-b)

theorem norm_eq_qR_zpow (y : F) (j : ℤ) (hy : Valued.v y = WithZero.exp (-j)) : ‖y‖ = qR p ^ (-j) := by
  rw [NumberField.FinitePlace.norm_def, hy, WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero, NNReal.coe_zpow]
  unfold qR
  congr 1

theorem norm_eq_one_of_v {u : F} (hu : Valued.v u = 1) : ‖u‖ = 1 := by
  have := norm_eq_qR_zpow p u 0 (by rw [hu, neg_zero, WithZero.exp_zero])
  rw [this, neg_zero, zpow_zero]

theorem qR_zpow_lt_norm_of_exp_lt {x : F} {m : ℤ} (h : qR p ^ m < ‖x‖) : WithZero.exp m < Valued.v x := by
  have hx : x ≠ 0 := by
    rintro rfl; rw [norm_zero] at h; exact absurd h (not_lt.2 (zpow_pos (zero_lt_one.trans (one_lt_qR p)) m).le)
  have hvx : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  obtain ⟨k, hk⟩ : ∃ k : ℤ, Valued.v x = WithZero.exp k := ⟨WithZero.log (Valued.v x), (WithZero.exp_log hvx).symm⟩
  rw [hk, WithZero.exp_lt_exp]
  have hn := norm_eq_qR_zpow p x (-k) (by rw [neg_neg]; exact hk)
  rw [hn, neg_neg] at h
  exact (zpow_lt_zpow_iff_right₀ (one_lt_qR p)).1 h

abbrev kzero : Subgroup G := AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤

theorem isLocalLevelOne_top_of_integral {m : Mat} (h : ∀ i j, m i j ∈ (O)) :
    AdelicDock.IsLocalLevelOne (𝓞 ℚ) ℚ p ⊤ m := by
  refine ⟨h, ?_, ?_⟩
  · rw [AdelicLevel.idealBound_top]
    exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (h 1 0)
  · rw [AdelicLevel.idealBound_top]
    calc Valued.v (m 1 1 - 1) ≤ max (Valued.v (m 1 1)) (Valued.v (1 : F)) := Valuation.map_sub _ _ _
      _ ≤ 1 := max_le ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (h 1 1)) (by simp)

theorem mem_kzero_iff (k : G) :
    k ∈ kzero p ↔ (∀ i j, (k : Mat) i j ∈ (O)) ∧ ∀ i j, ((k⁻¹ : G) : Mat) i j ∈ (O) := by
  rw [AdelicDock.mem_localLevelOne_iff]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1.integral, h2.integral⟩
  · rintro ⟨h1, h2⟩
    exact ⟨isLocalLevelOne_top_of_integral p h1, isLocalLevelOne_top_of_integral p h2⟩

theorem norm_entry_le_one_of_mem_kzero {k : G} (hk : k ∈ kzero p) (i j : Fin 2) : ‖(k : Mat) i j‖ ≤ 1 :=
  (norm_le_one_iff_mem p _).2 (((mem_kzero_iff p k).1 hk).1 i j)

theorem coe_det (g : G) : ((Matrix.GeneralLinearGroup.det g : Fˣ) : F) = (g : Mat) 0 0 * (g : Mat) 1 1 - (g : Mat) 0 1 * (g : Mat) 1 0 := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]

theorem norm_det_le (g : G) :
    ‖((Matrix.GeneralLinearGroup.det g : Fˣ) : F)‖ ≤
      max ‖(g : Mat) 0 0‖ ‖(g : Mat) 0 1‖ * max ‖(g : Mat) 1 0‖ ‖(g : Mat) 1 1‖ := by
  rw [coe_det]
  refine le_trans (norm_sub_le_max p _ _) (max_le ?_ ?_)
  · rw [norm_mul]; exact mul_le_mul (le_max_left _ _) (le_max_right _ _) (norm_nonneg _) (le_trans (norm_nonneg _) (le_max_left _ _))
  · rw [norm_mul]; exact mul_le_mul (le_max_right _ _) (le_max_left _ _) (norm_nonneg _) (le_trans (norm_nonneg _) (le_max_left _ _))

theorem norm_det_of_mem_kzero {k : G} (hk : k ∈ kzero p) :
    ‖((Matrix.GeneralLinearGroup.det k : Fˣ) : F)‖ = 1 := by
  have hle : ∀ {k : G}, k ∈ kzero p → ‖((Matrix.GeneralLinearGroup.det k : Fˣ) : F)‖ ≤ 1 := by
    intro k hk
    refine le_trans (norm_det_le p k) ?_
    have h := norm_entry_le_one_of_mem_kzero p hk
    calc max ‖(k : Mat) 0 0‖ ‖(k : Mat) 0 1‖ * max ‖(k : Mat) 1 0‖ ‖(k : Mat) 1 1‖ ≤ 1 * 1 :=
          mul_le_mul (max_le (h 0 0) (h 0 1)) (max_le (h 1 0) (h 1 1)) (le_trans (norm_nonneg _) (le_max_left _ _)) zero_le_one
      _ = 1 := one_mul 1
  have h1 := hle hk
  have h2 := hle (inv_mem hk)
  rw [map_inv, Units.val_inv_eq_inv_val, norm_inv] at h2
  have hpos : 0 < ‖((Matrix.GeneralLinearGroup.det k : Fˣ) : F)‖ := norm_pos_iff.2 (Units.ne_zero _)
  have := (inv_le_one₀ hpos).1 h2
  exact le_antisymm h1 this

theorem coe_modulus_eq_norm (x : F) : ((modulus x : NNReal) : ℝ) = ‖x‖ := by
  rw [modulus_adicCompletion_eq_nnnorm ℚ p x, coe_nnnorm]

theorem w0M_entry_mem (i j : Fin 2) : (!![0, 1; 1, 0] : Mat) i j ∈ (O) := by
  fin_cases i <;> fin_cases j <;> simp [zero_mem, one_mem]

theorem w0_mem_K0 : w0 p ∈ kzero p := by
  rw [mem_kzero_iff, w0_coe_inv, w0_coe]
  exact ⟨w0M_entry_mem p, w0M_entry_mem p⟩

theorem transposeInvN_mem_K0 {k : G} (hk : k ∈ kzero p) : transposeInvN (Fin 2) k ∈ kzero p := by
  rw [mem_kzero_iff] at hk ⊢
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [coe_transposeInvN, Matrix.transpose_apply]; exact hk.2 j i
  · rw [coe_inv_transposeInvN, Matrix.transpose_apply]; exact hk.1 j i

theorem conjW_mem_K0 {k : G} (hk : k ∈ kzero p) : conjW p k ∈ kzero p :=
  Subgroup.mul_mem _ (Subgroup.mul_mem _ (w0_mem_K0 p) hk) (w0_mem_K0 p)

theorem tauW_mem_K0 {k : G} (hk : k ∈ kzero p) : tauW p k ∈ kzero p :=
  conjW_mem_K0 p (transposeInvN_mem_K0 p hk)

theorem tauW_preimage_K0 : tauW p ⁻¹' K0 = K0 := by
  ext k
  simp only [Set.mem_preimage, SetLike.mem_coe]
  constructor
  · intro h; have := tauW_mem_K0 p h; rwa [tauW_tauW] at this
  · exact tauW_mem_K0 p

theorem modulus_det_of_mem_K0 {k : G} (hk : k ∈ kzero p) :
    modulus ((Matrix.GeneralLinearGroup.det k : Fˣ) : F) = 1 := by
  have h := norm_det_of_mem_kzero p hk
  rw [← coe_modulus_eq_norm p] at h
  exact_mod_cast h

theorem map_conjW :
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    ∀ (μ₂ : Measure G) [μ₂.IsHaarMeasure], Measure.map (conjW p) μ₂ = μ₂ := by
  letI := localGLBorel ℚ p
  haveI := borelSpace_localGLBorel ℚ p
  intro μ₂ _
  obtain ⟨hSC, hLC, -⟩ :=
    AutomorphicForm.secondCountableTopology_and_locallyCompactSpace_gl_two_and_isClosed_range_unipotentGL2Hom (K := ℚ) p
  haveI := hSC; haveI := hLC
  haveI : μ₂.IsMulRightInvariant := Matrix.GeneralLinearGroup.isMulRightInvariant_of_isHaarMeasure_fin_two μ₂
  have hc : conjW p = (fun h : G => h * w0 p) ∘ (fun h : G => w0 p * h) := rfl
  rw [hc, ← Measure.map_map (measurable_mul_const _) (measurable_const_mul _), MeasureTheory.map_mul_left_eq_self,
    MeasureTheory.map_mul_right_eq_self]

theorem continuous_transposeInvN : Continuous fun k : G => transposeInvN (Fin 2) k := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · show Continuous fun k : G => (((k⁻¹ : G) : Mat)).transpose
    exact Units.continuous_coe_inv.matrix_transpose
  · show Continuous fun k : G => ((k : G) : Mat).transpose
    exact Units.continuous_val.matrix_transpose

theorem continuous_tauW : Continuous (tauW p) := (continuous_conjW p).comp (continuous_transposeInvN p)

theorem map_tauW :
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    ∀ (μ₂ : Measure G) [μ₂.IsHaarMeasure], Measure.map (tauW p) μ₂ = μ₂ := by
  letI := localGLBorel ℚ p
  haveI := borelSpace_localGLBorel ℚ p
  intro μ₂ _
  have ht : tauW p = conjW p ∘ fun k : G => transposeInvN (Fin 2) k := rfl
  rw [ht, ← Measure.map_map (continuous_conjW p).measurable (continuous_transposeInvN p).measurable,
    AutomorphicForm.map_transposeInvN_eq_self_of_isHaarMeasure_fin_two p μ₂, map_conjW p μ₂]

def PhiC (Φ : Mat → ℂ) : Mat → ℂ := fun Y => Φ (!![0, 1; 1, 0] * Y * !![0, 1; 1, 0])

theorem continuous_cW : Continuous fun Y : Mat => (!![0, 1; 1, 0] : Mat) * Y * !![0, 1; 1, 0] :=
  (continuous_const.mul continuous_id).mul continuous_const

theorem cW_cW (Y : Mat) : (!![0, 1; 1, 0] : Mat) * ((!![0, 1; 1, 0] : Mat) * Y * !![0, 1; 1, 0]) * !![0, 1; 1, 0] = Y := by
  have h : (!![0, 1; 1, 0] : Mat) * !![0, 1; 1, 0] = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  rw [← mul_assoc, ← mul_assoc, h, one_mul, mul_assoc, h, mul_one]

theorem isSchwartzBruhat_PhiC (Φ : Mat → ℂ) (hlc : IsLocallyConstant Φ) (hcs : HasCompactSupport Φ) :
    IsSchwartzBruhat (PhiC p Φ) := by
  refine ⟨hlc.comp_continuous (continuous_cW p), ?_⟩
  refine HasCompactSupport.intro (hcs.image (continuous_cW p)) fun Y hY => ?_
  show Φ (!![0, 1; 1, 0] * Y * !![0, 1; 1, 0]) = 0
  apply image_eq_zero_of_notMem_tsupport
  intro hmem
  exact hY ⟨_, hmem, cW_cW p Y⟩

theorem matFourier22_PhiC (Φ : Mat → ℂ) (hΦ : IsSchwartzBruhat Φ) (X : Mat) :
    matFourier22 p ψp (PhiC p Φ) X = matFourier22 p ψp Φ (!![0, 1; 1, 0] * X * !![0, 1; 1, 0]) := by
  obtain ⟨h0, h0'⟩ := level_zero p

  set Φ₁ : Mat → ℂ := fun Z : Mat => Φ (Z * ((w0 p : G) : Mat)) with hΦ₁
  have hfun : PhiC p Φ = fun Y : Mat => Φ₁ ((((w0 p)⁻¹ : G) : Mat) * Y) := by
    funext Y; simp only [PhiC, hΦ₁, w0_coe_inv, w0_coe]
  rw [hfun, LanglandsTunnell.CubicInduction.matFourier22_comp_inv_mul_eq p ψp (w0 p) Φ₁ X, modulus_det_w0, hΦ₁,
    LanglandsTunnell.CubicInduction.matFourier22_comp_mul_right_eq p ψp 0 h0 h0' Φ hΦ (w0 p), modulus_det_w0,
    transposeInvN_w0, w0_coe, w0M_transpose]
  simp [mul_assoc]

theorem det_transposeInvN (k : G) :
    Matrix.GeneralLinearGroup.det (transposeInvN (Fin 2) k) = (Matrix.GeneralLinearGroup.det k)⁻¹ :=
  Units.ext (by
    rw [Matrix.GeneralLinearGroup.val_det_apply, coe_transposeInvN, Matrix.det_transpose,
      ← Matrix.GeneralLinearGroup.val_det_apply, map_inv])

theorem det_tauW (k : G) : Matrix.GeneralLinearGroup.det (tauW p k) = (Matrix.GeneralLinearGroup.det k)⁻¹ := by
  rw [tauW, det_conjW, det_transposeInvN]

theorem conjW_transposeInvN_tauW (k : G) : conjW p (transposeInvN (Fin 2) (tauW p k)) = k := by
  rw [tauW, transposeInvN_conjW, transposeInvN_transposeInvN, conjW_conjW]

theorem coe_tauW (k : G) : ((tauW p k : G) : Mat) = !![0, 1; 1, 0] * ((k⁻¹ : G) : Mat).transpose * !![0, 1; 1, 0] := by
  rw [tauW, coe_conjW, coe_transposeInvN]

theorem w0M_mul_w0M : (!![0, 1; 1, 0] : Mat) * !![0, 1; 1, 0] = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem w0M_upper_w0M (a x d : F) : (!![0, 1; 1, 0] : Mat) * !![a, x; 0, d] * !![0, 1; 1, 0] = !![d, 0; x, a] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem isSchwartzBruhat_comp_mul_right (Φ : Mat → ℂ) (hΦ : IsSchwartzBruhat Φ) (k : G) :
    IsSchwartzBruhat fun X : Mat => Φ (X * (k : Mat)) := by
  have hc : Continuous fun X : Mat => X * (k : Mat) := continuous_id.mul continuous_const
  refine ⟨hΦ.1.comp_continuous hc, ?_⟩
  have hc' : Continuous fun X : Mat => X * ((k⁻¹ : G) : Mat) := continuous_id.mul continuous_const
  refine HasCompactSupport.intro (hΦ.2.image hc') fun X hX => ?_
  apply image_eq_zero_of_notMem_tsupport
  intro hmem
  exact hX ⟨_, hmem, by simp only; rw [mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]⟩

section PsiNorm
open NumberField.StandardAddChar

theorem norm_psiPadicFun (q : ℕ) [Fact q.Prime] (x : ℚ_[q]) : ‖psiPadicFun x‖ = 1 := by
  unfold psiPadicFun
  obtain ⟨r, hr⟩ : ∃ r : ℝ, -(2 * (Real.pi : ℂ) * Complex.I) *
      ((((exists_pPow_approx x).choose : ℤ) : ℂ) / ((q : ℂ)) ^ ((exists_pPow_approx x).choose_spec.choose)) = (r : ℂ) * Complex.I :=
    ⟨-(2 * Real.pi * (((exists_pPow_approx x).choose : ℝ) / (q : ℝ) ^ ((exists_pPow_approx x).choose_spec.choose))), by push_cast; ring⟩
  rw [hr, Complex.norm_exp_ofReal_mul_I]

local instance (q : Nat.Primes) : Fact q.1.Prime := ⟨q.2⟩

theorem norm_psiV (v : HeightOneSpectrum (𝓞 ℚ)) (x : v.adicCompletion ℚ) : ‖psiV v x‖ = 1 := by
  rw [psiV_apply, psiPadic_apply]
  exact norm_psiPadicFun _ _

theorem norm_psiLocal' (x : F) : ‖ψp x‖ = 1 := by
  rw [NumberField.StandardAddChar.psiLocal_rat_eq_psiV]; exact norm_psiV p x

end PsiNorm

theorem continuous_detGL : Continuous (Matrix.GeneralLinearGroup.det : G → Fˣ) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · have : (fun g : G => ((Matrix.GeneralLinearGroup.det g : Fˣ) : F)) = fun g : G => ((g : G) : Mat).det := by
      funext g; exact Matrix.GeneralLinearGroup.val_det_apply g
    rw [show (Units.val ∘ (Matrix.GeneralLinearGroup.det : G → Fˣ)) = fun g : G => ((Matrix.GeneralLinearGroup.det g : Fˣ) : F) from rfl, this]
    exact Units.continuous_val.matrix_det
  · have : (fun g : G => (((Matrix.GeneralLinearGroup.det g)⁻¹ : Fˣ) : F)) = fun g : G => (((g⁻¹ : G) : Mat)).det := by
      funext g; rw [← map_inv]; exact Matrix.GeneralLinearGroup.val_det_apply g⁻¹
    rw [show (fun u : G => ((Matrix.GeneralLinearGroup.det u)⁻¹ : Fˣ).val) = fun g : G => (((Matrix.GeneralLinearGroup.det g)⁻¹ : Fˣ) : F) from rfl, this]
    exact Units.continuous_coe_inv.matrix_det

theorem continuous_upper (k : Mat) : Continuous fun z : (F × F) × F => (!![z.1.1, z.2; 0, z.1.2] : Mat) * k := by
  refine Continuous.mul ?_ continuous_const
  refine continuous_pi fun i => continuous_pi fun j => ?_
  fin_cases i <;> fin_cases j <;> simp <;> fun_prop

theorem continuous_upper' : Continuous fun z : (G × (F × F)) × F => (!![z.1.2.1, z.2; 0, z.1.2.2] : Mat) * ((z.1.1 : G) : Mat) := by
  refine Continuous.mul ?_ (Units.continuous_val.comp (continuous_fst.comp continuous_fst))
  refine continuous_pi fun i => continuous_pi fun j => ?_
  fin_cases i <;> fin_cases j <;> simp <;> fun_prop

theorem fubini_slice
    (lam : Fin 2 → (Fˣ →* ℂˣ)) (χ : Fˣ →* ℂˣ) (hχ : IsLocallyConstant χ)
    (Fsec : G → ℂ) (hF : Fsec ∈ principalSeries2 p lam)
    (Φ : Mat → ℂ) (hlc : IsLocallyConstant Φ) (hcs : HasCompactSupport Φ) (a d : F) :
    letI : MeasurableSpace F := localBorel ℚ p
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    ∀ (μ₂ : Measure G) [μ₂.IsHaarMeasure],
    (∫ k in K0, Fsec k * ((χ (Matrix.GeneralLinearGroup.det k) : ℂˣ) : ℂ) *
        (∫ vt : F × F, (∫ y : F, Φ (!![vt.1, y; 0, vt.2] * (k : Mat)) ∂(selfDualHaarAt ℚ p)) *
          ψp (vt.1 * d + vt.2 * a) ∂((selfDualHaarAt ℚ p).prod (selfDualHaarAt ℚ p))) ∂μ₂) =
      ∫ uv : F × F,
        (∫ k in K0, Fsec k * ((χ (Matrix.GeneralLinearGroup.det k) : ℂˣ) : ℂ) *
            (∫ x : F, Φ (!![uv.1, x; 0, uv.2] * (k : Mat)) ∂(selfDualHaarAt ℚ p)) ∂μ₂) *
          ψp (uv.1 * d + uv.2 * a) ∂((selfDualHaarAt ℚ p).prod (selfDualHaarAt ℚ p)) := by
  letI : MeasurableSpace F := localBorel ℚ p
  letI := localGLBorel ℚ p
  haveI := borelSpace_localGLBorel ℚ p
  intro μ₂ _
  haveI : BorelSpace F := borelSpace_localBorel ℚ p
  haveI : SFinite (selfDualHaarAt ℚ p) := by unfold selfDualHaarAt; infer_instance
  haveI := isAddHaarMeasure_selfDualHaarAt p
  obtain ⟨hSC, hLC, -⟩ :=
    AutomorphicForm.secondCountableTopology_and_locallyCompactSpace_gl_two_and_isClosed_range_unipotentGL2Hom (K := ℚ) p
  haveI := hSC; haveI := hLC
  haveI : SigmaCompactSpace G := sigmaCompactSpace_of_locallyCompact_secondCountable
  haveI : SigmaFinite μ₂ := by infer_instance
  obtain ⟨hKc, hKo⟩ := AdelicDock.isCompact_and_isOpen_localLevelOne ℚ p (⊤ : Ideal (𝓞 ℚ)) top_ne_bot
  have hK0meas : MeasurableSet K0 := hKo.measurableSet
  haveI : IsFiniteMeasure (μ₂.restrict K0) := ⟨by rw [Measure.restrict_apply_univ]; exact hKc.measure_lt_top⟩
  set σ : Measure F := selfDualHaarAt ℚ p with hσ

  set H : G → F × F → ℂ := fun k vt => Fsec k * ((χ (Matrix.GeneralLinearGroup.det k) : ℂˣ) : ℂ) *
      (∫ y : F, Φ (!![vt.1, y; 0, vt.2] * (k : Mat)) ∂σ) * ψp (vt.1 * d + vt.2 * a) with hH
  have eqL : (∫ k in K0, Fsec k * ((χ (Matrix.GeneralLinearGroup.det k) : ℂˣ) : ℂ) *
        (∫ vt : F × F, (∫ y : F, Φ (!![vt.1, y; 0, vt.2] * (k : Mat)) ∂σ) *
          ψp (vt.1 * d + vt.2 * a) ∂(σ.prod σ)) ∂μ₂) = ∫ k in K0, ∫ vt : F × F, H k vt ∂(σ.prod σ) ∂μ₂ := by
    congr 1; funext k
    rw [← integral_const_mul]
    congr 1; funext vt
    simp only [hH]; ring
  have eqR : (∫ uv : F × F, (∫ k in K0, Fsec k * ((χ (Matrix.GeneralLinearGroup.det k) : ℂˣ) : ℂ) *
        (∫ x : F, Φ (!![uv.1, x; 0, uv.2] * (k : Mat)) ∂σ) ∂μ₂) * ψp (uv.1 * d + uv.2 * a) ∂(σ.prod σ)) =
      ∫ vt : F × F, ∫ k in K0, H k vt ∂μ₂ ∂(σ.prod σ) := by
    congr 1; funext vt
    rw [← integral_mul_const]
  rw [eqL, eqR]
  refine integral_integral_swap ?_

  have hFc : Continuous Fsec := (mem_principalSeries2_iff.mp hF).1.continuous
  have hχc : Continuous fun k : G => ((χ (Matrix.GeneralLinearGroup.det k) : ℂˣ) : ℂ) :=
    Units.continuous_val.comp (hχ.continuous.comp (continuous_detGL p))
  have hΦc : Continuous Φ := hlc.continuous
  have hψc : Continuous fun vt : F × F => ψp (vt.1 * d + vt.2 * a) :=
    (NumberField.StandardAddChar.continuous_psiLocal ℚ p).comp (by fun_prop)
  have hJ : Continuous fun z : (G × (F × F)) × F => Φ ((!![z.1.2.1, z.2; 0, z.1.2.2] : Mat) * ((z.1.1 : G) : Mat)) :=
    hΦc.comp (continuous_upper' p)
  have hI : StronglyMeasurable fun q : G × (F × F) => ∫ y : F, Φ ((!![q.2.1, y; 0, q.2.2] : Mat) * ((q.1 : G) : Mat)) ∂σ :=
    hJ.stronglyMeasurable.integral_prod_right'
  have hmeas : AEStronglyMeasurable (Function.uncurry H) ((μ₂.restrict K0).prod (σ.prod σ)) := by
    have : Function.uncurry H = fun q : G × (F × F) =>
        (Fsec q.1 * ((χ (Matrix.GeneralLinearGroup.det q.1) : ℂˣ) : ℂ)) *
          (∫ y : F, Φ ((!![q.2.1, y; 0, q.2.2] : Mat) * ((q.1 : G) : Mat)) ∂σ) * ψp (q.2.1 * d + q.2.2 * a) := by
      funext q; simp only [Function.uncurry, hH]
    rw [this]
    exact ((((hFc.comp continuous_fst).mul (hχc.comp continuous_fst)).stronglyMeasurable.mul hI).mul
      (hψc.comp continuous_snd).stronglyMeasurable).aestronglyMeasurable

  obtain ⟨MF, hMF⟩ := hKc.exists_bound_of_continuousOn hFc.continuousOn
  obtain ⟨Mχ, hMχ⟩ := hKc.exists_bound_of_continuousOn hχc.continuousOn
  obtain ⟨MΦ, hMΦ⟩ := hΦc.bounded_above_of_compact_support hcs
  have hMΦ0 : 0 ≤ MΦ := le_trans (norm_nonneg _) (hMΦ 0)
  have hMF0 : 0 ≤ MF := by
    obtain ⟨k₀, hk₀⟩ : ∃ k₀, k₀ ∈ K0 := ⟨1, (AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤).one_mem⟩
    exact le_trans (norm_nonneg _) (hMF k₀ hk₀)
  have hMχ0 : 0 ≤ Mχ := le_trans (norm_nonneg _) (hMχ 1 (AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤).one_mem)

  have hEc : Continuous fun X : Mat => ∑ i : Fin 2, ∑ j : Fin 2, ‖X i j‖ := by fun_prop
  obtain ⟨R₀, hR₀⟩ := hcs.isCompact.exists_bound_of_continuousOn hEc.continuousOn
  have hentry : ∀ X ∈ tsupport Φ, ∀ i j : Fin 2, ‖X i j‖ ≤ R₀ := by
    intro X hX i j
    have h := hR₀ X hX
    rw [Real.norm_of_nonneg (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => norm_nonneg _)] at h
    refine le_trans ?_ h
    refine le_trans ?_ (Finset.single_le_sum (f := fun i => ∑ j : Fin 2, ‖X i j‖)
      (fun i _ => Finset.sum_nonneg fun j _ => norm_nonneg _) (Finset.mem_univ i))
    exact Finset.single_le_sum (f := fun j => ‖X i j‖) (fun j _ => norm_nonneg _) (Finset.mem_univ j)
  set R : ℝ := 2 * R₀ with hRdef

  have hsupp : ∀ k ∈ K0, ∀ v y t : F, Φ (!![v, y; 0, t] * (k : Mat)) ≠ 0 → ‖v‖ ≤ R ∧ ‖y‖ ≤ R ∧ ‖t‖ ≤ R := by
    intro k hk v y t hne
    have hX : !![v, y; 0, t] * (k : Mat) ∈ tsupport Φ := subset_tsupport _ hne
    have hkinv : ∀ i j : Fin 2, ‖((k⁻¹ : G) : Mat) i j‖ ≤ 1 := norm_entry_le_one_of_mem_kzero p (inv_mem hk)
    have hback : (!![v, y; 0, t] : Mat) = (!![v, y; 0, t] * (k : Mat)) * ((k⁻¹ : G) : Mat) := by
      rw [mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]
    have hR₀0 : 0 ≤ R₀ := le_trans (norm_nonneg _) (hentry _ hX 0 0)
    have hbound : ∀ i j : Fin 2, ‖(!![v, y; 0, t] : Mat) i j‖ ≤ R := by
      intro i j
      rw [hback, Matrix.mul_apply, Fin.sum_univ_two]
      refine le_trans (norm_add_le _ _) ?_
      rw [norm_mul, norm_mul, hRdef, two_mul]
      have e1 : ‖(!![v, y; 0, t] * (k : Mat)) i 0‖ * ‖((k⁻¹ : G) : Mat) 0 j‖ ≤ R₀ := by
        calc _ ≤ R₀ * 1 := mul_le_mul (hentry _ hX i 0) (hkinv 0 j) (norm_nonneg _) hR₀0
          _ = R₀ := mul_one _
      have e2 : ‖(!![v, y; 0, t] * (k : Mat)) i 1‖ * ‖((k⁻¹ : G) : Mat) 1 j‖ ≤ R₀ := by
        calc _ ≤ R₀ * 1 := mul_le_mul (hentry _ hX i 1) (hkinv 1 j) (norm_nonneg _) hR₀0
          _ = R₀ := mul_one _
      exact add_le_add e1 e2
    exact ⟨by simpa using hbound 0 0, by simpa using hbound 0 1, by simpa using hbound 1 1⟩

  set ball : Set F := Metric.closedBall (0 : F) R with hball
  have hball_meas : MeasurableSet ball := Metric.isClosed_closedBall.measurableSet
  have hball_fin : σ ball < ⊤ := (isCompact_closedBall (0 : F) R).measure_lt_top
  set B : Set (F × F) := ball ×ˢ ball with hB
  have hB_meas : MeasurableSet B := hball_meas.prod hball_meas
  have hB_fin : (σ.prod σ) B < ⊤ := by
    rw [hB, Measure.prod_prod]; exact ENNReal.mul_lt_top hball_fin hball_fin

  set C₀ : ℝ := MΦ * (σ ball).toReal with hC₀
  have hC₀0 : 0 ≤ C₀ := mul_nonneg hMΦ0 ENNReal.toReal_nonneg
  have hyint : ∀ k ∈ K0, ∀ vt : F × F,
      ‖∫ y : F, Φ (!![vt.1, y; 0, vt.2] * (k : Mat)) ∂σ‖ ≤ C₀ * B.indicator (fun _ => (1 : ℝ)) vt := by
    intro k hk vt
    by_cases hvt : vt ∈ B
    · rw [Set.indicator_of_mem hvt, mul_one]
      have hg : Integrable (ball.indicator fun _ : F => MΦ) σ := by
        haveI : IsFiniteMeasure (σ.restrict ball) := ⟨by rw [Measure.restrict_apply_univ]; exact hball_fin⟩
        have h1 : IntegrableOn (fun _ : F => MΦ) ball σ := integrable_const MΦ
        exact h1.integrable_indicator hball_meas
      refine le_trans (norm_integral_le_of_norm_le hg (Filter.Eventually.of_forall fun y => ?_)) ?_
      · by_cases hy : y ∈ ball
        · rw [Set.indicator_of_mem hy]; exact hMΦ _
        · rw [Set.indicator_of_notMem hy]
          have : Φ (!![vt.1, y; 0, vt.2] * (k : Mat)) = 0 := by
            by_contra hne
            exact hy (by rw [hball, mem_closedBall_zero_iff]; exact (hsupp k hk _ _ _ hne).2.1)
          rw [this, norm_zero]
      · rw [integral_indicator_const _ hball_meas, hC₀, smul_eq_mul, mul_comm]
        rfl
    · rw [Set.indicator_of_notMem hvt, mul_zero]
      have : (fun y : F => Φ (!![vt.1, y; 0, vt.2] * (k : Mat))) = fun _ => 0 := by
        funext y
        by_contra hne
        have h := hsupp k hk _ _ _ hne
        exact hvt (by rw [hB, hball]; exact ⟨mem_closedBall_zero_iff.2 h.1, mem_closedBall_zero_iff.2 h.2.2⟩)
      rw [this, integral_zero, norm_zero]

  set C : ℝ := MF * Mχ * C₀ with hC
  have hBind : Integrable (B.indicator fun _ : F × F => (1 : ℝ)) (σ.prod σ) := by
    haveI : IsFiniteMeasure ((σ.prod σ).restrict B) := ⟨by rw [Measure.restrict_apply_univ]; exact hB_fin⟩
    have h1 : IntegrableOn (fun _ : F × F => (1 : ℝ)) B (σ.prod σ) := integrable_const (1 : ℝ)
    exact h1.integrable_indicator hB_meas
  have hmaj : Integrable (fun q : G × (F × F) => (fun _ : G => C) q.1 * B.indicator (fun _ => (1 : ℝ)) q.2)
      ((μ₂.restrict K0).prod (σ.prod σ)) :=
    Integrable.mul_prod (integrable_const C) hBind
  have hae : ∀ᵐ q ∂((μ₂.restrict K0).prod (σ.prod σ)), q.1 ∈ K0 := by
    have : (μ₂.restrict K0).prod (σ.prod σ) = ((μ₂.prod (σ.prod σ)).restrict (K0 ×ˢ Set.univ)) := by
      rw [← Measure.prod_restrict, Measure.restrict_univ]
    rw [this]
    filter_upwards [ae_restrict_mem (hK0meas.prod MeasurableSet.univ)] with q hq
    exact hq.1
  refine hmaj.mono' hmeas ?_
  filter_upwards [hae] with q hq
  simp only [Function.uncurry, hH]
  rw [norm_mul, norm_mul, norm_mul, norm_psiLocal', mul_one, hC]
  have h1 := hMF q.1 hq
  have h2 := hMχ q.1 hq
  have h3 := hyint q.1 hq q.2
  have hind0 : 0 ≤ B.indicator (fun _ => (1 : ℝ)) q.2 := Set.indicator_nonneg (fun _ _ => zero_le_one) _
  calc ‖Fsec q.1‖ * ‖((χ (Matrix.GeneralLinearGroup.det q.1) : ℂˣ) : ℂ)‖ *
          ‖∫ y : F, Φ (!![q.2.1, y; 0, q.2.2] * (q.1 : Mat)) ∂σ‖
        ≤ MF * Mχ * (C₀ * B.indicator (fun _ => (1 : ℝ)) q.2) :=
          mul_le_mul (mul_le_mul h1 h2 (norm_nonneg _) hMF0) h3 (norm_nonneg _) (mul_nonneg hMF0 hMχ0)
    _ = MF * Mχ * C₀ * B.indicator (fun _ => (1 : ℝ)) q.2 := by ring

theorem slice_conj_eq
    (lam : Fin 2 → (Fˣ →* ℂˣ)) (χ : Fˣ →* ℂˣ) (hχ : IsLocallyConstant χ)
    (Fsec : G → ℂ) (hF : Fsec ∈ principalSeries2 p lam)
    (Φ : Mat → ℂ) (hlc : IsLocallyConstant Φ) (hcs : HasCompactSupport Φ) (a d : F) :
    letI : MeasurableSpace F := localBorel ℚ p
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    ∀ (μ₂ : Measure G) [μ₂.IsHaarMeasure],
    (∫ k in K0, Fsec (w0 p * transposeInvN (Fin 2) k * w0 p) *
        ((χ⁻¹ (Matrix.GeneralLinearGroup.det k) : ℂˣ) : ℂ) *
        (∫ x : F, matFourier22 p ψp (PhiC p Φ) (!![a, x; 0, d] * (k : Mat)) ∂(selfDualHaarAt ℚ p)) ∂μ₂) =
      ∫ uv : F × F,
        (∫ k in K0, Fsec k * ((χ (Matrix.GeneralLinearGroup.det k) : ℂˣ) : ℂ) *
            (∫ x : F, Φ (!![uv.1, x; 0, uv.2] * (k : Mat)) ∂(selfDualHaarAt ℚ p)) ∂μ₂) *
          ψp (uv.1 * d + uv.2 * a) ∂((selfDualHaarAt ℚ p).prod (selfDualHaarAt ℚ p)) := by
  letI : MeasurableSpace F := localBorel ℚ p
  letI := localGLBorel ℚ p
  haveI := borelSpace_localGLBorel ℚ p
  intro μ₂ _
  obtain ⟨h0, h0'⟩ := level_zero p

  let eτ : G ≃ᵐ G :=
    (Homeomorph.mk ⟨tauW p, tauW p, tauW_tauW p, tauW_tauW p⟩ (continuous_tauW p) (continuous_tauW p)).toMeasurableEquiv
  have heτ : ∀ k, eτ k = tauW p k := fun _ => rfl
  have hMPτ : MeasurePreserving eτ μ₂ μ₂ := ⟨eτ.measurable, map_tauW p μ₂⟩
  have hpre : eτ ⁻¹' K0 = K0 := tauW_preimage_K0 p
  have hsub := hMPτ.setIntegral_preimage_emb eτ.measurableEmbedding
    (fun k : G => Fsec (w0 p * transposeInvN (Fin 2) k * w0 p) *
        ((χ⁻¹ (Matrix.GeneralLinearGroup.det k) : ℂˣ) : ℂ) *
        (∫ x : F, matFourier22 p ψp (PhiC p Φ) (!![a, x; 0, d] * (k : Mat)) ∂(selfDualHaarAt ℚ p))) K0
  rw [hpre] at hsub
  rw [← hsub]

  have hK0meas : MeasurableSet K0 :=
    (AdelicDock.isCompact_and_isOpen_localLevelOne ℚ p (⊤ : Ideal (𝓞 ℚ)) top_ne_bot).2.measurableSet
  rw [← fubini_slice p lam χ hχ Fsec hF Φ hlc hcs a d μ₂]
  refine setIntegral_congr_fun hK0meas fun k hk => ?_
  have hk' : k ∈ kzero p := hk
  simp only [heτ]

  have h1 : w0 p * transposeInvN (Fin 2) (tauW p k) * w0 p = k := conjW_transposeInvN_tauW p k
  have h2 : ((χ⁻¹ (Matrix.GeneralLinearGroup.det (tauW p k)) : ℂˣ) : ℂ) =
      ((χ (Matrix.GeneralLinearGroup.det k) : ℂˣ) : ℂ) := by
    rw [det_tauW, MonoidHom.inv_apply, map_inv, inv_inv]
  have h3 : ∀ x : F, matFourier22 p ψp (PhiC p Φ) (!![a, x; 0, d] * (tauW p k : Mat)) =
      matFourier22 p ψp (fun X : Mat => Φ (X * (k : Mat))) !![d, 0; x, a] := by
    intro x
    rw [matFourier22_PhiC p Φ ⟨hlc, hcs⟩, coe_tauW,
      show (!![0, 1; 1, 0] : Mat) * (!![a, x; 0, d] * (!![0, 1; 1, 0] * ((k⁻¹ : G) : Mat).transpose * !![0, 1; 1, 0])) * !![0, 1; 1, 0]
        = (!![0, 1; 1, 0] : Mat) * !![a, x; 0, d] * !![0, 1; 1, 0] * ((k⁻¹ : G) : Mat).transpose * (!![0, 1; 1, 0] * !![0, 1; 1, 0]) by
          simp only [mul_assoc],
      w0M_mul_w0M, mul_one, w0M_upper_w0M, ← coe_transposeInvN,
      LanglandsTunnell.CubicInduction.matFourier22_comp_mul_right_eq p ψp 0 h0 h0' Φ ⟨hlc, hcs⟩ k,
      modulus_det_of_mem_K0 p hk']
    simp
  simp_rw [h1, h2, h3]
  rw [LanglandsTunnell.CubicInduction.integral_matFourier22_lowerTriangular_eq_integral_integral_upperTriangular_mul_psiLocal
    p _ (isSchwartzBruhat_comp_mul_right p Φ ⟨hlc, hcs⟩ k) d a]

end U2Dual
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_integrable_and_godementZeta2_transposeInv_matFourier22_eq_mul_twoVarZeta_fourierSlice_of_mem_principalSeries2.U2Dual"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_integrable_and_godementZeta2_transposeInv_matFourier22_eq_mul_twoVarZeta_fourierSlice_of_mem_principalSeries2.U2Dual"

theorem solution
    (p : HeightOneSpectrum (𝓞 ℚ))
    (lam : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) (hlam : ∀ i, IsLocallyConstant (lam i))
    (χ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (hχ : IsLocallyConstant χ) :
    letI : MeasurableSpace (p.adicCompletion ℚ) := localBorel ℚ p
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure] (κ : ℝ), 0 < κ →
      (∀ G : GL (Fin 2) (p.adicCompletion ℚ) → ENNReal, Measurable G →
          ∫⁻ g, G g ∂μ₂ =
            ENNReal.ofReal κ *
              ∫⁻ q : GL (Fin 2) (p.adicCompletion ℚ) × ((p.adicCompletion ℚ)ˣ × (p.adicCompletion ℚ)ˣ),
                (∫⁻ x : (p.adicCompletion ℚ), G (unipotent x * diagUnits2 q.2.1 q.2.2 * q.1) ∂(selfDualHaarAt ℚ p)) *
                  (modulus ((q.2.2 * q.2.1⁻¹ : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ENNReal)
                ∂((μ₂.restrict (AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ : Set (GL (Fin 2) (p.adicCompletion ℚ)))).prod
                  ((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))).prod (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))))) →
      ∀ F ∈ principalSeries2 p lam,
      ∀ (Φ : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) → ℂ), IsLocallyConstant Φ → HasCompactSupport Φ →
        let ϕ : (p.adicCompletion ℚ) × (p.adicCompletion ℚ) → ℂ := fun ad =>
          ∫ k in (AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ : Set (GL (Fin 2) (p.adicCompletion ℚ))),
            F k * ((χ (Matrix.GeneralLinearGroup.det k) : ℂˣ) : ℂ) *
              (∫ x : (p.adicCompletion ℚ), Φ (!![ad.1, x; 0, ad.2] * (k : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ))) ∂(selfDualHaarAt ℚ p)) ∂μ₂
        let ϕhat : (p.adicCompletion ℚ) × (p.adicCompletion ℚ) → ℂ := fun xy =>
          ∫ uv : (p.adicCompletion ℚ) × (p.adicCompletion ℚ), ϕ uv * NumberField.StandardAddChar.psiLocal ℚ p (uv.1 * xy.1 + uv.2 * xy.2)
            ∂((selfDualHaarAt ℚ p).prod (selfDualHaarAt ℚ p))
        ∃ σd : ℝ, ∀ s : ℂ, σd < s.re →
          Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
            F (transposeInvN (Fin 2) g) *
              matFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p) Φ (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) *
              ((χ⁻¹ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
              ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (s + 3 / 2)) μ₂ ∧
          Integrable (fun ad : (p.adicCompletion ℚ)ˣ × (p.adicCompletion ℚ)ˣ =>
            ϕhat ((ad.1 : (p.adicCompletion ℚ)), (ad.2 : (p.adicCompletion ℚ))) *
              (((χ * lam 0)⁻¹ ad.1 : ℂˣ) : ℂ) * (((χ * lam 1)⁻¹ ad.2 : ℂˣ) : ℂ) *
              ((modulus (ad.1 : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (1 + s) * ((modulus (ad.2 : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (1 + s))
            ((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))).prod (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) ∧
          godementZeta2 p μ₂ (fun g : GL (Fin 2) (p.adicCompletion ℚ) => F (transposeInvN (Fin 2) g))
              (matFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p) Φ) χ⁻¹ (s + 3 / 2) =
            (κ : ℂ) *
              ∫ ad : (p.adicCompletion ℚ)ˣ × (p.adicCompletion ℚ)ˣ,
                ϕhat ((ad.1 : (p.adicCompletion ℚ)), (ad.2 : (p.adicCompletion ℚ))) *
                  (((χ * lam 0)⁻¹ ad.1 : ℂˣ) : ℂ) * (((χ * lam 1)⁻¹ ad.2 : ℂˣ) : ℂ) *
                  ((modulus (ad.1 : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (1 + s) * ((modulus (ad.2 : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (1 + s)
                ∂((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))).prod (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) := by
  letI : MeasurableSpace (p.adicCompletion ℚ) := localBorel ℚ p
  letI := localGLBorel ℚ p
  haveI := borelSpace_localGLBorel ℚ p
  intro μ₂ hμ κ hκ h3808 Fsec hF Φ hlc hcs
  dsimp only
  haveI : SigmaFinite (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)) : Measure (p.adicCompletion ℚ)ˣ) :=
    U2Dual.sigmaFinite_mulHaar p
  obtain ⟨h0, h0'⟩ := U2Dual.level_zero p

  have hinv : ∀ (f : (p.adicCompletion ℚ)ˣ →* ℂˣ), IsLocallyConstant f →
      IsLocallyConstant (f⁻¹ : (p.adicCompletion ℚ)ˣ →* ℂˣ) := by
    intro f hf
    have : ((f⁻¹ : (p.adicCompletion ℚ)ˣ →* ℂˣ) : (p.adicCompletion ℚ)ˣ → ℂˣ) = (fun y : ℂˣ => y⁻¹) ∘ f := rfl
    rw [this]; exact hf.comp _
  have hlam' : ∀ i, IsLocallyConstant ((![(lam 1)⁻¹, (lam 0)⁻¹] : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) i) := by
    intro i; fin_cases i
    · simpa using hinv _ (hlam 1)
    · simpa using hinv _ (hlam 0)
  set Fv : GL (Fin 2) (p.adicCompletion ℚ) → ℂ :=
    fun h => Fsec (U2Dual.w0 p * transposeInvN (Fin 2) h * U2Dual.w0 p) with hFvdef
  have hFv : Fv ∈ principalSeries2 p ![(lam 1)⁻¹, (lam 0)⁻¹] :=
    LanglandsTunnell.CubicInduction.conj_transposeInvN_mem_principalSeries2 p lam Fsec hF (U2Dual.w0 p) (U2Dual.w0_coe p)
  have hPhiC := U2Dual.isSchwartzBruhat_PhiC p Φ hlc hcs
  set Ψ : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) → ℂ :=
    matFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p) (U2Dual.PhiC p Φ) with hΨdef
  have hΨ : IsSchwartzBruhat Ψ :=
    LanglandsTunnell.CubicInduction.isSchwartzBruhat_matFourier22 p _ 0 h0 h0' _ hPhiC
  have hU := LanglandsTunnell.RankinSelberg.exists_forall_integrable_and_godementZeta2_eq_mul_twoVarZeta_slice_of_mem_principalSeries2
    p ![(lam 1)⁻¹, (lam 0)⁻¹] hlam' χ⁻¹ (hinv χ hχ) μ₂ κ hκ h3808 Fv hFv Ψ hΨ.1 hΨ.2
  dsimp only at hU
  obtain ⟨-, σ₀, hσ⟩ := hU
  refine ⟨σ₀ - 1, fun s hs => ?_⟩
  have hs' : σ₀ < (s + 1).re := by simp only [Complex.add_re, Complex.one_re]; linarith
  obtain ⟨hI1', hI2', hEQ'⟩ := hσ (s + 1) hs'

  let e : GL (Fin 2) (p.adicCompletion ℚ) ≃ᵐ GL (Fin 2) (p.adicCompletion ℚ) :=
    (Homeomorph.mk ⟨U2Dual.conjW p, U2Dual.conjW p, U2Dual.conjW_conjW p, U2Dual.conjW_conjW p⟩
      (U2Dual.continuous_conjW p) (U2Dual.continuous_conjW p)).toMeasurableEquiv
  have he : ∀ h, e h = U2Dual.conjW p h := fun _ => rfl
  have hmapE : Measure.map e μ₂ = μ₂ := U2Dual.map_conjW p μ₂
  have hMP : MeasurePreserving e μ₂ μ₂ := ⟨e.measurable, hmapE⟩

  have hpt : ∀ h : GL (Fin 2) (p.adicCompletion ℚ),
      Fsec (transposeInvN (Fin 2) (e h)) *
          matFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p) Φ ((e h : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) *
          ((χ⁻¹ (Matrix.GeneralLinearGroup.det (e h)) : ℂˣ) : ℂ) *
          ((modulus ((Matrix.GeneralLinearGroup.det (e h) : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (s + 3 / 2) =
        Fv h * Ψ (h : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) *
          ((χ⁻¹ (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ) *
          ((modulus ((Matrix.GeneralLinearGroup.det h : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (s + 1 + 1 / 2) := by
    intro h
    rw [he, U2Dual.transposeInvN_conjW, U2Dual.det_conjW, U2Dual.coe_conjW, ← U2Dual.matFourier22_PhiC p Φ ⟨hlc, hcs⟩,
      hFvdef, hΨdef, U2Dual.conjW_apply, show (s + 3 / 2 : ℂ) = s + 1 + 1 / 2 by ring]

  have hsl := fun (a d : p.adicCompletion ℚ) => U2Dual.slice_conj_eq p lam χ hχ Fsec hF Φ hlc hcs a d μ₂
  have hchar0 : (χ⁻¹ * (![(lam 1)⁻¹, (lam 0)⁻¹] : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) 0) = (χ * lam 1)⁻¹ := by
    ext y; simp [mul_comm]
  have hchar1 : (χ⁻¹ * (![(lam 1)⁻¹, (lam 0)⁻¹] : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) 1) = (χ * lam 0)⁻¹ := by
    ext y; simp [mul_comm]

  have hST : ∀ ad : (p.adicCompletion ℚ)ˣ × (p.adicCompletion ℚ)ˣ,
      (∫ k in (AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ : Set (GL (Fin 2) (p.adicCompletion ℚ))),
          Fv k * ((χ⁻¹ (Matrix.GeneralLinearGroup.det k) : ℂˣ) : ℂ) *
            (∫ x : (p.adicCompletion ℚ), Ψ (!![(ad.1 : (p.adicCompletion ℚ)), x; 0, (ad.2 : (p.adicCompletion ℚ))] * (k : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ))) ∂(selfDualHaarAt ℚ p)) ∂μ₂) *
        (((χ⁻¹ * (![(lam 1)⁻¹, (lam 0)⁻¹] : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) 0) ad.1 : ℂˣ) : ℂ) *
        (((χ⁻¹ * (![(lam 1)⁻¹, (lam 0)⁻¹] : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) 1) ad.2 : ℂˣ) : ℂ) *
        ((modulus (ad.1 : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (s + 1) * ((modulus (ad.2 : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (s + 1) =
      (fun ad : (p.adicCompletion ℚ)ˣ × (p.adicCompletion ℚ)ˣ =>
            (∫ uv : (p.adicCompletion ℚ) × (p.adicCompletion ℚ),
                (∫ k in (AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ : Set (GL (Fin 2) (p.adicCompletion ℚ))),
                    Fsec k * ((χ (Matrix.GeneralLinearGroup.det k) : ℂˣ) : ℂ) *
                      (∫ x : (p.adicCompletion ℚ), Φ (!![uv.1, x; 0, uv.2] * (k : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ))) ∂(selfDualHaarAt ℚ p)) ∂μ₂) *
                  NumberField.StandardAddChar.psiLocal ℚ p (uv.1 * (ad.1 : (p.adicCompletion ℚ)) + uv.2 * (ad.2 : (p.adicCompletion ℚ)))
                ∂((selfDualHaarAt ℚ p).prod (selfDualHaarAt ℚ p))) *
              (((χ * lam 0)⁻¹ ad.1 : ℂˣ) : ℂ) * (((χ * lam 1)⁻¹ ad.2 : ℂˣ) : ℂ) *
              ((modulus (ad.1 : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (1 + s) * ((modulus (ad.2 : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (1 + s)) ad.swap := by
    intro ad
    simp only [Prod.fst_swap, Prod.snd_swap, hchar0, hchar1, hFvdef, hΨdef]
    rw [hsl, add_comm s 1]
    ring
  refine ⟨?_, ?_, ?_⟩
  ·
    refine (hMP.integrable_comp_emb e.measurableEmbedding).1 ?_
    refine hI1'.congr (Filter.EventuallyEq.of_eq ?_)
    funext h
    simp only [Function.comp_apply]
    exact (hpt h).symm
  ·
    refine (integrable_swap_iff (f := fun ad : (p.adicCompletion ℚ)ˣ × (p.adicCompletion ℚ)ˣ =>
            (∫ uv : (p.adicCompletion ℚ) × (p.adicCompletion ℚ),
                (∫ k in (AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ : Set (GL (Fin 2) (p.adicCompletion ℚ))),
                    Fsec k * ((χ (Matrix.GeneralLinearGroup.det k) : ℂˣ) : ℂ) *
                      (∫ x : (p.adicCompletion ℚ), Φ (!![uv.1, x; 0, uv.2] * (k : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ))) ∂(selfDualHaarAt ℚ p)) ∂μ₂) *
                  NumberField.StandardAddChar.psiLocal ℚ p (uv.1 * (ad.1 : (p.adicCompletion ℚ)) + uv.2 * (ad.2 : (p.adicCompletion ℚ)))
                ∂((selfDualHaarAt ℚ p).prod (selfDualHaarAt ℚ p))) *
              (((χ * lam 0)⁻¹ ad.1 : ℂˣ) : ℂ) * (((χ * lam 1)⁻¹ ad.2 : ℂˣ) : ℂ) *
              ((modulus (ad.1 : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (1 + s) * ((modulus (ad.2 : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (1 + s))).1 ?_
    refine hI2'.congr (Filter.EventuallyEq.of_eq ?_)
    funext ad
    exact hST ad
  ·
    calc godementZeta2 p μ₂ (fun g : GL (Fin 2) (p.adicCompletion ℚ) => Fsec (transposeInvN (Fin 2) g))
            (matFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p) Φ) χ⁻¹ (s + 3 / 2)
        = ∫ g, Fsec (transposeInvN (Fin 2) g) *
            matFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p) Φ ((g : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) *
            ((χ⁻¹ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
            ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (s + 3 / 2) ∂μ₂ := by rw [godementZeta2_apply]
      _ = ∫ h, Fsec (transposeInvN (Fin 2) (e h)) *
            matFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p) Φ (((e h) : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) *
            ((χ⁻¹ (Matrix.GeneralLinearGroup.det (e h)) : ℂˣ) : ℂ) *
            ((modulus ((Matrix.GeneralLinearGroup.det (e h) : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (s + 3 / 2) ∂μ₂ :=
          (hMP.integral_comp e.measurableEmbedding (fun g : GL (Fin 2) (p.adicCompletion ℚ) => Fsec (transposeInvN (Fin 2) g) *
            matFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p) Φ ((g : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) *
            ((χ⁻¹ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
            ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (s + 3 / 2))).symm
      _ = ∫ h, Fv h * Ψ (h : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) *
            ((χ⁻¹ (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ) *
            ((modulus ((Matrix.GeneralLinearGroup.det h : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (s + 1 + 1 / 2) ∂μ₂ := by congr 1; funext h; exact hpt h
      _ = godementZeta2 p μ₂ Fv Ψ χ⁻¹ (s + 1 + 1 / 2) := by rw [godementZeta2_apply]
      _ = _ := hEQ'
      _ = _ := by
          congr 1
          rw [← integral_prod_swap (fun ad : (p.adicCompletion ℚ)ˣ × (p.adicCompletion ℚ)ˣ =>
            (∫ uv : (p.adicCompletion ℚ) × (p.adicCompletion ℚ),
                (∫ k in (AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ : Set (GL (Fin 2) (p.adicCompletion ℚ))),
                    Fsec k * ((χ (Matrix.GeneralLinearGroup.det k) : ℂˣ) : ℂ) *
                      (∫ x : (p.adicCompletion ℚ), Φ (!![uv.1, x; 0, uv.2] * (k : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ))) ∂(selfDualHaarAt ℚ p)) ∂μ₂) *
                  NumberField.StandardAddChar.psiLocal ℚ p (uv.1 * (ad.1 : (p.adicCompletion ℚ)) + uv.2 * (ad.2 : (p.adicCompletion ℚ)))
                ∂((selfDualHaarAt ℚ p).prod (selfDualHaarAt ℚ p))) *
              (((χ * lam 0)⁻¹ ad.1 : ℂˣ) : ℂ) * (((χ * lam 1)⁻¹ ad.2 : ℂˣ) : ℂ) *
              ((modulus (ad.1 : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (1 + s) * ((modulus (ad.2 : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (1 + s))]
          congr 1; funext ad; exact hST ad

end S_LanglandsTunnell_RankinSelberg_exists_forall_integrable_and_godementZeta2_transposeInv_matFourier22_eq_mul_twoVarZeta_fourierSlice_of_mem_principalSeries2
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_integrable_and_godementZeta2_transposeInv_matFourier22_eq_mul_twoVarZeta_fourierSlice_of_mem_principalSeries2 (solution)
