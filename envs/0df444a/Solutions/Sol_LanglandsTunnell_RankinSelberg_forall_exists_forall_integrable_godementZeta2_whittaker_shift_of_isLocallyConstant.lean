-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.forall_exists_forall_integrable_godementZeta2_whittaker_shift_of_isLocallyConstant
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/fa734613-663f-5dd4-9de1-a04152a02b34

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
import Definitions.Def_LanglandsTunnell_CubicInduction_GodementSection
import Definitions.Def_LanglandsTunnell_CubicInduction_Congruence
import Theorems.Thm_LanglandsTunnell_RankinSelberg_forall_exists_integrable_godementZeta2_whittaker_shift
import Theorems.Thm_AdelicDock_isCompact_and_isOpen_localLevelOne
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_forall_exists_forall_integrable_godementZeta2_whittaker_shift_of_isLocallyConstant
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "LanglandsTunnell.CubicInduction.halfModulus2_one LanglandsTunnell.CubicInduction.unipotentHom2_ofAdd LanglandsTunnell.CubicInduction.diagonal2_coe LanglandsTunnell.CubicInduction.upperUnipotent2_coe LanglandsTunnell.CubicInduction.torusChar2_one LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val"

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker LanglandsTunnell.Converse LanglandsTunnell.CubicInduction

open scoped nonZeroDivisors
open NumberField.AdelicLevel (diagOne)

open scoped Classical

namespace U1C46

noncomputable section

attribute [local instance] LanglandsTunnell.TateLocal.localBorel
attribute [local instance] LanglandsTunnell.TateLocal.borelSpace_localBorel
attribute [local instance] AutomorphicForm.localGLBorel
attribute [local instance] AutomorphicForm.borelSpace_localGLBorel

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => (HeightOneSpectrum.adicCompletion ℚ p)
local notation "G" => (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))
local notation "M2" => (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))

section Generic
variable {H : Type*} [Group H]

theorem law_of_mem_span (f : H → ℂ) (a : H) (χ : ℂ) (hf : ∀ g : H, f (a * g) = χ * f g) {W : H → ℂ}
    (hW : W ∈ Submodule.span ℂ (Set.range fun h' : H => fun g : H => f (g * h'))) :
    ∀ g : H, W (a * g) = χ * W g := by
  induction hW using Submodule.span_induction with
  | mem W hWm =>
      obtain ⟨h', rfl⟩ := hWm
      intro g
      show f (a * g * h') = χ * f (g * h')
      rw [mul_assoc, hf]
  | zero => intro g; simp
  | add W₁ W₂ _ _ h₁ h₂ => intro g; simp only [Pi.add_apply, h₁ g, h₂ g]; ring
  | smul c W _ h₁ => intro g; simp only [Pi.smul_apply, smul_eq_mul, h₁ g]; ring

variable [TopologicalSpace H] [ContinuousMul H]

theorem exists_open_stabilizer_of_mem_span (f : H → ℂ) (K : Subgroup H) (hK : IsOpen (K : Set H))
    (hf : ∀ k ∈ K, ∀ g : H, f (g * k) = f g) {W : H → ℂ}
    (hW : W ∈ Submodule.span ℂ (Set.range fun h' : H => fun g : H => f (g * h'))) :
    ∃ U : Subgroup H, IsOpen (U : Set H) ∧ ∀ k ∈ U, ∀ g : H, W (g * k) = W g := by
  induction hW using Submodule.span_induction with
  | mem W hWm =>
      obtain ⟨h, rfl⟩ := hWm
      refine ⟨K.comap (MulAut.conj h⁻¹).toMonoidHom, ?_, ?_⟩
      · have hc : Continuous fun k : H => h⁻¹ * k * h⁻¹⁻¹ :=
          (continuous_const.mul continuous_id).mul continuous_const
        have hset : ((K.comap (MulAut.conj h⁻¹).toMonoidHom : Subgroup H) : Set H) =
            (fun k : H => h⁻¹ * k * h⁻¹⁻¹) ⁻¹' (K : Set H) := by
          ext k
          simp only [Subgroup.coe_comap, Set.mem_preimage, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
            SetLike.mem_coe]
        rw [hset]
        exact hK.preimage hc
      · intro k hk g
        rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at hk
        show f (g * k * h) = f (g * h)
        rw [show g * k * h = g * h * (h⁻¹ * k * h) by simp only [mul_assoc, mul_inv_cancel_left]]
        exact hf _ hk (g * h)
  | zero => exact ⟨⊤, by simp, fun _ _ _ => rfl⟩
  | add W₁ W₂ _ _ h₁ h₂ =>
      obtain ⟨U₁, hU₁, hW₁⟩ := h₁
      obtain ⟨U₂, hU₂, hW₂⟩ := h₂
      refine ⟨U₁ ⊓ U₂, ?_, ?_⟩
      · rw [Subgroup.coe_inf]; exact hU₁.inter hU₂
      · intro k hk g
        rw [Subgroup.mem_inf] at hk
        simp only [Pi.add_apply, hW₁ k hk.1 g, hW₂ k hk.2 g]
  | smul c W _ h₁ =>
      obtain ⟨U, hU, hWU⟩ := h₁
      exact ⟨U, hU, fun k hk g => by simp only [Pi.smul_apply, hWU k hk g]⟩

theorem continuous_of_open_stabilizer (f : H → ℂ) (U : Subgroup H) (hUo : IsOpen (U : Set H))
    (hU : ∀ k ∈ U, ∀ g : H, f (g * k) = f g) : Continuous f := by
  refine continuous_def.2 fun s _ => ?_
  rw [isOpen_iff_forall_mem_open]
  intro g hg
  refine ⟨(fun k => g * k) '' (U : Set H), ?_, ?_, ⟨1, U.one_mem, mul_one g⟩⟩
  · rintro _ ⟨k, hk, rfl⟩
    show f (g * k) ∈ s
    rw [hU k hk g]; exact hg
  · exact (Homeomorph.mulLeft g).isOpenMap _ hUo

end Generic

theorem one_lt_qN : (1 : NNReal) < (Ideal.absNorm p.asIdeal : NNReal) :=
  NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal p

theorem norm_le_norm_iff_v_le_v (x y : F) : ‖x‖ ≤ ‖y‖ ↔ Valued.v x ≤ Valued.v y := by
  rw [NumberField.FinitePlace.norm_def, NumberField.FinitePlace.norm_def, NNReal.coe_le_coe,
    (WithZeroMulInt.toNNReal_strictMono (one_lt_qN p)).le_iff_le]

theorem norm_lt_norm_iff_v_lt_v (x y : F) : ‖x‖ < ‖y‖ ↔ Valued.v x < Valued.v y := by
  rw [NumberField.FinitePlace.norm_def, NumberField.FinitePlace.norm_def, NNReal.coe_lt_coe,
    (WithZeroMulInt.toNNReal_strictMono (one_lt_qN p)).lt_iff_lt]

theorem coe_modulus_eq_norm (x : F) : ((modulus x : NNReal) : ℝ) = ‖x‖ := by
  rw [LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm]; rfl

theorem exists_uniformizer : ∃ ϖ : F, Valued.v ϖ = WithZero.exp (-1 : ℤ) := by
  obtain ⟨π, hπ⟩ := HeightOneSpectrum.valuation_exists_uniformizer ℚ p
  exact ⟨((WithVal.equiv (HeightOneSpectrum.valuation ℚ p)).symm π : F),
    by rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']; exact hπ⟩

theorem v_uniformizer_zpow {ϖ : F} (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) (j : ℤ) : Valued.v (ϖ ^ j) = WithZero.exp (-j) := by
  rw [map_zpow₀, hϖ, ← WithZero.exp_zsmul]
  congr 1
  simp

theorem uniformizer_ne_zero {ϖ : F} (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) : ϖ ≠ 0 := by
  intro h; rw [h, Valuation.map_zero] at hϖ; exact WithZero.exp_ne_zero hϖ.symm

theorem isOpen_vball (m : ℤ) : IsOpen {x : F | Valued.v x ≤ WithZero.exp m} := by
  obtain ⟨ϖ, hϖ⟩ := exists_uniformizer p
  have hset : {x : F | Valued.v x ≤ WithZero.exp m} =
      (fun x => ϖ ^ m * x) ⁻¹' (HeightOneSpectrum.adicCompletionIntegers ℚ p : Set F) := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_preimage, SetLike.mem_coe,
      HeightOneSpectrum.mem_adicCompletionIntegers, Valuation.map_mul, v_uniformizer_zpow p hϖ, WithZero.exp_neg]
    constructor
    · intro h
      calc (WithZero.exp m)⁻¹ * Valued.v x ≤ (WithZero.exp m)⁻¹ * WithZero.exp m := mul_le_mul_right h _
        _ = 1 := inv_mul_cancel₀ WithZero.exp_ne_zero
    · intro h
      calc Valued.v x = WithZero.exp m * ((WithZero.exp m)⁻¹ * Valued.v x) := by
            rw [← mul_assoc, mul_inv_cancel₀ WithZero.exp_ne_zero, one_mul]
        _ ≤ WithZero.exp m * 1 := mul_le_mul_right h _
        _ = WithZero.exp m := mul_one _
  rw [hset]
  exact (Valued.isOpen_valuationSubring _).preimage (continuous_const_mul _)

theorem isClosed_vball (γ : WithZero (Multiplicative ℤ)) : IsClosed {x : F | Valued.v x ≤ γ} := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro x hx
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le] at hx
  have hx0 : (Valued.v x : WithZero (Multiplicative ℤ)) ≠ 0 := ne_of_gt (lt_of_le_of_lt zero_le' hx)
  filter_upwards [Valued.locally_const hx0] with y hy
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le, hy]; exact hx

theorem isCompact_integers : IsCompact ((HeightOneSpectrum.adicCompletionIntegers ℚ p : Set F)) := by
  rw [← LanglandsTunnell.TateLocal.coe_integersPositiveCompacts]
  exact (LanglandsTunnell.TateLocal.integersPositiveCompacts ℚ p).isCompact

theorem isCompact_vball (m : ℤ) : IsCompact {x : F | Valued.v x ≤ WithZero.exp m} := by
  obtain ⟨ϖ, hϖ⟩ := exists_uniformizer p
  have hϖ0 := uniformizer_ne_zero p hϖ
  have hset : {x : F | Valued.v x ≤ WithZero.exp m} =
      (fun x => ϖ ^ (-m) * x) '' (HeightOneSpectrum.adicCompletionIntegers ℚ p : Set F) := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_image, SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers]
    constructor
    · intro h
      refine ⟨ϖ ^ m * x, ?_, ?_⟩
      · rw [Valuation.map_mul, v_uniformizer_zpow p hϖ, WithZero.exp_neg]
        calc (WithZero.exp m)⁻¹ * Valued.v x ≤ (WithZero.exp m)⁻¹ * WithZero.exp m := mul_le_mul_right h _
          _ = 1 := inv_mul_cancel₀ WithZero.exp_ne_zero
      · rw [← mul_assoc, ← zpow_add₀ hϖ0, neg_add_cancel, zpow_zero, one_mul]
    · rintro ⟨y, hy, rfl⟩
      rw [Valuation.map_mul, v_uniformizer_zpow p hϖ, neg_neg]
      calc WithZero.exp m * Valued.v y ≤ WithZero.exp m * 1 := mul_le_mul_right hy _
        _ = WithZero.exp m := mul_one _
  rw [hset]
  exact (isCompact_integers p).image (continuous_const_mul _)

theorem exists_nat_of_norm_bound (B : ℝ) : ∃ R : ℕ, ∀ x : F, ‖x‖ ≤ B → Valued.v x ≤ WithZero.exp (R : ℤ) := by
  obtain ⟨ϖ, hϖ⟩ := exists_uniformizer p
  have hinv : 1 < ‖ϖ⁻¹‖ := by
    rw [← norm_one (α := F), norm_lt_norm_iff_v_lt_v, map_inv₀, hϖ, Valuation.map_one, ← WithZero.exp_neg, ← WithZero.exp_zero,
      WithZero.exp_lt_exp]
    omega
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt B hinv
  refine ⟨n, fun x hx => ?_⟩
  have : ‖x‖ ≤ ‖ϖ⁻¹ ^ n‖ := by rw [norm_pow]; exact le_trans hx hn.le
  rw [norm_le_norm_iff_v_le_v, ← zpow_natCast, inv_zpow', v_uniformizer_zpow p hϖ, neg_neg] at this
  exact this

def boxM (R : ℤ) : Set M2 := {X : M2 | ∀ i j : Fin 2, Valued.v (X i j) ≤ WithZero.exp R}

theorem continuous_entry (i j : Fin 2) : Continuous fun X : M2 => X i j := continuous_id.matrix_elem i j

theorem boxM_eq (R : ℤ) : boxM p R = ⋂ i : Fin 2, ⋂ j : Fin 2, (fun X : M2 => X i j) ⁻¹' {x : F | Valued.v x ≤ WithZero.exp R} := by
  ext X; simp [boxM]

theorem isOpen_boxM (R : ℤ) : IsOpen (boxM p R) := by
  rw [boxM_eq]
  exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => (isOpen_vball p R).preimage (continuous_entry p i j)

theorem isClosed_boxM (R : ℤ) : IsClosed (boxM p R) := by
  rw [boxM_eq]
  exact isClosed_iInter fun i => isClosed_iInter fun j => (isClosed_vball p _).preimage (continuous_entry p i j)

theorem isCompact_boxM (R : ℤ) : IsCompact (boxM p R) := by
  have h := isCompact_univ_pi (fun (_ : Fin 2) => isCompact_univ_pi (fun (_ : Fin 2) => isCompact_vball p R))
  have hset : boxM p R = Set.pi Set.univ (fun (_ : Fin 2) => Set.pi Set.univ (fun (_ : Fin 2) => {x : F | Valued.v x ≤ WithZero.exp R})) := by
    ext X
    constructor
    · intro hX i _ j _; exact hX i j
    · intro hX i j; exact hX i (Set.mem_univ i) j (Set.mem_univ j)
  rw [hset]; exact h

def ind (R : ℤ) : M2 → ℂ := fun X => Set.indicator (boxM p R) (fun _ => (1 : ℂ)) X

theorem isLocallyConstant_ind (R : ℤ) : IsLocallyConstant (ind p R) := by
  intro s
  rw [isOpen_iff_mem_nhds]
  intro X hX
  by_cases hXS : X ∈ boxM p R
  · refine Filter.mem_of_superset ((isOpen_boxM p R).mem_nhds hXS) fun Y hY => ?_
    simp only [ind, Set.mem_preimage, Set.indicator_of_mem hXS] at hX
    simp only [ind, Set.mem_preimage, Set.indicator_of_mem hY]; exact hX
  · refine Filter.mem_of_superset ((isClosed_boxM p R).isOpen_compl.mem_nhds hXS) fun Y hY => ?_
    have hY' : Y ∉ boxM p R := hY
    simp only [ind, Set.mem_preimage, Set.indicator_of_notMem hXS] at hX
    simp only [ind, Set.mem_preimage, Set.indicator_of_notMem hY']; exact hX

theorem hasCompactSupport_ind (R : ℤ) : HasCompactSupport (ind p R) :=
  HasCompactSupport.intro (isCompact_boxM p R) fun X hX => Set.indicator_of_notMem hX _

theorem norm_ind (R : ℤ) (X : M2) : ‖ind p R X‖ = Set.indicator (boxM p R) (fun _ => (1 : ℝ)) X := by
  by_cases hX : X ∈ boxM p R
  · simp only [ind, Set.indicator_of_mem hX, norm_one]
  · simp only [ind, Set.indicator_of_notMem hX, norm_zero]

theorem coe_scalar_mul (z : Fˣ) (g : G) (i j : Fin 2) :
    ((Matrix.GeneralLinearGroup.scalar (Fin 2) z * g : G) : M2) i j = (z : F) * (g : M2) i j := by
  rw [Matrix.GeneralLinearGroup.coe_mul]
  show (Matrix.scalar (Fin 2) (z : F) * (g : M2)) i j = _
  rw [Matrix.scalar_apply, Matrix.diagonal_mul]

theorem det_scalar_mul (z : Fˣ) (g : G) :
    Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g : G) = z * z * Matrix.GeneralLinearGroup.det g := by
  rw [map_mul]
  congr 1
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_mul]
  show (Matrix.scalar (Fin 2) (z : F)).det = _
  rw [Matrix.scalar_apply, Matrix.det_diagonal]
  simp [Fin.prod_univ_two, pow_two]

theorem ind_scalar_mul {ϖ : F} (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) (k : ℕ) (g : G) :
    ind p (k : ℤ) ((Matrix.GeneralLinearGroup.scalar (Fin 2) ((Units.mk0 ϖ (uniformizer_ne_zero p hϖ))⁻¹ ^ k) * g : G) : M2) =
      ind p 0 ((g : G) : M2) := by
  have hz : Valued.v ((((Units.mk0 ϖ (uniformizer_ne_zero p hϖ))⁻¹ ^ k : Fˣ)) : F) = WithZero.exp (k : ℤ) := by
    rw [Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, Units.val_mk0, map_pow, map_inv₀, hϖ, ← WithZero.exp_neg, neg_neg,
      ← WithZero.exp_nsmul]
    simp
  have hiff : ((Matrix.GeneralLinearGroup.scalar (Fin 2) ((Units.mk0 ϖ (uniformizer_ne_zero p hϖ))⁻¹ ^ k) * g : G) : M2) ∈ boxM p (k : ℤ) ↔
      ((g : G) : M2) ∈ boxM p 0 := by
    simp only [boxM, Set.mem_setOf_eq, coe_scalar_mul, Valuation.map_mul, hz]
    constructor
    · intro h i j
      have h1 := h i j
      calc Valued.v (((g : G) : M2) i j) = (WithZero.exp (k : ℤ))⁻¹ * (WithZero.exp (k : ℤ) * Valued.v (((g : G) : M2) i j)) := by
            rw [← mul_assoc, inv_mul_cancel₀ WithZero.exp_ne_zero, one_mul]
        _ ≤ (WithZero.exp (k : ℤ))⁻¹ * WithZero.exp (k : ℤ) := mul_le_mul_right h1 _
        _ = WithZero.exp 0 := by rw [inv_mul_cancel₀ WithZero.exp_ne_zero, WithZero.exp_zero]
    · intro h i j
      calc WithZero.exp (k : ℤ) * Valued.v (((g : G) : M2) i j) ≤ WithZero.exp (k : ℤ) * WithZero.exp 0 := mul_le_mul_right (h i j) _
        _ = WithZero.exp (k : ℤ) := by rw [WithZero.exp_zero, mul_one]
  by_cases hg : ((g : G) : M2) ∈ boxM p 0
  · simp only [ind, Set.indicator_of_mem hg, Set.indicator_of_mem (hiff.2 hg)]
  · simp only [ind, Set.indicator_of_notMem hg, Set.indicator_of_notMem (fun h => hg (hiff.1 h))]

end

end U1C46

open U1C46 in
set_option maxHeartbeats 3200000 in
theorem solution
    (p : HeightOneSpectrum (𝓞 ℚ))
    (θ₀ : (p.adicCompletion ℚ)ˣ →* ℂˣ)
    (N : Ideal (𝓞 ℚ)) (hN : N ≠ ⊥)
    (w₂base : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hw₂law : ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w₂base (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * w₂base g)
    (hw₂K : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w₂base (g * k) = w₂base g)
    (hw₂ne : w₂base ≠ 0)
    (hw₂irr : ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      w ≠ 0 → w₂base ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w (g * h)))
    (hw₂adm : ∀ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) →
      ∃ B : Finset (GL (Fin 2) (p.adicCompletion ℚ) → ℂ),
        ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
          (∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w (g * k) = w g) →
            w ∈ Submodule.span ℂ (B : Set (GL (Fin 2) (p.adicCompletion ℚ) → ℂ)))
    (hcentral : ∀ (z : (p.adicCompletion ℚ)ˣ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w₂base (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((θ₀ z : ℂˣ) : ℂ) * w₂base g)
    (χ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (hχ : IsLocallyConstant χ) :
    letI := localBorel ℚ p
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure],
      ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
        ∀ s₀ : ℂ,
          ∃ σ : ℝ, ∀ (Φ : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) → ℂ), IsLocallyConstant Φ → HasCompactSupport Φ →
            ∀ s : ℂ, σ < s.re →
              Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                w g * Φ (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) * ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
                  ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s + s₀)) μ₂ := by
  letI : MeasurableSpace (p.adicCompletion ℚ) := localBorel ℚ p
  haveI : BorelSpace (p.adicCompletion ℚ) := borelSpace_localBorel ℚ p
  letI : MeasurableSpace (GL (Fin 2) (p.adicCompletion ℚ)) := localGLBorel ℚ p
  haveI : BorelSpace (GL (Fin 2) (p.adicCompletion ℚ)) := borelSpace_localGLBorel ℚ p
  intro μ₂ _ w hw s₀

  obtain ⟨σ, hσ⟩ := LanglandsTunnell.RankinSelberg.forall_exists_integrable_godementZeta2_whittaker_shift p θ₀ N hN w₂base hw₂law hw₂K hw₂ne
    hw₂irr hw₂adm hcentral χ hχ μ₂ w hw (ind p 0) (isLocallyConstant_ind p 0) (hasCompactSupport_ind p 0) s₀
  refine ⟨σ, fun Φ hΦlc hΦcs s hs => ?_⟩
  obtain ⟨ϖ, hϖ⟩ := exists_uniformizer p
  set zu : (p.adicCompletion ℚ)ˣ := (Units.mk0 ϖ (uniformizer_ne_zero p hϖ))⁻¹ with hzu

  have hcentralW : ∀ (z : (p.adicCompletion ℚ)ˣ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((θ₀ z : ℂˣ) : ℂ) * w g :=
    fun z => law_of_mem_span w₂base _ _ (hcentral z) hw
  obtain ⟨-, hKo⟩ := AdelicDock.isCompact_and_isOpen_localLevelOne ℚ p N hN
  obtain ⟨U, hUo, hU⟩ := exists_open_stabilizer_of_mem_span w₂base (AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N) hKo hw₂K hw
  have hwc : Continuous w := continuous_of_open_stabilizer w U hUo hU

  obtain ⟨MΦ, hMΦ⟩ := hΦlc.continuous.bounded_above_of_compact_support hΦcs
  have hMΦ0 : 0 ≤ MΦ := le_trans (norm_nonneg _) (hMΦ 0)
  have hbox : ∃ k : ℕ, tsupport Φ ⊆ boxM p (k : ℤ) := by
    have hK : IsCompact (tsupport Φ) := hΦcs
    have hij : ∀ i j : Fin 2, ∃ k : ℕ, ∀ X ∈ tsupport Φ, Valued.v (X i j) ≤ WithZero.exp (k : ℤ) := by
      intro i j
      obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn ((continuous_entry p i j).continuousOn)
      obtain ⟨k, hk⟩ := exists_nat_of_norm_bound p B
      exact ⟨k, fun X hX => hk _ (hB X hX)⟩
    choose kf hkf using hij
    refine ⟨Finset.univ.sup fun ij : Fin 2 × Fin 2 => kf ij.1 ij.2, fun X hX i j => le_trans (hkf i j X hX) ?_⟩
    rw [WithZero.exp_le_exp]
    exact_mod_cast Finset.le_sup (f := fun ij : Fin 2 × Fin 2 => kf ij.1 ij.2) (Finset.mem_univ (i, j))
  obtain ⟨k, hk⟩ := hbox

  set T : ℤ → GL (Fin 2) (p.adicCompletion ℚ) → ℂ := fun R g =>
      w g * ind p R (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) * ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
        ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s + s₀) with hT
  have hT0 : Integrable (T 0) μ₂ := hσ s hs
  have hzk : 0 < ‖(((zu ^ k * zu ^ k : (p.adicCompletion ℚ)ˣ)) : p.adicCompletion ℚ)‖ := norm_pos_iff.2 (zu ^ k * zu ^ k).ne_zero
  set C : ℂ := ((θ₀ (zu ^ k) : ℂˣ) : ℂ) * ((χ (zu ^ k * zu ^ k) : ℂˣ) : ℂ) *
      ((‖(((zu ^ k * zu ^ k : (p.adicCompletion ℚ)ˣ)) : p.adicCompletion ℚ)‖ : ℝ) : ℂ) ^ (s + s₀) with hC
  have hscale : (fun g : GL (Fin 2) (p.adicCompletion ℚ) => T k (Matrix.GeneralLinearGroup.scalar (Fin 2) (zu ^ k) * g)) =
      fun g => C * T 0 g := by
    funext g
    simp only [hT]
    rw [hcentralW, hzu, ind_scalar_mul p hϖ k g, ← hzu, det_scalar_mul, map_mul,
      Units.val_mul (χ (zu ^ k * zu ^ k)) (χ (Matrix.GeneralLinearGroup.det g)),
      show (((zu ^ k * zu ^ k * Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ)) : p.adicCompletion ℚ) =
        ((zu ^ k * zu ^ k : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) * ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ)
        from Units.val_mul _ _, modulus_mul]
    have hpos1 : 0 ≤ ((modulus (((zu ^ k * zu ^ k : (p.adicCompletion ℚ)ˣ)) : p.adicCompletion ℚ) : ℝ)) := NNReal.coe_nonneg _
    have hpos2 : 0 ≤ ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ)) := NNReal.coe_nonneg _
    rw [NNReal.coe_mul, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hpos1 hpos2,
      coe_modulus_eq_norm p (((zu ^ k * zu ^ k : (p.adicCompletion ℚ)ˣ)) : p.adicCompletion ℚ)]
    simp only [hC]
    ring
  have hTk : Integrable (T k) μ₂ := by
    have h1 : Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) => T k (Matrix.GeneralLinearGroup.scalar (Fin 2) (zu ^ k) * g)) μ₂ := by
      rw [hscale]; exact hT0.const_mul C
    have h2 := h1.comp_mul_left (Matrix.GeneralLinearGroup.scalar (Fin 2) (zu ^ k))⁻¹
    have h3 : (fun t : GL (Fin 2) (p.adicCompletion ℚ) =>
        (fun g : GL (Fin 2) (p.adicCompletion ℚ) => T k (Matrix.GeneralLinearGroup.scalar (Fin 2) (zu ^ k) * g))
          ((Matrix.GeneralLinearGroup.scalar (Fin 2) (zu ^ k))⁻¹ * t)) = T k := by
      funext t; simp only [mul_inv_cancel_left]
    rw [h3] at h2
    exact h2

  have hmeas : AEStronglyMeasurable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
      w g * Φ (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) * ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
        ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s + s₀)) μ₂ := by
    have hdetR : Continuous fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ)) := by
      have : (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ))) =
          fun g => ‖((g : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)).det‖ := by
        funext g; rw [coe_modulus_eq_norm, Matrix.GeneralLinearGroup.val_det_apply]
      rw [this]; exact continuous_norm.comp Units.continuous_val.matrix_det
    refine (((hwc.measurable.mul (hΦlc.continuous.comp Units.continuous_val).measurable).mul
      (Units.continuous_val.comp (hχ.continuous.comp Matrix.GeneralLinearGroup.continuous_det)).measurable).mul
      ((Complex.measurable_ofReal.comp hdetR.measurable).pow_const _)).aestronglyMeasurable
  refine Integrable.mono' (hTk.norm.const_mul MΦ) hmeas (Filter.Eventually.of_forall fun g => ?_)

  have hΦle : ‖Φ (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ))‖ ≤ MΦ * ‖ind p k (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ))‖ := by
    rw [norm_ind]
    by_cases hg : ((g : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) ∈ boxM p (k : ℤ)
    · rw [Set.indicator_of_mem hg, mul_one]; exact hMΦ _
    · rw [Set.indicator_of_notMem hg, mul_zero, image_eq_zero_of_notMem_tsupport (fun h => hg (hk h)), norm_zero]
  simp only [hT, norm_mul]
  calc ‖w g‖ * ‖Φ (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ))‖ * ‖((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)‖ *
        ‖(((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ)) ^ (s + s₀)‖
      ≤ ‖w g‖ * (MΦ * ‖ind p k (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ))‖) * ‖((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)‖ *
        ‖(((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ)) ^ (s + s₀)‖ := by
        gcongr
    _ = MΦ * (‖w g‖ * ‖ind p k (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ))‖ * ‖((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)‖ *
        ‖(((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ)) ^ (s + s₀)‖) := by ring

end S_LanglandsTunnell_RankinSelberg_forall_exists_forall_integrable_godementZeta2_whittaker_shift_of_isLocallyConstant
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_forall_exists_forall_integrable_godementZeta2_whittaker_shift_of_isLocallyConstant (solution)
