-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.exists_schwartz_godementZeta2_whittaker_eq_mul_torusZeta_and_dual_of_integrable
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/34bcf641-9a86-54a3-be52-cdaee367b34c

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
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Theorems.Thm_LanglandsTunnell_RankinSelberg_godementZeta2_boxIndicator_eq_mul_torusZeta_of_isOpen_of_chart
import Theorems.Thm_LanglandsTunnell_RankinSelberg_godementZeta2_transposeInv_matFourier22_boxIndicator_eq_mul_torusZeta_dual_of_integrable_of_chart
import Theorems.Thm_AdelicDock_isCompact_and_isOpen_localLevelOne
import Theorems.Thm_AutomorphicForm_WhittakerModel_exists_forall_diagOne_eq_zero_of_lt_modulus
import Theorems.Thm_AutomorphicForm_exists_haar_localGL2_eq_smul_map_unipotentGL2_mul_diagUnits2_mul_lowerUnipotentGL2
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Theorems.Thm_LanglandsTunnell_TateLocal_isHaarMeasure_comap_val_mulMeasure
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_exists_schwartz_godementZeta2_whittaker_eq_mul_torusZeta_and_dual_of_integrable
p2m_attr_erase "simp" "LanglandsTunnell.CubicInduction.halfModulus2_one LanglandsTunnell.CubicInduction.unipotentHom2_ofAdd LanglandsTunnell.CubicInduction.diagonal2_coe LanglandsTunnell.CubicInduction.upperUnipotent2_coe LanglandsTunnell.CubicInduction.torusChar2_one"

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker LanglandsTunnell.Converse LanglandsTunnell.CubicInduction

open scoped nonZeroDivisors
open NumberField.AdelicLevel (diagOne)

open scoped Classical

set_option maxHeartbeats 1600000

noncomputable section

namespace LRed46

section Generic

variable {G : Type*} [Group G]

theorem translate_mem_span (f : G → ℂ) (h : G) {W : G → ℂ}
    (hW : W ∈ Submodule.span ℂ (Set.range fun h' : G => fun g : G => f (g * h'))) :
    (fun g : G => W (g * h)) ∈ Submodule.span ℂ (Set.range fun h' : G => fun g : G => f (g * h')) := by
  induction hW using Submodule.span_induction with
  | mem W hWm =>
      obtain ⟨h', rfl⟩ := hWm
      exact Submodule.subset_span ⟨h * h', funext fun g => by simp only [mul_assoc]⟩
  | zero => exact Submodule.zero_mem _
  | add W₁ W₂ _ _ h₁ h₂ =>
      have : (fun g : G => (W₁ + W₂) (g * h)) = (fun g : G => W₁ (g * h)) + fun g : G => W₂ (g * h) := rfl
      rw [this]; exact Submodule.add_mem _ h₁ h₂
  | smul a W _ h₁ =>
      have : (fun g : G => (a • W) (g * h)) = a • fun g : G => W (g * h) := rfl
      rw [this]; exact Submodule.smul_mem _ a h₁

theorem law_of_mem_span (f : G → ℂ) (a : G) (χ : ℂ) (hf : ∀ g : G, f (a * g) = χ * f g) {W : G → ℂ}
    (hW : W ∈ Submodule.span ℂ (Set.range fun h' : G => fun g : G => f (g * h'))) :
    ∀ g : G, W (a * g) = χ * W g := by
  induction hW using Submodule.span_induction with
  | mem W hWm =>
      obtain ⟨h', rfl⟩ := hWm
      intro g
      show f (a * g * h') = χ * f (g * h')
      rw [mul_assoc, hf]
  | zero => intro g; simp
  | add W₁ W₂ _ _ h₁ h₂ => intro g; simp only [Pi.add_apply, h₁ g, h₂ g]; ring
  | smul c W _ h₁ => intro g; simp only [Pi.smul_apply, smul_eq_mul, h₁ g]; ring

variable [TopologicalSpace G] [ContinuousMul G]

theorem exists_open_stabilizer_of_mem_span (f : G → ℂ) (K : Subgroup G) (hK : IsOpen (K : Set G))
    (hf : ∀ k ∈ K, ∀ g : G, f (g * k) = f g) {W : G → ℂ}
    (hW : W ∈ Submodule.span ℂ (Set.range fun h' : G => fun g : G => f (g * h'))) :
    ∃ U : Subgroup G, IsOpen (U : Set G) ∧ ∀ k ∈ U, ∀ g : G, W (g * k) = W g := by
  induction hW using Submodule.span_induction with
  | mem W hWm =>
      obtain ⟨h, rfl⟩ := hWm
      refine ⟨K.comap (MulAut.conj h⁻¹).toMonoidHom, ?_, ?_⟩
      · have hc : Continuous fun k : G => h⁻¹ * k * h⁻¹⁻¹ :=
          (continuous_const.mul continuous_id).mul continuous_const
        have hset : ((K.comap (MulAut.conj h⁻¹).toMonoidHom : Subgroup G) : Set G) =
            (fun k : G => h⁻¹ * k * h⁻¹⁻¹) ⁻¹' (K : Set G) := by
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

end Generic

section Local

attribute [local instance] LanglandsTunnell.TateLocal.localBorel
attribute [local instance] LanglandsTunnell.TateLocal.borelSpace_localBorel
attribute [local instance] AutomorphicForm.localGLBorel
attribute [local instance] AutomorphicForm.borelSpace_localGLBorel

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => (HeightOneSpectrum.adicCompletion ℚ p)
local notation "O" => (HeightOneSpectrum.adicCompletionIntegers ℚ p)
local notation "G" => (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))
local notation "M2" => (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))

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

theorem exists_ball_subset {s : Set F} (hs : s ∈ nhds (0 : F)) : ∃ M : ℤ, 0 ≤ M ∧ {x : F | Valued.v x ≤ WithZero.exp (-M)} ⊆ s := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hs
  obtain ⟨ϖ, hϖ⟩ := exists_uniformizer p
  have hϖ1 : ‖ϖ‖ < 1 := by
    rw [← norm_one (α := F), norm_lt_norm_iff_v_lt_v, hϖ, Valuation.map_one, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    omega
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε hϖ1
  refine ⟨n, by omega, fun x hx => hball ?_⟩
  rw [Metric.mem_ball, dist_zero_right]
  have hx' : Valued.v x ≤ Valued.v (ϖ ^ n) := by
    rw [← zpow_natCast, v_uniformizer_zpow p hϖ]; exact hx
  calc ‖x‖ ≤ ‖ϖ ^ n‖ := (norm_le_norm_iff_v_le_v p _ _).2 hx'
    _ = ‖ϖ‖ ^ n := norm_pow _ _
    _ < ε := hn

theorem exists_prinUnits_subset {s : Set Fˣ} (hs : s ∈ nhds (1 : Fˣ)) :
    ∃ M : ℤ, 1 ≤ M ∧ {a : Fˣ | Valued.v ((a : F) - 1) ≤ WithZero.exp (-M)} ⊆ s := by
  rw [(Units.isEmbedding_val₀ (G₀ := HeightOneSpectrum.adicCompletion ℚ p)).isInducing.nhds_eq_comap, Filter.mem_comap] at hs
  obtain ⟨t, ht, hts⟩ := hs
  rw [Units.val_one] at ht
  have ht0 : (fun x : F => 1 + x) ⁻¹' t ∈ nhds (0 : F) :=
    (continuous_const.add continuous_id).continuousAt.preimage_mem_nhds (by simpa using ht)
  obtain ⟨M, hM, hMt⟩ := exists_ball_subset p ht0
  refine ⟨max M 1, le_max_right _ _, fun a ha => hts ?_⟩
  show (a : F) ∈ t
  have : (a : F) - 1 ∈ (fun x : F => 1 + x) ⁻¹' t := by
    refine hMt ?_
    show Valued.v ((a : F) - 1) ≤ WithZero.exp (-M)
    exact le_trans ha (by rw [WithZero.exp_le_exp]; omega)
  simpa using this

theorem exists_exp_of_modulus_bound {P : Fˣ → Prop} (h : ∃ c : ℝ, 0 < c ∧ ∀ y : Fˣ, c < modulus (y : F) → P y) :
    ∃ L : ℤ, 0 ≤ L ∧ ∀ y : Fˣ, WithZero.exp L < Valued.v (y : F) → P y := by
  obtain ⟨c, hc, hP⟩ := h
  obtain ⟨ϖ, hϖ⟩ := exists_uniformizer p
  have hϖ0 := uniformizer_ne_zero p hϖ
  have hinv : 1 < ‖ϖ⁻¹‖ := by
    rw [← norm_one (α := F), norm_lt_norm_iff_v_lt_v, map_inv₀, hϖ, Valuation.map_one, ← WithZero.exp_neg, ← WithZero.exp_zero,
      WithZero.exp_lt_exp]
    omega
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt c hinv
  refine ⟨n, by omega, fun y hy => hP y ?_⟩

  have hy0 : (Valued.v (y : F) : WithZero (Multiplicative ℤ)) ≠ 0 := (Valuation.ne_zero_iff _).2 y.ne_zero
  have hge : WithZero.exp ((n : ℤ) + 1) ≤ Valued.v (y : F) := by
    rw [← WithZero.exp_log hy0] at hy ⊢
    rw [WithZero.exp_lt_exp] at hy
    rw [WithZero.exp_le_exp]; omega
  have hnorm : ‖ϖ⁻¹‖ ^ (n + 1) ≤ ‖(y : F)‖ := by
    rw [← norm_pow, ← zpow_natCast, inv_zpow', norm_le_norm_iff_v_le_v, v_uniformizer_zpow p hϖ, neg_neg]
    exact_mod_cast hge
  rw [coe_modulus_eq_norm]
  calc c < ‖ϖ⁻¹‖ ^ n := hn
    _ ≤ ‖ϖ⁻¹‖ ^ (n + 1) := pow_le_pow_right₀ hinv.le (Nat.le_succ n)
    _ ≤ ‖(y : F)‖ := hnorm

end Local

section GroupSide

attribute [local instance] LanglandsTunnell.TateLocal.localBorel
attribute [local instance] LanglandsTunnell.TateLocal.borelSpace_localBorel
attribute [local instance] AutomorphicForm.localGLBorel
attribute [local instance] AutomorphicForm.borelSpace_localGLBorel

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => (HeightOneSpectrum.adicCompletion ℚ p)
local notation "G" => (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))
local notation "M2" => (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))

theorem continuous_unipotentGL2' : Continuous (fun x : F => (unipotentGL2 x : G)) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · show Continuous fun x : F => (!![(1 : F), x; 0, 1] : M2)
    refine continuous_matrix ?_
    intro i j; fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  · show Continuous fun x : F => (!![(1 : F), -x; 0, 1] : M2)
    refine continuous_matrix ?_
    intro i j; fin_cases i <;> fin_cases j <;> simp <;> fun_prop

theorem continuous_lowerUnipotentGL2' : Continuous (fun y : F => (lowerUnipotentGL2 y : G)) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · show Continuous fun y : F => (!![(1 : F), 0; y, 1] : M2)
    refine continuous_matrix ?_
    intro i j; fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  · show Continuous fun y : F => (!![(1 : F), 0; -y, 1] : M2)
    refine continuous_matrix ?_
    intro i j; fin_cases i <;> fin_cases j <;> simp <;> fun_prop

theorem continuous_diagUnits2' : Continuous (fun ab : Fˣ × Fˣ => (diagUnits2 ab.1 ab.2 : G)) := by
  have h1 : Continuous fun ab : Fˣ × Fˣ => ((ab.1 : Fˣ) : F) := Units.continuous_val.comp continuous_fst
  have h2 : Continuous fun ab : Fˣ × Fˣ => ((ab.2 : Fˣ) : F) := Units.continuous_val.comp continuous_snd
  have h1' : Continuous fun ab : Fˣ × Fˣ => (((ab.1 : Fˣ) : F))⁻¹ := h1.inv₀ (fun ab => ab.1.ne_zero)
  have h2' : Continuous fun ab : Fˣ × Fˣ => (((ab.2 : Fˣ) : F))⁻¹ := h2.inv₀ (fun ab => ab.2.ne_zero)
  have h0 : Continuous fun _ : Fˣ × Fˣ => (0 : F) := continuous_const
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · show Continuous fun ab : Fˣ × Fˣ => (!![((ab.1 : Fˣ) : F), 0; 0, ((ab.2 : Fˣ) : F)] : M2)
    refine continuous_matrix ?_
    intro i j; fin_cases i <;> fin_cases j
    · simpa using h1
    · simpa using h0
    · simpa using h0
    · simpa using h2
  · show Continuous fun ab : Fˣ × Fˣ => (!![(((ab.1)⁻¹ : Fˣ) : F), 0; 0, (((ab.2)⁻¹ : Fˣ) : F)] : M2)
    refine continuous_matrix ?_
    intro i j; fin_cases i <;> fin_cases j
    · simpa using h1'
    · simpa using h0
    · simpa using h0
    · simpa using h2'

theorem unipotent_eq_unipotentGL2 (x : F) : (unipotent x : G) = unipotentGL2 x := Units.ext rfl

theorem diagOne_coe (a : Fˣ) : ((diagOne a : G) : M2) = !![(a : F), 0; 0, 1] := by
  ext i j
  rw [AdelicLevel.diagOne_coe_apply]
  fin_cases i <;> fin_cases j <;> simp

theorem diagOne_eq_diagUnits2 (a : Fˣ) : (diagOne a : G) = diagUnits2 a 1 := by
  apply Units.ext; rw [diagOne_coe, coe_diagUnits2, Units.val_one]

theorem scalar_eq_diagUnits2 (a : Fˣ) : (Matrix.GeneralLinearGroup.scalar (Fin 2) a : G) = diagUnits2 a a := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  rw [coe_diagUnits2]
  show (Matrix.scalar (Fin 2) (a : F)) i j = !![(a : F), 0; 0, (a : F)] i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.scalar]

theorem continuous_diagOne : Continuous (fun a : Fˣ => (diagOne a : G)) := by
  have : (fun a : Fˣ => (diagOne a : G)) = fun a => diagUnits2 a 1 := funext (diagOne_eq_diagUnits2 p)
  rw [this]; exact (continuous_diagUnits2' p).comp (continuous_id.prodMk continuous_const)

theorem continuous_scalar : Continuous (fun a : Fˣ => (Matrix.GeneralLinearGroup.scalar (Fin 2) a : G)) := by
  have : (fun a : Fˣ => (Matrix.GeneralLinearGroup.scalar (Fin 2) a : G)) = fun a => diagUnits2 a a :=
    funext (scalar_eq_diagUnits2 p)
  rw [this]; exact (continuous_diagUnits2' p).comp (continuous_id.prodMk continuous_id)

theorem scalar_mul_comm (z : Fˣ) (g : G) :
    Matrix.GeneralLinearGroup.scalar (Fin 2) z * g = g * Matrix.GeneralLinearGroup.scalar (Fin 2) z := by
  apply Units.ext
  simp only [Units.val_mul]
  show Matrix.scalar (Fin 2) (z : F) * (g : M2) = (g : M2) * Matrix.scalar (Fin 2) (z : F)
  exact (Matrix.scalar_commute (z : F) (fun r' => Commute.all _ _) (g : M2)).eq

variable {p}

theorem exists_depth_unipotent (U : Subgroup G) (hUo : IsOpen (U : Set G)) :
    ∃ M : ℤ, 0 ≤ M ∧ ∀ x : F, Valued.v x ≤ WithZero.exp (-M) → (unipotent x : G) ∈ U := by
  have h0 : {x : F | (unipotentGL2 x : G) ∈ U} ∈ nhds (0 : F) := by
    refine (hUo.preimage (continuous_unipotentGL2' p)).mem_nhds ?_
    show (unipotentGL2 (0 : F) : G) ∈ U
    rw [unipotentGL2_zero]; exact U.one_mem
  obtain ⟨M, hM, hsub⟩ := exists_ball_subset p h0
  exact ⟨M, hM, fun x hx => by rw [unipotent_eq_unipotentGL2]; exact hsub hx⟩

theorem exists_depth_diagOne (U : Subgroup G) (hUo : IsOpen (U : Set G)) :
    ∃ M : ℤ, 1 ≤ M ∧ ∀ a : Fˣ, Valued.v ((a : F) - 1) ≤ WithZero.exp (-M) → (diagOne a : G) ∈ U := by
  have h1 : {a : Fˣ | (diagOne a : G) ∈ U} ∈ nhds (1 : Fˣ) := by
    refine (hUo.preimage (continuous_diagOne p)).mem_nhds ?_
    show (diagOne (1 : Fˣ) : G) ∈ U
    rw [map_one]; exact U.one_mem
  obtain ⟨M, hM, hsub⟩ := exists_prinUnits_subset p h1
  exact ⟨M, hM, fun a ha => hsub ha⟩

theorem exists_depth_diag_lower (U : Subgroup G) (hUo : IsOpen (U : Set G)) :
    ∃ M : ℤ, 1 ≤ M ∧ ∀ (a : Fˣ) (y : F), Valued.v ((a : F) - 1) ≤ WithZero.exp (-M) → Valued.v y ≤ WithZero.exp (-M) →
      diagUnits2 (1 : Fˣ) a * lowerUnipotentGL2 y ∈ U := by
  have hc : Continuous fun q : Fˣ × F => (diagUnits2 (1 : Fˣ) q.1 * lowerUnipotentGL2 q.2 : G) :=
    ((continuous_diagUnits2' p).comp (continuous_const.prodMk continuous_fst)).mul
      ((continuous_lowerUnipotentGL2' p).comp continuous_snd)
  have hmem : {q : Fˣ × F | (diagUnits2 (1 : Fˣ) q.1 * lowerUnipotentGL2 q.2 : G) ∈ U} ∈ nhds ((1 : Fˣ), (0 : F)) := by
    refine (hUo.preimage hc).mem_nhds ?_
    show (diagUnits2 (1 : Fˣ) (1 : Fˣ) * lowerUnipotentGL2 (0 : F) : G) ∈ U
    have h1 : (diagUnits2 (1 : Fˣ) (1 : Fˣ) : G) = 1 := by
      apply Units.ext
      rw [coe_diagUnits2]
      simp only [Units.val_one]
      exact Matrix.one_fin_two.symm
    have h2 : (lowerUnipotentGL2 (0 : F) : G) = 1 := by
      apply Units.ext
      show (!![(1 : F), 0; 0, 1] : M2) = ((1 : G) : M2)
      rw [Units.val_one]; exact Matrix.one_fin_two.symm
    rw [h1, h2, one_mul]; exact U.one_mem
  obtain ⟨t₁, ht₁, t₂, ht₂, hsub⟩ := mem_nhds_prod_iff.1 hmem
  obtain ⟨M₁, hM₁, h₁⟩ := exists_prinUnits_subset p ht₁
  obtain ⟨M₂, hM₂, h₂⟩ := exists_ball_subset p ht₂
  refine ⟨max M₁ M₂, le_trans hM₁ (le_max_left _ _), fun a y ha hy => ?_⟩
  have hM₁' : WithZero.exp (-(max M₁ M₂)) ≤ WithZero.exp (-M₁) := by rw [WithZero.exp_le_exp]; omega
  have hM₂' : WithZero.exp (-(max M₁ M₂)) ≤ WithZero.exp (-M₂) := by rw [WithZero.exp_le_exp]; omega
  have ha' : a ∈ t₁ := h₁ (show Valued.v ((a : F) - 1) ≤ WithZero.exp (-M₁) from le_trans ha hM₁')
  have hy' : y ∈ t₂ := h₂ (show Valued.v y ≤ WithZero.exp (-M₂) from le_trans hy hM₂')
  have hq : ((a, y) : Fˣ × F) ∈ {q : Fˣ × F | (diagUnits2 (1 : Fˣ) q.1 * lowerUnipotentGL2 q.2 : G) ∈ U} :=
    hsub (Set.mk_mem_prod ha' hy')
  exact hq

theorem exists_depth_char (χ : Fˣ →* ℂˣ) (hχ : IsLocallyConstant χ) :
    ∃ M : ℤ, 1 ≤ M ∧ ∀ a : Fˣ, Valued.v ((a : F) - 1) ≤ WithZero.exp (-M) → χ a = 1 := by
  have h1 : {a : Fˣ | χ a = 1} ∈ nhds (1 : Fˣ) := by
    have : {a : Fˣ | χ a = 1} = χ ⁻¹' {χ 1} := by ext a; simp
    rw [this]; exact (hχ.isOpen_fiber (χ 1)).mem_nhds rfl
  obtain ⟨M, hM, hsub⟩ := exists_prinUnits_subset p h1
  exact ⟨M, hM, fun a ha => hsub ha⟩

theorem exists_depth_central (θ₀ : Fˣ →* ℂˣ) (f : G → ℂ) (K : Subgroup G) (hK : IsOpen (K : Set G))
    (hfK : ∀ k ∈ K, ∀ g : G, f (g * k) = f g) (hf : f ≠ 0)
    (hcentral : ∀ (z : Fˣ) (g : G), f (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((θ₀ z : ℂˣ) : ℂ) * f g) :
    ∃ M : ℤ, 1 ≤ M ∧ ∀ a : Fˣ, Valued.v ((a : F) - 1) ≤ WithZero.exp (-M) → θ₀ a = 1 := by
  obtain ⟨g₀, hg₀⟩ := Function.ne_iff.1 hf
  have h1 : {a : Fˣ | (Matrix.GeneralLinearGroup.scalar (Fin 2) a : G) ∈ K} ∈ nhds (1 : Fˣ) := by
    refine (hK.preimage (continuous_scalar p)).mem_nhds ?_
    show (Matrix.GeneralLinearGroup.scalar (Fin 2) (1 : Fˣ) : G) ∈ K
    have : (Matrix.GeneralLinearGroup.scalar (Fin 2) (1 : Fˣ) : G) = 1 := by
      apply Units.ext; show Matrix.scalar (Fin 2) ((1 : Fˣ) : F) = 1; simp
    rw [this]; exact K.one_mem
  obtain ⟨M, hM, hsub⟩ := exists_prinUnits_subset p h1
  refine ⟨M, hM, fun a ha => ?_⟩
  have hk : (Matrix.GeneralLinearGroup.scalar (Fin 2) a : G) ∈ K := hsub ha
  have := hcentral a g₀
  rw [scalar_mul_comm p, hfK _ hk] at this
  have h1' : ((θ₀ a : ℂˣ) : ℂ) = 1 := by
    have := mul_left_eq_self₀.1 this.symm
    rcases this with h | h
    · exact h
    · exact absurd h hg₀
  exact Units.val_eq_one.1 h1'

end GroupSide

section Box

attribute [local instance] LanglandsTunnell.TateLocal.localBorel
attribute [local instance] LanglandsTunnell.TateLocal.borelSpace_localBorel

variable (p : HeightOneSpectrum (𝓞 ℚ))
local notation "F" => (HeightOneSpectrum.adicCompletion ℚ p)
local notation "M2" => (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))

def box (L Mb Mc Md : ℤ) : Set M2 :=
  {X : M2 | Valued.v (X 0 0) ≤ WithZero.exp L ∧ Valued.v (X 0 1) ≤ WithZero.exp (-Mb) ∧
      Valued.v (X 1 0) ≤ WithZero.exp (-Mc) ∧ Valued.v (X 1 1 - 1) ≤ WithZero.exp (-Md)}

theorem continuous_entry (i j : Fin 2) : Continuous fun X : M2 => X i j := continuous_id.matrix_elem i j

theorem isOpen_box (L Mb Mc Md : ℤ) : IsOpen (box p L Mb Mc Md) := by
  unfold box
  exact (((isOpen_vball p _).preimage (continuous_entry p 0 0)).inter (((isOpen_vball p _).preimage (continuous_entry p 0 1)).inter
    (((isOpen_vball p _).preimage (continuous_entry p 1 0)).inter ((isOpen_vball p _).preimage ((continuous_entry p 1 1).sub continuous_const)))))

theorem isClosed_box (L Mb Mc Md : ℤ) : IsClosed (box p L Mb Mc Md) := by
  unfold box
  exact (((isClosed_vball p _).preimage (continuous_entry p 0 0)).inter (((isClosed_vball p _).preimage (continuous_entry p 0 1)).inter
    (((isClosed_vball p _).preimage (continuous_entry p 1 0)).inter ((isClosed_vball p _).preimage ((continuous_entry p 1 1).sub continuous_const)))))

theorem isLocallyConstant_boxIndicator (L Mb Mc Md : ℤ) :
    IsLocallyConstant (fun X : M2 => Set.indicator (box p L Mb Mc Md) (fun _ => (1 : ℂ)) X) := by
  intro s
  rw [isOpen_iff_mem_nhds]
  intro X hX
  by_cases hXS : X ∈ box p L Mb Mc Md
  · refine Filter.mem_of_superset ((isOpen_box p L Mb Mc Md).mem_nhds hXS) fun Y hY => ?_
    simp only [Set.mem_preimage, Set.indicator_of_mem hXS] at hX
    simp only [Set.mem_preimage, Set.indicator_of_mem hY]; exact hX
  · refine Filter.mem_of_superset ((isClosed_box p L Mb Mc Md).isOpen_compl.mem_nhds hXS) fun Y hY => ?_
    have hY' : Y ∉ box p L Mb Mc Md := hY
    simp only [Set.mem_preimage, Set.indicator_of_notMem hXS] at hX
    simp only [Set.mem_preimage, Set.indicator_of_notMem hY']; exact hX

theorem hasCompactSupport_boxIndicator {L Mb Mc Md : ℤ} (hL : 0 ≤ L) (hMb : 0 ≤ Mb) (hMc : 0 ≤ Mc) (hMd : 0 ≤ Md) :
    HasCompactSupport (fun X : M2 => Set.indicator (box p L Mb Mc Md) (fun _ => (1 : ℂ)) X) := by
  have hK : IsCompact {X : M2 | ∀ i j : Fin 2, Valued.v (X i j) ≤ WithZero.exp L} := by
    have h := isCompact_univ_pi (fun (_ : Fin 2) => isCompact_univ_pi (fun (_ : Fin 2) => isCompact_vball p L))
    have hset : {X : M2 | ∀ i j : Fin 2, Valued.v (X i j) ≤ WithZero.exp L} =
        Set.pi Set.univ (fun (_ : Fin 2) => Set.pi Set.univ (fun (_ : Fin 2) => {x : F | Valued.v x ≤ WithZero.exp L})) := by
      ext X
      constructor
      · intro h i _ j _; exact h i j
      · intro h i j; exact h i (Set.mem_univ i) j (Set.mem_univ j)
    rw [hset]; exact h
  refine HasCompactSupport.intro hK fun X hX => ?_
  apply Set.indicator_of_notMem
  intro hXb
  apply hX
  obtain ⟨h00, h01, h10, h11⟩ := hXb
  have hb : WithZero.exp (-Mb) ≤ WithZero.exp L := by rw [WithZero.exp_le_exp]; omega
  have hc : WithZero.exp (-Mc) ≤ WithZero.exp L := by rw [WithZero.exp_le_exp]; omega
  have hd : Valued.v (X 1 1) ≤ WithZero.exp L := by
    have : X 1 1 = (X 1 1 - 1) + 1 := by ring
    rw [this]
    refine le_trans (Valuation.map_add _ _ _) (max_le (le_trans h11 ?_) ?_)
    · rw [WithZero.exp_le_exp]; omega
    · rw [Valuation.map_one, ← WithZero.exp_zero, WithZero.exp_le_exp]; exact hL
  intro i j
  fin_cases i <;> fin_cases j
  · exact h00
  · exact le_trans h01 hb
  · exact le_trans h10 hc
  · exact hd

end Box

section Main

attribute [local instance] LanglandsTunnell.TateLocal.localBorel
attribute [local instance] LanglandsTunnell.TateLocal.borelSpace_localBorel
attribute [local instance] AutomorphicForm.localGLBorel
attribute [local instance] AutomorphicForm.borelSpace_localGLBorel

variable (p : HeightOneSpectrum (𝓞 ℚ))

scoped instance borelSpace_units : BorelSpace (HeightOneSpectrum.adicCompletion ℚ p)ˣ :=
  ⟨by
    rw [(Units.isEmbedding_val₀ (G₀ := HeightOneSpectrum.adicCompletion ℚ p)).isInducing.eq_induced, borel_comap,
      ← BorelSpace.measurable_eq (α := HeightOneSpectrum.adicCompletion ℚ p)]
    rfl⟩

theorem isAddHaarMeasure_selfDualHaarAt : (selfDualHaarAt ℚ p).IsAddHaarMeasure := by
  set c : NNReal := (Ideal.absNorm p.asIdeal : NNReal) ^ (-(addCharLevel (NumberField.StandardAddChar.psiLocal ℚ p) : ℝ) / 2)
    with hc
  have hc0 : c ≠ 0 := by
    rw [hc]
    exact (NNReal.rpow_pos
      (by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr p.ne_bot))).ne'
  have hdef : selfDualHaarAt ℚ p = (c : ENNReal) • Measure.addHaarMeasure (integersPositiveCompacts ℚ p) := rfl
  rw [hdef]
  exact Measure.IsAddHaarMeasure.smul _ (by exact_mod_cast hc0) ENNReal.coe_ne_top

scoped instance : (selfDualHaarAt ℚ p).IsAddHaarMeasure := isAddHaarMeasure_selfDualHaarAt p

scoped instance isHaarMeasure_units :
    (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)) : Measure (HeightOneSpectrum.adicCompletion ℚ p)ˣ).IsHaarMeasure :=
  LanglandsTunnell.TateLocal.isHaarMeasure_comap_val_mulMeasure ℚ p _

end Main

end LRed46
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_schwartz_godementZeta2_whittaker_eq_mul_torusZeta_and_dual_of_integrable.LRed46"

open LRed46 in
set_option maxHeartbeats 3200000 in
theorem solution
    (p : HeightOneSpectrum (𝓞 ℚ))
    (θ₀ : (p.adicCompletion ℚ)ˣ →* ℂˣ)
    (N : Ideal (𝓞 ℚ)) (hN : N ≠ ⊥)
    (w₂base : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hw₂law : ∀ (x : (p.adicCompletion ℚ)) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w₂base (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * w₂base g)
    (hw₂K : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w₂base (g * k) = w₂base g)
    (hw₂ne : w₂base ≠ 0)
    (hcentral : ∀ (z : (p.adicCompletion ℚ)ˣ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w₂base (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((θ₀ z : ℂˣ) : ℂ) * w₂base g)
    (wJ : GL (Fin 2) (p.adicCompletion ℚ)) (hwJ : (wJ : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = !![0, 1; -1, 0])
    (χ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (hχ : IsLocallyConstant χ) :
    letI : MeasurableSpace (p.adicCompletion ℚ) := localBorel ℚ p
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure],
      ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
        ∃ Φ₀ : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) → ℂ, IsLocallyConstant Φ₀ ∧ HasCompactSupport Φ₀ ∧
          ∃ C : ℂ, C ≠ 0 ∧
            (∀ s : ℂ,
              Integrable (fun y : (p.adicCompletion ℚ)ˣ =>
                w (diagOne y) * ((χ y : ℂˣ) : ℂ) * ((modulus (y : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (s - 1 / 2)) (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) →
              Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                w g * Φ₀ (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) * ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
                  ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (s + 1 / 2)) μ₂ ∧
              godementZeta2 p μ₂ w Φ₀ χ (s + 1 / 2) =
                C * ∫ y : (p.adicCompletion ℚ)ˣ,
                  w (diagOne y) * ((χ y : ℂˣ) : ℂ) * ((modulus (y : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (s - 1 / 2) ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) ∧
            (∀ s : ℂ,
              Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                w (transposeInvN (Fin 2) g) *
                  matFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p) Φ₀ (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) *
                  ((χ⁻¹ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
                  ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (s + 3 / 2)) μ₂ →
              Integrable (fun y : (p.adicCompletion ℚ)ˣ =>
                w (diagOne y * wJ) * (((χ y : ℂˣ) : ℂ))⁻¹ * (((θ₀ y : ℂˣ) : ℂ))⁻¹ *
                  ((modulus (y : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (1 / 2 + s)) (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) ∧
              godementZeta2 p μ₂ (fun g : GL (Fin 2) (p.adicCompletion ℚ) => w (transposeInvN (Fin 2) g))
                  (matFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p) Φ₀) χ⁻¹ (s + 3 / 2) =
                C * ∫ y : (p.adicCompletion ℚ)ˣ,
                  w (diagOne y * wJ) * (((χ y : ℂˣ) : ℂ))⁻¹ * (((θ₀ y : ℂˣ) : ℂ))⁻¹ *
                    ((modulus (y : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (1 / 2 + s) ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) := by
  letI : MeasurableSpace (p.adicCompletion ℚ) := localBorel ℚ p
  haveI : BorelSpace (p.adicCompletion ℚ) := borelSpace_localBorel ℚ p
  letI : MeasurableSpace (GL (Fin 2) (p.adicCompletion ℚ)) := localGLBorel ℚ p
  haveI : BorelSpace (GL (Fin 2) (p.adicCompletion ℚ)) := borelSpace_localGLBorel ℚ p
  haveI : (selfDualHaarAt ℚ p).IsAddHaarMeasure := isAddHaarMeasure_selfDualHaarAt p
  haveI : BorelSpace (p.adicCompletion ℚ)ˣ := borelSpace_units p
  haveI := isHaarMeasure_units p
  intro μ₂ _ w hw

  have hwlawW : ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * w g :=
    fun x => law_of_mem_span w₂base (unipotent x) _ (hw₂law x) hw
  have hcentralW : ∀ (z : (p.adicCompletion ℚ)ˣ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((θ₀ z : ℂˣ) : ℂ) * w g :=
    fun z => law_of_mem_span w₂base _ _ (hcentral z) hw
  obtain ⟨-, hKo⟩ := AdelicDock.isCompact_and_isOpen_localLevelOne ℚ p N hN
  obtain ⟨U, hUo, hU⟩ := exists_open_stabilizer_of_mem_span w₂base (AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N) hKo hw₂K hw

  obtain ⟨L₀, hL₀, hsupp₀⟩ := exists_exp_of_modulus_bound p
    (AutomorphicForm.WhittakerModel.exists_forall_diagOne_eq_zero_of_lt_modulus p w hwlawW ⟨U, hUo, hU⟩)
  have hwJmem := translate_mem_span w₂base wJ hw
  obtain ⟨U', hU'o, hU'⟩ := exists_open_stabilizer_of_mem_span w₂base (AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N) hKo hw₂K hwJmem
  have hlawJ : ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      (fun g : GL (Fin 2) (p.adicCompletion ℚ) => w (g * wJ)) (unipotent x * g) =
        NumberField.StandardAddChar.psiLocal ℚ p x * (fun g : GL (Fin 2) (p.adicCompletion ℚ) => w (g * wJ)) g := by
    intro x g; simp only [mul_assoc]; exact hwlawW x (g * wJ)
  obtain ⟨Lc, hLc, hsuppJ₀⟩ := exists_exp_of_modulus_bound p
    (AutomorphicForm.WhittakerModel.exists_forall_diagOne_eq_zero_of_lt_modulus p (fun g => w (g * wJ)) hlawJ ⟨U', hU'o, hU'⟩)

  obtain ⟨M₁, hM₁, hN₁⟩ := exists_depth_unipotent (p := p) U hUo
  obtain ⟨M₂, hM₂, hD₁⟩ := exists_depth_diagOne (p := p) U hUo
  obtain ⟨M₃, hM₃, hDL⟩ := exists_depth_diag_lower (p := p) U hUo
  obtain ⟨M₄, hM₄, hχ₁⟩ := exists_depth_char (p := p) χ hχ
  obtain ⟨M₅, hM₅, hθ₁⟩ := exists_depth_central (p := p) θ₀ w₂base (AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N) hKo hw₂K hw₂ne hcentral

  set Md : ℤ := max (max M₂ M₃) (max M₄ M₅) with hMd
  set Mc : ℤ := max M₃ Lc with hMc
  set L : ℤ := max (max L₀ M₁) Md with hLd
  have hMd1 : 1 ≤ Md := le_trans hM₂ (le_trans (le_max_left _ _) (le_max_left _ _))
  have hMc0 : 0 ≤ Mc := le_trans hLc (le_max_right _ _)
  have hLMd : Md ≤ L := le_max_right _ _
  have hL0 : 0 ≤ L := le_trans (le_trans zero_le_one hMd1) hLMd
  have eMd2 : WithZero.exp (-Md) ≤ WithZero.exp (-M₂) := by rw [WithZero.exp_le_exp]; omega
  have eMd3 : WithZero.exp (-Md) ≤ WithZero.exp (-M₃) := by rw [WithZero.exp_le_exp]; omega
  have eMd4 : WithZero.exp (-Md) ≤ WithZero.exp (-M₄) := by rw [WithZero.exp_le_exp]; omega
  have eMd5 : WithZero.exp (-Md) ≤ WithZero.exp (-M₅) := by rw [WithZero.exp_le_exp]; omega
  have eMc3 : WithZero.exp (-Mc) ≤ WithZero.exp (-M₃) := by rw [WithZero.exp_le_exp]; omega
  have eL1 : WithZero.exp (-L) ≤ WithZero.exp (-M₁) := by rw [WithZero.exp_le_exp]; omega
  have eL0 : WithZero.exp L₀ ≤ WithZero.exp L := by rw [WithZero.exp_le_exp]; omega
  have eLc : WithZero.exp Lc ≤ WithZero.exp Mc := by rw [WithZero.exp_le_exp]; omega
  have hsupp : ∀ y : (p.adicCompletion ℚ)ˣ, WithZero.exp L < Valued.v (y : p.adicCompletion ℚ) → w (diagOne y) = 0 :=
    fun y hy => hsupp₀ y (lt_of_le_of_lt eL0 hy)
  have hsuppJ : ∀ y : (p.adicCompletion ℚ)ˣ, WithZero.exp Mc < Valued.v (y : p.adicCompletion ℚ) → w (diagOne y * wJ) = 0 :=
    fun y hy => hsuppJ₀ y (lt_of_le_of_lt eLc hy)
  have hstab : ∀ (a : (p.adicCompletion ℚ)ˣ) (y : p.adicCompletion ℚ),
      Valued.v ((a : p.adicCompletion ℚ) - 1) ≤ WithZero.exp (-Md) → Valued.v y ≤ WithZero.exp (-Mc) →
        diagUnits2 1 a * lowerUnipotentGL2 y ∈ U :=
    fun a y ha hy => hDL a y (le_trans ha eMd3) (le_trans hy eMc3)
  have hstabN : ∀ x : p.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (-L) → unipotent x ∈ U :=
    fun x hx => hN₁ x (le_trans hx eL1)
  have hstabD : ∀ a : (p.adicCompletion ℚ)ˣ, Valued.v ((a : p.adicCompletion ℚ) - 1) ≤ WithZero.exp (-Md) → diagOne a ∈ U :=
    fun a ha => hD₁ a (le_trans ha eMd2)
  have hχ' : ∀ a : (p.adicCompletion ℚ)ˣ, Valued.v ((a : p.adicCompletion ℚ) - 1) ≤ WithZero.exp (-Md) → χ a = 1 :=
    fun a ha => hχ₁ a (le_trans ha eMd4)
  have hθ' : ∀ a : (p.adicCompletion ℚ)ˣ, Valued.v ((a : p.adicCompletion ℚ) - 1) ≤ WithZero.exp (-Md) → θ₀ a = 1 :=
    fun a ha => hθ₁ a (le_trans ha eMd5)

  obtain ⟨c, hc0, hcT, hchart⟩ :=
    AutomorphicForm.exists_haar_localGL2_eq_smul_map_unipotentGL2_mul_diagUnits2_mul_lowerUnipotentGL2 ℚ p μ₂
      (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) (selfDualHaarAt ℚ p)

  obtain ⟨hC, h1⟩ := LanglandsTunnell.RankinSelberg.godementZeta2_boxIndicator_eq_mul_torusZeta_of_isOpen_of_chart p w hwlawW χ hχ U hUo hU
    L 0 Mc Md hL0 le_rfl hMc0 hMd1 hsupp hstab hχ' _ rfl μ₂ c hc0 hcT hchart
  have h2 := LanglandsTunnell.RankinSelberg.godementZeta2_transposeInv_matFourier22_boxIndicator_eq_mul_torusZeta_dual_of_integrable_of_chart p w hwlawW θ₀ hcentralW χ hχ U hUo hU
    wJ hwJ L 0 Mc Md hLMd le_rfl hMc0 hMd1 hsuppJ hstabN hstabD hθ' hχ' _ rfl μ₂ c hc0 hcT hchart
  refine ⟨_, ?_, ?_, _, hC, h1, h2⟩
  · exact isLocallyConstant_boxIndicator p L 0 Mc Md
  · exact hasCompactSupport_boxIndicator p hL0 le_rfl hMc0 (le_trans zero_le_one hMd1)

#print axioms solution

end
end S_LanglandsTunnell_RankinSelberg_exists_schwartz_godementZeta2_whittaker_eq_mul_torusZeta_and_dual_of_integrable
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_exists_schwartz_godementZeta2_whittaker_eq_mul_torusZeta_and_dual_of_integrable (solution)
