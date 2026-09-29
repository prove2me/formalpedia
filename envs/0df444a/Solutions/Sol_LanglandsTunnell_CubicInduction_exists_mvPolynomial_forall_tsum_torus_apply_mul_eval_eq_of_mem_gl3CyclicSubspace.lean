-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.exists_mvPolynomial_forall_tsum_torus_apply_mul_eval_eq_of_mem_gl3CyclicSubspace
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/f133a2fe-828d-5c1e-a262-00e0db696ef5

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
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_polynomial_sum_coeff_smul_rightTranslate_pow_mem_span_radical_of_admissible
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_forall_apply_iotaGL_torus_eq_zero_of_mem_span_radical_of_isGL3PsiWhittakerFn
import Theorems.Thm_Polynomial_exists_mvPolynomial_forall_hasSum_torusWeight_mul_eq_of_separated_recurrence
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Topology.Algebra.Valued.ValuationTopology
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Instances.Matrix
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_mvPolynomial_forall_tsum_torus_apply_mul_eval_eq_of_mem_gl3CyclicSubspace
p2m_attr_erase "simp" "LanglandsTunnell.CubicInduction.diagonal3_coe LanglandsTunnell.CubicInduction.halfModulus3_one LanglandsTunnell.CubicInduction.torusChar3_one"

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory LanglandsTunnell.TateLocal UnramifiedWhittaker LanglandsTunnell.CubicInduction

open scoped nonZeroDivisors

namespace Ws46
namespace SUP

open LanglandsTunnell LanglandsTunnell.CubicInduction

theorem exists_openSubgroup_conj_subset {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (U : Subgroup G) (hU : IsOpen (U : Set G)) (C : Set G) (hC : IsCompact C) :
    ∃ U'' : Subgroup G, IsOpen (U'' : Set G) ∧ ∀ h ∈ C, ∀ y ∈ U'', h⁻¹ * y * h ∈ U := by
  classical
  let U'' : Subgroup G :=
    { carrier := {y | ∀ h ∈ C, h⁻¹ * y * h ∈ U}
      mul_mem' := fun {a b} ha hb h hh => by
        have : h⁻¹ * (a * b) * h = (h⁻¹ * a * h) * (h⁻¹ * b * h) := by group
        rw [this]; exact U.mul_mem (ha h hh) (hb h hh)
      one_mem' := fun h _ => by simp
      inv_mem' := fun {a} ha h hh => by
        have : h⁻¹ * a⁻¹ * h = (h⁻¹ * a * h)⁻¹ := by group
        rw [this]; exact U.inv_mem (ha h hh) }
  refine ⟨U'', ?_, fun h hh y hy => hy h hh⟩

  have hcont : Continuous fun p : G × G => p.1⁻¹ * p.2 * p.1 :=
    ((continuous_fst.inv).mul continuous_snd).mul continuous_fst
  have hopen : IsOpen ((fun p : G × G => p.1⁻¹ * p.2 * p.1) ⁻¹' (U : Set G)) := hU.preimage hcont
  have hsub : C ×ˢ ({1} : Set G) ⊆ (fun p : G × G => p.1⁻¹ * p.2 * p.1) ⁻¹' (U : Set G) := by
    rintro ⟨h, y⟩ ⟨_, hy⟩
    rw [Set.mem_singleton_iff] at hy
    subst hy
    simp [U.one_mem]
  obtain ⟨u, w, -, hwo, hCu, h1w, huw⟩ := generalized_tube_lemma hC isCompact_singleton hopen hsub
  apply Subgroup.isOpen_of_mem_nhds U'' (g := 1)
  refine Filter.mem_of_superset (hwo.mem_nhds (h1w (Set.mem_singleton 1))) fun y hy h hh => ?_
  exact huw (Set.mk_mem_prod (hCu hh) hy)

variable (v : HeightOneSpectrum (𝓞 ℚ))

theorem continuous_upperUnipotent3_12 :
    Continuous fun x : v.adicCompletion ℚ => (upperUnipotent3 x 0 0 : LocalGL3 v) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · show Continuous fun x : v.adicCompletion ℚ => ((upperUnipotent3 x 0 0 : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))
    simp only [upperUnipotent3_coe]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  · have : ∀ x : v.adicCompletion ℚ, (((upperUnipotent3 x 0 0 : LocalGL3 v))⁻¹ : LocalGL3 v).val =
        !![1, -x, x * 0 - 0; 0, 1, -0; 0, 0, 1] := fun x => rfl
    show Continuous fun x : v.adicCompletion ℚ => (((upperUnipotent3 x 0 0 : LocalGL3 v))⁻¹ : LocalGL3 v).val
    simp only [this]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop

theorem continuous_upperUnipotent3_23 :
    Continuous fun x : v.adicCompletion ℚ => (upperUnipotent3 0 x 0 : LocalGL3 v) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · show Continuous fun x : v.adicCompletion ℚ => ((upperUnipotent3 0 x 0 : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))
    simp only [upperUnipotent3_coe]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  · have : ∀ x : v.adicCompletion ℚ, (((upperUnipotent3 0 x 0 : LocalGL3 v))⁻¹ : LocalGL3 v).val =
        !![1, -0, 0 * x - 0; 0, 1, -x; 0, 0, 1] := fun x => rfl
    show Continuous fun x : v.adicCompletion ℚ => (((upperUnipotent3 0 x 0 : LocalGL3 v))⁻¹ : LocalGL3 v).val
    simp only [this]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop

theorem exists_ball_subset (s : Set (v.adicCompletion ℚ)) (hs : s ∈ nhds (0 : v.adicCompletion ℚ)) :
    ∃ m : ℤ, ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp m → x ∈ s := by
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.mp hs
  have hγ0 : (MonoidWithZeroHom.ValueGroup₀.embedding γ.1 : WithZero (Multiplicative ℤ)) ≠ 0 :=
    (map_ne_zero MonoidWithZeroHom.ValueGroup₀.embedding).mpr γ.ne_zero
  refine ⟨WithZero.log (MonoidWithZeroHom.ValueGroup₀.embedding γ.1) - 1, fun x hx => hγ ?_⟩
  show Valued.v.restrict x < γ.1
  rw [Valuation.restrict_lt_iff_lt_embedding]
  refine lt_of_le_of_lt hx ?_
  conv_rhs => rw [← WithZero.exp_log hγ0]
  exact WithZero.exp_lt_exp.mpr (by omega)

theorem exists_level (U : Subgroup (LocalGL3 v)) (hU : IsOpen (U : Set (LocalGL3 v))) :
    ∃ m : ℤ, ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp m →
      (upperUnipotent3 x 0 0 : LocalGL3 v) ∈ U ∧ (upperUnipotent3 0 x 0 : LocalGL3 v) ∈ U := by
  have h1 : {x : v.adicCompletion ℚ | (upperUnipotent3 x 0 0 : LocalGL3 v) ∈ U} ∈ nhds (0 : v.adicCompletion ℚ) :=
    (continuous_upperUnipotent3_12 v).continuousAt.preimage_mem_nhds
      (by rw [upperUnipotent3_zero]; exact hU.mem_nhds U.one_mem)
  have h2 : {x : v.adicCompletion ℚ | (upperUnipotent3 0 x 0 : LocalGL3 v) ∈ U} ∈ nhds (0 : v.adicCompletion ℚ) :=
    (continuous_upperUnipotent3_23 v).continuousAt.preimage_mem_nhds
      (by rw [upperUnipotent3_zero]; exact hU.mem_nhds U.one_mem)
  obtain ⟨m₁, hm₁⟩ := exists_ball_subset v _ h1
  obtain ⟨m₂, hm₂⟩ := exists_ball_subset v _ h2
  refine ⟨min m₁ m₂, fun x hx => ⟨hm₁ x (hx.trans (WithZero.exp_le_exp.mpr (min_le_left _ _))),
    hm₂ x (hx.trans (WithZero.exp_le_exp.mpr (min_le_right _ _)))⟩⟩

variable {K : Type*} [Field K]

theorem iotaGL_diagUnitGL2_mul_upper12 (w : Kˣ) (x : K) :
    iotaGL (diagUnitGL2 w) * upperUnipotent3 x 0 0 = upperUnipotent3 ((w : K) * x) 0 0 * iotaGL (diagUnitGL2 w) := by
  apply Units.ext
  simp only [Units.val_mul, coe_iotaGL, coe_diagUnitGL2, upperUnipotent3_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [embedMat2, Matrix.mul_apply, Fin.sum_univ_three]

theorem commute_iotaGL_scalarPi_upper12 (π : K) (hπ : π ≠ 0) (x : K) :
    Commute (iotaGL (UnramifiedWhittaker.scalarPi π hπ)) (upperUnipotent3 x 0 0 : GL (Fin 3) K) := by
  unfold Commute SemiconjBy
  apply Units.ext
  simp only [Units.val_mul, coe_iotaGL, upperUnipotent3_coe, UnramifiedWhittaker.scalarPi,
    Matrix.GeneralLinearGroup.mkOfDetNeZero]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [embedMat2, Matrix.mul_apply, Fin.sum_univ_three, mul_comm]

theorem commute_iotaGL_diagUnitGL2_upper23 (w : Kˣ) (x : K) :
    Commute (iotaGL (diagUnitGL2 w)) (upperUnipotent3 0 x 0 : GL (Fin 3) K) := by
  unfold Commute SemiconjBy
  apply Units.ext
  simp only [Units.val_mul, coe_iotaGL, coe_diagUnitGL2, upperUnipotent3_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [embedMat2, Matrix.mul_apply, Fin.sum_univ_three]

theorem iotaGL_scalarPi_mul_upper23 (π : K) (hπ : π ≠ 0) (x : K) :
    iotaGL (UnramifiedWhittaker.scalarPi π hπ) * upperUnipotent3 0 x 0 =
      upperUnipotent3 0 (π * x) 0 * iotaGL (UnramifiedWhittaker.scalarPi π hπ) := by
  apply Units.ext
  simp only [Units.val_mul, coe_iotaGL, upperUnipotent3_coe, UnramifiedWhittaker.scalarPi,
    Matrix.GeneralLinearGroup.mkOfDetNeZero]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [embedMat2, Matrix.mul_apply, Fin.sum_univ_three, mul_comm]

theorem semiconj_pow_aux {G : Type*} [Group G] (s : G) (n : K → G) (π : K)
    (h : ∀ x, s * n x = n (π * x) * s) : ∀ (k : ℕ) (x : K), s ^ k * n x = n (π ^ k * x) * s ^ k := by
  intro k
  induction k with
  | zero => intro x; simp
  | succ k ih =>
      intro x
      rw [pow_succ, mul_assoc, h, ← mul_assoc, ih, mul_assoc, ← pow_succ, pow_succ]
      congr 2
      ring

theorem iotaGL_scalarPi_zpow_mul_upper23 (π : K) (hπ : π ≠ 0) (x : K) (n : ℤ) :
    iotaGL (UnramifiedWhittaker.scalarPi π hπ) ^ n * upperUnipotent3 0 x 0 =
      upperUnipotent3 0 (π ^ n * x) 0 * iotaGL (UnramifiedWhittaker.scalarPi π hπ) ^ n := by
  set s : GL (Fin 3) K := iotaGL (UnramifiedWhittaker.scalarPi π hπ) with hs
  have base : ∀ y : K, s * upperUnipotent3 0 y 0 = upperUnipotent3 0 (π * y) 0 * s :=
    fun y => iotaGL_scalarPi_mul_upper23 π hπ y
  have binv : ∀ y : K, s⁻¹ * upperUnipotent3 0 y 0 = upperUnipotent3 0 (π⁻¹ * y) 0 * s⁻¹ := by
    intro y
    have h0 := base (π⁻¹ * y)
    rw [show π * (π⁻¹ * y) = y by field_simp] at h0
    calc s⁻¹ * upperUnipotent3 0 y 0 = s⁻¹ * (upperUnipotent3 0 y 0 * s) * s⁻¹ := by group
      _ = s⁻¹ * (s * upperUnipotent3 0 (π⁻¹ * y) 0) * s⁻¹ := by rw [h0]
      _ = upperUnipotent3 0 (π⁻¹ * y) 0 * s⁻¹ := by group
  cases n with
  | ofNat k =>
      simp only [Int.ofNat_eq_coe, zpow_natCast]
      exact semiconj_pow_aux s (fun y => upperUnipotent3 0 y 0) π base k x
  | negSucc k =>
      simp only [zpow_negSucc, ← inv_pow]
      exact semiconj_pow_aux s⁻¹ (fun y => upperUnipotent3 0 y 0) π⁻¹ binv (k + 1) x

theorem continuous_embedMat2 {K : Type*} [Field K] [TopologicalSpace K] :
    Continuous (embedMat2 : Matrix (Fin 2) (Fin 2) K → Matrix (Fin 3) (Fin 3) K) := by
  refine continuous_matrix fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [embedMat2]
  all_goals first
    | exact continuous_const
    | exact (continuous_apply _).comp (continuous_apply _)
    | fun_prop

theorem continuous_iotaGL {K : Type*} [Field K] [TopologicalSpace K] [IsTopologicalRing K] :
    Continuous (iotaGL : GL (Fin 2) K → GL (Fin 3) K) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact (continuous_embedMat2.comp Units.continuous_val :
      Continuous fun g : GL (Fin 2) K => embedMat2 ((g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K))
  · exact (continuous_embedMat2.comp Units.continuous_coe_inv :
      Continuous fun g : GL (Fin 2) K => embedMat2 ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K))

theorem continuous_transposeInvN2 {K : Type*} [Field K] [TopologicalSpace K] [IsTopologicalRing K] :
    Continuous (AutomorphicForm.transposeInvN (Fin 2) : GL (Fin 2) K → GL (Fin 2) K) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact (Units.continuous_coe_inv.matrix_transpose :
      Continuous fun g : GL (Fin 2) K => Matrix.transpose ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K))
  · exact (Units.continuous_val.matrix_transpose :
      Continuous fun g : GL (Fin 2) K => Matrix.transpose ((g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K))

set_option maxHeartbeats 3200000 in
private theorem _root_.Ws46.SUP.core {ϖ : v.adicCompletionIntegers ℚ}
    (hπ : (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) ≠ 0) (hϖ : Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ))
    (ψ' : AddChar (v.adicCompletion ℚ) ℂ) (x₀ : v.adicCompletion ℚ) (hx₀ : ψ' x₀ ≠ 1)
    (W' : LocalGL3 v → ℂ) (hW' : IsGL3PsiWhittakerFn ψ' W')
    (U' : Subgroup (LocalGL3 v)) (hU'o : IsOpen (U' : Set (LocalGL3 v)))
    (hU'inv : ∀ k ∈ U', ∀ g : LocalGL3 v, W' (g * k) = W' g)
    (C : Set (LocalGL3 v)) (hC : IsCompact C) :
    ∃ N₁ : ℤ, ∀ n₁ n₂ : ℤ, (n₁ < N₁ ∨ n₂ < N₁) → ∀ u : (v.adicCompletion ℚ)ˣ, Valued.v (u : v.adicCompletion ℚ) = 1 →
      ∀ h₀ ∈ C, W' (iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n₂ *
        diagUnitGL2 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n₁ * u)) * h₀) = 0 := by
  obtain ⟨U'', hU''o, hU''⟩ := exists_openSubgroup_conj_subset U' hU'o C hC
  obtain ⟨m, hm⟩ := exists_level v U'' hU''o
  have hx₀0 : x₀ ≠ 0 := fun h => hx₀ (by rw [h, AddChar.map_zero_eq_one])
  have hvx₀ : Valued.v x₀ ≠ 0 := (Valuation.ne_zero_iff _).mpr hx₀0
  have hvx₀' : Valued.v x₀ = WithZero.exp (WithZero.log (Valued.v x₀)) := (WithZero.exp_log hvx₀).symm
  refine ⟨m - WithZero.log (Valued.v x₀), fun n₁ n₂ hn u hu h₀ hh₀ => ?_⟩
  have hW'' : ∀ (x y z : v.adicCompletion ℚ) (g : LocalGL3 v), W' (upperUnipotent3 x y z * g) = ψ' (x + y) * W' g := hW'
  have hvπ : ∀ j : ℤ, Valued.v ((algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) ^ j) = WithZero.exp (-j) := by
    intro j
    rw [map_zpow₀, hϖ, ← WithZero.exp_zsmul, smul_eq_mul, mul_neg, mul_one]

  have key : ∀ y : LocalGL3 v, y ∈ U'' → ∀ a b c : v.adicCompletion ℚ,
      iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n₂ * diagUnitGL2 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n₁ * u)) * y =
        upperUnipotent3 a b c * iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n₂ * diagUnitGL2 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n₁ * u)) →
      ψ' (a + b) ≠ 1 →
      W' (iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n₂ * diagUnitGL2 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n₁ * u)) * h₀) = 0 := by
    intro y hy a b c hTy hne
    have h1 := hU'inv _ (hU'' h₀ hh₀ y hy)
      (iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n₂ * diagUnitGL2 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n₁ * u)) * h₀)
    rw [show iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n₂ * diagUnitGL2 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n₁ * u)) * h₀ *
        (h₀⁻¹ * y * h₀) =
        (iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n₂ * diagUnitGL2 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n₁ * u)) * y) * h₀ by group,
      hTy, mul_assoc, hW''] at h1
    by_contra hw
    exact hne ((mul_eq_right₀ hw).mp h1)
  rcases hn with hlt | hlt
  ·
    set x' : v.adicCompletion ℚ := (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) ^ (-n₁) * ((u : v.adicCompletion ℚ)⁻¹ * x₀) with hx'
    have hvx' : Valued.v x' ≤ WithZero.exp m := by
      rw [hx', map_mul, map_mul, hvπ, map_inv₀, hu, inv_one, one_mul, hvx₀', ← WithZero.exp_add]
      exact WithZero.exp_le_exp.mpr (by omega)
    refine key (upperUnipotent3 x' 0 0) (hm x' hvx').1 x₀ 0 0 ?_ (by rw [add_zero]; exact hx₀)
    have hprod : ((Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n₁ * u : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) * x' = x₀ := by
      rw [hx', Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_mk0, zpow_neg]
      field_simp
    calc iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n₂ * diagUnitGL2 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n₁ * u)) * upperUnipotent3 x' 0 0
        = iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) ^ n₂ * (iotaGL (diagUnitGL2 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n₁ * u)) *
            upperUnipotent3 x' 0 0) := by rw [map_mul, map_zpow, mul_assoc]
      _ = iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) ^ n₂ * upperUnipotent3 x₀ 0 0 *
            iotaGL (diagUnitGL2 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n₁ * u)) := by
          rw [iotaGL_diagUnitGL2_mul_upper12, hprod, mul_assoc]
      _ = upperUnipotent3 x₀ 0 0 * iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n₂ * diagUnitGL2 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n₁ * u)) := by
          rw [((commute_iotaGL_scalarPi_upper12 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ x₀).zpow_left n₂).eq, map_mul, map_zpow, mul_assoc]
  ·
    set x' : v.adicCompletion ℚ := (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) ^ (-n₂) * x₀ with hx'
    have hvx' : Valued.v x' ≤ WithZero.exp m := by
      rw [hx', map_mul, hvπ, hvx₀', ← WithZero.exp_add]
      exact WithZero.exp_le_exp.mpr (by omega)
    refine key (upperUnipotent3 0 x' 0) (hm x' hvx').2 0 x₀ 0 ?_ (by rw [zero_add]; exact hx₀)
    have hprod : (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) ^ n₂ * x' = x₀ := by
      rw [hx', zpow_neg, ← mul_assoc, mul_inv_cancel₀ (zpow_ne_zero n₂ hπ), one_mul]
    calc iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n₂ * diagUnitGL2 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n₁ * u)) * upperUnipotent3 0 x' 0
        = iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) ^ n₂ * (iotaGL (diagUnitGL2 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n₁ * u)) *
            upperUnipotent3 0 x' 0) := by rw [map_mul, map_zpow, mul_assoc]
      _ = (iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) ^ n₂ * upperUnipotent3 0 x' 0) *
            iotaGL (diagUnitGL2 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n₁ * u)) := by
          rw [(commute_iotaGL_diagUnitGL2_upper23 _ x').eq, mul_assoc]
      _ = upperUnipotent3 0 x₀ 0 * iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n₂ * diagUnitGL2 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n₁ * u)) := by
          rw [iotaGL_scalarPi_zpow_mul_upper23, hprod, map_mul, map_zpow, mul_assoc]

p2m_export "Ws46.SUP" "core"
end Ws46.SUP

namespace Ws46
namespace TA

open Finset Polynomial

theorem sum_reverse_coeff_mul_eq_zero (A : ℤ → ℂ) (C : Polynomial ℂ) (N₀ : ℤ)
    (hrec : ∀ n₁ : ℤ, N₀ ≤ n₁ → ∑ i ∈ range (C.natDegree + 1), C.coeff i * A (n₁ + i) = 0)
    (x : ℤ) (hx : N₀ ≤ x - C.natDegree) :
    ∑ j ∈ range (C.reverse.natDegree + 1), C.reverse.coeff j * A (x - j) = 0 := by
  set d := C.natDegree with hd

  have hsub : range (C.reverse.natDegree + 1) ⊆ range (d + 1) := by
    apply range_subset_range.mpr
    have := reverse_natDegree_le C
    omega
  rw [sum_subset hsub (fun j _ hj => by
    have hj' : C.reverse.natDegree < j := by
      simp only [mem_range, not_lt] at hj; omega
    rw [coeff_eq_zero_of_natDegree_lt hj', zero_mul])]

  have hterm : ∀ j ∈ range (d + 1), C.reverse.coeff j * A (x - j) = C.coeff (d - j) * A (x - j) := by
    intro j hj
    rw [coeff_reverse, revAt_le (by simp only [mem_range] at hj; omega)]
  rw [sum_congr rfl hterm]

  have hrefl := sum_range_reflect (fun i => C.coeff i * A (x - d + i)) (d + 1)
  have hterm2 : ∀ j ∈ range (d + 1), C.coeff (d + 1 - 1 - j) * A (x - d + ((d + 1 - 1 - j : ℕ) : ℤ)) =
      C.coeff (d - j) * A (x - j) := by
    intro j hj
    simp only [mem_range] at hj
    have hjd : j ≤ d := by omega
    rw [show d + 1 - 1 - j = d - j by omega]
    congr 1
    rw [Nat.cast_sub hjd]; ring_nf
  rw [← sum_congr rfl hterm2, hrefl]
  exact hrec (x - d) hx

theorem rational_of_recurrences (A : ℤ × ℤ → ℂ) (N₁ : ℤ)
    (hsupp : ∀ n : ℤ × ℤ, (n.1 < N₁ ∨ n.2 < N₁) → A n = 0)
    (C₁ : Polynomial ℂ) (hC₁ : C₁ ≠ 0) (N₀ : ℤ)
    (hrec₁ : ∀ n₁ n₂ : ℤ, N₀ ≤ n₁ → ∑ i ∈ range (C₁.natDegree + 1), C₁.coeff i * A (n₁ + i, n₂) = 0)
    (C₂ : Polynomial ℂ) (hC₂ : C₂ ≠ 0) (N₀' : ℤ)
    (hrec₂ : ∀ n₁ n₂ : ℤ, N₀' ≤ n₂ → ∑ i ∈ range (C₂.natDegree + 1), C₂.coeff i * A (n₁, n₂ + i) = 0) :
    ∃ (N : ℤ) (D₁ D₂ : Polynomial ℂ) (M : ℕ), D₁.eval 0 ≠ 0 ∧ D₂.eval 0 ≠ 0 ∧
      (∀ n : ℤ × ℤ, (n.1 < N ∨ n.2 < N) → A n = 0) ∧
      (∀ m₁ m₂ : ℕ, (M ≤ m₁ ∨ M ≤ m₂) →
        ∑ i ∈ range (D₁.natDegree + 1), ∑ l ∈ range (D₂.natDegree + 1),
          D₁.coeff i * D₂.coeff l * A (N + (m₁ : ℤ) - (i : ℤ), N + (m₂ : ℤ) - (l : ℤ)) = 0) := by
  refine ⟨N₁, C₁.reverse, C₂.reverse, C₁.natDegree + C₂.natDegree + (N₀ - N₁).toNat + (N₀' - N₁).toNat,
    ?_, ?_, hsupp, ?_⟩
  · rw [← coeff_zero_eq_eval_zero, coeff_zero_reverse]; exact leadingCoeff_ne_zero.mpr hC₁
  · rw [← coeff_zero_eq_eval_zero, coeff_zero_reverse]; exact leadingCoeff_ne_zero.mpr hC₂
  intro m₁ m₂ hm
  rcases hm with h1 | h2
  ·
    have hinner : ∀ l : ℕ, ∑ i ∈ range (C₁.reverse.natDegree + 1),
        C₁.reverse.coeff i * A (N₁ + (m₁ : ℤ) - (i : ℤ), N₁ + (m₂ : ℤ) - (l : ℤ)) = 0 := by
      intro l
      have := sum_reverse_coeff_mul_eq_zero (fun z => A (z, N₁ + (m₂ : ℤ) - (l : ℤ))) C₁ N₀
        (fun n₁ hn₁ => hrec₁ n₁ _ hn₁) (N₁ + m₁) (by
          have : ((N₀ - N₁).toNat : ℤ) ≥ N₀ - N₁ := Int.self_le_toNat _
          push_cast at h1 ⊢; omega)
      simpa using this
    calc ∑ i ∈ range (C₁.reverse.natDegree + 1), ∑ l ∈ range (C₂.reverse.natDegree + 1),
          C₁.reverse.coeff i * C₂.reverse.coeff l * A (N₁ + (m₁ : ℤ) - (i : ℤ), N₁ + (m₂ : ℤ) - (l : ℤ))
        = ∑ l ∈ range (C₂.reverse.natDegree + 1), C₂.reverse.coeff l *
            ∑ i ∈ range (C₁.reverse.natDegree + 1),
              C₁.reverse.coeff i * A (N₁ + (m₁ : ℤ) - (i : ℤ), N₁ + (m₂ : ℤ) - (l : ℤ)) := by
          rw [sum_comm]; refine sum_congr rfl fun l _ => ?_; rw [mul_sum]; refine sum_congr rfl fun i _ => ?_; ring
      _ = 0 := by simp [hinner]
  · have hinner : ∀ i : ℕ, ∑ l ∈ range (C₂.reverse.natDegree + 1),
        C₂.reverse.coeff l * A (N₁ + (m₁ : ℤ) - (i : ℤ), N₁ + (m₂ : ℤ) - (l : ℤ)) = 0 := by
      intro i
      have := sum_reverse_coeff_mul_eq_zero (fun z => A (N₁ + (m₁ : ℤ) - (i : ℤ), z)) C₂ N₀'
        (fun n₂ hn₂ => hrec₂ _ n₂ hn₂) (N₁ + m₂) (by
          have : ((N₀' - N₁).toNat : ℤ) ≥ N₀' - N₁ := Int.self_le_toNat _
          push_cast at h2 ⊢; omega)
      simpa using this
    calc ∑ i ∈ range (C₁.reverse.natDegree + 1), ∑ l ∈ range (C₂.reverse.natDegree + 1),
          C₁.reverse.coeff i * C₂.reverse.coeff l * A (N₁ + (m₁ : ℤ) - (i : ℤ), N₁ + (m₂ : ℤ) - (l : ℤ))
        = ∑ i ∈ range (C₁.reverse.natDegree + 1), C₁.reverse.coeff i *
            ∑ l ∈ range (C₂.reverse.natDegree + 1),
              C₂.reverse.coeff l * A (N₁ + (m₁ : ℤ) - (i : ℤ), N₁ + (m₂ : ℤ) - (l : ℤ)) := by
          refine sum_congr rfl fun i _ => ?_; rw [mul_sum]; refine sum_congr rfl fun l _ => ?_; ring
      _ = 0 := by simp [hinner]

section Shift
variable {K : Type*} [Field K]

theorem diagUnitGL2_zpow_mul_pow (u : Kˣ) (n : ℤ) (i : ℕ) :
    diagUnitGL2 (u ^ n) * diagUnitGL2 u ^ i = diagUnitGL2 (u ^ (n + (i : ℤ))) := by
  rw [← diagHom_apply, ← diagHom_apply, ← diagHom_apply, ← map_pow, ← map_mul, ← zpow_natCast, ← zpow_add]

theorem scalarPi_commute_diagUnitGL2 (π : K) (hπ : π ≠ 0) (w : Kˣ) :
    Commute (UnramifiedWhittaker.scalarPi π hπ) (diagUnitGL2 w) := by
  unfold Commute SemiconjBy
  apply Units.ext
  simp only [Units.val_mul, coe_diagUnitGL2, UnramifiedWhittaker.scalarPi, Matrix.GeneralLinearGroup.mkOfDetNeZero]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

theorem torus_mul_T₁ (π : K) (hπ : π ≠ 0) (n₁ n₂ : ℤ) (i : ℕ) :
    iotaGL (UnramifiedWhittaker.scalarPi π hπ ^ n₂ * diagUnitGL2 (Units.mk0 π hπ ^ n₁)) *
        iotaGL (diagUnitGL2 (Units.mk0 π hπ)) ^ i =
      iotaGL (UnramifiedWhittaker.scalarPi π hπ ^ n₂ * diagUnitGL2 (Units.mk0 π hπ ^ (n₁ + (i : ℤ)))) := by
  rw [← map_pow, ← map_mul, mul_assoc, diagUnitGL2_zpow_mul_pow]

theorem torus_mul_T₂ (π : K) (hπ : π ≠ 0) (n₁ n₂ : ℤ) (i : ℕ) :
    iotaGL (UnramifiedWhittaker.scalarPi π hπ ^ n₂ * diagUnitGL2 (Units.mk0 π hπ ^ n₁)) *
        iotaGL (UnramifiedWhittaker.scalarPi π hπ) ^ i =
      iotaGL (UnramifiedWhittaker.scalarPi π hπ ^ (n₂ + (i : ℤ)) * diagUnitGL2 (Units.mk0 π hπ ^ n₁)) := by
  rw [← map_pow, ← map_mul, mul_assoc, ((scalarPi_commute_diagUnitGL2 π hπ _).symm.pow_right i).eq,
    ← mul_assoc, ← zpow_natCast, ← zpow_add]

end Shift

end Ws46.TA

namespace Ws1
namespace WAlg

theorem hsymm_one_zero (m : ℕ) :
    (∑ i ∈ Finset.range (m + 1), (1 : ℂ) ^ i * (0 : ℂ) ^ (m - i)) = 1 := by
  rw [Finset.sum_eq_single_of_mem m (Finset.mem_range.mpr (Nat.lt_succ_self m))]
  · simp
  · intro i hi hne
    have h : m - i ≠ 0 := by
      have := Finset.mem_range.mp hi
      omega
    simp [h]

private theorem _root_.Ws1.WAlg.core (A : ℤ × ℤ → ℂ)
    (h : ∃ (N₁ : ℤ) (D₁ D₂ : Polynomial ℂ) (M : ℕ), D₁.eval 0 ≠ 0 ∧ D₂.eval 0 ≠ 0 ∧
      (∀ n : ℤ × ℤ, (n.1 < N₁ ∨ n.2 < N₁) → A n = 0) ∧
      (∀ m₁ m₂ : ℕ, (M ≤ m₁ ∨ M ≤ m₂) →
        ∑ i ∈ Finset.range (D₁.natDegree + 1), ∑ l ∈ Finset.range (D₂.natDegree + 1),
          D₁.coeff i * D₂.coeff l * A (N₁ + (m₁ : ℤ) - (i : ℤ), N₁ + (m₂ : ℤ) - (l : ℤ)) = 0)) :
    ∃ (N₁ : ℤ) (D₁ D₂ : Polynomial ℂ) (P : MvPolynomial (Fin 2) ℂ) (r : ℝ),
      D₁.eval 0 ≠ 0 ∧ D₂.eval 0 ≠ 0 ∧ 0 < r ∧
      (∀ n : ℤ × ℤ, (n.1 < N₁ ∨ n.2 < N₁) → A n = 0) ∧
      ∀ X Y : ℂ, ‖X‖ < r → ‖Y‖ < r →
        Summable (fun m : ℕ × ℕ => ‖A (N₁ + (m.1 : ℤ), N₁ + (m.2 : ℤ)) * X ^ m.1 * Y ^ m.2‖) ∧
        (∑' m : ℕ × ℕ, A (N₁ + (m.1 : ℤ), N₁ + (m.2 : ℤ)) * X ^ m.1 * Y ^ m.2) * (D₁.eval X * D₂.eval Y) =
          MvPolynomial.eval ![X, Y] P := by
  obtain ⟨N₁, D₁, D₂, M, hD₁, hD₂, hsupp, hrec⟩ := h
  obtain ⟨P, hP⟩ :=
    Polynomial.exists_mvPolynomial_forall_hasSum_torusWeight_mul_eq_of_separated_recurrence
      A N₁ D₁ D₂ M hD₁ hD₂ hsupp hrec
  obtain ⟨r, hr, hXY⟩ := hP 1 0
  let f : Fin 4 → MvPolynomial (Fin 2) ℂ := ![MvPolynomial.X 0, MvPolynomial.X 1, 1, 0]
  refine ⟨N₁, D₁, D₂, MvPolynomial.C (D₁.eval 0)⁻¹ * MvPolynomial.bind₁ f P, r, hD₁, hD₂, hr, hsupp, ?_⟩
  intro X Y hX hY
  obtain ⟨hsum, heq⟩ := hXY X Y hX hY
  have hw : ∀ m : ℕ × ℕ, A (N₁ + (m.1 : ℤ), N₁ + (m.2 : ℤ)) *
      (∑ i ∈ Finset.range (m.1 + 1), (1 : ℂ) ^ i * (0 : ℂ) ^ (m.1 - i)) * X ^ m.1 * Y ^ m.2 =
      A (N₁ + (m.1 : ℤ), N₁ + (m.2 : ℤ)) * X ^ m.1 * Y ^ m.2 := by
    intro m
    rw [hsymm_one_zero, mul_one]
  simp_rw [hw] at hsum heq
  refine ⟨hsum, ?_⟩
  have hev : MvPolynomial.eval ![X, Y] (MvPolynomial.bind₁ f P) = MvPolynomial.eval ![X, Y, 1, 0] P := by
    have h := MvPolynomial.aeval_bind₁ (R := ℂ) (S := ℂ) ![X, Y] f P
    rw [MvPolynomial.aeval_eq_eval, MvPolynomial.aeval_eq_eval] at h
    have hf : (fun i => MvPolynomial.eval ![X, Y] (f i)) = ![X, Y, 1, 0] := by
      funext i
      fin_cases i <;> simp [f]
    rw [h, hf]
  rw [map_mul, MvPolynomial.eval_C, hev, ← heq]
  simp only [one_mul, zero_mul]
  field_simp

p2m_export "Ws1.WAlg" "core"
end Ws1.WAlg

open Ws46.TA LanglandsTunnell LanglandsTunnell.CubicInduction in

theorem solution
    (v : HeightOneSpectrum (𝓞 ℚ)) (ψv : AddChar (v.adicCompletion ℚ) ℂ) (hψ : ψv ≠ 1)
    (W : LocalGL3 v → ℂ) (hW : IsGL3PsiWhittakerFn ψv W)
    (hsm : ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 v, W (g * k) = W g)
    (hadm : ∀ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) →
      ∃ B : Finset (LocalGL3 v → ℂ), ∀ F ∈ gl3CyclicSubspace W,
        (∀ k ∈ Uv, ∀ g : LocalGL3 v, F (g * k) = F g) → F ∈ Submodule.span ℂ (B : Set (LocalGL3 v → ℂ)))
    (ωv : (v.adicCompletion ℚ)ˣ →* ℂˣ)
    (hω : ∀ (t : (v.adicCompletion ℚ)ˣ) (h : LocalGL3 v),
      W (Matrix.GeneralLinearGroup.scalar (Fin 3) t * h) = ((ωv t : ℂˣ) : ℂ) * W h)
    {ϖ : v.adicCompletionIntegers ℚ}
    (hπ : algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ))
    (Φ : LocalGL3 v → ℂ) (hΦ : Φ ∈ gl3CyclicSubspace W)
    (hΦsm : ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 v, Φ (g * k) = Φ g) :
    let A : ℤ × ℤ → ℂ := fun n =>
      Φ (iotaGL (UnramifiedWhittaker.scalarPi
            (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n.2 *
          diagUnitGL2 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n.1)))
    (∃ (N₁ : ℤ) (D₁ D₂ : Polynomial ℂ) (P : MvPolynomial (Fin 2) ℂ) (r : ℝ),
      D₁.eval 0 ≠ 0 ∧ D₂.eval 0 ≠ 0 ∧ 0 < r ∧
      (∀ n : ℤ × ℤ, (n.1 < N₁ ∨ n.2 < N₁) → A n = 0) ∧
      ∀ X Y : ℂ, ‖X‖ < r → ‖Y‖ < r →
        Summable (fun m : ℕ × ℕ => ‖A (N₁ + (m.1 : ℤ), N₁ + (m.2 : ℤ)) * X ^ m.1 * Y ^ m.2‖) ∧
        (∑' m : ℕ × ℕ, A (N₁ + (m.1 : ℤ), N₁ + (m.2 : ℤ)) * X ^ m.1 * Y ^ m.2) * (D₁.eval X * D₂.eval Y) =
          MvPolynomial.eval ![X, Y] P) := by
  intro A

  have hΦW : IsGL3PsiWhittakerFn ψv Φ := by
    have hle : gl3CyclicSubspace W ≤ gl3PsiWhittakerFnSpace (v.adicCompletion ℚ) ℂ ψv := by
      unfold gl3CyclicSubspace
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨h, rfl⟩
      exact rightTranslate_mem_gl3PsiWhittakerFnSpace ψv h ((mem_gl3PsiWhittakerFnSpace_iff ψv W).mpr hW)
    exact (mem_gl3PsiWhittakerFnSpace_iff ψv Φ).mp (hle hΦ)

  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : v.adicCompletion ℚ, ψv x₀ ≠ 1 := by
    by_contra h
    push_neg at h
    exact hψ (AddChar.ext ψv 1 fun a => by rw [h a, AddChar.one_apply])

  obtain ⟨UΦ, hUΦo, hUΦ⟩ := hΦsm
  obtain ⟨N₁, hN₁⟩ := Ws46.SUP.core v hπ hϖ ψv x₀ hx₀ Φ hΦW UΦ hUΦo hUΦ {1} isCompact_singleton
  have hsupp : ∀ n : ℤ × ℤ, (n.1 < N₁ ∨ n.2 < N₁) → A n = 0 := by
    intro n hn
    have h := hN₁ n.1 n.2 hn 1 (by simp) 1 (Set.mem_singleton 1)
    simpa only [mul_one] using h

  by_cases hW0 : ∀ g : LocalGL3 v, W g = 0
  · have hW'0 : W = 0 := funext hW0
    have hbot : gl3CyclicSubspace W = ⊥ := by
      unfold gl3CyclicSubspace
      rw [Submodule.span_eq_bot]
      rintro _ ⟨h, rfl⟩
      simp only [hW'0, map_zero]
    have hΦ0 : Φ = 0 := by rw [hbot] at hΦ; exact (Submodule.mem_bot ℂ).mp hΦ
    have hA0 : ∀ n, A n = 0 := fun n => by show Φ _ = 0; rw [hΦ0]; rfl
    exact Ws1.WAlg.core A (rational_of_recurrences A 0 (fun n _ => hA0 n) 1 one_ne_zero 0
      (fun n₁ n₂ _ => by simp [hA0]) 1 one_ne_zero 0 (fun n₁ n₂ _ => by simp [hA0]))
  push_neg at hW0
  obtain ⟨g, hg⟩ := hW0
  have hψball : ∃ m : ℤ, ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp m → ψv x = 1 := by
    obtain ⟨Uv, hUo, hUinv⟩ := hsm
    have hW' : ∀ (x y z : v.adicCompletion ℚ) (h : LocalGL3 v), W (upperUnipotent3 x y z * h) = ψv (x + y) * W h := hW

    have hcu : Continuous fun x : v.adicCompletion ℚ => (upperUnipotent3 x 0 0 : LocalGL3 v) := by
      refine Units.continuous_iff.2 ⟨?_, ?_⟩
      · show Continuous fun x : v.adicCompletion ℚ => ((upperUnipotent3 x 0 0 : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))
        simp only [upperUnipotent3_coe]
        refine continuous_matrix fun i j => ?_
        fin_cases i <;> fin_cases j <;> simp <;> fun_prop
      · show Continuous fun x : v.adicCompletion ℚ => (((upperUnipotent3 x 0 0 : LocalGL3 v))⁻¹ : LocalGL3 v).val
        have : ∀ x : v.adicCompletion ℚ, (((upperUnipotent3 x 0 0 : LocalGL3 v))⁻¹ : LocalGL3 v).val =
            !![1, -x, x * 0 - 0; 0, 1, -0; 0, 0, 1] := fun x => rfl
        simp only [this]
        refine continuous_matrix fun i j => ?_
        fin_cases i <;> fin_cases j <;> simp <;> fun_prop
    have hc : Continuous fun x : v.adicCompletion ℚ => g⁻¹ * (upperUnipotent3 x 0 0 : LocalGL3 v) * g :=
      (continuous_const.mul hcu).mul continuous_const
    have h0 : g⁻¹ * (upperUnipotent3 (0 : v.adicCompletion ℚ) 0 0 : LocalGL3 v) * g = 1 := by
      rw [upperUnipotent3_zero, mul_one, inv_mul_cancel]
    have hmem : {x : v.adicCompletion ℚ | g⁻¹ * (upperUnipotent3 x 0 0 : LocalGL3 v) * g ∈ (Uv : Set (LocalGL3 v))} ∈
        nhds (0 : v.adicCompletion ℚ) :=
      hc.continuousAt.preimage_mem_nhds (by rw [h0]; exact hUo.mem_nhds Uv.one_mem)
    obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.mp hmem
    have hγ0 : (MonoidWithZeroHom.ValueGroup₀.embedding γ.1 : WithZero (Multiplicative ℤ)) ≠ 0 :=
      (map_ne_zero MonoidWithZeroHom.ValueGroup₀.embedding).mpr γ.ne_zero
    refine ⟨WithZero.log (MonoidWithZeroHom.ValueGroup₀.embedding γ.1) - 1, fun x hx => ?_⟩
    have hxγ : Valued.v.restrict x < γ.1 := by
      rw [Valuation.restrict_lt_iff_lt_embedding]
      refine lt_of_le_of_lt hx ?_
      conv_rhs => rw [← WithZero.exp_log hγ0]
      exact WithZero.exp_lt_exp.mpr (by omega)
    have hk : g⁻¹ * (upperUnipotent3 x 0 0 : LocalGL3 v) * g ∈ Uv := hγ hxγ
    have h1 := hUinv _ hk g
    rw [← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul, hW' x 0 0 g, add_zero] at h1
    exact (mul_eq_right₀ hg).mp h1

  obtain ⟨⟨C₁, hC₁, hF₁⟩, ⟨C₂, hC₂, hF₂⟩⟩ :=
    LanglandsTunnell.CubicInduction.exists_polynomial_sum_coeff_smul_rightTranslate_pow_mem_span_radical_of_admissible
      v W hsm hadm hπ hϖ Φ hΦ
  obtain ⟨hV12, hV21⟩ :=
    LanglandsTunnell.CubicInduction.exists_forall_apply_iotaGL_torus_eq_zero_of_mem_span_radical_of_isGL3PsiWhittakerFn
      v ψv hψball W hW hπ hϖ
  obtain ⟨N₀, hN₀⟩ := hV12 _ hF₁
  obtain ⟨N₀', hN₀'⟩ := hV21 _ hF₂
  have hrec₁ : ∀ n₁ n₂ : ℤ, N₀ ≤ n₁ →
      ∑ i ∈ Finset.range (C₁.natDegree + 1), C₁.coeff i * A (n₁ + i, n₂) = 0 := by
    intro n₁ n₂ hn₁
    have h := hN₀ n₁ n₂ hn₁
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h
    rw [← h]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [torus_mul_T₁]
  have hrec₂ : ∀ n₁ n₂ : ℤ, N₀' ≤ n₂ →
      ∑ i ∈ Finset.range (C₂.natDegree + 1), C₂.coeff i * A (n₁, n₂ + i) = 0 := by
    intro n₁ n₂ hn₂
    have h := hN₀' n₁ n₂ hn₂
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h
    rw [← h]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [torus_mul_T₂]
  exact Ws1.WAlg.core A (rational_of_recurrences A N₁ hsupp C₁ hC₁ N₀ hrec₁ C₂ hC₂ N₀' hrec₂)

end S_LanglandsTunnell_CubicInduction_exists_mvPolynomial_forall_tsum_torus_apply_mul_eval_eq_of_mem_gl3CyclicSubspace
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_exists_mvPolynomial_forall_tsum_torus_apply_mul_eval_eq_of_mem_gl3CyclicSubspace (solution)
