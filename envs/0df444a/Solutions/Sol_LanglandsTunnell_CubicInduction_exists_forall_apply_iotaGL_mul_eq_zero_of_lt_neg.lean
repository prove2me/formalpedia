-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.exists_forall_apply_iotaGL_mul_eq_zero_of_lt_neg
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/23a78ed1-1493-5b81-86ab-a13549d46cc6

import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries3
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_AutomorphicForm_SmoothingKernel
import Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_ne_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_apply_iotaGL_mul_eq_zero_of_lt_neg

set_option autoImplicit false

open IsDedekindDomain NumberField

namespace TorusShellVanishing

open Matrix LanglandsTunnell.CubicInduction

section Algebra

variable {F : Type*} [Field F]

def diag3 (a b c : Fˣ) : GL (Fin 3) F where
  val := !![(a : F), 0, 0; 0, (b : F), 0; 0, 0, (c : F)]
  inv := !![((a⁻¹ : Fˣ) : F), 0, 0; 0, ((b⁻¹ : Fˣ) : F), 0; 0, 0, ((c⁻¹ : Fˣ) : F)]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

@[scoped simp] theorem coe_diag3 (a b c : Fˣ) :
    ((diag3 a b c : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      !![(a : F), 0, 0; 0, (b : F), 0; 0, 0, (c : F)] := rfl

@[scoped simp] theorem coe_inv_diag3 (a b c : Fˣ) :
    (((diag3 a b c)⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      !![((a⁻¹ : Fˣ) : F), 0, 0; 0, ((b⁻¹ : Fˣ) : F), 0; 0, 0, ((c⁻¹ : Fˣ) : F)] := rfl

theorem diag3_mul_upperUnipotent3 (a b c : Fˣ) (x y : F) :
    diag3 a b c * upperUnipotent3 x y 0 =
      upperUnipotent3 (((a * b⁻¹ : Fˣ) : F) * x) (((b * c⁻¹ : Fˣ) : F) * y) 0 * diag3 a b c := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, coe_diag3, upperUnipotent3_coe, upperUnipotent3_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;> field_simp

theorem transposeInv3_diag3 (a b c : Fˣ) : transposeInv3 (diag3 a b c) = diag3 a⁻¹ b⁻¹ c⁻¹ := by
  refine Units.ext ?_
  show (((diag3 a b c)⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)ᵀ = _
  rw [coe_inv_diag3, coe_diag3]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem longWeyl3_mul_diag3 (a b c : Fˣ) :
    (longWeyl3 : GL (Fin 3) F) * diag3 a b c = diag3 c b a * longWeyl3 := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, coe_diag3, coe_diag3, longWeyl3_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

theorem scalarPi_eq_scalar (π : F) (hπ : π ≠ 0) :
    UnramifiedWhittaker.scalarPi π hπ = Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 π hπ) := by
  refine Units.ext ?_
  rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [UnramifiedWhittaker.scalarPi, Matrix.diagonal]

theorem iotaGL_scalarPi_zpow_mul_diagUnitGL2 (π : F) (hπ : π ≠ 0) (m : ℤ) (w : Fˣ) :
    iotaGL (UnramifiedWhittaker.scalarPi π hπ ^ m * diagUnitGL2 w) =
      diag3 (Units.mk0 π hπ ^ m * w) (Units.mk0 π hπ ^ m) 1 := by
  refine Units.ext ?_
  rw [coe_iotaGL, scalarPi_eq_scalar, ← map_zpow, Units.val_mul,
    Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, coe_diagUnitGL2, coe_diag3]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [embedMat2, Matrix.mul_apply, Matrix.diagonal]

end Algebra

section PsiArgument

variable {F : Type*} [Field F] {R : Type*} [CommRing R] [IsDomain R]

theorem apply_diag3_mul_eq_zero_of_root₁ {ψ : AddChar F R} {W : GL (Fin 3) F → R}
    (hW : IsGL3PsiWhittakerFn ψ W) (a b c : Fˣ) (g : GL (Fin 3) F) (x : F)
    (hfix : W (diag3 a b c * upperUnipotent3 x 0 0 * g) = W (diag3 a b c * g))
    (hψ : ψ (((a * b⁻¹ : Fˣ) : F) * x) ≠ 1) : W (diag3 a b c * g) = 0 := by
  rw [diag3_mul_upperUnipotent3, mul_assoc, hW, mul_zero, add_zero] at hfix
  have h : (ψ (((a * b⁻¹ : Fˣ) : F) * x) - 1) * W (diag3 a b c * g) = 0 := by
    rw [sub_mul, one_mul, hfix, sub_self]
  rcases mul_eq_zero.mp h with h | h
  · exact absurd (sub_eq_zero.mp h) hψ
  · exact h

theorem apply_diag3_mul_eq_zero_of_root₂ {ψ : AddChar F R} {W : GL (Fin 3) F → R}
    (hW : IsGL3PsiWhittakerFn ψ W) (a b c : Fˣ) (g : GL (Fin 3) F) (y : F)
    (hfix : W (diag3 a b c * upperUnipotent3 0 y 0 * g) = W (diag3 a b c * g))
    (hψ : ψ (((b * c⁻¹ : Fˣ) : F) * y) ≠ 1) : W (diag3 a b c * g) = 0 := by
  rw [diag3_mul_upperUnipotent3, mul_assoc, hW, mul_zero, zero_add] at hfix
  have h : (ψ (((b * c⁻¹ : Fˣ) : F) * y) - 1) * W (diag3 a b c * g) = 0 := by
    rw [sub_mul, one_mul, hfix, sub_self]
  rcases mul_eq_zero.mp h with h | h
  · exact absurd (sub_eq_zero.mp h) hψ
  · exact h

end PsiArgument

section Topology

variable {F : Type*} [Field F] [TopologicalSpace F] [IsTopologicalRing F]

theorem continuous_upperUnipotent3_left : Continuous fun x : F => upperUnipotent3 x (0 : F) 0 := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    show Continuous fun x : F => ((upperUnipotent3 x (0 : F) 0 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) i j
    fin_cases i <;> fin_cases j <;> simp [continuous_const, continuous_id']
  · refine continuous_matrix fun i j => ?_
    show Continuous fun x : F =>
      (((upperUnipotent3 x (0 : F) 0)⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) i j
    fin_cases i <;> fin_cases j <;> simp [upperUnipotent3, continuous_const, continuous_neg]

theorem continuous_upperUnipotent3_mid : Continuous fun y : F => upperUnipotent3 (0 : F) y 0 := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    show Continuous fun y : F => ((upperUnipotent3 (0 : F) y 0 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) i j
    fin_cases i <;> fin_cases j <;> simp [continuous_const, continuous_id']
  · refine continuous_matrix fun i j => ?_
    show Continuous fun y : F =>
      (((upperUnipotent3 (0 : F) y 0)⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) i j
    fin_cases i <;> fin_cases j <;> simp [upperUnipotent3, continuous_const, continuous_neg]

end Topology

section Balls

open Filter Topology

variable {F : Type*} [Field F] [Valued F (WithZero (Multiplicative ℤ))]

theorem exists_forall_valued_le_exp_neg_mem {s : Set F} (hs : s ∈ 𝓝 (0 : F)) :
    ∃ L : ℕ, ∀ x : F, Valued.v x ≤ WithZero.exp (-(L : ℤ)) → x ∈ s := by
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.mp hs
  let vv : Valuation F (WithZero (Multiplicative ℤ)) := Valued.v
  let g : (WithZero (Multiplicative ℤ))ˣ := Units.map (MonoidWithZeroHom.ValueGroup₀.embedding (f := MonoidWithZeroHom.ofClass vv)) γ
  refine ⟨(WithZero.log (g : WithZero (Multiplicative ℤ))).natAbs + 1, fun x hx => hγ ?_⟩
  show Valued.v.restrict x < γ.1
  rw [Valuation.restrict_lt_iff_lt_embedding]
  show Valued.v x < (g : WithZero (Multiplicative ℤ))
  calc Valued.v x ≤ WithZero.exp (-(((WithZero.log (g : WithZero (Multiplicative ℤ))).natAbs + 1 : ℕ) : ℤ)) := hx
    _ < WithZero.exp (WithZero.log (g : WithZero (Multiplicative ℤ))) := WithZero.exp_lt_exp.mpr (by omega)
    _ = g := WithZero.exp_log g.ne_zero

theorem exists_forall_valued_le_exp_neg_mem_subgroup {G : Type*} [Group G] [TopologicalSpace G]
    (U : Subgroup G) (hU : IsOpen (U : Set G)) {φ : F → G} (hφ : Continuous φ) (h0 : φ 0 = 1) :
    ∃ L : ℕ, ∀ x : F, Valued.v x ≤ WithZero.exp (-(L : ℤ)) → φ x ∈ U := by
  have hs : φ ⁻¹' (U : Set G) ∈ 𝓝 (0 : F) :=
    hφ.continuousAt.preimage_mem_nhds (hU.mem_nhds (by rw [h0]; exact U.one_mem))
  exact exists_forall_valued_le_exp_neg_mem hs

theorem valued_units_inv_mul_le (r : Fˣ) (x₀ : F) (n k₀ : ℤ) (L₀ : ℕ)
    (hr : Valued.v (r : F) = WithZero.exp (-n)) (hx₀ : Valued.v x₀ = WithZero.exp k₀)
    (hn : n < -((L₀ : ℤ) + (k₀.natAbs : ℕ))) :
    Valued.v (((r⁻¹ : Fˣ) : F) * x₀) ≤ WithZero.exp (-(L₀ : ℤ)) := by
  rw [map_mul, Units.val_inv_eq_inv_val, map_inv₀, hr, hx₀, ← WithZero.exp_neg, neg_neg,
    ← WithZero.exp_add, WithZero.exp_le_exp]
  omega

end Balls

end TorusShellVanishing
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_apply_iotaGL_mul_eq_zero_of_lt_neg.TorusShellVanishing"

open AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker LanglandsTunnell.Converse

open scoped nonZeroDivisors

open TorusShellVanishing LanglandsTunnell.CubicInduction in

theorem solution
    (v : HeightOneSpectrum (𝓞 ℚ)) (ψv : AddChar (v.adicCompletion ℚ) ℂ)
    (hψinv : ψv = (NumberField.StandardAddChar.psiLocal ℚ v)⁻¹)
    (W : LocalGL3 v → ℂ) (hW : IsGL3PsiWhittakerFn ψv W)
    {ϖ : v.adicCompletionIntegers ℚ}
    (hπ : algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ))
    (C : Set (LocalGL3 v)) (U : Subgroup (LocalGL3 v)) (hU : IsOpen (U : Set (LocalGL3 v)))
    (hfix : ∀ y ∈ C, ∀ k' ∈ U, ∀ x : LocalGL3 v, W (x * k' * y) = W (x * y)) :
    ∃ L : ℕ, ∀ y ∈ C, ∀ n : ℤ × ℤ, (n.1 < -(L : ℤ) ∨ n.2 < -(L : ℤ)) →
      ∀ u : (v.adicCompletion ℚ)ˣ, Valued.v (u : v.adicCompletion ℚ) = 1 →
        W (iotaGL (UnramifiedWhittaker.scalarPi
              (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n.2 *
            diagUnitGL2 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ
              ^ n.1 * u)) * y) = 0 ∧
        W (longWeyl3 * transposeInv3 (iotaGL (UnramifiedWhittaker.scalarPi
              (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n.2 *
            diagUnitGL2 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ
              ^ n.1 * u))) * y) = 0 := by

  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : v.adicCompletion ℚ, ψv x₀ ≠ 1 := by
    obtain ⟨x, hx⟩ := AddChar.ne_one_iff.mp (LanglandsTunnell.TateLocal.psiLocal_ne_one ℚ v)
    refine ⟨-x, ?_⟩
    rwa [hψinv, AddChar.inv_apply, neg_neg]
  have hx₀0 : x₀ ≠ 0 := by
    rintro rfl
    exact hx₀ (AddChar.map_zero_eq_one ψv)
  have hvx₀ : Valued.v x₀ = WithZero.exp (WithZero.log (Valued.v x₀)) :=
    (WithZero.exp_log ((Valuation.ne_zero_iff _).mpr hx₀0)).symm

  obtain ⟨L₁, hL₁⟩ := exists_forall_valued_le_exp_neg_mem_subgroup U hU
    (continuous_upperUnipotent3_left (F := v.adicCompletion ℚ)) (by simp)
  obtain ⟨L₂, hL₂⟩ := exists_forall_valued_le_exp_neg_mem_subgroup U hU
    (continuous_upperUnipotent3_mid (F := v.adicCompletion ℚ)) (by simp)
  obtain ⟨L₃, hL₃⟩ := exists_forall_valued_le_exp_neg_mem_subgroup U hU
    ((continuous_const.mul (continuous_upperUnipotent3_left (F := v.adicCompletion ℚ))).mul continuous_const :
      Continuous fun x : v.adicCompletion ℚ => (longWeyl3 : LocalGL3 v)⁻¹ * upperUnipotent3 x 0 0 * longWeyl3)
    (by simp)
  obtain ⟨L₄, hL₄⟩ := exists_forall_valued_le_exp_neg_mem_subgroup U hU
    ((continuous_const.mul (continuous_upperUnipotent3_mid (F := v.adicCompletion ℚ))).mul continuous_const :
      Continuous fun y : v.adicCompletion ℚ => (longWeyl3 : LocalGL3 v)⁻¹ * upperUnipotent3 0 y 0 * longWeyl3)
    (by simp)
  have hball : ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (-((L₁ + L₂ + L₃ + L₄ : ℕ) : ℤ)) →
      upperUnipotent3 x 0 0 ∈ U ∧ upperUnipotent3 0 x 0 ∈ U ∧
        (longWeyl3 : LocalGL3 v)⁻¹ * upperUnipotent3 x 0 0 * longWeyl3 ∈ U ∧
        (longWeyl3 : LocalGL3 v)⁻¹ * upperUnipotent3 0 x 0 * longWeyl3 ∈ U := by
    intro x hx
    exact ⟨hL₁ x (hx.trans (WithZero.exp_le_exp.mpr (by push_cast; omega))),
      hL₂ x (hx.trans (WithZero.exp_le_exp.mpr (by push_cast; omega))),
      hL₃ x (hx.trans (WithZero.exp_le_exp.mpr (by push_cast; omega))),
      hL₄ x (hx.trans (WithZero.exp_le_exp.mpr (by push_cast; omega)))⟩

  refine ⟨L₁ + L₂ + L₃ + L₄ + (WithZero.log (Valued.v x₀)).natAbs, fun y hy n hn u hu => ?_⟩

  set L₀ : ℕ := L₁ + L₂ + L₃ + L₄ with hL₀
  set k₀ : ℤ := WithZero.log (Valued.v x₀) with hk₀
  set c : (v.adicCompletion ℚ)ˣ :=
    Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n.2 with hc
  set w : (v.adicCompletion ℚ)ˣ :=
    Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n.1 * u with hw
  have hvw : Valued.v (w : v.adicCompletion ℚ) = WithZero.exp (-n.1) := by
    rw [hw, Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_mk0, map_mul, map_zpow₀, hϖ, hu, mul_one,
      ← WithZero.exp_zsmul, smul_eq_mul, mul_neg, mul_one]
  have hvc : Valued.v (c : v.adicCompletion ℚ) = WithZero.exp (-n.2) := by
    rw [hc, Units.val_zpow_eq_zpow_val, Units.val_mk0, map_zpow₀, hϖ, ← WithZero.exp_zsmul, smul_eq_mul,
      mul_neg, mul_one]
  have hι : iotaGL (UnramifiedWhittaker.scalarPi
        (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n.2 * diagUnitGL2 w) =
      diag3 (c * w) c 1 :=
    iotaGL_scalarPi_zpow_mul_diagUnitGL2 _ hπ n.2 w
  have hdual : (longWeyl3 : LocalGL3 v) * transposeInv3 (diag3 (c * w) c 1) =
      diag3 1 c⁻¹ (c * w)⁻¹ * longWeyl3 := by
    rw [transposeInv3_diag3, inv_one, longWeyl3_mul_diag3]

  have hr₁ : c * w * c⁻¹ = w := by rw [mul_comm c w, mul_inv_cancel_right]
  have hr₂ : c * (1 : (v.adicCompletion ℚ)ˣ)⁻¹ = c := by rw [inv_one, mul_one]
  have hr₃ : (1 : (v.adicCompletion ℚ)ˣ) * c⁻¹⁻¹ = c := by rw [inv_inv, one_mul]
  have hr₄ : c⁻¹ * (c * w)⁻¹⁻¹ = w := by rw [inv_inv, inv_mul_cancel_left]

  have hfix₁ : ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (-(L₀ : ℤ)) →
      W (diag3 (c * w) c 1 * upperUnipotent3 x 0 0 * y) = W (diag3 (c * w) c 1 * y) :=
    fun x hx => hfix y hy _ (hball x hx).1 _
  have hfix₂ : ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (-(L₀ : ℤ)) →
      W (diag3 (c * w) c 1 * upperUnipotent3 0 x 0 * y) = W (diag3 (c * w) c 1 * y) :=
    fun x hx => hfix y hy _ (hball x hx).2.1 _
  have hfix₃ : ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (-(L₀ : ℤ)) →
      W (diag3 1 c⁻¹ (c * w)⁻¹ * upperUnipotent3 x 0 0 * ((longWeyl3 : LocalGL3 v) * y)) =
        W (diag3 1 c⁻¹ (c * w)⁻¹ * ((longWeyl3 : LocalGL3 v) * y)) := by
    intro x hx
    have h := hfix y hy _ (hball x hx).2.2.1 (diag3 1 c⁻¹ (c * w)⁻¹ * longWeyl3)
    have e : diag3 1 c⁻¹ (c * w)⁻¹ * (longWeyl3 : LocalGL3 v) *
        ((longWeyl3 : LocalGL3 v)⁻¹ * upperUnipotent3 x 0 0 * longWeyl3) * y =
          diag3 1 c⁻¹ (c * w)⁻¹ * upperUnipotent3 x 0 0 * (longWeyl3 * y) := by group
    rw [e, mul_assoc (diag3 1 c⁻¹ (c * w)⁻¹) (longWeyl3 : LocalGL3 v) y] at h
    exact h
  have hfix₄ : ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (-(L₀ : ℤ)) →
      W (diag3 1 c⁻¹ (c * w)⁻¹ * upperUnipotent3 0 x 0 * ((longWeyl3 : LocalGL3 v) * y)) =
        W (diag3 1 c⁻¹ (c * w)⁻¹ * ((longWeyl3 : LocalGL3 v) * y)) := by
    intro x hx
    have h := hfix y hy _ (hball x hx).2.2.2 (diag3 1 c⁻¹ (c * w)⁻¹ * longWeyl3)
    have e : diag3 1 c⁻¹ (c * w)⁻¹ * (longWeyl3 : LocalGL3 v) *
        ((longWeyl3 : LocalGL3 v)⁻¹ * upperUnipotent3 0 x 0 * longWeyl3) * y =
          diag3 1 c⁻¹ (c * w)⁻¹ * upperUnipotent3 0 x 0 * (longWeyl3 * y) := by group
    rw [e, mul_assoc (diag3 1 c⁻¹ (c * w)⁻¹) (longWeyl3 : LocalGL3 v) y] at h
    exact h

  rw [hι, hdual, mul_assoc (diag3 1 c⁻¹ (c * w)⁻¹)]
  rcases hn with hn | hn
  ·
    have hsmall : Valued.v (((w⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) * x₀) ≤
        WithZero.exp (-(L₀ : ℤ)) :=
      valued_units_inv_mul_le w x₀ n.1 k₀ L₀ hvw hvx₀ (by push_cast at hn ⊢; omega)
    refine ⟨?_, ?_⟩
    · refine apply_diag3_mul_eq_zero_of_root₁ hW _ _ _ y _ (hfix₁ _ hsmall) ?_
      rwa [hr₁, Units.mul_inv_cancel_left]
    · refine apply_diag3_mul_eq_zero_of_root₂ hW _ _ _ _ _ (hfix₄ _ hsmall) ?_
      rwa [hr₄, Units.mul_inv_cancel_left]
  ·
    have hsmall : Valued.v (((c⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) * x₀) ≤
        WithZero.exp (-(L₀ : ℤ)) :=
      valued_units_inv_mul_le c x₀ n.2 k₀ L₀ hvc hvx₀ (by push_cast at hn ⊢; omega)
    refine ⟨?_, ?_⟩
    · refine apply_diag3_mul_eq_zero_of_root₂ hW _ _ _ y _ (hfix₂ _ hsmall) ?_
      rwa [hr₂, Units.mul_inv_cancel_left]
    · refine apply_diag3_mul_eq_zero_of_root₁ hW _ _ _ _ _ (hfix₃ _ hsmall) ?_
      rwa [hr₃, Units.mul_inv_cancel_left]

end S_LanglandsTunnell_CubicInduction_exists_forall_apply_iotaGL_mul_eq_zero_of_lt_neg
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_apply_iotaGL_mul_eq_zero_of_lt_neg (solution)
