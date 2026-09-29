-- Prove2me | solution 1 for LT.TwistedNorm.setOf_exists_mem_center_subset_and_exists_and_eq_iff_of_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/d6b3f7d9-61f5-5d90-b005-b574223be5e3

import Definitions.Def_TwistedNormClasses
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Theorems.Thm_LT_TwistedNorm_exists_eq_inv_mul_mul_map_iff_norm_eq_of_diagonal
import Theorems.Thm_LT_TwistedNorm_exists_mem_hyperbolicCell_and_normClassMap_eq_iff_norm_div_ne_one
import Theorems.Thm_LT_TwistedNorm_exists_sigmaConj_diagonal_of_mem_hyperbolicCell_of_normClassMap_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LT_TwistedNorm_setOf_exists_mem_center_subset_and_exists_and_eq_iff_of_diagonal

set_option autoImplicit false

namespace LT
p2m_export "LT" "mk TwistedNorm.SigmaConjClasses TwistedNorm.SigmaConjClasses.mk TwistedNorm.SigmaConjClasses.mk_eq_mk_iff_exists_eq_inv_mul_mul_map TwistedNorm.normClassMap TwistedNorm.exists_eq_inv_mul_mul_map_iff_norm_eq_of_diagonal TwistedNorm.exists_mem_hyperbolicCell_and_normClassMap_eq_iff_norm_div_ne_one TwistedNorm.exists_sigmaConj_diagonal_of_mem_hyperbolicCell_of_normClassMap_eq"
namespace TwistedNorm
p2m_export "LT.TwistedNorm" "SigmaConjClasses SigmaConjClasses.mk SigmaConjClasses.mk_eq_mk_iff_exists_eq_inv_mul_mul_map normClassMap exists_eq_inv_mul_mul_map_iff_norm_eq_of_diagonal exists_mem_hyperbolicCell_and_normClassMap_eq_iff_norm_div_ne_one exists_sigmaConj_diagonal_of_mem_hyperbolicCell_of_normClassMap_eq"
namespace CuspClassesProof
p2m_open "LT.TwistedNorm LT"

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

open Matrix

theorem coe_map_apply (σ : L ≃ₐ[K] L) (g : GL (Fin 2) L) (i j : Fin 2) :
    ((Matrix.GeneralLinearGroup.map (σ : L →+* L) g : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) i j =
      σ ((g : Matrix (Fin 2) (Fin 2) L) i j) :=
  Matrix.GeneralLinearGroup.map_apply _ _ _ _

theorem det_ne (g : GL (Fin 2) L) :
    (g : Matrix (Fin 2) (Fin 2) L) 0 0 * (g : Matrix (Fin 2) (Fin 2) L) 1 1 -
      (g : Matrix (Fin 2) (Fin 2) L) 0 1 * (g : Matrix (Fin 2) (Fin 2) L) 1 0 ≠ 0 := by
  have h := (Matrix.GeneralLinearGroup.det g).ne_zero
  rwa [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two] at h

theorem upper_mul {a b : GL (Fin 2) L} (ha : (a : Matrix (Fin 2) (Fin 2) L) 1 0 = 0)
    (hb : (b : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) : ((a * b : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 := by
  simp [Matrix.mul_apply, Fin.sum_univ_two, ha, hb]

theorem upper_inv {a : GL (Fin 2) L} (ha : (a : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) :
    ((a⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 := by
  have h00 : (a : Matrix (Fin 2) (Fin 2) L) 0 0 ≠ 0 := by
    have h := det_ne a; rw [ha, mul_zero, sub_zero] at h; exact left_ne_zero_of_mul h
  have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) L => M 1 0) (Units.inv_mul a)
  simp only [Matrix.mul_apply, Fin.sum_univ_two, ha, mul_zero, add_zero,
    Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0)] at h
  exact (mul_eq_zero.mp h).resolve_right h00

theorem upper_map (σ : L ≃ₐ[K] L) {a : GL (Fin 2) L} (ha : (a : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) :
    ((Matrix.GeneralLinearGroup.map (σ : L →+* L) a : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 := by
  rw [coe_map_apply, ha, map_zero]

theorem exists_val_eq_smul_one_of_mem_center {z : GL (Fin 2) L} (hz : z ∈ Subgroup.center (GL (Fin 2) L)) :
    ∃ c : L, c ≠ 0 ∧ (z : Matrix (Fin 2) (Fin 2) L) = c • (1 : Matrix (Fin 2) (Fin 2) L) := by
  obtain ⟨c, hc⟩ := Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mp hz
  have hc' : (z : Matrix (Fin 2) (Fin 2) L) = c • (1 : Matrix (Fin 2) (Fin 2) L) := by
    rw [← hc]; ext i j; simp [Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.one_apply]
  refine ⟨c, ?_, hc'⟩
  intro h0
  have h := det_ne z
  rw [hc', h0] at h
  simp at h

theorem exists_val_mul_eq_smul_of_mem_center (t : GL (Fin 2) L) {z : GL (Fin 2) L}
    (hz : z ∈ Subgroup.center (GL (Fin 2) L)) :
    ∃ c : L, c ≠ 0 ∧ ((t * z : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) = c • (t : Matrix (Fin 2) (Fin 2) L) := by
  obtain ⟨c, hc0, hc⟩ := exists_val_eq_smul_one_of_mem_center hz
  exact ⟨c, hc0, by rw [Units.val_mul, hc, Matrix.mul_smul, mul_one]⟩

noncomputable def scalarGL (c : L) (hc : c ≠ 0) : GL (Fin 2) L :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (c • (1 : Matrix (Fin 2) (Fin 2) L))
    (by simp [Matrix.det_fin_two, Matrix.smul_apply, hc])

theorem scalarGL_val (c : L) (hc : c ≠ 0) :
    ((scalarGL c hc : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) = c • (1 : Matrix (Fin 2) (Fin 2) L) := rfl

theorem scalarGL_mem_center (c : L) (hc : c ≠ 0) : scalarGL c hc ∈ Subgroup.center (GL (Fin 2) L) := by
  refine Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mpr ⟨c, ?_⟩
  change Matrix.scalar (Fin 2) c = c • (1 : Matrix (Fin 2) (Fin 2) L)
  ext i j; simp [Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.one_apply]

noncomputable def weylGL : GL (Fin 2) L :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![(0 : L), 1; 1, 0] (by simp [Matrix.det_fin_two])

theorem weylGL_val : ((weylGL : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) = !![(0 : L), 1; 1, 0] := rfl

theorem map_weylGL (σ : L ≃ₐ[K] L) :
    Matrix.GeneralLinearGroup.map (σ : L →+* L) (weylGL : GL (Fin 2) L) = weylGL := by
  ext i j
  rw [coe_map_apply, weylGL_val]
  fin_cases i <;> fin_cases j <;> simp

theorem inv_mul_mem_center_iff' (t X : GL (Fin 2) L) :
    t⁻¹ * X ∈ Subgroup.center (GL (Fin 2) L) ↔ ∃ z ∈ Subgroup.center (GL (Fin 2) L), X = t * z :=
  ⟨fun h => ⟨t⁻¹ * X, h, by rw [mul_inv_cancel_left]⟩, fun ⟨z, hz, hX⟩ => by rwa [hX, inv_mul_cancel_left]⟩

end LT.TwistedNorm.CuspClassesProof

namespace LT
p2m_export "LT" "mk TwistedNorm.SigmaConjClasses TwistedNorm.SigmaConjClasses.mk TwistedNorm.SigmaConjClasses.mk_eq_mk_iff_exists_eq_inv_mul_mul_map TwistedNorm.normClassMap TwistedNorm.exists_eq_inv_mul_mul_map_iff_norm_eq_of_diagonal TwistedNorm.exists_mem_hyperbolicCell_and_normClassMap_eq_iff_norm_div_ne_one TwistedNorm.exists_sigmaConj_diagonal_of_mem_hyperbolicCell_of_normClassMap_eq"
namespace TwistedNorm
p2m_export "LT.TwistedNorm" "SigmaConjClasses SigmaConjClasses.mk SigmaConjClasses.mk_eq_mk_iff_exists_eq_inv_mul_mul_map normClassMap exists_eq_inv_mul_mul_map_iff_norm_eq_of_diagonal exists_mem_hyperbolicCell_and_normClassMap_eq_iff_norm_div_ne_one exists_sigmaConj_diagonal_of_mem_hyperbolicCell_of_normClassMap_eq"
namespace CuspClassesProof
p2m_open "LT.TwistedNorm LT"

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

theorem memJ_mono (σ : L ≃ₐ[K] L) {t₁ t₂ A z₁ : GL (Fin 2) L}
    (hA : (A : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) (hz₁ : z₁ ∈ Subgroup.center (GL (Fin 2) L))
    (h : t₂ = A⁻¹ * (t₁ * z₁) * Matrix.GeneralLinearGroup.map (σ : L →+* L) A) {γ : GL (Fin 2) L}
    (hγ : ∃ b : GL (Fin 2) L, (b : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
      t₂⁻¹ * (b⁻¹ * γ * Matrix.GeneralLinearGroup.map (σ : L →+* L) b) ∈ Subgroup.center (GL (Fin 2) L)) :
    ∃ b : GL (Fin 2) L, (b : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
      t₁⁻¹ * (b⁻¹ * γ * Matrix.GeneralLinearGroup.map (σ : L →+* L) b) ∈ Subgroup.center (GL (Fin 2) L) := by
  obtain ⟨b, hb, hbz⟩ := hγ
  obtain ⟨z₂, hz₂, e⟩ := (inv_mul_mem_center_iff' _ _).mp hbz
  have hc₂ : ∀ g : GL (Fin 2) L, g * z₂ = z₂ * g := Subgroup.mem_center_iff.mp hz₂
  refine ⟨b * A⁻¹, upper_mul hb (upper_inv hA), ?_⟩
  rw [inv_mul_mem_center_iff']
  refine ⟨z₁ * z₂, Subgroup.mul_mem _ hz₁ hz₂, ?_⟩
  have hγ' : γ = b * (t₂ * z₂) * (Matrix.GeneralLinearGroup.map (σ : L →+* L) b)⁻¹ := by rw [← e]; group
  calc (b * A⁻¹)⁻¹ * γ * Matrix.GeneralLinearGroup.map (σ : L →+* L) (b * A⁻¹)
      = A * (t₂ * z₂) * (Matrix.GeneralLinearGroup.map (σ : L →+* L) A)⁻¹ := by
        rw [hγ', map_mul, map_inv]; group
    _ = t₁ * z₁ * (Matrix.GeneralLinearGroup.map (σ : L →+* L) A * z₂) *
          (Matrix.GeneralLinearGroup.map (σ : L →+* L) A)⁻¹ := by rw [h]; group
    _ = t₁ * (z₁ * z₂) := by rw [hc₂]; group

theorem memI_of_memJ (σ : L ≃ₐ[K] L) {t₁ t₂ W : GL (Fin 2) L}
    (h : t₂ = W⁻¹ * t₁ * Matrix.GeneralLinearGroup.map (σ : L →+* L) W) {γ : GL (Fin 2) L}
    (hγ : ∃ b : GL (Fin 2) L, (b : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
      t₂⁻¹ * (b⁻¹ * γ * Matrix.GeneralLinearGroup.map (σ : L →+* L) b) ∈ Subgroup.center (GL (Fin 2) L)) :
    ∃ g : GL (Fin 2) L,
      t₁⁻¹ * (g⁻¹ * γ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g) ∈ Subgroup.center (GL (Fin 2) L) := by
  obtain ⟨b, -, hbz⟩ := hγ
  obtain ⟨z₂, hz₂, e⟩ := (inv_mul_mem_center_iff' _ _).mp hbz
  have hc₂ : ∀ g : GL (Fin 2) L, g * z₂ = z₂ * g := Subgroup.mem_center_iff.mp hz₂
  refine ⟨b * W⁻¹, ?_⟩
  rw [inv_mul_mem_center_iff']
  refine ⟨z₂, hz₂, ?_⟩
  have hγ' : γ = b * (t₂ * z₂) * (Matrix.GeneralLinearGroup.map (σ : L →+* L) b)⁻¹ := by rw [← e]; group
  calc (b * W⁻¹)⁻¹ * γ * Matrix.GeneralLinearGroup.map (σ : L →+* L) (b * W⁻¹)
      = W * (t₂ * z₂) * (Matrix.GeneralLinearGroup.map (σ : L →+* L) W)⁻¹ := by
        rw [hγ', map_mul, map_inv]; group
    _ = t₁ * (Matrix.GeneralLinearGroup.map (σ : L →+* L) W * z₂) *
          (Matrix.GeneralLinearGroup.map (σ : L →+* L) W)⁻¹ := by rw [h]; group
    _ = t₁ * z₂ := by rw [hc₂]; group

theorem upper_of_memJ (σ : L ≃ₐ[K] L) {t : GL (Fin 2) L} (ht : (t : Matrix (Fin 2) (Fin 2) L) 1 0 = 0)
    {γ : GL (Fin 2) L}
    (hγ : ∃ b : GL (Fin 2) L, (b : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
      t⁻¹ * (b⁻¹ * γ * Matrix.GeneralLinearGroup.map (σ : L →+* L) b) ∈ Subgroup.center (GL (Fin 2) L)) :
    (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 := by
  obtain ⟨b, hb, hbz⟩ := hγ
  obtain ⟨z, hz, e⟩ := (inv_mul_mem_center_iff' _ _).mp hbz
  obtain ⟨c, -, hc⟩ := exists_val_eq_smul_one_of_mem_center hz
  have hz10 : (z : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 := by rw [hc]; simp
  have hγ' : γ = b * (t * z) * (Matrix.GeneralLinearGroup.map (σ : L →+* L) b)⁻¹ := by rw [← e]; group
  rw [hγ']
  exact upper_mul (upper_mul hb (upper_mul ht hz10)) (upper_inv (upper_map σ hb))

theorem eq_weyl_conj (σ : L ≃ₐ[K] L) {t tw : GL (Fin 2) L}
    (h10 : (t : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) (h01 : (t : Matrix (Fin 2) (Fin 2) L) 0 1 = 0)
    (htw : (tw : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (tw : Matrix (Fin 2) (Fin 2) L) 0 1 = 0)
    (htw00 : (tw : Matrix (Fin 2) (Fin 2) L) 0 0 = (t : Matrix (Fin 2) (Fin 2) L) 1 1)
    (htw11 : (tw : Matrix (Fin 2) (Fin 2) L) 1 1 = (t : Matrix (Fin 2) (Fin 2) L) 0 0) :
    tw = (weylGL : GL (Fin 2) L)⁻¹ * t * Matrix.GeneralLinearGroup.map (σ : L →+* L) weylGL := by
  rw [map_weylGL, mul_assoc, eq_inv_mul_iff_mul_eq, Units.ext_iff, Units.val_mul, Units.val_mul, weylGL_val,
    ← Matrix.ext_iff]
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, h10, h01, htw.1, htw.2, htw00, htw11]

theorem exists_upper_diag_conj [FiniteDimensional K L] (σ : L ≃ₐ[K] L) (γ : GL (Fin 2) L)
    (hγ10 : (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0)
    (hN : Algebra.norm K ((γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 1) :
    ∃ N : GL (Fin 2) L, (N : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ ∃ t'' : GL (Fin 2) L,
      ((t'' : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (t'' : Matrix (Fin 2) (Fin 2) L) 0 1 = 0) ∧
      t'' = N⁻¹ * γ * Matrix.GeneralLinearGroup.map (σ : L →+* L) N := by
  set p := (γ : Matrix (Fin 2) (Fin 2) L) 0 0 with hp
  set q := (γ : Matrix (Fin 2) (Fin 2) L) 0 1 with hq
  set s := (γ : Matrix (Fin 2) (Fin 2) L) 1 1 with hs
  have hps : p * s ≠ 0 := by simpa [hγ10, ← hp, ← hq, ← hs] using det_ne γ
  have hp0 : p ≠ 0 := left_ne_zero_of_mul hps
  have hs0 : s ≠ 0 := right_ne_zero_of_mul hps

  let f : L →ₗ[K] L := p • (σ : L ≃ₐ[K] L).toLinearMap - s • LinearMap.id
  have hf : ∀ v, f v = p * σ v - s * v := by intro v; simp [f]
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    rw [hf, sub_eq_zero] at hv
    by_contra hv0
    apply hN
    have hNv : Algebra.norm K v ≠ 0 := Algebra.norm_ne_zero_iff.mpr hv0
    have h := congrArg (Algebra.norm K) hv
    rw [map_mul, map_mul, Algebra.norm_eq_of_algEquiv] at h
    have hps' : Algebra.norm K p = Algebra.norm K s := mul_right_cancel₀ hNv h
    have hNs : Algebra.norm K s ≠ 0 := Algebra.norm_ne_zero_iff.mpr hs0
    rw [show Algebra.norm K (p / s) = Algebra.norm K p / Algebra.norm K s from by
      rw [eq_div_iff hNs, ← map_mul, div_mul_cancel₀ p hs0], hps', div_self hNs]
  obtain ⟨x, hx⟩ := (LinearMap.injective_iff_surjective.mp hinj) q
  rw [hf] at hx
  refine ⟨(Matrix.GeneralLinearGroup.mkOfDetNeZero !![(1 : L), x; 0, 1] (by simp [Matrix.det_fin_two]))⁻¹,
    upper_inv (by simp [Matrix.GeneralLinearGroup.mkOfDetNeZero]),
    Matrix.GeneralLinearGroup.mkOfDetNeZero !![p, 0; 0, s] (by simp [Matrix.det_fin_two, hp0, hs0]),
    ⟨by simp [Matrix.GeneralLinearGroup.mkOfDetNeZero], by simp [Matrix.GeneralLinearGroup.mkOfDetNeZero]⟩, ?_⟩
  rw [inv_inv, map_inv, eq_mul_inv_iff_mul_eq, Units.ext_iff, Units.val_mul, Units.val_mul, ← Matrix.ext_iff]
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.mul_apply, Fin.sum_univ_two, coe_map_apply, hγ10,
      ← hp, ← hq, ← hs]
  · linear_combination hx

end LT.TwistedNorm.CuspClassesProof

namespace LT
p2m_export "LT" "mk TwistedNorm.SigmaConjClasses TwistedNorm.SigmaConjClasses.mk TwistedNorm.SigmaConjClasses.mk_eq_mk_iff_exists_eq_inv_mul_mul_map TwistedNorm.normClassMap TwistedNorm.exists_eq_inv_mul_mul_map_iff_norm_eq_of_diagonal TwistedNorm.exists_mem_hyperbolicCell_and_normClassMap_eq_iff_norm_div_ne_one TwistedNorm.exists_sigmaConj_diagonal_of_mem_hyperbolicCell_of_normClassMap_eq"
namespace TwistedNorm
p2m_export "LT.TwistedNorm" "SigmaConjClasses SigmaConjClasses.mk SigmaConjClasses.mk_eq_mk_iff_exists_eq_inv_mul_mul_map normClassMap exists_eq_inv_mul_mul_map_iff_norm_eq_of_diagonal exists_mem_hyperbolicCell_and_normClassMap_eq_iff_norm_div_ne_one exists_sigmaConj_diagonal_of_mem_hyperbolicCell_of_normClassMap_eq"
namespace CuspClassesProof
p2m_open "LT.TwistedNorm LT"

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

theorem memI_mono (σ : L ≃ₐ[K] L) {t₁ t₂ W z₁ z₂ : GL (Fin 2) L}
    (hz₁ : z₁ ∈ Subgroup.center (GL (Fin 2) L)) (hz₂ : z₂ ∈ Subgroup.center (GL (Fin 2) L))
    (h : t₂ * z₂ = W⁻¹ * (t₁ * z₁) * Matrix.GeneralLinearGroup.map (σ : L →+* L) W) {γ : GL (Fin 2) L}
    (hγ : ∃ g : GL (Fin 2) L,
      t₂⁻¹ * (g⁻¹ * γ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g) ∈ Subgroup.center (GL (Fin 2) L)) :
    ∃ g : GL (Fin 2) L,
      t₁⁻¹ * (g⁻¹ * γ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g) ∈ Subgroup.center (GL (Fin 2) L) := by
  obtain ⟨b, hbz⟩ := hγ
  obtain ⟨z₃, hz₃, e⟩ := (inv_mul_mem_center_iff' _ _).mp hbz
  have hc₂ : ∀ g : GL (Fin 2) L, g * z₂⁻¹ = z₂⁻¹ * g := Subgroup.mem_center_iff.mp (Subgroup.inv_mem _ hz₂)
  have hc₃ : ∀ g : GL (Fin 2) L, g * z₃ = z₃ * g := Subgroup.mem_center_iff.mp hz₃
  refine ⟨b * W⁻¹, ?_⟩
  rw [inv_mul_mem_center_iff']
  refine ⟨z₁ * z₂⁻¹ * z₃, Subgroup.mul_mem _ (Subgroup.mul_mem _ hz₁ (Subgroup.inv_mem _ hz₂)) hz₃, ?_⟩
  have hγ' : γ = b * (t₂ * z₃) * (Matrix.GeneralLinearGroup.map (σ : L →+* L) b)⁻¹ := by rw [← e]; group
  have ht₂ : t₂ = W⁻¹ * (t₁ * z₁) * Matrix.GeneralLinearGroup.map (σ : L →+* L) W * z₂⁻¹ := by rw [← h]; group
  calc (b * W⁻¹)⁻¹ * γ * Matrix.GeneralLinearGroup.map (σ : L →+* L) (b * W⁻¹)
      = W * (t₂ * z₃) * (Matrix.GeneralLinearGroup.map (σ : L →+* L) W)⁻¹ := by
        rw [hγ', map_mul, map_inv]; group
    _ = t₁ * z₁ * (Matrix.GeneralLinearGroup.map (σ : L →+* L) W * z₂⁻¹ * z₃) *
          (Matrix.GeneralLinearGroup.map (σ : L →+* L) W)⁻¹ := by rw [ht₂]; group
    _ = t₁ * z₁ * (z₂⁻¹ * (Matrix.GeneralLinearGroup.map (σ : L →+* L) W * z₃)) *
          (Matrix.GeneralLinearGroup.map (σ : L →+* L) W)⁻¹ := by rw [hc₂]; group
    _ = t₁ * (z₁ * z₂⁻¹ * z₃) := by rw [hc₃]; group

theorem self_memI (σ : L ≃ₐ[K] L) (t : GL (Fin 2) L) :
    ∃ g : GL (Fin 2) L,
      t⁻¹ * (g⁻¹ * t * Matrix.GeneralLinearGroup.map (σ : L →+* L) g) ∈ Subgroup.center (GL (Fin 2) L) :=
  ⟨1, by simp only [inv_one, one_mul, map_one, mul_one, inv_mul_cancel]; exact Subgroup.one_mem _⟩

end LT.TwistedNorm.CuspClassesProof

open LT.TwistedNorm.CuspClassesProof in
theorem solution
    {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    {σ : L ≃ₐ[K] L} (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) :
    (∀ t : GL (Fin 2) L, ((t : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (t : Matrix (Fin 2) (Fin 2) L) 0 1 = 0) → Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0 / (t : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 1 →
      {δ : GL (Fin 2) L | ∃ g : GL (Fin 2) L, t⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g) ∈ Subgroup.center (GL (Fin 2) L)} ⊆
        {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K, γ ∈ AutomorphicForm.hyperbolicCell K ∧
          LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ}) ∧
    (∀ δ : GL (Fin 2) L, δ ∈ {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K, γ ∈ AutomorphicForm.hyperbolicCell K ∧
          LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ} →
      ∃ t : GL (Fin 2) L, ((t : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (t : Matrix (Fin 2) (Fin 2) L) 0 1 = 0) ∧ Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0 / (t : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 1 ∧
        ∃ g : GL (Fin 2) L, t⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g) ∈ Subgroup.center (GL (Fin 2) L)) ∧
    (∀ t t' : GL (Fin 2) L, ((t : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (t : Matrix (Fin 2) (Fin 2) L) 0 1 = 0) → ((t' : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (t' : Matrix (Fin 2) (Fin 2) L) 0 1 = 0) →
      (({δ : GL (Fin 2) L | ∃ g : GL (Fin 2) L, t'⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g) ∈ Subgroup.center (GL (Fin 2) L)} ∩
          {δ : GL (Fin 2) L | ∃ g : GL (Fin 2) L, t⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g) ∈ Subgroup.center (GL (Fin 2) L)}).Nonempty ↔
        {δ : GL (Fin 2) L | ∃ g : GL (Fin 2) L, t'⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g) ∈ Subgroup.center (GL (Fin 2) L)} =
          {δ : GL (Fin 2) L | ∃ g : GL (Fin 2) L, t⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g) ∈ Subgroup.center (GL (Fin 2) L)}) ∧
      ({δ : GL (Fin 2) L | ∃ g : GL (Fin 2) L, t'⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g) ∈ Subgroup.center (GL (Fin 2) L)} =
          {δ : GL (Fin 2) L | ∃ g : GL (Fin 2) L, t⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g) ∈ Subgroup.center (GL (Fin 2) L)} ↔
        ∃ ζ : L, ζ ≠ 0 ∧
          ((Algebra.norm K ((t' : Matrix (Fin 2) (Fin 2) L) 0 0) = Algebra.norm K (ζ) * Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0) ∧
              Algebra.norm K ((t' : Matrix (Fin 2) (Fin 2) L) 1 1) = Algebra.norm K (ζ) * Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 1 1)) ∨
            (Algebra.norm K ((t' : Matrix (Fin 2) (Fin 2) L) 0 0) = Algebra.norm K (ζ) * Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 1 1) ∧
              Algebra.norm K ((t' : Matrix (Fin 2) (Fin 2) L) 1 1) = Algebra.norm K (ζ) * Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0))))) := by
  have scaled : ∀ {z : GL (Fin 2) L}, z ∈ Subgroup.center (GL (Fin 2) L) →
      ∃ c : L, c ≠ 0 ∧ ∀ (s : GL (Fin 2) L) (i j : Fin 2),
        ((s * z : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) i j = c * (s : Matrix (Fin 2) (Fin 2) L) i j := by
    intro z hz
    obtain ⟨c, hc0, hc⟩ := exists_val_eq_smul_one_of_mem_center hz
    exact ⟨c, hc0, fun s i j => by rw [Units.val_mul, hc, Matrix.mul_smul, mul_one, Matrix.smul_apply, smul_eq_mul]⟩

  have diag_tz : ∀ {t z : GL (Fin 2) L}, (t : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (t : Matrix (Fin 2) (Fin 2) L) 0 1 = 0 →
      z ∈ Subgroup.center (GL (Fin 2) L) →
      (((t * z : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
        ((t * z : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 0 1 = 0) ∧
      ((t * z : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 0 0 / ((t * z : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 1 =
        (t : Matrix (Fin 2) (Fin 2) L) 0 0 / (t : Matrix (Fin 2) (Fin 2) L) 1 1 := by
    intro t z ht hz
    obtain ⟨c, hc0, hcz⟩ := scaled hz
    rw [hcz, hcz, hcz, hcz, ht.1, ht.2, mul_zero, mul_div_mul_left _ _ hc0]
    exact ⟨⟨rfl, rfl⟩, rfl⟩

  have part1 : ∀ t : GL (Fin 2) L, ((t : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (t : Matrix (Fin 2) (Fin 2) L) 0 1 = 0) →
      Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0 / (t : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 1 →
      ∀ δ : GL (Fin 2) L, (∃ g : GL (Fin 2) L,
        t⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g) ∈ Subgroup.center (GL (Fin 2) L)) →
      ∃ γ : GL (Fin 2) K, γ ∈ AutomorphicForm.hyperbolicCell K ∧
        LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ := by
    intro t ht hN δ ⟨g, hg⟩
    obtain ⟨z, hz, hgz⟩ := (inv_mul_mem_center_iff' _ _).mp hg
    obtain ⟨htz, hratio⟩ := diag_tz ht hz
    obtain ⟨γK, hγK, hm⟩ := (LT.TwistedNorm.exists_mem_hyperbolicCell_and_normClassMap_eq_iff_norm_div_ne_one
      hgen (t * z) htz.1).mpr (by rw [hratio]; exact hN)
    have hmk : LT.TwistedNorm.SigmaConjClasses.mk σ δ = LT.TwistedNorm.SigmaConjClasses.mk σ (t * z) :=
      LT.TwistedNorm.SigmaConjClasses.mk_eq_mk_iff_exists_eq_inv_mul_mul_map.mpr ⟨g, hgz.symm⟩
    exact ⟨γK, hγK, by rw [hmk, hm]⟩
  refine ⟨fun t ht hN δ hδ => part1 t ht hN δ hδ, ?_, ?_⟩
  ·
    rintro δ ⟨γK, hγK, hm⟩
    obtain ⟨g, hg⟩ := LT.TwistedNorm.exists_sigmaConj_diagonal_of_mem_hyperbolicCell_of_normClassMap_eq hgen γK hγK δ hm
    set t : GL (Fin 2) L := g⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g with ht
    have hmk : LT.TwistedNorm.SigmaConjClasses.mk σ δ = LT.TwistedNorm.SigmaConjClasses.mk σ t :=
      LT.TwistedNorm.SigmaConjClasses.mk_eq_mk_iff_exists_eq_inv_mul_mul_map.mpr ⟨g, rfl⟩
    refine ⟨t, hg, ?_, g, ?_⟩
    · exact (LT.TwistedNorm.exists_mem_hyperbolicCell_and_normClassMap_eq_iff_norm_div_ne_one hgen t hg.1).mp
        ⟨γK, hγK, by rw [← hmk, hm]⟩
    · rw [← ht, inv_mul_cancel]; exact Subgroup.one_mem _
  ·
    intro t t' ht ht'

    have key : ∀ δ : GL (Fin 2) L,
        (∃ g : GL (Fin 2) L, t'⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g) ∈
          Subgroup.center (GL (Fin 2) L)) →
        (∃ g : GL (Fin 2) L, t⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g) ∈
          Subgroup.center (GL (Fin 2) L)) →
        {δ : GL (Fin 2) L | ∃ g : GL (Fin 2) L, t'⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g) ∈
            Subgroup.center (GL (Fin 2) L)} =
          {δ : GL (Fin 2) L | ∃ g : GL (Fin 2) L, t⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g) ∈
            Subgroup.center (GL (Fin 2) L)} := by
      rintro δ ⟨g', hg'⟩ ⟨g, hg⟩
      obtain ⟨z', hz', e'⟩ := (inv_mul_mem_center_iff' _ _).mp hg'
      obtain ⟨z, hz, e⟩ := (inv_mul_mem_center_iff' _ _).mp hg
      have hδ : δ = g * (t * z) * (Matrix.GeneralLinearGroup.map (σ : L →+* L) g)⁻¹ := by rw [← e]; group
      have hrel : t' * z' = (g⁻¹ * g')⁻¹ * (t * z) * Matrix.GeneralLinearGroup.map (σ : L →+* L) (g⁻¹ * g') := by
        rw [← e', hδ, map_mul, map_inv]; group
      have hrel' : t * z = (g'⁻¹ * g)⁻¹ * (t' * z') * Matrix.GeneralLinearGroup.map (σ : L →+* L) (g'⁻¹ * g) := by
        rw [hrel, map_mul, map_mul, map_inv, map_inv]; group
      ext γ
      exact ⟨fun h => memI_mono σ hz hz' hrel h, fun h => memI_mono σ hz' hz hrel' h⟩
    have meet_iff : ({δ : GL (Fin 2) L | ∃ g : GL (Fin 2) L, t'⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g) ∈
            Subgroup.center (GL (Fin 2) L)} ∩
          {δ : GL (Fin 2) L | ∃ g : GL (Fin 2) L, t⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g) ∈
            Subgroup.center (GL (Fin 2) L)}).Nonempty ↔
        {δ : GL (Fin 2) L | ∃ g : GL (Fin 2) L, t'⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g) ∈
            Subgroup.center (GL (Fin 2) L)} =
          {δ : GL (Fin 2) L | ∃ g : GL (Fin 2) L, t⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g) ∈
            Subgroup.center (GL (Fin 2) L)} := by
      constructor
      · rintro ⟨δ, h', h⟩; exact key δ h' h
      · intro h; exact ⟨t, by rw [h]; exact self_memI σ t, self_memI σ t⟩
    refine ⟨meet_iff, ?_⟩

    constructor
    · intro h
      have ht'mem : t' ∈ {δ : GL (Fin 2) L | ∃ g : GL (Fin 2) L,
          t⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g) ∈ Subgroup.center (GL (Fin 2) L)} :=
        h ▸ self_memI σ t'
      obtain ⟨g, hg⟩ := ht'mem
      obtain ⟨z, hz, e⟩ := (inv_mul_mem_center_iff' _ _).mp hg
      obtain ⟨c, hc0, hcz⟩ := scaled hz
      obtain ⟨htz, -⟩ := diag_tz ht hz
      have hrel : ∃ g₁ : GL (Fin 2) L, t' = g₁⁻¹ * (t * z) * Matrix.GeneralLinearGroup.map (σ : L →+* L) g₁ :=
        ⟨g⁻¹, by rw [← e, map_inv]; group⟩
      have E := (LT.TwistedNorm.exists_eq_inv_mul_mul_map_iff_norm_eq_of_diagonal hgen (t * z) t' htz ht').2.2.mp hrel
      refine ⟨c, hc0, ?_⟩
      rw [hcz, hcz, map_mul, map_mul] at E
      exact E
    · rintro ⟨ζ, hζ, hnorms⟩
      have hzc : scalarGL ζ hζ ∈ Subgroup.center (GL (Fin 2) L) := scalarGL_mem_center _ _
      obtain ⟨c, hc0, hcz⟩ := scaled hzc
      have hcval : c = ζ := by
        have h := hcz 1 0 0
        simp only [Units.val_one, one_mul, scalarGL_val, Matrix.smul_apply, Matrix.one_apply_eq,
          smul_eq_mul, mul_one] at h
        exact h.symm
      obtain ⟨htz, -⟩ := diag_tz (z := scalarGL ζ hζ) ht hzc
      obtain ⟨g₁, hg₁⟩ := (LT.TwistedNorm.exists_eq_inv_mul_mul_map_iff_norm_eq_of_diagonal hgen
        (t * scalarGL ζ hζ) t' htz ht').2.2.mpr (by rw [hcz, hcz, map_mul, map_mul, hcval]; exact hnorms)
      apply key t' (self_memI σ t')
      refine ⟨g₁⁻¹, ?_⟩
      rw [inv_mul_mem_center_iff']
      exact ⟨scalarGL ζ hζ, hzc, by rw [hg₁, map_inv]; group⟩

end S_LT_TwistedNorm_setOf_exists_mem_center_subset_and_exists_and_eq_iff_of_diagonal
end P2MW
export P2MW.S_LT_TwistedNorm_setOf_exists_mem_center_subset_and_exists_and_eq_iff_of_diagonal (solution)
