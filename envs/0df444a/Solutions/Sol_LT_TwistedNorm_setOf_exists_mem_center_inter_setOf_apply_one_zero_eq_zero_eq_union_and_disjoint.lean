-- Prove2me | solution 1 for LT.TwistedNorm.setOf_exists_mem_center_inter_setOf_apply_one_zero_eq_zero_eq_union_and_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/935b14dc-c3ed-5294-860b-1692d86b7828

import Definitions.Def_TwistedNormClasses
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Theorems.Thm_LT_TwistedNorm_exists_eq_inv_mul_mul_map_iff_norm_eq_of_diagonal
import Theorems.Thm_LT_TwistedNorm_exists_mem_hyperbolicCell_and_normClassMap_eq_iff_norm_div_ne_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LT_TwistedNorm_setOf_exists_mem_center_inter_setOf_apply_one_zero_eq_zero_eq_union_and_disjoint

set_option autoImplicit false

namespace LT
p2m_export "LT" "mk TwistedNorm.SigmaConjClasses TwistedNorm.SigmaConjClasses.mk TwistedNorm.SigmaConjClasses.mk_eq_mk_iff_exists_eq_inv_mul_mul_map TwistedNorm.exists_eq_inv_mul_mul_map_iff_norm_eq_of_diagonal TwistedNorm.exists_mem_hyperbolicCell_and_normClassMap_eq_iff_norm_div_ne_one"
namespace TwistedNorm
p2m_export "LT.TwistedNorm" "SigmaConjClasses SigmaConjClasses.mk SigmaConjClasses.mk_eq_mk_iff_exists_eq_inv_mul_mul_map exists_eq_inv_mul_mul_map_iff_norm_eq_of_diagonal exists_mem_hyperbolicCell_and_normClassMap_eq_iff_norm_div_ne_one"
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
p2m_export "LT" "mk TwistedNorm.SigmaConjClasses TwistedNorm.SigmaConjClasses.mk TwistedNorm.SigmaConjClasses.mk_eq_mk_iff_exists_eq_inv_mul_mul_map TwistedNorm.exists_eq_inv_mul_mul_map_iff_norm_eq_of_diagonal TwistedNorm.exists_mem_hyperbolicCell_and_normClassMap_eq_iff_norm_div_ne_one"
namespace TwistedNorm
p2m_export "LT.TwistedNorm" "SigmaConjClasses SigmaConjClasses.mk SigmaConjClasses.mk_eq_mk_iff_exists_eq_inv_mul_mul_map exists_eq_inv_mul_mul_map_iff_norm_eq_of_diagonal exists_mem_hyperbolicCell_and_normClassMap_eq_iff_norm_div_ne_one"
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

open LT.TwistedNorm.CuspClassesProof in
theorem solution
    {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    {σ : L ≃ₐ[K] L} (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) (t tw : GL (Fin 2) L)
    (h10 : (t : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) (h01 : (t : Matrix (Fin 2) (Fin 2) L) 0 1 = 0) (hN : Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0 / (t : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 1)
    (htw : (tw : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (tw : Matrix (Fin 2) (Fin 2) L) 0 1 = 0) (htw00 : (tw : Matrix (Fin 2) (Fin 2) L) 0 0 = (t : Matrix (Fin 2) (Fin 2) L) 1 1) (htw11 : (tw : Matrix (Fin 2) (Fin 2) L) 1 1 = (t : Matrix (Fin 2) (Fin 2) L) 0 0) :
    ({γ : GL (Fin 2) L | (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ ∃ g : GL (Fin 2) L, t⁻¹ * (g⁻¹ * γ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g) ∈ Subgroup.center (GL (Fin 2) L)} =
      {γ : GL (Fin 2) L | ∃ b : GL (Fin 2) L, (b : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ t⁻¹ * (b⁻¹ * γ * Matrix.GeneralLinearGroup.map (σ : L →+* L) b) ∈ Subgroup.center (GL (Fin 2) L)} ∪
        {γ : GL (Fin 2) L | ∃ b : GL (Fin 2) L, (b : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ tw⁻¹ * (b⁻¹ * γ * Matrix.GeneralLinearGroup.map (σ : L →+* L) b) ∈ Subgroup.center (GL (Fin 2) L)}) ∧
    (Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0 / (t : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ -1 →
      Disjoint {γ : GL (Fin 2) L | ∃ b : GL (Fin 2) L, (b : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ t⁻¹ * (b⁻¹ * γ * Matrix.GeneralLinearGroup.map (σ : L →+* L) b) ∈ Subgroup.center (GL (Fin 2) L)}
        {γ : GL (Fin 2) L | ∃ b : GL (Fin 2) L, (b : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ tw⁻¹ * (b⁻¹ * γ * Matrix.GeneralLinearGroup.map (σ : L →+* L) b) ∈ Subgroup.center (GL (Fin 2) L)}) ∧
    (Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0 / (t : Matrix (Fin 2) (Fin 2) L) 1 1) = -1 →
      {γ : GL (Fin 2) L | ∃ b : GL (Fin 2) L, (b : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ t⁻¹ * (b⁻¹ * γ * Matrix.GeneralLinearGroup.map (σ : L →+* L) b) ∈ Subgroup.center (GL (Fin 2) L)} =
        {γ : GL (Fin 2) L | ∃ b : GL (Fin 2) L, (b : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ tw⁻¹ * (b⁻¹ * γ * Matrix.GeneralLinearGroup.map (σ : L →+* L) b) ∈ Subgroup.center (GL (Fin 2) L)}) := by
  have had : (t : Matrix (Fin 2) (Fin 2) L) 0 0 * (t : Matrix (Fin 2) (Fin 2) L) 1 1 ≠ 0 := by simpa [h10, h01] using det_ne t
  have ha0 : (t : Matrix (Fin 2) (Fin 2) L) 0 0 ≠ 0 := left_ne_zero_of_mul had
  have hd0 : (t : Matrix (Fin 2) (Fin 2) L) 1 1 ≠ 0 := right_ne_zero_of_mul had
  have hNa0 : Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0) ≠ 0 := Algebra.norm_ne_zero_iff.mpr ha0
  have hNd0 : Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 0 := Algebra.norm_ne_zero_iff.mpr hd0
  have hNdiv : Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0 / (t : Matrix (Fin 2) (Fin 2) L) 1 1) = Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0) / Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 1 1) := by
    rw [eq_div_iff hNd0, ← map_mul, div_mul_cancel₀ _ hd0]

  have scaled : ∀ {z : GL (Fin 2) L}, z ∈ Subgroup.center (GL (Fin 2) L) →
      ∃ c : L, c ≠ 0 ∧ ∀ (s : GL (Fin 2) L) (i j : Fin 2),
        ((s * z : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) i j = c * (s : Matrix (Fin 2) (Fin 2) L) i j := by
    intro z hz
    obtain ⟨c, hc0, hc⟩ := exists_val_eq_smul_one_of_mem_center hz
    exact ⟨c, hc0, fun s i j => by rw [Units.val_mul, hc, Matrix.mul_smul, mul_one, Matrix.smul_apply, smul_eq_mul]⟩
  refine ⟨?_, ?_, ?_⟩
  ·
    ext γ
    simp only [Set.mem_setOf_eq, Set.mem_union]
    constructor
    · rintro ⟨hγ10, g, hg⟩
      obtain ⟨z, hz, hgz⟩ := (inv_mul_mem_center_iff' _ _).mp hg
      obtain ⟨c, hc0, hcz⟩ := scaled hz
      have htz : ((t * z : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
          ((t * z : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 0 1 = 0 := by
        rw [hcz, hcz, h10, h01, mul_zero]; exact ⟨rfl, rfl⟩
      have hreg_tz : Algebra.norm K (((t * z : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 0 0 /
          ((t * z : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 1 := by
        rw [hcz, hcz, mul_div_mul_left _ _ hc0]; exact hN

      obtain ⟨γK, hγK, hm⟩ := (LT.TwistedNorm.exists_mem_hyperbolicCell_and_normClassMap_eq_iff_norm_div_ne_one
        hgen (t * z) htz.1).mpr hreg_tz
      have hmk : LT.TwistedNorm.SigmaConjClasses.mk σ γ = LT.TwistedNorm.SigmaConjClasses.mk σ (t * z) :=
        LT.TwistedNorm.SigmaConjClasses.mk_eq_mk_iff_exists_eq_inv_mul_mul_map.mpr ⟨g, hgz.symm⟩
      have hregγ : Algebra.norm K ((γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 1 :=
        (LT.TwistedNorm.exists_mem_hyperbolicCell_and_normClassMap_eq_iff_norm_div_ne_one hgen γ hγ10).mp
          ⟨γK, hγK, by rw [hmk, hm]⟩

      obtain ⟨N, hN10, t'', ht'', hconj⟩ := exists_upper_diag_conj σ γ hγ10 hregγ
      have hγN : γ = N * t'' * (Matrix.GeneralLinearGroup.map (σ : L →+* L) N)⁻¹ := by rw [hconj]; group
      have hrel : ∃ h : GL (Fin 2) L, t'' = h⁻¹ * (t * z) * Matrix.GeneralLinearGroup.map (σ : L →+* L) h := by
        refine ⟨g⁻¹ * N, ?_⟩
        rw [← hgz, hconj, map_mul, map_inv]; group
      have E := LT.TwistedNorm.exists_eq_inv_mul_mul_map_iff_norm_eq_of_diagonal hgen (t * z) t'' htz ht''
      rcases E.2.2.mp hrel with hord | hswap
      ·
        left
        obtain ⟨A, hA, hA'⟩ := E.2.1.mpr hord
        refine ⟨N * A⁻¹, upper_mul hN10 (upper_inv hA.1), ?_⟩
        rw [inv_mul_mem_center_iff']
        refine ⟨z, hz, ?_⟩
        rw [hγN, hA', map_mul, map_inv]; group
      ·
        right
        have htwz : ((tw * z : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
            ((tw * z : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 0 1 = 0 := by
          rw [hcz, hcz, htw.1, htw.2, mul_zero]; exact ⟨rfl, rfl⟩
        have E2 := LT.TwistedNorm.exists_eq_inv_mul_mul_map_iff_norm_eq_of_diagonal hgen (tw * z) t'' htwz ht''
        obtain ⟨A, hA, hA'⟩ := E2.2.1.mpr (by
          rw [hcz, hcz, htw00, htw11]
          rw [hcz, hcz] at hswap
          exact hswap)
        refine ⟨N * A⁻¹, upper_mul hN10 (upper_inv hA.1), ?_⟩
        rw [inv_mul_mem_center_iff']
        refine ⟨z, hz, ?_⟩
        rw [hγN, hA', map_mul, map_inv]; group
    · rintro (hJ | hJ)
      · exact ⟨upper_of_memJ σ h10 hJ, by obtain ⟨b, -, hb⟩ := hJ; exact ⟨b, hb⟩⟩
      · exact ⟨upper_of_memJ σ htw.1 hJ, memI_of_memJ σ (eq_weyl_conj σ h10 h01 htw htw00 htw11) hJ⟩
  ·
    intro hN1
    rw [Set.disjoint_left]
    rintro γ ⟨b, hb, hbz⟩ ⟨b', hb', hbz'⟩
    obtain ⟨z, hz, e⟩ := (inv_mul_mem_center_iff' _ _).mp hbz
    obtain ⟨z', hz', e'⟩ := (inv_mul_mem_center_iff' _ _).mp hbz'
    obtain ⟨c, hc0, hcz⟩ := scaled hz
    obtain ⟨c', hc'0, hcz'⟩ := scaled hz'
    have htz : ((t * z : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
        ((t * z : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 0 1 = 0 := by
      rw [hcz, hcz, h10, h01, mul_zero]; exact ⟨rfl, rfl⟩
    have htwz : ((tw * z' : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
        ((tw * z' : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 0 1 = 0 := by
      rw [hcz', hcz', htw.1, htw.2, mul_zero]; exact ⟨rfl, rfl⟩
    have hγ' : γ = b * (t * z) * (Matrix.GeneralLinearGroup.map (σ : L →+* L) b)⁻¹ := by rw [← e]; group
    have hrel : ∃ B : GL (Fin 2) L, (B : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
        tw * z' = B⁻¹ * (t * z) * Matrix.GeneralLinearGroup.map (σ : L →+* L) B := by
      refine ⟨b⁻¹ * b', upper_mul (upper_inv hb) hb', ?_⟩
      rw [← e', hγ', map_mul, map_inv]; group
    have E := (LT.TwistedNorm.exists_eq_inv_mul_mul_map_iff_norm_eq_of_diagonal hgen (t * z) (tw * z') htz htwz).1.mp
      hrel
    rw [hcz', hcz', hcz, hcz, htw00, htw11, map_mul, map_mul, map_mul, map_mul] at E
    obtain ⟨E1, E2⟩ := E

    have hNc0 : Algebra.norm K c ≠ 0 := Algebra.norm_ne_zero_iff.mpr hc0
    have hNc'0 : Algebra.norm K c' ≠ 0 := Algebra.norm_ne_zero_iff.mpr hc'0
    have hsq' : Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0) * Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0) = Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 1 1) * Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 1 1) := by
      have h := congrArg₂ (· * ·) E1 E2.symm
      have h' : Algebra.norm K c * Algebra.norm K c' * (Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 1 1) * Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 1 1)) =
          Algebra.norm K c * Algebra.norm K c' * (Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0) * Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0)) := by
        linear_combination h
      exact (mul_left_cancel₀ (mul_ne_zero hNc0 hNc'0) h').symm
    have hsq : (Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0 / (t : Matrix (Fin 2) (Fin 2) L) 1 1)) * (Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0 / (t : Matrix (Fin 2) (Fin 2) L) 1 1)) = 1 := by
      rw [hNdiv, div_mul_div_comm, hsq', div_self (mul_ne_zero hNd0 hNd0)]
    rcases mul_self_eq_one_iff.mp hsq with h1 | h1
    · exact hN h1
    · exact hN1 h1
  ·
    intro hN1
    have hc₁ : (t : Matrix (Fin 2) (Fin 2) L) 1 1 / (t : Matrix (Fin 2) (Fin 2) L) 0 0 ≠ 0 := div_ne_zero hd0 ha0
    have hz₁c : scalarGL ((t : Matrix (Fin 2) (Fin 2) L) 1 1 / (t : Matrix (Fin 2) (Fin 2) L) 0 0) hc₁ ∈ Subgroup.center (GL (Fin 2) L) := scalarGL_mem_center _ _
    obtain ⟨c, hc0, hcz⟩ := scaled hz₁c

    have hcval : c = (t : Matrix (Fin 2) (Fin 2) L) 1 1 / (t : Matrix (Fin 2) (Fin 2) L) 0 0 := by
      have h := hcz 1 0 0
      simp only [Units.val_mul, Units.val_one, one_mul, scalarGL_val, Matrix.smul_apply, Matrix.one_apply_eq,
        smul_eq_mul, mul_one] at h
      exact h.symm
    have htz₁d : ((t * scalarGL ((t : Matrix (Fin 2) (Fin 2) L) 1 1 / (t : Matrix (Fin 2) (Fin 2) L) 0 0) hc₁ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
        ((t * scalarGL ((t : Matrix (Fin 2) (Fin 2) L) 1 1 / (t : Matrix (Fin 2) (Fin 2) L) 0 0) hc₁ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 0 1 = 0 := by
      rw [hcz, hcz, h10, h01, mul_zero]; exact ⟨rfl, rfl⟩
    have E := LT.TwistedNorm.exists_eq_inv_mul_mul_map_iff_norm_eq_of_diagonal hgen
      (t * scalarGL ((t : Matrix (Fin 2) (Fin 2) L) 1 1 / (t : Matrix (Fin 2) (Fin 2) L) 0 0) hc₁) tw htz₁d htw
    obtain ⟨A, hA, hA'⟩ := E.2.1.mpr (by
      rw [hcz, hcz, htw00, htw11, hcval, div_mul_cancel₀ _ ha0]
      refine ⟨rfl, ?_⟩
      have Ndiv' : Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 1 1 / (t : Matrix (Fin 2) (Fin 2) L) 0 0) = Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 1 1) / Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0) := by
        rw [eq_div_iff hNa0, ← map_mul, div_mul_cancel₀ _ ha0]
      have h : Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0) = - Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 1 1) := by
        rw [hNdiv, div_eq_iff hNd0] at hN1; linear_combination hN1
      rw [map_mul, Ndiv', div_mul_eq_mul_div, eq_div_iff hNa0, h]
      ring)
    have hA'' : t = (A⁻¹)⁻¹ * (tw * (scalarGL ((t : Matrix (Fin 2) (Fin 2) L) 1 1 / (t : Matrix (Fin 2) (Fin 2) L) 0 0) hc₁)⁻¹) *
        Matrix.GeneralLinearGroup.map (σ : L →+* L) A⁻¹ := by
      have hcomm : ∀ g : GL (Fin 2) L, g * (scalarGL ((t : Matrix (Fin 2) (Fin 2) L) 1 1 / (t : Matrix (Fin 2) (Fin 2) L) 0 0) hc₁)⁻¹ = (scalarGL ((t : Matrix (Fin 2) (Fin 2) L) 1 1 / (t : Matrix (Fin 2) (Fin 2) L) 0 0) hc₁)⁻¹ * g :=
        Subgroup.mem_center_iff.mp (Subgroup.inv_mem _ hz₁c)
      rw [inv_inv, map_inv, hA']
      calc t = t * scalarGL ((t : Matrix (Fin 2) (Fin 2) L) 1 1 / (t : Matrix (Fin 2) (Fin 2) L) 0 0) hc₁ * Matrix.GeneralLinearGroup.map (σ : L →+* L) A *
            ((Matrix.GeneralLinearGroup.map (σ : L →+* L) A)⁻¹ * (scalarGL ((t : Matrix (Fin 2) (Fin 2) L) 1 1 / (t : Matrix (Fin 2) (Fin 2) L) 0 0) hc₁)⁻¹) := by group
        _ = t * scalarGL ((t : Matrix (Fin 2) (Fin 2) L) 1 1 / (t : Matrix (Fin 2) (Fin 2) L) 0 0) hc₁ * Matrix.GeneralLinearGroup.map (σ : L →+* L) A *
            ((scalarGL ((t : Matrix (Fin 2) (Fin 2) L) 1 1 / (t : Matrix (Fin 2) (Fin 2) L) 0 0) hc₁)⁻¹ * (Matrix.GeneralLinearGroup.map (σ : L →+* L) A)⁻¹) := by rw [hcomm]
        _ = A * (A⁻¹ * (t * scalarGL ((t : Matrix (Fin 2) (Fin 2) L) 1 1 / (t : Matrix (Fin 2) (Fin 2) L) 0 0) hc₁) * Matrix.GeneralLinearGroup.map (σ : L →+* L) A *
            (scalarGL ((t : Matrix (Fin 2) (Fin 2) L) 1 1 / (t : Matrix (Fin 2) (Fin 2) L) 0 0) hc₁)⁻¹) * (Matrix.GeneralLinearGroup.map (σ : L →+* L) A)⁻¹ := by group
    ext γ
    exact ⟨fun hJ => memJ_mono σ (upper_inv hA.1) (Subgroup.inv_mem _ hz₁c) hA'' hJ,
      fun hJ => memJ_mono σ hA.1 hz₁c hA' hJ⟩

end S_LT_TwistedNorm_setOf_exists_mem_center_inter_setOf_apply_one_zero_eq_zero_eq_union_and_disjoint
end P2MW
export P2MW.S_LT_TwistedNorm_setOf_exists_mem_center_inter_setOf_apply_one_zero_eq_zero_eq_union_and_disjoint (solution)
