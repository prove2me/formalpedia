-- Prove2me | solution 1 for GlobalTheory.HermLineZeros.finite_zeros_on_line
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:29:12.70228+00:00
-- url     : https://prove2.me/submissions/b10bc864-580a-4913-b6d4-33f8fadbea08

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_HermitianFormFiniteZerosOnLineCmExt
import Theorems.Thm_GlobalTheory_HermLineZeros_hform_expand
import Theorems.Thm_GlobalTheory_HermLineZeros_exists_anisotropic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory GlobalTheory.HermLineZeros
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E}
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E}
namespace GlobalTheory.HermLineZeros
namespace _root_.GlobalTheory.HermLineZeros
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ → ∀ (M : ℕ), 1 ≤ M → ∀ (J : Matrix (Fin M) (Fin M) E), _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsHermND σ J → ∀ (K : Type) [Field K] [Algebra F K], ∃ y : Fin M → K ⊗[F] E, ∀ x : Fin M → K ⊗[F] E, {t : K | _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR K σ J (x + t • y) = 0}.Finite := by
  intro F E _ _ _ _ _ σ h M hM J hJ K _ _
  obtain ⟨y₀, a, ha, hy⟩ := _root_.GlobalTheory.HermLineZeros.exists_anisotropic h hM hJ
  let φ : E →ₐ[F] K ⊗[F] E := Algebra.TensorProduct.includeRight
  let S := _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR K σ
  let JR := _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (F := F) K J
  set y : Fin M → K ⊗[F] E := fun i => φ (y₀ i)
  refine ⟨y, fun x => ?_⟩
  have hSc : ∀ t : K, S (algebraMap K (K ⊗[F] E) t) = algebraMap K (K ⊗[F] E) t := fun t => by
    simp [S, _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, Algebra.TensorProduct.algebraMap_apply]
  have hSφ : ∀ e : E, S (φ e) = φ (σ e) := fun e => by simp [S, φ, _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR]
  have hyy : _root_.Formalism.UG.hform S JR y y = algebraMap K (K ⊗[F] E) (algebraMap F K a) := by
    rw [← IsScalarTower.algebraMap_apply, ← φ.commutes, ← hy]
    simp only [_root_.Formalism.UG.hform, _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hE, map_sum, map_mul, y, hSφ, JR, _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR, Matrix.map_apply, _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR]
    rfl
  have htr : Algebra.trace K (K ⊗[F] E) (_root_.Formalism.UG.hform S JR y y)
      = Module.finrank K (K ⊗[F] E) • algebraMap F K a := by
    rw [hyy, Algebra.trace_algebraMap]
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap F K).injective
  have hfr : Module.finrank K (K ⊗[F] E) ≠ 0 := by
    rw [Module.finrank_baseChange, h.2.2.1]; norm_num
  set α := algebraMap F K (1 / 2) * Algebra.trace K (K ⊗[F] E) (_root_.Formalism.UG.hform S JR y y) with hα
  set β := algebraMap F K (1 / 2) * Algebra.trace K (K ⊗[F] E) (_root_.Formalism.UG.hform S JR x y + _root_.Formalism.UG.hform S JR y x)
  set γ := algebraMap F K (1 / 2) * Algebra.trace K (K ⊗[F] E) (_root_.Formalism.UG.hform S JR x x)
  have hα0 : α ≠ 0 := by
    rw [hα, htr]
    refine mul_ne_zero ?_ (smul_ne_zero hfr ?_)
    · rw [Ne, map_eq_zero_iff _ (algebraMap F K).injective]; norm_num
    · rw [Ne, map_eq_zero_iff _ (algebraMap F K).injective]; exact ha
  let p : Polynomial K := Polynomial.C α * Polynomial.X ^ 2 + Polynomial.C β * Polynomial.X + Polynomial.C γ
  have hp : p ≠ 0 := by
    intro hp
    have := congrArg (Polynomial.coeff · 2) hp
    simp [p, Polynomial.coeff_X, Polynomial.coeff_C] at this
    exact hα0 this
  refine (Polynomial.finite_setOf_isRoot hp).subset fun t ht => ?_
  simp only [Set.mem_setOf_eq] at ht ⊢
  rw [Polynomial.IsRoot.def, ← ht]
  have hsmul : t • y = algebraMap K (K ⊗[F] E) t • y := by
    funext i; simp [Algebra.smul_def]
  have hexp := _root_.GlobalTheory.HermLineZeros.hform_expand S JR x y (algebraMap K (K ⊗[F] E) t)
  rw [hSc] at hexp
  have hq : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR K σ J (x + t • y) = algebraMap F K (1 / 2) *
      Algebra.trace K (K ⊗[F] E) (_root_.Formalism.UG.hform S JR (x + algebraMap K (K ⊗[F] E) t • y)
        (x + algebraMap K (K ⊗[F] E) t • y)) := by
    rw [← hsmul]; rfl
  have htc : ∀ z, Algebra.trace K (K ⊗[F] E) (algebraMap K (K ⊗[F] E) t * z)
      = t * Algebra.trace K (K ⊗[F] E) z := fun z => by
    rw [← Algebra.smul_def, map_smul, smul_eq_mul]
  rw [hq, hexp, mul_assoc (algebraMap K (K ⊗[F] E) t), map_add, map_add, map_add, htc, htc, htc, htc]
  simp only [p, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_X, α, β, γ, map_add]
  ring
end _root_.GlobalTheory.HermLineZeros
end GlobalTheory.HermLineZeros
