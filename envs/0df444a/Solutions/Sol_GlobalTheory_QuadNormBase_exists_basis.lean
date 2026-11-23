-- Prove2me | solution 1 for GlobalTheory.QuadNormBase.exists_basis
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:46:38.468598+00:00
-- url     : https://prove2.me/submissions/97854789-1169-4250-8b7b-a78fdbbfb8e2

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_QuadraticExtNormFormOverAlgebra

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct
open GlobalTheory GlobalTheory.QuadNormBase
namespace GlobalTheory.QuadNormBase
theorem _root_.solution (F E : Type) [Field F] [CharZero F] [Field E] [Algebra F E] (σ : E →ₐ[F] E)
    (hr : Module.finrank F E = 2) (hσ : ∀ x, σ (σ x) = x) (hne : ∃ x, σ x ≠ x) :
    ∃ (δ : F) (b : Module.Basis (Fin 2) F E), ¬ IsSquare δ ∧ b 0 = 1 ∧ σ (b 1) = - b 1 ∧
      b 1 * b 1 = algebraMap F E δ := by
  haveI : CharZero E := charZero_of_injective_algebraMap (algebraMap F E).injective
  obtain ⟨x0, hx0⟩ := hne
  have hsm : ∀ (c : F) (e : E), σ (c • e) = c • σ e := fun c e => by
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, AlgHom.commutes]
  set θ : E := x0 - σ x0 with hθ
  have hθ0 : θ ≠ 0 := sub_ne_zero.2 hx0.symm
  have hσθ : σ θ = -θ := by rw [hθ, map_sub, hσ]; ring
  have hli : LinearIndependent F ![(1 : E), θ] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h2 := congrArg σ hst
    rw [map_add, hsm, hsm, map_one, hσθ, map_zero, smul_neg] at h2
    have h3 : (2 : E) * (t • θ) = 0 := by linear_combination hst - h2
    have h4 : t • θ = 0 := by simpa only [mul_eq_zero, two_ne_zero, false_or] using h3
    have ht : t = 0 := (smul_eq_zero.1 h4).resolve_right hθ0
    subst ht
    exact ⟨by simpa using hst, rfl⟩
  let b : Module.Basis (Fin 2) F E :=
    basisOfLinearIndependentOfCardEqFinrank hli (by simp [hr])
  have hb0 : b 0 = 1 := by simp [b]
  have hb1 : b 1 = θ := by simp [b]
  have hrep := b.sum_repr (θ * θ)
  rw [Fin.sum_univ_two, hb0, hb1] at hrep
  set s := b.repr (θ * θ) 0
  set t := b.repr (θ * θ) 1
  have h2 := congrArg σ hrep
  rw [map_add, hsm, hsm, map_one, map_mul, hσθ, smul_neg] at h2
  have h3 : (2 : E) * (t • θ) = 0 := by linear_combination hrep - h2
  have h4 : t • θ = 0 := by simpa only [mul_eq_zero, two_ne_zero, false_or] using h3
  have hsq : θ * θ = algebraMap F E s := by
    rw [← hrep, h4, add_zero, Algebra.algebraMap_eq_smul_one]
  refine ⟨s, b, ?_, hb0, by rw [hb1, hσθ], by rw [hb1, hsq]⟩
  rintro ⟨r, hr⟩
  rw [hr, map_mul, mul_self_eq_mul_self_iff] at hsq
  have hfix : σ θ = θ := by
    rcases hsq with h | h
    · rw [h, AlgHom.commutes]
    · rw [h, map_neg, AlgHom.commutes]
  have h5 : (2 : E) * θ = 0 := by linear_combination hσθ - hfix
  exact hθ0 (by simpa only [mul_eq_zero, two_ne_zero, false_or] using h5)
end GlobalTheory.QuadNormBase
