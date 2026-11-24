-- Prove2me | solution 1 for GlobalTheory.repTrace_eq_mul_trace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:31:25.755831+00:00
-- url     : https://prove2.me/submissions/68afa9a5-094f-4413-8439-f9edc6ae8f0d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RepTraceEqMulTrace
import Theorems.Thm_GlobalTheory_RepTrace_isUnit_of_ne_zero
import Theorems.Thm_GlobalTheory_RepTrace_trace_lsmul_restrictScalars

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {E : Type} [Field E] [NumberField E] {r : ℕ} (ρ : 𝓞 E →+* Matrix (Fin r) (Fin r) ℤ) (s : ℕ)
    (hr : r = s * Module.finrank ℚ E) (a : 𝓞 E) : (ρ a).trace = s * Algebra.trace ℤ (𝓞 E) a := by
  classical
  let g : 𝓞 E →+* Module.End ℚ (Fin r → ℚ) :=
    (Matrix.toLinAlgEquiv' : Matrix (Fin r) (Fin r) ℚ ≃ₐ[ℚ] _).toRingEquiv.toRingHom.comp
      ((Int.castRingHom ℚ).mapMatrix.comp ρ)
  let A := Algebra.adjoin ℚ (Set.range g)
  letI : CommRing A := Algebra.adjoinCommRingOfComm ℚ (by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    rw [← map_mul, ← map_mul, mul_comm])
  let g' : 𝓞 E →+* A := g.codRestrict A (fun x => Algebra.subset_adjoin ⟨x, rfl⟩)
  let φ : E →+* Module.End ℚ (Fin r → ℚ) :=
    (A.val : A →ₐ[ℚ] Module.End ℚ (Fin r → ℚ)).toRingHom.comp
      (IsLocalization.lift (M := nonZeroDivisors (𝓞 E)) (S := E) (g := g')
        (fun y => RepTrace.isUnit_of_ne_zero g' y (nonZeroDivisors.ne_zero y.2)))
  letI : Module E (Fin r → ℚ) := Module.compHom (Fin r → ℚ) φ
  have hφq : φ.comp (algebraMap ℚ E) = algebraMap ℚ (Module.End ℚ (Fin r → ℚ)) := Subsingleton.elim _ _
  haveI : IsScalarTower ℚ E (Fin r → ℚ) := ⟨fun q x v => by
    change φ (q • x) v = q • φ x v
    rw [Algebra.smul_def, map_mul, Module.End.mul_apply]
    have := RingHom.congr_fun hφq q
    simp only [RingHom.comp_apply] at this
    rw [this, Module.algebraMap_end_apply]⟩
  haveI : FiniteDimensional E (Fin r → ℚ) := Module.Finite.of_restrictScalars_finite ℚ E _
  have hfin : Module.finrank E (Fin r → ℚ) = s := by
    have h := Module.finrank_mul_finrank ℚ E (Fin r → ℚ)
    rw [Module.finrank_fin_fun] at h
    have hd : 0 < Module.finrank ℚ E := Module.finrank_pos
    have h2 : Module.finrank ℚ E * Module.finrank E (Fin r → ℚ) = Module.finrank ℚ E * s := by
      rw [h, hr, mul_comm]
    exact Nat.eq_of_mul_eq_mul_left hd h2
  have key : LinearMap.trace ℚ (Fin r → ℚ) (g a) = ((ρ a).trace : ℚ) := by
    change LinearMap.trace ℚ _ (Matrix.toLin' ((ρ a).map (Int.castRingHom ℚ))) = _
    rw [LinearMap.trace_eq_matrix_trace ℚ (Pi.basisFun ℚ (Fin r)), LinearMap.toMatrix_eq_toMatrix',
      LinearMap.toMatrix'_toLin']
    simp [Matrix.trace]
  have hga : g a = (LinearMap.lsmul E (Fin r → ℚ) (a : E)).restrictScalars ℚ := by
    refine LinearMap.ext fun v => ?_
    change g a v = φ (algebraMap (𝓞 E) E a) v
    simp only [φ, RingHom.comp_apply, IsLocalization.lift_eq]
    rfl
  apply Int.cast_injective (α := ℚ)
  rw [← key, hga, RepTrace.trace_lsmul_restrictScalars, hfin]
  push_cast
  rw [Algebra.coe_trace_int]
end GlobalTheory
