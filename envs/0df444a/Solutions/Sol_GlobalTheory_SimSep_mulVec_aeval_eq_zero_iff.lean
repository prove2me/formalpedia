-- Prove2me | solution 1 for GlobalTheory.SimSep.mulVec_aeval_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:48:14.477145+00:00
-- url     : https://prove2.me/submissions/0e52fc7b-a22b-4e25-bb54-d374fb0921f3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsCyclicVectorOfSeparableCharpoly
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ConjOfCharpolyEqOfCharpolySeparable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Polynomial
open GlobalTheory GlobalTheory.SimSep
namespace GlobalTheory.SimSep
theorem _root_.solution {R : Type} [Field R] {m : ℕ} (A : Matrix (Fin m) (Fin m) R)
    (v : Fin m → R) (hv : ∀ u : Fin m → R, ∃ p : R[X], u = aeval A p *ᵥ v) (p : R[X]) :
    aeval A p *ᵥ v = 0 ↔ A.charpoly ∣ p := by
  constructor
  · intro h
    have hA : aeval A p = 0 := by
      refine Matrix.toLin'.injective (LinearMap.ext fun u => ?_)
      obtain ⟨q, rfl⟩ := hv u
      simp only [Matrix.toLin'_apply, map_zero, LinearMap.zero_apply, Matrix.mulVec_mulVec]
      rw [← map_mul, mul_comm, map_mul, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_zero]
    have hmin : minpoly R A ∣ p := minpoly.dvd R A hA
    have hmon : (minpoly R A).Monic := minpoly.monic (Matrix.isIntegral A)

    set d := (minpoly R A).natDegree with hd
    let ψ : (Fin d → R) →ₗ[R] (Fin m → R) :=
      { toFun := fun c => aeval A (((degreeLTEquiv R d).symm c : degreeLT R d) : R[X]) *ᵥ v
        map_add' := fun a b => by simp [Matrix.add_mulVec]
        map_smul' := fun c a => by simp [Matrix.smul_mulVec] }
    have hψ : Function.Surjective ψ := by
      intro u
      obtain ⟨q, rfl⟩ := hv u
      have hq : q %ₘ minpoly R A ∈ degreeLT R d := by
        rw [mem_degreeLT]
        exact lt_of_lt_of_le (degree_modByMonic_lt q hmon) (degree_le_natDegree)
      refine ⟨degreeLTEquiv R d ⟨_, hq⟩, ?_⟩
      simp [ψ, Polynomial.aeval_modByMonic_eq_self_of_root (minpoly.aeval R A)]
    have hle : m ≤ d := by
      have := LinearMap.finrank_range_le ψ
      rw [LinearMap.range_eq_top.mpr hψ, finrank_top] at this
      simpa using this
    have heq : minpoly R A = A.charpoly := by
      refine (Polynomial.eq_of_monic_of_dvd_of_natDegree_le hmon (Matrix.charpoly_monic A)
        (Matrix.minpoly_dvd_charpoly A) ?_).symm
      rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
      exact hle
    rwa [heq] at hmin
  · rintro ⟨q, rfl⟩
    rw [map_mul, Matrix.aeval_self_charpoly, zero_mul, Matrix.zero_mulVec]
end GlobalTheory.SimSep
