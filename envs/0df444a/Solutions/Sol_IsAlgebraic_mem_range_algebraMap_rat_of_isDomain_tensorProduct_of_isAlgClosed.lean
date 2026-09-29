-- Prove2me | solution 1 for IsAlgebraic.mem_range_algebraMap_rat_of_isDomain_tensorProduct_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/50124f9b-ebc9-55cd-a727-0750537bbb85

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsAlgebraic_mem_range_algebraMap_rat_of_isDomain_tensorProduct_of_isAlgClosed

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct Polynomial AlgebraicGeometry.Polynomial"

theorem solution
    (K : Type) [Field K] [CharZero K]
    (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (h : IsDomain (K ⊗[ℚ] C))
    (x : K) (hx : IsAlgebraic ℚ x) :
    x ∈ Set.range (algebraMap ℚ K) := by
  classical
  haveI := h

  have hint : IsIntegral ℚ x := hx.isIntegral
  set p : ℚ[X] := minpoly ℚ x with hp
  have hpmonic : p.Monic := minpoly.monic hint
  have hpx : aeval x p = 0 := minpoly.aeval ℚ x

  let ιC : C →+* K ⊗[ℚ] C := (Algebra.TensorProduct.includeRight : C →ₐ[ℚ] K ⊗[ℚ] C).toRingHom
  let ιK : K →+* K ⊗[ℚ] C := (Algebra.TensorProduct.includeLeftRingHom : K →+* K ⊗[ℚ] C)
  let ψ : C[X] →+* K ⊗[ℚ] C := Polynomial.eval₂RingHom ιC (x ⊗ₜ[ℚ] (1 : C))

  have hψp : ψ (p.map (algebraMap ℚ C)) = 0 := by
    show Polynomial.eval₂ ιC (x ⊗ₜ[ℚ] (1 : C)) (p.map (algebraMap ℚ C)) = 0
    rw [Polynomial.eval₂_map]
    have hcomp : ιC.comp (algebraMap ℚ C) = ιK.comp (algebraMap ℚ K) := by
      ext q
      show (1 : K) ⊗ₜ[ℚ] (algebraMap ℚ C q) = (algebraMap ℚ K q) ⊗ₜ[ℚ] (1 : C)
      rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
    rw [hcomp, ← Polynomial.eval₂_map, show x ⊗ₜ[ℚ] (1 : C) = ιK x from rfl]
    have : Polynomial.eval₂ ιK (ιK x) (p.map (algebraMap ℚ K)) = ιK (Polynomial.eval₂ (RingHom.id K) x (p.map (algebraMap ℚ K))) := by
      rw [Polynomial.hom_eval₂, RingHom.comp_id]
    rw [this, Polynomial.eval₂_id, Polynomial.eval_map, ← Polynomial.aeval_def, hpx, map_zero]

  have hsplit := Polynomial.Splits.eq_prod_roots (IsAlgClosed.splits (p.map (algebraMap ℚ C)))
  rw [(hpmonic.map (algebraMap ℚ C)).leadingCoeff, map_one, one_mul] at hsplit
  have hprod : ((p.map (algebraMap ℚ C)).roots.map fun r => ψ (Polynomial.X - Polynomial.C r)).prod = 0 := by
    have : ((p.map (algebraMap ℚ C)).roots.map fun r => ψ (Polynomial.X - Polynomial.C r)) =
        (((p.map (algebraMap ℚ C)).roots.map fun r => Polynomial.X - Polynomial.C r).map ψ) := by
      rw [Multiset.map_map]; rfl
    rw [this, ← map_multiset_prod, ← hsplit]; exact hψp
  obtain ⟨r, -, hr⟩ : ∃ r ∈ (p.map (algebraMap ℚ C)).roots, ψ (Polynomial.X - Polynomial.C r) = 0 := by
    have h0 := Multiset.prod_eq_zero_iff.1 hprod
    rw [Multiset.mem_map] at h0
    obtain ⟨r, hr, h⟩ := h0
    exact ⟨r, hr, h⟩

  have hxr : x ⊗ₜ[ℚ] (1 : C) = (1 : K) ⊗ₜ[ℚ] r := by
    have : ψ (Polynomial.X - Polynomial.C r) = x ⊗ₜ[ℚ] (1 : C) - (1 : K) ⊗ₜ[ℚ] r := by
      show Polynomial.eval₂ ιC (x ⊗ₜ[ℚ] (1 : C)) (Polynomial.X - Polynomial.C r) = _
      rw [Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_C]; rfl
    rw [this] at hr
    exact sub_eq_zero.1 hr

  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap ℚ C)
    (by rw [LinearMap.ker_eq_bot]; exact (algebraMap ℚ C).injective)
  have hg1 : g 1 = 1 := by
    have := LinearMap.congr_fun hg (1 : ℚ)
    simpa using this
  let Φ : K ⊗[ℚ] C →ₗ[ℚ] K := (TensorProduct.rid ℚ K).toLinearMap ∘ₗ LinearMap.lTensor K g
  have h1 : Φ (x ⊗ₜ[ℚ] (1 : C)) = x := by
    simp [Φ, LinearMap.lTensor_tmul, hg1]
  have h2 : Φ ((1 : K) ⊗ₜ[ℚ] r) = algebraMap ℚ K (g r) := by
    simp [Φ, LinearMap.lTensor_tmul, Algebra.algebraMap_eq_smul_one]
  refine ⟨g r, ?_⟩
  rw [← h2, ← hxr, h1]

end S_IsAlgebraic_mem_range_algebraMap_rat_of_isDomain_tensorProduct_of_isAlgClosed
end P2MW
export P2MW.S_IsAlgebraic_mem_range_algebraMap_rat_of_isDomain_tensorProduct_of_isAlgClosed (solution)
