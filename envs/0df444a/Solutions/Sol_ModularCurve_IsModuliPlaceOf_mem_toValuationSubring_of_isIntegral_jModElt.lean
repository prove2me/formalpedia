-- Prove2me | solution 1 for ModularCurve.IsModuliPlaceOf.mem_toValuationSubring_of_isIntegral_jModElt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/afa6c217-3c27-5e24-8a1e-8666dfc0005f

import Mathlib
import Definitions.Def_ModularCurve_ModuliPlace
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_IsModuliPlaceOf_mem_toValuationSubring_of_isIntegral_jModElt

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 400000

universe u

theorem solution
    (K : Type u) [Field K] [DecidableEq K] (N : ℕ) [NeZero N]
    (x : ModularCurve.ModuliPoint N K) (v : AlgebraicCurve.Place K ↥(ModularCurve.modularFunctionFieldFullC K N))
    (h : ModularCurve.IsModuliPlaceOf K N x v)
    (a : ↥(ModularCurve.modularFunctionFieldFullC K N)) (ha : (∃ P : Polynomial (Polynomial K), P.Monic ∧ Polynomial.eval₂ (Polynomial.aeval (R := K) (ModularCurve.jModElt K (ModularCurve.jqModC_mem_full K N))).toRingHom a P = 0)) :
    a ∈ v.toValuationSubring := by
  classical
  obtain ⟨P, hPmonic, hP⟩ := ha

  have hsub_ne : ModularCurve.jModElt K (ModularCurve.jqModC_mem_full K N) - algebraMap K ↥(ModularCurve.modularFunctionFieldFullC K N) x.j ≠ 0 := ModularCurve.jModElt_sub_algebraMap_ne_zero K N x.j
  have hord : 0 < v.ord (ModularCurve.jModElt K (ModularCurve.jqModC_mem_full K N) - algebraMap K ↥(ModularCurve.modularFunctionFieldFullC K N) x.j) := ModularCurve.IsModuliPlaceOf.ord_jModElt_sub_pos h
  have hsub_mem : ModularCurve.jModElt K (ModularCurve.jqModC_mem_full K N) - algebraMap K ↥(ModularCurve.modularFunctionFieldFullC K N) x.j ∈ v.toValuationSubring :=
    (ModularCurve.ComapPlace.mem_iff_ord_nonneg v hsub_ne).2 hord.le
  have hK : ∀ c : K, algebraMap K ↥(ModularCurve.modularFunctionFieldFullC K N) c ∈ v.toValuationSubring := v.algebraMap_mem'
  have hjt_mem : ModularCurve.jModElt K (ModularCurve.jqModC_mem_full K N) ∈ v.toValuationSubring := by
    have := add_mem hsub_mem (hK x.j)
    rwa [sub_add_cancel] at this

  have haeval : ∀ q : Polynomial K, Polynomial.aeval (R := K) (ModularCurve.jModElt K (ModularCurve.jqModC_mem_full K N)) q ∈ v.toValuationSubring := by
    intro q
    induction q using Polynomial.induction_on with
    | C c => rw [Polynomial.aeval_C]; exact hK c
    | add p q hp hq => rw [map_add (Polynomial.aeval (R := K) (ModularCurve.jModElt K (ModularCurve.jqModC_mem_full K N))) p q]; exact add_mem hp hq
    | monomial n c _ =>
      rw [map_mul (Polynomial.aeval (R := K) (ModularCurve.jModElt K (ModularCurve.jqModC_mem_full K N))), map_pow (Polynomial.aeval (R := K) (ModularCurve.jModElt K (ModularCurve.jqModC_mem_full K N))),
        Polynomial.aeval_C, Polynomial.aeval_X]
      exact mul_mem (hK c) (pow_mem hjt_mem _)

  let ψ : Polynomial K →+* ↥v.toValuationSubring :=
    (Polynomial.aeval (R := K) (ModularCurve.jModElt K (ModularCurve.jqModC_mem_full K N))).toRingHom.codRestrict v.toValuationSubring haeval
  have hψ : (algebraMap (↥v.toValuationSubring) ↥(ModularCurve.modularFunctionFieldFullC K N)).comp ψ = (Polynomial.aeval (R := K) (ModularCurve.jModElt K (ModularCurve.jqModC_mem_full K N))).toRingHom :=
    RingHom.ext fun q => rfl

  have hint : IsIntegral (↥v.toValuationSubring) a := by
    refine ⟨P.map ψ, hPmonic.map ψ, ?_⟩
    rw [Polynomial.eval₂_map, hψ]
    exact hP
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ↥v.toValuationSubring) (K := ↥(ModularCurve.modularFunctionFieldFullC K N))).1 hint
  rw [← hy]
  exact y.2

end S_ModularCurve_IsModuliPlaceOf_mem_toValuationSubring_of_isIntegral_jModElt
end P2MW
export P2MW.S_ModularCurve_IsModuliPlaceOf_mem_toValuationSubring_of_isIntegral_jModElt (solution)
