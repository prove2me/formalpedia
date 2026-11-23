-- Prove2me | solution 1 for GlobalTheory.one_tmul_D_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:17:04.953821+00:00
-- url     : https://prove2.me/submissions/1c88a3f2-81ad-4926-bd64-899536624fc4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_AlternatingMapSumSmulEqDetSmul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsBasisKaehlerOfAlgebraicIndependent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open scoped BigOperators TensorProduct nonZeroDivisors
open Module KaehlerDifferential IsLocalRing
variable (K : Type*) {V : Type*} [Field K] [PerfectField K] [CommRing V] [IsDomain V]
  [IsDiscreteValuationRing V] [Algebra K V] [Algebra.EssFiniteType K V]
  [Algebra.FormallySmooth K V]
namespace GlobalTheory
theorem _root_.solution {t : V} (ht : Irreducible t) :
    (1 : ResidueField V) ⊗ₜ[V] D K V t ≠ 0 := by
  have hs : Function.Surjective (algebraMap V (ResidueField V)) := residue_surjective
  have : Algebra.EssFiniteType K (ResidueField V) := .comp K V _
  have hinj := (Algebra.FormallySmooth.kerCotangentToTensor_injective_iff (R := K) hs).mpr
    inferInstance
  have hker : RingHom.ker (algebraMap V (ResidueField V)) = Ideal.span {t} :=
    ker_residue.trans ht.maximalIdeal_eq
  have hmem : t ∈ RingHom.ker (algebraMap V (ResidueField V)) :=
    hker ▸ Ideal.mem_span_singleton_self t
  intro h
  have h₁ : (RingHom.ker (algebraMap V (ResidueField V))).toCotangent ⟨t, hmem⟩ = 0 := by
    apply hinj
    rw [kerCotangentToTensor_toCotangent, map_zero]
    exact h
  have h₂ : t ∈ RingHom.ker (algebraMap V (ResidueField V)) ^ 2 :=
    (Ideal.toCotangent_eq_zero _ _).mp h₁
  rw [hker, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h₂
  obtain ⟨c, hc⟩ := h₂
  have : t * 1 = t * (t * c) := by rw [mul_one, ← mul_assoc, ← sq]; exact hc
  exact ht.not_isUnit (IsUnit.of_mul_eq_one c (mul_left_cancel₀ ht.ne_zero this).symm)
end GlobalTheory
