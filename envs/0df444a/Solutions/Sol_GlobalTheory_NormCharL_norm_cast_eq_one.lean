-- Prove2me | solution 1 for GlobalTheory.NormCharL.norm_cast_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:15:50.060795+00:00
-- url     : https://prove2.me/submissions/aa4c4731-a298-44d4-886b-bb730ace2387

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IdealCharacterLContinuationNeZeroOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_InfinitelyManyPrimesInRayClass
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsMixedSpaceNormSignCharacterStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsContinuousNormCharLFunctionNeZeroOne
import Theorems.Thm_Formalism_H_dualEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
open NumberField IsDedekindDomain NumberField.mixedEmbedding Filter Topology Asymptotics Polynomial
open scoped ContDiff Classical
open GlobalTheory
open GlobalTheory.NormCharL
namespace GlobalTheory.NormCharL
theorem _root_.solution (K : Type) [Field K] [NumberField K] (m : ℕ) (β : 𝓞 K)
    (h : β - 1 ∈ Ideal.span {(m : 𝓞 K)}) : ((Algebra.norm ℤ β : ℤ) : ZMod m) = 1 := by
  obtain ⟨γ, hγ⟩ := Ideal.mem_span_singleton'.1 h
  have hβ : β = 1 + (m : 𝓞 K) * γ := by rw [mul_comm, hγ]; ring
  let b := Module.Free.chooseBasis ℤ (𝓞 K)
  have key : (Int.castRingHom (ZMod m)).mapMatrix (Algebra.leftMulMatrix b β) = 1 := by
    rw [hβ, map_add, map_one, map_mul, map_natCast, map_add, map_one, map_mul, map_natCast]
    ext i j
    simp [Matrix.one_apply]
  have h2 := (Int.castRingHom (ZMod m)).map_det (Algebra.leftMulMatrix b β)
  rw [key, Matrix.det_one, ← Algebra.norm_eq_matrix_det] at h2
  simpa using h2
end GlobalTheory.NormCharL
