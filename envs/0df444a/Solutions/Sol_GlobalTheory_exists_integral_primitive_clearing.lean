-- Prove2me | solution 1 for GlobalTheory.exists_integral_primitive_clearing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:42:39.015852+00:00
-- url     : https://prove2.me/submissions/5b50b77b-8502-4880-84ae-43c35e8e6c6c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SepIntPolyRootModPrimeSqStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NumberFieldToModPSquared

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct Polynomial
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (K : Type) [Field K] [NumberField K], ∃ θ : K, IsIntegral ℤ θ ∧ 0 < (minpoly ℤ θ).natDegree ∧ ((minpoly ℤ θ).map (Int.castRingHom ℚ)).Separable ∧ ∀ s : K, ∃ N : ℕ, 0 < N ∧ (N : K) * s ∈ Algebra.adjoin ℤ ({θ} : Set K) := by
  intro K _ _
  obtain ⟨α, hα⟩ := Field.exists_primitive_element ℚ K
  have halg : IsAlgebraic ℤ α := (IsFractionRing.isAlgebraic_iff ℤ ℚ K).2 (Algebra.IsAlgebraic.isAlgebraic α)
  obtain ⟨y, hy0, hy⟩ := halg.exists_integral_multiple
  set θ : K := (y : K) * α with hθdef
  have hθ : IsIntegral ℤ θ := by rw [hθdef, ← zsmul_eq_mul]; exact hy
  refine ⟨θ, hθ, minpoly.natDegree_pos hθ, ?_, ?_⟩
  · rw [← algebraMap_int_eq, ← minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hθ]
    exact Algebra.IsSeparable.isSeparable ℚ θ
  · intro s
    set O := Algebra.adjoin ℤ ({θ} : Set K)
    have hθO : θ ∈ O := Algebra.subset_adjoin rfl
    have hs : s ∈ Algebra.adjoin ℚ ({α} : Set K) := by
      rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic (Algebra.IsAlgebraic.isAlgebraic α), hα]
      trivial
    induction hs using Algebra.adjoin_induction with
    | mem x hx =>
      rw [Set.mem_singleton_iff] at hx
      refine ⟨y.natAbs, Int.natAbs_pos.mpr hy0, ?_⟩
      rw [hx]
      rcases Int.natAbs_eq y with h | h
      · have : ((y.natAbs : ℕ) : K) = (y : K) := (Int.cast_natCast (R := K) _).symm.trans (congrArg (Int.cast (R := K)) h.symm)
        rw [this]; exact hθO
      · have h' : (y.natAbs : ℤ) = -y := by omega
        have : ((y.natAbs : ℕ) : K) = -(y : K) := (Int.cast_natCast (R := K) _).symm.trans ((congrArg (Int.cast (R := K)) h').trans (Int.cast_neg y))
        rw [this, neg_mul]; exact O.neg_mem hθO
    | algebraMap q =>
      refine ⟨q.den, q.den_pos, ?_⟩
      have : ((q.den : ℕ) : K) * algebraMap ℚ K q = algebraMap ℤ K q.num := by
        rw [algebraMap_int_eq, eq_intCast, ← map_natCast (algebraMap ℚ K), ← map_mul,
          ← map_intCast (algebraMap ℚ K)]
        congr 1
        rw [mul_comm]; exact Rat.mul_den_eq_num q
      rw [this]; exact O.algebraMap_mem _
    | add a b _ _ ha hb =>
      obtain ⟨M, hM, hMa⟩ := ha
      obtain ⟨M', hM', hMb⟩ := hb
      refine ⟨M * M', Nat.mul_pos hM hM', ?_⟩
      have : ((M * M' : ℕ) : K) * (a + b) = (M' : ℤ) • ((M : K) * a) + (M : ℤ) • ((M' : K) * b) := by
        simp only [zsmul_eq_mul]; push_cast; ring
      rw [this]
      exact O.add_mem (O.zsmul_mem hMa _) (O.zsmul_mem hMb _)
    | mul a b _ _ ha hb =>
      obtain ⟨M, hM, hMa⟩ := ha
      obtain ⟨M', hM', hMb⟩ := hb
      refine ⟨M * M', Nat.mul_pos hM hM', ?_⟩
      have : ((M * M' : ℕ) : K) * (a * b) = ((M : K) * a) * ((M' : K) * b) := by
        push_cast; ring
      rw [this]
      exact O.mul_mem hMa hMb
end GlobalTheory
