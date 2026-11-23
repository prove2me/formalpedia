-- Prove2me | solution 1 for GlobalTheory.WeilM.isQuad_split
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:12:49.788687+00:00
-- url     : https://prove2.me/submissions/87f3236c-ab31-4e00-b610-f16847f07c63

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsSplittingSplitOm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open scoped NNReal Kronecker
open GlobalTheory GlobalTheory.WeilM
variable {R : Type} [CommRing R]
namespace GlobalTheory.WeilM
theorem _root_.solution [Invertible (2 : R)] : IsQuad (swapA R) ((1, -1) : R × R) where
  unit := IsUnit.of_mul_eq_one ((1, -1) : R × R) (by ext <;> simp)
  anti := by ext <;> simp [swapA_apply]
  basis := by
    have hli : LinearIndependent R ![(1 : R × R), (1, -1)] := by
      rw [LinearIndependent.pair_iff]
      intro s t hst
      have h1 := congrArg Prod.fst hst
      have h2 := congrArg Prod.snd hst
      simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, Prod.fst_one, Prod.snd_one,
        smul_eq_mul, mul_one, mul_neg, Prod.fst_zero, Prod.snd_zero] at h1 h2
      have hs : s = 0 := by
        have h3 : (2 : R) * s = 0 := by linear_combination h1 + h2
        simpa using congrArg (⅟(2 : R) * ·) h3
      exact ⟨hs, by rw [hs] at h1; simpa using h1⟩
    have hsp : ⊤ ≤ Submodule.span R (Set.range ![(1 : R × R), (1, -1)]) := by
      intro z _
      rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Submodule.mem_span_pair]
      refine ⟨⅟(2 : R) * (z.1 + z.2), ⅟(2 : R) * (z.1 - z.2), ?_⟩
      ext
      · simp only [Prod.fst_add, Prod.smul_fst, Prod.fst_one, smul_eq_mul, mul_one]
        linear_combination z.1 * (invOf_mul_self (2 : R))
      · simp only [Prod.snd_add, Prod.smul_snd, Prod.snd_one, smul_eq_mul, mul_one, mul_neg]
        linear_combination z.2 * (invOf_mul_self (2 : R))
    exact ⟨Module.Basis.mk hli hsp, by rw [Module.Basis.mk_apply]; rfl, by rw [Module.Basis.mk_apply]; rfl⟩
end GlobalTheory.WeilM
