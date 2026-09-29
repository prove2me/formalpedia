-- Prove2me | solution 1 for NumberField.mixedEmbedding.exists_forall_norm_embedding_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/ae510a75-1d0e-597b-909a-0c4961793050

import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_mixedEmbedding_exists_forall_norm_embedding_sub_le

open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding Module

open scoped Classical

noncomputable section

namespace M4aP1R
namespace IntegerTranslate

variable (K : Type*) [Field K] [NumberField K]

theorem exists_norm_sub_mixedEmbedding_le :
    ∃ U : ℝ, ∀ m : mixedSpace K, ∃ b : 𝓞 K, ‖m - mixedEmbedding K (b : K)‖ ≤ U := by
  classical
  let B := mixedEmbedding.latticeBasis K
  refine ⟨∑ i, ‖B i‖, fun m => ?_⟩
  have hv : m - ZSpan.fract B m ∈ mixedEmbedding.integerLattice K := by
    rw [← mem_span_latticeBasis]
    have h1 : m - ZSpan.fract B m = (ZSpan.floor B m : mixedSpace K) := by
      rw [ZSpan.fract_apply]; abel
    rw [h1]
    exact (ZSpan.floor B m).2
  obtain ⟨b, hb⟩ := LinearMap.mem_range.mp hv
  refine ⟨b, ?_⟩
  have hb' : mixedEmbedding K (b : K) = m - ZSpan.fract B m := hb
  rw [hb', sub_sub_cancel]
  exact ZSpan.norm_fract_le B m

end M4aP1R.IntegerTranslate

open M4aP1R.IntegerTranslate in

theorem M4aP1R.IntegerTranslate.exists_forall_norm_embedding_sub_le_impl (K : Type*) [Field K]
    [NumberField K] : ∃ U : ℝ, ∀ ξ : NumberField.InfinitePlace K → ℂ,
      (∀ w : NumberField.InfinitePlace K, w.IsReal → (ξ w).im = 0) →
        ∃ b : NumberField.RingOfIntegers K, ∀ w : NumberField.InfinitePlace K,
          ‖w.embedding (b : K) - ξ w‖ ≤ U := by
  classical
  obtain ⟨U, hU⟩ := exists_norm_sub_mixedEmbedding_le K
  refine ⟨U, fun ξ hξ => ?_⟩
  let m : mixedSpace K := (fun w => (ξ w.val).re, fun w => ξ w.val)
  obtain ⟨b, hb⟩ := hU m
  refine ⟨b, fun w => ?_⟩
  by_cases hw : IsReal w
  · have h1 := (norm_le_pi_norm (m - mixedEmbedding K (b : K)).1 ⟨w, hw⟩).trans
      ((norm_fst_le _).trans hb)
    rw [Prod.fst_sub, Pi.sub_apply, mixedEmbedding_apply_isReal, Real.norm_eq_abs] at h1
    have hξw : ξ w = ((ξ w).re : ℂ) := by
      apply Complex.ext
      · simp
      · simp [hξ w hw]
    rw [hξw, ← embedding_of_isReal_apply hw, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs, abs_sub_comm]
    exact h1
  · have hc : IsComplex w := not_isReal_iff_isComplex.mp hw
    have h1 := (norm_le_pi_norm (m - mixedEmbedding K (b : K)).2 ⟨w, hc⟩).trans
      ((norm_snd_le _).trans hb)
    rw [Prod.snd_sub, Pi.sub_apply, mixedEmbedding_apply_isComplex] at h1
    rw [norm_sub_rev]
    exact h1

theorem solution (K : Type*) [Field K]
    [NumberField K] : ∃ U : ℝ, ∀ ξ : NumberField.InfinitePlace K → ℂ,
      (∀ w : NumberField.InfinitePlace K, w.IsReal → (ξ w).im = 0) →
        ∃ b : NumberField.RingOfIntegers K, ∀ w : NumberField.InfinitePlace K,
          ‖w.embedding (b : K) - ξ w‖ ≤ U := by
  exact M4aP1R.IntegerTranslate.exists_forall_norm_embedding_sub_le_impl K

end
end S_NumberField_mixedEmbedding_exists_forall_norm_embedding_sub_le
end P2MW
export P2MW.S_NumberField_mixedEmbedding_exists_forall_norm_embedding_sub_le (solution)
