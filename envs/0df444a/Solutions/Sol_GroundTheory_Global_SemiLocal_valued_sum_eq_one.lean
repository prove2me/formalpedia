-- Prove2me | solution 1 for GroundTheory.Global.SemiLocal.valued_sum_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:28:35.76774+00:00
-- url     : https://prove2.me/submissions/c056acf3-b081-433b-bba0-52322c724527

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_ContinuousCompletionMap
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_LocalDegree
import Theorems.Thm_GroundTheory_Global_SemiLocal_valued_algebraMap_int_le_one
import Theorems.Thm_GroundTheory_Global_SemiLocal_valued_algebraMap_int_lt_one_iff
import Theorems.Thm_GroundTheory_Global_SemiLocal_exists_int_valued_sub_lt_one
import Theorems.Thm_GroundTheory_Global_SemiLocal_algebraMap_completion_algebraMap_int
import Theorems.Thm_GroundTheory_Global_SemiLocal_valued_algebraMap_completion
import Theorems.Thm_GroundTheory_Global_SemiLocal_valued_sum_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open IsDedekindDomain NumberField WithZero
noncomputable section
open GroundTheory.Global.SemiLocal
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
  [w.asIdeal.LiesOver v.asIdeal]
variable {ι : Type*} [Fintype ι]
namespace GroundTheory.Global.SemiLocal
theorem _root_.solution (ω : ι → 𝓞 L)
    (hω : LinearIndependent (𝓞 K ⧸ v.asIdeal) (fun j ↦ Ideal.Quotient.mk w.asIdeal (ω j)))
    (d : ι → v.adicCompletion K) (hd : ∀ j, Valued.v (d j) ≤ 1) (j0 : ι)
    (hj0 : Valued.v (d j0) = 1) :
    Valued.v (∑ j, algebraMap (v.adicCompletion K) (w.adicCompletion L) (d j) *
      algebraMap (𝓞 L) (w.adicCompletion L) (ω j)) = 1 := by
  refine le_antisymm (by simpa using valued_sum_le v w ω d 1 hd) ?_
  by_contra hlt
  replace hlt := not_le.1 hlt
  have he0 : w.asIdeal.ramificationIdx (𝓞 K) ≠ 0 := (Ideal.ramificationIdx_pos w.asIdeal (𝓞 K)).ne'
  choose r hr using fun j ↦ exists_int_valued_sub_lt_one v (d j) (hd j)
  have h1 : Valued.v (algebraMap (𝓞 L) (w.adicCompletion L)
      (∑ j, algebraMap (𝓞 K) (𝓞 L) (r j) * ω j)) < 1 := by
    have heq : algebraMap (𝓞 L) (w.adicCompletion L) (∑ j, algebraMap (𝓞 K) (𝓞 L) (r j) * ω j) =
        (∑ j, algebraMap (v.adicCompletion K) (w.adicCompletion L) (d j) *
          algebraMap (𝓞 L) (w.adicCompletion L) (ω j)) -
        ∑ j, algebraMap (v.adicCompletion K) (w.adicCompletion L)
          (d j - algebraMap (𝓞 K) (v.adicCompletion K) (r j)) *
          algebraMap (𝓞 L) (w.adicCompletion L) (ω j) := by
      rw [← Finset.sum_sub_distrib, map_sum]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [map_mul, map_sub, algebraMap_completion_algebraMap_int]
      ring
    rw [heq]
    refine lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt hlt ?_)
    apply Valuation.map_sum_lt _ one_ne_zero
    intro j _
    rw [map_mul, valued_algebraMap_completion]
    calc _ ≤ Valued.v (d j - algebraMap (𝓞 K) (v.adicCompletion K) (r j)) ^
          w.asIdeal.ramificationIdx (𝓞 K) * 1 :=
          mul_le_mul' le_rfl (valued_algebraMap_int_le_one w (ω j))
      _ < 1 := by rw [mul_one]; exact pow_lt_one' (hr j) he0
  rw [valued_algebraMap_int_lt_one_iff, ← Ideal.Quotient.eq_zero_iff_mem, map_sum] at h1
  have hsum : ∑ j, Ideal.Quotient.mk v.asIdeal (r j) • Ideal.Quotient.mk w.asIdeal (ω j) = 0 := by
    rw [← h1]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [Algebra.smul_def, map_mul, Ideal.Quotient.algebraMap_mk_of_liesOver]
  have hr0 := Fintype.linearIndependent_iff.1 hω _ hsum j0
  rw [Ideal.Quotient.eq_zero_iff_mem, ← valued_algebraMap_int_lt_one_iff v] at hr0
  have : Valued.v (d j0) < 1 := by
    calc Valued.v (d j0) = Valued.v ((d j0 - algebraMap (𝓞 K) (v.adicCompletion K) (r j0)) +
          algebraMap (𝓞 K) (v.adicCompletion K) (r j0)) := by rw [sub_add_cancel]
      _ ≤ max _ _ := Valuation.map_add _ _ _
      _ < 1 := max_lt (hr j0) hr0
  exact absurd hj0 this.ne
end GroundTheory.Global.SemiLocal
