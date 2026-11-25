-- Prove2me | solution 1 for GlobalTheory.DefinitePacking.one_le_norm_mul_absNorm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T06:26:14.161801+00:00
-- url     : https://prove2.me/submissions/4f997c11-09ab-4261-8e11-6aa3ae627af4

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubmodulesAndLinearEquivBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubgroupsOfIndexLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_OneLeNormMulAbsNormSq
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
open NumberField Module Matrix Formalism.BasicNotions
open scoped ENNReal
open GlobalTheory GlobalTheory.DefinitePacking
namespace GlobalTheory.DefinitePacking
theorem _root_.solution {K : Type} [Field K] [NumberField K] (c : K) (hc : c ≠ 0)
    (J : Ideal (𝓞 K)) (hJ : J ≠ ⊥) (h : ∀ a ∈ J, ∃ o : 𝓞 K, (o : K) = c * a) :
    (1 : ℝ) ≤ |((Algebra.norm ℚ c : ℚ) : ℝ)| * (Ideal.absNorm J : ℝ) := by
  obtain ⟨a, d, hd, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) c
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  have hdK : algebraMap (𝓞 K) K d ≠ 0 := by simpa using hd0
  have ha0 : a ≠ 0 := by rintro rfl; simp at hc
  have hle : Ideal.span {a} * J ≤ Ideal.span {d} := by
    rw [Ideal.span_singleton_mul_le_iff]
    intro z hz
    obtain ⟨o, ho⟩ := h z hz
    rw [Ideal.mem_span_singleton']
    refine ⟨o, ?_⟩
    apply IsFractionRing.injective (𝓞 K) K
    rw [map_mul, map_mul]
    change (o : K) * _ = _ * (z : K)
    rw [ho]
    field_simp
  have hdvd := Ideal.absNorm_dvd_absNorm_of_le hle
  have hne : Ideal.absNorm (Ideal.span {a} * J) ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact mul_ne_zero (by simpa using ha0) hJ
  have hl := Nat.le_of_dvd (Nat.pos_of_ne_zero hne) hdvd
  rw [map_mul, Ideal.absNorm_span_singleton, Ideal.absNorm_span_singleton] at hl
  have hl' : (((Algebra.norm ℤ d).natAbs : ℕ) : ℝ) ≤ (((Algebra.norm ℤ a).natAbs : ℕ) : ℝ) * (Ideal.absNorm J : ℝ) := by
    exact_mod_cast hl
  have key : ∀ z : 𝓞 K, (((Algebra.norm ℤ z).natAbs : ℕ) : ℝ) = |((Algebra.norm ℚ (z : K) : ℚ) : ℝ)| := by
    intro z
    rw [← Algebra.coe_norm_int, Nat.cast_natAbs]
    push_cast
    rfl
  rw [key, key] at hl'
  have hdn : (0 : ℝ) < |((Algebra.norm ℚ (d : K) : ℚ) : ℝ)| := by
    rw [abs_pos]
    exact_mod_cast (Algebra.norm_ne_zero_iff.mpr hdK)
  have hm : Algebra.norm ℚ (algebraMap (𝓞 K) K a / algebraMap (𝓞 K) K d) * Algebra.norm ℚ (d : K)
      = Algebra.norm ℚ (a : K) := by
    rw [← map_mul]
    congr 1
    exact div_mul_cancel₀ _ hdK
  rw [← hm] at hl'
  push_cast at hl'
  rw [abs_mul] at hl'
  refine le_of_mul_le_mul_right ?_ hdn
  linarith
end GlobalTheory.DefinitePacking
