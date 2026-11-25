-- Prove2me | solution 1 for GlobalTheory.DefinitePacking.one_le_norm_mul_absNorm_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:01:47.813671+00:00
-- url     : https://prove2.me/submissions/aad8ac48-9770-4ce6-aa25-6a2877cec483

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubmodulesAndLinearEquivBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubgroupsOfIndexLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_OneLeNormMulAbsNormSq
import Theorems.Thm_GlobalTheory_DefinitePacking_one_le_norm_mul_absNorm
import Theorems.Thm_GlobalTheory_DefinitePacking_absNorm_map_equiv
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
theorem _root_.solution {K : Type} [Field K] [NumberField K] [StarRing K] (c : K)
    (hc : c ≠ 0) (I : Ideal (𝓞 K)) (hI : I ≠ ⊥)
    (h : ∀ a ∈ I, ∀ b ∈ I, ∃ o : 𝓞 K, (o : K) = c * (star (a : K) * b)) :
    (1 : ℝ) ≤ |((Algebra.norm ℚ c : ℚ) : ℝ)| * (Ideal.absNorm I : ℝ) ^ 2 := by
  let e : 𝓞 K ≃+* 𝓞 K := RingOfIntegers.mapRingEquiv (starRingAut : K ≃+* K)
  have he : ∀ a : 𝓞 K, (e a : K) = star (a : K) := fun a => rfl
  have hN := absNorm_map_equiv e I
  have h1 : I.map (e : 𝓞 K →+* 𝓞 K) ≠ ⊥ := by
    rw [Ne, ← Ideal.absNorm_eq_zero_iff, hN, Ideal.absNorm_eq_zero_iff]
    exact hI
  have := one_le_norm_mul_absNorm c hc (I.map (e : 𝓞 K →+* 𝓞 K) * I) (mul_ne_zero h1 hI) (by
    intro a ha
    refine Submodule.mul_induction_on ha ?_ ?_
    · intro m hm n hn
      obtain ⟨m', hm', rfl⟩ := (Ideal.mem_map_iff_of_surjective (e : 𝓞 K →+* 𝓞 K) e.surjective).mp hm
      obtain ⟨o, ho⟩ := h m' hm' n hn
      refine ⟨o, ?_⟩
      rw [ho, ← he]
      simp
    · rintro x y ⟨o, ho⟩ ⟨o', ho'⟩
      refine ⟨o + o', ?_⟩
      change algebraMap _ K (o + o') = c * algebraMap _ K (x + y)
      rw [map_add, map_add, mul_add]
      exact congrArg₂ (· + ·) ho ho')
  rw [map_mul, hN] at this
  push_cast at this
  rw [sq]
  exact this
end GlobalTheory.DefinitePacking
