-- Prove2me | solution 1 for GlobalTheory.xClasses_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:03:55.400659+00:00
-- url     : https://prove2.me/submissions/980a0292-a523-45bb-a8d5-5cfefdfcf898

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubmodulesAndLinearEquivBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubgroupsOfIndexLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_XClassesDenom
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
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {K : Type} [Field K] [NumberField K] (I J : Ideal (𝓞 K)) (a : 𝓞 K)
    (hI : I ≠ ⊥) (haI : a ∈ I) (h : Ideal.span {a} = I * J) (z : K)
    (hz : ∀ α ∈ I, ∃ o : 𝓞 K, (o : K) = (α : K) * z) :
    ∃ o : J.toAddSubgroup, ((o : 𝓞 K) : K) = (a : K) * z := by
  obtain ⟨o, ho⟩ := hz a haI
  have hmem : o ∈ J := by
    have hle : Ideal.span {o} * I ≤ J * I := by
      rw [Ideal.span_singleton_mul_le_iff]
      intro α hα
      obtain ⟨p, hp⟩ := hz α hα
      have hop : o * α = a * p := by
        apply IsFractionRing.injective (𝓞 K) K
        simp only [map_mul]
        change (o : K) * (α : K) = (a : K) * (p : K)
        rw [ho, hp]; ring
      rw [hop, mul_comm J I, ← h]
      exact Ideal.mul_mem_right p _ (Ideal.mem_span_singleton_self a)
    have hdvd : J * I ∣ Ideal.span {o} * I := Ideal.dvd_iff_le.mpr hle
    rw [mul_dvd_mul_iff_right hI] at hdvd
    exact Ideal.dvd_span_singleton.mp hdvd
  exact ⟨⟨o, hmem⟩, ho⟩
end GlobalTheory
