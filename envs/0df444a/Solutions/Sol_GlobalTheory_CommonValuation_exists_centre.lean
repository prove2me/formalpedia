-- Prove2me | solution 1 for GlobalTheory.CommonValuation.exists_centre
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:15:59.751394+00:00
-- url     : https://prove2.me/submissions/20deb61f-8c73-427a-a999-b238a68daab3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsFiniteSeparableCompositum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RamificationIndexValuationCompat
import Theorems.Thm_GlobalTheory_CommonValuation_le_one_of_ringOfIntegers

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open GlobalTheory GlobalTheory.CommonValuation
namespace GlobalTheory.CommonValuation
theorem _root_.solution {F Γ : Type} [Field F] [LinearOrderedCommGroupWithZero Γ] (u : Valuation F Γ) :
    ∃ Q : Ideal (𝓞 F), Q.IsPrime ∧ ∀ r, r ∈ Q ↔ u (algebraMap (𝓞 F) F r) < 1 := by
  refine ⟨{ carrier := {r | u (algebraMap (𝓞 F) F r) < 1}
            add_mem' := fun {a b} ha hb => ?_
            zero_mem' := by simp
            smul_mem' := fun c r hr => ?_ }, ⟨?_, fun {a b} h => ?_⟩, fun _ => Iff.rfl⟩
  · change u _ < 1
    rw [map_add]
    exact u.map_add_lt ha hb
  · change u _ < 1
    rw [smul_eq_mul, map_mul, map_mul]
    exact (mul_le_of_le_one_left' (le_one_of_ringOfIntegers u c)).trans_lt hr
  · rw [Ideal.ne_top_iff_one]
    change ¬ u _ < 1
    simp
  · by_contra! hn
    have ha : u (algebraMap _ F a) = 1 := le_antisymm (le_one_of_ringOfIntegers u a) (not_lt.1 hn.1)
    have hb : u (algebraMap _ F b) = 1 := le_antisymm (le_one_of_ringOfIntegers u b) (not_lt.1 hn.2)
    change u _ < 1 at h
    rw [map_mul, map_mul, ha, hb, mul_one] at h
    exact lt_irrefl _ h
end GlobalTheory.CommonValuation
