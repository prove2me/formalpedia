-- Prove2me | solution 1 for GlobalTheory.PadicUnitBall.norm_lt_one_of_mem_maximalIdeal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:18:43.642727+00:00
-- url     : https://prove2.me/submissions/5fe456dc-62a2-41d1-9ac8-c45d81b8d57f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PadicMemRangeCompleteDvrPadicAlgCl

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory GlobalTheory.PadicUnitBall
variable {p : ℕ} [Fact p.Prime] {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  {κ : FractionRing V →+* PadicAlgCl p}
namespace GlobalTheory.PadicUnitBall
theorem _root_.solution
    (hV : ∀ x, ‖κ x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap V (FractionRing V)))
    {v : V} (hv : v ∈ maximalIdeal V) : ‖κ (algebraMap V (FractionRing V) v)‖ < 1 := by
  have hle : ‖κ (algebraMap V (FractionRing V) v)‖ ≤ 1 := (hV _).2 ⟨v, rfl⟩
  refine lt_of_le_of_ne hle fun h1 => ?_
  have hv0 : v ≠ 0 := by
    rintro rfl; simp at h1
  have hι : algebraMap V (FractionRing V) v ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective V (FractionRing V))).2 hv0
  have hinv : ‖κ (algebraMap V (FractionRing V) v)⁻¹‖ ≤ 1 := by
    rw [map_inv₀, norm_inv, h1, inv_one]
  obtain ⟨w, hw⟩ := (hV _).1 hinv
  have hvw : v * w = 1 := by
    apply IsFractionRing.injective V (FractionRing V)
    rw [map_mul, hw, map_one, mul_inv_cancel₀ hι]
  exact (mem_maximalIdeal _).1 hv ⟨⟨v, w, hvw, by rw [mul_comm]; exact hvw⟩, rfl⟩
end GlobalTheory.PadicUnitBall
