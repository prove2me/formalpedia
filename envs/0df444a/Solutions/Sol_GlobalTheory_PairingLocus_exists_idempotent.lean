-- Prove2me | solution 1 for GlobalTheory.PairingLocus.exists_idempotent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:19:40.92869+00:00
-- url     : https://prove2.me/submissions/8bba7312-00c3-4ff2-a6f0-2c4bfbad1935

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueWeilIs
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsCommVOfLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsAlternatingSkewNatural
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsClopenOfIsLocallyNoetherian

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.PairingLocus
namespace GlobalTheory.PairingLocus
theorem _root_.solution {R : Type} [CommRing R] {n : ℕ} (hn : IsUnit (n : R)) {u : R} (hu : u ^ n = 1) :
    ∃ e : R, IsIdempotentElem e ∧ ∀ (R' : Type) [CommRing R'] (φ : R →+* R'), φ u = 1 ↔ φ e = 1 := by
  obtain ⟨m, hm⟩ := hn.exists_left_inv
  have h₀ : (∑ i ∈ Finset.range n, u ^ i) * (u - 1) = 0 := by rw [geom_sum_mul, hu, sub_self]
  have h₁ : u * (m * ∑ i ∈ Finset.range n, u ^ i) = m * ∑ i ∈ Finset.range n, u ^ i := by
    linear_combination m * h₀
  have h₂ : ∀ i : ℕ, u ^ i * (m * ∑ i ∈ Finset.range n, u ^ i) = m * ∑ i ∈ Finset.range n, u ^ i := by
    intro i
    induction i with
    | zero => rw [pow_zero, _root_.one_mul]
    | succ i ih => rw [pow_succ, _root_.mul_assoc, h₁, ih]
  refine ⟨m * ∑ i ∈ Finset.range n, u ^ i, ?_, fun R' _ φ => ⟨fun h => ?_, fun h => ?_⟩⟩
  · show _ * _ = _
    rw [_root_.mul_assoc, Finset.sum_mul, Finset.sum_congr rfl fun i _ => h₂ i, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul, ← _root_.mul_assoc, hm, _root_.one_mul]
  · have := congrArg φ hm
    simp only [map_mul, map_sum, map_pow, h, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      _root_.mul_one, map_natCast, map_one] at this ⊢
    exact this
  · have := congrArg φ h₁
    rwa [map_mul, h, _root_.mul_one] at this
end GlobalTheory.PairingLocus
