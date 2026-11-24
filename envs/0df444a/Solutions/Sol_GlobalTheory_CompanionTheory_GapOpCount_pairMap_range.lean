-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.GapOpCount.pairMap_range
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:33:19.451073+00:00
-- url     : https://prove2.me/submissions/a971f7ff-44c6-4ea1-bb58-f04060d99bd2

import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MemRiemannRochSpaceIffRegularAtEverywhere
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardTwoAffineHyperplanes

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Classical PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.GLFirstBasisOrbit
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.GapOpCount
namespace GlobalTheory.CompanionTheory.GapOpCount
theorem _root_.solution {k : Type} [Field k] {n : ℕ} (a b : Fin (n + 1) → k)
    (ha : a ≠ 0) (hb : ∀ s : k, b ≠ s • a) : LinearMap.range (pairMap a b) = ⊤ := by
  by_contra hne
  obtain ⟨φ, hφ, hle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hne)
  have hform : ∀ u v : k, φ (u, v) = u * φ (1, 0) + v * φ (0, 1) := by
    intro u v
    have h : ((u, v) : k × k) = u • ((1, 0) : k × k) + v • ((0, 1) : k × k) := by simp
    rw [h, map_add, map_smul, map_smul]
    simp
  have hzero : (φ (1, 0) • a + φ (0, 1) • b) = 0 := by
    apply dotProduct_eq_zero
    intro x
    have hx : φ (pairMap a b x) = 0 := hle (LinearMap.mem_range_self _ x)
    have hx' : φ (a ⬝ᵥ x, b ⬝ᵥ x) = 0 := hx
    rw [hform] at hx'
    rw [add_dotProduct, smul_dotProduct, smul_dotProduct, smul_eq_mul, smul_eq_mul]
    linear_combination hx'
  by_cases hμ : φ (0, 1) = 0
  · rw [hμ, zero_smul, add_zero] at hzero
    rcases smul_eq_zero.mp hzero with hl | h0
    · apply hφ
      ext p
      · simp [hl]
      · simp [hμ]
    · exact ha h0
  · apply hb (-(φ (0, 1))⁻¹ * φ (1, 0))
    have h1 : φ (0, 1) • b = -(φ (1, 0) • a) := eq_neg_of_add_eq_zero_right hzero
    calc b = (φ (0, 1))⁻¹ • (φ (0, 1) • b) := by rw [smul_smul, inv_mul_cancel₀ hμ, one_smul]
      _ = (-(φ (0, 1))⁻¹ * φ (1, 0)) • a := by
        rw [h1, smul_neg, smul_smul, neg_mul, neg_smul]
end GlobalTheory.CompanionTheory.GapOpCount
