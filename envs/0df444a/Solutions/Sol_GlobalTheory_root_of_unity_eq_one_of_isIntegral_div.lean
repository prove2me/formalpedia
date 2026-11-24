-- Prove2me | solution 1 for GlobalTheory.root_of_unity_eq_one_of_isIntegral_div
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:32:48.9275+00:00
-- url     : https://prove2.me/submissions/fa24ecae-7f89-4923-893c-350829452fb5

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_UnFree
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_RootOfUnityEqOneOfConjCongruence

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj
open scoped Matrix
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {E : Type} [Field E] [NumberField E] {M n : ℕ}
    (hM : 3 ≤ M) (hn : 0 < n) {u : E} (hu : u ^ n = 1) (h : IsIntegral ℤ ((u - 1) / M)) :
    u = 1 := by
  have hM3 : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have hM0 : (M : E) ≠ 0 := by exact_mod_cast (by omega : M ≠ 0)
  have hlt : ∀ φ : E →+* ℂ, ‖φ ((u - 1) / M)‖ < 1 := by
    intro φ
    have h1 : ‖φ u‖ = 1 := by
      have : ‖φ u‖ ^ n = 1 := by rw [← norm_pow, ← map_pow, hu, map_one, norm_one]
      exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 this
    have h2 : ‖φ u - 1‖ ≤ 2 := by
      have := norm_sub_le (φ u) 1
      rw [h1, norm_one] at this
      linarith
    rw [map_div₀, map_sub, map_one, map_natCast, norm_div, Complex.norm_natCast,
      div_lt_one (by linarith)]
    linarith
  by_contra hne
  have hx : (u - 1) / M ≠ 0 := div_ne_zero (sub_ne_zero.2 hne) hM0
  obtain ⟨k, hk, hk1⟩ := NumberField.Embeddings.pow_eq_one_of_norm_le_one E ℂ hx h
    fun φ => (hlt φ).le
  obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have h3 : ‖φ ((u - 1) / M)‖ ^ k = 1 := by rw [← norm_pow, ← map_pow, hk1, map_one, norm_one]
  exact (hlt φ).ne ((pow_eq_one_iff_of_nonneg (norm_nonneg _) hk.ne').1 h3)
end GlobalTheory
