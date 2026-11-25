-- Prove2me | solution 1 for GlobalTheory.DetIdeal.det_ideal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:16:14.441284+00:00
-- url     : https://prove2.me/submissions/20ea867a-9ffc-454f-bbd9-372d44b1c1c0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FinrankEqOfInjectiveOfSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DetMulVolMulConj
import Theorems.Thm_GlobalTheory_DetIdeal_exists_denominator
import Theorems.Thm_GlobalTheory_DetIdeal_exists_det_ne_zero
import Theorems.Thm_GlobalTheory_DetIdeal_det_mul_vol_mul_conj
import Theorems.Thm_GlobalTheory_HermModel_rank_integral_selfDual


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.DetIdeal
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace GlobalTheory.DetIdeal
theorem _root_.solution (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D D' : Datum H) (r : ℕ)
    (ξ : E) (Gm : Matrix (Fin r) (Fin r) E) (φ : D.La →ₗ[𝓞 E] (Fin r → E)) (Gm' : Matrix (Fin r) (Fin r) E)
    (φ' : D'.La →ₗ[𝓞 E] (Fin r → E)) (hξ : FD.cc ξ = -ξ)
    (h : Function.Injective φ ∧ Submodule.span E (Set.range φ) = ⊤ ∧
      (∀ a b, FD.cc (Gm a b) = Gm b a) ∧ Gm.det ≠ 0 ∧
      ∀ x y, ((D.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (ξ * FD.herm Gm (φ x) (φ y)))
    (h' : Function.Injective φ' ∧ Submodule.span E (Set.range φ') = ⊤ ∧
      (∀ a b, FD.cc (Gm' a b) = Gm' b a) ∧ Gm'.det ≠ 0 ∧
      ∀ x y, ((D'.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (ξ * FD.herm Gm' (φ' x) (φ' y))) :
    ∃ I J : Ideal (𝓞 E), I ≠ ⊥ ∧ J ≠ ⊥ ∧ FractionalIdeal.spanSingleton (𝓞 E)⁰ (Gm'.det / Gm.det) *
      ((I * I.map (H.bar : 𝓞 E →+* 𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) =
      ((J * J.map (H.bar : 𝓞 E →+* 𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · refine ⟨⊤, ⊤, top_ne_bot, top_ne_bot, ?_⟩
    simp
  have hξ0 : ξ ≠ 0 := by
    intro h0
    obtain ⟨-, hspan, -, -, hEF⟩ := h
    obtain ⟨Y, hY, hYd⟩ := exists_det_ne_zero _ hspan
    obtain ⟨z, hz⟩ := hY ⟨0, hr⟩
    have hz0 : z = 0 := by
      apply D.unimod.1
      ext y
      have := hEF z y
      rw [h0, zero_mul, map_zero] at this
      simpa using this
    rw [hz0, map_zero] at hz
    exact hYd (Matrix.det_eq_zero_of_row_eq_zero ⟨0, hr⟩ fun j => by rw [← hz]; rfl)
  obtain ⟨-, hfg, -, -⟩ := HermModel.rank_integral_selfDual E H D r ξ Gm φ hξ h
  obtain ⟨-, hfg', -, -⟩ := HermModel.rank_integral_selfDual E H D' r ξ Gm' φ' hξ h'
  obtain ⟨n, hn, hint⟩ := exists_denominator _ (hfg.sup hfg')
  have hn0 : n ≠ 0 := nonZeroDivisors.ne_zero hn
  obtain ⟨J, hJ, hJe⟩ := det_mul_vol_mul_conj H D ξ Gm φ hξ hξ0 h n hn0
    fun z => hint _ (Submodule.mem_sup_left ⟨z, rfl⟩)
  obtain ⟨I, hI, hIe⟩ := det_mul_vol_mul_conj H D' ξ Gm' φ' hξ hξ0 h' n hn0
    fun z => hint _ (Submodule.mem_sup_right ⟨z, rfl⟩)
  refine ⟨I, J, hI, hJ, ?_⟩
  have hnE : (n : E) ≠ 0 := by exact_mod_cast hn0
  have hcn : FD.cc (n : E) ≠ 0 := by simpa [FD.cc] using hn0
  have hk : (ξ / ((n : E) * FD.cc (n : E))) ^ r * Gm.det ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (div_ne_zero hξ0 (mul_ne_zero hnE hcn))) h.2.2.2.1
  apply mul_left_cancel₀ (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hk :
    FractionalIdeal.spanSingleton (𝓞 E)⁰ _ ≠ 0)
  rw [hJe, ← hIe, ← mul_assoc, FractionalIdeal.spanSingleton_mul_spanSingleton, mul_assoc,
    mul_div_cancel₀ _ h.2.2.2.1]
end GlobalTheory.DetIdeal
