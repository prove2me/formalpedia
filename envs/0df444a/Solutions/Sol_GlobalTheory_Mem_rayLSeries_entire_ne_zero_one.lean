-- Prove2me | solution 1 for GlobalTheory.Mem.rayLSeries_entire_ne_zero_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:21:44.229041+00:00
-- url     : https://prove2.me/submissions/d78af425-4fc1-41ce-bacb-2e877797683e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_NonemptyRayDataOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RayClassPartialZetaContinuationStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_DedekindZetaFactorizationRayStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RayLNonvanishingAtOne
import Theorems.Thm_GlobalTheory_Mem_exists_entire_div_sub_one
import Theorems.Thm_GlobalTheory_Mem_RayData_LSeries_coef_eq_sum
import Theorems.Thm_GlobalTheory_Mem_PosDirichlet_mul
import Theorems.Thm_GlobalTheory_T_dedekind_zeta_factorization_ray
import Theorems.Thm_GlobalTheory_T_ray_class_partial_zeta_continuation


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.Mem Complex
open scoped ComplexOrder
open GlobalTheory GlobalTheory.Mem
namespace GlobalTheory.Mem
theorem _root_.solution : ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K], Module.finrank ℚ K = 2 → ∀ (M : ℕ), 2 ≤ M → ∀ (D : RayData K M) (χ : D.G →* ℂˣ), χ ≠ 1 → ∃ L : ℂ → ℂ, Differentiable ℂ L ∧ L 1 ≠ 0 ∧ ∀ s : ℂ, 1 < s.re → L s = LSeries (D.coef χ) s := by
  intro K _ _ _ hK M hM D χ₀ hχ₀
  classical
  obtain ⟨ρ, -, hZ⟩ := GlobalTheory.T.ray_class_partial_zeta_continuation K hK M hM D
  choose Z hZd hZ1 hZm hZs using hZ
  let Y : (D.G →* ℂˣ) → ℂ → ℂ := fun χ s => ∑ c, (χ c : ℂ) * Z c s
  have hYd : ∀ χ, Differentiable ℂ (Y χ) := fun χ =>
    Differentiable.fun_sum fun c _ => (hZd c).const_mul _
  have hYm : ∀ χ, Y χ (-1) = 0 := fun χ => by simp [Y, hZm]
  have hYs : ∀ χ s, 1 < s.re → Y χ s = (s - 1) * LSeries (D.coef χ) s := by
    intro χ s hs
    rw [D.LSeries_coef_eq_sum χ s fun c => (hZs c s hs).1, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [(hZs c s hs).2]; ring
  have hY1 : ∀ χ, χ ≠ 1 → Y χ 1 = 0 := by
    intro χ hχ
    have h0 : ∑ c, (χ c : ℂ) = 0 := by
      have := sum_hom_units_eq_zero ((Units.coeHom ℂ).comp χ) (by
        intro h
        apply hχ
        ext c
        simpa using DFunLike.congr_fun h c)
      simpa using this
    simp only [Y, hZ1]
    rw [← Finset.sum_mul, h0, zero_mul]
  have hL : ∀ χ : D.G →* ℂˣ, ∃ L : ℂ → ℂ, χ ≠ 1 →
      Differentiable ℂ L ∧ ∀ s : ℂ, 1 < s.re → L s = LSeries (D.coef χ) s := by
    intro χ
    by_cases hχ : χ = 1
    · exact ⟨0, fun h => absurd hχ h⟩
    obtain ⟨g, hg, hg'⟩ := exists_entire_div_sub_one (hYd χ) (hY1 χ hχ)
    refine ⟨g, fun _ => ⟨hg, fun s hs => ?_⟩⟩
    have hs1 : s - 1 ≠ 0 := by
      rw [sub_ne_zero]; rintro rfl; simp at hs
    exact mul_left_cancel₀ hs1 ((hg' s).symm.trans (hYs χ s hs))
  choose L hL using hL
  refine ⟨L χ₀, (hL χ₀ hχ₀).1, fun h0 => ?_, (hL χ₀ hχ₀).2⟩
  obtain ⟨g, hg, hg'⟩ := exists_entire_div_sub_one (hL χ₀ hχ₀).1 h0
  haveI : NeZero ((Monoid.exponent D.G : ℕ) : ℂ) := ⟨by exact_mod_cast Monoid.exponent_ne_zero_of_finite⟩
  haveI : Finite (D.G →* ℂˣ) := by
    obtain ⟨e⟩ := CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity D.G ℂ
    exact Finite.of_equiv _ e.toEquiv.symm
  haveI : Fintype (D.G →* ℂˣ) := Fintype.ofFinite _
  obtain ⟨b, hb0, hb1, hba, hbs⟩ := GlobalTheory.T.dedekind_zeta_factorization_ray K M hM D
  let F : ℂ → ℂ := fun s => Y 1 s * (g s * ∏ χ ∈ (Finset.univ.erase 1).erase χ₀, L χ s)
  have hFd : Differentiable ℂ F := by
    refine (hYd 1).mul (hg.mul ?_)
    refine Differentiable.fun_finset_prod fun χ hχ => (hL χ ?_).1
    exact Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hχ)
  have hFs : {s : ℂ | (1 : ℝ) < s.re}.EqOn F (LSeries b) := by
    intro s hs
    have hs' : 1 < s.re := hs
    rw [hbs s hs', ← Finset.mul_prod_erase _ _ (Finset.mem_univ (1 : D.G →* ℂˣ)),
      ← Finset.mul_prod_erase _ _ (Finset.mem_erase.2 ⟨hχ₀, Finset.mem_univ χ₀⟩),
      ← (hL χ₀ hχ₀).2 s hs', hg' s]
    simp only [F]
    rw [hYs 1 s hs', Finset.prod_congr rfl fun χ hχ =>
      (hL χ (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hχ))).2 s hs']
    ring
  have hpos := LSeries.positive_of_differentiable_of_eqOn hb0 hb1 hFd (x := 1)
    (by exact_mod_cast hba) hFs (-1)
  have : F ((-1 : ℝ) : ℂ) = 0 := by
    simp [F, hYm]
  rw [this] at hpos
  exact lt_irrefl _ hpos
end GlobalTheory.Mem
