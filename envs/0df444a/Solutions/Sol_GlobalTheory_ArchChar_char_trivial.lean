-- Prove2me | solution 1 for GlobalTheory.ArchChar.char_trivial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:53:09.568437+00:00
-- url     : https://prove2.me/submissions/7ad46b65-9ab2-4a89-bf0a-f4b9eff0f1e3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ContinuousCharUnitsComplexStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_CharConstOnTranslatesTrivial
import Theorems.Thm_GlobalTheory_T_continuous_units_complex_hom_eq_exp_mul_arg_pow


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open GlobalTheory GlobalTheory.ArchChar
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.ArchChar
theorem _root_.solution (e : ℂˣ →* ℂˣ) (he : Continuous e) (θ : ℂ) (hθ : θ.im ≠ 0) (C : ℝ)
    (hpos : ∀ (ρ : ℝ) (h : 0 < ρ), e (Units.mk0 _ (ofReal_ne h)) = 1)
    (hnear : ∀ R : ℝ, ∃ t : ℝ, |t - R| ≤ C ∧ e (Units.mk0 _ (add_ne hθ t)) = 1) : e = 1 := by
  obtain ⟨s, n, hform⟩ := GlobalTheory.T.continuous_units_complex_hom_eq_exp_mul_arg_pow e he
  have hs0 : ∀ x : ℝ, Complex.exp (s * x) = 1 := by
    intro x
    have h := hform (Units.mk0 _ (ofReal_ne (Real.exp_pos x)))
    rw [hpos _ (Real.exp_pos x)] at h
    simp at h
    exact h.symm
  have hs : s = 0 := by
    by_contra hsne
    obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.1 (hs0 (1 / (‖s‖ + 1)))
    have hpos' : (0 : ℝ) < ‖s‖ + 1 := by positivity
    have hnorm : ‖s * ((1 / (‖s‖ + 1) : ℝ) : ℂ)‖ < 1 := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
      rw [show ‖s‖ * (1 / (‖s‖ + 1)) = ‖s‖ / (‖s‖ + 1) by ring, div_lt_one hpos']
      linarith
    have hk0 : k = 0 := by
      by_contra hk0
      rw [hk] at hnorm
      have hn2 : ‖(k : ℂ) * (2 * Real.pi * Complex.I)‖ = |(k : ℝ)| * (2 * Real.pi) := by
        rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_intCast]
        simp [abs_of_pos Real.pi_pos]
      have hk1 : (1 : ℝ) ≤ |(k : ℝ)| := by exact_mod_cast Int.one_le_abs hk0
      rw [hn2] at hnorm
      nlinarith [Real.pi_gt_three]
    rw [hk0] at hk
    simp at hk
    rcases hk with h | h
    · exact hsne h
    · exact (by exact_mod_cast hpos'.ne' : ((‖s‖ : ℂ) + 1) ≠ 0) h
  subst hs
  have hform' : ∀ z : ℂˣ, (e z : ℂ) = ((z : ℂ) / (‖(z : ℂ)‖ : ℂ)) ^ n := by
    intro z
    rw [hform]
    simp
  by_cases hn : n = 0
  · refine MonoidHom.ext fun z => ?_
    ext
    rw [hform', hn, zpow_zero]
    simp
  · exfalso
    let u : ℝ → ℂ := fun t => ((t : ℂ) + θ) / (‖(t : ℂ) + θ‖ : ℂ)
    have uinj : ∀ t t' : ℝ, u t = u t' → t = t' := by
      intro t t' h
      have hA : ((t : ℂ) + θ) ≠ 0 := add_ne hθ t
      have hB : ((t' : ℂ) + θ) ≠ 0 := add_ne hθ t'
      have hnA : (‖(t : ℂ) + θ‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_pos_iff.2 hA).ne'
      have hnB : (‖(t' : ℂ) + θ‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_pos_iff.2 hB).ne'
      simp only [u] at h
      rw [div_eq_div_iff hnA hnB] at h
      have him := congrArg Complex.im h
      simp at him
      have hnorm : ‖(t' : ℂ) + θ‖ = ‖(t : ℂ) + θ‖ := him.resolve_right hθ
      rw [hnorm] at h
      have h' := mul_right_cancel₀ hnA h
      have hre := congrArg Complex.re h'
      simpa using hre
    have hk : 0 < n.natAbs := Int.natAbs_pos.2 hn
    have hS : {t : ℝ | u t ^ n.natAbs = 1}.Finite := by
      have hfin : {z : ℂ | z ^ n.natAbs = 1}.Finite := by
        apply (Polynomial.nthRoots n.natAbs (1 : ℂ)).toFinset.finite_toSet.subset
        intro z hz
        simpa [Polynomial.mem_nthRoots hk] using hz
      exact hfin.preimage (fun t _ t' _ h => uinj t t' h)
    obtain ⟨M, hM⟩ := hS.bddAbove
    obtain ⟨t, ht, he1⟩ := hnear (M + C + 1)
    have hmem : t ∈ {t : ℝ | u t ^ n.natAbs = 1} := by
      have h := congrArg Units.val he1
      rw [hform'] at h
      simp only [Units.val_mk0, Units.val_one] at h
      show u t ^ n.natAbs = 1
      rcases Int.natAbs_eq n with h' | h'
      · rw [h', zpow_natCast] at h
        exact h
      · rw [h', zpow_neg, zpow_natCast, inv_eq_one] at h
        exact h
    have htM := hM hmem
    rw [abs_le] at ht
    linarith [ht.1]
end GlobalTheory.ArchChar
