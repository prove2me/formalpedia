-- Prove2me | solution 1 for LinearHashingPoissonesque.ExpectedLoads.variational_expectation
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T22:14:52.115367+00:00
-- url     : https://prove2.me/submissions/dea8502b-aff5-4d88-8463-0cab2de0d8ce

import Mathlib
import Definitions.Def_LinMaxLoad_avgLin
import Definitions.Def_LinearHashingPoissonesque_ExpectedLoads_LogPotential
import Definitions.Def_LinearHashingPoissonesque_ExpectedLoads_ExtremeLoads
import Definitions.Def_LinearHashingPoissonesque_ExpectedLoads_VariationalBounds
import Theorems.Thm_LinearHashingPoissonesque_ExpectedLoads_potential_poisson
import Theorems.Thm_LinearHashingPoissonesque_ExpectedLoads_extract_load_average

section
set_option autoImplicit false

namespace LinearHashingPoissonesque.Dev.VarExp

lemma avgLin_mono' {E : Type*} [AddCommGroup E] [Module (ZMod 2) E] [Finite E] (r : ℕ)
    (X Y : (E →ₗ[ZMod 2] (Fin r → ZMod 2)) → ℝ) (h : ∀ g, X g ≤ Y g) :
    LinMaxLoad.avgLin (ZMod 2) E r X ≤ LinMaxLoad.avgLin (ZMod 2) E r Y := by
  unfold LinMaxLoad.avgLin
  letI : Fintype (E →ₗ[ZMod 2] (Fin r → ZMod 2)) := Fintype.ofFinite _
  have hc : (0 : ℝ) < (Fintype.card (E →ₗ[ZMod 2] (Fin r → ZMod 2)) : ℝ) := by
    exact_mod_cast Fintype.card_pos
  apply div_le_div_of_nonneg_right _ hc.le
  exact Finset.sum_le_sum (fun g _ => h g)

lemma avgLin_affine {E : Type*} [AddCommGroup E] [Module (ZMod 2) E] [Finite E] (r : ℕ)
    (X : (E →ₗ[ZMod 2] (Fin r → ZMod 2)) → ℝ) (lam μ L : ℝ) :
    LinMaxLoad.avgLin (ZMod 2) E r (fun g => lam * (X g - μ) - L)
      = lam * (LinMaxLoad.avgLin (ZMod 2) E r X - μ) - L := by
  unfold LinMaxLoad.avgLin
  letI : Fintype (E →ₗ[ZMod 2] (Fin r → ZMod 2)) := Fintype.ofFinite _
  have hc : (0 : ℝ) < (Fintype.card (E →ₗ[ZMod 2] (Fin r → ZMod 2)) : ℝ) := by
    exact_mod_cast Fintype.card_pos
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

end LinearHashingPoissonesque.Dev.VarExp

namespace LinearHashingPoissonesque.ExpectedLoads
open LinearHashingPoissonesque.Dev.VarExp in
theorem chk_variational_expectation {u ell m : ℕ} (hu : ell ≤ u) (hell : 1 ≤ ell) (hm : 1 ≤ m)
    (S : Finset (Fin u → ZMod 2)) (hS : S.card = m)
    (r : ℕ) (hr : 1 ≤ r) (hrn : r ≤ 2 ^ ell) (sign : Extreme) :
    variationalLower ((m : ℝ) / (2 : ℝ) ^ ell) (2 ^ ell) r ≤
      LinMaxLoad.avgLin (ZMod 2) (Fin u → ZMod 2) ell
        (fun h => extremeAverage S h r sign) ∧
    LinMaxLoad.avgLin (ZMod 2) (Fin u → ZMod 2) ell
        (fun h => extremeAverage S h r sign) ≤
      variationalUpper ((m : ℝ) / (2 : ℝ) ^ ell) (2 ^ ell) r := by
  set A := LinMaxLoad.avgLin (ZMod 2) (Fin u → ZMod 2) ell
        (fun h => extremeAverage S h r sign) with hA
  set μ : ℝ := (m : ℝ) / (2 : ℝ) ^ ell with hμ
  have key : ∀ lam : ℝ, lam * (A - μ) - Real.log (((2 : ℝ) ^ ell) / (r : ℝ))
      ≤ μ * (Real.exp lam - lam - 1) := by
    intro lam
    have h1 := avgLin_mono' (E := Fin u → ZMod 2) ell
      (fun h => lam * (extremeAverage S h r sign - μ) - Real.log (((2 : ℝ) ^ ell) / (r : ℝ)))
      (fun h => logPotential S h lam) (fun h => by
        have := extract_load_average hu hell r hr hrn S h lam sign
        rw [hS] at this
        exact this)
    rw [avgLin_affine] at h1
    exact h1.trans (potential_poisson hu hell hm S hS lam)
  have hn : (((2 ^ ell : ℕ)) : ℝ) = (2 : ℝ) ^ ell := by push_cast; rfl
  have hval : ∀ lam : ℝ, variationalValue μ (2 ^ ell) r lam
      = (μ * (Real.exp lam - 1) + Real.log (((2 : ℝ) ^ ell) / (r : ℝ))) / lam := by
    intro lam; unfold variationalValue; rw [hn]
  constructor
  · apply csSup_le
    · exact ⟨_, -1, by norm_num, rfl⟩
    · rintro z ⟨lam, hl, rfl⟩
      rw [hval, div_le_iff_of_neg hl]
      have := key lam
      nlinarith
  · apply le_csInf
    · exact ⟨_, 1, by norm_num, rfl⟩
    · rintro z ⟨lam, hl, rfl⟩
      rw [hval, le_div_iff₀ hl]
      have := key lam
      nlinarith
end LinearHashingPoissonesque.ExpectedLoads
end

theorem solution : type_of% @LinearHashingPoissonesque.ExpectedLoads.chk_variational_expectation := @LinearHashingPoissonesque.ExpectedLoads.chk_variational_expectation
