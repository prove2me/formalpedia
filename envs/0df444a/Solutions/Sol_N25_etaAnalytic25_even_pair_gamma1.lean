-- Prove2me | solution 1 for N25.etaAnalytic25_even_pair_gamma1
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:49:23.723202+00:00
-- url     : https://prove2.me/submissions/bda23f01-dd72-426d-94fd-52b8c779f861

import Mathlib
import Definitions.Def_N25_UnitAnalytic
import Theorems.Thm_N25_siegelDilation_gamma0
import Definitions.Def_ModularCurve_SiegelFunction
import Theorems.Thm_N25_siegelFun_first_index_period_two_levels

set_option autoImplicit false

namespace N25

/-- Even residue pairs with square sum divisible by fifty transform with one
common square multiplier under Gamma1, before taking an unpowered ratio. -/
theorem _root_.solution
    (A : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (hA : A ∈ CongruenceSubgroup.Gamma1 25) :
    ∃ μ : ℂ, μ^12 = 1 ∧ ∀ (g h : ℕ), Even g → Even h →
      50 ∣ g^2+h^2 → ∀ τ : UpperHalfPlane,
        etaAnalytic25 g (A • τ) * etaAnalytic25 h (A • τ) =
          μ^2 * (etaAnalytic25 g τ * etaAnalytic25 h τ) := by
  let a : ℤ := (A : Matrix (Fin 2) (Fin 2) ℤ) 0 0
  let b : ℤ := (A : Matrix (Fin 2) (Fin 2) ℤ) 0 1
  obtain ⟨ha, _, hc⟩ := (CongruenceSubgroup.Gamma1_mem 25 A).mp hA
  have hdiv : (25 : ℤ) ∣ (A : Matrix (Fin 2) (Fin 2) ℤ) 1 0 := by
    simpa only [ZMod.intCast_zmod_eq_zero_iff_dvd, Nat.cast_ofNat] using hc
  have hadiv : (25 : ℤ) ∣ a-1 := by
    have he : ((a-1 : ℤ) : ZMod 25) = 0 := by
      simpa only [Int.cast_sub, Int.cast_one, sub_eq_zero] using ha
    simpa only [ZMod.intCast_zmod_eq_zero_iff_dvd, Nat.cast_ofNat] using he
  obtain ⟨m, hm⟩ := hadiv
  have ham : a = 1+25*m := by omega
  obtain ⟨μ, hμ, htrans⟩ := siegelDilation_gamma0 A hdiv
  refine ⟨μ, hμ, ?_⟩
  have hfix (g : ℕ) (hg : Even g) (τ : UpperHalfPlane) :
      -ModularCurve.siegelFun 25 (a*(g : ℤ)) 0 (25*(τ : ℂ)) = etaAnalytic25 g τ := by
    obtain ⟨u, hu⟩ := hg
    let τ25 : UpperHalfPlane := ⟨25*(τ : ℂ), by
      simpa using (mul_pos (by norm_num : (0 : ℝ) < 25) τ.im_pos)⟩
    have hg' : (g : ℤ) = 2*(u : ℤ) := by omega
    have hindex : a*(g : ℤ) = (g : ℤ) + 2*(m*(u : ℤ))*(25 : ℤ) := by
      rw [ham, hg']
      ring
    rw [hindex]
    simpa only [etaAnalytic25, Nat.cast_ofNat] using
      congrArg Neg.neg (siegelFun_first_index_period_two_levels 25 (g : ℤ) (m*(u : ℤ)) τ25)
  intro g h hg hh hsq τ
  let C (t : ℕ) : ℂ := Real.pi * Complex.I *
    ((a : ℂ)*(b : ℂ)*(t : ℂ)^2/25 - (b : ℂ)*(t : ℂ))
  have tg := htrans (g : ℤ) τ
  have th := htrans (h : ℤ) τ
  change etaAnalytic25 g (A • τ) = μ * Complex.exp (C g) *
    (-ModularCurve.siegelFun 25 (a*(g : ℤ)) 0 (25*(τ : ℂ))) at tg
  change etaAnalytic25 h (A • τ) = μ * Complex.exp (C h) *
    (-ModularCurve.siegelFun 25 (a*(h : ℤ)) 0 (25*(τ : ℂ))) at th
  rw [hfix g hg τ] at tg
  rw [hfix h hh τ] at th
  have hphase : Complex.exp (C g) * Complex.exp (C h) = 1 := by
    rw [← Complex.exp_add]
    obtain ⟨u, hu⟩ := hg
    obtain ⟨v, hv⟩ := hh
    obtain ⟨t, ht⟩ := hsq
    have hsum : (g : ℂ)+(h : ℂ) = 2*((u : ℂ)+(v : ℂ)) := by
      exact_mod_cast (show g+h = 2*(u+v) by omega)
    have hsquare : (g : ℂ)^2+(h : ℂ)^2 = 50*(t : ℂ) := by exact_mod_cast ht
    have he : C g+C h =
        ((a*b*(t : ℤ)-b*((u : ℤ)+(v : ℤ)) : ℤ) : ℂ) * (2*Real.pi*Complex.I) := by
      dsimp only [C]
      push_cast
      linear_combination (Real.pi*Complex.I*(a : ℂ)*(b : ℂ)/25)*hsquare -
        (Real.pi*Complex.I*(b : ℂ))*hsum
    rw [he]
    exact Complex.exp_int_mul_two_pi_mul_I _
  rw [tg, th]
  calc
    (μ * Complex.exp (C g) * etaAnalytic25 g τ) *
        (μ * Complex.exp (C h) * etaAnalytic25 h τ) =
      μ^2 * (Complex.exp (C g)*Complex.exp (C h)) *
        (etaAnalytic25 g τ * etaAnalytic25 h τ) := by ring
    _ = μ^2 * (etaAnalytic25 g τ * etaAnalytic25 h τ) := by rw [hphase, mul_one]

end N25
