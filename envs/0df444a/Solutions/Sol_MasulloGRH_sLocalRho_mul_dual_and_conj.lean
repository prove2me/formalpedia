-- Prove2me | solution 1 for MasulloGRH.sLocalRho_mul_dual_and_conj
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T18:34:13.690165+00:00
-- url     : https://prove2.me/submissions/7bae8f53-94f6-4a6b-b372-ab03de1ced49
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_MasulloGRH_SLocalZetaIntegrals
import Theorems.Thm_MasulloGRH_sZetaIntegral_functional_equation_and_continuation
import Theorems.Thm_MasulloGRH_sLocalFourier_schwartzBruhat_equiv
import Theorems.Thm_MasulloGRH_sMultiplicativeTamagawa_isHaarMeasure_and_rectangle
import Theorems.Thm_MasulloGRH_sAdditiveTamagawa_selfDual_sStdCharacter
import Theorems.Thm_MasulloGRH_sZetaIntegral_exists_real_ne_zero

open MeasureTheory NumberField IsDedekindDomain

set_option autoImplicit false

namespace Sol_MasulloGRH_sLocalRho_mul_dual_and_conj

open MasulloGRH

variable {F : Type*} [Field F] [NumberField F] {Sf : Finset (HeightOneSpectrum (𝓞 F))}

theorem coord_inf_ne_zero (g : SIdeleGroup F Sf) (w : InfinitePlace F) :
    (g : SAdeleRing F Sf).1 w ≠ 0 := by
  have h := congrArg (fun x : SAdeleRing F Sf => x.1 w) g.mul_inv
  simp only [Prod.fst_mul, Prod.fst_one] at h
  exact left_ne_zero_of_mul_eq_one h

theorem coord_fin_ne_zero (g : SIdeleGroup F Sf) (v : Sf) :
    (g : SAdeleRing F Sf).2 v ≠ 0 := by
  have h := congrArg (fun x : SAdeleRing F Sf => x.2 v) g.mul_inv
  simp only [Prod.snd_mul, Prod.snd_one] at h
  exact left_ne_zero_of_mul_eq_one h

theorem sIdeleNorm_pos' (g : SIdeleGroup F Sf) : 0 < sIdeleNorm Sf g := by
  unfold sIdeleNorm
  exact mul_pos (Finset.prod_pos fun w _ => pow_pos (norm_pos_iff.mpr (coord_inf_ne_zero g w)) _)
    (Finset.prod_pos fun v _ => norm_pos_iff.mpr (coord_fin_ne_zero g v))

theorem sIdeleNorm_mul' (g h : SIdeleGroup F Sf) :
    sIdeleNorm Sf (g * h) = sIdeleNorm Sf g * sIdeleNorm Sf h := by
  have h1 : ∀ w : InfinitePlace F, ((g * h : SIdeleGroup F Sf) : SAdeleRing F Sf).1 w =
      (g : SAdeleRing F Sf).1 w * (h : SAdeleRing F Sf).1 w := fun w => rfl
  have h2 : ∀ v : Sf, ((g * h : SIdeleGroup F Sf) : SAdeleRing F Sf).2 v =
      (g : SAdeleRing F Sf).2 v * (h : SAdeleRing F Sf).2 v := fun v => rfl
  unfold sIdeleNorm
  simp only [h1, h2, norm_mul, mul_pow, Finset.prod_mul_distrib]
  ring

theorem continuous_sIdeleNorm' : Continuous (sIdeleNorm (F := F) Sf) := by
  have h1 : Continuous fun g : SIdeleGroup F Sf => (g : SAdeleRing F Sf) := Units.continuous_val
  show Continuous fun g : SIdeleGroup F Sf =>
    (∏ w : InfinitePlace F, ‖(g : SAdeleRing F Sf).1 w‖ ^ w.mult) * ∏ v : Sf, ‖(g : SAdeleRing F Sf).2 v‖
  refine Continuous.mul (continuous_finsetProd _ fun w _ => ?_)
    (continuous_finsetProd _ fun v _ => ?_)
  · exact ((continuous_apply w).comp (continuous_fst.comp h1)).norm.pow _
  · exact ((continuous_apply v).comp (continuous_snd.comp h1)).norm

theorem sIdeleNorm_neg_one : sIdeleNorm Sf (-1 : SIdeleGroup F Sf) = 1 := by
  unfold sIdeleNorm
  have h1 : ∀ w : InfinitePlace F,
      ((-1 : SIdeleGroup F Sf) : SAdeleRing F Sf).1 w = -1 := fun w => rfl
  have h2 : ∀ v : Sf, ((-1 : SIdeleGroup F Sf) : SAdeleRing F Sf).2 v = -1 := fun v => rfl
  simp only [h1, h2, norm_neg, norm_one, one_pow, Finset.prod_const_one, mul_one]

theorem dual_isQC {c : SIdeleGroup F Sf → ℂ} (hc : IsSIdeleQuasiCharacter Sf c) :
    IsSIdeleQuasiCharacter Sf (sQuasiDual Sf c) := by
  obtain ⟨hcont, hmul, hne⟩ := hc
  refine ⟨?_, ?_, ?_⟩
  · unfold sQuasiDual
    exact (Complex.continuous_ofReal.comp continuous_sIdeleNorm').mul (hcont.inv₀ hne)
  · intro g h
    unfold sQuasiDual
    rw [hmul, sIdeleNorm_mul', Complex.ofReal_mul, mul_inv]
    ring
  · intro g
    unfold sQuasiDual
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (sIdeleNorm_pos' g).ne') (inv_ne_zero (hne g))

theorem dual_norm {c : SIdeleGroup F Sf → ℂ} {σ : ℝ}
    (hσ : ∀ g : SIdeleGroup F Sf, ‖c g‖ = sIdeleNorm Sf g ^ σ) (g : SIdeleGroup F Sf) :
    ‖sQuasiDual Sf c g‖ = sIdeleNorm Sf g ^ (1 - σ) := by
  unfold sQuasiDual
  rw [norm_mul, norm_inv, hσ, Complex.norm_of_nonneg (sIdeleNorm_pos' g).le,
    Real.rpow_sub (sIdeleNorm_pos' g), Real.rpow_one, div_eq_mul_inv]

theorem conj_isQC {c : SIdeleGroup F Sf → ℂ} (hc : IsSIdeleQuasiCharacter Sf c) :
    IsSIdeleQuasiCharacter Sf (fun g => (starRingEnd ℂ) (c g)) := by
  obtain ⟨hcont, hmul, hne⟩ := hc
  refine ⟨Complex.continuous_conj.comp hcont, fun g h => ?_, fun g => ?_⟩
  · simp only [hmul, map_mul]
  · exact (map_ne_zero _).mpr (hne g)

theorem dual_dual {c : SIdeleGroup F Sf → ℂ} :
    sQuasiDual Sf (sQuasiDual Sf c) = c := by
  funext g
  unfold sQuasiDual
  have h : ((sIdeleNorm Sf g : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (sIdeleNorm_pos' g).ne'
  rw [mul_inv, inv_inv, mul_inv_cancel_left₀ h]

theorem dual_conj (c : SIdeleGroup F Sf → ℂ) :
    sQuasiDual Sf (fun g => (starRingEnd ℂ) (c g)) =
      fun g => (starRingEnd ℂ) (sQuasiDual Sf c g) := by
  funext g
  unfold sQuasiDual
  rw [map_mul, map_inv₀, Complex.conj_ofReal]

theorem twist_zero (c : SIdeleGroup F Sf → ℂ) : sQuasiTwist Sf c 0 = c := by
  funext g
  unfold sQuasiTwist
  rw [Complex.cpow_zero, mul_one]

/-- The defining property of `sLocalRho`, from the `S`-local functional equation. -/
theorem rho_spec {c : SIdeleGroup F Sf → ℂ} (hc : IsSIdeleQuasiCharacter Sf c) {σ : ℝ}
    (hσ : ∀ g : SIdeleGroup F Sf, ‖c g‖ = sIdeleNorm Sf g ^ σ) (h0 : 0 < σ) (h1 : σ < 1) :
    ∀ f : SAdelicSchwartz F Sf,
      sZetaIntegral f c =
        sLocalRho Sf c * sZetaIntegralFun Sf (sLocalFourier Sf f.eval) (sQuasiDual Sf c) := by
  classical
  obtain ⟨ρ, -, -, hFE, -⟩ := sZetaIntegral_functional_equation_and_continuation F Sf c hc σ hσ
  have hex : ∃ r : ℂ, ∀ f : SAdelicSchwartz F Sf,
      sZetaIntegral f c = r * sZetaIntegralFun Sf (sLocalFourier Sf f.eval) (sQuasiDual Sf c) := by
    refine ⟨ρ 0, fun f => ?_⟩
    have h := hFE f 0 (by simpa using h0) (by simpa using h1)
    rwa [twist_zero] at h
  unfold sLocalRho
  rw [dif_pos hex]
  exact hex.choose_spec

/-- Substitution `g ↦ -g` in a zeta integral (invariance of the Haar measure `μ_S`). -/
theorem zeta_neg {c : SIdeleGroup F Sf → ℂ} (hc : IsSIdeleQuasiCharacter Sf c)
    (φ : SAdeleRing F Sf → ℂ) :
    sZetaIntegralFun Sf (fun x => φ (-x)) c = c (-1) * sZetaIntegralFun Sf φ c := by
  have := (sMultiplicativeTamagawa_isHaarMeasure_and_rectangle F Sf).1
  unfold sZetaIntegralFun
  have h := integral_mul_left_eq_self (μ := sMultiplicativeTamagawa F Sf)
    (fun g : SIdeleGroup F Sf => φ (-(g : SAdeleRing F Sf)) * c g) (-1)
  rw [← h, ← integral_const_mul]
  congr 1
  funext g
  rw [hc.2.1]
  simp only [Units.val_neg, neg_one_mul, neg_neg]
  ring

/-- `ψ(-z) = conj ψ(z)` for the standard character. -/
theorem std_neg (z : SAdeleRing F Sf) :
    sStdCharacter Sf (-z) = (starRingEnd ℂ) (sStdCharacter Sf z) := by
  obtain ⟨hadd, hnorm, -, -⟩ := sAdditiveTamagawa_selfDual_sStdCharacter F Sf
  have h0 : sStdCharacter Sf 0 = 1 := by
    have h := hadd 0 0
    rw [add_zero] at h
    have hne : sStdCharacter Sf 0 ≠ 0 := by
      intro h'; have := hnorm 0; rw [h', norm_zero] at this; exact zero_ne_one this
    exact (mul_eq_left₀ hne).mp h.symm
  have hne : sStdCharacter Sf z ≠ 0 := by
    intro h'; have := hnorm z; rw [h', norm_zero] at this; exact zero_ne_one this
  have e1 : sStdCharacter Sf z * sStdCharacter Sf (-z) = 1 := by
    rw [← hadd, add_neg_cancel, h0]
  have e2 : sStdCharacter Sf z * (starRingEnd ℂ) (sStdCharacter Sf z) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hnorm]
    norm_num
  exact mul_left_cancel₀ hne (e1.trans e2.symm)

/-- The Fourier transform of a real function satisfies `\hat φ(-y) = conj \hat φ(y)`. -/
theorem fourier_neg_of_real (φ : SAdeleRing F Sf → ℂ)
    (hφ : ∀ x, (starRingEnd ℂ) (φ x) = φ x) (y : SAdeleRing F Sf) :
    sLocalFourier Sf φ (-y) = (starRingEnd ℂ) (sLocalFourier Sf φ y) := by
  unfold sLocalFourier
  rw [← integral_conj]
  congr 1
  funext x
  rw [map_mul, hφ, mul_neg, std_neg]

/-- Conjugating both the function and the character conjugates the zeta integral. -/
theorem zeta_conj (φ : SAdeleRing F Sf → ℂ) (c : SIdeleGroup F Sf → ℂ) :
    sZetaIntegralFun Sf (fun x => (starRingEnd ℂ) (φ x)) (fun g => (starRingEnd ℂ) (c g)) =
      (starRingEnd ℂ) (sZetaIntegralFun Sf φ c) := by
  unfold sZetaIntegralFun
  rw [← integral_conj]
  congr 1
  funext g
  rw [map_mul]

end Sol_MasulloGRH_sLocalRho_mul_dual_and_conj

open MasulloGRH Sol_MasulloGRH_sLocalRho_mul_dual_and_conj

theorem solution
    (F : Type*) [Field F] [NumberField F] (Sf : Finset (HeightOneSpectrum (𝓞 F)))
    (c : SIdeleGroup F Sf → ℂ) (hc : IsSIdeleQuasiCharacter Sf c)
    (σ : ℝ) (hσ : ∀ g : SIdeleGroup F Sf, ‖c g‖ = sIdeleNorm Sf g ^ σ)
    (h0 : 0 < σ) (h1 : σ < 1) :
    (∀ f : SAdelicSchwartz F Sf,
      sZetaIntegral f c =
        sLocalRho Sf c * sZetaIntegralFun Sf (sLocalFourier Sf f.eval) (sQuasiDual Sf c)) ∧
    sLocalRho Sf c * sLocalRho Sf (sQuasiDual Sf c) = c (-1) ∧
    sLocalRho Sf (fun g => (starRingEnd ℂ) (c g)) =
      c (-1) * (starRingEnd ℂ) (sLocalRho Sf c) ∧
    (σ = 1 / 2 → ‖sLocalRho Sf c‖ = 1) := by
  obtain ⟨-, T, hT, hTT⟩ := sLocalFourier_schwartzBruhat_equiv F Sf
  have hdc := dual_isQC hc
  have hdn : ∀ g : SIdeleGroup F Sf, ‖sQuasiDual Sf c g‖ = sIdeleNorm Sf g ^ (1 - σ) :=
    dual_norm hσ
  have hcc := conj_isQC hc
  have hcn : ∀ g : SIdeleGroup F Sf, ‖(starRingEnd ℂ) (c g)‖ = sIdeleNorm Sf g ^ σ := by
    intro g; rw [Complex.norm_conj, hσ]
  have R1 := rho_spec hc hσ h0 h1
  have R2 := rho_spec hdc hdn (by linarith) (by linarith)
  have R3 := rho_spec hcc hcn h0 h1
  -- values of `c` at `-1`
  have hc1 : c 1 = 1 := by
    have h := hc.2.1 1 1
    rw [one_mul] at h
    exact (mul_eq_left₀ (hc.2.2 1)).mp h.symm
  have hm1sq : c (-1) * c (-1) = 1 := by
    rw [← hc.2.1, neg_one_mul, neg_neg, hc1]
  have hm1conj : (starRingEnd ℂ) (c (-1)) = c (-1) := by
    rcases mul_self_eq_one_iff.mp hm1sq with h | h <;> rw [h] <;> simp
  have hdm1 : sQuasiDual Sf c (-1) = c (-1) := by
    unfold sQuasiDual
    rw [sIdeleNorm_neg_one, Complex.ofReal_one, one_mul]
    exact inv_eq_of_mul_eq_one_right hm1sq
  -- a real test function with non-vanishing zeta integral
  obtain ⟨f, hfr, hfne⟩ := sZetaIntegral_exists_real_ne_zero F Sf c hc
  set N := sZetaIntegral f c with hNdef
  set D := sZetaIntegralFun Sf (sLocalFourier Sf f.eval) (sQuasiDual Sf c) with hDdef
  have hN : N = sLocalRho Sf c * D := R1 f
  have hD : D ≠ 0 := fun h => hfne (by rw [hN, h, mul_zero])
  -- item (2)
  have item2 : sLocalRho Sf c * sLocalRho Sf (sQuasiDual Sf c) = c (-1) := by
    have h2 := R2 (T f)
    have hTf : sZetaIntegral (T f) (sQuasiDual Sf c) = D := by
      rw [sZetaIntegral, hT f]
    have hTTf : sLocalFourier Sf (T f).eval = fun x => f.eval (-x) := by
      rw [← hT (T f)]
      funext x
      exact hTT f x
    rw [hTf, hTTf, dual_dual, zeta_neg hc] at h2
    have key : N = (sLocalRho Sf c * sLocalRho Sf (sQuasiDual Sf c) * c (-1)) * N := by
      calc N = sLocalRho Sf c * D := hN
        _ = sLocalRho Sf c * (sLocalRho Sf (sQuasiDual Sf c) * (c (-1) * N)) := by
          rw [h2]; rfl
        _ = _ := by ring
    have h1' : sLocalRho Sf c * sLocalRho Sf (sQuasiDual Sf c) * c (-1) = 1 :=
      (mul_eq_right₀ hfne).mp key.symm
    calc sLocalRho Sf c * sLocalRho Sf (sQuasiDual Sf c)
        = sLocalRho Sf c * sLocalRho Sf (sQuasiDual Sf c) * (c (-1) * c (-1)) := by
          rw [hm1sq, mul_one]
      _ = (sLocalRho Sf c * sLocalRho Sf (sQuasiDual Sf c) * c (-1)) * c (-1) := by ring
      _ = c (-1) := by rw [h1', one_mul]
  -- item (3)
  have item3 : sLocalRho Sf (fun g => (starRingEnd ℂ) (c g)) =
      c (-1) * (starRingEnd ℂ) (sLocalRho Sf c) := by
    have h3 := R3 f
    have hfe : (fun x => (starRingEnd ℂ) (f.eval x)) = f.eval := funext hfr
    have hl : sZetaIntegral f (fun g => (starRingEnd ℂ) (c g)) = (starRingEnd ℂ) N := by
      rw [hNdef, sZetaIntegral, sZetaIntegral, ← zeta_conj, hfe]
    have hfh : sLocalFourier Sf f.eval =
        fun x => (starRingEnd ℂ) (sLocalFourier Sf f.eval (-x)) := by
      funext x
      rw [fourier_neg_of_real f.eval hfr, Complex.conj_conj]
    have hr : sZetaIntegralFun Sf (sLocalFourier Sf f.eval)
        (sQuasiDual Sf (fun g => (starRingEnd ℂ) (c g))) =
        c (-1) * (starRingEnd ℂ) D := by
      rw [dual_conj, hfh, zeta_conj, zeta_neg hdc, hdm1, map_mul, hm1conj]
    rw [hl, hr] at h3
    -- conj N = ρ(c̄) c(-1) conj D, and conj N = conj ρ(c) conj D
    have hcN : (starRingEnd ℂ) N = (starRingEnd ℂ) (sLocalRho Sf c) * (starRingEnd ℂ) D := by
      rw [hN, map_mul]
    have hcD : (starRingEnd ℂ) D ≠ 0 := (map_ne_zero _).mpr hD
    have e : (starRingEnd ℂ) (sLocalRho Sf c) =
        sLocalRho Sf (fun g => (starRingEnd ℂ) (c g)) * c (-1) := by
      apply mul_right_cancel₀ hcD
      rw [← hcN, h3]
      ring
    calc sLocalRho Sf (fun g => (starRingEnd ℂ) (c g))
        = sLocalRho Sf (fun g => (starRingEnd ℂ) (c g)) * (c (-1) * c (-1)) := by
          rw [hm1sq, mul_one]
      _ = c (-1) * (sLocalRho Sf (fun g => (starRingEnd ℂ) (c g)) * c (-1)) := by ring
      _ = _ := by rw [e]
  refine ⟨R1, item2, item3, fun hhalf => ?_⟩
  -- item (4): on `σ = 1/2`, `\hat c = \bar c`
  have hdual : sQuasiDual Sf c = fun g => (starRingEnd ℂ) (c g) := by
    funext g
    unfold sQuasiDual
    have hcg := hc.2.2 g
    have hnorm : ((sIdeleNorm Sf g : ℝ) : ℂ) = c g * (starRingEnd ℂ) (c g) := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hσ, hhalf, ← Real.rpow_natCast,
        ← Real.rpow_mul (sIdeleNorm_pos' g).le]
      norm_num
    rw [hnorm, mul_comm (c g), mul_assoc, mul_inv_cancel₀ hcg, mul_one]
  rw [hdual, item3] at item2
  have hm1ne : c (-1) ≠ 0 := hc.2.2 (-1)
  have hprod : sLocalRho Sf c * (starRingEnd ℂ) (sLocalRho Sf c) = 1 := by
    apply mul_left_cancel₀ hm1ne
    calc c (-1) * (sLocalRho Sf c * (starRingEnd ℂ) (sLocalRho Sf c))
        = sLocalRho Sf c * (c (-1) * (starRingEnd ℂ) (sLocalRho Sf c)) := by ring
      _ = c (-1) * 1 := by rw [item2, mul_one]
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq] at hprod
  have hsq : ‖sLocalRho Sf c‖ ^ 2 = 1 := by exact_mod_cast hprod
  have hnn := norm_nonneg (sLocalRho Sf c)
  nlinarith [hsq, hnn]
