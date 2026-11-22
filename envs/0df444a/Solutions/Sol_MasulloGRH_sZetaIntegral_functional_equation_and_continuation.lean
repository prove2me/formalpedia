-- Prove2me | solution 1 for MasulloGRH.sZetaIntegral_functional_equation_and_continuation
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T19:30:11.312291+00:00
-- url     : https://prove2.me/submissions/2f0b4863-cca7-48c5-aea6-c150e37609d3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_MasulloGRH_SLocalZetaIntegrals
import Theorems.Thm_MasulloGRH_sZetaIntegral_integrable_and_differentiableOn
import Theorems.Thm_MasulloGRH_sLocalFourier_schwartzBruhat_equiv
import Theorems.Thm_MasulloGRH_sZetaIntegral_mul_fourier_symm
import Theorems.Thm_MasulloGRH_exists_meromorphic_sZetaIntegral_ratio

open MeasureTheory NumberField IsDedekindDomain

set_option autoImplicit false

namespace Sol_MasulloGRH_sZetaIntegral_functional_equation_and_continuation

open MasulloGRH Filter Topology

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
  show Continuous fun g : SIdeleGroup F Sf => (∏ w : InfinitePlace F, ‖(g : SAdeleRing F Sf).1 w‖ ^ w.mult) *
    ∏ v : Sf, ‖(g : SAdeleRing F Sf).2 v‖
  refine Continuous.mul (continuous_finsetProd _ fun w _ => ?_)
    (continuous_finsetProd _ fun v _ => ?_)
  · exact ((continuous_apply w).comp (continuous_fst.comp h1)).norm.pow _
  · exact ((continuous_apply v).comp (continuous_snd.comp h1)).norm

theorem twist_isQC {c : SIdeleGroup F Sf → ℂ} (hc : IsSIdeleQuasiCharacter Sf c) (s : ℂ) :
    IsSIdeleQuasiCharacter Sf (sQuasiTwist Sf c s) := by
  obtain ⟨hcont, hmul, hne⟩ := hc
  refine ⟨?_, ?_, ?_⟩
  · unfold sQuasiTwist
    exact hcont.mul ((Complex.continuous_ofReal.comp continuous_sIdeleNorm').cpow continuous_const
      fun g => Complex.ofReal_mem_slitPlane.mpr (sIdeleNorm_pos' g))
  · intro g h
    unfold sQuasiTwist
    rw [hmul, sIdeleNorm_mul', Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (sIdeleNorm_pos' g).le (sIdeleNorm_pos' h).le]
    ring
  · intro g
    unfold sQuasiTwist
    refine mul_ne_zero (hne g) ?_
    rw [Ne, Complex.cpow_eq_zero_iff]
    exact fun h => (Complex.ofReal_ne_zero.mpr (sIdeleNorm_pos' g).ne') h.1

theorem twist_norm {c : SIdeleGroup F Sf → ℂ} {σ : ℝ}
    (hσ : ∀ g : SIdeleGroup F Sf, ‖c g‖ = sIdeleNorm Sf g ^ σ) (s : ℂ) (g : SIdeleGroup F Sf) :
    ‖sQuasiTwist Sf c s g‖ = sIdeleNorm Sf g ^ (σ + s.re) := by
  unfold sQuasiTwist
  rw [norm_mul, hσ, Complex.norm_cpow_eq_rpow_re_of_pos (sIdeleNorm_pos' g),
    Real.rpow_add (sIdeleNorm_pos' g)]

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

theorem dual_twist (c : SIdeleGroup F Sf → ℂ) (s : ℂ) :
    sQuasiDual Sf (sQuasiTwist Sf c s) = sQuasiTwist Sf (sQuasiDual Sf c) (-s) := by
  funext g
  unfold sQuasiDual sQuasiTwist
  rw [mul_inv, Complex.cpow_neg]
  ring

end Sol_MasulloGRH_sZetaIntegral_functional_equation_and_continuation

open MasulloGRH Sol_MasulloGRH_sZetaIntegral_functional_equation_and_continuation Filter Topology

theorem solution
    (F : Type*) [Field F] [NumberField F] (Sf : Finset (HeightOneSpectrum (𝓞 F)))
    (c : SIdeleGroup F Sf → ℂ) (hc : IsSIdeleQuasiCharacter Sf c)
    (σ : ℝ) (hσ : ∀ g : SIdeleGroup F Sf, ‖c g‖ = sIdeleNorm Sf g ^ σ) :
    ∃ ρ : ℂ → ℂ, MeromorphicOn ρ Set.univ ∧
      (∀ (f : SAdelicSchwartz F Sf) (s : ℂ), σ + s.re < 1 →
        Integrable
          (fun g : SIdeleGroup F Sf =>
            sLocalFourier Sf f.eval (g : SAdeleRing F Sf) * sQuasiDual Sf (sQuasiTwist Sf c s) g)
          (sMultiplicativeTamagawa F Sf)) ∧
      (∀ (f : SAdelicSchwartz F Sf) (s : ℂ), 0 < σ + s.re → σ + s.re < 1 →
        sZetaIntegral f (sQuasiTwist Sf c s) =
          ρ s * sZetaIntegralFun Sf (sLocalFourier Sf f.eval)
            (sQuasiDual Sf (sQuasiTwist Sf c s))) ∧
      ∀ f : SAdelicSchwartz F Sf, ∃ M : ℂ → ℂ, MeromorphicOn M Set.univ ∧
        (∀ s : ℂ, 0 < σ + s.re → M s = sZetaIntegral f (sQuasiTwist Sf c s)) ∧
        ∀ s : ℂ, σ + s.re < 1 → AnalyticAt ℂ ρ s →
          AnalyticAt ℂ M s ∧
          M s = ρ s * sZetaIntegralFun Sf (sLocalFourier Sf f.eval)
            (sQuasiDual Sf (sQuasiTwist Sf c s)) := by
  classical
  -- the meromorphic factor `ρ`, with one witness test function for each `s` in the strip
  obtain ⟨ρ, hρm, hρ⟩ := exists_meromorphic_sZetaIntegral_ratio F Sf c hc σ hσ
  -- the Fourier transform as an automorphism of the Schwartz–Bruhat space
  obtain ⟨-, T, hT, -⟩ := sLocalFourier_schwartzBruhat_equiv F Sf
  have hdc := dual_isQC hc
  have hdn : ∀ g : SIdeleGroup F Sf, ‖sQuasiDual Sf c g‖ = sIdeleNorm Sf g ^ (1 - σ) :=
    dual_norm hσ
  -- `Z_S(\hat f, \hat{c_s}) = Z_S(T f, \hat c |·|^{-s})`
  have hZh : ∀ (f : SAdelicSchwartz F Sf) (s : ℂ),
      sZetaIntegralFun Sf (sLocalFourier Sf f.eval) (sQuasiDual Sf (sQuasiTwist Sf c s)) =
        sZetaIntegral (T f) (sQuasiTwist Sf (sQuasiDual Sf c) (-s)) := by
    intro f s
    rw [dual_twist, sZetaIntegral, hT f]
  -- part (1): integrability of `\hat f \hat{c_s}` for `σ + Re s < 1`
  have hint : ∀ (f : SAdelicSchwartz F Sf) (s : ℂ), σ + s.re < 1 →
      Integrable
        (fun g : SIdeleGroup F Sf =>
          sLocalFourier Sf f.eval (g : SAdeleRing F Sf) * sQuasiDual Sf (sQuasiTwist Sf c s) g)
        (sMultiplicativeTamagawa F Sf) := by
    intro f s hs
    have h := (sZetaIntegral_integrable_and_differentiableOn F Sf (T f) (sQuasiDual Sf c) hdc
      (1 - σ) hdn).1 (-s) (by simp only [Complex.neg_re]; linarith)
    rw [dual_twist, ← hT f]
    exact h
  -- holomorphy of `s ↦ Z_S(\hat f, \hat{c_s})` on `σ + Re s < 1`
  have hdiff : ∀ f : SAdelicSchwartz F Sf,
      DifferentiableOn ℂ
        (fun s => sZetaIntegralFun Sf (sLocalFourier Sf f.eval) (sQuasiDual Sf (sQuasiTwist Sf c s)))
        {s : ℂ | σ + s.re < 1} := by
    intro f
    have hd := (sZetaIntegral_integrable_and_differentiableOn F Sf (T f) (sQuasiDual Sf c) hdc
      (1 - σ) hdn).2
    have heq : (fun s => sZetaIntegralFun Sf (sLocalFourier Sf f.eval)
        (sQuasiDual Sf (sQuasiTwist Sf c s))) =
        (fun s => sZetaIntegral (T f) (sQuasiTwist Sf (sQuasiDual Sf c) s)) ∘ (fun s : ℂ => -s) := by
      funext s
      exact hZh f s
    rw [heq]
    refine hd.comp differentiable_neg.differentiableOn ?_
    intro s hs
    simp only [Set.mem_ofPred_eq, Complex.neg_re] at hs ⊢
    linarith
  -- part (2): the functional equation on the strip (Tate's argument)
  have hFE : ∀ (f : SAdelicSchwartz F Sf) (s : ℂ), 0 < σ + s.re → σ + s.re < 1 →
      sZetaIntegral f (sQuasiTwist Sf c s) =
        ρ s * sZetaIntegralFun Sf (sLocalFourier Sf f.eval)
          (sQuasiDual Sf (sQuasiTwist Sf c s)) := by
    intro f s h0 h1
    obtain ⟨f0, hne, hf0⟩ := hρ s h0 h1
    have hsym := sZetaIntegral_mul_fourier_symm F Sf (sQuasiTwist Sf c s) (twist_isQC hc s)
      (σ + s.re) (twist_norm hσ s) h0 h1 f f0
    apply mul_right_cancel₀ hne
    rw [hsym, hf0]
    ring
  refine ⟨ρ, hρm, hint, hFE, fun f => ?_⟩
  -- part (3): the continuation
  have hU : IsOpen {s : ℂ | 0 < σ + s.re} :=
    isOpen_lt continuous_const (continuous_const.add Complex.continuous_re)
  have hV : IsOpen {s : ℂ | σ + s.re < 1} :=
    isOpen_lt (continuous_const.add Complex.continuous_re) continuous_const
  have hZf := (sZetaIntegral_integrable_and_differentiableOn F Sf f c hc σ hσ).2
  let Zf : ℂ → ℂ := fun s => sZetaIntegral f (sQuasiTwist Sf c s)
  let Zh : ℂ → ℂ := fun s =>
    sZetaIntegralFun Sf (sLocalFourier Sf f.eval) (sQuasiDual Sf (sQuasiTwist Sf c s))
  let M : ℂ → ℂ := fun s => if 0 < σ + s.re then Zf s else ρ s * Zh s
  have hMU : ∀ s : ℂ, 0 < σ + s.re → M s = Zf s := fun s h => if_pos h
  have hMV : ∀ s : ℂ, σ + s.re < 1 → M s = ρ s * Zh s := by
    intro s hs
    by_cases h : 0 < σ + s.re
    · exact (if_pos h).trans (hFE f s h hs)
    · exact if_neg h
  refine ⟨M, ?_, hMU, ?_⟩
  · intro s _
    by_cases h : 0 < σ + s.re
    · have hev : Zf =ᶠ[𝓝 s] M :=
        Filter.eventually_of_mem (hU.mem_nhds h) fun t ht => (hMU t ht).symm
      have han : AnalyticAt ℂ Zf s := hZf.analyticAt (hU.mem_nhds h)
      exact han.meromorphicAt.congr (hev.filter_mono nhdsWithin_le_nhds)
    · have h1 : σ + s.re < 1 := by linarith [not_lt.mp h]
      have hev : (fun t => ρ t * Zh t) =ᶠ[𝓝 s] M :=
        Filter.eventually_of_mem (hV.mem_nhds h1) fun t ht => (hMV t ht).symm
      have hm : MeromorphicAt (fun t => ρ t * Zh t) s :=
        (hρm s (Set.mem_univ s)).mul ((hdiff f).analyticAt (hV.mem_nhds h1)).meromorphicAt
      exact hm.congr (hev.filter_mono nhdsWithin_le_nhds)
  · intro s hs hρa
    have han : AnalyticAt ℂ (fun t => ρ t * Zh t) s :=
      hρa.mul ((hdiff f).analyticAt (hV.mem_nhds hs))
    exact ⟨han.congr (Filter.eventually_of_mem (hV.mem_nhds hs) fun t ht => (hMV t ht).symm),
      hMV s hs⟩
