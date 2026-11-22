-- Prove2me | solution 1 for MasulloGRH.completedHeckeLFunction_properties
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-21T20:17:27.15299+00:00
-- url     : https://prove2.me/submissions/03293ea7-4722-4472-9cbb-5fca48a70282

import Definitions.Def_MasulloGRH_CompletedL
import Theorems.Thm_MasulloGRH_heckeLFunction_exists_meromorphic_continuation
import Theorems.Thm_MasulloGRH_heckeLFunction_no_zero_re_ge_one
import Theorems.Thm_MasulloGRH_finite_hecke_entire_or_simple_norm_pole
import Theorems.Thm_MasulloGRH_heckeLFunction_reflected_order_left_half
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

set_option autoImplicit false
open NumberField MasulloGRH Set Complex

private theorem smooth_gamma_aux {b : ℂ} (hb : b ≠ 0) (u : ℂ → ℂ) (du : Differentiable ℂ u) :
    Meromorphic (fun z => b ^ (-(u z)) * Complex.Gamma (u z)) ∧
    ∀ z, 0 < (u z).re →
      AnalyticAt ℂ (fun z => b ^ (-(u z)) * Complex.Gamma (u z)) z ∧
        b ^ (-(u z)) * Complex.Gamma (u z) ≠ 0 := by
  have hbfun : Differentiable ℂ (fun z => b ^ (-(u z))) := by
    simp_rw [Complex.cpow_def_of_ne_zero hb]
    fun_prop
  have hrec : Differentiable ℂ (fun z => (Complex.Gamma (u z))⁻¹) :=
    Complex.differentiable_one_div_Gamma.comp du
  have hinv : ((fun z : ℂ => (Complex.Gamma (u z))⁻¹) : ℂ → ℂ)⁻¹ =
      fun z => Complex.Gamma (u z) := by funext z; simp
  constructor
  · intro z
    apply (hbfun.analyticAt z).meromorphicAt.mul
    simpa only [hinv] using (hrec.analyticAt z).meromorphicAt.inv
  intro z hz
  have hn := Complex.Gamma_ne_zero_of_re_pos hz
  constructor
  · apply (hbfun.analyticAt z).mul
    simpa only [hinv] using (hrec.analyticAt z).inv (inv_ne_zero hn)
  · exact mul_ne_zero (Complex.cpow_ne_zero_iff.mpr (Or.inl hb)) hn

private theorem smooth_arch_factors (F : Type*) [Field F] [NumberField F] (χ : HeckeCharacter F)
    (w : InfinitePlace F) : Meromorphic (χ.archLFactor w) ∧
    ∀ z : ℂ, 0 < z.re → AnalyticAt ℂ (χ.archLFactor w) z ∧ χ.archLFactor w z ≠ 0 := by
  classical
  by_cases hw : w.IsReal
  · let u := fun s : ℂ => (s + χ.archExponent w * Complex.I + χ.archParity w) / 2
    have hu : Differentiable ℂ u := by dsimp [u]; fun_prop
    have h := smooth_gamma_aux (b := (Real.pi : ℂ)) (by exact_mod_cast Real.pi_ne_zero) u hu
    have eqF : χ.archLFactor w = fun z : ℂ => (Real.pi : ℂ) ^ (-u z) * Complex.Gamma (u z) := by
      funext z; simp [HeckeCharacter.archLFactor, hw, u]
    rw [eqF]
    refine ⟨h.1, fun z hz => h.2 z ?_⟩
    dsimp [u]
    simp only [Complex.div_ofNat_re, Complex.add_re, Complex.mul_I_re, Complex.ofReal_im,
      neg_zero, add_zero, Complex.natCast_re]
    positivity
  · let u := fun s : ℂ => s + χ.archExponent w * Complex.I + (χ.archWeight w : ℂ) / 2
    have hu : Differentiable ℂ u := by dsimp [u]; fun_prop
    have hb : (2 * (Real.pi : ℂ)) ≠ 0 := mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)
    have h := smooth_gamma_aux hb u hu
    have eqF : χ.archLFactor w = fun z : ℂ => (2 * (Real.pi : ℂ)) ^ (-u z) * Complex.Gamma (u z) := by
      funext z; simp [HeckeCharacter.archLFactor, hw, u]
    rw [eqF]
    refine ⟨h.1, fun z hz => h.2 z ?_⟩
    dsimp [u]
    simp only [Complex.div_ofNat_re, Complex.add_re, Complex.mul_I_re, Complex.ofReal_im,
      neg_zero, add_zero, Complex.natCast_re]
    positivity

private theorem smooth_gamma_factors (F : Type*) [Field F] [NumberField F] (χ : HeckeCharacter F) :
    Meromorphic χ.gammaFactor ∧
    ∀ z : ℂ, 0 < z.re → AnalyticAt ℂ χ.gammaFactor z ∧ χ.gammaFactor z ≠ 0 := by
  classical
  constructor
  · intro z
    exact MeromorphicAt.fun_prod fun w _ => (smooth_arch_factors F χ w).1 z
  intro z hz
  constructor
  · exact Finset.analyticAt_fun_prod _ fun w _ => ((smooth_arch_factors F χ w).2 z hz).1
  · exact Finset.prod_ne_zero_iff.mpr fun w _ => ((smooth_arch_factors F χ w).2 z hz).2

private theorem smooth_completed_orders (F : Type*) [Field F] [NumberField F] (χ : HeckeCharacter F) :
    MeromorphicNFOn (completedHeckeLFunction χ) Set.univ ∧
    (∀ z : ℂ, 1 < z.re → completedHeckeLFunction χ z = χ.gammaFactor z * heckeEulerProduct χ z) ∧
    (∀ z : ℂ, 0 < z.re → meromorphicOrderAt (completedHeckeLFunction χ) z =
      meromorphicOrderAt (heckeLFunction χ) z) ∧
    (∀ z : ℂ, meromorphicOrderAt (completedHeckeLFunction χ) z =
      meromorphicOrderAt χ.gammaFactor z + meromorphicOrderAt (heckeLFunction χ) z) := by
  have hc := heckeLFunction_exists_meromorphic_continuation F χ
  have hfin : MeromorphicNFOn (heckeLFunction χ) Set.univ ∧
      ∀ z : ℂ, 1 < z.re → heckeLFunction χ z = heckeEulerProduct χ z := by
    unfold heckeLFunction
    rw [dif_pos hc]
    exact hc.choose_spec
  obtain ⟨hγ, hγU⟩ := smooth_gamma_factors F χ
  let P := fun z : ℂ => χ.gammaFactor z * heckeLFunction χ z
  have hP : MeromorphicOn P univ := hγ.meromorphicOn.mul hfin.1.meromorphicOn
  refine ⟨meromorphicNFOn_toMeromorphicNFOn _ _, ?_, ?_, ?_⟩
  · intro z hz
    have hz' := hγU z (by linarith)
    have hnf : MeromorphicNFAt P z := (meromorphicNFAt_mul_iff_right hz'.1 hz'.2).mpr (hfin.1 (mem_univ _))
    change toMeromorphicNFOn P univ z = _
    rw [toMeromorphicNFOn_eq_toMeromorphicNFAt hP (mem_univ _), toMeromorphicNFAt_eq_self.mpr hnf]
    exact congrArg (χ.gammaFactor z * ·) (hfin.2 z hz)
  · intro z hz
    change meromorphicOrderAt (toMeromorphicNFOn P univ) z = _
    rw [meromorphicOrderAt_toMeromorphicNFOn hP (mem_univ _)]
    exact meromorphicOrderAt_mul_of_ne_zero (hγU z hz).1 (hγU z hz).2

  · intro z
    change meromorphicOrderAt (toMeromorphicNFOn P univ) z = _
    rw [meromorphicOrderAt_toMeromorphicNFOn hP (mem_univ _)]
    exact meromorphicOrderAt_mul (hγ z) (hfin.1.meromorphicOn z (mem_univ _))


private theorem smooth_quotient_unit {f g : ℂ → ℂ}
    (hf : MeromorphicNFOn f univ) (hg : MeromorphicNFOn g univ)
    (hord : ∀ z, meromorphicOrderAt g z = meromorphicOrderAt f z)
    (hfinite : ∀ z, meromorphicOrderAt f z ≠ ⊤) :
    ∃ ε : ℂ → ℂ, Differentiable ℂ ε ∧ (∀ z, ε z ≠ 0) ∧ ∀ z, g z = ε z * f z := by
  let q := toMeromorphicNFOn (g / f) univ
  have hm : MeromorphicOn (g / f) univ := hg.meromorphicOn.div hf.meromorphicOn
  have hn (z : ℂ) : MeromorphicNFAt q z := meromorphicNFOn_toMeromorphicNFOn _ _ (mem_univ z)
  have hzero (z : ℂ) : meromorphicOrderAt q z = 0 := by
    change meromorphicOrderAt (toMeromorphicNFOn (g / f) univ) z = 0
    rw [meromorphicOrderAt_toMeromorphicNFOn hm (mem_univ _),
      meromorphicOrderAt_div (hg.meromorphicOn z (mem_univ _)) (hf.meromorphicOn z (mem_univ _)),
      hord]
    lift meromorphicOrderAt f z to ℤ using hfinite z with m
    simp
  refine ⟨q, fun z => ((hn z).meromorphicOrderAt_nonneg_iff_analyticAt.mp (hzero z).ge).differentiableAt,
    fun z => (hn z).meromorphicOrderAt_eq_zero_iff.mp (hzero z), ?_⟩
  intro z
  by_cases hz : f z = 0
  · have hgz : g z = 0 := by
      by_contra h
      exact (((hf (mem_univ z)).meromorphicOrderAt_eq_zero_iff).mp
        ((hord z).symm.trans ((hg (mem_univ z)).meromorphicOrderAt_eq_zero_iff.mpr h))) hz
    simp [hz, hgz]
  · have ho := (hf (mem_univ z)).meromorphicOrderAt_eq_zero_iff.mpr hz
    have hfo := (hf (mem_univ z)).meromorphicOrderAt_nonneg_iff_analyticAt.mp ho.ge
    have hgo := (hg (mem_univ z)).meromorphicOrderAt_nonneg_iff_analyticAt.mp ((hord z).trans ho).ge
    have hquot : MeromorphicNFAt (g/f) z := (hgo.div hfo hz).meromorphicNFAt
    change g z = toMeromorphicNFOn (g/f) univ z * f z
    rw [toMeromorphicNFOn_eq_toMeromorphicNFAt hm (mem_univ _), toMeromorphicNFAt_eq_self.mpr hquot]
    exact (div_mul_cancel₀ _ hz).symm

private theorem smooth_inv_nontrivial {F : Type*} [Field F] [NumberField F] (χ : HeckeCharacter F)
    (hχ : ¬ χ.IsTrivialOnNormOne) : ¬ χ⁻¹.IsTrivialOnNormOne := by
  intro h
  apply hχ
  intro g hg
  have he := h g hg
  change (χ (QuotientGroup.mk g))⁻¹ = 1 at he
  simpa using he

private theorem smooth_inv_norm {F : Type*} [Field F] [NumberField F] (χ : HeckeCharacter F)
    (t : ℝ) (hχ : χ.IsNormPower t) : χ⁻¹.IsNormPower (-t) := by
  intro g
  change (((χ (QuotientGroup.mk g))⁻¹ : Circle) : ℂ) =
    ((ideleNorm g : ℝ) : ℂ) ^ (-(((-t : ℝ) : ℂ) * Complex.I))
  rw [Circle.coe_inv, hχ g, Complex.cpow_neg]
  simp


private theorem smooth_parent_aux
    (F : Type*) [Field F] [NumberField F]
    (finite_entire : ∀ χ : HeckeCharacter F, ¬ χ.IsTrivialOnNormOne →
      Differentiable ℂ (heckeLFunction χ))
    (finite_pole : ∀ (χ : HeckeCharacter F) (t : ℝ), χ.IsNormPower t →
      meromorphicOrderAt (heckeLFunction χ) (1+t*Complex.I) = -1 ∧
      ∀ s : ℂ, s ≠ 1+t*Complex.I → AnalyticAt ℂ (heckeLFunction χ) s)
    (χ : HeckeCharacter F) :
    (MeromorphicNFOn (completedHeckeLFunction χ) Set.univ ∧
      ∀ s : ℂ, 1 < s.re → completedHeckeLFunction χ s = χ.gammaFactor s * heckeEulerProduct χ s) ∧
    (¬ χ.IsTrivialOnNormOne → Differentiable ℂ (completedHeckeLFunction χ)) ∧
    (∀ t : ℝ, χ.IsNormPower t →
      meromorphicOrderAt (completedHeckeLFunction χ) (t * Complex.I) = -1 ∧
      meromorphicOrderAt (completedHeckeLFunction χ) (1 + t * Complex.I) = -1 ∧
      ∀ s : ℂ, s ≠ t * Complex.I → s ≠ 1 + t * Complex.I →
        AnalyticAt ℂ (completedHeckeLFunction χ) s) ∧
    (∃ ε : ℂ → ℂ, Differentiable ℂ ε ∧ (∀ s : ℂ, ε s ≠ 0) ∧
      ∀ s : ℂ, completedHeckeLFunction χ⁻¹ (1 - s) = ε s * completedHeckeLFunction χ s) ∧
    (∀ s : ℂ, 0 < s.re → 0 < meromorphicOrderAt (completedHeckeLFunction χ) s → s.re < 1) := by
  let c := fun (η : HeckeCharacter F) => completedHeckeLFunction η
  let fin := fun (η : HeckeCharacter F) => heckeLFunction η
  have hnf (η : HeckeCharacter F) := (smooth_completed_orders F η).1
  have hu (η : HeckeCharacter F) (z : ℂ) (hz : 0 < z.re) :
      meromorphicOrderAt (c η) z = meromorphicOrderAt (fin η) z :=
    (smooth_completed_orders F η).2.2.1 z hz
  have hleft (η : HeckeCharacter F) (s : ℂ) (hs : s.re ≤ 1/2) :
      meromorphicOrderAt (c η) s = meromorphicOrderAt (c η⁻¹) (1-s) := by
    rw [(smooth_completed_orders F η).2.2.2 s, hu η⁻¹ _ (by simp only [sub_re, one_re]; linarith)]
    exact heckeLFunction_reflected_order_left_half F η s hs
  have href (η : HeckeCharacter F) (s : ℂ) :
      meromorphicOrderAt (c η) s = meromorphicOrderAt (c η⁻¹) (1-s) := by
    by_cases hs : s.re ≤ 1/2
    · exact hleft η s hs
    · have hr : (1-s).re ≤ 1/2 := by simp only [sub_re, one_re]; linarith
      simpa only [inv_inv, sub_sub_cancel] using (hleft η⁻¹ (1-s) hr).symm
  have hright (η : HeckeCharacter F) (s : ℂ) (hs : 1 ≤ s.re) :
      meromorphicOrderAt (c η) s ≤ 0 := by
    rw [hu η s (by linarith)]
    exact heckeLFunction_no_zero_re_ge_one F η s hs
  have hfinite (η : HeckeCharacter F) (s : ℂ) : meromorphicOrderAt (c η) s ≠ ⊤ := by
    apply ((hnf η).meromorphicOn.exists_meromorphicOrderAt_ne_top_iff_forall isConnected_univ).mp
      (u := ⟨s, mem_univ s⟩)
    exact ⟨⟨1, mem_univ _⟩, ne_top_of_le_ne_top (by simp) (hright η 1 (by simp))⟩
  have hA (η : HeckeCharacter F) (s : ℂ) (hs : 0 ≤ meromorphicOrderAt (c η) s) :
      AnalyticAt ℂ (c η) s := ((hnf η) (mem_univ s)).meromorphicOrderAt_nonneg_iff_analyticAt.mp hs
  refine ⟨⟨hnf χ, (smooth_completed_orders F χ).2.1⟩, ?_, ?_, ?_, ?_⟩
  · intro hχ s
    apply (hA χ s ?_).differentiableAt
    by_cases hs : 0 < s.re
    · rw [hu χ s hs]
      exact ((finite_entire χ hχ).analyticAt s).meromorphicOrderAt_nonneg
    · rw [href, hu χ⁻¹ _ (by simp only [sub_re, one_re]; linarith)]
      exact ((finite_entire χ⁻¹ (smooth_inv_nontrivial χ hχ)).analyticAt _).meromorphicOrderAt_nonneg
  · intro t ht
    obtain ⟨hpo, hol⟩ := finite_pole χ t ht
    obtain ⟨hpo', hol'⟩ := finite_pole χ⁻¹ (-t) (smooth_inv_norm χ t ht)
    have hre : (1+t*Complex.I).re = 1 := by simp
    have hre' : (1-(t:ℂ)*Complex.I).re = 1 := by simp
    refine ⟨?_, ?_, ?_⟩
    · rw [href, hu χ⁻¹ _ (by linarith)]
      simpa [sub_eq_add_neg] using hpo'
    · rw [hu χ _ (by linarith)]
      exact hpo
    · intro s hs hs'
      apply hA
      by_cases hpos : 0 < s.re
      · rw [hu χ s hpos]
        exact (hol s hs').meromorphicOrderAt_nonneg
      · rw [href, hu χ⁻¹ _ (by simp only [sub_re, one_re]; linarith)]
        apply (hol' (1-s) ?_).meromorphicOrderAt_nonneg
        intro h
        apply hs
        push_cast at h
        linear_combination -h
  · let r := fun z : ℂ => 1-z
    have hr (s : ℂ) : AnalyticAt ℂ r s := by dsimp [r]; fun_prop
    have dr (s : ℂ) : deriv r s ≠ 0 := by dsimp [r]; simp
    let g := c χ⁻¹ ∘ r
    have hg : MeromorphicNFOn g univ := fun s _ =>
      (meromorphicNFAt_comp_iff_of_deriv_ne_zero (hr s) (dr s)).mpr ((hnf χ⁻¹) (mem_univ _))
    have hord (s : ℂ) : meromorphicOrderAt g s = meromorphicOrderAt (c χ) s :=
      (meromorphicOrderAt_comp_of_deriv_ne_zero (hr s) (dr s)).trans (href χ s).symm
    exact smooth_quotient_unit (hnf χ) hg hord (hfinite χ)
  · intro s _ hs
    by_contra! h
    exact hs.not_ge (hright χ s h)
theorem solution (F : Type*) [Field F] [NumberField F]
    (χ : HeckeCharacter F) :
    (MeromorphicNFOn (completedHeckeLFunction χ) Set.univ ∧
      ∀ s : ℂ, 1 < s.re → completedHeckeLFunction χ s = χ.gammaFactor s * heckeEulerProduct χ s) ∧
    (¬ χ.IsTrivialOnNormOne → Differentiable ℂ (completedHeckeLFunction χ)) ∧
    (∀ t₀ : ℝ, χ.IsNormPower t₀ →
      meromorphicOrderAt (completedHeckeLFunction χ) (t₀ * Complex.I) = -1 ∧
      meromorphicOrderAt (completedHeckeLFunction χ) (1 + t₀ * Complex.I) = -1 ∧
      ∀ s : ℂ, s ≠ t₀ * Complex.I → s ≠ 1 + t₀ * Complex.I →
        AnalyticAt ℂ (completedHeckeLFunction χ) s) ∧
    (∃ ε : ℂ → ℂ, Differentiable ℂ ε ∧ (∀ s : ℂ, ε s ≠ 0) ∧
      ∀ s : ℂ, completedHeckeLFunction χ⁻¹ (1 - s) = ε s * completedHeckeLFunction χ s) ∧
    (∀ s : ℂ, 0 < s.re → 0 < meromorphicOrderAt (completedHeckeLFunction χ) s → s.re < 1) := by
  apply smooth_parent_aux F
    (fun η => (finite_hecke_entire_or_simple_norm_pole F η).1)
    (fun η => (finite_hecke_entire_or_simple_norm_pole F η).2) χ
