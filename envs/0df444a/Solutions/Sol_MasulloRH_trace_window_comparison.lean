-- Prove2me | solution 1 for MasulloRH.trace_window_comparison
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-20T22:17:40.420873+00:00
-- url     : https://prove2.me/submissions/ffc65ede-4571-4ec3-9379-027ce018611a

import Definitions.Def_MasulloRH_RationalTrace
import Theorems.Thm_ConnesRZ_explicit_formula
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Data.Nat.Factorization.PrimePow
import Mathlib.MeasureTheory.Function.LocallyIntegrable

set_option autoImplicit false

open MeasureTheory Set Filter

namespace MasulloRH

private theorem log_test {φ : ℝ → ℂ} (h : IsRationalTraceTest φ) :
    ConnesRZ.IsTest (φ ∘ Real.exp) := by
  refine ⟨h.1.comp Real.contDiff_exp, HasCompactSupport.of_support_subset_isCompact
    (K := Real.log '' tsupport φ) (h.2.1.image_of_continuousOn ?_) ?_⟩
  · exact Real.continuousOn_log.mono (fun t ht => (h.2.2.1 ht).ne')
  · intro t ht
    exact ⟨Real.exp t, subset_tsupport φ ht, Real.log_exp t⟩

private theorem log_mellin (φ : ℝ → ℂ) (z : ℂ) :
    ConnesRZ.mellinHat (φ ∘ Real.exp) z = mellin φ (z - 1/2) := by
  unfold ConnesRZ.mellinHat mellin
  rw [← Real.range_exp, ← image_univ]
  rw [integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) Real.exp_injective.injOn]
  rw [setIntegral_univ]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [Function.comp_apply, abs_of_pos (Real.exp_pos x), smul_eq_mul,
    Complex.real_smul, Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos x).ne'),
    ← Complex.ofReal_log (Real.exp_pos x).le, Real.log_exp]
  rw [Complex.ofReal_exp, ← mul_assoc, ← Complex.exp_add]
  rw [mul_comm (φ (Real.exp x))]
  congr 2
  ring

private theorem prime_reindex (φ : ℝ → ℂ) :
    ConnesRZ.primeSum (φ ∘ Real.exp) = ∑' i, primePowerTraceTerm φ i := by
  let idx (i : Nat.Primes × ℕ) : ℕ := Nat.Primes.prodNatEquiv i
  have hi : Function.Injective idx := Subtype.val_injective.comp Nat.Primes.prodNatEquiv.injective
  unfold ConnesRZ.primeSum
  rw [← hi.tsum_eq]
  · apply tsum_congr
    rintro ⟨p,k⟩
    have hm : 0 < ((p : ℕ) : ℝ) ^ (k+1) := pow_pos (by exact_mod_cast p.prop.pos) _
    simp [-Real.log_pow, idx, primePowerTraceTerm, ArithmeticFunction.vonMangoldt_apply_pow (Nat.succ_ne_zero _),
      ArithmeticFunction.vonMangoldt_apply_prime p.prop, Real.exp_neg, Real.exp_log hm]
  · intro m hm
    by_contra hn
    have h : ¬ IsPrimePow m := fun h => hn ⟨Nat.Primes.prodNatEquiv.symm ⟨m,h⟩,
      congrArg Subtype.val (Nat.Primes.prodNatEquiv.apply_symm_apply _)⟩
    exact hm (by simp [ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr h])


private theorem tail_zero {φ : ℝ → ℂ} (h : IsRationalTraceTest φ) :
    ∃ R : ℝ, ∀ t ≥ R, φ t = 0 ∧ φ t⁻¹ = 0 := by
  have h0 : (0:ℝ) ∉ tsupport φ := fun ht => (lt_irrefl (0 : ℝ)) (h.2.2.1 ht)
  have ht : φ =ᶠ[atTop] 0 :=
    (hasCompactSupport_iff_eventuallyEq.mp h.2.1).filter_mono (by rw [Filter.coclosedCompact_eq_cocompact]; exact atTop_le_cocompact)
  exact eventually_atTop.mp (ht.and (tendsto_inv_atTop_zero.eventually
    (notMem_tsupport_iff_eventuallyEq.mp h0)))

private theorem trace_prime_summable {φ : ℝ → ℂ} (h : IsRationalTraceTest φ) :
    Summable (primePowerTraceTerm φ) := by
  obtain ⟨R, hR⟩ := tail_zero h
  obtain ⟨N, hN⟩ := exists_nat_gt R
  let q (i : Nat.Primes × ℕ) : ℕ := Nat.Primes.prodNatEquiv i
  have hi : Function.Injective q := Subtype.val_injective.comp Nat.Primes.prodNatEquiv.injective
  apply summable_of_hasFiniteSupport
  apply ((Set.finite_Iio N).preimage hi.injOn).subset
  rintro ⟨p,k⟩ ht
  change (p:ℕ)^(k+1) < N
  by_contra! hge
  have hh := hR ((p:ℕ)^(k+1):ℝ) (hN.le.trans (by exact_mod_cast hge))
  exact ht (by simp [primePowerTraceTerm, hh.1, hh.2])

private theorem trace_real_integrable {φ : ℝ → ℂ} (h : IsRationalTraceTest φ) :
    IntegrableOn (realTraceIntegrand φ) (Ioi 1) := by
  obtain ⟨R, hR⟩ := tail_zero h
  let g := fun t : ℝ => φ t + φ t⁻¹
  have hcont {t : ℝ} (ht : 0 < t) : ContinuousAt g t :=
    h.1.continuous.continuousAt.add (h.1.continuous.continuousAt.comp (continuousAt_inv₀ ht.ne'))
  have hd : DifferentiableAt ℝ g 1 := by
    have hdφ := h.1.differentiable (by decide)
    exact (hdφ 1).add ((hdφ (1:ℝ)⁻¹).comp 1 (differentiableAt_inv (by norm_num)))
  let F := fun t : ℝ => dslope g 1 t * ((Real.sqrt t / (t+1) : ℝ) : ℂ)
  have hc : ContinuousOn F (Icc 1 R) := by
    intro t ht
    have ht0 := zero_lt_one.trans_le ht.1
    have hds : ContinuousAt (dslope g 1) t := by
      by_cases he : t=1
      · subst t; exact continuousAt_dslope_same.mpr hd
      · exact (continuousAt_dslope_of_ne he).mpr (hcont ht0)
    apply ContinuousAt.continuousWithinAt
    exact hds.mul (Complex.continuous_ofReal.continuousAt.comp
      (Real.continuous_sqrt.continuousAt.div (continuousAt_id.add continuousAt_const) (by dsimp; linarith)))
  have heq {t : ℝ} (ht : 1 < t) : F t = realTraceIntegrand φ t := by
    have hg1 : g 1 = 0 := by simp [g,h.2.2.2]
    have ht1 : ((t:ℂ)-1) ≠ 0 := by exact_mod_cast (sub_ne_zero.mpr ht.ne')
    have ht2 : ((t:ℂ)+1) ≠ 0 := by exact_mod_cast (show t+1 ≠ 0 by linarith)
    unfold F realTraceIntegrand
    rw [dslope_of_ne _ ht.ne', slope, hg1, vsub_eq_sub, sub_zero, Complex.real_smul]
    push_cast
    change _ = g t * _
    rw [show (t:ℂ)^2-1 = (t-1)*(t+1) by ring]
    field_simp
  have hb := hc.integrableOn_compact (μ := volume) isCompact_Icc
  have hsmall : IntegrableOn (realTraceIntegrand φ) (Ioc 1 R) :=
    (hb.mono_set Ioc_subset_Icc_self).congr_fun (fun t ht => heq ht.1) measurableSet_Ioc
  have hlarge : IntegrableOn (realTraceIntegrand φ) (Ioi R) := by
    apply (integrableOn_zero (ε' := ℂ)).congr_fun _ measurableSet_Ioi
    intro t ht
    obtain ⟨ht₁,ht₂⟩ := hR t (le_of_lt ht)
    simp [realTraceIntegrand,ht₁,ht₂]
  exact (hsmall.union hlarge).mono_set (fun t ht => by
    by_cases htR : t ≤ R
    · exact Or.inl ⟨ht,htR⟩
    · exact Or.inr (lt_of_not_ge htR))

end MasulloRH

open MasulloRH

/-- The full explicit formula, with the spectral term split at the mission window. -/
theorem solution (α : ℝ) (φ : ℝ → ℂ) (hφ : IsRationalTraceTest φ) :
    let omitted := {ρ : {z : ℂ // ConnesRZ.IsCriticalZero z} | α ≤ |ρ.val.re - 1/2|}
    IntegrableOn (realTraceIntegrand φ) (Ioi 1) ∧ Summable (primePowerTraceTerm φ) ∧
    Summable (zetaTraceTerm φ α) ∧
    Summable (fun r : omitted => (ConnesRZ.zeroMult r.val.val : ℂ) * mellin φ (r.val.val - 1/2)) ∧
    (∑' i, primePowerTraceTerm φ i) + (∑' ρ, zetaTraceTerm φ α ρ) +
      (∑' r : omitted, (ConnesRZ.zeroMult r.val.val : ℂ) * mellin φ (r.val.val - 1/2)) =
    mellin φ (1/2) + mellin φ (-1/2) + ConnesRZ.archTerm (φ ∘ Real.exp) := by
  let Z := {z : ℂ // ConnesRZ.IsCriticalZero z}
  let inner : Set Z := {r | |r.val.re - 1/2| < α}
  let f := fun r : Z => (ConnesRZ.zeroMult r.val : ℂ) * mellin φ (r.val - 1/2)
  have hf : HasSum f (ConnesRZ.weilDistribution (φ ∘ Real.exp)) := by
    apply (ConnesRZ.explicit_formula _ (log_test hφ)).congr_fun
    intro r
    exact congrArg (_ * ·) (log_mellin φ r.val).symm
  let e : ZetaZerosInTraceStrip α ≃ inner :=
    { toFun := fun r => ⟨⟨r.val, r.prop.1, r.prop.2.1, r.prop.2.2.1⟩, r.prop.2.2.2⟩
      invFun := fun r => ⟨r.val.val, r.val.prop.1, r.val.prop.2.1, r.val.prop.2.2, r.prop⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hsplit := hf.summable.tsum_subtype_add_tsum_subtype_compl inner
  have hin := e.tsum_eq (fun r => f r.val)
  have hout : innerᶜ = {r : Z | α ≤ |r.val.re - 1/2|} := by ext; simp [inner]
  rw [hout, ← hin, hf.tsum_eq] at hsplit
  change _ + _ = ConnesRZ.mellinHat _ 0 + ConnesRZ.mellinHat _ 1 - ConnesRZ.primeSum _ + _ at hsplit
  rw [log_mellin φ 0, log_mellin φ 1, prime_reindex φ] at hsplit
  rw [show (0:ℂ)-1/2 = -1/2 by ring, show (1:ℂ)-1/2=1/2 by ring] at hsplit
  have hsum : Summable (f ∘ (Subtype.val ∘ e)) :=
    hf.summable.comp_injective (Subtype.val_injective.comp e.injective)
  have hrest := hf.summable.subtype (· ∈ innerᶜ)
  rw [hout] at hrest
  refine ⟨trace_real_integrable hφ, trace_prime_summable hφ, hsum, hrest, ?_⟩
  change _ + (∑' r, f (e r).val) + (∑' r : {r : Z | α ≤ |r.val.re - 1/2|}, f r.val) = _
  rw [add_assoc, hsplit]
  ring
