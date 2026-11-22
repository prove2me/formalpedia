-- Prove2me | solution 1 for MasulloGRH.finiteLocalZeta_integers_of_unramified
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T16:50:37.61978+00:00
-- url     : https://prove2.me/submissions/58abb7b0-81d8-41d4-923c-cdeea49d1772

import Mathlib
import Definitions.Def_MasulloGRH_SLocalTamagawaMeasures
import Theorems.Thm_MasulloGRH_finiteLocalMulTamagawa_isHaarMeasure_and_units

open MeasureTheory NumberField IsDedekindDomain

set_option autoImplicit false

open MasulloGRH

namespace Sol_MasulloGRH_finiteLocalZeta_integers_of_unramified

variable {F : Type*} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)}

/-- A sphere `{x ∈ F_vˣ | v(x) = γ}` with `γ ≠ 0` is open, hence Borel measurable. -/
lemma measurableSet_sphere (γ : WithZero (Multiplicative ℤ)) (hγ : γ ≠ 0) :
    MeasurableSet {x : (v.adicCompletion F)ˣ | Valued.v (x : v.adicCompletion F) = γ} := by
  have hopen : IsOpen {y : v.adicCompletion F | Valued.v y = γ} := by
    rw [isOpen_iff_mem_nhds]
    intro y hy
    have hy' : Valued.v y = γ := hy
    have h0 : (Valued.v y) ≠ 0 := by rw [hy']; exact hγ
    have := Valued.locally_const h0
    rw [hy'] at this
    exact this
  exact (hopen.preimage Units.continuous_val).measurableSet

end Sol_MasulloGRH_finiteLocalZeta_integers_of_unramified

open Sol_MasulloGRH_finiteLocalZeta_integers_of_unramified in
theorem solution
    (F : Type*) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (c : (v.adicCompletion F)ˣ → ℂ)
    (hmul : ∀ x y : (v.adicCompletion F)ˣ, c (x * y) = c x * c y)
    (hunr : ∀ u : (v.adicCompletion F)ˣ, Valued.v (u : v.adicCompletion F) = 1 → c u = 1)
    (ϖ : (v.adicCompletion F)ˣ) (hϖ : IsUniformizerAt v ϖ) (hσ : ‖c ϖ‖ < 1) :
    IntegrableOn c {x : (v.adicCompletion F)ˣ | Valued.v (x : v.adicCompletion F) ≤ 1}
      (finiteLocalMulTamagawa F v) ∧
    ∫ x in {x : (v.adicCompletion F)ˣ | Valued.v (x : v.adicCompletion F) ≤ 1}, c x
        ∂(finiteLocalMulTamagawa F v) =
      (((Real.sqrt ((Ideal.absNorm v.asIdeal : ℝ) ^
        multiplicity v.asIdeal (differentIdeal ℤ (𝓞 F))))⁻¹ : ℝ) : ℂ) * (1 - c ϖ)⁻¹ := by
  classical
  obtain ⟨hHaar, hU⟩ := finiteLocalMulTamagawa_isHaarMeasure_and_units F v
  have hϖv : Valued.v (ϖ : v.adicCompletion F) = WithZero.exp (-1 : ℤ) := hϖ
  -- the unit sphere and the spheres `v(x) = exp(-k)`
  obtain ⟨U, hUdef⟩ : ∃ U : Set (v.adicCompletion F)ˣ,
      U = {u : (v.adicCompletion F)ˣ | Valued.v (u : v.adicCompletion F) = 1} := ⟨_, rfl⟩
  obtain ⟨s, hsdef⟩ : ∃ s : ℕ → Set (v.adicCompletion F)ˣ,
      s = fun k : ℕ => {x : (v.adicCompletion F)ˣ |
        Valued.v (x : v.adicCompletion F) = WithZero.exp (-(k : ℤ))} :=
    ⟨_, rfl⟩
  have hmemU : ∀ x, x ∈ U ↔ Valued.v (x : v.adicCompletion F) = 1 := by
    intro x; rw [hUdef]; rfl
  have hmems : ∀ k x, x ∈ s k ↔ Valued.v (x : v.adicCompletion F) = WithZero.exp (-(k : ℤ)) := by
    intro k x; rw [hsdef]; rfl
  rw [← hUdef] at hU
  have hs_meas : ∀ k, MeasurableSet (s k) := by
    intro k
    rw [hsdef]
    exact measurableSet_sphere _ WithZero.exp_ne_zero
  have hs_disj : Pairwise (Function.onFun Disjoint s) := by
    intro i j hij
    rw [Function.onFun, Set.disjoint_left]
    intro x hxi hxj
    apply hij
    rw [hmems] at hxi hxj
    have h := hxi.symm.trans hxj
    rw [WithZero.exp_inj] at h
    omega
  have hx0 : ∀ x : (v.adicCompletion F)ˣ, Valued.v (x : v.adicCompletion F) ≠ 0 := by
    intro x
    rw [Ne, Valuation.zero_iff]
    exact x.ne_zero
  have hs_union : {x : (v.adicCompletion F)ˣ | Valued.v (x : v.adicCompletion F) ≤ 1} =
      ⋃ k, s k := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, hmems]
    constructor
    · intro hx
      refine ⟨(-(WithZero.log (Valued.v (x : v.adicCompletion F)))).toNat, ?_⟩
      have hlog : WithZero.log (Valued.v (x : v.adicCompletion F)) ≤ 0 := by
        rw [← WithZero.exp_le_exp, WithZero.exp_log (hx0 x), WithZero.exp_zero]
        exact hx
      rw [Int.toNat_of_nonneg (by omega), neg_neg, WithZero.exp_log (hx0 x)]
    · rintro ⟨k, hk⟩
      rw [hk, ← WithZero.exp_zero, WithZero.exp_le_exp]
      omega
  -- valuation of `ϖ⁻¹ ^ k * x`
  have hval : ∀ (k : ℕ) (x : (v.adicCompletion F)ˣ),
      Valued.v ((ϖ⁻¹ ^ k * x : (v.adicCompletion F)ˣ) : v.adicCompletion F) =
        WithZero.exp (k : ℤ) * Valued.v (x : v.adicCompletion F) := by
    intro k x
    rw [Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow, Units.val_inv_eq_inv_val,
      map_inv₀, hϖv, ← WithZero.exp_neg, neg_neg, ← WithZero.exp_nsmul, nsmul_eq_mul, mul_one]
  have hs_pre : ∀ k, s k = (fun h => ϖ⁻¹ ^ k * h) ⁻¹' U := by
    intro k
    ext x
    rw [Set.mem_preimage, hmems, hmemU, hval]
    constructor
    · intro hx
      rw [hx, ← WithZero.exp_add, add_neg_cancel, WithZero.exp_zero]
    · intro hx
      have h : WithZero.exp (-(k : ℤ)) *
          (WithZero.exp (k : ℤ) * Valued.v (x : v.adicCompletion F)) =
          WithZero.exp (-(k : ℤ)) * 1 := by rw [hx]
      rw [← mul_assoc, ← WithZero.exp_add, neg_add_cancel, WithZero.exp_zero, one_mul,
        mul_one] at h
      exact h
  have hμs : ∀ k, finiteLocalMulTamagawa F v (s k) = finiteLocalMulTamagawa F v U := by
    intro k
    rw [hs_pre k]
    exact measure_preimage_mul (finiteLocalMulTamagawa F v) _ U
  -- `c` is constant equal to `c ϖ ^ k` on the `k`-th sphere
  have hc1 : c 1 = 1 := hunr 1 (by simp)
  have hcpow : ∀ k : ℕ, c (ϖ ^ k) = c ϖ ^ k := by
    intro k
    induction k with
    | zero => simpa using hc1
    | succ n ih => rw [pow_succ, hmul, ih, pow_succ]
  have hc : ∀ k, ∀ x ∈ s k, c x = c ϖ ^ k := by
    intro k x hx
    have hxU : ϖ⁻¹ ^ k * x ∈ U := by
      rw [hs_pre k] at hx
      exact hx
    calc c x = c (ϖ ^ k * (ϖ⁻¹ ^ k * x)) := by
          rw [inv_pow, mul_inv_cancel_left]
      _ = c ϖ ^ k := by rw [hmul, hcpow, hunr _ ((hmemU _).1 hxU), mul_one]
  -- the measure of the units
  have hNpos : (0 : ℝ) < Real.sqrt ((Ideal.absNorm v.asIdeal : ℝ) ^
      multiplicity v.asIdeal (differentIdeal ℤ (𝓞 F))) := by
    apply Real.sqrt_pos.mpr
    apply pow_pos
    have h : Ideal.absNorm v.asIdeal ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff]
      exact v.ne_bot
    exact_mod_cast Nat.pos_of_ne_zero h
  have hUfin : finiteLocalMulTamagawa F v U ≠ ⊤ := by
    rw [hU]
    exact ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr hNpos).ne'
  have hUreal : (finiteLocalMulTamagawa F v).real U = (Real.sqrt ((Ideal.absNorm v.asIdeal : ℝ) ^
      multiplicity v.asIdeal (differentIdeal ℤ (𝓞 F))))⁻¹ := by
    rw [measureReal_def, hU, ENNReal.toReal_inv, ENNReal.toReal_ofReal hNpos.le]
  have hμrs : ∀ k, (finiteLocalMulTamagawa F v).real (s k) =
      (finiteLocalMulTamagawa F v).real U := by
    intro k
    rw [measureReal_def, measureReal_def, hμs k]
  -- integrability and integrals on each sphere
  have hint_k : ∀ k, IntegrableOn c (s k) (finiteLocalMulTamagawa F v) := by
    intro k
    have h1 : IntegrableOn (fun _ => c ϖ ^ k) (s k) (finiteLocalMulTamagawa F v) :=
      integrableOn_const (by rw [hμs k]; exact hUfin)
    exact h1.congr_fun (fun x hx => (hc k x hx).symm) (hs_meas k)
  have hintc : ∀ k, ∫ x in s k, c x ∂(finiteLocalMulTamagawa F v) =
      ((finiteLocalMulTamagawa F v).real U : ℂ) * c ϖ ^ k := by
    intro k
    rw [setIntegral_congr_fun (g := fun _ => c ϖ ^ k) (hs_meas k) (fun x hx => hc k x hx),
      setIntegral_const, hμrs k, Complex.real_smul]
  have hintn : ∀ k, ∫ x in s k, ‖c x‖ ∂(finiteLocalMulTamagawa F v) =
      (finiteLocalMulTamagawa F v).real U * ‖c ϖ‖ ^ k := by
    intro k
    rw [setIntegral_congr_fun (g := fun _ => ‖c ϖ‖ ^ k) (hs_meas k)
        (fun x hx => by simp only; rw [hc k x hx, norm_pow]),
      setIntegral_const, hμrs k, smul_eq_mul]
  have hsum : Summable fun k => ∫ x in s k, ‖c x‖ ∂(finiteLocalMulTamagawa F v) := by
    simp_rw [hintn]
    exact (summable_geometric_of_lt_one (norm_nonneg _) hσ).mul_left _
  have hintU : IntegrableOn c (⋃ k, s k) (finiteLocalMulTamagawa F v) :=
    integrableOn_iUnion_of_summable_integral_norm hint_k hsum
  rw [hs_union]
  refine ⟨hintU, ?_⟩
  rw [integral_iUnion hs_meas hs_disj hintU]
  simp_rw [hintc]
  rw [tsum_mul_left, tsum_geometric_of_norm_lt_one hσ, hUreal]
