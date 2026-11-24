-- Prove2me | solution 1 for GlobalTheory.HilbFam.ExpH.hasQ_hfun
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:57:44.869829+00:00
-- url     : https://prove2.me/submissions/81a8b94c-5845-4ec9-a858-9a5fe28e3c18

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasLevelStd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HilbertEisensteinLatticeJetSplitDirectionAddStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HilbertEisensteinCoeffSupportTraceFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasQExpansionOfLevelHilbertEisensteinQuasiPeriod
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
import Theorems.Thm_GlobalTheory_HilbFam_coef_support_trace
import Theorems.Thm_GlobalTheory_HilbFam_hasSum_jet_split
import Theorems.Thm_GlobalTheory_HilbFam_jet_split_add
import Theorems.Thm_GlobalTheory_QFam_hasQ_iff
import Theorems.Thm_GlobalTheory_WeightTwoSum_dz_apply
import Theorems.Thm_GlobalTheory_WeightTwoSum_dzbar_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub
attribute [local simp] GlobalTheory.WeightTwoSum.dz_apply
attribute [local simp] GlobalTheory.WeightTwoSum.dzbar_apply


section
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
namespace GlobalTheory.HilbFam.ExpH
set_option autoImplicit false in
open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
private lemma omegaFactor_ne_zero' {F : Type} [Field F] [NumberField F] (𝔞 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.omegaFactor 𝔞 ≠ 0 := by
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.omegaFactor _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.dF _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.nrm
  refine mul_ne_zero ?_ ?_
  · have h : (0:ℝ) < |((discr F : ℤ) : ℝ)| := by
      rw [abs_pos]; exact_mod_cast discr_ne_zero F
    positivity
  · rw [Rat.cast_ne_zero, Ne, FractionalIdeal.absNorm_eq_zero_iff]
    exact 𝔞.ne_zero
open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
private lemma norm_exp_two_pi_I_div_lt_one (N : ℕ) (hN : 0 < N) (τ : ℍ) :
    ‖Complex.exp (2 * ↑Real.pi * Complex.I * ↑τ / ↑N)‖ < 1 := by
  rw [Complex.norm_exp]
  simp [Complex.div_re]
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  apply div_neg_of_neg_of_pos
  · have := mul_pos (mul_pos two_pos Real.pi_pos) (mul_pos τ.im_pos hN')
    linarith
  · positivity
open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
private lemma summable_norm_qExpansion_of_hasSum_everywhere (N : ℕ) (hN : 0 < N) (b : ℕ → ℂ) (f : ℍ → ℂ)
    (h : ∀ τ : ℍ, HasSum (fun n => b n * Complex.exp (2 * ↑Real.pi * Complex.I * ↑τ / ↑N) ^ n) (f τ))
    (τ : ℍ) : Summable (fun n => ‖b n * Complex.exp (2 * ↑Real.pi * Complex.I * ↑τ / ↑N) ^ n‖) := by
  let σ : ℍ := ⟨(τ : ℂ) / 2, by simpa using div_pos τ.im_pos two_pos⟩
  set w := Complex.exp (2 * ↑Real.pi * Complex.I * ↑σ / ↑N) with hw
  have hq : Complex.exp (2 * ↑Real.pi * Complex.I * ↑τ / ↑N) = w ^ 2 := by
    rw [hw, ← Complex.exp_nat_mul]
    congr 1
    simp only [σ, UpperHalfPlane.coe_mk]
    push_cast
    ring
  have hw1 := norm_exp_two_pi_I_div_lt_one N hN σ
  rw [← hw] at hw1
  have ht := (h σ).summable.tendsto_cofinite_zero
  have hev : ∀ᶠ n in Filter.cofinite, ‖b n * w ^ n‖ ≤ 1 := by
    have := ht.norm
    rw [norm_zero] at this
    exact this.eventually (ge_mem_nhds one_pos)
  refine Summable.of_norm_bounded_eventually (g := fun n => ‖w‖ ^ n)
    (summable_geometric_of_lt_one (norm_nonneg _) hw1) ?_
  filter_upwards [hev] with n hn
  rw [norm_norm, hq, ← pow_mul, mul_comm 2 n, pow_mul, sq, ← mul_assoc, norm_mul, norm_pow]
  exact mul_le_of_le_one_left (by positivity) hn
open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
private lemma lag_zero_left_eq_pow (k n : ℕ) (y : ℂ) :
    _root_.GlobalTheory.HilbFam.lag k n 0 y = y ^ n := by
  unfold _root_.GlobalTheory.HilbFam.lag
  rw [Finset.sum_eq_single n]
  · simp [_root_.GlobalTheory.HilbFam.rco]
  · intro m hm hmn
    have : n - m ≠ 0 := by
      rw [Finset.mem_range] at hm
      omega
    simp [zero_pow this]
  · intro h
    exact absurd (Finset.self_mem_range_succ n) h
open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
private lemma hasSum_hilbertDiagonalTraceCoefficient_lemma_3 (F : Type) [Field F] [NumberField F]
    [IsTotallyReal F] (k : ℕ) (𝔞 𝔟 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) (a₀ : ℂ) (a : F → ℂ) (x : F)
    (N : ℕ) (hN : 0 < N) (hk : Even k) (ha : _root_.GlobalTheory.HilbFam.IsCoef k 𝔞 𝔟 a₀ a)
    (hlev : _root_.GlobalTheory.HilbFam.HasLevel N (_root_.GlobalTheory.HilbFam.split 𝔞 𝔟 x))
    (μ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℕ) (τ : ℍ) :
    HasSum (fun n => _root_.GlobalTheory.HilbFam.ecoef N a x μ n *
        Complex.exp (2 * ↑Real.pi * Complex.I * ↑τ / ↑N) ^ n)
      (_root_.GlobalTheory.HilbFam.jet k (_root_.GlobalTheory.HilbFam.split 𝔞 𝔟 x) μ τ 0
          (-(2 * Real.pi * Complex.I)) /
        (((2 * Real.pi * Complex.I) ^ Module.finrank ℚ F * (_root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.omegaFactor 𝔞 : ℂ)) ^ k *
          (-(2 * Real.pi * Complex.I) ^ 2) ^ (∑ i, μ i))) := by
  set P : ℂ := 2 * Real.pi * Complex.I with hP
  have hP0 : P ≠ 0 := by simp [hP, Real.pi_ne_zero, Complex.I_ne_zero]
  set C : ℂ := (P ^ Module.finrank ℚ F * (_root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.omegaFactor 𝔞 : ℂ)) ^ k with hC
  have hC0 : C ≠ 0 := pow_ne_zero _ (mul_ne_zero (pow_ne_zero _ hP0) (by exact_mod_cast omegaFactor_ne_zero' 𝔞))
  set q : ℂ := Complex.exp (2 * ↑Real.pi * Complex.I * ↑τ / ↑N) with hq
  let A : F → ℂ := fun ξ => a ξ * _root_.GlobalTheory.HilbFam.eTr (ξ * x) * ∏ i : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F, ((i ξ : ℝ) : ℂ) ^ μ i
  have h0 := (_root_.GlobalTheory.HilbFam.hasSum_jet_split F k 𝔞 𝔟 a₀ a x τ 0 (-P) μ hk ha τ.im_pos).div_const
    (C * (-P ^ 2) ^ (∑ i, μ i))
  rw [← hP, ← hC] at h0
  have hg : HasSum (fun ξ => A ξ * Complex.exp (P * ((Algebra.trace ℚ F ξ : ℚ) : ℂ) * τ)) _ :=
    h0.congr_fun fun ξ => by
      simp only [A, lag_zero_left_eq_pow]
      have hprod : ∏ i : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F, (P * ((i ξ : ℝ) : ℂ) * -P) ^ μ i =
          (-P ^ 2) ^ (∑ i, μ i) * ∏ i : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F, ((i ξ : ℝ) : ℂ) ^ μ i := by
        rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [← mul_pow]; ring_nf
      rw [hprod]
      have : (-P ^ 2) ^ (∑ i, μ i) ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr (pow_ne_zero _ hP0))
      field_simp
  obtain ⟨hint, hfin⟩ := _root_.GlobalTheory.HilbFam.coef_support_trace F k 𝔞 𝔟 a₀ a x N hN ha hlev
  let ν : F → ℕ := fun ξ => if h : ∃ n : ℕ, (N : ℚ) * Algebra.trace ℚ F ξ = n then h.choose else 0
  have hν : ∀ ξ, a ξ ≠ 0 → (N : ℚ) * Algebra.trace ℚ F ξ = ν ξ := by
    intro ξ hξ
    have h := hint ξ hξ
    simp only [ν, dif_pos h]
    exact h.choose_spec
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hgA : ∀ ξ, A ξ * Complex.exp (P * ((Algebra.trace ℚ F ξ : ℚ) : ℂ) * τ) = A ξ * q ^ ν ξ := by
    intro ξ
    by_cases hξ : a ξ = 0
    · simp [A, hξ]
    · have h := hν ξ hξ
      have h' : (N : ℂ) * ((Algebra.trace ℚ F ξ : ℚ) : ℂ) = (ν ξ : ℂ) := by exact_mod_cast h
      rw [hq, ← Complex.exp_nat_mul, ← h', hP]
      congr 2
      field_simp
      done
  replace hg := (hg.congr_fun fun ξ => (hgA ξ).symm).tsum_fiberwise ν
  refine hg.congr_fun fun m => ?_
  have hfib : ∑' ξ : ↑(ν ⁻¹' {m}), A ξ * q ^ ν ξ = (∑' ξ : ↑(ν ⁻¹' {m}), A ξ) * q ^ m := by
    rw [← tsum_mul_right]
    refine tsum_congr fun ξ => ?_
    rw [show ν ξ = m from ξ.2]
  rw [hfib]
  congr 1
  have hind : (ν ⁻¹' {m}).indicator A = {ξ | (N : ℚ) * Algebra.trace ℚ F ξ = m}.indicator A := by
    funext ξ
    by_cases hξ : a ξ = 0
    · simp only [Set.indicator_apply, A, hξ, zero_mul, ite_self]
    · have h := hν ξ hξ
      simp only [Set.indicator, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq, h]
      norm_cast
  unfold _root_.GlobalTheory.HilbFam.ecoef
  rw [tsum_subtype, finsum_mem_def, hind]
  refine (tsum_eq_finsum ?_).symm
  refine (hfin m).subset fun ξ hξ => ?_
  rw [Function.mem_support] at hξ
  by_cases hm : (N : ℚ) * Algebra.trace ℚ F ξ = m
  · refine ⟨fun h0 => hξ ?_, hm⟩
    simp [Set.indicator, A, h0]
  · exact absurd (by simp [Set.indicator, hm]) hξ
open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
private lemma hasSum_powerSeries_mul_of_absolutely_summable (A B : PowerSeries ℂ) (z x y : ℂ)
    (hA : HasSum (fun n => PowerSeries.coeff n A * z ^ n) x)
    (hA' : Summable (fun n => ‖PowerSeries.coeff n A * z ^ n‖))
    (hB : HasSum (fun n => PowerSeries.coeff n B * z ^ n) y)
    (hB' : Summable (fun n => ‖PowerSeries.coeff n B * z ^ n‖)) :
    HasSum (fun n => PowerSeries.coeff n (A * B) * z ^ n) (x * y) ∧
      Summable (fun n => ‖PowerSeries.coeff n (A * B) * z ^ n‖) := by
  have hpt : ∀ n, PowerSeries.coeff n (A * B) * z ^ n =
      ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n,
        (PowerSeries.coeff kl.1 A * z ^ kl.1) * (PowerSeries.coeff kl.2 B * z ^ kl.2) := by
    intro n
    rw [PowerSeries.coeff_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun kl hkl => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hkl
    rw [← hkl, pow_add]
    ring
  have hs := summable_norm_sum_mul_antidiagonal_of_summable_norm hA' hB'
  refine ⟨?_, hs.congr fun n => by rw [hpt n]⟩
  have := (Summable.of_norm hs).hasSum
  rw [← tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hA' hB', hA.tsum_eq, hB.tsum_eq] at this
  exact this.congr_fun hpt
open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
private lemma hasSum_powerSeries_pow_of_absolutely_summable (A : PowerSeries ℂ) (z x : ℂ)
    (hA : HasSum (fun n => PowerSeries.coeff n A * z ^ n) x)
    (hA' : Summable (fun n => ‖PowerSeries.coeff n A * z ^ n‖)) (m : ℕ) :
    HasSum (fun n => PowerSeries.coeff n (A ^ m) * z ^ n) (x ^ m) ∧
      Summable (fun n => ‖PowerSeries.coeff n (A ^ m) * z ^ n‖) := by
  induction m with
  | zero =>
    have h1 : (fun n => PowerSeries.coeff n (A ^ 0) * z ^ n) = fun n => if n = 0 then 1 else 0 := by
      funext n
      rw [pow_zero, PowerSeries.coeff_one]
      split_ifs with hn <;> simp [hn]
    rw [h1, pow_zero]
    refine ⟨?_, ?_⟩
    · convert hasSum_ite_eq 0 (1 : ℂ) using 1
    · exact (hasSum_ite_eq 0 (1 : ℝ)).summable.congr fun n => by split_ifs with hn <;> simp [hn]
  | succ m ih =>
    rw [pow_succ, pow_succ]
    exact hasSum_powerSeries_mul_of_absolutely_summable _ _ z _ _ ih.1 ih.2 hA hA'
end GlobalTheory.HilbFam.ExpH
end

set_option autoImplicit false
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory GlobalTheory.HilbFam GlobalTheory.HilbFam.ExpH
open NumberField UpperHalfPlane
open scoped Classical MatrixGroups nonZeroDivisors
namespace GlobalTheory.HilbFam.ExpH
namespace _root_.GlobalTheory.HilbFam.ExpH
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (𝔞 𝔟 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) (a₀ : ℂ) (a : F → ℂ) (x : F) (N : ℕ) (κ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℕ) (Ch : ℍ → ℂ) (c : ℕ → ℂ), 0 < N → Even k → _root_.GlobalTheory.HilbFam.IsCoef k 𝔞 𝔟 a₀ a → _root_.GlobalTheory.HilbFam.HasLevel N (_root_.GlobalTheory.HilbFam.split 𝔞 𝔟 x) → _root_.GlobalTheory.QFam.HasQ N Ch c → _root_.GlobalTheory.QFam.HasQ N (_root_.GlobalTheory.HilbFam.hfun k (_root_.GlobalTheory.HilbFam.split 𝔞 𝔟 x) κ Ch) (fun n ↦ PowerSeries.coeff n (_root_.GlobalTheory.HilbFam.hser k N 𝔞 a x κ c)) := by
  intro F _ _ _ k 𝔞 𝔟 a₀ a x N κ Ch c hN hk ha hlev hCh
  rw [_root_.GlobalTheory.QFam.hasQ_iff] at hCh ⊢
  intro τ
  set P : ℂ := 2 * Real.pi * Complex.I with hP
  have hP0 : P ≠ 0 := by simp [hP, Real.pi_ne_zero, Complex.I_ne_zero]
  set q : ℂ := Complex.exp (2 * ↑Real.pi * Complex.I * ↑τ / ↑N) with hq
  set C : ℂ := (P ^ Module.finrank ℚ F * (_root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.omegaFactor 𝔞 : ℂ)) ^ k with hC
  have hC0 : C ≠ 0 :=
    pow_ne_zero _ (mul_ne_zero (pow_ne_zero _ hP0) (by exact_mod_cast omegaFactor_ne_zero' 𝔞))
  let V : (_root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℕ) → ℂ := fun μ =>
    _root_.GlobalTheory.HilbFam.jet k (_root_.GlobalTheory.HilbFam.split 𝔞 𝔟 x) μ τ 0 (-P) /
      (C * (-P ^ 2) ^ (∑ i, μ i))
  have hc : HasSum (fun n => PowerSeries.coeff n (PowerSeries.mk c) * q ^ n) (Ch τ) := by
    simpa only [PowerSeries.coeff_mk] using hCh τ
  have hc' : Summable (fun n => ‖PowerSeries.coeff n (PowerSeries.mk c) * q ^ n‖) := by
    simpa only [PowerSeries.coeff_mk] using summable_norm_qExpansion_of_hasSum_everywhere N hN c Ch hCh τ
  have hterm : ∀ μ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℕ, HasSum (fun n => PowerSeries.coeff n
      ((PowerSeries.mk c ^ ∑ i, (κ i - μ i)) *
        PowerSeries.mk (_root_.GlobalTheory.HilbFam.ecoef N a x μ)) * q ^ n)
      (Ch τ ^ (∑ i, (κ i - μ i)) * V μ) := by
    intro μ
    have hD := fun σ : ℍ => hasSum_hilbertDiagonalTraceCoefficient_lemma_3 F k 𝔞 𝔟 a₀ a x N hN hk ha hlev μ σ
    have hD1 : HasSum (fun n => PowerSeries.coeff n
        (PowerSeries.mk (_root_.GlobalTheory.HilbFam.ecoef N a x μ)) * q ^ n) (V μ) := by
      simpa only [PowerSeries.coeff_mk] using hD τ
    have hD2 : Summable (fun n => ‖PowerSeries.coeff n
        (PowerSeries.mk (_root_.GlobalTheory.HilbFam.ecoef N a x μ)) * q ^ n‖) := by
      simpa only [PowerSeries.coeff_mk] using
        summable_norm_qExpansion_of_hasSum_everywhere N hN _ _ hD τ
    have hpow := hasSum_powerSeries_pow_of_absolutely_summable _ q _ hc hc' (∑ i, (κ i - μ i))
    exact (hasSum_powerSeries_mul_of_absolutely_summable _ _ q _ _ hpow.1 hpow.2 hD1 hD2).1
  have hs := (hasSum_sum (s := Finset.Iic κ) fun μ _ => (hterm μ).mul_left
    (((∏ i, _root_.GlobalTheory.HilbFam.rco k (κ i) (μ i) * (-1) ^ μ i : ℤ) : ℂ))).mul_left
    ((_root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.omegaFactor 𝔞 : ℂ) ^ k)
  suffices hv : _root_.GlobalTheory.HilbFam.hfun k (_root_.GlobalTheory.HilbFam.split 𝔞 𝔟 x) κ Ch τ =
      (_root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.omegaFactor 𝔞 : ℂ) ^ k * ∑ μ ∈ Finset.Iic κ,
        ((∏ i, _root_.GlobalTheory.HilbFam.rco k (κ i) (μ i) * (-1) ^ μ i : ℤ) : ℂ) *
          (Ch τ ^ (∑ i, (κ i - μ i)) * V μ) by
    rw [hv]
    refine hs.congr_fun fun n => ?_
    unfold _root_.GlobalTheory.HilbFam.hser
    simp only [PowerSeries.coeff_smul, map_sum, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun μ _ => ?_
    push_cast
    ring
  unfold _root_.GlobalTheory.HilbFam.hfun _root_.GlobalTheory.HilbFam.wt
  have hadd := _root_.GlobalTheory.HilbFam.jet_split_add F k 𝔞 𝔟 a₀ a x τ 0 (-P)
    (P ^ 2 * Ch τ) κ hk ha τ.im_pos
  rw [zero_add] at hadd
  rw [← hP, hadd, Finset.sum_div, Finset.mul_sum (Finset.Iic κ)]
  refine Finset.sum_congr rfl fun μ hμ => ?_
  rw [Finset.mem_Iic] at hμ
  have hsum : ∑ i, κ i = ∑ i, (κ i - μ i) + ∑ i, μ i := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => (Nat.sub_add_cancel (hμ i)).symm
  have hΩ : (_root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.omegaFactor 𝔞 : ℂ) ≠ 0 := by exact_mod_cast omegaFactor_ne_zero' 𝔞
  simp only [V]
  rw [hC]
  clear_value P
  have hm : (-P ^ 2) ^ (∑ i, μ i) ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr (pow_ne_zero _ hP0))
  push_cast
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hsum, neg_pow (P ^ 2)]
  field_simp
  ring
end _root_.GlobalTheory.HilbFam.ExpH
end GlobalTheory.HilbFam.ExpH
