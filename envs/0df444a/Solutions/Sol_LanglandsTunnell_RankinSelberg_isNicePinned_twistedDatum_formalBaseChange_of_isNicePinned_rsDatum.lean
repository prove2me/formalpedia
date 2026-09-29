-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.isNicePinned_twistedDatum_formalBaseChange_of_isNicePinned_rsDatum
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/a393d12f-3d5f-5647-ae5c-ba40bc944e9c

import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Theorems.Thm_LanglandsTunnell_RankinSelberg_rsEulerPoly_induced_eq_finprod_twist_formalBaseChange
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_isNicePinned_twistedDatum_formalBaseChange_of_isNicePinned_rsDatum

set_option autoImplicit false

open NumberField IsDedekindDomain AutomorphicForm LanglandsTunnell LanglandsTunnell.Converse LanglandsTunnell.RankinSelberg NumberField.TateGlobal

noncomputable section

namespace RsToBaseChangeTransport

variable (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]

private theorem quad_coeff_degree (x y : ℂ) :
    (Polynomial.C 1 - Polynomial.C x * Polynomial.X + Polynomial.C y * Polynomial.X ^ 2).coeff 0 = 1 ∧
    (Polynomial.C 1 - Polynomial.C x * Polynomial.X + Polynomial.C y * Polynomial.X ^ 2).natDegree ≤ 2 := by
  constructor
  · simp [Polynomial.coeff_X_pow, Polynomial.coeff_X_zero]
  · refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
    · refine (Polynomial.natDegree_sub_le _ _).trans (max_le (by simp) ?_)
      exact (Polynomial.natDegree_C_mul_le _ _).trans (Polynomial.natDegree_X_le.trans one_le_two)
    · exact Polynomial.natDegree_C_mul_X_pow_le y 2

private theorem wf_local (Φ : HeckeEigensystem ℚ ℂ) (T : Finset (HeightOneSpectrum (𝓞 K)))
    (archR : ∀ w : InfinitePlace K, w.IsReal → RealArchParam)
    (archC : ∀ w : InfinitePlace K, w.IsComplex → ComplexArchParam)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ) (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
    (uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ) (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ)
    (v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T}) :
    ((twistedDatum K (formalBaseChange ℚ K Φ) T archR archC μ uR aR uC kC).euler v).coeff 0 = 1 ∧
    ((twistedDatum K (formalBaseChange ℚ K Φ) T archR archC μ uR aR uC kC).euler v).natDegree ≤
      (twistedDatum K (formalBaseChange ℚ K Φ) T archR archC μ uR aR uC kC).degree ∧
    ((twistedDatum K (formalBaseChange ℚ K Φ) T archR archC μ uR aR uC kC).dual v).coeff 0 = 1 ∧
    ((twistedDatum K (formalBaseChange ℚ K Φ) T archR archC μ uR aR uC kC).dual v).natDegree ≤
      (twistedDatum K (formalBaseChange ℚ K Φ) T archR archC μ uR aR uC kC).degree := by
  classical
  by_cases hu : IsUnramifiedCharAt μ v.1
  · simp only [twistedDatum, hu, ↓reduceIte]
    exact ⟨(quad_coeff_degree _ _).1, (quad_coeff_degree _ _).2, (quad_coeff_degree _ _).1,
      (quad_coeff_degree _ _).2⟩
  · simp only [twistedDatum, hu, ↓reduceIte, Polynomial.coeff_C_zero, Polynomial.natDegree_C, zero_le, and_self]

private theorem norm_satakePow_le (a b : ℂ) (hb : ‖b‖ = 1) :
    ∀ n : ℕ, ‖satakePow n a b‖ ≤ 2 * (‖a‖ + 1) ^ n
  | 0 => by
      rw [satakePow_zero, pow_zero, mul_one]
      have h2 : (2 : ℂ) = 1 + 1 := by norm_num
      calc ‖(2 : ℂ)‖ = ‖(1 : ℂ) + 1‖ := by rw [h2]
        _ ≤ ‖(1 : ℂ)‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
        _ = 2 := by rw [norm_one]; norm_num
  | 1 => by
      rw [satakePow_one, pow_one]
      linarith [norm_nonneg a]
  | (n + 2) => by
      rw [satakePow_add_two]
      have h1 := norm_satakePow_le a b hb (n + 1)
      have h0 := norm_satakePow_le a b hb n
      have hA : 0 ≤ ‖a‖ := norm_nonneg a
      have hp : 0 ≤ (‖a‖ + 1) ^ n := by positivity
      have e1 : (‖a‖ + 1) ^ (n + 1) = (‖a‖ + 1) ^ n * (‖a‖ + 1) := by ring
      have e2 : (‖a‖ + 1) ^ (n + 2) = (‖a‖ + 1) ^ n * ((‖a‖ + 1) * (‖a‖ + 1)) := by ring
      calc ‖a * satakePow (n + 1) a b - b * satakePow n a b‖
          ≤ ‖a * satakePow (n + 1) a b‖ + ‖b * satakePow n a b‖ := norm_sub_le _ _
        _ = ‖a‖ * ‖satakePow (n + 1) a b‖ + ‖satakePow n a b‖ := by
            rw [norm_mul, norm_mul, hb, one_mul]
        _ ≤ ‖a‖ * (2 * (‖a‖ + 1) ^ (n + 1)) + 2 * (‖a‖ + 1) ^ n := by gcongr
        _ ≤ 2 * (‖a‖ + 1) ^ (n + 2) := by
            rw [e1, e2]
            nlinarith [mul_nonneg hA hp]

private theorem norm_eval_quadratic_sub_one_le (m m' A B x : ℂ) (hm : ‖m‖ = 1) (hm' : ‖m'‖ = 1) :
    ‖(Polynomial.C 1 - Polynomial.C (m * A) * Polynomial.X
        + Polynomial.C (m' * B) * Polynomial.X ^ 2).eval x - 1‖ ≤ ‖A‖ * ‖x‖ + ‖B‖ * ‖x‖ ^ 2 := by
  have h : (Polynomial.C 1 - Polynomial.C (m * A) * Polynomial.X
      + Polynomial.C (m' * B) * Polynomial.X ^ 2).eval x - 1 = m' * B * x ^ 2 - m * A * x := by
    simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, Polynomial.eval_pow]
    ring
  rw [h]
  calc ‖m' * B * x ^ 2 - m * A * x‖ ≤ ‖m' * B * x ^ 2‖ + ‖m * A * x‖ := norm_sub_le _ _
    _ = ‖B‖ * ‖x‖ ^ 2 + ‖A‖ * ‖x‖ := by
        rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_pow, hm, hm', one_mul, one_mul]
    _ = ‖A‖ * ‖x‖ + ‖B‖ * ‖x‖ ^ 2 := add_comm _ _

private theorem pow_le_mul_sq (w : ℝ) (hw : 0 ≤ w) (f : ℕ) (hf1 : 1 ≤ f) (hf3 : f ≤ 3) :
    w ^ f ≤ w * (1 + w) ^ 2 := by
  interval_cases f <;> nlinarith [mul_nonneg hw hw, mul_nonneg (mul_nonneg hw hw) hw]

private theorem bound_chain (α t : ℝ) (hα : 0 ≤ α) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (f : ℕ) (hf1 : 1 ≤ f)
    (hf3 : f ≤ 3) :
    2 * (α + 1) ^ f * t ^ f + (t ^ f) ^ 2 ≤ 3 * ((α * t + t) * (1 + (α * t + t)) ^ 2) := by
  have hw0 : 0 ≤ α * t + t := by positivity
  have htw : t ≤ α * t + t := by linarith [mul_nonneg hα ht0]
  have hpow : (α + 1) ^ f * t ^ f = (α * t + t) ^ f := by
    rw [← mul_pow]
    congr 1
    ring
  have h1 : (α * t + t) ^ f ≤ (α * t + t) * (1 + (α * t + t)) ^ 2 := pow_le_mul_sq _ hw0 f hf1 hf3
  have h2 : t ^ f ≤ (α * t + t) ^ f := by gcongr
  have h3 : t ^ f ≤ 1 := pow_le_one₀ ht0 ht1
  have h4 : (t ^ f) ^ 2 ≤ t ^ f := by
    have h0 : 0 ≤ t ^ f := pow_nonneg ht0 f
    nlinarith
  rw [mul_assoc, hpow]
  linarith

private theorem summable_cubic {ι : Type*} (w : ι → ℝ) (hw0 : ∀ i, 0 ≤ w i) (hw : Summable w) :
    Summable fun i => 3 * (w i * (1 + w i) ^ 2) := by
  have hev : ∀ᶠ i in Filter.cofinite, w i < 1 := by
    have h := Metric.tendsto_nhds.mp hw.tendsto_cofinite_zero 1 one_pos
    filter_upwards [h] with i hi
    rwa [Real.dist_eq, sub_zero, abs_of_nonneg (hw0 i)] at hi
  refine Summable.of_norm_bounded_eventually (hw.mul_left 12) ?_
  filter_upwards [hev] with i hi
  rw [Real.norm_of_nonneg (mul_nonneg (by norm_num) (mul_nonneg (hw0 i) (sq_nonneg _)))]
  nlinarith [hw0 i, hi, mul_nonneg (hw0 i) (sub_nonneg.2 hi.le),
    mul_nonneg (mul_nonneg (hw0 i) (sub_nonneg.2 hi.le)) (hw0 i)]

private theorem norm_inv_sub_one_le (z : ℂ) (hz : ‖z - 1‖ ≤ 1 / 2) : ‖z⁻¹ - 1‖ ≤ 2 * ‖z - 1‖ := by
  have h1 : 1 / 2 ≤ ‖z‖ := by
    have h := norm_sub_norm_le (1 : ℂ) z
    rw [norm_one, norm_sub_rev (1 : ℂ) z] at h
    linarith
  have hz0 : z ≠ 0 := by
    intro h
    rw [h, norm_zero] at h1
    norm_num at h1
  have h2 : z⁻¹ - 1 = (1 - z) / z := by
    rw [sub_div, div_self hz0, one_div]
  rw [h2, norm_div, norm_sub_rev (1 : ℂ) z, div_le_iff₀ (by linarith)]
  nlinarith [norm_nonneg (z - 1), mul_le_mul_of_nonneg_left h1 (norm_nonneg (z - 1))]

private theorem multipliable_inv_of_summable {ι : Type*} (F : ι → ℂ)
    (hF : Summable fun i => ‖F i - 1‖) : Multipliable fun i => (F i)⁻¹ := by
  have hev : ∀ᶠ i in Filter.cofinite, ‖F i - 1‖ ≤ 1 / 2 := by
    have h := Metric.tendsto_nhds.mp hF.tendsto_cofinite_zero (1 / 2) (by norm_num)
    filter_upwards [h] with i hi
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)] at hi
    exact hi.le
  have hS : Summable fun i => ‖(F i)⁻¹ - 1‖ := by
    refine Summable.of_norm_bounded_eventually (hF.mul_left 2) ?_
    filter_upwards [hev] with i hi
    rw [Real.norm_of_nonneg (norm_nonneg _)]
    exact norm_inv_sub_one_le (F i) hi
  exact (multipliable_one_add_of_summable hS).congr fun i => by ring

private theorem asIdeal_eq_span_absNorm (P : HeightOneSpectrum (𝓞 ℚ)) :
    P.asIdeal = Ideal.span {((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 ℚ)} := by
  have hn0 : Ideal.absNorm P.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact P.ne_bot
  have hnorm : Ideal.absNorm (Ideal.span {((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 ℚ)}) =
      Ideal.absNorm P.asIdeal := by
    simp [Ideal.absNorm_span_singleton, Algebra.norm_natCast, NumberField.RingOfIntegers.rank (K := ℚ)]
  obtain ⟨J, hJ⟩ := Ideal.dvd_iff_le.mpr (Ideal.span_singleton_absNorm_le P.asIdeal)
  have hJ1 : J = ⊤ := by
    rw [← Ideal.absNorm_eq_one_iff]
    have h := hnorm
    rw [hJ, map_mul] at h
    exact (mul_eq_left₀ hn0).mp h
  rw [hJ, hJ1, Ideal.mul_top]

private theorem absNorm_injective_rat :
    Function.Injective fun P : HeightOneSpectrum (𝓞 ℚ) => Ideal.absNorm P.asIdeal := by
  intro P Q h
  have h' : Ideal.absNorm P.asIdeal = Ideal.absNorm Q.asIdeal := h
  refine IsDedekindDomain.HeightOneSpectrum.ext ?_
  rw [asIdeal_eq_span_absNorm P, asIdeal_eq_span_absNorm Q, h']

private theorem summable_absNorm_rpow {τ : ℝ} (hτ : 1 < τ) :
    Summable fun p : HeightOneSpectrum (𝓞 ℚ) => (Ideal.absNorm p.asIdeal : ℝ) ^ (-τ) := by
  have h : Summable fun n : ℕ => (n : ℝ) ^ (-τ) := Real.summable_nat_rpow.mpr (by linarith)
  exact h.comp_injective absNorm_injective_rat

private theorem cpow_neg_of_eq_pow {N n f : ℕ} (h : N = n ^ f) (s : ℂ) :
    (N : ℂ) ^ (-s) = ((n : ℂ) ^ (-s)) ^ f := by
  subst h
  rw [Nat.cast_pow, ← Complex.natCast_cpow_natCast_mul, Complex.cpow_nat_mul]

private theorem fibre_data (hdeg : Module.finrank ℚ K = 3) (p : HeightOneSpectrum (𝓞 ℚ)) :
    ∃ Tf : Finset (HeightOneSpectrum (𝓞 K)),
      (∀ 𝔓 : HeightOneSpectrum (𝓞 K), 𝔓 ∈ Tf ↔ 𝔓.under (𝓞 ℚ) = p) ∧
      (∀ 𝔓 ∈ Tf, 1 ≤ (𝔓.under (𝓞 ℚ)).asIdeal.inertiaDeg' 𝔓.asIdeal ∧
        Ideal.absNorm 𝔓.asIdeal =
          Ideal.absNorm p.asIdeal ^ (𝔓.under (𝓞 ℚ)).asIdeal.inertiaDeg' 𝔓.asIdeal) ∧
      ∑ 𝔓 ∈ Tf, (𝔓.under (𝓞 ℚ)).asIdeal.inertiaDeg' 𝔓.asIdeal ≤ 3 := by
  classical

  have huniq : ∀ P Q : Algebra (𝓞 ℚ) (𝓞 K), P = Q := by
    intro P Q
    refine Algebra.algebra_ext P Q fun r => ?_
    have key : ∀ f g : 𝓞 ℚ →+* 𝓞 K, f = g := by
      intro f g
      have h := Subsingleton.elim (f.comp Rat.ringOfIntegersEquiv.symm.toRingHom)
        (g.comp Rat.ringOfIntegersEquiv.symm.toRingHom)
      refine RingHom.ext fun x => ?_
      obtain ⟨n, rfl⟩ := Rat.ringOfIntegersEquiv.symm.surjective x
      exact RingHom.congr_fun h n
    exact congrArg (fun φ => φ r) (key (@algebraMap _ _ _ _ P) (@algebraMap _ _ _ _ Q))
  obtain rfl : ‹Algebra (𝓞 ℚ) (𝓞 K)› = NumberField.inst_ringOfIntegersAlgebra ℚ K := huniq _ _
  haveI : p.asIdeal.IsMaximal := p.isMaximal
  have hfin : (primeFibre ℚ K p).Finite := by
    have h1 : (p.asIdeal.primesOver (𝓞 K)).Finite :=
      IsDedekindDomain.primesOver_finite p.asIdeal (𝓞 K)
    refine (h1.preimage (Set.injOn_of_injective (fun x y h =>
      IsDedekindDomain.HeightOneSpectrum.ext h))).subset ?_
    intro 𝔓 h𝔓
    rw [mem_primeFibre] at h𝔓
    refine ⟨𝔓.isPrime, ⟨?_⟩⟩
    rw [← h𝔓]
    rfl
  set T := hfin.toFinset with hT
  have hmem : ∀ 𝔓, 𝔓 ∈ T ↔ 𝔓.under (𝓞 ℚ) = p := fun 𝔓 => by
    rw [hT, Set.Finite.mem_toFinset, mem_primeFibre]
  have hlies : ∀ 𝔓 ∈ T, 𝔓.asIdeal.LiesOver p.asIdeal := fun 𝔓 h𝔓 =>
    ⟨by rw [← (hmem 𝔓).mp h𝔓]; rfl⟩
  refine ⟨T, hmem, fun 𝔓 h𝔓 => ?_, ?_⟩
  · haveI := hlies 𝔓 h𝔓
    rw [(hmem 𝔓).mp h𝔓]
    exact ⟨Ideal.inertiaDeg'_pos p.asIdeal 𝔓.asIdeal,
      Ideal.absNorm_eq_pow_inertiaDeg_of_liesOver 𝔓.asIdeal p.asIdeal p.isPrime p.ne_bot⟩
  · have hfund := Ideal.sum_ramification_inertia (𝓞 K) ℚ K (p := p.asIdeal) p.ne_bot
    rw [hdeg] at hfund
    have hinj : Set.InjOn (fun 𝔓 : HeightOneSpectrum (𝓞 K) => 𝔓.asIdeal) T :=
      fun x _ y _ h => IsDedekindDomain.HeightOneSpectrum.ext h
    calc ∑ 𝔓 ∈ T, (𝔓.under (𝓞 ℚ)).asIdeal.inertiaDeg' 𝔓.asIdeal
        = ∑ 𝔓 ∈ T, p.asIdeal.inertiaDeg' 𝔓.asIdeal :=
          Finset.sum_congr rfl fun 𝔓 h𝔓 => by rw [(hmem 𝔓).mp h𝔓]
      _ = ∑ P ∈ T.image (fun 𝔓 => 𝔓.asIdeal), p.asIdeal.inertiaDeg' P := by
          rw [Finset.sum_image hinj]
      _ ≤ ∑ P ∈ IsDedekindDomain.primesOverFinset p.asIdeal (𝓞 K), p.asIdeal.inertiaDeg' P := by
          refine Finset.sum_le_sum_of_subset fun P hP => ?_
          obtain ⟨𝔓, h𝔓, rfl⟩ := Finset.mem_image.mp hP
          rw [IsDedekindDomain.mem_primesOverFinset_iff p.ne_bot]
          exact ⟨𝔓.isPrime, hlies 𝔓 (Finset.mem_coe.mp h𝔓)⟩
      _ ≤ ∑ P ∈ IsDedekindDomain.primesOverFinset p.asIdeal (𝓞 K),
            p.asIdeal.ramificationIdx' P * p.asIdeal.inertiaDeg' P := by
          refine Finset.sum_le_sum fun P hP => ?_
          have hP' := (IsDedekindDomain.mem_primesOverFinset_iff p.ne_bot _).mp hP
          haveI : P.IsPrime := hP'.1
          haveI : P.LiesOver p.asIdeal := hP'.2
          exact Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero
            (Ideal.IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver P p.ne_bot))
      _ = 3 := hfund

private def fibreEquiv (SQ : Finset (HeightOneSpectrum (𝓞 ℚ))) (T : Finset (HeightOneSpectrum (𝓞 K)))
    (hfib : ∀ 𝔓 : HeightOneSpectrum (𝓞 K), 𝔓 ∈ T ↔ 𝔓.under (𝓞 ℚ) ∈ SQ)
    (Tf : HeightOneSpectrum (𝓞 ℚ) → Finset (HeightOneSpectrum (𝓞 K)))
    (hTf : ∀ p 𝔓, 𝔓 ∈ Tf p ↔ 𝔓.under (𝓞 ℚ) = p) :
    (Σ P : {p : HeightOneSpectrum (𝓞 ℚ) // p ∉ SQ}, ↥(Tf P.1)) ≃
      {v : HeightOneSpectrum (𝓞 K) // v ∉ T} where
  toFun x := ⟨x.2.1, fun h => x.1.2 (by
    rw [← (hTf x.1.1 x.2.1).mp x.2.2]
    exact (hfib x.2.1).mp h)⟩
  invFun v := ⟨⟨v.1.under (𝓞 ℚ), fun h => v.2 ((hfib v.1).mpr h)⟩, ⟨v.1, (hTf _ _).mpr rfl⟩⟩
  left_inv := by
    rintro ⟨⟨p, hp⟩, ⟨𝔓, h𝔓⟩⟩
    have h := (hTf p 𝔓).mp h𝔓
    subst h
    rfl
  right_inv := by
    rintro ⟨v, hv⟩
    rfl

omit [NumberField K] in

private theorem tprod_fibre (SQ : Finset (HeightOneSpectrum (𝓞 ℚ))) (T : Finset (HeightOneSpectrum (𝓞 K)))
    (hfib : ∀ 𝔓 : HeightOneSpectrum (𝓞 K), 𝔓 ∈ T ↔ 𝔓.under (𝓞 ℚ) ∈ SQ)
    (Tf : HeightOneSpectrum (𝓞 ℚ) → Finset (HeightOneSpectrum (𝓞 K)))
    (hTf : ∀ p 𝔓, 𝔓 ∈ Tf p ↔ 𝔓.under (𝓞 ℚ) = p)
    (G : HeightOneSpectrum (𝓞 K) → ℂ) (H : HeightOneSpectrum (𝓞 ℚ) → ℂ)
    (hG : Multipliable fun v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T} => G v.1)
    (hloc : ∀ p, ∏ 𝔓 ∈ Tf p, G 𝔓 = H p) :
    ∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T}, G v.1 =
      ∏' P : {p : HeightOneSpectrum (𝓞 ℚ) // p ∉ SQ}, H P.1 := by
  have h1 : HasProd ((fun v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T} => G v.1) ∘
      fibreEquiv K SQ T hfib Tf hTf) (∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T}, G v.1) :=
    (fibreEquiv K SQ T hfib Tf hTf).hasProd_iff.mpr hG.hasProd
  have h2 : ∀ P : {p : HeightOneSpectrum (𝓞 ℚ) // p ∉ SQ},
      HasProd (fun c : ↥(Tf P.1) => ((fun v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T} => G v.1) ∘
        fibreEquiv K SQ T hfib Tf hTf) ⟨P, c⟩) (H P.1) := by
    intro P
    have h := hasProd_fintype fun c : ↥(Tf P.1) => G c.1
    rw [Finset.prod_coe_sort (s := Tf P.1) (f := G), hloc P.1] at h
    exact h
  exact ((h1.sigma h2).tprod_eq).symm

omit [NumberField K] in

private theorem summable_comp_under (SQ : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (T : Finset (HeightOneSpectrum (𝓞 K)))
    (hfib : ∀ 𝔓 : HeightOneSpectrum (𝓞 K), 𝔓 ∈ T ↔ 𝔓.under (𝓞 ℚ) ∈ SQ)
    (Tf : HeightOneSpectrum (𝓞 ℚ) → Finset (HeightOneSpectrum (𝓞 K)))
    (hTf : ∀ p 𝔓, 𝔓 ∈ Tf p ↔ 𝔓.under (𝓞 ℚ) = p) (hcard : ∀ p, (Tf p).card ≤ 3)
    (V : HeightOneSpectrum (𝓞 ℚ) → ℝ) (hV0 : ∀ p, 0 ≤ V p) (hV : Summable V) :
    Summable fun v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T} => V (v.1.under (𝓞 ℚ)) := by
  have hF : Summable fun x : (Σ P : {p : HeightOneSpectrum (𝓞 ℚ) // p ∉ SQ}, ↥(Tf P.1)) =>
      V x.1.1 := by
    refine (summable_sigma_of_nonneg fun x => hV0 _).mpr ⟨fun P => Summable.of_finite, ?_⟩
    show Summable fun P : {p : HeightOneSpectrum (𝓞 ℚ) // p ∉ SQ} => ∑' _c : ↥(Tf P.1), V P.1
    refine Summable.of_nonneg_of_le (fun P => tsum_nonneg fun _ => hV0 _) (fun P => ?_)
      ((hV.comp_injective Subtype.val_injective).mul_left 3)
    show (∑' _c : ↥(Tf P.1), V P.1) ≤ 3 * V P.1
    rw [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard P.1) (hV0 _)
  refine (fibreEquiv K SQ T hfib Tf hTf).summable_iff.mp (hF.congr ?_)
  rintro ⟨P, c⟩
  show V P.1 = V (c.1.under (𝓞 ℚ))
  rw [(hTf P.1 c.1).mp c.2]

open scoped Classical in

private def twFactor (Φ : HeckeEigensystem ℚ ℂ) (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (𝔓 : HeightOneSpectrum (𝓞 K)) : Polynomial ℂ :=
  if IsUnramifiedCharAt μ 𝔓
  then Polynomial.C 1
    - Polynomial.C (((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) * (formalBaseChange ℚ K Φ).a 𝔓) * Polynomial.X
    + Polynomial.C ((((μ (uniformizerIdele K 𝔓))^2 : ℂˣ) : ℂ) * (formalBaseChange ℚ K Φ).b 𝔓)
      * Polynomial.X ^ 2
  else Polynomial.C 1

open scoped Classical in

private def twFactorDual (Φ : HeckeEigensystem ℚ ℂ) (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (𝔓 : HeightOneSpectrum (𝓞 K)) : Polynomial ℂ :=
  if IsUnramifiedCharAt μ 𝔓
  then Polynomial.C 1
    - Polynomial.C ((((μ (uniformizerIdele K 𝔓))⁻¹ : ℂˣ) : ℂ)
        * ((formalBaseChange ℚ K Φ).a 𝔓 / (formalBaseChange ℚ K Φ).b 𝔓)) * Polynomial.X
    + Polynomial.C ((((μ (uniformizerIdele K 𝔓))^(-2 : ℤ) : ℂˣ) : ℂ) * ((formalBaseChange ℚ K Φ).b 𝔓)⁻¹)
      * Polynomial.X ^ 2
  else Polynomial.C 1

private theorem norm_twFactor_sub_one_le (Φ : HeckeEigensystem ℚ ℂ) (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (hμ : ∀ x, ‖((μ x : ℂˣ) : ℂ)‖ = 1) (𝔓 : HeightOneSpectrum (𝓞 K))
    (hb𝔓 : ‖Φ.b (𝔓.under (𝓞 ℚ))‖ = 1) (x : ℂ) :
    ‖(twFactor K Φ μ 𝔓).eval x - 1‖ ≤
        2 * (‖Φ.a (𝔓.under (𝓞 ℚ))‖ + 1) ^ ((𝔓.under (𝓞 ℚ)).asIdeal.inertiaDeg' 𝔓.asIdeal) * ‖x‖
          + ‖x‖ ^ 2 ∧
      ‖(twFactorDual K Φ μ 𝔓).eval x - 1‖ ≤
        2 * (‖Φ.a (𝔓.under (𝓞 ℚ))‖ + 1) ^ ((𝔓.under (𝓞 ℚ)).asIdeal.inertiaDeg' 𝔓.asIdeal) * ‖x‖
          + ‖x‖ ^ 2 := by
  have hA : ‖(formalBaseChange ℚ K Φ).a 𝔓‖ ≤
      2 * (‖Φ.a (𝔓.under (𝓞 ℚ))‖ + 1) ^ ((𝔓.under (𝓞 ℚ)).asIdeal.inertiaDeg' 𝔓.asIdeal) := by
    rw [formalBaseChange_a]
    exact norm_satakePow_le _ _ hb𝔓 _
  have hB : ‖(formalBaseChange ℚ K Φ).b 𝔓‖ = 1 := by
    rw [formalBaseChange_b, norm_pow, hb𝔓, one_pow]
  by_cases hu : IsUnramifiedCharAt μ 𝔓
  · constructor
    · simp only [twFactor, hu, ↓reduceIte]
      refine (norm_eval_quadratic_sub_one_le _ _ _ _ x (hμ _) (by simp [hμ])).trans ?_
      rw [hB, one_mul]
      gcongr
    · simp only [twFactorDual, hu, ↓reduceIte]
      refine (norm_eval_quadratic_sub_one_le _ _ _ _ x (by simp [hμ]) (by simp [hμ])).trans ?_
      rw [norm_div, hB, div_one, norm_inv, hB, inv_one, one_mul]
      gcongr
  · simp only [twFactor, twFactorDual, hu, ↓reduceIte, Polynomial.eval_C, sub_self, norm_zero]
    constructor <;> positivity

open scoped Classical in

private theorem eval_rs_eq_prod (hdeg : Module.finrank ℚ K = 3) (Φ : HeckeEigensystem ℚ ℂ)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (p : HeightOneSpectrum (𝓞 ℚ)) (Tf : Finset (HeightOneSpectrum (𝓞 K)))
    (hTf : ∀ 𝔓 : HeightOneSpectrum (𝓞 K), 𝔓 ∈ Tf ↔ 𝔓.under (𝓞 ℚ) = p)
    (hN : ∀ 𝔓 ∈ Tf, Ideal.absNorm 𝔓.asIdeal =
      Ideal.absNorm p.asIdeal ^ (𝔓.under (𝓞 ℚ)).asIdeal.inertiaDeg' 𝔓.asIdeal) (s : ℂ) :
    (rsEulerPoly (Φ.a p) (Φ.b p)
        (inducedE1 ℚ (fun 𝔓 => if IsUnramifiedCharAt μ 𝔓 then ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) else 0) p)
        (inducedE2 ℚ (fun 𝔓 => if IsUnramifiedCharAt μ 𝔓 then ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) else 0) p)
        (inducedE3 ℚ (fun 𝔓 => if IsUnramifiedCharAt μ 𝔓 then ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) else 0)
          p)).eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
      ∏ 𝔓 ∈ Tf, (twFactor K Φ μ 𝔓).eval ((Ideal.absNorm 𝔓.asIdeal : ℂ) ^ (-s)) ∧
    (rsEulerPoly (Φ.a p / Φ.b p) (Φ.b p)⁻¹
        (inducedE1 ℚ
          (fun 𝔓 => (if IsUnramifiedCharAt μ 𝔓 then ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) else 0)⁻¹) p)
        (inducedE2 ℚ
          (fun 𝔓 => (if IsUnramifiedCharAt μ 𝔓 then ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) else 0)⁻¹) p)
        (inducedE3 ℚ
          (fun 𝔓 => (if IsUnramifiedCharAt μ 𝔓 then ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) else 0)⁻¹)
          p)).eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
      ∏ 𝔓 ∈ Tf, (twFactorDual K Φ μ 𝔓).eval ((Ideal.absNorm 𝔓.asIdeal : ℂ) ^ (-s)) := by
  have hRID := LanglandsTunnell.RankinSelberg.rsEulerPoly_induced_eq_finprod_twist_formalBaseChange
    K hdeg Φ μ p
  have hfin : (primeFibre ℚ K p).Finite := by
    refine Tf.finite_toSet.subset fun 𝔓 h => ?_
    rw [Finset.mem_coe, hTf]
    exact h
  have hset : hfin.toFinset = Tf := by
    ext 𝔓
    rw [Set.Finite.mem_toFinset, mem_primeFibre, hTf]
  have hx : ∀ 𝔓 ∈ Tf, (Ideal.absNorm 𝔓.asIdeal : ℂ) ^ (-s) =
      ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) ^ ((𝔓.under (𝓞 ℚ)).asIdeal.inertiaDeg' 𝔓.asIdeal) :=
    fun 𝔓 h𝔓 => cpow_neg_of_eq_pow (hN 𝔓 h𝔓) s
  refine ⟨?_, ?_⟩
  · rw [hRID.1, finprod_mem_eq_finite_toFinset_prod _ hfin, hset, Polynomial.eval_prod]
    refine Finset.prod_congr rfl fun 𝔓 h𝔓 => ?_
    rw [hx 𝔓 h𝔓]
    by_cases hu : IsUnramifiedCharAt μ 𝔓
    · simp only [twFactor, hu, ↓reduceIte, Polynomial.eval_add, Polynomial.eval_sub,
        Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_pow, pow_mul']
    · simp only [twFactor, hu, ↓reduceIte, Polynomial.eval_C]
  · rw [hRID.2, finprod_mem_eq_finite_toFinset_prod _ hfin, hset, Polynomial.eval_prod]
    refine Finset.prod_congr rfl fun 𝔓 h𝔓 => ?_
    rw [hx 𝔓 h𝔓]
    by_cases hu : IsUnramifiedCharAt μ 𝔓
    · simp only [twFactorDual, hu, ↓reduceIte, Polynomial.eval_add, Polynomial.eval_sub,
        Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_pow, pow_mul']
    · simp only [twFactorDual, hu, ↓reduceIte, Polynomial.eval_C]

private theorem summable_twisted (hdeg : Module.finrank ℚ K = 3) (Φ : HeckeEigensystem ℚ ℂ)
    (SQ : Finset (HeightOneSpectrum (𝓞 ℚ))) (T : Finset (HeightOneSpectrum (𝓞 K)))
    (hfib : ∀ 𝔓 : HeightOneSpectrum (𝓞 K), 𝔓 ∈ T ↔ 𝔓.under (𝓞 ℚ) ∈ SQ)
    (hb : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ → ‖Φ.b p‖ = 1)
    (ha : ∀ σ : ℝ, 1 < σ →
      Summable fun p : HeightOneSpectrum (𝓞 ℚ) => ‖Φ.a p‖ * (Ideal.absNorm p.asIdeal : ℝ) ^ (-σ))
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hμ : ∀ x, ‖((μ x : ℂˣ) : ℂ)‖ = 1)
    (D : LDatum {v : HeightOneSpectrum (𝓞 K) // v ∉ T})
    (hE : ∀ v, D.euler v = twFactor K Φ μ v.1) (hEd : ∀ v, D.dual v = twFactorDual K Φ μ v.1)
    (hn : ∀ v, D.norm v = Ideal.absNorm v.1.asIdeal) (s : ℂ) (hs : 1 < s.re) :
    (Summable fun v => ‖(D.euler v).eval ((D.norm v : ℂ) ^ (-s)) - 1‖) ∧
      (Summable fun v => ‖(D.dual v).eval ((D.norm v : ℂ) ^ (-s)) - 1‖) := by
  simp only [hE, hEd, hn]
  choose Tf hTf using fibre_data K hdeg
  have hcard : ∀ p, (Tf p).card ≤ 3 := fun p =>
    calc (Tf p).card = ∑ _𝔓 ∈ Tf p, 1 := Finset.card_eq_sum_ones _
      _ ≤ ∑ 𝔓 ∈ Tf p, (𝔓.under (𝓞 ℚ)).asIdeal.inertiaDeg' 𝔓.asIdeal :=
          Finset.sum_le_sum fun 𝔓 h => ((hTf p).2.1 𝔓 h).1
      _ ≤ 3 := (hTf p).2.2
  have hpos : ∀ p : HeightOneSpectrum (𝓞 ℚ), 0 < Ideal.absNorm p.asIdeal := fun p =>
    Nat.pos_of_ne_zero (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact p.ne_bot)
  have ht_eq : ∀ p : HeightOneSpectrum (𝓞 ℚ),
      ‖(Ideal.absNorm p.asIdeal : ℂ) ^ (-s)‖ = (Ideal.absNorm p.asIdeal : ℝ) ^ (-s.re) := fun p => by
    rw [Complex.norm_natCast_cpow_of_pos (hpos p), Complex.neg_re]
  have ht1 : ∀ p : HeightOneSpectrum (𝓞 ℚ), ‖(Ideal.absNorm p.asIdeal : ℂ) ^ (-s)‖ ≤ 1 := fun p => by
    rw [ht_eq]
    exact Real.rpow_le_one_of_one_le_of_nonpos (Nat.one_le_cast.mpr (hpos p)) (by linarith)
  have hw : Summable fun p : HeightOneSpectrum (𝓞 ℚ) =>
      ‖Φ.a p‖ * ‖(Ideal.absNorm p.asIdeal : ℂ) ^ (-s)‖ + ‖(Ideal.absNorm p.asIdeal : ℂ) ^ (-s)‖ := by
    simp only [ht_eq]
    exact (ha s.re hs).add (summable_absNorm_rpow hs)
  have hV := summable_cubic _ (fun p => by positivity) hw
  have hG := summable_comp_under K SQ T hfib Tf (fun p => (hTf p).1) hcard _ (fun p => by positivity) hV
  have key : ∀ v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
      2 * (‖Φ.a (v.1.under (𝓞 ℚ))‖ + 1) ^ ((v.1.under (𝓞 ℚ)).asIdeal.inertiaDeg' v.1.asIdeal) *
          ‖(Ideal.absNorm v.1.asIdeal : ℂ) ^ (-s)‖ + ‖(Ideal.absNorm v.1.asIdeal : ℂ) ^ (-s)‖ ^ 2 ≤
        3 * ((‖Φ.a (v.1.under (𝓞 ℚ))‖ * ‖(Ideal.absNorm (v.1.under (𝓞 ℚ)).asIdeal : ℂ) ^ (-s)‖ +
              ‖(Ideal.absNorm (v.1.under (𝓞 ℚ)).asIdeal : ℂ) ^ (-s)‖) *
            (1 + (‖Φ.a (v.1.under (𝓞 ℚ))‖ * ‖(Ideal.absNorm (v.1.under (𝓞 ℚ)).asIdeal : ℂ) ^ (-s)‖ +
              ‖(Ideal.absNorm (v.1.under (𝓞 ℚ)).asIdeal : ℂ) ^ (-s)‖)) ^ 2) := by
    intro v
    have hmem : v.1 ∈ Tf (v.1.under (𝓞 ℚ)) := ((hTf _).1 v.1).mpr rfl
    obtain ⟨hf1, hN⟩ := (hTf (v.1.under (𝓞 ℚ))).2.1 v.1 hmem
    have hf3 : (v.1.under (𝓞 ℚ)).asIdeal.inertiaDeg' v.1.asIdeal ≤ 3 :=
      (Finset.single_le_sum (fun 𝔓 _ => Nat.zero_le _) hmem).trans (hTf (v.1.under (𝓞 ℚ))).2.2
    have hx : ‖(Ideal.absNorm v.1.asIdeal : ℂ) ^ (-s)‖ =
        ‖(Ideal.absNorm (v.1.under (𝓞 ℚ)).asIdeal : ℂ) ^ (-s)‖ ^
          ((v.1.under (𝓞 ℚ)).asIdeal.inertiaDeg' v.1.asIdeal) := by
      rw [cpow_neg_of_eq_pow hN s, norm_pow]
    rw [hx]
    exact bound_chain _ _ (norm_nonneg _) (norm_nonneg _) (ht1 _) _ hf1 hf3
  have hbv : ∀ v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T}, ‖Φ.b (v.1.under (𝓞 ℚ))‖ = 1 :=
    fun v => hb _ fun h => v.2 ((hfib v.1).mpr h)
  exact ⟨Summable.of_nonneg_of_le (fun v => norm_nonneg _)
      (fun v => (norm_twFactor_sub_one_le K Φ μ hμ v.1 (hbv v) _).1.trans (key v)) hG,
    Summable.of_nonneg_of_le (fun v => norm_nonneg _)
      (fun v => (norm_twFactor_sub_one_le K Φ μ hμ v.1 (hbv v) _).2.trans (key v)) hG⟩

open scoped Classical in

private theorem lfun_eq (hdeg : Module.finrank ℚ K = 3) (Φ : HeckeEigensystem ℚ ℂ)
    (SQ : Finset (HeightOneSpectrum (𝓞 ℚ))) (T : Finset (HeightOneSpectrum (𝓞 K)))
    (hfib : ∀ 𝔓 : HeightOneSpectrum (𝓞 K), 𝔓 ∈ T ↔ 𝔓.under (𝓞 ℚ) ∈ SQ)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (D : LDatum {v : HeightOneSpectrum (𝓞 K) // v ∉ T})
    (hE : ∀ v, D.euler v = twFactor K Φ μ v.1) (hEd : ∀ v, D.dual v = twFactorDual K Φ μ v.1)
    (hn : ∀ v, D.norm v = Ideal.absNorm v.1.asIdeal) (s : ℂ)
    (hS : Summable fun v => ‖(D.euler v).eval ((D.norm v : ℂ) ^ (-s)) - 1‖)
    (hSd : Summable fun v => ‖(D.dual v).eval ((D.norm v : ℂ) ^ (-s)) - 1‖) :
    D.LFun s = (rsDatum ℚ SQ Φ.a Φ.b
        (fun 𝔓 => if IsUnramifiedCharAt μ 𝔓 then ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) else 0)
        D.gammaR D.gammaC D.gammaRDual D.gammaCDual).LFun s ∧
      D.LFunDual s = (rsDatum ℚ SQ Φ.a Φ.b
        (fun 𝔓 => if IsUnramifiedCharAt μ 𝔓 then ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) else 0)
        D.gammaR D.gammaC D.gammaRDual D.gammaCDual).LFunDual s := by
  choose Tf hTf using fibre_data K hdeg
  have hTf1 : ∀ p 𝔓, 𝔓 ∈ Tf p ↔ 𝔓.under (𝓞 ℚ) = p := fun p => (hTf p).1
  have hloc := fun p => eval_rs_eq_prod K hdeg Φ μ p (Tf p) (hTf p).1
    (fun 𝔓 h => ((hTf p).2.1 𝔓 h).2) s
  simp only [hE, hn] at hS
  simp only [hEd, hn] at hSd
  simp only [LDatum.LFun, LDatum.LFunDual, hE, hEd, hn, rsDatum]
  exact ⟨tprod_fibre K SQ T hfib Tf hTf1
      (fun 𝔓 => ((twFactor K Φ μ 𝔓).eval ((Ideal.absNorm 𝔓.asIdeal : ℂ) ^ (-s)))⁻¹)
      (fun p => ((rsEulerPoly (Φ.a p) (Φ.b p)
        (inducedE1 ℚ (fun 𝔓 => if IsUnramifiedCharAt μ 𝔓 then ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) else 0) p)
        (inducedE2 ℚ (fun 𝔓 => if IsUnramifiedCharAt μ 𝔓 then ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) else 0) p)
        (inducedE3 ℚ (fun 𝔓 => if IsUnramifiedCharAt μ 𝔓 then ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) else 0)
          p)).eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)))⁻¹)
      (multipliable_inv_of_summable _ hS)
      (fun p => by rw [Finset.prod_inv_distrib]; exact congrArg Inv.inv (hloc p).1.symm),
    tprod_fibre K SQ T hfib Tf hTf1
      (fun 𝔓 => ((twFactorDual K Φ μ 𝔓).eval ((Ideal.absNorm 𝔓.asIdeal : ℂ) ^ (-s)))⁻¹)
      (fun p => ((rsEulerPoly (Φ.a p / Φ.b p) (Φ.b p)⁻¹
        (inducedE1 ℚ
          (fun 𝔓 => (if IsUnramifiedCharAt μ 𝔓 then ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) else 0)⁻¹) p)
        (inducedE2 ℚ
          (fun 𝔓 => (if IsUnramifiedCharAt μ 𝔓 then ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) else 0)⁻¹) p)
        (inducedE3 ℚ
          (fun 𝔓 => (if IsUnramifiedCharAt μ 𝔓 then ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) else 0)⁻¹)
          p)).eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)))⁻¹)
      (multipliable_inv_of_summable _ hSd)
      (fun p => by rw [Finset.prod_inv_distrib]; exact congrArg Inv.inv (hloc p).2.symm)⟩

open scoped Classical in

private theorem analytic (hdeg : Module.finrank ℚ K = 3) (Φ : HeckeEigensystem ℚ ℂ)
    (SQ : Finset (HeightOneSpectrum (𝓞 ℚ))) (T : Finset (HeightOneSpectrum (𝓞 K)))
    (hfib : ∀ 𝔓 : HeightOneSpectrum (𝓞 K), 𝔓 ∈ T ↔ 𝔓.under (𝓞 ℚ) ∈ SQ)
    (hb : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ → ‖Φ.b p‖ = 1)
    (ha : ∀ σ : ℝ, 1 < σ →
      Summable fun p : HeightOneSpectrum (𝓞 ℚ) => ‖Φ.a p‖ * (Ideal.absNorm p.asIdeal : ℝ) ^ (-σ))
    (archR : ∀ w : InfinitePlace K, w.IsReal → RealArchParam)
    (archC : ∀ w : InfinitePlace K, w.IsComplex → ComplexArchParam)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hadm : IsAdmissibleTwist K μ)
    (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ) (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
    (uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ) (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ)
    (hConv : (rsDatum ℚ SQ Φ.a Φ.b
        (fun 𝔓 => if IsUnramifiedCharAt μ 𝔓 then ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) else 0)
        (twistedGammaR K archR uR aR) (twistedGammaC K archR archC uR aR uC kC)
        (twistedGammaR K (fun w hw => (archR w hw).dual) (fun w hw => -uR w hw) aR)
        (twistedGammaC K (fun w hw => (archR w hw).dual) (fun w hw => (archC w hw).dual)
          (fun w hw => -uR w hw) aR (fun w hw => -uC w hw) (fun w hw => -kC w hw))).Converges) :
    (twistedDatum K (formalBaseChange ℚ K Φ) T archR archC μ uR aR uC kC).Converges ∧
    (∀ s : ℂ, 1 < s.re →
      (twistedDatum K (formalBaseChange ℚ K Φ) T archR archC μ uR aR uC kC).LFun s =
        (rsDatum ℚ SQ Φ.a Φ.b
          (fun 𝔓 => if IsUnramifiedCharAt μ 𝔓 then ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) else 0)
          (twistedGammaR K archR uR aR) (twistedGammaC K archR archC uR aR uC kC)
          (twistedGammaR K (fun w hw => (archR w hw).dual) (fun w hw => -uR w hw) aR)
          (twistedGammaC K (fun w hw => (archR w hw).dual) (fun w hw => (archC w hw).dual)
            (fun w hw => -uR w hw) aR (fun w hw => -uC w hw) (fun w hw => -kC w hw))).LFun s ∧
      (twistedDatum K (formalBaseChange ℚ K Φ) T archR archC μ uR aR uC kC).LFunDual s =
        (rsDatum ℚ SQ Φ.a Φ.b
          (fun 𝔓 => if IsUnramifiedCharAt μ 𝔓 then ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) else 0)
          (twistedGammaR K archR uR aR) (twistedGammaC K archR archC uR aR uC kC)
          (twistedGammaR K (fun w hw => (archR w hw).dual) (fun w hw => -uR w hw) aR)
          (twistedGammaC K (fun w hw => (archR w hw).dual) (fun w hw => (archC w hw).dual)
            (fun w hw => -uR w hw) aR (fun w hw => -uC w hw) (fun w hw => -kC w hw))).LFunDual s) := by
  obtain ⟨-, -, hμ⟩ := hadm
  have hμ' : ∀ x, ‖((μ x : ℂˣ) : ℂ)‖ = 1 := hμ
  have hsum := fun (s : ℂ) (hs : 1 < s.re) =>
    summable_twisted K hdeg Φ SQ T hfib hb ha μ hμ'
      (twistedDatum K (formalBaseChange ℚ K Φ) T archR archC μ uR aR uC kC)
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) s hs
  have hL := fun (s : ℂ) (hs : 1 < s.re) =>
    lfun_eq K hdeg Φ SQ T hfib μ
      (twistedDatum K (formalBaseChange ℚ K Φ) T archR archC μ uR aR uC kC)
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) s (hsum s hs).1 (hsum s hs).2
  refine ⟨fun s hs => ⟨(hsum s hs).1, (hsum s hs).2, ?_, ?_⟩, hL⟩
  · rw [(hL s hs).1]
    exact (hConv s hs).2.2.1
  · rw [(hL s hs).2]
    exact (hConv s hs).2.2.2

open scoped Classical in

private theorem transport (hdeg : Module.finrank ℚ K = 3) (Φ : HeckeEigensystem ℚ ℂ)
    (SQ : Finset (HeightOneSpectrum (𝓞 ℚ))) (T : Finset (HeightOneSpectrum (𝓞 K)))
    (hfib : ∀ 𝔓 : HeightOneSpectrum (𝓞 K), 𝔓 ∈ T ↔ 𝔓.under (𝓞 ℚ) ∈ SQ)
    (hb : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ → ‖Φ.b p‖ = 1)
    (ha : ∀ σ : ℝ, 1 < σ →
      Summable fun p : HeightOneSpectrum (𝓞 ℚ) => ‖Φ.a p‖ * (Ideal.absNorm p.asIdeal : ℝ) ^ (-σ))
    (archR : ∀ w : InfinitePlace K, w.IsReal → RealArchParam)
    (archC : ∀ w : InfinitePlace K, w.IsComplex → ComplexArchParam)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ) (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
    (uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ) (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ)
    (ΛS ΛSd : ℂ → ℂ) (ε : ℂ) (N : ℝ) (hadm : IsAdmissibleTwist K μ)
    (H : IsNicePinned (rsDatum ℚ SQ Φ.a Φ.b
        (fun 𝔓 => if IsUnramifiedCharAt μ 𝔓 then ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) else 0)
        (twistedGammaR K archR uR aR) (twistedGammaC K archR archC uR aR uC kC)
        (twistedGammaR K (fun w hw => (archR w hw).dual) (fun w hw => -uR w hw) aR)
        (twistedGammaC K (fun w hw => (archR w hw).dual) (fun w hw => (archC w hw).dual)
          (fun w hw => -uR w hw) aR (fun w hw => -uC w hw) (fun w hw => -kC w hw))) ΛS ΛSd ε N) :
    IsNicePinned (twistedDatum K (formalBaseChange ℚ K Φ) T archR archC μ uR aR uC kC) ΛS ΛSd ε N := by
  obtain ⟨hWF, hConv, hN, Λ, Λd, hdΛ, hdΛd, hbΛ, hbΛd, hΛ, hΛd, hFE⟩ := H
  obtain ⟨hConvT, hL⟩ := analytic K hdeg Φ SQ T hfib hb ha archR archC μ hadm uR aR uC kC hConv
  refine ⟨?_, hConvT, hN, Λ, Λd, hdΛ, hdΛd, hbΛ, hbΛd, ?_, ?_, ?_⟩
  ·
    obtain ⟨-, -, hR, hCx, hRd, hCd⟩ := hWF
    refine ⟨fun v => ?_, fun v => ?_, hR, hCx, hRd, hCd⟩
    ·
      have h0 : Ideal.absNorm v.1.asIdeal ≠ 0 := by
        rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.1.ne_bot
      have h1 : Ideal.absNorm v.1.asIdeal ≠ 1 := by
        rw [Ne, Ideal.absNorm_eq_one_iff]; exact v.1.isPrime.ne_top
      show 2 ≤ Ideal.absNorm v.1.asIdeal
      omega
    · exact wf_local K Φ T archR archC μ uR aR uC kC v
  · intro s hs
    rw [hΛ s hs, (hL s hs).1]
    rfl
  · intro s hs
    rw [hΛd s hs, (hL s hs).2]
    rfl
  · exact hFE

end RsToBaseChangeTransport

end

open scoped Classical in
theorem solution
    (K : Type) [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (hdeg : Module.finrank ℚ K = 3)
    (Φ : HeckeEigensystem ℚ ℂ)
    (SQ : Finset (HeightOneSpectrum (𝓞 ℚ))) (T : Finset (HeightOneSpectrum (𝓞 K)))
    (hfib : ∀ 𝔓 : HeightOneSpectrum (𝓞 K), 𝔓 ∈ T ↔ 𝔓.under (𝓞 ℚ) ∈ SQ)
    (hb : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ → ‖Φ.b p‖ = 1)
    (ha : ∀ σ : ℝ, 1 < σ →
      Summable fun p : HeightOneSpectrum (𝓞 ℚ) => ‖Φ.a p‖ * (Ideal.absNorm p.asIdeal : ℝ) ^ (-σ))
    (archR : ∀ w : InfinitePlace K, w.IsReal → RealArchParam)
    (archC : ∀ w : InfinitePlace K, w.IsComplex → ComplexArchParam)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hμ : IsAdmissibleTwist K μ)
    (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ) (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
    (uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ) (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ)
    (ΛS ΛSd : ℂ → ℂ) (ε : ℂ) (N : ℝ)
    (hRS : IsNicePinned
      (rsDatum ℚ SQ Φ.a Φ.b
        (fun 𝔓 => if IsUnramifiedCharAt μ 𝔓 then ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) else 0)
        (twistedGammaR K archR uR aR) (twistedGammaC K archR archC uR aR uC kC)
        (twistedGammaR K (fun w hw => (archR w hw).dual) (fun w hw => -uR w hw) aR)
        (twistedGammaC K (fun w hw => (archR w hw).dual) (fun w hw => (archC w hw).dual)
          (fun w hw => -uR w hw) aR (fun w hw => -uC w hw) (fun w hw => -kC w hw)))
      ΛS ΛSd ε N) :
    IsNicePinned (twistedDatum K (formalBaseChange ℚ K Φ) T archR archC μ uR aR uC kC) ΛS ΛSd ε N := by
  exact RsToBaseChangeTransport.transport K hdeg Φ SQ T hfib hb ha archR archC μ uR aR uC kC ΛS ΛSd ε N hμ
    hRS

end S_LanglandsTunnell_RankinSelberg_isNicePinned_twistedDatum_formalBaseChange_of_isNicePinned_rsDatum
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_isNicePinned_twistedDatum_formalBaseChange_of_isNicePinned_rsDatum (solution)
