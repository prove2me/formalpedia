-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.rsEulerPoly_induced_eq_finprod_twist_formalBaseChange
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/78e3b65c-bb3c-5693-bce2-e92b53960c24

import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_HeckeEigenfunction
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_rsEulerPoly_induced_eq_finprod_twist_formalBaseChange

set_option autoImplicit false

open Polynomial IsDedekindDomain NumberField

namespace RsCubicInductionProof

private theorem satakePow_eq (α β : ℂ) :
    ∀ n : ℕ, AutomorphicForm.satakePow n (α + β) (α * β) = α ^ n + β ^ n
  | 0 => by simp [AutomorphicForm.satakePow]; norm_num
  | 1 => by simp [AutomorphicForm.satakePow]
  | (n + 2) => by
      rw [AutomorphicForm.satakePow, satakePow_eq α β (n + 1), satakePow_eq α β n]; ring

private theorem exists_roots (a b : ℂ) : ∃ α β : ℂ, a = α + β ∧ b = α * β := by
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_eq_mul_self (a ^ 2 - 4 * b)
  refine ⟨(a + s) / 2, (a - s) / 2, by ring, ?_⟩
  have h : (a + s) / 2 * ((a - s) / 2) = (a ^ 2 - s * s) / 4 := by ring
  rw [h, ← hs]
  ring

private theorem universal (α β p₁ p₂ p₃ : ℂ) :
    LanglandsTunnell.RankinSelberg.rsEulerPoly (α + β) (α * β) (-p₁) p₂ (-p₃) =
      (C 1 + C p₁ * X + C p₂ * X ^ 2 + C p₃ * X ^ 3).comp (C α * X) *
        (C 1 + C p₁ * X + C p₂ * X ^ 2 + C p₃ * X ^ 3).comp (C β * X) := by
  simp only [LanglandsTunnell.RankinSelberg.rsEulerPoly, add_comp, mul_comp, C_comp, X_comp, pow_comp,
    one_comp, map_add, map_sub, map_mul, map_neg, map_pow, map_ofNat, map_one]
  ring

private theorem factor (α β c : ℂ) (f : ℕ) :
    (C 1 - C c * X ^ f).comp (C α * X) * (C 1 - C c * X ^ f).comp (C β * X) =
      C 1 - C (c * (α ^ f + β ^ f)) * X ^ f + C (c ^ 2 * (α * β) ^ f) * X ^ (2 * f) := by
  simp only [sub_comp, mul_comp, C_comp, X_comp, pow_comp, one_comp, map_add, map_mul, map_pow, map_one,
    mul_pow, pow_mul]
  ring

private theorem key {ι : Type*} (T : Finset ι) (f : ι → ℕ) (c : ι → ℂ) (a b : ℂ)
    (hf : ∀ i ∈ T, 1 ≤ f i) (hsum : ∑ i ∈ T, f i ≤ 3) :
    LanglandsTunnell.RankinSelberg.rsEulerPoly a b
        (-(∏ i ∈ T, (C 1 - C (c i) * X ^ (f i))).coeff 1)
        ((∏ i ∈ T, (C 1 - C (c i) * X ^ (f i))).coeff 2)
        (-(∏ i ∈ T, (C 1 - C (c i) * X ^ (f i))).coeff 3) =
      ∏ i ∈ T, (C 1 - C (c i * AutomorphicForm.satakePow (f i) a b) * X ^ (f i)
        + C (c i ^ 2 * b ^ (f i)) * X ^ (2 * f i)) := by
  obtain ⟨α, β, rfl, rfl⟩ := exists_roots a b
  set P : ℂ[X] := ∏ i ∈ T, (C 1 - C (c i) * X ^ (f i)) with hP

  have hdeg : P.natDegree ≤ 3 := by
    refine (natDegree_prod_le _ _).trans (le_trans (Finset.sum_le_sum fun i hi => ?_) hsum)
    refine (natDegree_sub_le _ _).trans ?_
    simp only [natDegree_C, zero_le, max_eq_right]
    exact (natDegree_C_mul_X_pow_le (c i) (f i))
  have h0 : P.coeff 0 = 1 := by
    rw [coeff_zero_eq_eval_zero, hP, eval_prod]
    refine Finset.prod_eq_one fun i hi => ?_
    have : f i ≠ 0 := Nat.one_le_iff_ne_zero.mp (hf i hi)
    simp [this]
  have hPexp : P = C 1 + C (P.coeff 1) * X + C (P.coeff 2) * X ^ 2 + C (P.coeff 3) * X ^ 3 := by
    conv_lhs => rw [P.as_sum_range_C_mul_X_pow' (show P.natDegree < 4 by omega)]
    simp [Finset.sum_range_succ, h0]

  have h1 := universal α β (P.coeff 1) (P.coeff 2) (P.coeff 3)
  rw [h1, ← hPexp, hP, prod_comp, prod_comp, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i hi => ?_
  rw [factor, satakePow_eq]

private theorem satakePow_dual (a b : ℂ) (f : ℕ) (hf : 1 ≤ f) :
    AutomorphicForm.satakePow f (a / b) b⁻¹ = AutomorphicForm.satakePow f a b / b ^ f := by
  obtain ⟨α, β, rfl, rfl⟩ := exists_roots a b
  by_cases hα : α = 0
  · subst hα

    have hz : ∀ n, 1 ≤ n → AutomorphicForm.satakePow n (0 : ℂ) 0 = 0 := by
      intro n hn
      induction n using Nat.strong_induction_on with
      | _ n ih =>
        match n, hn with
        | 1, _ => simp [AutomorphicForm.satakePow]
        | (n + 2), _ => simp [AutomorphicForm.satakePow]
    have hf0 : f ≠ 0 := by omega
    simp [hz f hf, zero_pow hf0]
  by_cases hβ : β = 0
  · subst hβ
    have hz : ∀ n, 1 ≤ n → AutomorphicForm.satakePow n (0 : ℂ) 0 = 0 := by
      intro n hn
      induction n using Nat.strong_induction_on with
      | _ n ih =>
        match n, hn with
        | 1, _ => simp [AutomorphicForm.satakePow]
        | (n + 2), _ => simp [AutomorphicForm.satakePow]
    have hf0 : f ≠ 0 := by omega
    simp [hz f hf, zero_pow hf0]
  have hsum : (α + β) / (α * β) = α⁻¹ + β⁻¹ := by field_simp; ring
  have hprod : (α * β)⁻¹ = α⁻¹ * β⁻¹ := by rw [mul_inv]
  rw [hsum, hprod, satakePow_eq, satakePow_eq, inv_pow, inv_pow, mul_pow]
  have hαf : α ^ f ≠ 0 := pow_ne_zero _ hα
  have hβf : β ^ f ≠ 0 := pow_ne_zero _ hβ
  field_simp
  ring

end RsCubicInductionProof

open RsCubicInductionProof in
open scoped Classical in
theorem solution
    (K : Type) [Field K] [NumberField K]
    [Algebra (NumberField.RingOfIntegers ℚ) (NumberField.RingOfIntegers K)]
    [Algebra.IsIntegral (NumberField.RingOfIntegers ℚ) (NumberField.RingOfIntegers K)]
    (hdeg : Module.finrank ℚ K = 3)
    (Pi : AutomorphicForm.HeckeEigensystem ℚ ℂ)
    (μ : (NumberField.AdeleRing (NumberField.RingOfIntegers K) K)ˣ →* ℂˣ)
    (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) :
    LanglandsTunnell.RankinSelberg.rsEulerPoly (Pi.a p) (Pi.b p)
        (LanglandsTunnell.RankinSelberg.inducedE1 ℚ
        (fun 𝔓 => if NumberField.TateGlobal.IsUnramifiedCharAt μ 𝔓
          then ((μ (AutomorphicForm.uniformizerIdele K 𝔓) : ℂˣ) : ℂ) else 0) p)
        (LanglandsTunnell.RankinSelberg.inducedE2 ℚ
        (fun 𝔓 => if NumberField.TateGlobal.IsUnramifiedCharAt μ 𝔓
          then ((μ (AutomorphicForm.uniformizerIdele K 𝔓) : ℂˣ) : ℂ) else 0) p)
        (LanglandsTunnell.RankinSelberg.inducedE3 ℚ
        (fun 𝔓 => if NumberField.TateGlobal.IsUnramifiedCharAt μ 𝔓
          then ((μ (AutomorphicForm.uniformizerIdele K 𝔓) : ℂˣ) : ℂ) else 0) p) =
      ∏ᶠ 𝔓 ∈ LanglandsTunnell.RankinSelberg.primeFibre ℚ K p,
        (if NumberField.TateGlobal.IsUnramifiedCharAt μ 𝔓
          then Polynomial.C 1
            - Polynomial.C (((μ (AutomorphicForm.uniformizerIdele K 𝔓) : ℂˣ) : ℂ)
                * (AutomorphicForm.formalBaseChange ℚ K Pi).a 𝔓)
              * Polynomial.X ^
                ((𝔓.under (NumberField.RingOfIntegers ℚ)).asIdeal.inertiaDeg' 𝔓.asIdeal)
            + Polynomial.C ((((μ (AutomorphicForm.uniformizerIdele K 𝔓))^2 : ℂˣ) : ℂ)
                * (AutomorphicForm.formalBaseChange ℚ K Pi).b 𝔓)
              * Polynomial.X ^
                (2 * ((𝔓.under (NumberField.RingOfIntegers ℚ)).asIdeal.inertiaDeg' 𝔓.asIdeal))
          else Polynomial.C 1) ∧
    LanglandsTunnell.RankinSelberg.rsEulerPoly (Pi.a p / Pi.b p) (Pi.b p)⁻¹
        (LanglandsTunnell.RankinSelberg.inducedE1 ℚ
        (fun 𝔓 => (if NumberField.TateGlobal.IsUnramifiedCharAt μ 𝔓
          then ((μ (AutomorphicForm.uniformizerIdele K 𝔓) : ℂˣ) : ℂ) else 0)⁻¹) p)
        (LanglandsTunnell.RankinSelberg.inducedE2 ℚ
        (fun 𝔓 => (if NumberField.TateGlobal.IsUnramifiedCharAt μ 𝔓
          then ((μ (AutomorphicForm.uniformizerIdele K 𝔓) : ℂˣ) : ℂ) else 0)⁻¹) p)
        (LanglandsTunnell.RankinSelberg.inducedE3 ℚ
        (fun 𝔓 => (if NumberField.TateGlobal.IsUnramifiedCharAt μ 𝔓
          then ((μ (AutomorphicForm.uniformizerIdele K 𝔓) : ℂˣ) : ℂ) else 0)⁻¹) p) =
      ∏ᶠ 𝔓 ∈ LanglandsTunnell.RankinSelberg.primeFibre ℚ K p,
        (if NumberField.TateGlobal.IsUnramifiedCharAt μ 𝔓
          then Polynomial.C 1
            - Polynomial.C ((((μ (AutomorphicForm.uniformizerIdele K 𝔓))⁻¹ : ℂˣ) : ℂ)
                * ((AutomorphicForm.formalBaseChange ℚ K Pi).a 𝔓
                    / (AutomorphicForm.formalBaseChange ℚ K Pi).b 𝔓))
              * Polynomial.X ^
                ((𝔓.under (NumberField.RingOfIntegers ℚ)).asIdeal.inertiaDeg' 𝔓.asIdeal)
            + Polynomial.C ((((μ (AutomorphicForm.uniformizerIdele K 𝔓))^(-2 : ℤ) : ℂˣ) : ℂ)
                * ((AutomorphicForm.formalBaseChange ℚ K Pi).b 𝔓)⁻¹)
              * Polynomial.X ^
                (2 * ((𝔓.under (NumberField.RingOfIntegers ℚ)).asIdeal.inertiaDeg' 𝔓.asIdeal))
          else Polynomial.C 1) := by
  classical

  have huniq : ∀ P Q : Algebra (NumberField.RingOfIntegers ℚ) (NumberField.RingOfIntegers K), P = Q := by
    intro P Q
    refine Algebra.algebra_ext P Q fun r => ?_
    have key : ∀ f g : NumberField.RingOfIntegers ℚ →+* NumberField.RingOfIntegers K, f = g := by
      intro f g
      have h := Subsingleton.elim (f.comp Rat.ringOfIntegersEquiv.symm.toRingHom)
        (g.comp Rat.ringOfIntegersEquiv.symm.toRingHom)
      refine RingHom.ext fun x => ?_
      obtain ⟨n, rfl⟩ := Rat.ringOfIntegersEquiv.symm.surjective x
      exact RingHom.congr_fun h n
    exact congrArg (fun φ => φ r) (key (@algebraMap _ _ _ _ P) (@algebraMap _ _ _ _ Q))
  obtain rfl : ‹Algebra (NumberField.RingOfIntegers ℚ) (NumberField.RingOfIntegers K)› =
      NumberField.inst_ringOfIntegersAlgebra ℚ K := huniq _ _

  set a : ℂ := Pi.a p with ha
  set b : ℂ := Pi.b p with hb
  set c : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) → ℂ := fun 𝔓 =>
    if NumberField.TateGlobal.IsUnramifiedCharAt μ 𝔓
      then ((μ (AutomorphicForm.uniformizerIdele K 𝔓) : ℂˣ) : ℂ) else 0 with hc
  set fd : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) → ℕ := fun 𝔓 =>
    (𝔓.under (NumberField.RingOfIntegers ℚ)).asIdeal.inertiaDeg' 𝔓.asIdeal with hfd

  haveI : p.asIdeal.IsMaximal := p.isMaximal
  have hfin : (LanglandsTunnell.RankinSelberg.primeFibre ℚ K p).Finite := by
    have h1 : (p.asIdeal.primesOver (NumberField.RingOfIntegers K)).Finite :=
      IsDedekindDomain.primesOver_finite p.asIdeal (NumberField.RingOfIntegers K)
    refine (h1.preimage (Set.injOn_of_injective (fun x y h =>
      IsDedekindDomain.HeightOneSpectrum.ext h))).subset ?_
    intro 𝔓 h𝔓
    rw [LanglandsTunnell.RankinSelberg.mem_primeFibre] at h𝔓
    refine ⟨𝔓.isPrime, ⟨?_⟩⟩
    rw [← h𝔓]
    rfl
  set T := hfin.toFinset with hT
  have hmem : ∀ 𝔓, 𝔓 ∈ T ↔ 𝔓.under (NumberField.RingOfIntegers ℚ) = p := fun 𝔓 => by
    rw [hT, Set.Finite.mem_toFinset, LanglandsTunnell.RankinSelberg.mem_primeFibre]

  have hfdT : ∀ 𝔓 ∈ T, fd 𝔓 = p.asIdeal.inertiaDeg' 𝔓.asIdeal := fun 𝔓 h𝔓 => by
    simp only [hfd]; rw [(hmem 𝔓).mp h𝔓]
  have hlies : ∀ 𝔓 ∈ T, 𝔓.asIdeal.LiesOver p.asIdeal := fun 𝔓 h𝔓 =>
    ⟨by rw [← (hmem 𝔓).mp h𝔓]; rfl⟩
  have hf : ∀ 𝔓 ∈ T, 1 ≤ fd 𝔓 := fun 𝔓 h𝔓 => by
    rw [hfdT 𝔓 h𝔓]
    haveI := hlies 𝔓 h𝔓
    exact Ideal.inertiaDeg'_pos p.asIdeal 𝔓.asIdeal
  have hsum : ∑ 𝔓 ∈ T, fd 𝔓 ≤ 3 := by
    have hfund := Ideal.sum_ramification_inertia (NumberField.RingOfIntegers K) ℚ K
      (p := p.asIdeal) p.ne_bot
    rw [hdeg] at hfund
    have hinj : Set.InjOn (fun 𝔓 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) =>
        𝔓.asIdeal) T := fun x _ y _ h => IsDedekindDomain.HeightOneSpectrum.ext h
    calc ∑ 𝔓 ∈ T, fd 𝔓
        = ∑ 𝔓 ∈ T, p.asIdeal.inertiaDeg' 𝔓.asIdeal := Finset.sum_congr rfl hfdT
      _ = ∑ P ∈ T.image (fun 𝔓 => 𝔓.asIdeal), p.asIdeal.inertiaDeg' P := by
          rw [Finset.sum_image hinj]
      _ ≤ ∑ P ∈ IsDedekindDomain.primesOverFinset p.asIdeal (NumberField.RingOfIntegers K),
            p.asIdeal.inertiaDeg' P := by
          refine Finset.sum_le_sum_of_subset fun P hP => ?_
          obtain ⟨𝔓, h𝔓, rfl⟩ := Finset.mem_image.mp hP
          rw [IsDedekindDomain.mem_primesOverFinset_iff p.ne_bot]
          exact ⟨𝔓.isPrime, hlies 𝔓 (Finset.mem_coe.mp h𝔓)⟩
      _ ≤ ∑ P ∈ IsDedekindDomain.primesOverFinset p.asIdeal (NumberField.RingOfIntegers K),
            p.asIdeal.ramificationIdx' P * p.asIdeal.inertiaDeg' P := by
          refine Finset.sum_le_sum fun P hP => ?_
          have hP' := (IsDedekindDomain.mem_primesOverFinset_iff p.ne_bot _).mp hP
          haveI : P.IsPrime := hP'.1
          haveI : P.LiesOver p.asIdeal := hP'.2
          exact Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero
            (Ideal.IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver P p.ne_bot))
      _ = 3 := hfund

  have hP : LanglandsTunnell.RankinSelberg.inducedEulerPoly ℚ c p =
      ∏ 𝔓 ∈ T, (C 1 - C (c 𝔓) * X ^ (fd 𝔓)) := by
    rw [LanglandsTunnell.RankinSelberg.inducedEulerPoly, finprod_mem_eq_finite_toFinset_prod _ hfin]
    rfl
  have hPd : LanglandsTunnell.RankinSelberg.inducedEulerPoly ℚ (fun 𝔓 => (c 𝔓)⁻¹) p =
      ∏ 𝔓 ∈ T, (C 1 - C ((fun 𝔓 => (c 𝔓)⁻¹) 𝔓) * X ^ (fd 𝔓)) := by
    rw [LanglandsTunnell.RankinSelberg.inducedEulerPoly, finprod_mem_eq_finite_toFinset_prod _ hfin]
    rfl
  have hunder : ∀ 𝔓 ∈ T, (AutomorphicForm.formalBaseChange ℚ K Pi).a 𝔓 =
      AutomorphicForm.satakePow (fd 𝔓) a b ∧ (AutomorphicForm.formalBaseChange ℚ K Pi).b 𝔓 = b ^ (fd 𝔓) := by
    intro 𝔓 h𝔓
    simp only [AutomorphicForm.formalBaseChange_a, AutomorphicForm.formalBaseChange_b, ha, hb, hfd,
      (hmem 𝔓).mp h𝔓, and_self]
  refine ⟨?_, ?_⟩
  ·
    have lhs : LanglandsTunnell.RankinSelberg.inducedE1 ℚ c p = -(∏ 𝔓 ∈ T, (C 1 - C (c 𝔓) * X ^ (fd 𝔓))).coeff 1
        ∧ LanglandsTunnell.RankinSelberg.inducedE2 ℚ c p = (∏ 𝔓 ∈ T, (C 1 - C (c 𝔓) * X ^ (fd 𝔓))).coeff 2
        ∧ LanglandsTunnell.RankinSelberg.inducedE3 ℚ c p = -(∏ 𝔓 ∈ T, (C 1 - C (c 𝔓) * X ^ (fd 𝔓))).coeff 3 := by
      simp only [LanglandsTunnell.RankinSelberg.inducedE1, LanglandsTunnell.RankinSelberg.inducedE2,
        LanglandsTunnell.RankinSelberg.inducedE3, hP, and_self]
    rw [lhs.1, lhs.2.1, lhs.2.2, key T fd c a b hf hsum, finprod_mem_eq_finite_toFinset_prod _ hfin]
    refine Finset.prod_congr rfl fun 𝔓 h𝔓 => ?_
    obtain ⟨hA, hB⟩ := hunder 𝔓 h𝔓
    by_cases hu : NumberField.TateGlobal.IsUnramifiedCharAt μ 𝔓
    · simp only [hc, hu, if_true, hA, hB, Units.val_pow_eq_pow_val, hfd]
    · simp only [hc, hu, if_false, zero_mul, map_zero, sub_zero, ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, zero_pow, add_zero]
  ·
    have lhs : LanglandsTunnell.RankinSelberg.inducedE1 ℚ (fun 𝔓 => (c 𝔓)⁻¹) p =
          -(∏ 𝔓 ∈ T, (C 1 - C ((fun 𝔓 => (c 𝔓)⁻¹) 𝔓) * X ^ (fd 𝔓))).coeff 1
        ∧ LanglandsTunnell.RankinSelberg.inducedE2 ℚ (fun 𝔓 => (c 𝔓)⁻¹) p =
          (∏ 𝔓 ∈ T, (C 1 - C ((fun 𝔓 => (c 𝔓)⁻¹) 𝔓) * X ^ (fd 𝔓))).coeff 2
        ∧ LanglandsTunnell.RankinSelberg.inducedE3 ℚ (fun 𝔓 => (c 𝔓)⁻¹) p =
          -(∏ 𝔓 ∈ T, (C 1 - C ((fun 𝔓 => (c 𝔓)⁻¹) 𝔓) * X ^ (fd 𝔓))).coeff 3 := by
      simp only [LanglandsTunnell.RankinSelberg.inducedE1, LanglandsTunnell.RankinSelberg.inducedE2,
        LanglandsTunnell.RankinSelberg.inducedE3, hPd, and_self]
    rw [lhs.1, lhs.2.1, lhs.2.2, key T fd (fun 𝔓 => (c 𝔓)⁻¹) (a / b) b⁻¹ hf hsum,
      finprod_mem_eq_finite_toFinset_prod _ hfin]
    refine Finset.prod_congr rfl fun 𝔓 h𝔓 => ?_
    obtain ⟨hA, hB⟩ := hunder 𝔓 h𝔓
    have hdual := satakePow_dual a b (fd 𝔓) (hf 𝔓 h𝔓)
    by_cases hu : NumberField.TateGlobal.IsUnramifiedCharAt μ 𝔓
    · rw [hdual, if_pos hu]
      have hcu : c 𝔓 = ((μ (AutomorphicForm.uniformizerIdele K 𝔓) : ℂˣ) : ℂ) := by
        simp only [hc, hu, if_true]
      rw [hcu, hA, hB]
      simp only [hfd, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, zpow_neg, zpow_ofNat, inv_pow]
    · simp only [hc, hu, if_false, inv_zero, zero_mul, map_zero, sub_zero, ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, zero_pow, add_zero]

end S_LanglandsTunnell_RankinSelberg_rsEulerPoly_induced_eq_finprod_twist_formalBaseChange
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_rsEulerPoly_induced_eq_finprod_twist_formalBaseChange (solution)
