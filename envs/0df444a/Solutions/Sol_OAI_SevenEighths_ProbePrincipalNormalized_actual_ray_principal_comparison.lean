-- Prove2me | solution 1 for OAI.SevenEighths.ProbePrincipalNormalized.actual_ray_principal_comparison
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T05:29:12.262088+00:00
-- url     : https://prove2.me/submissions/410a7fc1-46bb-45b8-b27a-a03890a6c1a0

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B027
import Theorems.Thm_OAI_SevenEighths_HeckeRayPrimes_quotientClassCoeff_ratio_tendsto
import Theorems.Thm_OAI_SevenEighths_ProbePrincipalPhysical_physical_principal_residue_remainder
import Theorems.Thm_OAI_SevenEighths_ProbePrincipalResidueActual_normalized_actual_window_residue
import Theorems.Thm_OAI_SmoothMobiusCorrection_prime_norm_two_le

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.NormFiberCharacters
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology

namespace ShortDraftHeckeBridge

private theorem orderOf_mod3_eq_one {p : ℕ} (h : p % 3 = 1) :
    orderOf (p : ZMod 3) = 1 := by
  have hc : (p : ZMod 3) = 1 :=
    (ZMod.natCast_eq_natCast_iff' p 1 3).2 (by simpa using h)
  simp [hc]

private theorem degree_two : Module.finrank ℚ K = 2 := by
  rw [IsCyclotomicExtension.Rat.finrank 3 K]
  decide

private theorem gal_card_two : Nat.card Gal(K/ℚ) = 2 := by
  rw [IsGaloisGroup.card_eq_finrank Gal(K/ℚ) ℚ K]
  exact degree_two

theorem split_count_of_mod_one {p : ℕ} (hp : p.Prime) (hmod : p % 3 = 1) :
    ((Ideal.span {(p : ℤ)}).primesOver O).ncard = 2 := by
  let : Fact p.Prime := ⟨hp⟩
  have hneq : p ≠ 3 := by
    intro heq
    subst p
    norm_num at hmod
  have hnd := not_dvd_three hp hneq
  have hmain := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
    (Ideal.span {(p : ℤ)}) O Gal(K/ℚ)
  rw [IsCyclotomicExtension.Rat.ramificationIdxIn_eq_of_not_dvd p K hnd,
    IsCyclotomicExtension.Rat.inertiaDegIn_eq_of_not_dvd p K hnd,
    orderOf_mod3_eq_one hmod, gal_card_two] at hmain
  omega

theorem inert_count_of_mod_two {p : ℕ} (hp : p.Prime) (hmod : p % 3 = 2) :
    ((Ideal.span {(p : ℤ)}).primesOver O).ncard = 1 := by
  let : Fact p.Prime := ⟨hp⟩
  have hneq : p ≠ 3 := by
    intro heq
    subst p
    norm_num at hmod
  have hnd := not_dvd_three hp hneq
  have hmain := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
    (Ideal.span {(p : ℤ)}) O Gal(K/ℚ)
  rw [IsCyclotomicExtension.Rat.ramificationIdxIn_eq_of_not_dvd p K hnd,
    IsCyclotomicExtension.Rat.inertiaDegIn_eq_of_not_dvd p K hnd,
    orderOf_mod3_eq_two hmod, gal_card_two] at hmain
  omega

theorem ramified_count :
    ((Ideal.span {(3 : ℤ)}).primesOver O).ncard = 1 := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  exact IsCyclotomicExtension.Rat.ncard_primesOver_of_prime 3 K

theorem absNorm_split {p : ℕ} (hp : p.Prime) (hmod : p % 3 = 1)
    (P : Ideal O) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})] :
    Ideal.absNorm P = p := by
  let : Fact p.Prime := ⟨hp⟩
  have hneq : p ≠ 3 := by
    intro heq
    subst p
    norm_num at hmod
  have hnd := not_dvd_three hp hneq
  have hf : P.inertiaDeg ℤ = 1 := by
    rw [← Ideal.inertiaDegIn_eq_inertiaDeg (Ideal.span {(p : ℤ)}) P Gal(K/ℚ),
      IsCyclotomicExtension.Rat.inertiaDegIn_eq_of_not_dvd p K hnd,
      orderOf_mod3_eq_one hmod]
  rw [← Ideal.pow_inertiaDeg p P, hf, pow_one]

theorem absNorm_ramified
    (P : Ideal O) [P.IsPrime] [P.LiesOver (Ideal.span {(3 : ℤ)})] :
    Ideal.absNorm P = 3 := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hfin : (Ideal.span {(3 : ℤ)}).inertiaDegIn O = 1 := by
    simpa using IsCyclotomicExtension.Rat.inertiaDegIn_eq_of_prime 3 K
  have hf : P.inertiaDeg ℤ = 1 := by
    rw [← Ideal.inertiaDegIn_eq_inertiaDeg (Ideal.span {(3 : ℤ)}) P Gal(K/ℚ)]
    exact hfin
  rw [← Ideal.pow_inertiaDeg 3 P, hf, pow_one]

end ShortDraftHeckeBridge

end

end OAI
end

section
-- module Solutions.OAIHecke.Vendor.PrimeNumberTheoremAnd.Sobolev
open Real Complex MeasureTheory Filter Topology BoundedContinuousFunction SchwartzMap  BigOperators
open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}

namespace W1

theorem differentiable (f : W1 (n + 1) E) : Differentiable ℝ f :=
  f.smooth.differentiable (by simp)

end W1
end

section
-- module Solutions.OAIHecke.Vendor.PrimeNumberTheoremAnd.Wiener
open Real BigOperators ArithmeticFunction MeasureTheory Filter Set FourierTransform LSeries
  Asymptotics SchwartzMap
open Complex hiding log
open scoped Topology
open scoped ContDiff
open scoped ComplexConjugate

variable {n : ℕ} {A a b c d u x y t σ' : ℝ} {ψ Ψ : ℝ → ℂ} {F G : ℂ → ℂ} {f : ℕ → ℂ} {𝕜 : Type}
  [RCLike 𝕜]

attribute [fun_prop] Real.continuous_fourierChar

attribute [fun_prop] measurable_coe_nnreal_ennreal

section nabla

variable {α E : Type*} [OfNat α 1] [Add α] [Sub α] {u : α → ℂ}

theorem cumsum_nonneg {u : ℕ → ℝ} (hu : 0 ≤ u) : 0 ≤ cumsum u :=
  fun _ => Finset.sum_nonneg (fun i _ => hu i)

end nabla

theorem BoundedAtFilter.add_const {u : ℕ → ℝ} {c : ℝ} :
    BoundedAtFilter atTop (fun n => u n + c) ↔ BoundedAtFilter atTop u := by
  have : u = fun n => (u n + c) + (-c) := by ext n ; ring
  simp only [BoundedAtFilter]
  constructor <;> intro h
  on_goal 1 => rw [this]
  all_goals { exact h.add (const_boundedAtFilter _ _) }

local instance instCoeForallRealForallComplex_solutions_re5ec66_1 {E : Type*} : Coe (E → ℝ) (E → ℂ) := ⟨fun f n => f n⟩
theorem vonMangoldt_cheby : (∃ C : ℝ, ∀ n : ℕ, cumsum (fun k : ℕ ↦ ‖(Λ k : ℂ)‖) n ≤ C * n) := by
  use Real.log 4 + 4
  intro N
  by_cases! h : N = 0
  · simp [h, cumsum]
  simp only [cumsum, norm_real, norm_eq_abs]
  rw [Nat.range_eq_Icc_zero_sub_one _ h, (by simp : N - 1 = ⌊(N : ℝ) - 1⌋₊)]
  simp_rw [abs_of_nonneg vonMangoldt_nonneg]
  rw [← Chebyshev.psi_eq_sum_Icc]
  grw [Chebyshev.psi_le_const_mul_self <| sub_nonneg_of_le <| Nat.one_le_cast_iff_ne_zero.mpr h]
  gcongr
  linarith
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.IdealMangoldt
namespace OAI

namespace SevenEighths.IdealMangoldt

open ActualEisensteinCubic UniqueFactorizationMonoid ArithmeticFunction
open scoped BigOperators Classical

noncomputable section

theorem primeBase_spec {I : Ideal O} (hI : IsPrimePow I) :
    Prime (primeBase I) ∧ ∃ k : ℕ, 0 < k ∧ primeBase I ^ k = I := by
  obtain ⟨k, hp, hk, heq⟩ := hI.choose_spec
  simp only [primeBase, hI, dite_true]
  exact ⟨hp, k, hk, heq⟩

theorem primeBase_pow {P : Ideal O} (hP : Prime P) {k : ℕ} (hk : 0 < k) :
    primeBase (P ^ k) = P := by
  have hpow : IsPrimePow (P ^ k) := ⟨P, k, hP, hk, rfl⟩
  obtain ⟨hQ, l, hl, heq⟩ := primeBase_spec hpow
  apply associated_iff_eq.mp
  apply hQ.associated_of_dvd hP
  exact hQ.dvd_of_dvd_pow (heq ▸ dvd_pow_self (primeBase (P ^ k)) hl.ne')

theorem value_pow {P : Ideal O} (hP : Prime P) {k : ℕ} (hk : 0 < k) :
    value (P ^ k) = Real.log (Ideal.absNorm P) := by
  rw [value, if_pos (show IsPrimePow (P ^ k) from ⟨P, k, hP, hk, rfl⟩),
    primeBase_pow hP hk]

theorem value_nonneg (I : Ideal O) : 0 ≤ value I := by
  by_cases hI : IsPrimePow I
  · rw [value, if_pos hI]
    apply Real.log_nonneg
    exact_mod_cast (SmoothMobiusCorrection.prime_norm_two_le ⟨_, (primeBase_spec hI).1⟩).trans' (by decide : 1 ≤ 2)
  · simp only [value, hI, ite_false, le_refl]

theorem isPrimePow_absNorm {I : Ideal O} (hI : IsPrimePow I) :
    IsPrimePow (Ideal.absNorm I) := by
  obtain ⟨P, k, hP, hk, rfl⟩ := hI
  let : P.IsMaximal := (Ideal.isPrime_of_prime hP).isMaximal hP.ne_zero
  obtain ⟨p, n, hn, _, hp, hnorm⟩ := Ideal.exists_prime_and_absNorm_eq_pow P
  rw [map_pow, hnorm, ← pow_mul]
  exact (isPrimePow_nat_iff _).mpr ⟨p, n * k, hp, mul_pos hn hk, rfl⟩

theorem value_eq_zero_of_norm_not_primePow {I : Ideal O}
    (hI : ¬IsPrimePow (Ideal.absNorm I)) : value I = 0 := by
  exact if_neg (fun h => hI (isPrimePow_absNorm h))

theorem prime_mem_primesOver_of_dvd_norm {P : Ideal O} (hP : Prime P)
    {p : ℕ} (hp : p.Prime) (hd : p ∣ Ideal.absNorm P) :
    P ∈ (Ideal.span {(p : ℤ)}).primesOver O := by
  obtain ⟨Q, hQ, hQu, hQP⟩ := Ideal.exists_isMaximal_dvd_of_dvd_absNorm' hp P hd
  have heq : P = Q := (Ideal.isPrime_of_prime hP).isMaximal hP.ne_zero |>.eq_of_le
    hQ.ne_top (Ideal.dvd_iff_le.mp hQP)
  subst Q
  exact ⟨Ideal.isPrime_of_prime hP, ⟨hQu.symm⟩⟩

theorem primeBase_mem_primesOver {p k : ℕ} (hp : p.Prime) (hk : 0 < k)
    {I : Ideal O} (hI : IsPrimePow I) (hn : Ideal.absNorm I = p ^ k) :
    primeBase I ∈ (Ideal.span {(p : ℤ)}).primesOver O := by
  obtain ⟨hP, l, hl, heq⟩ := primeBase_spec hI
  apply prime_mem_primesOver_of_dvd_norm hP hp
  apply hp.dvd_of_dvd_pow
  have hnorm := congrArg Ideal.absNorm heq
  rw [map_pow, hn] at hnorm
  rw [hnorm]
  exact dvd_pow_self _ hk.ne'

theorem primeBase_injective_on_norm {I J : Ideal O} (hI : IsPrimePow I)
    (hJ : IsPrimePow J) (hn : Ideal.absNorm I = Ideal.absNorm J)
    (hbase : primeBase I = primeBase J) : I = J := by
  obtain ⟨hP, k, hk, hPk⟩ := primeBase_spec hI
  obtain ⟨_, l, hl, hPl⟩ := primeBase_spec hJ
  rw [← hbase] at hPl
  have hkl : k = l := by
    apply Nat.pow_right_injective (SmoothMobiusCorrection.prime_norm_two_le ⟨_, hP⟩)
    have hnI : Ideal.absNorm (primeBase I) ^ k = Ideal.absNorm I := by
      simpa only [map_pow] using congrArg Ideal.absNorm hPk
    have hnJ : Ideal.absNorm (primeBase I) ^ l = Ideal.absNorm J := by
      simpa only [map_pow] using congrArg Ideal.absNorm hPl
    exact hnI.trans (hn.trans hnJ.symm)
  exact hPk.symm.trans ((congrArg (primeBase I ^ ·) hkl).trans hPl)

theorem coeff_nonneg (w : Ideal O → ℝ) (hw : ∀ I, 0 ≤ w I) (n : ℕ) :
    0 ≤ coeff w n :=
  Finset.sum_nonneg (fun I _ => mul_nonneg (hw I) (value_nonneg I))

theorem coeff_le_unweighted (w : Ideal O → ℝ) (hw : ∀ I, w I ≤ 1) (n : ℕ) :
    coeff w n ≤ coeff (fun _ => 1) n := by
  apply Finset.sum_le_sum
  intro I hI
  exact mul_le_mul_of_nonneg_right (hw I) (value_nonneg I)

theorem coeff_eq_sum_primePowers (n : ℕ) :
    coeff (fun _ => 1) n =
      ∑ I ∈ (normFiber n).filter IsPrimePow, Real.log (Ideal.absNorm (primeBase I)) := by
  simp only [coeff, one_mul, value, Finset.sum_filter]

theorem coeff_eq_zero_of_not_primePow {n : ℕ} (hn : ¬IsPrimePow n)
    (w : Ideal O → ℝ) : coeff w n = 0 := by
  apply Finset.sum_eq_zero
  intro I hI
  rw [value_eq_zero_of_norm_not_primePow (by simpa only [(mem_normFiber n I).mp hI] using hn),
    mul_zero]

theorem primesOver_card (p : ℕ) [Fact p.Prime] :
    (primesOver p).card = ((Ideal.span {(p : ℤ)}).primesOver O).ncard := by
  exact (Set.ncard_eq_toFinset_card _).symm

theorem primesOver_log_sum_le (p : ℕ) [hp : Fact p.Prime] :
    ∑ P ∈ primesOver p, Real.log (Ideal.absNorm P) ≤ 2 * Real.log p := by
  have hlog : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hp.out.one_lt.le)
  by_cases h1 : p % 3 = 1
  · have hv (P : Ideal O) (hP : P ∈ primesOver p) :
        Real.log (Ideal.absNorm P) = Real.log p := by
      have hPP := (mem_primesOver p P).mp hP
      let : P.IsPrime := hPP.1
      let : P.LiesOver (Ideal.span {(p : ℤ)}) := hPP.2
      rw [ShortDraftHeckeBridge.absNorm_split hp.out h1 P]
    rw [Finset.sum_congr rfl hv, Finset.sum_const, nsmul_eq_mul, primesOver_card,
      ShortDraftHeckeBridge.split_count_of_mod_one hp.out h1]
    norm_num
  by_cases h2 : p % 3 = 2
  · have hv (P : Ideal O) (hP : P ∈ primesOver p) :
        Real.log (Ideal.absNorm P) = 2 * Real.log p := by
      have hPP := (mem_primesOver p P).mp hP
      let : P.IsPrime := hPP.1
      let : P.LiesOver (Ideal.span {(p : ℤ)}) := hPP.2
      rw [ShortDraftHeckeBridge.absNorm_inert hp.out h2 P, Nat.cast_pow, Real.log_pow]
      norm_num
    rw [Finset.sum_congr rfl hv, Finset.sum_const, nsmul_eq_mul, primesOver_card,
      ShortDraftHeckeBridge.inert_count_of_mod_two hp.out h2]
    norm_num
  have h3 : p = 3 := by
    have h0 : p % 3 = 0 := by have := Nat.mod_lt p (by decide : 0 < 3); omega
    have h := (Nat.dvd_prime hp.out).mp (Nat.dvd_of_mod_eq_zero h0)
    omega
  subst p
  have hv (P : Ideal O) (hP : P ∈ primesOver 3) :
      Real.log (Ideal.absNorm P) = Real.log 3 := by
    have hPP := (mem_primesOver 3 P).mp hP
    let : P.IsPrime := hPP.1
    let : P.LiesOver (Ideal.span {(3 : ℤ)}) := hPP.2
    rw [ShortDraftHeckeBridge.absNorm_ramified P]
    norm_num
  rw [Finset.sum_congr rfl hv, Finset.sum_const, nsmul_eq_mul, primesOver_card]
  norm_num only [Nat.cast_ofNat]
  rw [ShortDraftHeckeBridge.ramified_count]
  norm_num only [Nat.cast_one, one_mul, Nat.cast_ofNat]
  norm_num only [Nat.cast_ofNat] at hlog
  linarith

theorem coeff_prime_pow_le (p : ℕ) [hp : Fact p.Prime] {k : ℕ} (hk : 0 < k) :
    coeff (fun _ => 1) (p ^ k) ≤ 2 * Real.log p := by
  rw [coeff_eq_sum_primePowers]
  let S := (normFiber (p ^ k)).filter IsPrimePow
  have hS (I : Ideal O) (hI : I ∈ S) : IsPrimePow I ∧ Ideal.absNorm I = p ^ k :=
    ⟨(Finset.mem_filter.mp hI).2, (mem_normFiber _ I).mp (Finset.mem_filter.mp hI).1⟩
  have hinj : Set.InjOn primeBase (↑S : Set (Ideal O)) := by
    intro I hI J hJ heq
    exact primeBase_injective_on_norm (hS I hI).1 (hS J hJ).1
      ((hS I hI).2.trans (hS J hJ).2.symm) heq
  have hsub : S.image primeBase ⊆ primesOver p := by
    intro P hP
    obtain ⟨I, hI, rfl⟩ := Finset.mem_image.mp hP
    exact (mem_primesOver p _).mpr (primeBase_mem_primesOver hp.out hk (hS I hI).1 (hS I hI).2)
  calc
    _ = ∑ P ∈ S.image primeBase, Real.log (Ideal.absNorm P) := (Finset.sum_image hinj).symm
    _ ≤ ∑ P ∈ primesOver p, Real.log (Ideal.absNorm P) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro P hP _
      have hPP := (mem_primesOver p P).mp hP
      have hprime : Prime P := Ideal.prime_of_mem_primesOver
        (by simpa using (show (p : ℤ) ≠ 0 by exact_mod_cast hp.out.ne_zero)) hPP
      exact Real.log_nonneg (by exact_mod_cast
        (SmoothMobiusCorrection.prime_norm_two_le ⟨P, hprime⟩).trans' (by decide : 1 ≤ 2))
    _ ≤ _ := primesOver_log_sum_le p

theorem coeff_le_two_vonMangoldt (w : Ideal O → ℝ) (hw : ∀ I, w I ≤ 1) (n : ℕ) :
    coeff w n ≤ 2 * vonMangoldt n := by
  by_cases hn : IsPrimePow n
  · obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff n).mp hn
    let : Fact p.Prime := ⟨hp⟩
    rw [vonMangoldt_apply_pow hk.ne', vonMangoldt_apply_prime hp]
    exact (coeff_le_unweighted w hw _).trans (coeff_prime_pow_le p hk)
  · rw [coeff_eq_zero_of_not_primePow hn, vonMangoldt_eq_zero_iff.mpr hn, mul_zero]

theorem coeff_chebyshev (w : Ideal O → ℝ) (hw0 : ∀ I, 0 ≤ w I)
    (hw1 : ∀ I, w I ≤ 1) :
    ∃ C : ℝ, ∀ N : ℕ, cumsum (fun n => ‖(coeff w n : ℂ)‖) N ≤ C * N := by
  obtain ⟨C, hC⟩ := vonMangoldt_cheby
  refine ⟨2 * C, fun N => ?_⟩
  calc
    _ ≤ 2 * cumsum (fun n => ‖(vonMangoldt n : ℂ)‖) N := by
      unfold cumsum
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro n hn
      simpa only [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (coeff_nonneg w hw0 n), abs_of_nonneg vonMangoldt_nonneg]
        using coeff_le_two_vonMangoldt w hw1 n
    _ ≤ 2 * (C * N) := mul_le_mul_of_nonneg_left (hC N) (by norm_num)
    _ = _ := by ring

theorem classCoeff_nonneg (C : Set (Ideal O)) (n : ℕ) : 0 ≤ classCoeff C n :=
  coeff_nonneg _ (fun _ => by split_ifs <;> norm_num) n

theorem classCoeff_le_two_vonMangoldt (C : Set (Ideal O)) (n : ℕ) :
    classCoeff C n ≤ 2 * vonMangoldt n :=
  coeff_le_two_vonMangoldt _ (fun _ => by split_ifs <;> norm_num) n

theorem classCoeff_chebyshev (C : Set (Ideal O)) :
    ∃ B : ℝ, ∀ N : ℕ, cumsum (fun n => ‖(classCoeff C n : ℂ)‖) N ≤ B * N :=
  coeff_chebyshev _ (fun _ => by split_ifs <;> norm_num)
    (fun _ => by split_ifs <;> norm_num)

end

end SevenEighths.IdealMangoldt

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.RayOrthogonality
namespace OAI

namespace SevenEighths.RayOrthogonality

open scoped Classical
noncomputable section

section FiniteMonoid
variable {R : Type*} [CommMonoid R] [Finite R]

theorem ray_card_pos (H : Subgroup Rˣ) : 0 < Nat.card (Rˣ ⧸ H) :=
  Nat.card_pos

end FiniteMonoid

end
end SevenEighths.RayOrthogonality

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.PrincipalSignalComparison
namespace OAI

noncomputable section
open scoped Classical BigOperators Topology
open MeasureTheory Set Filter Asymptotics Complex
namespace SevenEighths.PrincipalSignalComparison
open HeckeFamily PrincipalSlotEstimate ProbeEuler ProbeLocal Continuation HeckeSignal

variable {κ ι : Type*}

open ProbePhysical ActualEisensteinCubic CompletedGauss

theorem prime_coprime_of_norm_gt (η : Character) (P : PrimeIdeal)
    (hN : Ideal.absNorm η.modulus < Ideal.absNorm P.val) : IsCoprime P.val η.modulus := by
  let : P.val.IsPrime := Ideal.isPrime_of_prime P.property
  let : P.val.IsMaximal := Ideal.IsPrime.isMaximal inferInstance P.property.ne_zero
  rw [Ideal.isCoprime_iff_codisjoint,
    ← (Ideal.isMaximal_def.mp (inferInstance : P.val.IsMaximal)).not_le_iff_codisjoint]
  intro hle
  have hn : 0 < Ideal.absNorm η.modulus := Nat.pos_of_ne_zero
    (Ideal.absNorm_eq_zero_iff.not.mpr η.modulus_ne_bot)
  exact (Nat.not_le_of_gt hN) (Nat.le_of_dvd hn (Ideal.absNorm_dvd_absNorm_of_le hle))

open PrincipalMellinResidues

end SevenEighths.PrincipalSignalComparison
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.PrimeCounting.PrimeMass
namespace OAI

namespace SevenEighths.PNT

open Filter ArithmeticFunction
open scoped Topology BigOperators

theorem cumsum_div_tendsto_zero_of_summable_div {f : ℕ → ℝ}
    (hf : ∀ n, 0 ≤ f n) (hzero : f 0 = 0)
    (hsum : Summable (fun n => f n / n)) :
    Tendsto (fun N : ℕ => cumsum f N / N) atTop (𝓝 0) := by
  let F : ℕ → ℕ → ℝ := fun N n => if n < N then f n / N else 0
  have hlim (n : ℕ) : Tendsto (fun N => F N n) atTop (𝓝 0) := by
    apply (tendsto_const_div_atTop_nhds_zero_nat (f n)).congr'
    filter_upwards [eventually_gt_atTop n] with N hN
    simp [F, hN]
  have hbound : ∀ N n, ‖F N n‖ ≤ f n / n := by
    intro N n
    by_cases hn : n = 0
    · subst n
      simp [F, hzero]
    by_cases hN : n < N
    · simp only [F, if_pos hN, Real.norm_eq_abs,
        abs_of_nonneg (div_nonneg (hf n) (Nat.cast_nonneg N))]
      exact div_le_div_of_nonneg_left (hf n)
        (show (0 : ℝ) < n by exact_mod_cast Nat.pos_of_ne_zero hn)
        (show (n : ℝ) ≤ N by exact_mod_cast hN.le)
    · simp only [F, if_neg hN, norm_zero]
      exact div_nonneg (hf n) (by positivity)
  have h := tendsto_tsum_of_dominated_convergence hsum hlim
    (Filter.Eventually.of_forall hbound)
  have heq (N : ℕ) : (∑' n, F N n) = cumsum f N / N := by
    rw [tsum_eq_sum (s := Finset.range N) (fun n hn => by
      simp only [Finset.mem_range] at hn
      simp [F, hn])]
    rw [cumsum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro n hn
    simp [F, Finset.mem_range.mp hn]
  simpa only [heq, tsum_zero] using h

end SevenEighths.PNT

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.PrimeCounting.IdealPrimeMass
namespace OAI

namespace SevenEighths.PNT.IdealPrimeMass

open ActualEisensteinCubic ArithmeticFunction Filter
open SevenEighths.IdealMangoldt
open scoped BigOperators Classical Topology

noncomputable section

theorem value_prime {P : Ideal O} (hP : Prime P) : value P = Real.log (Ideal.absNorm P) := by
  simpa only [pow_one] using value_pow hP (k := 1) (by decide)

theorem prime_of_isPrimePow_of_norm_prime {I : Ideal O}
    (hI : IsPrimePow I) (hn : (Ideal.absNorm I).Prime) : Prime I := by
  obtain ⟨P, k, hP, hk, rfl⟩ := hI
  rw [map_pow] at hn
  rw [hn.eq_one_of_pow, pow_one]
  exact hP

theorem value_eq_zero_of_nonprime_of_norm_prime {I : Ideal O}
    (hI : ¬Prime I) (hn : (Ideal.absNorm I).Prime) : value I = 0 := by
  apply if_neg
  exact fun hpow => hI (prime_of_isPrimePow_of_norm_prime hpow hn)

theorem primeClassCoeff_eq_sum_log (C : Set (Ideal O)) (n : ℕ) :
    primeClassCoeff C n =
      ∑ P ∈ (normFiber n).filter (fun P => P ∈ C ∧ Prime P), Real.log (Ideal.absNorm P) := by
  unfold primeClassCoeff classCoeff coeff
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro I hI
  by_cases h : I ∈ C ∧ Prime I
  · simp [h, value_prime h.2]
  · simp only [Set.mem_ofPred_eq, h, ite_false, zero_mul]

theorem primeClassCoeff_nonneg (C : Set (Ideal O)) (n : ℕ) : 0 ≤ primeClassCoeff C n :=
  classCoeff_nonneg _ n

theorem higherClassCoeff_nonneg (C : Set (Ideal O)) (n : ℕ) : 0 ≤ higherClassCoeff C n :=
  classCoeff_nonneg _ n

theorem classCoeff_eq_prime_add_higher (C : Set (Ideal O)) (n : ℕ) :
    classCoeff C n = primeClassCoeff C n + higherClassCoeff C n := by
  unfold primeClassCoeff higherClassCoeff classCoeff coeff
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro I hI
  by_cases hC : I ∈ C <;> by_cases hP : Prime I <;> simp [hC, hP]

@[simp] theorem higherClassCoeff_zero (C : Set (Ideal O)) : higherClassCoeff C 0 = 0 :=
  coeff_eq_zero_of_not_primePow not_isPrimePow_zero _

@[simp] theorem primeClassCoeff_zero (C : Set (Ideal O)) : primeClassCoeff C 0 = 0 :=
  coeff_eq_zero_of_not_primePow not_isPrimePow_zero _

theorem higherClassCoeff_eq_zero_of_prime (C : Set (Ideal O)) {n : ℕ} (hn : n.Prime) :
    higherClassCoeff C n = 0 := by
  apply Finset.sum_eq_zero
  intro I hI
  simp only [Set.mem_ofPred_eq]
  split_ifs with h
  · rw [value_eq_zero_of_nonprime_of_norm_prime h.2
      (by simpa only [(mem_normFiber n I).mp hI] using hn), mul_zero]
  · exact zero_mul _

theorem higherClassCoeff_le_nonprime_vonMangoldt (C : Set (Ideal O)) (n : ℕ) :
    higherClassCoeff C n ≤ 2 * (if n.Prime then 0 else vonMangoldt n) := by
  by_cases hn : n.Prime
  · rw [higherClassCoeff_eq_zero_of_prime C hn, if_pos hn, mul_zero]
  · rw [if_neg hn]
    exact classCoeff_le_two_vonMangoldt _ n

theorem summable_nonprime_vonMangoldt_div :
    Summable (fun n : ℕ => (if n.Prime then 0 else vonMangoldt n) / n) := by
  have h := vonMangoldt.summable_residueClass_non_primes_div (0 : ZMod 1)
  simpa only [vonMangoldt.residueClass, Subsingleton.elim (α := ZMod 1) _ 0,
    Set.ofPred_true, Set.indicator_univ] using h

theorem higherClassCoeff_summable_div (C : Set (Ideal O)) :
    Summable (fun n : ℕ => higherClassCoeff C n / n) := by
  apply (summable_nonprime_vonMangoldt_div.mul_left 2).of_nonneg_of_le
  · intro n
    exact div_nonneg (higherClassCoeff_nonneg C n) (Nat.cast_nonneg n)
  · intro n
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right (higherClassCoeff_le_nonprime_vonMangoldt C n)
      (Nat.cast_nonneg n)

theorem higherClassCoeff_ratio_tendsto_zero (C : Set (Ideal O)) :
    Tendsto (fun N : ℕ => cumsum (higherClassCoeff C) N / N) atTop (𝓝 0) :=
  cumsum_div_tendsto_zero_of_summable_div (higherClassCoeff_nonneg C)
    (higherClassCoeff_zero C) (higherClassCoeff_summable_div C)

theorem primeClassCoeff_ratio_tendsto (C : Set (Ideal O)) {A : ℝ}
    (h : Tendsto (fun N : ℕ => cumsum (classCoeff C) N / N) atTop (𝓝 A)) :
    Tendsto (fun N : ℕ => cumsum (primeClassCoeff C) N / N) atTop (𝓝 A) := by
  have h' := h.sub (higherClassCoeff_ratio_tendsto_zero C)
  have heq (N : ℕ) :
      cumsum (classCoeff C) N / N - cumsum (higherClassCoeff C) N / N =
        cumsum (primeClassCoeff C) N / N := by
    rw [← sub_div]
    congr 1
    simp only [cumsum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    rw [classCoeff_eq_prime_add_higher, add_sub_cancel_right]
  simpa only [heq, sub_zero] using h'

theorem primeLogMass_eq_cumsum (C : Set (Ideal O)) (N : ℕ) :
    primeLogMass C N = cumsum (primeClassCoeff C) N := by
  have hmap : ∀ P ∈ primeIdealsBelow C N, Ideal.absNorm P ∈ Finset.range N := by
    intro P hP
    exact Finset.mem_range.mpr ((mem_primeIdealsBelow C N P).mp hP).2.2
  rw [primeLogMass, ← Finset.sum_fiberwise_of_maps_to hmap]
  unfold cumsum
  apply Finset.sum_congr rfl
  intro n hn
  rw [primeClassCoeff_eq_sum_log]
  apply Finset.sum_congr
  · ext P
    simp only [Finset.mem_filter, mem_primeIdealsBelow, mem_normFiber]
    constructor
    · rintro ⟨⟨hC, hP, hN⟩, heq⟩
      exact ⟨heq, hC, hP⟩
    · rintro ⟨heq, hC, hP⟩
      exact ⟨⟨hC, hP, heq ▸ Finset.mem_range.mp hn⟩, heq⟩
  · intro P hP
    rfl

end

end SevenEighths.PNT.IdealPrimeMass

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.RayQuotient
namespace OAI

namespace SevenEighths.RayQuotient
open SevenEighths.RayOrthogonality
open scoped Classical
noncomputable section

variable {A : Type*} [CommRing A] (M : Ideal A) [Finite (A ⧸ M)]
    (H : Subgroup (A ⧸ M)ˣ) (hH : globalUnits M ≤ H)

theorem classNumber_pos : 0 < classNumber M H := ray_card_pos H

include hH

variable [IsDomain A] [IsPrincipalIdealRing A]

end
end SevenEighths.RayQuotient

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.PrimeCounting.AnnularPrimeMass
namespace OAI

namespace SevenEighths.PNT.AnnularPrimeMass

open ActualEisensteinCubic ArithmeticFunction Filter MeasureTheory
open SevenEighths.IdealMangoldt SevenEighths.PNT.IdealPrimeMass
open scoped BigOperators Classical Topology ContDiff

noncomputable section

theorem cumulative_ratio_tendsto {f : ℕ → ℝ} {A : ℝ}
    (h : Tendsto (fun N : ℕ => cumsum f N / N) atTop (𝓝 A)) :
    Tendsto (fun t : ℝ => cumulative f t / t) atTop (𝓝 A) := by
  have ht : Tendsto (fun t : ℝ => ⌊t⌋₊ + 1) atTop atTop :=
    tendsto_atTop_mono (fun _ => Nat.le_succ _) tendsto_nat_floor_atTop
  have hr : Tendsto (fun t : ℝ => ((⌊t⌋₊ + 1 : ℕ) : ℝ) / t) atTop (𝓝 1) := by
    convert (preTransparency := .instances) (tendsto_nat_floor_div_atTop (R := ℝ)).add
      (show Tendsto (fun t : ℝ => 1 / t) atTop (𝓝 0) by simpa only [one_div] using tendsto_inv_atTop_zero) using 1 <;> simp [add_div]
  convert (preTransparency := .instances) (h.comp ht).mul hr using 1
  · ext t
    simp only [Function.comp_def, cumulative]
    field_simp
  · simp

theorem scaledCumulative_tendsto {f : ℕ → ℝ} {A : ℝ}
    (h : Tendsto (fun N : ℕ => cumsum f N / N) atTop (𝓝 A))
    {y : ℝ} (hy : 0 < y) :
    Tendsto (fun x : ℝ => scaledCumulative f x y) atTop (𝓝 (A * y)) := by
  have ht : Tendsto (fun x : ℝ => x * y) atTop atTop := tendsto_id.atTop_mul_const hy
  apply ((cumulative_ratio_tendsto h).comp ht).mul_const y |>.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  unfold scaledCumulative
  dsimp only [Function.comp_def]
  field_simp

theorem cumulative_nonneg {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n) (t : ℝ) :
    0 ≤ cumulative f t := cumsum_nonneg hf _

theorem scaledCumulative_bound {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ N : ℕ, cumsum f N ≤ C * N)
    {x y b : ℝ} (hx : 1 ≤ x) (hy : 0 ≤ y) (hyb : y ≤ b) :
    ‖scaledCumulative f x y‖ ≤ C * (b + 1) := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  rw [scaledCumulative, Real.norm_eq_abs, abs_of_nonneg
    (div_nonneg (cumulative_nonneg hf _) hx0.le)]
  calc
    cumulative f (x * y) / x ≤ (C * (⌊x * y⌋₊ + 1 : ℕ)) / x := by
      exact div_le_div_of_nonneg_right (hbound _) hx0.le
    _ ≤ (C * (x * y + 1)) / x := by
      gcongr
      push_cast
      linarith [Nat.floor_le (mul_nonneg hx0.le hy)]
    _ ≤ C * (b + 1) := by
      rw [div_le_iff₀ hx0]
      nlinarith [mul_le_mul_of_nonneg_left hyb hx0.le,
        mul_nonneg hC (sub_nonneg.mpr hx)]

theorem measurable_cumulative (f : ℕ → ℝ) : Measurable (cumulative f) :=
  (measurable_of_countable (cumsum f)).comp (measurable_id.nat_floor.add_const 1)

theorem measurable_scaledCumulative (f : ℕ → ℝ) (x : ℝ) :
    Measurable (scaledCumulative f x) :=
  ((measurable_cumulative f).comp (measurable_const.mul measurable_id)).div_const x

theorem annularSum_div_eq_integral (f : ℕ → ℝ) (φ : ℝ → ℝ)
    (hφ : Differentiable ℝ φ) (hφ' : Continuous (deriv φ))
    {a b x : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hx : 0 < x)
    (hφa : φ a = 0) (hφb : φ b = 0) :
    annularSum f φ a b x / x =
      -(∫ y in a..b, deriv φ y * scaledCumulative f x y) := by
  let g : ℝ → ℝ := fun t => φ (t / x)
  have hg (t : ℝ) : HasDerivAt g (deriv φ (t / x) / x) t := by
    convert (preTransparency := .instances) (hφ (t / x)).hasDerivAt.comp t ((hasDerivAt_id t).div_const x) using 1 <;>
      simp only [g, Function.comp_def, div_eq_mul_inv, id_eq, one_mul]
  have hgc : Continuous (deriv g) := by
    have heq : deriv g = fun t => deriv φ (t / x) / x := funext (fun t => (hg t).deriv)
    rw [heq]
    exact (hφ'.comp (continuous_id.div_const x)).div_const x
  have h := sum_mul_eq_sub_sub_integral_mul f (a := x * a) (b := x * b)
    (mul_nonneg hx.le ha) (mul_le_mul_of_nonneg_left hab hx.le)
    (fun t _ => (hg t).differentiableAt) hgc.integrableOn_Icc
  have hcum (t : ℝ) : (∑ k ∈ Finset.Icc 0 ⌊t⌋₊, f k) = cumulative f t := by
    simp only [cumulative, cumsum, Nat.range_succ_eq_Icc_zero]
  simp_rw [hcum, (hg _).deriv] at h
  have hga : g (x * a) = 0 := by simp only [g, mul_div_cancel_left₀ _ hx.ne', hφa]
  have hgb : g (x * b) = 0 := by simp only [g, mul_div_cancel_left₀ _ hx.ne', hφb]
  rw [hga, hgb, zero_mul, zero_mul, sub_zero, zero_sub,
    ← intervalIntegral.integral_of_le (mul_le_mul_of_nonneg_left hab hx.le)] at h
  have hs : annularSum f φ a b x =
      -(∫ t in x * a..x * b, (deriv φ (t / x) / x) * cumulative f t) := by
    rw [← h]
    unfold annularSum g
    apply Finset.sum_congr rfl
    intro n hn
    ring
  rw [hs, neg_div]
  congr 1
  have hi := intervalIntegral.integral_comp_mul_left
    (fun t => (deriv φ (t / x) / x) * cumulative f t) hx.ne' (a := a) (b := b)
  simp only [smul_eq_mul, ← div_eq_inv_mul] at hi
  rw [← hi]
  apply intervalIntegral.integral_congr
  intro y hy
  simp only [mul_div_cancel_left₀ _ hx.ne', scaledCumulative]
  ring

theorem integral_scaledCumulative_tendsto {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n)
    {A C a b : ℝ} (hC : 0 ≤ C) (hbound : ∀ N : ℕ, cumsum f N ≤ C * N)
    (hmass : Tendsto (fun N : ℕ => cumsum f N / N) atTop (𝓝 A))
    (ha : 0 < a) (hab : a ≤ b) (g : ℝ → ℝ) (hg : Continuous g) :
    Tendsto (fun x : ℝ => ∫ y in a..b, g y * scaledCumulative f x y) atTop
      (𝓝 (∫ y in a..b, g y * (A * y))) := by
  simp_rw [intervalIntegral.integral_of_le hab]
  apply tendsto_integral_filter_of_dominated_convergence (fun y => ‖g y‖ * (C * (b + 1)))
  · exact Eventually.of_forall (fun x =>
      (hg.measurable.mul (measurable_scaledCumulative f x)).aestronglyMeasurable)
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left
      (scaledCumulative_bound hf hC hbound hx (ha.le.trans hy.1.le) hy.2) (norm_nonneg _)
  · exact (hg.norm.mul_const _).integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
    exact (scaledCumulative_tendsto hmass (ha.trans hy.1)).const_mul (g y)

theorem annularSum_div_tendsto {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n)
    {A C a b : ℝ} (hC : 0 ≤ C) (hbound : ∀ N : ℕ, cumsum f N ≤ C * N)
    (hmass : Tendsto (fun N : ℕ => cumsum f N / N) atTop (𝓝 A))
    (φ : ℝ → ℝ) (hφ : Differentiable ℝ φ) (hφ' : Continuous (deriv φ))
    (ha : 0 < a) (hab : a ≤ b) (hφa : φ a = 0) (hφb : φ b = 0) :
    Tendsto (fun x : ℝ => annularSum f φ a b x / x) atTop
      (𝓝 (A * ∫ y in a..b, φ y)) := by
  have h := (integral_scaledCumulative_tendsto hf hC hbound hmass ha hab (deriv φ) hφ').neg
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := fun y : ℝ => y) (u' := fun _ => (1 : ℝ)) (v := φ) (v' := deriv φ)
    (fun y _ => hasDerivAt_id y) (fun y _ => (hφ y).hasDerivAt)
    (continuous_const.intervalIntegrable a b) (hφ'.intervalIntegrable a b)
  have heq : -(∫ y in a..b, deriv φ y * (A * y)) = A * ∫ y in a..b, φ y := by
    have hfun : (fun y => deriv φ y * (A * y)) = fun y => A * (y * deriv φ y) := by
      ext y
      ring
    rw [hfun, intervalIntegral.integral_const_mul, hibp, hφa, hφb]
    simp
  rw [heq] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  exact (annularSum_div_eq_integral f φ hφ hφ' ha.le hab hx hφa hφb).symm

theorem primeLogAnnularSum_eq (C : Set (Ideal O)) (φ : ℝ → ℝ) (a b x : ℝ) :
    primeLogAnnularSum C φ a b x = annularSum (primeClassCoeff C) φ a b x := by
  have hmap : ∀ P ∈ annularPrimeIdeals C a b x,
      Ideal.absNorm P ∈ Finset.Ioc ⌊x * a⌋₊ ⌊x * b⌋₊ := by
    intro P hP
    exact Finset.mem_Ioc.mpr ((mem_annularPrimeIdeals C a b x P).mp hP).2.2
  rw [primeLogAnnularSum, ← Finset.sum_fiberwise_of_maps_to hmap]
  unfold annularSum
  apply Finset.sum_congr rfl
  intro n hn
  rw [primeClassCoeff_eq_sum_log, Finset.sum_mul]
  apply Finset.sum_congr
  · ext P
    simp only [Finset.mem_filter, mem_annularPrimeIdeals, mem_normFiber]
    constructor
    · rintro ⟨⟨hC, hP, hN⟩, heq⟩
      exact ⟨heq, hC, hP⟩
    · rintro ⟨heq, hC, hP⟩
      exact ⟨⟨hC, hP, heq ▸ Finset.mem_Ioc.mp hn⟩, heq⟩
  · intro P hP
    rw [(mem_normFiber n P).mp (Finset.mem_filter.mp hP).1]

theorem primeClassCoeff_chebyshev (C : Set (Ideal O)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℕ, cumsum (primeClassCoeff C) N ≤ B * N := by
  obtain ⟨B, hB⟩ := classCoeff_chebyshev {I | I ∈ C ∧ Prime I}
  have hbound (N : ℕ) : cumsum (primeClassCoeff C) N ≤ B * N := by
    convert (preTransparency := .instances) hB N using 1
    congr 1
    funext n
    exact (Complex.norm_of_nonneg (primeClassCoeff_nonneg C n)).symm
  refine ⟨B, ?_, hbound⟩
  have h := (cumsum_nonneg (primeClassCoeff_nonneg C) 1).trans (hbound 1)
  simpa only [Nat.cast_one, mul_one, Pi.zero_apply] using h

theorem primeLogAnnularSum_div_tendsto (C : Set (Ideal O)) {A a b : ℝ}
    (hmass : Tendsto (fun N : ℕ => cumsum (classCoeff C) N / N) atTop (𝓝 A))
    (φ : ℝ → ℝ) (hφ : Differentiable ℝ φ) (hφ' : Continuous (deriv φ))
    (ha : 0 < a) (hab : a ≤ b) (hφa : φ a = 0) (hφb : φ b = 0) :
    Tendsto (fun x : ℝ => primeLogAnnularSum C φ a b x / x) atTop
      (𝓝 (A * ∫ y in a..b, φ y)) := by
  obtain ⟨B, hB, hbound⟩ := primeClassCoeff_chebyshev C
  simpa only [primeLogAnnularSum_eq] using annularSum_div_tendsto
    (primeClassCoeff_nonneg C) hB hbound (primeClassCoeff_ratio_tendsto C hmass)
    φ hφ hφ' ha hab hφa hφb

theorem norm_bounds_of_mem_annularPrimeIdeals {C : Set (Ideal O)} {a b x : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hx : 0 < x) {P : Ideal O}
    (hP : P ∈ annularPrimeIdeals C a b x) :
    x * a < (Ideal.absNorm P : ℝ) ∧ (Ideal.absNorm P : ℝ) ≤ x * b := by
  have h := (mem_annularPrimeIdeals C a b x P).mp hP
  exact ⟨(Nat.floor_lt (mul_nonneg hx.le ha)).mp h.2.2.1,
    (Nat.le_floor_iff (mul_nonneg hx.le (ha.trans hab))).mp h.2.2.2⟩

theorem ratio_mem_of_mem_annularPrimeIdeals {C : Set (Ideal O)} {a b x : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hx : 0 < x) {P : Ideal O}
    (hP : P ∈ annularPrimeIdeals C a b x) :
    (Ideal.absNorm P : ℝ) / x ∈ Set.Icc a b := by
  obtain ⟨hl, hu⟩ := norm_bounds_of_mem_annularPrimeIdeals ha hab hx hP
  exact ⟨(le_div_iff₀ hx).mpr (by nlinarith), (div_le_iff₀ hx).mpr (by nlinarith)⟩

theorem log_norm_difference_bound {a b x : ℝ} (ha : 0 < a) (_hab : a ≤ b)
    (hx : 0 < x) {n : ℕ} (hn : (n : ℝ) / x ∈ Set.Icc a b) :
    |Real.log x - Real.log n| ≤ |Real.log a| + |Real.log b| := by
  have hn0 : 0 < (n : ℝ) := by
    have h := (le_div_iff₀ hx).mp hn.1
    exact (mul_pos ha hx).trans_le h
  have hl := Real.log_le_log ha hn.1
  have hu := Real.log_le_log (ha.trans_le hn.1) hn.2
  rw [Real.log_div hn0.ne' hx.ne'] at hl hu
  apply abs_le.mpr
  constructor <;> linarith [le_abs_self (Real.log a), neg_abs_le (Real.log a),
    le_abs_self (Real.log b), neg_abs_le (Real.log b), abs_nonneg (Real.log a),
    abs_nonneg (Real.log b)]

theorem annularPrime_card_div_bound (C : Set (Ideal O)) {B a b x : ℝ}
    (hB : 0 ≤ B) (hbound : ∀ N : ℕ, cumsum (primeClassCoeff C) N ≤ B * N)
    (ha : 0 < a) (hab : a ≤ b) (hx : 1 ≤ x) (hxa : 1 < x * a) :
    ((annularPrimeIdeals C a b x).card : ℝ) / x ≤ B * (b + 1) / Real.log (x * a) := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hlog : 0 < Real.log (x * a) := Real.log_pos hxa
  have hlower : Real.log (x * a) * (annularPrimeIdeals C a b x).card ≤
      ∑ P ∈ annularPrimeIdeals C a b x, Real.log (Ideal.absNorm P) := by
    rw [mul_comm, ← nsmul_eq_mul, ← Finset.sum_const]
    apply Finset.sum_le_sum
    intro P hP
    exact Real.log_le_log (mul_pos hx0 ha)
      (norm_bounds_of_mem_annularPrimeIdeals ha.le hab hx0 hP).1.le
  have hupper : (∑ P ∈ annularPrimeIdeals C a b x, Real.log (Ideal.absNorm P)) ≤
      cumsum (primeClassCoeff C) (⌊x * b⌋₊ + 1) := by
    rw [← primeLogMass_eq_cumsum, primeLogMass]
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    intro P hP _
    rw [← value_prime ((mem_primeIdealsBelow C _ P).mp hP).2.1]
    exact value_nonneg P
  have hnorm := scaledCumulative_bound (primeClassCoeff_nonneg C) hB hbound hx
    (ha.le.trans hab) (le_refl b)
  have hcum : cumsum (primeClassCoeff C) (⌊x * b⌋₊ + 1) / x ≤ B * (b + 1) :=
    (le_abs_self _).trans (by simpa only [Real.norm_eq_abs, scaledCumulative, cumulative] using hnorm)
  apply (le_div_iff₀ hlog).mpr
  calc
    ((annularPrimeIdeals C a b x).card : ℝ) / x * Real.log (x * a) =
        (Real.log (x * a) * (annularPrimeIdeals C a b x).card) / x := by ring
    _ ≤ (∑ P ∈ annularPrimeIdeals C a b x, Real.log (Ideal.absNorm P)) / x :=
      div_le_div_of_nonneg_right hlower hx0.le
    _ ≤ cumsum (primeClassCoeff C) (⌊x * b⌋₊ + 1) / x :=
      div_le_div_of_nonneg_right hupper hx0.le
    _ ≤ _ := hcum

theorem primeAnnularSum_log_error_bound (C : Set (Ideal O)) (φ : ℝ → ℝ)
    {B M a b x : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ N : ℕ, cumsum (primeClassCoeff C) N ≤ B * N)
    (hM : 0 ≤ M) (hφ : ∀ y ∈ Set.Icc a b, |φ y| ≤ M)
    (ha : 0 < a) (hab : a ≤ b) (hx : 1 ≤ x) (hxa : 1 < x * a) :
    ‖Real.log x * primeAnnularSum C φ a b x / x - primeLogAnnularSum C φ a b x / x‖ ≤
      ((|Real.log a| + |Real.log b|) * M) * (B * (b + 1) / Real.log (x * a)) := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have heq : Real.log x * primeAnnularSum C φ a b x - primeLogAnnularSum C φ a b x =
      ∑ P ∈ annularPrimeIdeals C a b x,
        (Real.log x - Real.log (Ideal.absNorm P)) * φ (Ideal.absNorm P / x) := by
    simp only [primeAnnularSum, primeLogAnnularSum, Finset.mul_sum, ← Finset.sum_sub_distrib,
      sub_mul]
  rw [← sub_div, heq, norm_div, Real.norm_of_nonneg hx0.le]
  calc
    _ ≤ (∑ P ∈ annularPrimeIdeals C a b x,
        ‖(Real.log x - Real.log (Ideal.absNorm P)) * φ (Ideal.absNorm P / x)‖) / x :=
      div_le_div_of_nonneg_right (norm_sum_le _ _) hx0.le
    _ ≤ (∑ _P ∈ annularPrimeIdeals C a b x, (|Real.log a| + |Real.log b|) * M) / x := by
      apply div_le_div_of_nonneg_right _ hx0.le
      apply Finset.sum_le_sum
      intro P hP
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      have hratio := ratio_mem_of_mem_annularPrimeIdeals ha.le hab hx0 hP
      exact mul_le_mul (log_norm_difference_bound ha hab hx0 hratio) (hφ _ hratio)
        (abs_nonneg _) (add_nonneg (abs_nonneg _) (abs_nonneg _))
    _ = ((|Real.log a| + |Real.log b|) * M) * ((annularPrimeIdeals C a b x).card / x) := by
      rw [Finset.sum_const, nsmul_eq_mul]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (annularPrime_card_div_bound C hB hbound ha hab hx hxa)
      (mul_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _)) hM)

theorem primeAnnularSum_log_error_tendsto (C : Set (Ideal O)) (φ : ℝ → ℝ)
    (hφ : Continuous φ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    Tendsto (fun x : ℝ => Real.log x * primeAnnularSum C φ a b x / x -
      primeLogAnnularSum C φ a b x / x) atTop (𝓝 0) := by
  obtain ⟨B, hB, hbound⟩ := primeClassCoeff_chebyshev C
  obtain ⟨M, hMbound⟩ := isCompact_Icc.exists_bound_of_continuousOn hφ.continuousOn
  have hM : 0 ≤ M := (norm_nonneg _).trans (hMbound a ⟨le_rfl, hab⟩)
  have hup : Tendsto (fun x : ℝ => ((|Real.log a| + |Real.log b|) * M) *
      (B * (b + 1) / Real.log (x * a))) atTop (𝓝 0) := by
    have hi := tendsto_inv_atTop_zero.comp
      (Real.tendsto_log_atTop.comp (tendsto_id.atTop_mul_const ha))
    convert (preTransparency := .instances) (hi.const_mul (B * (b + 1))).const_mul ((|Real.log a| + |Real.log b|) * M)
      using 1 <;> simp only [div_eq_mul_inv, mul_zero, Function.comp_def, id_eq]
  apply squeeze_zero_norm' _ hup
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    (tendsto_id.atTop_mul_const ha).eventually_gt_atTop 1] with x hx hxa
  exact primeAnnularSum_log_error_bound C φ hB hbound hM
    (fun y hy => by simpa only [Real.norm_eq_abs] using hMbound y hy) ha hab hx hxa

theorem primeAnnularSum_log_div_tendsto (C : Set (Ideal O)) {A a b : ℝ}
    (hmass : Tendsto (fun N : ℕ => cumsum (classCoeff C) N / N) atTop (𝓝 A))
    (φ : ℝ → ℝ) (hφ : Differentiable ℝ φ) (hφ' : Continuous (deriv φ))
    (ha : 0 < a) (hab : a ≤ b) (hφa : φ a = 0) (hφb : φ b = 0) :
    Tendsto (fun x : ℝ => Real.log x * primeAnnularSum C φ a b x / x) atTop
      (𝓝 (A * ∫ y in a..b, φ y)) := by
  have h := (primeAnnularSum_log_error_tendsto C φ hφ.continuous ha hab).add
    (primeLogAnnularSum_div_tendsto C hmass φ hφ hφ' ha hab hφa hφb)
  simpa only [sub_add_cancel, zero_add] using h

theorem contDiff_powerWeight (W : ℝ → ℝ) (hW : ContDiff ℝ ∞ W)
    {a b : ℝ} (ha : 0 < a) (hsupp : Function.support W ⊆ Set.Ioo a b) (r : ℝ) :
    ContDiff ℝ ∞ (fun y => W y * y ^ r) := by
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy : y = 0
  · subst y
    apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds ha] with y hy
    have hWy : W y = 0 := Function.notMem_support.mp (by
      intro h
      exact (not_lt_of_ge (hsupp h).1.le) hy)
    simp only [hWy, zero_mul]
  · exact hW.contDiffAt.mul (Real.contDiffAt_rpow_const_of_ne hy)

theorem weightedPrimeAnnularSum_normalization (C : Set (Ideal O)) (W : ℝ → ℝ)
    (a b : ℝ) {x : ℝ} (hx : 0 < x) :
    Real.log x / x ^ (1 / 6 : ℝ) * weightedPrimeAnnularSum C W a b x =
      Real.log x * primeAnnularSum C (fun y => W y * y ^ (-5 / 6 : ℝ)) a b x / x := by
  have heq : primeAnnularSum C (fun y => W y * y ^ (-5 / 6 : ℝ)) a b x =
      weightedPrimeAnnularSum C W a b x / x ^ (-5 / 6 : ℝ) := by
    unfold primeAnnularSum weightedPrimeAnnularSum
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro P hP
    dsimp only
    rw [Real.div_rpow (Nat.cast_nonneg _) hx.le]
    ring
  have hp : x ^ (-5 / 6 : ℝ) * x = x ^ (1 / 6 : ℝ) := by
    calc
      _ = x ^ (-5 / 6 : ℝ) * x ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = x ^ ((-5 / 6 : ℝ) + 1) := (Real.rpow_add hx _ _).symm
      _ = _ := by norm_num
  rw [heq, mul_div_assoc, div_div, hp]
  ring

theorem weightedPrimeAnnularSum_tendsto (C : Set (Ideal O)) {A a b : ℝ}
    (hmass : Tendsto (fun N : ℕ => cumsum (classCoeff C) N / N) atTop (𝓝 A))
    (W : ℝ → ℝ) (hW : ContDiff ℝ ∞ W)
    (ha : 0 < a) (hab : a ≤ b) (hsupp : Function.support W ⊆ Set.Ioo a b) :
    Tendsto (fun x : ℝ => Real.log x / x ^ (1 / 6 : ℝ) * weightedPrimeAnnularSum C W a b x)
      atTop (𝓝 (A * ∫ y : ℝ, W y * y ^ (-5 / 6 : ℝ))) := by
  let φ : ℝ → ℝ := fun y => W y * y ^ (-5 / 6 : ℝ)
  have hφ : ContDiff ℝ ∞ φ := contDiff_powerWeight W hW ha hsupp _
  have hWa : W a = 0 := Function.notMem_support.mp (fun h => (hsupp h).1.false)
  have hWb : W b = 0 := Function.notMem_support.mp (fun h => (hsupp h).2.false)
  have hφa : φ a = 0 := by simp only [φ, hWa, zero_mul]
  have hφb : φ b = 0 := by simp only [φ, hWb, zero_mul]
  have hint : (∫ y in a..b, φ y) = ∫ y, φ y := by
    rw [intervalIntegral.integral_of_le hab]
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro y hy
    have hWy : W y = 0 := Function.notMem_support.mp
      (fun h => hy ⟨(hsupp h).1, (hsupp h).2.le⟩)
    simp only [φ, hWy, zero_mul]
  have h := primeAnnularSum_log_div_tendsto C hmass φ (hφ.differentiable (by simp))
    (hφ.continuous_deriv (by simp)) ha hab hφa hφb
  rw [hint] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  exact (weightedPrimeAnnularSum_normalization C W a b hx).symm

theorem exists_positive_support_annulus (W : ℝ → ℝ) (hc : HasCompactSupport W)
    (hp : tsupport W ⊆ Set.Ioi 0) :
    ∃ a b : ℝ, 0 < a ∧ a < b ∧ Function.support W ⊆ Set.Ioo a b := by
  by_cases hne : (tsupport W).Nonempty
  · obtain ⟨m, hm, hmin⟩ := hc.exists_isMinOn hne continuous_id.continuousOn
    obtain ⟨M, hM, hmax⟩ := hc.exists_isMaxOn hne continuous_id.continuousOn
    have hm0 : 0 < m := hp hm
    have hmM : m ≤ M := hmin hM
    refine ⟨m / 2, M + 1, by positivity, by linarith, ?_⟩
    intro y hy
    have hyt : y ∈ tsupport W := subset_closure hy
    have hl : m ≤ y := hmin hyt
    have hu : y ≤ M := hmax hyt
    exact ⟨by linarith, by linarith⟩
  · refine ⟨1, 2, by norm_num, by norm_num, ?_⟩
    intro y hy
    exact (hne ⟨y, subset_closure hy⟩).elim

theorem mem_annularPrimeIdeals_of_weight_ne_zero {C : Set (Ideal O)} {W : ℝ → ℝ}
    {a b x : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hsupp : Function.support W ⊆ Set.Ioo a b) (hx : 0 < x)
    {P : Ideal O} (hC : P ∈ C) (hP : Prime P) (hW : W (Ideal.absNorm P / x) ≠ 0) :
    P ∈ annularPrimeIdeals C a b x := by
  have hy := hsupp hW
  apply (mem_annularPrimeIdeals C a b x P).mpr
  refine ⟨hC, hP, ?_, ?_⟩
  · apply (Nat.floor_lt (mul_nonneg hx.le ha.le)).mpr
    have h := (lt_div_iff₀ hx).mp hy.1
    nlinarith
  · apply (Nat.le_floor_iff (mul_nonneg hx.le (ha.le.trans hab))).mpr
    have h := (div_lt_iff₀ hx).mp hy.2
    nlinarith

theorem primeWeightTerm_support_subset (C : Set (Ideal O)) (W : ℝ → ℝ)
    {a b x : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hsupp : Function.support W ⊆ Set.Ioo a b) (hx : 0 < x) :
    Function.support (primeWeightTerm C W x) ⊆ (annularPrimeIdeals C a b x : Set (Ideal O)) := by
  intro P hP
  change primeWeightTerm C W x P ≠ 0 at hP
  unfold primeWeightTerm at hP
  split_ifs at hP with h
  · exact mem_annularPrimeIdeals_of_weight_ne_zero ha hab hsupp hx h.1 h.2
      (left_ne_zero_of_mul hP)
  · exact (hP rfl).elim

theorem weightedPrimeSum_eq_annular (C : Set (Ideal O)) (W : ℝ → ℝ)
    {a b x : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hsupp : Function.support W ⊆ Set.Ioo a b) (hx : 0 < x) :
    weightedPrimeSum C W x = weightedPrimeAnnularSum C W a b x := by
  rw [weightedPrimeSum, finsum_eq_finsetSum_of_support_subset _
    (primeWeightTerm_support_subset C W ha hab hsupp hx)]
  apply Finset.sum_congr rfl
  intro P hP
  have h := (mem_annularPrimeIdeals C a b x P).mp hP
  simp only [primeWeightTerm, h.1, h.2.1, and_self, ite_true]

theorem weightedPrimeSum_tendsto (C : Set (Ideal O)) {A : ℝ}
    (hmass : Tendsto (fun N : ℕ => cumsum (classCoeff C) N / N) atTop (𝓝 A))
    (W : ℝ → ℝ) (hW : ContDiff ℝ ∞ W) (hc : HasCompactSupport W)
    (hp : tsupport W ⊆ Set.Ioi 0) :
    Tendsto (fun x : ℝ => Real.log x / x ^ (1 / 6 : ℝ) * weightedPrimeSum C W x)
      atTop (𝓝 (A * ∫ y : ℝ, W y * y ^ (-5 / 6 : ℝ))) := by
  obtain ⟨a, b, ha, hab, hsupp⟩ := exists_positive_support_annulus W hc hp
  apply (weightedPrimeAnnularSum_tendsto C hmass W hW ha hab.le hsupp).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [weightedPrimeSum_eq_annular C W ha hab.le hsupp hx]

theorem finite_prime_weights_eventually_zero (C : Set (Ideal O)) (S : Finset (Ideal O))
    (W : ℝ → ℝ) (hp : tsupport W ⊆ Set.Ioi 0) :
    ∀ᶠ x : ℝ in atTop, ∀ P ∈ S, primeWeightTerm C W x P = 0 := by
  have hz : ∀ᶠ y in 𝓝 (0 : ℝ), W y = 0 :=
    notMem_tsupport_iff_eventuallyEq.mp (fun h => (show (0 : ℝ) < 0 from hp h).false)
  rw [eventually_all_finset]
  intro P hP
  have ht : Tendsto (fun x : ℝ => (Ideal.absNorm P : ℝ) / x) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using
      tendsto_inv_atTop_zero.const_mul (Ideal.absNorm P : ℝ)
  filter_upwards [ht hz] with x hx
  change W (Ideal.absNorm P / x) = 0 at hx
  simp only [primeWeightTerm, hx, zero_mul, ite_self]

theorem fixed_prime_deletion_eventually_eq (C : Set (Ideal O)) (S : Finset (Ideal O))
    (W : ℝ → ℝ) (hp : tsupport W ⊆ Set.Ioi 0) :
    weightedPrimeSumDeleted C S W =ᶠ[atTop] weightedPrimeSum C W := by
  filter_upwards [finite_prime_weights_eventually_zero C S W hp] with x hx
  unfold weightedPrimeSumDeleted weightedPrimeSum
  congr 1
  ext P
  by_cases hP : P ∈ S
  · simp only [hP, ite_true, hx P hP]
  · simp only [hP, ite_false]

theorem weightedPrimeSumDeleted_tendsto (C : Set (Ideal O)) (S : Finset (Ideal O)) {A : ℝ}
    (hmass : Tendsto (fun N : ℕ => cumsum (classCoeff C) N / N) atTop (𝓝 A))
    (W : ℝ → ℝ) (hW : ContDiff ℝ ∞ W) (hc : HasCompactSupport W)
    (hp : tsupport W ⊆ Set.Ioi 0) :
    Tendsto (fun x : ℝ => Real.log x / x ^ (1 / 6 : ℝ) * weightedPrimeSumDeleted C S W x)
      atTop (𝓝 (A * ∫ y : ℝ, W y * y ^ (-5 / 6 : ℝ))) := by
  apply (weightedPrimeSum_tendsto C hmass W hW hc hp).congr'
  filter_upwards [fixed_prime_deletion_eventually_eq C S W hp] with x hx
  rw [hx]

theorem weightedPrimeSumDeleted_eq_annular (C : Set (Ideal O)) (S : Finset (Ideal O))
    (W : ℝ → ℝ) {a b x : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hsupp : Function.support W ⊆ Set.Ioo a b) (hx : 0 < x) :
    weightedPrimeSumDeleted C S W x =
      ∑ P ∈ annularPrimeIdeals C a b x \ S,
        W (Ideal.absNorm P / x) * (Ideal.absNorm P : ℝ) ^ (-5 / 6 : ℝ) := by
  have hsub : Function.support (fun P => if P ∈ S then 0 else primeWeightTerm C W x P) ⊆
      (↑(annularPrimeIdeals C a b x \ S) : Set (Ideal O)) := by
    intro P hP
    change (if P ∈ S then 0 else primeWeightTerm C W x P) ≠ 0 at hP
    by_cases hPS : P ∈ S
    · simp only [hPS, ite_true, ne_self_iff_false] at hP
    · simp only [hPS, ite_false] at hP
      exact Finset.mem_sdiff.mpr ⟨primeWeightTerm_support_subset C W ha hab hsupp hx hP, hPS⟩
  rw [weightedPrimeSumDeleted, finsum_eq_finsetSum_of_support_subset _ hsub]
  apply Finset.sum_congr rfl
  intro P hP
  have hS := (Finset.mem_sdiff.mp hP).2
  have h := (mem_annularPrimeIdeals C a b x P).mp (Finset.mem_sdiff.mp hP).1
  simp only [hS, ite_false, primeWeightTerm, h.1, h.2.1, and_self, ite_true]

theorem powerWeight_integral_pos (W : ℝ → ℝ) (hW : ContDiff ℝ ∞ W)
    (hc : HasCompactSupport W) (hp : tsupport W ⊆ Set.Ioi 0)
    (hW0 : ∀ y, 0 ≤ W y) (hWne : W ≠ 0) :
    0 < ∫ y : ℝ, W y * y ^ (-5 / 6 : ℝ) := by
  obtain ⟨a, b, ha, hab, hsupp⟩ := exists_positive_support_annulus W hc hp
  have hφ := contDiff_powerWeight W hW ha hsupp (-5 / 6)
  obtain ⟨y, hy⟩ : ∃ y : ℝ, W y ≠ 0 := by
    by_contra h
    push Not at h
    exact hWne (funext h)
  have hy0 : 0 < y := hp (subset_closure hy)
  apply hφ.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero hc.mul_right
  · intro z
    by_cases hz : W z = 0
    · simp only [hz, zero_mul, Pi.zero_apply, le_refl]
    · have hz0 : 0 < z := hp (subset_closure hz)
      exact mul_nonneg (hW0 z) (Real.rpow_nonneg hz0.le _)
  · exact mul_ne_zero hy (Real.rpow_pos_of_pos hy0 _).ne'

theorem weightedPrimeSumDeleted_eventually_lower_bound (C : Set (Ideal O))
    (S : Finset (Ideal O)) {A : ℝ} (hA : 0 < A)
    (hmass : Tendsto (fun N : ℕ => cumsum (classCoeff C) N / N) atTop (𝓝 A))
    (W : ℝ → ℝ) (hW : ContDiff ℝ ∞ W) (hc : HasCompactSupport W)
    (hp : tsupport W ⊆ Set.Ioi 0) (hW0 : ∀ y, 0 ≤ W y) (hWne : W ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ x : ℝ in atTop,
      c * x ^ (1 / 6 : ℝ) / Real.log x ≤ weightedPrimeSumDeleted C S W x := by
  let L : ℝ := A * ∫ y : ℝ, W y * y ^ (-5 / 6 : ℝ)
  have hL : 0 < L := mul_pos hA (powerWeight_integral_pos W hW hc hp hW0 hWne)
  refine ⟨L / 2, half_pos hL, ?_⟩
  have ht := weightedPrimeSumDeleted_tendsto C S hmass W hW hc hp
  have he := ht (Ioi_mem_nhds (half_lt_self hL))
  filter_upwards [he, eventually_gt_atTop (1 : ℝ)] with x hx hx1
  change L / 2 < Real.log x / x ^ (1 / 6 : ℝ) * weightedPrimeSumDeleted C S W x at hx
  have hxp : 0 < x ^ (1 / 6 : ℝ) := Real.rpow_pos_of_pos (zero_lt_one.trans hx1) _
  apply (div_le_iff₀ (Real.log_pos hx1)).mpr
  have hmul := (le_div_iff₀ hxp).mp (show L / 2 ≤
      (Real.log x * weightedPrimeSumDeleted C S W x) / x ^ (1 / 6 : ℝ) by
    convert (preTransparency := .instances) hx.le using 1; ring)
  nlinarith

theorem weightedPrimeSumDeleted_eventually_pos (C : Set (Ideal O))
    (S : Finset (Ideal O)) {A : ℝ} (hA : 0 < A)
    (hmass : Tendsto (fun N : ℕ => cumsum (classCoeff C) N / N) atTop (𝓝 A))
    (W : ℝ → ℝ) (hW : ContDiff ℝ ∞ W) (hc : HasCompactSupport W)
    (hp : tsupport W ⊆ Set.Ioi 0) (hW0 : ∀ y, 0 ≤ W y) (hWne : W ≠ 0) :
    ∀ᶠ x : ℝ in atTop, 0 < weightedPrimeSumDeleted C S W x := by
  obtain ⟨c, hc0, he⟩ := weightedPrimeSumDeleted_eventually_lower_bound C S hA hmass
    W hW hc hp hW0 hWne
  filter_upwards [he, eventually_gt_atTop (1 : ℝ)] with x hx hx1
  exact (div_pos (mul_pos hc0 (Real.rpow_pos_of_pos (zero_lt_one.trans hx1) _))
    (Real.log_pos hx1)).trans_le hx

end

end SevenEighths.PNT.AnnularPrimeMass

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.RayPrimeNormalizer
namespace OAI

noncomputable section
open Filter MeasureTheory
open scoped Classical Topology ContDiff
namespace SevenEighths.RayPrimeNormalizer
open HeckeFamily
variable (M : Ideal O) [NeZero M]
local instance instFiniteQuotientOIdeal_solutions : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

include hH

theorem eventually_lower_bound (S : Finset (Ideal O)) (W : ℝ → ℝ)
    (hW : ContDiff ℝ ∞ W) (hc : HasCompactSupport W) (hp : tsupport W ⊆ Set.Ioi 0)
    (hW0 : ∀ y, 0 ≤ W y) (hWne : W ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ x : ℝ in atTop,
      c * x ^ (1/6 : ℝ) / Real.log x ≤ normalizer M H S W x := by
  apply PNT.AnnularPrimeMass.weightedPrimeSumDeleted_eventually_lower_bound _ S
    (show 0 < (RayQuotient.classNumber M H : ℝ)⁻¹ from inv_pos.mpr (by
      exact_mod_cast RayQuotient.classNumber_pos M H))
    (HeckeRayPrimes.quotientClassCoeff_ratio_tendsto M H hH) W hW hc hp hW0 hWne

theorem eventually_pos (S : Finset (Ideal O)) (W : ℝ → ℝ)
    (hW : ContDiff ℝ ∞ W) (hc : HasCompactSupport W) (hp : tsupport W ⊆ Set.Ioi 0)
    (hW0 : ∀ y, 0 ≤ W y) (hWne : W ≠ 0) :
    ∀ᶠ x : ℝ in atTop, 0 < normalizer M H S W x := by
  apply PNT.AnnularPrimeMass.weightedPrimeSumDeleted_eventually_pos _ S
    (show 0 < (RayQuotient.classNumber M H : ℝ)⁻¹ from inv_pos.mpr (by
      exact_mod_cast RayQuotient.classNumber_pos M H))
    (HeckeRayPrimes.quotientClassCoeff_ratio_tendsto M H hH) W hW hc hp hW0 hWne

end SevenEighths.RayPrimeNormalizer

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.RaySlots
namespace OAI

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter
namespace SevenEighths.ProbeRaySlots
open HeckeFamily ProbePhysical PNT.AnnularPrimeMass
open PrincipalSignalComparison ProbePrincipalResidueActual
local notation "Id" => Ideal HeckeFamily.O

theorem pool_norm_bounds (C : Set Id) (S : Finset Id) {a b x : ℝ}
    (ha : 0≤a) (hab : a≤b) (hx : 0<x) (P : PrimeIdeal) (hP : P∈pool C S a b x) :
    x*a<(Ideal.absNorm P.val:ℝ) ∧ (Ideal.absNorm P.val:ℝ)≤x*b :=
  norm_bounds_of_mem_annularPrimeIdeals ha hab hx
    (Finset.mem_sdiff.mp (Finset.mem_subtype.mp hP)).1

lemma pool_sum (C : Set Id) (S : Finset Id) (a b x : ℝ) (f : Id→ℝ) :
    (∑P∈pool C S a b x,f P.val)=∑P∈annularPrimeIdeals C a b x\S,f P := by
  apply Finset.sum_bij (fun P _=>P.val)
  · intro P hP
    exact Finset.mem_subtype.mp hP
  · intro P hP Q hQ he
    exact Subtype.ext he
  · intro P hP
    have hp : Prime P := ((mem_annularPrimeIdeals C a b x P).mp (Finset.mem_sdiff.mp hP).1).2.1
    exact ⟨⟨P,hp⟩,Finset.mem_subtype.mpr hP,rfl⟩
  · intro P hP
    rfl

theorem pool_mass_eq_deleted (C : Set Id) (S : Finset Id) (W : ℝ→ℝ)
    {a b x : ℝ} (ha : 0<a) (hab : a≤b)
    (hsupp : Function.support W⊆Set.Ioo a b) (hx : 0<x) :
    (∑P∈pool C S a b x,W ((Ideal.absNorm P.val:ℝ)/x)*(Ideal.absNorm P.val:ℝ)^(-(5/6:ℝ)))=
      weightedPrimeSumDeleted C S W x := by
  rw [pool_sum C S a b x (fun P=>W ((Ideal.absNorm P:ℝ)/x)*(Ideal.absNorm P:ℝ)^(-(5/6:ℝ))),
    weightedPrimeSumDeleted_eq_annular C S W ha hab hsupp hx]
  norm_num

variable (M : Id) [NeZero M]
variable (H : Subgroup (HeckeFamily.O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

include hH

local instance instFiniteQuotientOIdeal_solutions_re5ec66_1 : Finite (HeckeFamily.O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
theorem ray_pool_mass_eventually_positive (S : Finset Id) (W : ℝ→ℝ)
    (a b : ℝ) (ha : 0<a) (hab : a≤b) (hsupp : Function.support W⊆Set.Ioo a b)
    (hW : ContDiff ℝ ∞ W) (hc : HasCompactSupport W) (hp : tsupport W⊆Set.Ioi 0)
    (hW0 : ∀y,0≤W y) (hWne : W≠0) :
    ∀ᶠx : ℝ in atTop,0<∑P∈pool (RayQuotient.identityClass M H) S a b x,
      W ((Ideal.absNorm P.val:ℝ)/x)*(Ideal.absNorm P.val:ℝ)^(-(5/6:ℝ)) := by
  filter_upwards [RayPrimeNormalizer.eventually_pos M H hH S W hW hc hp hW0 hWne,
    eventually_gt_atTop (0:ℝ)] with x hx hx0
  rw [pool_mass_eq_deleted _ _ _ ha hab hsupp hx0]
  exact hx

theorem ray_pool_mass_eventually_lower_bound (S : Finset Id) (W : ℝ→ℝ)
    (a b : ℝ) (ha : 0<a) (hab : a≤b) (hsupp : Function.support W⊆Set.Ioo a b)
    (hW : ContDiff ℝ ∞ W) (hc : HasCompactSupport W) (hp : tsupport W⊆Set.Ioi 0)
    (hW0 : ∀y,0≤W y) (hWne : W≠0) :
    ∃c : ℝ,0<c ∧ ∀ᶠx : ℝ in atTop,c*x^(1/6:ℝ)/Real.log x≤
      ∑P∈pool (RayQuotient.identityClass M H) S a b x,
        W ((Ideal.absNorm P.val:ℝ)/x)*(Ideal.absNorm P.val:ℝ)^(-(5/6:ℝ)) := by
  obtain ⟨c,hc0,hbound⟩ := RayPrimeNormalizer.eventually_lower_bound M H hH S W hW hc hp hW0 hWne
  refine ⟨c,hc0,?_⟩
  filter_upwards [hbound,eventually_gt_atTop (0:ℝ)] with x hx hx0
  rw [pool_mass_eq_deleted _ _ _ ha hab hsupp hx0]
  exact hx

end SevenEighths.ProbeRaySlots
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.RayNormalization
namespace OAI

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter
namespace SevenEighths.ProbeRayNormalization
open HeckeFamily ProbePhysical ProbeRaySlots
local notation "Id" => Ideal HeckeFamily.O

theorem log_power_absorption (c ell d : ℝ) (hc : 0<c) (hell : 0<ell) (hd : 0<d) :
    ∀ᶠZ : ℝ in atTop,Z^(ell/6-d)≤ c*(Z^ell)^(1/6:ℝ)/Real.log (Z^ell) := by
  have hh := (isLittleO_log_rpow_atTop hd).bound (div_pos hc hell)
  filter_upwards [hh,eventually_gt_atTop (1:ℝ)] with Z hZ hZ1
  have hZ0 : 0<Z := by linarith
  have hlog : 0<Real.log Z := Real.log_pos hZ1
  have hzd : 0<Z^d := Real.rpow_pos_of_pos hZ0 _
  have hb : ell*Real.log Z≤ c*Z^d := by
    have hb' : Real.log Z≤(c/ell)*Z^d := by
      simpa only [Real.norm_eq_abs,abs_of_pos hlog,abs_of_pos hzd] using hZ
    calc
      _ ≤ ell*((c/ell)*Z^d) := mul_le_mul_of_nonneg_left hb' hell.le
      _ = _ := by field_simp
  rw [Real.log_rpow hZ0,←Real.rpow_mul hZ0.le]
  apply (le_div_iff₀ (mul_pos hell hlog)).mpr
  calc
    Z^(ell/6-d)*(ell*Real.log Z) ≤ Z^(ell/6-d)*(c*Z^d) :=
      mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hZ0.le _)
    _ = c*Z^(ell*(1/6:ℝ)) := by
      rw [mul_left_comm,←Real.rpow_add hZ0]
      congr 1
      ring_nf

theorem principalScalar_inverse_of_slot_bounds {ι : Type*} (J : Finset ι)
    (ell mass : ι→ℝ) (Z d eps : ℝ) (hZ : 1≤Z) (_hd : 0≤d)
    (hbudget : d*J.card≤eps) (hm : ∀i∈J,Z^(ell i/6-d)≤ mass i) :
    |(Probe.principalScalar J Z (∑i∈J,ell i) mass)⁻¹|≤Z^eps := by
  have hZ0 : 0<Z := by linarith
  have hm0 : ∀i∈J,0≤ mass i := fun i hi=>(Real.rpow_nonneg hZ0.le _).trans (hm i hi)
  have hprod : Z^(∑i∈J,(ell i/6-d))≤∏i∈J,mass i := by
    rw [Real.rpow_sum_of_pos hZ0]
    exact Finset.prod_le_prod (fun i _=>Real.rpow_nonneg hZ0.le _) hm
  have hn : |Probe.principalScalar J Z (∑i∈J,ell i) mass|=
      Z^(-(∑i∈J,ell i)/6)*(∏i∈J,mass i) := by
    unfold Probe.principalScalar
    rw [abs_mul,abs_mul,abs_pow,abs_neg,abs_one,one_pow,one_mul,
      abs_of_pos (Real.rpow_pos_of_pos hZ0 _),abs_of_nonneg (Finset.prod_nonneg hm0)]
  have hpow : Z^(-(∑i∈J,ell i)/6)*Z^(∑i∈J,(ell i/6-d))=Z^(-d*J.card) := by
    rw [←Real.rpow_add hZ0]
    congr 1
    rw [Finset.sum_sub_distrib,←Finset.sum_div,Finset.sum_const,nsmul_eq_mul]
    ring
  have hl : Z^(-eps)≤|Probe.principalScalar J Z (∑i∈J,ell i) mass| := by
    calc
      _ ≤ Z^(-d*J.card) := Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
      _ = Z^(-(∑i∈J,ell i)/6)*Z^(∑i∈J,(ell i/6-d)) := hpow.symm
      _ ≤ _ := by rw [hn];exact mul_le_mul_of_nonneg_left hprod (Real.rpow_nonneg hZ0.le _)
  rw [abs_inv]
  have hi := (inv_le_inv₀ ((Real.rpow_pos_of_pos hZ0 (-eps)).trans_le hl)
    (Real.rpow_pos_of_pos hZ0 (-eps))).mpr hl
  simpa only [Real.rpow_neg hZ0.le,inv_inv] using hi

variable (M : Id) [NeZero M]
variable (H : Subgroup (HeckeFamily.O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)
include hH

local instance instFiniteQuotientOIdeal_solutions_re5ec66_2 : Finite (HeckeFamily.O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
theorem ray_slot_subpower_lower (S : Finset Id) (W : ℝ→ℝ)
    (a b : ℝ) (ha : 0<a) (hab : a≤b) (hsupp : Function.support W⊆Set.Ioo a b)
    (hW : ContDiff ℝ ∞ W) (hc : HasCompactSupport W) (hp : tsupport W⊆Set.Ioi 0)
    (hW0 : ∀y,0≤W y) (hWne : W≠0) (ell d : ℝ) (hell : 0<ell) (hd : 0<d) :
    ∀ᶠZ : ℝ in atTop,Z^(ell/6-d)≤
      ∑P∈pool (RayQuotient.identityClass M H) S a b (Z^ell),
        W ((Ideal.absNorm P.val:ℝ)/(Z^ell))*(Ideal.absNorm P.val:ℝ)^(-(5/6:ℝ)) := by
  obtain ⟨c,hc0,hbound⟩ := ray_pool_mass_eventually_lower_bound M H hH S W a b ha hab hsupp hW hc hp hW0 hWne
  filter_upwards [(tendsto_rpow_atTop hell).eventually hbound,log_power_absorption c ell d hc0 hell hd]
    with Z hZ hlog
  exact hlog.trans hZ

theorem ray_principalScalar_inverse_subpower {ι : Type*} (J : Finset ι)
    (S : Finset Id) (W : ι→ℝ→ℝ) (a b ell : ι→ℝ)
    (ha : ∀i∈J,0<a i) (hab : ∀i∈J,a i≤b i)
    (hsupp : ∀i∈J,Function.support (W i)⊆Set.Ioo (a i) (b i))
    (hW : ∀i∈J,ContDiff ℝ ∞ (W i)) (hc : ∀i∈J,HasCompactSupport (W i))
    (hp : ∀i∈J,tsupport (W i)⊆Set.Ioi 0)
    (hW0 : ∀i∈J,∀y,0≤W i y) (hWne : ∀i∈J,W i≠0) (hell : ∀i∈J,0<ell i)
    (eps : ℝ) (heps : 0<eps) :
    ∀ᶠZ : ℝ in atTop,
      |(Probe.principalScalar J Z (∑i∈J,ell i) (fun i=>
        ∑P∈pool (RayQuotient.identityClass M H) S (a i) (b i) (Z^(ell i)),
          W i ((Ideal.absNorm P.val:ℝ)/(Z^(ell i)))*(Ideal.absNorm P.val:ℝ)^(-(5/6:ℝ))))⁻¹|≤Z^eps := by
  let d : ℝ := eps/(J.card+1)
  have hd : 0<d := div_pos heps (by positivity)
  have hb : d*J.card≤eps := by
    dsimp [d]
    rw [div_mul_eq_mul_div,div_le_iff₀ (by positivity : (0:ℝ)<J.card+1)]
    nlinarith
  have hm : ∀ᶠZ : ℝ in atTop,∀i∈J,Z^(ell i/6-d)≤
      ∑P∈pool (RayQuotient.identityClass M H) S (a i) (b i) (Z^(ell i)),
        W i ((Ideal.absNorm P.val:ℝ)/(Z^(ell i)))*(Ideal.absNorm P.val:ℝ)^(-(5/6:ℝ)) := by
    apply (Filter.eventually_all_finset J).mpr
    intro i hi
    exact ray_slot_subpower_lower M H hH S (W i) (a i) (b i) (ha i hi) (hab i hi)
      (hsupp i hi) (hW i hi) (hc i hi) (hp i hi) (hW0 i hi) (hWne i hi) (ell i) d (hell i hi) hd
  filter_upwards [hm,eventually_ge_atTop (1:ℝ)] with Z hmass hZ
  exact principalScalar_inverse_of_slot_bounds J ell _ Z d eps hZ hd.le hb hmass

end SevenEighths.ProbeRayNormalization
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.RayPoolDisjoint
namespace OAI

noncomputable section
open scoped Classical Topology
open Filter
namespace SevenEighths.ProbeRaySlots
open HeckeFamily ProbePhysical
local notation "Id" => Ideal HeckeFamily.O

lemma annular_power_separation (a b r s : ℝ) (ha : 0<a) (hrs : r<s) :
    ∀ᶠZ : ℝ in atTop,b*Z^r<a*Z^s := by
  have hh := (tendsto_rpow_atTop (show 0<s-r by linarith)).eventually (eventually_gt_atTop (b/a))
  filter_upwards [hh,eventually_gt_atTop (0:ℝ)] with Z hZ hZ0
  have ht : b<a*Z^(s-r) := by
    have h := (div_lt_iff₀ ha).mp hZ
    nlinarith
  have hp : 0<Z^r := Real.rpow_pos_of_pos hZ0 _
  calc
    b*Z^r < (a*Z^(s-r))*Z^r := mul_lt_mul_of_pos_right ht hp
    _=a*Z^s := by rw [mul_assoc,←Real.rpow_add hZ0];congr 1;congr 1;ring

theorem power_pools_eventually_disjoint {ι : Type*} [Fintype ι]
    (C : Set Id) (S : Finset Id) (a b ell : ι→ℝ)
    (ha : ∀i,0<a i) (hab : ∀i,a i≤b i) (hell : Function.Injective ell) :
    ∀ᶠZ : ℝ in atTop,∀i j, i≠j→Disjoint (pool C S (a i) (b i) (Z^(ell i)))
      (pool C S (a j) (b j) (Z^(ell j))) := by
  apply Filter.eventually_all.mpr
  intro i
  apply Filter.eventually_all.mpr
  intro j
  by_cases hij : i=j
  · exact Filter.Eventually.of_forall (fun Z hn=>(hn hij).elim)
  have hne : ell i≠ell j := fun h=>hij (hell h)
  rcases lt_or_gt_of_ne hne with hlt|hgt
  · filter_upwards [annular_power_separation (a j) (b i) (ell i) (ell j) (ha j) hlt,
      eventually_gt_atTop (0:ℝ)] with Z hsep hZ _
    apply Finset.disjoint_left.mpr
    intro P hPi hPj
    have hi := pool_norm_bounds C S (ha i).le (hab i) (Real.rpow_pos_of_pos hZ _) P hPi
    have hj := pool_norm_bounds C S (ha j).le (hab j) (Real.rpow_pos_of_pos hZ _) P hPj
    nlinarith
  · filter_upwards [annular_power_separation (a i) (b j) (ell j) (ell i) (ha i) hgt,
      eventually_gt_atTop (0:ℝ)] with Z hsep hZ _
    apply Finset.disjoint_left.mpr
    intro P hPi hPj
    have hi := pool_norm_bounds C S (ha i).le (hab i) (Real.rpow_pos_of_pos hZ _) P hPi
    have hj := pool_norm_bounds C S (ha j).le (hab j) (Real.rpow_pos_of_pos hZ _) P hPj
    nlinarith

theorem power_pool_tuples_eventually_injective {ι : Type*} [Fintype ι]
    (C : Set Id) (S : Finset Id) (a b ell : ι→ℝ)
    (ha : ∀i,0<a i) (hab : ∀i,a i≤b i) (hell : Function.Injective ell) :
    ∀ᶠZ : ℝ in atTop,∀P:(∀i,pool C S (a i) (b i) (Z^(ell i))),
      Function.Injective (fun i=>(P i).val) := by
  filter_upwards [power_pools_eventually_disjoint C S a b ell ha hab hell] with Z hZ P
  intro i j heq
  by_contra hn
  have hq : (P i).val=(P j).val := heq
  exact Finset.disjoint_left.mp (hZ i j hn) (P i).property (by rw [hq];exact (P j).property)
end SevenEighths.ProbeRaySlots
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.RayPoolGood
namespace OAI

noncomputable section
open scoped Classical Topology
open Filter
namespace SevenEighths.ProbeRaySlots
open HeckeFamily ProbePhysical CanonicalQuadraticSieve PrincipalSignalComparison
local notation "Id" => Ideal HeckeFamily.O

theorem prime_coprime_of_norm_gt (η : Character) (P : PrimeIdeal)
    (hN : (η.modulus.absNorm:ℝ)<(P.val.absNorm:ℝ)) : IsCoprime P.val η.modulus := by
  apply Ideal.coprime_of_no_prime_ge
  intro J hPJ hηJ hJ
  have hmax := (Ideal.isPrime_of_prime P.property).isMaximal P.property.ne_zero
  have heq := hmax.eq_of_le hJ.ne_top hPJ
  rw [←heq] at hηJ
  have hd : P.val∣η.modulus := Ideal.dvd_iff_le.mpr hηJ
  have hn := Nat.le_of_dvd (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr η.modulus_ne_bot))
    (map_dvd Ideal.absNorm hd)
  exact (not_le_of_gt hN) (by exact_mod_cast hn)

end SevenEighths.ProbeRaySlots
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.RayPoolThresholds
namespace OAI

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter
namespace SevenEighths.ProbeRaySlots
open HeckeFamily ProbePhysical PrincipalSignalComparison ProbePrincipalResidueActual
local notation "Id" => Ideal HeckeFamily.O

theorem power_pool_thresholds {ι : Type*} [Fintype ι]
    (C : Set Id) (S : Finset Id) (η : Character) (c d ellMin : ℝ)
    (hc : 0<c) (hd : c≤d) (hmin : 0<ellMin)
    (ell : ι→ℝ) (hell : ∀j,ellMin≤ell j) :
    ∀ᶠZ : ℝ in atTop,
      1≤Z ∧ 480≤ c*Z^ellMin ∧ 1440*(c*Z^ellMin)^(-(7/8:ℝ))≤1 ∧
      (∀j,480≤ c*Z^(ell j) ∧ (η.modulus.absNorm:ℝ)<c*Z^(ell j)) ∧
      (∀j,∀P∈pool C S c d (Z^(ell j)),
        c*Z^ellMin≤(P.val.absNorm:ℝ) ∧ IsCoprime P.val η.modulus ∧ P.val∉S) := by
  have ht := (tendsto_rpow_atTop hmin).const_mul_atTop hc
  have hs : Tendsto (fun Z : ℝ=>1440*(c*Z^ellMin)^(-(7/8:ℝ))) atTop (nhds 0) := by
    simpa only [mul_zero,Function.comp_def] using ((tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<7/8)).comp ht).const_mul (1440:ℝ)
  filter_upwards [eventually_ge_atTop (1:ℝ),ht.eventually (eventually_ge_atTop (480:ℝ)),
    ht.eventually (eventually_gt_atTop (η.modulus.absNorm:ℝ)),
    hs.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1))] with Z hZ h480 hmod hsmall
  have hZ0 : 0<Z := by linarith
  have hmono (j : ι) : c*Z^ellMin≤ c*Z^(ell j) := mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hZ (hell j)) hc.le
  refine ⟨hZ,h480,hsmall.le,fun j=>⟨h480.trans (hmono j),hmod.trans_le (hmono j)⟩,?_⟩
  intro j P hP
  have hp := pool_norm_bounds C S hc.le hd (Real.rpow_pos_of_pos hZ0 _) P hP
  have hn : c*Z^ellMin<(P.val.absNorm:ℝ) := (hmono j).trans_lt (by simpa only [mul_comm] using hp.1)
  exact ⟨hn.le,prime_coprime_of_norm_gt η P (hmod.trans hn),(mem_pool C S c d _ P).mp hP |>.2.2.2⟩

variable (M : Id) [NeZero M]
variable (H : Subgroup (HeckeFamily.O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)
include hH

local instance instFiniteQuotientOIdeal_solutions_1_re5ec66_1 : Finite (HeckeFamily.O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
theorem power_ray_mass_and_normalizer {ι : Type*} [Fintype ι]
    (S : Finset Id) (W : ι→ℝ→ℝ) (c d : ℝ) (hc : 0<c) (hd : c≤d)
    (hsupp : ∀j,Function.support (W j)⊆Set.Ioo c d)
    (hW : ∀j,ContDiff ℝ ∞ (W j)) (hcompact : ∀j,HasCompactSupport (W j))
    (hp : ∀j,tsupport (W j)⊆Set.Ioi 0) (hW0 : ∀j y,0≤W j y) (hne : ∀j,W j≠0)
    (ell : ι→ℝ) (hell : ∀j,0<ell j) (eps : ℝ) (heps : 0<eps) :
    ∀ᶠZ : ℝ in atTop,
      let T := fun j=>pool (RayQuotient.identityClass M H) S c d (Z^(ell j))
      (∀j,0<slotMass T (residueWeights W (fun j=>Z^(ell j))) j) ∧
      |(Probe.principalScalar Finset.univ Z (∑j,ell j)
        (slotMass T (residueWeights W (fun j=>Z^(ell j)))))⁻¹|≤Z^eps := by
  have hm : ∀ᶠZ : ℝ in atTop,∀j,0<slotMass
      (fun j=>pool (RayQuotient.identityClass M H) S c d (Z^(ell j)))
      (residueWeights W (fun j=>Z^(ell j))) j := by
    apply Filter.eventually_all.mpr
    intro j
    exact (tendsto_rpow_atTop (hell j)).eventually
      (ray_pool_mass_eventually_positive M H hH S (W j) c d hc hd (hsupp j)
        (hW j) (hcompact j) (hp j) (hW0 j) (hne j))
  have hi := ProbeRayNormalization.ray_principalScalar_inverse_subpower M H hH Finset.univ S W
    (fun _=>c) (fun _=>d) ell (fun _ _=>hc) (fun _ _=>hd) (fun j _=>hsupp j)
    (fun j _=>hW j) (fun j _=>hcompact j) (fun j _=>hp j) (fun j _=>hW0 j) (fun j _=>hne j)
    (fun j _=>hell j) eps heps
  filter_upwards [hm,hi] with Z hmass hinv
  exact ⟨hmass,hinv⟩
end SevenEighths.ProbeRaySlots
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.PrincipalNormalized
namespace OAI

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Complex Filter
namespace SevenEighths.ProbePrincipalNormalized
open HeckeFamily ProbePhysical CompletedGauss ProbeFiniteProductBounds
open PrincipalMellinResidues PrincipalSignalComparison ProbePrincipalResidueActual ProbeRaySlots
local notation "Id" => Ideal HeckeFamily.O

lemma normalized_error (A R F N : ℂ) (c d v : ℝ)
    (hc : 0≤ c) (hA : ‖A-R‖≤ c) (hN : ‖N⁻¹‖≤v)
    (hR : ‖R/N-F‖≤d) : ‖A/N-F‖≤ c*v+d := by
  calc
    _ = ‖(A-R)*N⁻¹+(R/N-F)‖ := by congr 1; simp only [div_eq_mul_inv];ring
    _ ≤ ‖(A-R)*N⁻¹‖+‖R/N-F‖ := norm_add_le _ _
    _ ≤ c*v+d := by rw [norm_mul];gcongr

theorem actual_ray_principal_comparison_oai {K : ℕ}
    (M : Id) [NeZero M] [Finite (HeckeFamily.O ⧸ M)]
    (H : Subgroup (HeckeFamily.O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)
    (η : Character) (S : Finset Id) (hS : SourceExclusions S)
    (c d B ellMin : ℝ) (hc : 0<c) (hd : c≤d) (hB : 0≤B) (hmin : 0<ellMin)
    (ell : Fin K→ℝ) (hell : ∀j,ellMin≤ell j) (hdis : Function.Injective ell)
    (hsum : (∑j,ell j)=1/6)
    (W : Fin K→ℝ→ℝ) (hW : ∀j,ContDiff ℝ ∞ (W j))
    (hcompact : ∀j,HasCompactSupport (W j))
    (hsupp : ∀j,Function.support (W j)⊆Set.Ioo c d)
    (hWbounds : ∀j y,0≤W j y ∧ W j y≤B) (hne : ∀j,W j≠0)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hr0 : ∀y,(W0 y).im=0) (hr1 : ∀y,(W1 y).im=0)
    (hp0 : ∀y,0≤(W0 y).re) (hp1 : ∀y,0≤(W1 y).re) (hn0 : W0≠0) (hn1 : W1≠0)
    (e nu : ℝ) (he : 0<e) (hehi : e≤1/1000) (hnu : 0<nu)
    (ha : 7/8<HeckeZeroSupremum.beta+e) (ha2 : HeckeZeroSupremum.beta+e≤2) :
    letI : NeZero (∏p∈S,p) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    ∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in atTop,
      let T := fun j=>pool (RayQuotient.identityClass M H) S c d (Z^(ell j))
      let normer := sourceResidueConstant W0 W1 (∏p∈S,p)*
        (Probe.principalScalar Finset.univ Z (1/6)
          (slotMass T (residueWeights W (fun j=>Z^(ell j)))) : ℂ)
      normer≠0 ∧
      ‖(∑P:(∀j,T j),(∏j,(W j ((Ideal.absNorm (P j).val.val:ℝ)/Z^(ell j)):ℂ))*
        principalRowIntegral η S (fun j=>primaryGenerator (P j).val.val)
          W0 W1 (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z)/normer-
        HeckeSignal.signal (η.excludePrimes S hS.prime) (sourceCorrection η S) (-11/16) Z‖≤
      C*(Z^(HeckeZeroSupremum.beta-11/16-17/48000+nu)+
        Z^(HeckeZeroSupremum.beta-11/16+e-(7/8)*ellMin)) := by
  let : NeZero (∏p∈S,p) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  obtain ⟨C0,hC0,hrem⟩ := ProbePrincipalPhysical.physical_principal_residue_remainder
    η S hS c d B hc hd hB W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 e he hehi ha ha2 (K:=K)
  obtain ⟨D,hD,hres⟩ := normalized_actual_window_residue S hS η ha ha2 (by linarith) (Finset.univ : Finset (Fin K))
  let cs := sourceResidueConstant W0 W1 (∏p∈S,p)
  let C := C0/e*‖cs⁻¹‖+D*c^(-(7/8:ℝ))+1
  refine ⟨C,by dsimp [C];positivity,?_⟩
  have hpos (j : Fin K) : tsupport (W j)⊆Set.Ioi 0 := by
    apply subset_trans (closure_minimal (Set.Subset.trans (hsupp j) Set.Ioo_subset_Icc_self) isClosed_Icc)
    intro y hy; exact lt_of_lt_of_le hc hy.1
  filter_upwards [power_pool_thresholds (RayQuotient.identityClass M H) S η c d ellMin hc hd hmin ell hell,
    power_ray_mass_and_normalizer M H hH S W c d hc hd hsupp hW hcompact hpos
      (fun j y=>(hWbounds j y).1) hne ell (fun j=>hmin.trans_le (hell j)) nu hnu,
    power_pool_tuples_eventually_injective (RayQuotient.identityClass M H) S
      (fun _=>c) (fun _=>d) ell (fun _=>hc) (fun _=>hd) hdis] with Z hthreshold hmass htuple
  rcases hthreshold with ⟨hZ,h480,hsmall,hslot,hpool⟩
  have hZ0 : 0<Z := by linarith
  let T := fun j=>pool (RayQuotient.identityClass M H) S c d (Z^(ell j))
  let normer := cs*(Probe.principalScalar Finset.univ Z (1/6)
    (slotMass T (residueWeights W (fun j=>Z^(ell j)))) : ℂ)
  have hr := hres W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hr0 hr1 hp0 hp1 hn0 hn1
    T W (fun j=>Z^(ell j)) (c*Z^ellMin) (Z^(23/48:ℝ)) Z h480 hsmall
    (fun j _ p _=>(hWbounds j _).1) (fun j _ p hp=>(hpool j p hp).1)
    (fun j _ p hp=>(hpool j p hp).2.1) (fun j _=>hmass.1 j) hZ
  dsimp only at hr ⊢
  refine ⟨hr.1,?_⟩
  have hraw := hrem ell hsum W hWbounds (fun j=>Set.Subset.trans (hsupp j) Set.Ioo_subset_Icc_self)
    T (fun j p hp=>(hpool j p hp).2.2) htuple Z hZ (fun j=>(hslot j).1) (fun j=>(hslot j).2)
  have hinv : ‖normer⁻¹‖≤‖cs⁻¹‖*Z^nu := by
    dsimp only [normer]
    rw [mul_inv_rev,norm_mul,←Complex.ofReal_inv,norm_real]
    simpa only [hsum,Real.norm_eq_abs,mul_comm] using mul_le_mul_of_nonneg_left hmass.2 (norm_nonneg cs⁻¹)
  have hh := normalized_error _ _ _ normer _ _ _ (by positivity) hraw hinv hr.2.2
  have hpw : (c*Z^ellMin)^(-(7/8:ℝ))=c^(-(7/8:ℝ))*Z^(-(7/8:ℝ)*ellMin) := by
    rw [Real.mul_rpow hc.le (Real.rpow_nonneg hZ0.le _),←Real.rpow_mul hZ0.le]
    congr 2;ring
  have heq1 : (C0/e*Z^(HeckeZeroSupremum.beta-11/16-17/48000))*(‖cs⁻¹‖*Z^nu)=
      (C0/e*‖cs⁻¹‖)*Z^(HeckeZeroSupremum.beta-11/16-17/48000+nu) := by
    rw [Real.rpow_add hZ0];ring
  have heq2 : D*Z^(HeckeZeroSupremum.beta+e-11/16)*(c*Z^ellMin)^(-(7/8:ℝ))=
      (D*c^(-(7/8:ℝ)))*Z^(HeckeZeroSupremum.beta-11/16+e-(7/8)*ellMin) := by
    rw [hpw]
    rw [show HeckeZeroSupremum.beta-11/16+e-(7/8)*ellMin=
      (HeckeZeroSupremum.beta+e-11/16)+(-(7/8:ℝ)*ellMin) by ring,Real.rpow_add hZ0]
    ring
  apply hh.trans
  rw [heq1,heq2]
  have h1 : C0/e*‖cs⁻¹‖≤C := by
    dsimp [C]
    have : 0≤D*c^(-(7/8:ℝ)) := by positivity
    linarith
  have h2 : D*c^(-(7/8:ℝ))≤C := by
    dsimp [C]
    have : 0≤C0/e*‖cs⁻¹‖ := by positivity
    linarith
  calc
    _ ≤ C*Z^(HeckeZeroSupremum.beta-11/16-17/48000+nu)+
        C*Z^(HeckeZeroSupremum.beta-11/16+e-(7/8)*ellMin) := by gcongr
    _ = _ := by ring
end SevenEighths.ProbePrincipalNormalized
end

end OAI
end

theorem solution : type_of% @OAI.SevenEighths.ProbePrincipalNormalized.actual_ray_principal_comparison_oai := @OAI.SevenEighths.ProbePrincipalNormalized.actual_ray_principal_comparison_oai
