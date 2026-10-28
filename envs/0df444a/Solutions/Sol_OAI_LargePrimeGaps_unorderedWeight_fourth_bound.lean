-- Prove2me | solution 1 for OAI.LargePrimeGaps.unorderedWeight_fourth_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T04:59:08.282449+00:00
-- url     : https://prove2.me/submissions/a2548de0-fa2a-4ae5-b1a3-1df6e744afb3

import Mathlib
import Definitions.Def_OAIW2PG000

section
-- module Solutions.OAIW2_P344.Compat
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
theorem dite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : ¬p) :
    dite p a b = b h := dif_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIW2_P344.PrimeGaps_Indices
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

theorem log_pos_of_two_le {X : ℕ} (hX : 2 ≤ X) : 0 < Real.log (X : ℝ) :=
  Real.log_pos (by exact_mod_cast (show 1 < X by omega))

open Filter

theorem blockLength_le_mul_log {lam : ℝ} (hlam : 0 ≤ lam) {X : ℕ} (hX : 2 ≤ X) :
    (blockLength lam X : ℝ) ≤ lam * Real.log (X : ℝ) :=
  Nat.floor_le (mul_nonneg hlam (log_pos_of_two_le hX).le)

end LargePrimeGaps

end OAI
end

section
-- module Solutions.OAIW2_P344.PrimeGaps_DivisorSums
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

open Filter

theorem divisorCoefficient_ne_zero_iff {ι : Type*} [Fintype ι]
    {X : ℕ} {F : (ι → ℝ) → ℝ} {d : ι → ℕ} :
    divisorCoefficient X F d ≠ 0 ↔
      (∀ i, Squarefree (d i)) ∧ F (logCoordinates X d) ≠ 0 := by
  simp only [divisorCoefficient, mul_ne_zero_iff, Finset.prod_ne_zero_iff,
    Finset.mem_univ, forall_true_left, Int.cast_ne_zero,
    ArithmeticFunction.moebius_ne_zero_iff_squarefree]

theorem logCoordinates_nonneg {ι : Type*} {X : ℕ} (hX : 2 ≤ X)
    {d : ι → ℕ} (hd : ∀ i, 0 < d i) (i : ι) : 0 ≤ logCoordinates X d i := by
  exact div_nonneg (Real.log_nonneg (by exact_mod_cast hd i)) (log_pos_of_two_le hX).le

theorem divisor_product_bound {ι : Type*} [Fintype ι]
    {X : ℕ} (hX : 2 ≤ X) {F : (ι → ℝ) → ℝ} {rho : ℝ}
    (hbudget : HasBudget F rho) {d : ι → ℕ} (hd : ∀ i, 0 < d i)
    (hF : F (logCoordinates X d) ≠ 0) :
    ((∏ i, d i : ℕ) : ℝ) ≤ Real.exp (rho * Real.log (X : ℝ)) := by
  have hsum : ∑ i, logCoordinates X d i ≤ rho := by
    by_contra! hgt
    exact hF (hbudget _ (logCoordinates_nonneg hX hd) hgt)
  have hlog : ∑ i, Real.log (d i : ℝ) ≤ rho * Real.log (X : ℝ) := by
    apply (div_le_iff₀ (log_pos_of_two_le hX)).mp
    simpa only [logCoordinates, Finset.sum_div] using hsum
  calc
    ((∏ i, d i : ℕ) : ℝ) = Real.exp (∑ i, Real.log (d i : ℝ)) := by
      rw [Real.exp_sum, Nat.cast_prod]
      apply Finset.prod_congr rfl
      intro i _
      exact (Real.exp_log (by exact_mod_cast hd i)).symm
    _ ≤ Real.exp (rho * Real.log (X : ℝ)) := Real.exp_le_exp.mpr hlog

theorem divisor_coordinate_bound {ι : Type*} [Fintype ι]
    {X : ℕ} (hX : 2 ≤ X) {F : (ι → ℝ) → ℝ} {rho : ℝ}
    (hbudget : HasBudget F rho) {d : ι → ℕ} (hd : ∀ i, 0 < d i)
    (hF : F (logCoordinates X d) ≠ 0) (i : ι) :
    d i ≤ ⌊Real.exp (rho * Real.log (X : ℝ))⌋₊ := by
  have hprod : 0 < ∏ i, d i := Finset.prod_pos fun i _ => hd i
  have hle : d i ≤ ∏ i, d i := Nat.le_of_dvd hprod (Finset.dvd_prod_of_mem _ (Finset.mem_univ i))
  exact (Nat.le_floor_iff (Real.exp_pos _).le).mpr
    ((by exact_mod_cast hle : (d i : ℝ) ≤ ((∏ i, d i : ℕ) : ℝ)).trans
      (divisor_product_bound hX hbudget hd hF))

theorem abs_divisorCoefficient_le {ι : Type*} [Fintype ι]
    (X : ℕ) (F : (ι → ℝ) → ℝ) (d : ι → ℕ) :
    |divisorCoefficient X F d| ≤ |F (logCoordinates X d)| := by
  rw [divisorCoefficient, abs_mul, Finset.abs_prod]
  have hp : (∏ i, |(ArithmeticFunction.moebius (d i) : ℝ)|) ≤ 1 := by
    apply Finset.prod_le_one
    · intro i _
      exact abs_nonneg _
    · intro i _
      exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := d i))
  simpa using mul_le_mul_of_nonneg_right hp (abs_nonneg (F (logCoordinates X d)))

theorem divisorSum_eq_bounded {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X : ℕ} (hX : 2 ≤ X) {F : (ι → ℝ) → ℝ} {rho : ℝ}
    (hbudget : HasBudget F rho) (m : ℕ) (hm : 0 < m) (b : ι → ℕ) :
    divisorSum X F m b =
      ∑ d ∈ (Fintype.piFinset (fun _ : ι =>
        Finset.Icc 1 ⌊Real.exp (rho * Real.log (X : ℝ))⌋₊)).filter
          (fun d => ∀ i, d i ∣ m + b i), divisorCoefficient X F d := by
  classical
  unfold divisorSum
  symm
  apply Finset.sum_subset
  · intro d hd
    have hdbox := Fintype.mem_piFinset.mp (Finset.mem_filter.mp hd).1
    have hddiv := (Finset.mem_filter.mp hd).2
    apply Fintype.mem_piFinset.mpr
    intro i
    exact Nat.mem_divisors.mpr ⟨hddiv i, by omega⟩
  · intro d hd hdnot
    by_contra hne
    have hdpos : ∀ i, 0 < d i := by
      intro i
      have hdmem := Fintype.mem_piFinset.mp hd i
      exact Nat.pos_of_mem_divisors hdmem
    have hF := (divisorCoefficient_ne_zero_iff.mp hne).2
    apply hdnot
    apply Finset.mem_filter.mpr
    refine ⟨Fintype.mem_piFinset.mpr (fun i => ?_), fun i => ?_⟩
    · exact Finset.mem_Icc.mpr ⟨hdpos i, divisor_coordinate_bound hX hbudget hdpos hF i⟩
    · exact (Nat.mem_divisors.mp (Fintype.mem_piFinset.mp hd i)).1

theorem residueStarts_card_error (X : ℕ) {q c : ℕ} (hq : 0 < q) (hc : c < q) :
    |((residueStarts X q c).card : ℝ) - (X : ℝ) / (q : ℝ)| ≤ 2 := by
  have hupper : (residueStarts X q c).card ≤
      (Finset.Icc (X / q) ((2 * X) / q)).card := by
    apply Finset.card_le_card_of_injOn (fun m => m / q)
    · intro m hm
      obtain ⟨hmrange, hmc⟩ := Finset.mem_filter.mp hm
      obtain ⟨hmlo, hmhi⟩ := Finset.mem_Ioc.mp hmrange
      exact Finset.mem_Icc.mpr ⟨Nat.div_le_div_right hmlo.le, Nat.div_le_div_right hmhi⟩
    · intro m hm n hn heq
      have hmc := (Finset.mem_filter.mp hm).2
      have hnc := (Finset.mem_filter.mp hn).2
      have hmdiv := Nat.div_add_mod m q
      have hndiv := Nat.div_add_mod n q
      change m / q = n / q at heq
      rw [heq, hmc] at hmdiv
      rw [hnc] at hndiv
      omega
  have hlower : (Finset.Ioo (X / q) ((2 * X) / q)).card ≤
      (residueStarts X q c).card := by
    apply Finset.card_le_card_of_injOn (fun k => q * k + c)
    · intro k hk
      obtain ⟨hklo, hkhi⟩ := Finset.mem_Ioo.mp hk
      have hrX := Nat.mod_lt X hq
      have hr2X := Nat.mod_lt (2 * X) hq
      have hXdiv := Nat.div_add_mod X q
      have h2Xdiv := Nat.div_add_mod (2 * X) q
      change q * k + c ∈ residueStarts X q c
      simp only [residueStarts, Finset.mem_filter, Finset.mem_Ioc]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · have hh := Nat.mul_le_mul_left q (show X / q + 1 ≤ k by omega)
        simp only [Nat.mul_add, Nat.mul_one] at hh
        omega
      · have hh := Nat.mul_le_mul_left q (show k + 1 ≤ (2 * X) / q by omega)
        simp only [Nat.mul_add, Nat.mul_one] at hh
        omega
      · simp [Nat.add_mod, Nat.mod_eq_of_lt hc]
    · intro k _ l _ heq
      exact Nat.eq_of_mul_eq_mul_left hq (Nat.add_right_cancel heq)
  rw [Nat.card_Icc] at hupper
  rw [Nat.card_Ioo] at hlower
  have hord : X / q ≤ (2 * X) / q := Nat.div_le_div_right (by omega)
  have hu : (residueStarts X q c).card + X / q ≤ (2 * X) / q + 1 := by omega
  have hl : (2 * X) / q ≤ (residueStarts X q c).card + X / q + 1 := by omega
  have hrX := Nat.mod_lt X hq
  have hr2X := Nat.mod_lt (2 * X) hq
  have hXdiv := Nat.div_add_mod X q
  have h2Xdiv := Nat.div_add_mod (2 * X) q
  have hupperN : (residueStarts X q c).card * q ≤ X + 2 * q := by
    have hh := Nat.mul_le_mul_left q hu
    rw [Nat.mul_comm]
    simp only [Nat.mul_add, Nat.mul_one] at hh
    omega
  have hlowerN : X ≤ (residueStarts X q c).card * q + 2 * q := by
    have hh := Nat.mul_le_mul_left q hl
    rw [Nat.mul_comm]
    simp only [Nat.mul_add, Nat.mul_one] at hh
    omega
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hupperR : ((residueStarts X q c).card : ℝ) * q ≤ (X : ℝ) + 2 * q := by
    exact_mod_cast hupperN
  have hlowerR : (X : ℝ) ≤ ((residueStarts X q c).card : ℝ) * q + 2 * q := by
    exact_mod_cast hlowerN
  have hu' : ((residueStarts X q c).card : ℝ) ≤ (X : ℝ) / q + 2 := by
    have hh := (le_div_iff₀ hqR).mpr hupperR
    simpa [add_div, hqR.ne'] using hh
  have hl' : (X : ℝ) / q ≤ ((residueStarts X q c).card : ℝ) + 2 := by
    apply (div_le_iff₀ hqR).mpr
    nlinarith
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem tupleModulus_pos {ι : Type*} [Fintype ι] {d : ι → ℕ}
    (hd : ∀ i, 0 < d i) : 0 < tupleModulus d := by
  apply Nat.pos_of_ne_zero
  exact Finset.lcm_ne_zero_iff.mpr fun i _ => (hd i).ne'

theorem tupleModulus_dvd_prod {ι : Type*} [Fintype ι] (d : ι → ℕ) :
    tupleModulus d ∣ ∏ i, d i :=
  Finset.lcm_dvd fun _ hi => Finset.dvd_prod_of_mem d hi

theorem modEq_lcm_iff {ι : Type*} (s : Finset ι) (d : ι → ℕ) (m c : ℕ) :
    Nat.ModEq (s.lcm d) m c ↔ ∀ i ∈ s, Nat.ModEq (d i) m c := by
  classical
  constructor
  · intro h i hi
    exact h.of_dvd (Finset.dvd_lcm hi)
  · induction s using Finset.induction_on with
    | empty => intro _; exact Nat.modEq_one
    | @insert a s ha ih =>
      intro h
      rw [Finset.lcm_insert]
      exact Nat.mod_lcm (h a (Finset.mem_insert_self a s))
        (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem tuple_divisibility_iff_modEq {ι : Type*} [Fintype ι]
    (d b : ι → ℕ) {c : ℕ} (hc : ∀ i, d i ∣ c + b i) (m : ℕ) :
    (∀ i, d i ∣ m + b i) ↔ Nat.ModEq (tupleModulus d) m c := by
  rw [tupleModulus, modEq_lcm_iff]
  simp only [Finset.mem_univ, forall_true_left]
  constructor
  · intro hm i
    apply Nat.ModEq.add_right_cancel (Nat.ModEq.refl (b i))
    exact (Nat.modEq_zero_iff_dvd.mpr (hm i)).trans (Nat.modEq_zero_iff_dvd.mpr (hc i)).symm
  · intro hm i
    exact ((hm i |>.add_right (b i)).dvd_iff (dvd_refl (d i))).mpr (hc i)

theorem compatible_of_solution {ι : Type*} [Fintype ι] {d b : ι → ℕ}
    (hd : ∀ i, 0 < d i) {m : ℕ} (hm : ∀ i, d i ∣ m + b i) : tupleCompatible d b := by
  refine ⟨m % tupleModulus d, Nat.mod_lt _ (tupleModulus_pos hd), ?_⟩
  apply (tuple_divisibility_iff_modEq d b hm _).mpr
  simp [Nat.ModEq]

theorem localCompatible_of_tupleCompatible {ι : Type*} [Fintype ι]
    {d b : ι → ℕ} (h : tupleCompatible d b) : localCompatible d b := by
  obtain ⟨c, _, hc⟩ := h
  intro p _ _ i j hpi hpj
  apply Nat.ModEq.add_left_cancel (Nat.ModEq.refl c)
  exact (Nat.modEq_zero_iff_dvd.mpr (hpi.trans (hc i))).trans
    (Nat.modEq_zero_iff_dvd.mpr (hpj.trans (hc j))).symm

theorem squarefree_dvd_of_prime_dvd {n k : ℕ} (hn : Squarefree n)
    (h : ∀ p, Nat.Prime p → p ∣ n → p ∣ k) : n ∣ k := by
  by_cases hk : k = 0
  · simp [hk]
  rw [← Nat.prod_primeFactors_of_squarefree hn, Nat.prod_primeFactors_dvd_iff hk]
  intro p hp
  obtain ⟨hpp, hpn, _⟩ := Nat.mem_primeFactors.mp hp
  exact Nat.mem_primeFactors.mpr ⟨hpp, h p hpp hpn, hk⟩

theorem tupleCompatible_of_localCompatible {ι : Type*} [Fintype ι]
    {d b : ι → ℕ} (hd : ∀ i, Squarefree (d i)) (h : localCompatible d b) :
    tupleCompatible d b := by
  classical
  have hdpos : ∀ i, 0 < d i := fun i => Nat.pos_of_ne_zero (hd i).ne_zero
  let P := {p : ℕ // p ∈ (tupleModulus d).primeFactors}
  have hp : ∀ p : P, Nat.Prime p.val := fun p => Nat.prime_of_mem_primeFactors p.property
  have hit : ∀ p : P, ∃ i, p.val ∣ d i := by
    intro p
    have hpq := (Nat.mem_primeFactors.mp p.property).2.1
    obtain ⟨i, _, hi⟩ := ((hp p).prime.dvd_finsetProd_iff d).mp
      (hpq.trans (tupleModulus_dvd_prod d))
    exact ⟨i, hi⟩
  choose idx hidx using hit
  let a : P → ℕ := fun p => (p.val - b (idx p) % p.val) % p.val
  obtain ⟨c, hc⟩ := Nat.chineseRemainderOfFinset a (fun p : P => p.val) Finset.univ
    (fun p _ => (hp p).ne_zero) (by
      intro p _ q _ hpq
      exact (Nat.coprime_primes (hp p) (hp q)).mpr fun heq => hpq (Subtype.ext heq))
  apply compatible_of_solution hdpos (m := c)
  intro i
  apply squarefree_dvd_of_prime_dvd (hd i)
  intro p hpp hpi
  have hpq : p ∣ tupleModulus d := hpi.trans (Finset.dvd_lcm (Finset.mem_univ i))
  let p' : P := ⟨p, Nat.mem_primeFactors.mpr ⟨hpp, hpq, (tupleModulus_pos hdpos).ne'⟩⟩
  have hshift : Nat.ModEq p (b (idx p')) (b i) := h p hpp hpq (idx p') i (hidx p') hpi
  have hres : Nat.ModEq p c (a p') := hc p' (Finset.mem_univ _)
  have hb : b (idx p') % p < p := Nat.mod_lt _ hpp.pos
  have hzero : Nat.ModEq p (a p' + b (idx p')) 0 := by
    change (((p - b (idx p') % p) % p + b (idx p')) % p) = 0 % p
    rw [Nat.zero_mod, Nat.add_mod, Nat.mod_mod]
    calc
      ((p - b (idx p') % p) % p + b (idx p') % p) % p =
          ((p - b (idx p') % p) + b (idx p') % p) % p := by
            rw [Nat.add_mod (p - b (idx p') % p) (b (idx p') % p) p,
              Nat.mod_eq_of_lt hb]
      _ = 0 := by rw [Nat.sub_add_cancel hb.le, Nat.mod_self]
  exact Nat.modEq_zero_iff_dvd.mp ((hres.add hshift.symm).trans hzero)

theorem tupleCompatible_iff_localCompatible {ι : Type*} [Fintype ι]
    {d b : ι → ℕ} (hd : ∀ i, Squarefree (d i)) :
    tupleCompatible d b ↔ localCompatible d b :=
  ⟨localCompatible_of_tupleCompatible, tupleCompatible_of_localCompatible hd⟩

theorem tupleStarts_eq_residueStarts {ι : Type*} [Fintype ι] (X : ℕ)
    (d b : ι → ℕ) {c : ℕ} (hc : c < tupleModulus d) (hsol : ∀ i, d i ∣ c + b i) :
    tupleStarts X d b = residueStarts X (tupleModulus d) c := by
  classical
  ext m
  simp only [tupleStarts, residueStarts, Finset.mem_filter]
  rw [tuple_divisibility_iff_modEq d b hsol, Nat.ModEq, Nat.mod_eq_of_lt hc]

theorem tupleStarts_eq_empty_of_incompatible {ι : Type*} [Fintype ι] (X : ℕ)
    {d b : ι → ℕ} (hd : ∀ i, 0 < d i) (h : ¬ tupleCompatible d b) :
    tupleStarts X d b = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro m hm
  exact h (compatible_of_solution hd (Finset.mem_filter.mp hm).2)

theorem tupleStarts_card_error {ι : Type*} [Fintype ι] (X : ℕ)
    {d b : ι → ℕ} (hd : ∀ i, 0 < d i) (h : tupleCompatible d b) :
    |((tupleStarts X d b).card : ℝ) - (X : ℝ) / (tupleModulus d : ℝ)| ≤ 2 := by
  obtain ⟨c, hc, hsol⟩ := h
  rw [tupleStarts_eq_residueStarts X d b hc hsol]
  exact residueStarts_card_error X (tupleModulus_pos hd) hc

theorem tupleModulus_squarefree {ι : Type*} [Fintype ι] {d : ι → ℕ}
    (hd : ∀ i, Squarefree (d i)) : Squarefree (tupleModulus d) := by
  have hq : 0 < tupleModulus d := tupleModulus_pos fun i => Nat.pos_of_ne_zero (hd i).ne_zero
  apply Squarefree.squarefree_of_dvd (y := primorial (tupleModulus d))
  · apply Finset.lcm_dvd
    intro i _
    apply squarefree_dvd_of_prime_dvd (hd i)
    intro p hp hpi
    apply hp.dvd_primorial_iff.mpr
    exact Nat.le_of_dvd hq (hpi.trans (Finset.dvd_lcm (Finset.mem_univ i)))
  · exact squarefree_primorial _

theorem tupleStarts_density_error {ι : Type*} [Fintype ι] (X : ℕ)
    {d b : ι → ℕ} (hd : ∀ i, 0 < d i) :
    |((tupleStarts X d b).card : ℝ) - (X : ℝ) * tupleDensity d b| ≤ 2 := by
  classical
  by_cases h : tupleCompatible d b
  · simpa [tupleDensity, h, div_eq_mul_inv] using tupleStarts_card_error X hd h
  · simp [tupleDensity, h, tupleStarts_eq_empty_of_incompatible X hd h]

theorem sum_divisibility_eq_counts {ι : Type*} [Fintype ι]
    (X : ℕ) (s : Finset (ι → ℕ)) (A : (ι → ℕ) → ℝ) (b : ι → ℕ) :
    (∑ m ∈ Finset.Ioc X (2 * X), ∑ d ∈ s, if ∀ i, d i ∣ m + b i then A d else 0) =
      ∑ d ∈ s, A d * ((tupleStarts X d b).card : ℝ) := by
  classical
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  rw [← Finset.sum_filter]
  simp only [tupleStarts, Finset.sum_const, nsmul_eq_mul, mul_comm]

theorem finite_density_sum_error {ι : Type*} [Fintype ι]
    {X : ℕ} (hX : 0 < X) (s : Finset (ι → ℕ)) (A : (ι → ℕ) → ℝ)
    (b : ι → ℕ) (hs : ∀ d ∈ s, ∀ i, 0 < d i) :
    |average X (fun m => ∑ d ∈ s, if ∀ i, d i ∣ m + b i then A d else 0) -
        ∑ d ∈ s, A d * tupleDensity d b| ≤
      2 / (X : ℝ) * ∑ d ∈ s, |A d| := by
  classical
  have hXR : (0 : ℝ) < X := by exact_mod_cast hX
  have hexp : average X (fun m => ∑ d ∈ s, if ∀ i, d i ∣ m + b i then A d else 0) -
      ∑ d ∈ s, A d * tupleDensity d b =
      (X : ℝ)⁻¹ * ∑ d ∈ s, A d * (((tupleStarts X d b).card : ℝ) -
        (X : ℝ) * tupleDensity d b) := by
    unfold average
    rw [sum_divisibility_eq_counts]
    simp only [Finset.sum_div, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro d _
    field_simp [hXR.ne']
  rw [hexp, abs_mul, abs_of_pos (inv_pos.mpr hXR)]
  have he : |∑ d ∈ s, A d * (((tupleStarts X d b).card : ℝ) -
        (X : ℝ) * tupleDensity d b)| ≤ 2 * ∑ d ∈ s, |A d| := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro d hd
    rw [abs_mul, mul_comm (2 : ℝ)]
    exact mul_le_mul_of_nonneg_left (tupleStarts_density_error X (hs d hd)) (abs_nonneg _)
  calc
    _ ≤ (X : ℝ)⁻¹ * (2 * ∑ d ∈ s, |A d|) := mul_le_mul_of_nonneg_left he (inv_nonneg.mpr hXR.le)
    _ = _ := by ring

theorem positiveProductTuples_card_bound (n Y : ℕ) :
    ((positiveProductTuples (n + 1) Y).card : ℝ) ≤
      (Y : ℝ) * (harmonic Y : ℝ) ^ n := by
  classical
  let B := Fintype.piFinset (fun _ : Fin n => Finset.Icc 1 Y)
  let A : (Fin n → ℕ) → Finset (Fin (n + 1) → ℕ) :=
    fun e => (Finset.Icc 1 (Y / ∏ i, e i)).image fun v => Fin.cons v e
  have hsubset : positiveProductTuples (n + 1) Y ⊆ B.biUnion A := by
    intro d hd
    obtain ⟨hbox, hprod⟩ := Finset.mem_filter.mp hd
    have hemem : Fin.tail d ∈ B := Fintype.mem_piFinset.mpr
      fun i => (Fintype.mem_piFinset.mp hbox) i.succ
    have hdpos : ∀ i, 0 < d i := fun i => (Finset.mem_Icc.mp
      (Fintype.mem_piFinset.mp hbox i)).1
    have hepos : 0 < ∏ i : Fin n, Fin.tail d i := Finset.prod_pos fun i _ => hdpos i.succ
    refine Finset.mem_biUnion.mpr ⟨Fin.tail d, hemem, ?_⟩
    apply Finset.mem_image.mpr
    refine ⟨d 0, Finset.mem_Icc.mpr ⟨hdpos 0, ?_⟩, Fin.cons_self_tail d⟩
    apply (Nat.le_div_iff_mul_le hepos).mpr
    simpa only [Fin.prod_univ_succ, Fin.tail] using hprod
  have hcard : (positiveProductTuples (n + 1) Y).card ≤
      ∑ e ∈ B, Y / ∏ i, e i := by
    calc
      _ ≤ (B.biUnion A).card := Finset.card_le_card hsubset
      _ ≤ ∑ e ∈ B, (A e).card := Finset.card_biUnion_le
      _ ≤ ∑ e ∈ B, (Finset.Icc 1 (Y / ∏ i, e i)).card :=
        Finset.sum_le_sum fun _ _ => Finset.card_image_le
      _ = _ := by simp only [Nat.card_Icc, Nat.add_sub_cancel]
  calc
    ((positiveProductTuples (n + 1) Y).card : ℝ) ≤
        ∑ e ∈ B, ((Y / ∏ i, e i : ℕ) : ℝ) := by exact_mod_cast hcard
    _ ≤ ∑ e ∈ B, (Y : ℝ) / ((∏ i, e i : ℕ) : ℝ) :=
      Finset.sum_le_sum fun _ _ => Nat.cast_div_le
    _ = (Y : ℝ) * ∑ e ∈ B, ∏ i, (e i : ℝ)⁻¹ := by
      simp only [div_eq_mul_inv, Nat.cast_prod, Finset.prod_inv_distrib, Finset.mul_sum]
    _ = (Y : ℝ) * (harmonic Y : ℝ) ^ n := by
      congr 1
      dsimp only [B]
      rw [Finset.sum_prod_piFinset _ (fun (_ : Fin n) (a : ℕ) => (a : ℝ)⁻¹)]
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      congr 1
      simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]

theorem positiveProductTuples_card_log_bound (n Y : ℕ) :
    ((positiveProductTuples (n + 1) Y).card : ℝ) ≤
      (Y : ℝ) * (1 + Real.log (Y : ℝ)) ^ n := by
  apply (positiveProductTuples_card_bound n Y).trans
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg Y)
  apply pow_le_pow_left₀ (by
    simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    exact Finset.sum_nonneg fun _ _ => inv_nonneg.mpr (Nat.cast_nonneg _))
  exact harmonic_le_one_add_log Y

end LargePrimeGaps

end OAI
end

section
-- module Solutions.OAIW2_P344.PrimeGaps_DivisorBounds
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

open Filter

theorem divisorSum_eq_product_bounded {n X : ℕ} (hX : 2 ≤ X)
    {F : (Fin n → ℝ) → ℝ} {rho : ℝ} (hbudget : HasBudget F rho)
    (m : ℕ) (hm : 0 < m) (b : Fin n → ℕ) :
    divisorSum X F m b =
      ∑ d ∈ positiveProductTuples n ⌊Real.exp (rho * Real.log (X : ℝ))⌋₊,
        if ∀ i, d i ∣ m + b i then divisorCoefficient X F d else 0 := by
  classical
  rw [divisorSum_eq_bounded hX hbudget m hm b, ← Finset.sum_filter]
  symm
  apply Finset.sum_subset
  · intro d hd
    simp only [Finset.mem_filter] at hd ⊢
    exact ⟨(Finset.mem_filter.mp hd.1).1, hd.2⟩
  · intro d hd hdnot
    by_contra hne
    simp only [Finset.mem_filter] at hd
    obtain ⟨hbox, hdiv⟩ := hd
    have hdpos : ∀ i, 0 < d i := fun i =>
      (Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hbox i)).1
    have hF := (divisorCoefficient_ne_zero_iff.mp hne).2
    have hp : ∏ i, d i ≤ ⌊Real.exp (rho * Real.log (X : ℝ))⌋₊ :=
      (Nat.le_floor_iff (Real.exp_pos _).le).mpr (divisor_product_bound hX hbudget hdpos hF)
    exact hdnot (Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hbox, hp⟩, hdiv⟩)

theorem unmarked_arithmetic_error {n X : ℕ} (hX : 2 ≤ X)
    {F : (Fin (n + 1) → ℝ) → ℝ} {rho M : ℝ} (hbudget : HasBudget F rho)
    (hM : 0 ≤ M) (hbound : ∀ v, (∀ i, 0 ≤ v i) → |F v| ≤ M)
    (b : Fin (n + 1) → ℕ) :
    |average X (fun m => divisorSum X F m b) - unmarkedDensitySum X F rho b| ≤
      2 * M / (X : ℝ) * ⌊Real.exp (rho * Real.log (X : ℝ))⌋₊ *
       (1 + Real.log (⌊Real.exp (rho * Real.log (X : ℝ))⌋₊ : ℝ)) ^ n := by
  classical
  let Y : ℕ := ⌊Real.exp (rho * Real.log (X : ℝ))⌋₊
  let s := positiveProductTuples (n + 1) Y
  have hs : ∀ d ∈ s, ∀ i, 0 < d i := by
    intro d hd i
    exact (Finset.mem_Icc.mp (Fintype.mem_piFinset.mp (Finset.mem_filter.mp hd).1 i)).1
  have heq : average X (fun m => divisorSum X F m b) =
      average X (fun m => ∑ d ∈ s, if ∀ i, d i ∣ m + b i then divisorCoefficient X F d else 0) := by
    unfold average
    congr 1
    apply Finset.sum_congr rfl
    intro m hm
    exact divisorSum_eq_product_bounded hX hbudget m
      (lt_trans (by omega : 0 < X) (Finset.mem_Ioc.mp hm).1) b
  rw [heq]
  have he := finite_density_sum_error (by omega : 0 < X) s (divisorCoefficient X F) b hs
  have he' : |average X (fun m => ∑ d ∈ s, if ∀ i, d i ∣ m + b i then divisorCoefficient X F d else 0) -
      unmarkedDensitySum X F rho b| ≤ 2 / (X : ℝ) * ∑ d ∈ s, |divisorCoefficient X F d| := by
    convert he using 1
    congr 2
    unfold average
    congr 1
    apply Finset.sum_congr rfl
    intro m _
    apply Finset.sum_congr rfl
    intro d _
    split_ifs <;> rfl
  apply he'.trans
  have habs : ∑ d ∈ s, |divisorCoefficient X F d| ≤ (s.card : ℝ) * M := by
    calc
      _ ≤ ∑ _d ∈ s, M := Finset.sum_le_sum fun d hd =>
        (abs_divisorCoefficient_le X F d).trans (hbound _ (logCoordinates_nonneg hX (hs d hd)))
      _ = _ := by simp
  have hcard := positiveProductTuples_card_log_bound n Y
  have hXR : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  calc
    2 / (X : ℝ) * ∑ d ∈ s, |divisorCoefficient X F d| ≤
        2 / (X : ℝ) * ((s.card : ℝ) * M) :=
      mul_le_mul_of_nonneg_left habs (by positivity)
    _ ≤ 2 / (X : ℝ) * (((Y : ℝ) * (1 + Real.log (Y : ℝ)) ^ n) * M) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcard hM) (by positivity)
    _ = _ := by ring

theorem unmarked_arithmetic_error_exponential {n X : ℕ} (hX : 2 ≤ X)
    (hlog : 1 ≤ Real.log (X : ℝ)) {F : (Fin (n + 1) → ℝ) → ℝ} {rho M : ℝ}
    (hrho : 0 ≤ rho) (hbudget : HasBudget F rho) (hM : 0 ≤ M)
    (hbound : ∀ v, (∀ i, 0 ≤ v i) → |F v| ≤ M) (b : Fin (n + 1) → ℕ) :
    |average X (fun m => divisorSum X F m b) - unmarkedDensitySum X F rho b| ≤
      (2 * M * (1 + rho) ^ n) * (Real.log (X : ℝ)) ^ n *
        Real.exp (-(1 - rho) * Real.log (X : ℝ)) := by
  let L := Real.log (X : ℝ)
  let Y : ℕ := ⌊Real.exp (rho * L)⌋₊
  have hL : 0 ≤ L := le_trans (by norm_num) hlog
  have hY : 1 ≤ Y := (Nat.le_floor_iff (Real.exp_pos _).le).mpr
    (by simpa using Real.one_le_exp_iff.mpr (mul_nonneg hrho hL))
  have hYR : (0 : ℝ) < Y := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hY)
  have hfloor : (Y : ℝ) ≤ Real.exp (rho * L) := Nat.floor_le (Real.exp_pos _).le
  have hlogY : Real.log (Y : ℝ) ≤ rho * L := by
    simpa only [Real.log_exp] using Real.log_le_log hYR hfloor
  have hlogY0 : 0 ≤ Real.log (Y : ℝ) := Real.log_nonneg (by exact_mod_cast hY)
  have hlogbound : 1 + Real.log (Y : ℝ) ≤ (1 + rho) * L := by nlinarith
  have hXR : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  apply (unmarked_arithmetic_error hX hbudget hM hbound b).trans
  calc
    2 * M / (X : ℝ) * (Y : ℝ) * (1 + Real.log (Y : ℝ)) ^ n ≤
        2 * M / (X : ℝ) * Real.exp (rho * L) * ((1 + rho) * L) ^ n := by
      gcongr
    _ = (2 * M * (1 + rho) ^ n) * L ^ n * Real.exp (-(1 - rho) * L) := by
      rw [show -(1 - rho) * L = rho * L - L by ring, Real.exp_sub, Real.exp_log hXR]
      rw [mul_pow]
      ring

end LargePrimeGaps

end OAI
end

section
-- module Solutions.OAIW2_P344.PrimeGaps_SingularSeries
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

theorem residueCount_le_card (H : Finset ℤ) (p : ℕ) : residueCount H p ≤ H.card :=
  Finset.card_image_le

theorem bernoulli_second_order (s : ℕ) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    0 ≤ (1-u)^s - (1-(s:ℝ)*u) ∧
    (1-u)^s - (1-(s:ℝ)*u) ≤ (s:ℝ)^2*u^2 := by
  induction s with
  | zero => simp
  | succ s ih =>
    have hid : (1-u)^(s+1) - (1-((s+1:ℕ):ℝ)*u) =
        (1-u)*((1-u)^s-(1-(s:ℝ)*u))+(s:ℝ)*u^2 := by
      rw [pow_succ, Nat.cast_add, Nat.cast_one]
      ring
    rw [hid]
    constructor
    · exact add_nonneg (mul_nonneg (by linarith) ih.1) (by positivity)
    · have hh := mul_le_mul_of_nonneg_left ih.2 (by linarith : 0≤1-u)
      have hpos : 0 ≤ (s:ℝ)^2*u^2 := by positivity
      have hsm : (1-u)*((s:ℝ)^2*u^2) ≤ (s:ℝ)^2*u^2 := by nlinarith
      push_cast
      nlinarith [sq_nonneg u, Nat.cast_nonneg (α:=ℝ) s]

theorem generic_local_error (s : ℕ) {p : ℕ} (hp : 2 ≤ p) :
    |(1-(s:ℝ)/(p:ℝ))/(1-1/(p:ℝ))^s - 1| ≤
      ((s:ℝ)^2 * (2:ℝ)^s) / (p:ℝ)^2 := by
  have hpR : (2:ℝ)≤p := by exact_mod_cast hp
  have hp0 : (0:ℝ)<p := by linarith
  have hu0 : 0 ≤ (1:ℝ)/p := by positivity
  have hu1 : (1:ℝ)/p ≤ 1/2 := (one_div_le_one_div_of_le (by norm_num) hpR)
  have hs := bernoulli_second_order s hu0 (by linarith)
  have hm : (s:ℝ)*(1/(p:ℝ))=(s:ℝ)/(p:ℝ) := by ring
  rw [hm] at hs
  have hd0 : 0 < (1-(1:ℝ)/p)^s := pow_pos (by linarith) _
  have hdp : (1/2:ℝ)^s ≤ (1-1/(p:ℝ))^s :=
    pow_le_pow_left₀ (by norm_num) (by linarith) s
  have hnum : (1-(s:ℝ)/(p:ℝ))/(1-1/(p:ℝ))^s ≤ 1 := by
    apply (div_le_one hd0).mpr
    nlinarith [hs.1]
  rw [abs_of_nonpos (by linarith : (1-(s:ℝ)/(p:ℝ))/(1-1/(p:ℝ))^s-1≤0)]
  calc
    _ = ((1-1/(p:ℝ))^s - (1-(s:ℝ)/(p:ℝ))) / (1-1/(p:ℝ))^s := by simp only [sub_div, div_self hd0.ne']; ring
    _ ≤ ((s:ℝ)^2 * (1/(p:ℝ))^2) / (1-1/(p:ℝ))^s := by
      apply div_le_div_of_nonneg_right _ hd0.le
      exact hs.2
    _ ≤ ((s:ℝ)^2 * (1/(p:ℝ))^2) / (1/2:ℝ)^s :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hdp
    _ = _ := by simp only [div_pow, one_pow]; field_simp

theorem residueCount_eq_card_of_large (H : Finset ℤ) {p : ℕ}
    (hp : 2 * H.sup Int.natAbs < p) : residueCount H p = H.card := by
  apply Finset.card_image_of_injOn
  intro a ha b hb hab
  have hd : (p:ℤ) ∣ a-b := Int.dvd_of_emod_eq_zero
    (Int.emod_eq_emod_iff_emod_sub_eq_zero.mp hab)
  have hdN : p ∣ (a-b).natAbs := by
    simpa only [Int.natAbs_natCast] using Int.natAbs_dvd_natAbs.mpr hd
  have hlt : (a-b).natAbs < p := by
    have h1 := Finset.le_sup (f:=Int.natAbs) ha
    have h2 := Finset.le_sup (f:=Int.natAbs) hb
    have h3 := Int.natAbs_sub_le a b
    omega
  exact sub_eq_zero.mp (Int.natAbs_eq_zero.mp (Nat.eq_zero_of_dvd_of_lt hdN hlt))

theorem singularLocal_generic_error (H : Finset ℤ) {p : ℕ} (hp : 2 ≤ p)
    (hlarge : 2 * H.sup Int.natAbs < p) :
    |singularLocal H p - 1| ≤ ((H.card:ℝ)^2 * (2:ℝ)^H.card) / (p:ℝ)^2 := by
  simpa only [singularLocal, residueCount_eq_card_of_large H hlarge] using
    generic_local_error H.card hp

theorem singularLocal_summable_error (H : Finset ℤ) :
    Summable (fun p : ℕ => if p.Prime then singularLocal H p - 1 else 0) := by
  have hh : Summable (fun p : ℕ => ((H.card:ℝ)^2 * (2:ℝ)^H.card) / (p:ℝ)^2) := by
    simpa only [mul_one_div] using
      ((Real.summable_one_div_nat_pow.mpr (by norm_num : 1<2)).mul_left
        ((H.card:ℝ)^2 * (2:ℝ)^H.card))
  apply hh.of_norm_bounded_eventually_nat
  filter_upwards [eventually_ge_atTop (max 2 (2*H.sup Int.natAbs+1))] with p hp
  split_ifs with hprime
  · rw [Real.norm_eq_abs]
    exact singularLocal_generic_error H (by omega) (by omega)
  · simp only [norm_zero]
    positivity

theorem singularSeries_multipliable (H : Finset ℤ) :
    Multipliable (fun p : Nat.Primes => singularLocal H p) := by
  apply (Nat.Primes.multipliable_iff_multipliable_ite (singularLocal H)).mpr
  have hh := Real.multipliable_one_add_of_summable (singularLocal_summable_error H)
  apply hh.congr
  intro p
  split_ifs <;> ring

theorem differenceProduct_pos (H : Finset ℤ) : 0 < differenceProduct H := by
  classical
  apply Finset.prod_pos
  intro a _
  apply Finset.prod_pos
  intro b hb
  have hba : b ≠ a := (Finset.mem_erase.mp hb).1
  exact Int.natAbs_pos.mpr (sub_ne_zero.mpr hba.symm)

theorem prime_dvd_differenceProduct_of_collision {H : Finset ℤ} {p : ℕ}
    {a b : ℤ} (ha : a ∈ H) (hb : b ∈ H) (hab : a ≠ b)
    (hmod : a % (p:ℤ) = b % (p:ℤ)) : p ∣ differenceProduct H := by
  have hd : (p:ℤ) ∣ a-b := Int.dvd_of_emod_eq_zero
    (Int.emod_eq_emod_iff_emod_sub_eq_zero.mp hmod)
  have hdN : p ∣ (a-b).natAbs := by
    simpa only [Int.natAbs_natCast] using Int.natAbs_dvd_natAbs.mpr hd
  exact hdN.trans ((Finset.dvd_prod_of_mem (fun b => (a-b).natAbs)
    (Finset.mem_erase.mpr ⟨hab.symm, hb⟩)).trans
    (Finset.dvd_prod_of_mem (fun a => ∏ b ∈ H.erase a, (a-b).natAbs) ha))

theorem residueCount_eq_card_of_not_dvd (H : Finset ℤ) {p : ℕ}
    (hp : ¬p ∣ differenceProduct H) : residueCount H p = H.card := by
  apply Finset.card_image_of_injOn
  intro a ha b hb hab
  by_contra hne
  exact hp (prime_dvd_differenceProduct_of_collision ha hb hne hab)

theorem differenceProduct_le (H : Finset ℤ) {M : ℕ}
    (hM : ∀ a ∈ H, ∀ b ∈ H, (a-b).natAbs ≤ M) :
    differenceProduct H ≤ M^(H.card*(H.card-1)) := by
  classical
  calc
    _ ≤ ∏ a ∈ H, M^(H.card-1) := by
      apply Finset.prod_le_prod'
      intro a ha
      calc
        _ ≤ ∏ _b ∈ H.erase a, M := Finset.prod_le_prod' fun b hb =>
          hM a ha b (Finset.mem_erase.mp hb).2
        _ = _ := by simp [Finset.card_erase_of_mem ha]
    _ = _ := by simp [← pow_mul, Nat.mul_comm]

theorem abs_log_le_two_abs_sub_one {x : ℝ} (hx : 1/2 ≤ x) :
    |Real.log x| ≤ 2*|x-1| := by
  have hx0 : 0<x := by linarith
  by_cases hx1 : 1 ≤ x
  · rw [abs_of_nonneg (Real.log_nonneg hx1), abs_of_nonneg (by linarith)]
    linarith [Real.log_le_sub_one_of_pos hx0]
  · have hx1' : x ≤ 1 := le_of_not_ge hx1
    rw [abs_of_nonpos (Real.log_nonpos hx0.le hx1'), abs_of_nonpos (by linarith)]
    have hh := Real.log_le_sub_one_of_pos (inv_pos.mpr hx0)
    rw [Real.log_inv] at hh
    have hi : x⁻¹-1 ≤ 2*(1-x) := by
      have hh : (1:ℝ) / x ≤ 2*(1-x)+1 := (div_le_iff₀ hx0).mpr (by nlinarith)
      simpa only [one_div] using (sub_le_iff_le_add).mpr hh
    linarith

theorem abs_log_one_sub_le {u : ℝ} (hu0 : 0≤u) (hu1 : u≤1/2) :
    |Real.log (1-u)| ≤ 2*u := by
  have hh := abs_log_le_two_abs_sub_one (x:=1-u) (by linarith)
  simpa only [sub_sub_cancel_left, abs_neg, abs_of_nonneg hu0] using hh

theorem singularLocal_ge_half (H : Finset ℤ) {p : ℕ} (hp : 2 ≤ p)
    (hps : 2 * H.card ≤ p) : 1/2 ≤ singularLocal H p := by
  have hp0 : (0:ℝ)<p := by exact_mod_cast (show 0<p by omega)
  have hs : (2:ℝ)*H.card ≤ p := by exact_mod_cast hps
  have hn : (residueCount H p:ℝ) ≤ H.card := by exact_mod_cast residueCount_le_card H p
  have hpR : (2:ℝ)≤p := by exact_mod_cast hp
  have hd0 : 0 ≤ 1-(1:ℝ)/p := by
    have hh := one_div_le_one_div_of_le (by norm_num : (0:ℝ)<2) hpR
    linarith
  have hd1 : 1-(1:ℝ)/p ≤ 1 := sub_le_self _ (by positivity)
  have hpow : (1-(1:ℝ)/p)^H.card ≤ 1 := pow_le_one₀ hd0 hd1
  have hn0 : 1/2 ≤ 1-(residueCount H p:ℝ)/p := by
    have hh : (residueCount H p:ℝ)/p ≤ 1/2 := (div_le_iff₀ hp0).mpr (by linarith)
    linarith
  unfold singularLocal
  have hdpos : 0 < 1-(1:ℝ)/p := by
    have hh := one_div_le_one_div_of_le (by norm_num : (0:ℝ)<2) hpR
    linarith
  exact hn0.trans (le_div_self (by linarith) (pow_pos hdpos _) hpow)

theorem singularLocal_log_generic (H : Finset ℤ) {p : ℕ} (hp : 2 ≤ p)
    (hps : 2*H.card ≤ p) (hdiv : ¬p ∣ differenceProduct H) :
    |Real.log (singularLocal H p)| ≤
      2*((H.card:ℝ)^2*(2:ℝ)^H.card)/(p:ℝ)^2 := by
  have h1 := abs_log_le_two_abs_sub_one (singularLocal_ge_half H hp hps)
  have h2 : |singularLocal H p-1| ≤ ((H.card:ℝ)^2*(2:ℝ)^H.card)/(p:ℝ)^2 := by
    simpa only [singularLocal, residueCount_eq_card_of_not_dvd H hdiv] using
      generic_local_error H.card hp
  calc
    _ ≤ 2*|singularLocal H p-1| := h1
    _ ≤ 2*(((H.card:ℝ)^2*(2:ℝ)^H.card)/(p:ℝ)^2) := by gcongr
    _ = _ := by ring

theorem singularLocal_log_bound (H : Finset ℤ) {p : ℕ} (hp : 2 ≤ p)
    (hps : 2*H.card ≤ p) :
    |Real.log (singularLocal H p)| ≤ 4*(H.card:ℝ)/(p:ℝ) := by
  have hp0 : (0:ℝ)<p := by exact_mod_cast (show 0<p by omega)
  have hpR : (2:ℝ)≤p := by exact_mod_cast hp
  have hs : (2:ℝ)*H.card ≤ p := by exact_mod_cast hps
  have hn : (residueCount H p:ℝ) ≤ H.card := by exact_mod_cast residueCount_le_card H p
  have hn0 : 0 ≤ (residueCount H p:ℝ)/p := by positivity
  have hn1 : (residueCount H p:ℝ)/p ≤ 1/2 := (div_le_iff₀ hp0).mpr (by linarith)
  have hq1 : (1:ℝ)/p ≤ 1/2 := one_div_le_one_div_of_le (by norm_num) hpR
  have hlog1 := abs_log_one_sub_le hn0 hn1
  have hlog2 := abs_log_one_sub_le (by positivity : 0≤(1:ℝ)/p) hq1
  rw [singularLocal, Real.log_div (by linarith : (1-(residueCount H p:ℝ)/p) ≠ 0)
    (pow_ne_zero _ (by linarith : (1-(1:ℝ)/p) ≠ 0)), Real.log_pow]
  calc
    _ ≤ |Real.log (1-(residueCount H p:ℝ)/p)| +
          |(H.card:ℝ)*Real.log (1-(1:ℝ)/p)| := abs_sub _ _
    _ = |Real.log (1-(residueCount H p:ℝ)/p)| +
          (H.card:ℝ)*|Real.log (1-(1:ℝ)/p)| := by rw [abs_mul, abs_of_nonneg (show (0:ℝ) ≤ H.card from Nat.cast_nonneg _)]
    _ ≤ 2*((residueCount H p:ℝ)/p) + (H.card:ℝ)*(2*((1:ℝ)/p)) := by gcongr
    _ ≤ _ := by
      have hh := div_le_div_of_nonneg_right hn hp0.le
      calc
        _ ≤ 2*((H.card:ℝ)/p) + (H.card:ℝ)*(2*((1:ℝ)/p)) := by gcongr
        _ = _ := by ring

theorem sum_reciprocal_sq_le {S : Finset ℕ} {y : ℕ} (hy : 0 < y)
    (hS : ∀ n ∈ S, y < n) : (∑ n ∈ S, (1:ℝ)/(n:ℝ)^2) ≤ 1/(y:ℝ) := by
  classical
  by_cases hempty : S = ∅
  · subst S
    simp
  let N := S.sup id
  have hsub : S ⊆ Finset.Ico y (N+1) := by
    intro n hn
    exact Finset.mem_Ico.mpr ⟨(hS n hn).le, Nat.lt_succ_iff.mpr (Finset.le_sup (f:=id) hn)⟩
  have hN : y ≤ N+1 := by
    obtain ⟨n, hn⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
    exact (Finset.mem_Ico.mp (hsub hn)).1.trans (Finset.mem_Ico.mp (hsub hn)).2.le
  have htel : (∑ n ∈ Finset.Ico y (N+1), ((1:ℝ)/(n:ℝ)-1/((n:ℝ)+1))) =
      1/(y:ℝ)-1/(N+1:ℕ) := by
    rw [Finset.sum_Ico_eq_sub _ hN]
    have hh (k : ℕ) : (∑ n ∈ Finset.range k, ((1:ℝ)/(n:ℝ)-1/((n:ℝ)+1))) =
        (1:ℝ)/(0:ℕ)-1/(k:ℝ) := by
      simpa only [Nat.cast_add, Nat.cast_one] using
        Finset.sum_range_sub' (fun n : ℕ => (1:ℝ)/(n:ℝ)) k
    rw [hh, hh]
    ring
  have hstep (n : ℕ) (hn : y < n) :
      (1:ℝ)/(n:ℝ)^2 ≤ (1:ℝ)/((n:ℝ)-1)-1/(n:ℝ) := by
    have hn1 : (1:ℝ)<n := by exact_mod_cast (show 1<n by omega)
    have hid : (1:ℝ)/((n:ℝ)-1)-1/(n:ℝ) = 1/((n:ℝ)*((n:ℝ)-1)) := by
      field_simp [show (n:ℝ) ≠ 0 by linarith, show (n:ℝ)-1 ≠ 0 by linarith]
      ring
    rw [hid]
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith

  let T := S.image (fun n => n-1)
  have hi : Set.InjOn (fun n : ℕ => n-1) ↑S := by
    intro n hn m hm he
    have := hS n hn
    have := hS m hm
    change n-1=m-1 at he
    omega
  have he : (∑ n ∈ S, ((1:ℝ)/((n:ℝ)-1)-1/(n:ℝ))) =
      ∑ n ∈ T, ((1:ℝ)/(n:ℝ)-1/((n:ℝ)+1)) := by
    rw [Finset.sum_image hi]
    apply Finset.sum_congr rfl
    intro n hn
    rw [Nat.cast_sub (by have := hS n hn; omega), Nat.cast_one]
    congr 2
    ring
  calc
    _ ≤ ∑ n ∈ S, ((1:ℝ)/((n:ℝ)-1)-1/(n:ℝ)) :=
      Finset.sum_le_sum fun n hn => hstep n (hS n hn)
    _ = _ := he
    _ ≤ ∑ n ∈ Finset.Ico y (N+1), ((1:ℝ)/(n:ℝ)-1/((n:ℝ)+1)) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro m hm
        obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hm
        have := hS n hn
        have hsup : n ≤ N := Finset.le_sup (f:=id) hn
        simp only [Finset.mem_Ico]
        change y ≤ n-1 ∧ n-1<N+1
        omega
      · intro n hn _
        have hn0 : (0:ℝ)<n := by exact_mod_cast (hy.trans_le (Finset.mem_Ico.mp hn).1)
        exact sub_nonneg.mpr (one_div_le_one_div_of_le hn0 (by linarith))
    _ = 1/(y:ℝ)-1/(N+1:ℕ) := htel
    _ ≤ _ := sub_le_self _ (by positivity)

theorem prime_divisor_reciprocal_sum_le {D y : ℕ} (hD : 0 < D) (hy : 1 < y)
    (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p ∧ y < p ∧ p ∣ D) :
    (∑ p ∈ S, (1:ℝ)/(p:ℝ)) ≤ Real.log D / ((y:ℝ)*Real.log y) := by
  have hy0 : (0:ℝ)<y := by exact_mod_cast (show 0<y by omega)
  have hy1 : (1:ℝ)<y := by exact_mod_cast hy
  have hlogy : 0 < Real.log (y:ℝ) := Real.log_pos hy1
  have hsub : S ⊆ D.primeFactors := fun p hp =>
    Nat.mem_primeFactors.mpr ⟨(hS p hp).1, (hS p hp).2.2, hD.ne'⟩
  have hprod : (∏ p ∈ S, p) ≤ D := Nat.le_of_dvd hD
    ((Finset.prod_dvd_prod_of_subset S D.primeFactors id hsub).trans (Nat.prod_primeFactors_dvd D))
  have hprodpos : (0:ℝ) < ∏ p ∈ S, (p:ℝ) := Finset.prod_pos fun p hp => by
    exact_mod_cast (hS p hp).1.pos
  have hlogs : (∑ p ∈ S, Real.log (p:ℝ)) ≤ Real.log D := by
    rw [← Real.log_prod (s:=S) (f:=fun p : ℕ => (p:ℝ))
      (fun p hp => (ne_of_gt (by exact_mod_cast (hS p hp).1.pos : (0:ℝ)<p)))]
    exact Real.log_le_log hprodpos (by
      simpa only [Nat.cast_prod] using (show ((∏ p ∈ S, p : ℕ):ℝ) ≤ (D:ℝ) by exact_mod_cast hprod))
  calc
    _ ≤ ∑ p ∈ S, Real.log (p:ℝ) / ((y:ℝ)*Real.log y) := by
      apply Finset.sum_le_sum
      intro p hp
      have hpy : (y:ℝ)≤p := by exact_mod_cast (hS p hp).2.1.le
      have hlogp := Real.log_le_log hy0 hpy
      calc
        _ ≤ 1/(y:ℝ) := one_div_le_one_div_of_le hy0 hpy
        _ = Real.log (y:ℝ)/((y:ℝ)*Real.log y) := by field_simp
        _ ≤ _ := div_le_div_of_nonneg_right hlogp (by positivity)
    _ = (∑ p ∈ S, Real.log (p:ℝ))/((y:ℝ)*Real.log y) := (Finset.sum_div _ _ _).symm
    _ ≤ _ := div_le_div_of_nonneg_right hlogs (by positivity)

theorem singularLocal_log_sum_bound (H : Finset ℤ) {y : ℕ} (hy : 1<y)
    (hys : 2*H.card ≤ y) (S : Finset ℕ)
    (hS : ∀ p ∈ S, Nat.Prime p ∧ y < p) :
    (∑ p ∈ S, |Real.log (singularLocal H p)|) ≤ singularTailBound H y := by
  classical
  let K : ℝ := 2*((H.card:ℝ)^2*(2:ℝ)^H.card)
  have hK : 0≤K := by dsimp [K]; positivity
  have hsum : (∑ p ∈ S, |Real.log (singularLocal H p)|) ≤
      (∑ p ∈ S, K*(1/(p:ℝ)^2)) +
      ∑ p ∈ S.filter (fun p => p ∣ differenceProduct H), 4*(H.card:ℝ)*(1/(p:ℝ)) := by
    rw [Finset.sum_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro p hp
    by_cases hd : p ∣ differenceProduct H
    · simp only [hd, ite_true]
      have hh := singularLocal_log_bound H (hS p hp).1.two_le (hys.trans (hS p hp).2.le)
      calc
        _ ≤ 4*(H.card:ℝ)/(p:ℝ) := hh
        _ ≤ K*(1/(p:ℝ)^2) + 4*(H.card:ℝ)*(1/(p:ℝ)) := by
          have h0 : 0≤K*(1/(p:ℝ)^2) := by positivity
          simpa only [mul_one_div] using
            (le_add_of_nonneg_left h0 : 4*(H.card:ℝ)*(1/(p:ℝ)) ≤
              K*(1/(p:ℝ)^2) + 4*(H.card:ℝ)*(1/(p:ℝ)))
    · simp only [hd, ite_false, add_zero]
      simpa only [K, mul_one_div] using
        singularLocal_log_generic H (hS p hp).1.two_le (hys.trans (hS p hp).2.le) hd
  have hinv := sum_reciprocal_sq_le (show 0<y by omega) (fun p hp => (hS p hp).2)
  have hdiv := prime_divisor_reciprocal_sum_le (differenceProduct_pos H) hy
    (S.filter (fun p => p ∣ differenceProduct H)) (by
      intro p hp
      obtain ⟨hpS, hd⟩ := Finset.mem_filter.mp hp
      exact ⟨(hS p hpS).1, (hS p hpS).2, hd⟩)
  calc
    _ ≤ _ := hsum
    _ = K*(∑ p ∈ S, 1/(p:ℝ)^2) +
        4*(H.card:ℝ)*(∑ p ∈ S.filter (fun p => p ∣ differenceProduct H), 1/(p:ℝ)) := by
      rw [Finset.mul_sum, Finset.mul_sum]
    _ ≤ K*(1/(y:ℝ)) + 4*(H.card:ℝ)*(Real.log (differenceProduct H)/((y:ℝ)*Real.log y)) := by
      exact add_le_add (mul_le_mul_of_nonneg_left hinv hK)
        (mul_le_mul_of_nonneg_left hdiv (by positivity))
    _ = _ := by unfold singularTailBound K; ring

end LargePrimeGaps

end OAI
end

section
-- module Solutions.OAIW2_P344.PrimeGaps_SingularTails
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

theorem singularTailFactor_pos (H : Finset ℤ) {y : ℕ} (hys : 2*H.card ≤ y) (p : ℕ) :
    0 < singularTailFactor H y p := by
  unfold singularTailFactor
  split_ifs with h
  · have hh := singularLocal_ge_half H h.1.two_le (hys.trans h.2.le)
    linarith
  · norm_num

theorem singularTail_log_summable_bound (H : Finset ℤ) {y : ℕ} (hy : 1<y)
    (hys : 2*H.card ≤ y) :
    Summable (fun p : ℕ => Real.log (singularTailFactor H y p)) ∧
    |∑' p : ℕ, Real.log (singularTailFactor H y p)| ≤ singularTailBound H y := by
  have hfin (S : Finset ℕ) :
      (∑ p ∈ S, |Real.log (singularTailFactor H y p)|) ≤ singularTailBound H y := by
    have hh := singularLocal_log_sum_bound H hy hys (S.filter (fun p => p.Prime ∧ y<p))
      (fun p hp => (Finset.mem_filter.mp hp).2)
    simpa only [Finset.sum_filter, singularTailFactor, apply_ite Real.log,
      Real.log_one, apply_ite abs, abs_zero] using hh
  have hs := summable_of_sum_le (fun p => abs_nonneg (Real.log (singularTailFactor H y p))) hfin
  refine ⟨summable_abs_iff.mp hs, ?_⟩
  calc
    _ ≤ ∑' p : ℕ, |Real.log (singularTailFactor H y p)| := by
      simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm (f:=fun p : ℕ => Real.log (singularTailFactor H y p)) (by
        simpa only [Real.norm_eq_abs] using hs)
    _ ≤ _ := hs.tsum_le_of_sum_le hfin

theorem singularTail_pos_and_log_bound (H : Finset ℤ) {y : ℕ} (hy : 1<y)
    (hys : 2*H.card ≤ y) :
    0 < singularTail H y ∧ |Real.log (singularTail H y)| ≤ singularTailBound H y := by
  have hs := singularTail_log_summable_bound H hy hys
  have he : singularTail H y = Real.exp (∑' p : ℕ, Real.log (singularTailFactor H y p)) :=
    (Real.rexp_tsum_eq_tprod (singularTailFactor_pos H hys) hs.1).symm
  rw [he, Real.log_exp]
  exact ⟨Real.exp_pos _, hs.2⟩

theorem singularTail_error (H : Finset ℤ) {y : ℕ} (hy : 1<y)
    (hys : 2*H.card ≤ y) (hsmall : singularTailBound H y ≤ 1) :
    |singularTail H y - 1| ≤ 2*singularTailBound H y := by
  obtain ⟨hpos, hlog⟩ := singularTail_pos_and_log_bound H hy hys
  have he := Real.abs_exp_sub_one_le (hlog.trans hsmall)
  rw [Real.exp_log hpos] at he
  exact he.trans (mul_le_mul_of_nonneg_left hlog (by norm_num))

theorem singularSeries_eq_truncation_mul_tail (H : Finset ℤ) {y : ℕ} (hy : 1<y)
    (hys : 2*H.card ≤ y) :
    singularSeries H = singularTruncation H y * singularTail H y := by
  classical
  let head : ℕ → ℝ := fun p => if p ∈ Nat.primesLE y then singularLocal H p else 1
  have hh : HasProd head (singularTruncation H y) := by
    have hh : HasProd head (∏ p ∈ Nat.primesLE y, head p) :=
      hasProd_prod_of_ne_finset_one (s:=Nat.primesLE y) (f:=head)
      (fun p hp => ite_eq_right hp)
    simpa only [head, singularTruncation, Finset.prod_ite_mem, Finset.inter_self] using hh
  have ht := Real.hasProd_of_hasSum_log (singularTailFactor_pos H hys)
    (singularTail_log_summable_bound H hy hys).1.hasSum
  have hp : (fun p => head p * singularTailFactor H y p) =
      (fun p : ℕ => if p.Prime then singularLocal H p else 1) := by
    funext p
    simp only [head, singularTailFactor, Nat.mem_primesLE]
    split_ifs <;> first | omega | simp_all
  have htt : HasProd (singularTailFactor H y) (singularTail H y) := by
    simpa only [singularTail, ← ht.tprod_eq] using ht
  have hfull := hh.mul htt
  rw [hp] at hfull
  simpa only [singularSeries, Nat.Primes.tprod_eq_tprod_ite] using hfull.tprod_eq

theorem unit_indicator_sum (q : ℕ) [NeZero q] :
    (∑ x : ZMod q, if IsUnit x then (1:ℝ) else 0) = (q.totient:ℝ) := by
  classical
  have he : (Finset.univ.filter fun x : ZMod q => IsUnit x) =
      Finset.univ.image (fun x : (ZMod q)ˣ => (x:ZMod q)) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    change IsUnit x ↔ ∃ u : (ZMod q)ˣ, (u:ZMod q) = x
    constructor
    · rintro ⟨u, hu⟩
      exact ⟨u, hu⟩
    · rintro ⟨u, rfl⟩
      exact u.isUnit
  simp only [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one, he]
  rw [Finset.card_image_of_injective _ Units.val_injective, Finset.card_univ,
    ZMod.card_units_eq_totient]

theorem shifted_unit_indicator_sum {q : ℕ} [NeZero q] (x : ZMod q) :
    (∑ a : ZMod q, if IsUnit (x-a) then (1:ℝ) else 0) = (q.totient:ℝ) := by
  classical
  have hh := (Equiv.subLeft x).sum_comp (fun a : ZMod q => if IsUnit a then (1:ℝ) else 0)
  exact hh.trans (unit_indicator_sum q)

theorem siftedCount_sum (s q : ℕ) [NeZero q] :
    (∑ a : Fin s → ZMod q, siftedCount a) = (q:ℝ)*(q.totient:ℝ)^s := by
  classical
  unfold siftedCount
  rw [Finset.sum_comm]
  have hf (x : ZMod q) :
      (∑ a : Fin s → ZMod q, ∏ i : Fin s, if IsUnit (x-a i) then (1:ℝ) else 0) =
      (q.totient:ℝ)^s := by
    calc
      _ = ∏ _i : Fin s, ∑ b : ZMod q, if IsUnit (x-b) then (1:ℝ) else 0 :=
        (Fintype.prod_sum (fun (_i : Fin s) (b : ZMod q) =>
          if IsUnit (x-b) then (1:ℝ) else 0)).symm
      _ = _ := by simp only [shifted_unit_indicator_sum, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  simp_rw [hf]
  simp

theorem normalizedSiftedCount_sum (s q : ℕ) [NeZero q] :
    (∑ a : Fin s → ZMod q, normalizedSiftedCount a) = (q:ℝ)^s := by
  classical
  have hq : (q:ℝ) ≠ 0 := by exact_mod_cast NeZero.ne q
  have ht : (q.totient:ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos q)).ne'
  unfold normalizedSiftedCount
  rw [← Finset.sum_div, ← Finset.mul_sum, siftedCount_sum]
  rw [div_pow]
  field_simp

theorem siftedCount_crt {s m n : ℕ} [NeZero m] [NeZero n]
    (hcop : m.Coprime n) (a : Fin s → ZMod (m*n)) :
    siftedCount a =
      siftedCount (fun i => (ZMod.chineseRemainder hcop (a i)).1) *
      siftedCount (fun i => (ZMod.chineseRemainder hcop (a i)).2) := by
  classical
  let e := ZMod.chineseRemainder hcop
  have hu (y : ZMod (m*n)) : IsUnit y ↔ IsUnit (e y) := by
    constructor
    · intro hy
      exact hy.map e.toMonoidHom
    · intro hy
      have hh := hy.map e.symm.toMonoidHom
      change IsUnit (e.symm (e y)) at hh
      simpa only [e.symm_apply_apply] using hh
  have hi (x : ZMod (m*n)) (i : Fin s) :
      (if IsUnit (x-a i) then (1:ℝ) else 0) =
      (if IsUnit ((e x).1-(e (a i)).1) then (1:ℝ) else 0) *
      (if IsUnit ((e x).2-(e (a i)).2) then (1:ℝ) else 0) := by
    simp only [hu, e.map_sub, Prod.isUnit_iff, Prod.fst_sub, Prod.snd_sub]
    split_ifs <;> first | omega | simp_all
  unfold siftedCount
  simp_rw [hi, Finset.prod_mul_distrib]
  have he := e.toEquiv.sum_comp (fun x : ZMod m × ZMod n =>
      (∏ i : Fin s, if IsUnit (x.1-(e (a i)).1) then (1:ℝ) else 0) *
      (∏ i : Fin s, if IsUnit (x.2-(e (a i)).2) then (1:ℝ) else 0))
  change _ = _ at he
  calc
    _ = ∑ x : ZMod m × ZMod n,
      (∏ i : Fin s, if IsUnit (x.1-(e (a i)).1) then (1:ℝ) else 0) *
      (∏ i : Fin s, if IsUnit (x.2-(e (a i)).2) then (1:ℝ) else 0) := he
    _ = _ := by
      rw [Fintype.sum_prod_type]
      exact (Fintype.sum_mul_sum
        (fun x : ZMod m => ∏ i : Fin s, if IsUnit (x-(e (a i)).1) then (1:ℝ) else 0)
        (fun x : ZMod n => ∏ i : Fin s, if IsUnit (x-(e (a i)).2) then (1:ℝ) else 0)).symm

theorem normalizedSiftedCount_crt {s m n : ℕ} [NeZero m] [NeZero n]
    (hcop : m.Coprime n) (a : Fin s → ZMod (m*n)) :
    normalizedSiftedCount a =
      normalizedSiftedCount (fun i => (ZMod.chineseRemainder hcop (a i)).1) *
      normalizedSiftedCount (fun i => (ZMod.chineseRemainder hcop (a i)).2) := by
  rw [normalizedSiftedCount, siftedCount_crt hcop, Nat.totient_mul hcop]
  simp only [normalizedSiftedCount, Nat.cast_mul, mul_div_mul_comm, mul_pow]
  ring

theorem product_indicator (s : ℕ) (P : Fin s → Prop) [DecidablePred P] :
    (∏ i : Fin s, if P i then (1:ℝ) else 0) = if ∀ i, P i then 1 else 0 := by
  classical
  by_cases h : ∀ i, P i
  · simp [h]
  · rw [ite_eq_right h]
    obtain ⟨i, hi⟩ := not_forall.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

theorem siftedCount_prime {s p : ℕ} [NeZero p] (hp : Nat.Prime p) (a : Fin s → ZMod p) :
    siftedCount a = (p:ℝ) - (Finset.univ.image a).card := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  have he : (Finset.univ.filter fun x : ZMod p => ∀ i, x ≠ a i) =
      Finset.univ \ Finset.univ.image a := by
    ext x
    simp [eq_comm]
  unfold siftedCount
  simp_rw [isUnit_iff_ne_zero, sub_ne_zero, product_indicator]
  simp only [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one, he]
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Nat.cast_sub]
  · simp [ZMod.card]
  · exact Finset.card_le_card (Finset.subset_univ _)

theorem normalizedSiftedCount_prime {s p : ℕ} [NeZero p] (hp : Nat.Prime p) (a : Fin s → ZMod p) :
    normalizedSiftedCount a =
      (1 - ((Finset.univ.image a).card:ℝ)/(p:ℝ)) / (1-1/(p:ℝ))^s := by
  classical
  have hp0 : (p:ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hp1 : (p:ℝ)-1 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hp.ne_one)
  rw [normalizedSiftedCount, siftedCount_prime hp, Nat.totient_prime hp]
  rw [Nat.cast_sub hp.one_le, Nat.cast_one]
  have hd : (1:ℝ)-1/p = ((p:ℝ)-1)/p := by field_simp
  rw [hd]
  simp only [div_pow]
  field_simp

theorem siftedTuple_eq {s q : ℕ} [NeZero q] (a : Fin s → ℤ) :
    siftedTuple a q = normalizedSiftedCount (fun i => (a i : ZMod q)) := by
  simp only [siftedTuple, dite_eq_right (NeZero.ne q)]

theorem siftedTuple_crt {s m n : ℕ} [NeZero m] [NeZero n]
    (hcop : m.Coprime n) (a : Fin s → ℤ) :
    siftedTuple a (m*n) = siftedTuple a m * siftedTuple a n := by
  simp only [siftedTuple_eq]
  rw [normalizedSiftedCount_crt hcop]
  simp only [map_intCast, Prod.fst_intCast, Prod.snd_intCast]

theorem siftedTuple_one {s : ℕ} (a : Fin s → ℤ) : siftedTuple a 1 = 1 := by
  classical
  have hu (x : ZMod 1) : IsUnit x := by
    convert isUnit_one (M:=ZMod 1) using 1
    exact Subsingleton.elim _ _
  simp only [siftedTuple_eq, normalizedSiftedCount, siftedCount, hu, ite_true]
  simp

theorem siftedTuple_product {s : ℕ} (a : Fin s → ℤ) (P : Finset ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p) :
    siftedTuple a (∏ p ∈ P, p) = ∏ p ∈ P, siftedTuple a p := by
  classical
  induction P using Finset.induction_on with
  | empty => simp [siftedTuple_one]
  | @insert p P hp ih =>
    have hpP := hP p (Finset.mem_insert_self p P)
    have hP' (q) (hq : q ∈ P) := hP q (Finset.mem_insert_of_mem hq)
    let hp0 : NeZero p := ⟨hpP.ne_zero⟩
    let hprod0 : NeZero (∏ q ∈ P, q) := ⟨Finset.prod_ne_zero_iff.mpr
      (fun q hq => (hP' q hq).ne_zero)⟩
    have hc : p.Coprime (∏ q ∈ P, q) := Nat.Coprime.prod_right fun q hq => by
      apply hpP.coprime_iff_not_dvd.mpr
      intro hd
      have he := ((hP' q hq).dvd_iff_eq hpP.ne_one).mp hd
      exact hp (he.symm ▸ hq)
    simp only [Finset.prod_insert hp]
    rw [siftedTuple_crt hc, ih hP']

theorem siftedCount_nonneg {s q : ℕ} [NeZero q] (a : Fin s → ZMod q) :
    0 ≤ siftedCount a := by
  unfold siftedCount
  positivity

theorem siftedCount_le {s q : ℕ} [NeZero q] (a : Fin s → ZMod q) :
    siftedCount a ≤ (q:ℝ) := by
  classical
  calc
    _ ≤ ∑ _x : ZMod q, (1:ℝ) := by
      unfold siftedCount
      apply Finset.sum_le_sum
      intro x _
      exact Finset.prod_le_one (fun _ _ => by positivity) (fun _ _ => by split_ifs <;> norm_num)
    _ = _ := by simp

theorem normalizedSiftedCount_nonneg {s q : ℕ} [NeZero q] (a : Fin s → ZMod q) :
    0 ≤ normalizedSiftedCount a :=
  div_nonneg (mul_nonneg (by positivity) (siftedCount_nonneg a)) (Nat.cast_nonneg _)

theorem normalizedSiftedCount_le {s q : ℕ} [NeZero q] (a : Fin s → ZMod q) :
    normalizedSiftedCount a ≤ (q:ℝ)^s := by
  have hq : (0:ℝ)<q := by exact_mod_cast NeZero.pos q
  have ht : (1:ℝ) ≤ q.totient := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  have hdiv : (q:ℝ)/q.totient ≤ q := (div_le_self hq.le ht)
  unfold normalizedSiftedCount
  calc
    _ ≤ (q:ℝ)^s * q / q := div_le_div_of_nonneg_right
      (mul_le_mul (pow_le_pow_left₀ (by positivity) hdiv s) (siftedCount_le a)
        (siftedCount_nonneg a) (by positivity)) hq.le
    _ = _ := mul_div_cancel_right₀ _ hq.ne'

theorem residueCount_eq_card_zmod (H : Finset ℤ) {q : ℕ} [NeZero q] :
    residueCount H q = (H.image fun a : ℤ => (a : ZMod q)).card := by
  classical
  have he : (H.image fun a => a % (q:ℤ)).image (fun a : ℤ => (a : ZMod q)) =
      H.image (fun a : ℤ => (a : ZMod q)) := by
    rw [Finset.image_image]
    congr 1
    funext a
    exact ZMod.intCast_mod a q
  rw [← he]
  symm
  apply Finset.card_image_of_injOn
  intro a ha b hb heq
  obtain ⟨a', _, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨b', _, rfl⟩ := Finset.mem_image.mp hb
  have hh := (ZMod.intCast_eq_intCast_iff _ _ q).mp heq
  change (a' % (q:ℤ)) % (q:ℤ) = (b' % (q:ℤ)) % (q:ℤ) at hh
  simpa only [Int.emod_emod] using hh

theorem siftedTuple_prime_eq {s p : ℕ} (hp : Nat.Prime p) (a : Fin s → ℤ)
    (ha : Function.Injective a) :
    siftedTuple a p = singularLocal (Finset.univ.image a) p := by
  let : NeZero p := ⟨hp.ne_zero⟩
  rw [siftedTuple_eq, normalizedSiftedCount_prime hp, singularLocal,
    residueCount_eq_card_zmod, Finset.image_image,
    Finset.card_image_of_injective _ ha, Finset.card_univ, Fintype.card_fin]
  rfl

theorem siftedTuple_primorial_eq {s y : ℕ} (a : Fin s → ℤ) (ha : Function.Injective a) :
    siftedTuple a (∏ p ∈ Nat.primesLE y, p) = singularTruncation (Finset.univ.image a) y := by
  rw [siftedTuple_product a _ (fun p hp => (Nat.mem_primesLE.mp hp).2)]
  exact Finset.prod_congr rfl fun p hp => siftedTuple_prime_eq (Nat.mem_primesLE.mp hp).2 a ha

theorem rangeResidue_card_bounds (h : ℕ) {q c : ℕ} (hq : 0<q) (hc : c<q) :
    h/q ≤ (rangeResidue h q c).card ∧ (rangeResidue h q c).card ≤ h/q+1 := by
  have hlo : (Finset.range (h/q)).card ≤ (rangeResidue h q c).card := by
    apply Finset.card_le_card_of_injOn (fun k => q*k+c)
    · intro k hk
      have hh := Nat.mul_le_mul_left q (Nat.succ_le_of_lt (Finset.mem_range.mp hk))
      have hh' : q*k+q ≤ q*(h/q) := by simpa only [Nat.mul_succ] using hh
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by
        change q*k+c<h
        have hd : q*(h/q) ≤ h := by simpa only [Nat.mul_comm] using Nat.div_mul_le_self h q
        omega), ?_⟩
      simp only [Nat.add_mod, Nat.mul_mod_right, zero_add, Nat.mod_eq_of_lt hc]
    · intro k _ l _ heq
      exact Nat.eq_of_mul_eq_mul_left hq (Nat.add_right_cancel heq)
  have hup : (rangeResidue h q c).card ≤ (Finset.range (h/q+1)).card := by
    apply Finset.card_le_card_of_injOn (fun n => n/q)
    · intro n hn
      have hh : n/q ≤ h/q := Nat.div_le_div_right (Finset.mem_range.mp (Finset.mem_filter.mp hn).1).le
      exact Finset.mem_range.mpr (by dsimp only; omega)
    · intro n hn m hm heq
      have hnmod := (Finset.mem_filter.mp hn).2
      have hmmod := (Finset.mem_filter.mp hm).2
      have hnform := Nat.div_add_mod n q
      have hmform := Nat.div_add_mod m q
      change n/q=m/q at heq
      rw [heq, hnmod] at hnform
      rw [hmmod] at hmform
      omega
  simpa only [Finset.card_range] using And.intro hlo hup

theorem cyclicFiber_card_bounds (a : ℤ) (h q : ℕ) [NeZero q] (r : ZMod q) :
    h/q ≤ (cyclicFiber a h q r).card ∧ (cyclicFiber a h q r).card ≤ h/q+1 := by
  classical
  have hpred (n : ℕ) : (a:ZMod q)+(n:ZMod q)=r ↔ n%q=(r-(a:ZMod q)).val := by
    rw [← eq_sub_iff_add_eq']
    constructor
    · intro he
      simpa only [ZMod.val_natCast] using congrArg ZMod.val he
    · intro he
      apply ZMod.val_injective q
      simpa only [ZMod.val_natCast] using he
  have hc : (cyclicFiber a h q r).card = (rangeResidue h q (r-(a:ZMod q)).val).card := by
    apply Finset.card_bij (fun (n : Fin h) _ => (n:ℕ))
    · intro n hn
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr n.isLt, ?_⟩
      exact (hpred n).mp (Finset.mem_filter.mp hn).2
    · intro n _ m _ he
      exact Fin.ext he
    · intro n hn
      obtain ⟨hn, hmod⟩ := Finset.mem_filter.mp hn
      refine ⟨⟨n, Finset.mem_range.mp hn⟩, ?_, rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hpred n).mpr hmod⟩
  rw [hc]
  exact rangeResidue_card_bounds h (NeZero.pos q) (ZMod.val_lt _)

theorem residueTuple_fiber_card {s h q : ℕ} [NeZero q] (a : Fin s → ℤ) (r : Fin s → ZMod q) :
    (Finset.univ.filter fun n : Fin s → Fin h => residueTuple a n = r).card =
      ∏ i : Fin s, (cyclicFiber (a i) h q (r i)).card := by
  classical
  have he : (Finset.univ.filter fun n : Fin s → Fin h => residueTuple a n = r) =
      Fintype.piFinset (fun i => cyclicFiber (a i) h q (r i)) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset,
      cyclicFiber, funext_iff, residueTuple]
  rw [he, Fintype.card_piFinset]

theorem residueTuple_sum_bounds {s h q : ℕ} [NeZero q] (a : Fin s → ℤ)
    (f : (Fin s → ZMod q) → ℝ) (hf : ∀ r, 0≤f r) :
    ((h/q:ℕ):ℝ)^s * (∑ r, f r) ≤ (∑ n : Fin s → Fin h, f (residueTuple a n)) ∧
    (∑ n : Fin s → Fin h, f (residueTuple a n)) ≤ ((h/q+1:ℕ):ℝ)^s * (∑ r, f r) := by
  classical
  have he : (∑ n : Fin s → Fin h, f (residueTuple a n)) =
      ∑ r : Fin s → ZMod q,
        ((Finset.univ.filter fun n : Fin s → Fin h => residueTuple a n = r).card:ℝ) * f r := by
    rw [← Finset.sum_fiberwise Finset.univ (residueTuple (q:=q) a) (fun n => f (residueTuple a n))]
    apply Finset.sum_congr rfl
    intro r _
    calc
      _ = ∑ _n ∈ Finset.univ.filter (fun n : Fin s → Fin h => residueTuple a n = r), f r := by
        apply Finset.sum_congr rfl
        intro n hn
        rw [(Finset.mem_filter.mp hn).2]
      _ = _ := by simp
  rw [he]
  have hcard (r : Fin s → ZMod q) : ((h/q:ℕ):ℝ)^s ≤
      ((Finset.univ.filter fun n : Fin s → Fin h => residueTuple a n = r).card:ℝ) ∧
      ((Finset.univ.filter fun n : Fin s → Fin h => residueTuple a n = r).card:ℝ) ≤
        ((h/q+1:ℕ):ℝ)^s := by
    rw [residueTuple_fiber_card, Nat.cast_prod]
    constructor
    · calc
        _ = ∏ _i : Fin s, ((h/q:ℕ):ℝ) := by simp
        _ ≤ _ := Finset.prod_le_prod (fun _ _ => by positivity) fun i _ => by
          exact_mod_cast (cyclicFiber_card_bounds (a i) h q (r i)).1
    · calc
        _ ≤ ∏ _i : Fin s, ((h/q+1:ℕ):ℝ) :=
          Finset.prod_le_prod (fun _ _ => by positivity) fun i _ => by
            exact_mod_cast (cyclicFiber_card_bounds (a i) h q (r i)).2
        _ = _ := by simp
  simp only [Finset.mul_sum]
  exact ⟨Finset.sum_le_sum fun r _ => mul_le_mul_of_nonneg_right (hcard r).1 (hf r),
    Finset.sum_le_sum fun r _ => mul_le_mul_of_nonneg_right (hcard r).2 (hf r)⟩

theorem boxTuple_collision_count {s h : ℕ} (a : Fin s → ℤ) {i j : Fin s} (hij : i≠j) :
    (Finset.univ.filter fun n : Fin s → Fin h => boxTuple a n i = boxTuple a n j).card ≤
      h^(s-1) := by
  classical
  have hc : Fintype.card {k : Fin s // k ≠ j} = s-1 := by
    rw [Fintype.card_subtype_compl]
    simp
  calc
    _ ≤ (Finset.univ : Finset ({k : Fin s // k ≠ j} → Fin h)).card := by
      apply Finset.card_le_card_of_injOn (fun n k => n k.val)
      · intro n _
        exact Finset.mem_univ _
      · intro n hn m hm he
        have hi := congrFun he ⟨i, hij⟩
        have hn' := (Finset.mem_filter.mp hn).2
        have hm' := (Finset.mem_filter.mp hm).2
        funext k
        by_cases hk : k=j
        · subst k
          unfold boxTuple at hn' hm'
          have hci : (n i:ℕ)=(m i:ℕ) := congrArg Fin.val hi
          apply Fin.ext
          omega
        · exact congrFun he ⟨k, hk⟩
    _ = _ := by simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, hc]

theorem boxTuple_nondistinct_count {s h : ℕ} (a : Fin s → ℤ) :
    (Finset.univ.filter fun n : Fin s → Fin h => ¬ Function.Injective (boxTuple a n)).card ≤
      s^2 * h^(s-1) := by
  classical
  let pairs : Finset (Fin s × Fin s) := Finset.univ.filter fun ij => ij.1 ≠ ij.2
  let bad (ij : Fin s × Fin s) := Finset.univ.filter fun n : Fin s → Fin h =>
    boxTuple a n ij.1 = boxTuple a n ij.2
  have hsub : (Finset.univ.filter fun n : Fin s → Fin h => ¬ Function.Injective (boxTuple a n)) ⊆
      pairs.biUnion bad := by
    intro n hn
    have hni := (Finset.mem_filter.mp hn).2
    simp only [Function.Injective, not_forall] at hni
    obtain ⟨i, j, he, hne⟩ := hni
    exact Finset.mem_biUnion.mpr ⟨(i,j), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩⟩
  calc
    _ ≤ (pairs.biUnion bad).card := Finset.card_le_card hsub
    _ ≤ pairs.card * h^(s-1) := Finset.card_biUnion_le_card_mul pairs bad _ fun ij hij =>
      boxTuple_collision_count a (Finset.mem_filter.mp hij).2
    _ ≤ s^2 * h^(s-1) := Nat.mul_le_mul_right _ (by
      calc
        pairs.card ≤ (Finset.univ : Finset (Fin s × Fin s)).card := Finset.card_filter_le _ _
        _ = _ := by simp [pow_two])

end LargePrimeGaps

end OAI
end

section
-- module Solutions.OAIW2_P344.PrimeGaps_BoxMeans
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

theorem siftedTuple_boxTuple {s h q : ℕ} [NeZero q] (a : Fin s → ℤ) (n : Fin s → Fin h) :
    siftedTuple (boxTuple a n) q = normalizedSiftedCount (residueTuple (q:=q) a n) := by
  rw [siftedTuple_eq]
  congr 1
  funext i
  simp only [boxTuple, residueTuple, Int.cast_add, Int.cast_natCast]

theorem truncatedBoxMean_bounds {s h q : ℕ} [NeZero q] (hh : 0<h) (hq : q≤h)
    (a : Fin s → ℤ) :
    (1-(q:ℝ)/h)^s ≤ truncatedBoxMean (h:=h) a q ∧
    truncatedBoxMean (h:=h) a q ≤ (1+(q:ℝ)/h)^s := by
  have hhR : (0:ℝ)<h := by exact_mod_cast hh
  have hqR : (q:ℝ)≤h := by exact_mod_cast hq
  have hdiv : ((h/q:ℕ):ℝ)*(q:ℝ) ≤ h := by exact_mod_cast Nat.div_mul_le_self h q
  have hfloor : (h:ℝ)-(q:ℝ) ≤ ((h/q:ℕ):ℝ)*(q:ℝ) := by
    have he := Nat.div_add_mod h q
    have hm := Nat.mod_lt h (NeZero.pos q)
    have heR : ((h/q:ℕ):ℝ)*(q:ℝ)+(h%q:ℕ)=h := by
      exact_mod_cast (by simpa only [Nat.mul_comm] using he : h/q*q+h%q=h)
    have hmR : ((h%q:ℕ):ℝ)<q := by exact_mod_cast hm
    linarith
  have hb := residueTuple_sum_bounds (h:=h) a (@normalizedSiftedCount s q _) normalizedSiftedCount_nonneg
  rw [normalizedSiftedCount_sum] at hb
  simp_rw [← siftedTuple_boxTuple] at hb
  unfold truncatedBoxMean
  constructor
  · calc
      _ = ((h:ℝ)-(q:ℝ))^s/(h:ℝ)^s := by rw [← div_pow]; congr 1; field_simp
      _ ≤ (((h/q:ℕ):ℝ)*(q:ℝ))^s/(h:ℝ)^s := div_le_div_of_nonneg_right
        (pow_le_pow_left₀ (sub_nonneg.mpr hqR) hfloor s) (by positivity)
      _ ≤ _ := by rw [mul_pow]; exact div_le_div_of_nonneg_right hb.1 (by positivity)
  · calc
      _ ≤ (((h/q+1:ℕ):ℝ)*(q:ℝ))^s/(h:ℝ)^s := by
        rw [mul_pow]; exact div_le_div_of_nonneg_right hb.2 (by positivity)
      _ ≤ ((h:ℝ)+(q:ℝ))^s/(h:ℝ)^s := div_le_div_of_nonneg_right
        (pow_le_pow_left₀ (by positivity) (by push_cast; nlinarith) s) (by positivity)
      _ = _ := by rw [← div_pow]; congr 1; field_simp

theorem distinctTruncatedBoxMean_le {s h q : ℕ} [NeZero q] (a : Fin s → ℤ) :
    distinctTruncatedBoxMean (h:=h) a q ≤ truncatedBoxMean (h:=h) a q := by
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
  intro n _ _
  rw [siftedTuple_eq]
  exact normalizedSiftedCount_nonneg _

theorem truncatedBoxMean_sub_distinct_le {s h q : ℕ} [NeZero q] (hh : 0<h)
    (a : Fin s → ℤ) :
    truncatedBoxMean (h:=h) a q - distinctTruncatedBoxMean (h:=h) a q ≤
      (s:ℝ)^2*(q:ℝ)^s/(h:ℝ) := by
  classical
  by_cases hs : s=0
  · subst s
    have hall : distinctBox (h:=h) a = Finset.univ := by
      ext n
      simp [distinctBox, Function.Injective]
    simp [truncatedBoxMean, distinctTruncatedBoxMean, hall]
  have hhR : (0:ℝ)<h := by exact_mod_cast hh
  have hsum := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Fin s → Fin h))
    (fun n => Function.Injective (boxTuple a n)) (fun n => siftedTuple (boxTuple a n) q)
  have hb : (∑ n ∈ Finset.univ.filter (fun n : Fin s → Fin h => ¬Function.Injective (boxTuple a n)),
      siftedTuple (boxTuple a n) q) ≤ (s:ℝ)^2*(h:ℝ)^(s-1)*(q:ℝ)^s := by
    calc
      _ ≤ ((Finset.univ.filter fun n : Fin s → Fin h => ¬Function.Injective (boxTuple a n)).card:ℝ) *
          (q:ℝ)^s := by
        simpa only [nsmul_eq_mul] using Finset.sum_le_card_nsmul _ _ ((q:ℝ)^s) (fun n _ => by
          rw [siftedTuple_eq]
          exact normalizedSiftedCount_le _)
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast boxTuple_nondistinct_count (h:=h) a)
        (by positivity)
  unfold truncatedBoxMean distinctTruncatedBoxMean distinctBox
  rw [← sub_div]
  calc
    _ ≤ ((s:ℝ)^2*(h:ℝ)^(s-1)*(q:ℝ)^s)/(h:ℝ)^s := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      linarith [hsum]
    _ = _ := by
      have hp : (h:ℝ)^s=(h:ℝ)^(s-1)*(h:ℝ) := by
        rw [← pow_succ]; congr 1; omega
      rw [hp]
      field_simp

theorem distinctTruncatedBoxMean_error {s h q : ℕ} [NeZero q] (hh : 0<h) (hq : q≤h)
    (a : Fin s → ℤ) :
    |distinctTruncatedBoxMean (h:=h) a q-1| ≤ boxTruncationError s h q := by
  have hb := truncatedBoxMean_bounds hh hq a
  have hd := truncatedBoxMean_sub_distinct_le (q:=q) hh a
  have hle := distinctTruncatedBoxMean_le (q:=q) (h:=h) a
  unfold boxTruncationError
  apply abs_le.mpr
  constructor
  · have hl := neg_abs_le ((1-(q:ℝ)/h)^s-1)
    have hpos := abs_nonneg ((1+(q:ℝ)/h)^s-1)
    linarith
  · have hu := le_abs_self ((1+(q:ℝ)/h)^s-1)
    have hpos := abs_nonneg ((1-(q:ℝ)/h)^s-1)
    have hnn : 0≤(s:ℝ)^2*(q:ℝ)^s/h := by positivity
    linarith

theorem singularTailBound_le_uniform {s M y : ℕ} (a : Fin s → ℤ)
    (ha : Function.Injective a) (hy : 1<y)
    (hd : ∀ i j, (a i-a j).natAbs ≤ M) :
    singularTailBound (Finset.univ.image a) y ≤ uniformSingularTailBound s M y := by
  have hc : (Finset.univ.image a).card=s := by
    rw [Finset.card_image_of_injective _ ha, Finset.card_univ, Fintype.card_fin]
  have hb := differenceProduct_le (Finset.univ.image a) (M:=M) (by
    intro x hx z hz
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hz
    exact hd i j)
  rw [hc] at hb
  have hl : Real.log (differenceProduct (Finset.univ.image a)) ≤
      ((s*(s-1):ℕ):ℝ)*Real.log M := by
    rw [← Real.log_pow]
    apply Real.log_le_log
    · exact_mod_cast differenceProduct_pos (Finset.univ.image a)
    · exact_mod_cast hb
  unfold singularTailBound uniformSingularTailBound
  rw [hc]
  apply add_le_add le_rfl
  calc
    _ ≤ 4*(s:ℝ)*(((s*(s-1):ℕ):ℝ)*Real.log M)/((y:ℝ)*Real.log y) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hl (by positivity))
        (mul_nonneg (by positivity) (Real.log_nonneg (by exact_mod_cast (show 1≤y by omega))))
    _ = _ := by ring

theorem uniformSingularTailBound_nonneg (s : ℕ) {M y : ℕ} (hM : 0<M) (hy : 1<y) :
    0 ≤ uniformSingularTailBound s M y := by
  have hlogM : 0≤Real.log (M:ℝ) := Real.log_nonneg (by exact_mod_cast hM)
  have hlogy : 0≤Real.log (y:ℝ) := Real.log_nonneg (by exact_mod_cast (show 1≤y by omega))
  unfold uniformSingularTailBound
  positivity

theorem singularBoxMean_sub_truncation {s h M y : ℕ} (a : Fin s → ℤ)
    (hy : 1<y) (hys : 2*s≤y) (hd : boxDiameterBound (h:=h) a M)
    (hB : uniformSingularTailBound s M y≤1) :
    |singularBoxMean (h:=h) a-distinctTruncatedBoxMean (h:=h) a (primorial y)| ≤
      2*uniformSingularTailBound s M y*distinctTruncatedBoxMean (h:=h) a (primorial y) := by
  classical
  let : NeZero (primorial y) := ⟨(primorial_pos y).ne'⟩
  have hpoint (n : Fin s → Fin h) (hn : n∈distinctBox a) :
      |singularSeries (Finset.univ.image (boxTuple a n))-siftedTuple (boxTuple a n) (primorial y)| ≤
      2*uniformSingularTailBound s M y*siftedTuple (boxTuple a n) (primorial y) := by
    have hi := (Finset.mem_filter.mp hn).2
    have hc : (Finset.univ.image (boxTuple a n)).card=s := by
      rw [Finset.card_image_of_injective _ hi, Finset.card_univ, Fintype.card_fin]
    have hut := singularTailBound_le_uniform (boxTuple a n) hi hy (hd n)
    have ht := singularTail_error (Finset.univ.image (boxTuple a n)) hy (by simpa only [hc] using hys)
      (hut.trans hB)
    have hp : 0 ≤ siftedTuple (boxTuple a n) (primorial y) := by
      rw [siftedTuple_eq]
      exact normalizedSiftedCount_nonneg _
    rw [singularSeries_eq_truncation_mul_tail _ hy (by simpa only [hc] using hys),
      ← siftedTuple_primorial_eq _ hi, ← primorial_eq_prod_primesLE]
    calc
      _ = siftedTuple (boxTuple a n) (primorial y)*|singularTail (Finset.univ.image (boxTuple a n)) y-1| := by
        rw [← mul_sub_one, abs_mul, abs_of_nonneg hp]
      _ ≤ siftedTuple (boxTuple a n) (primorial y)*(2*uniformSingularTailBound s M y) :=
        mul_le_mul_of_nonneg_left (ht.trans (mul_le_mul_of_nonneg_left hut (by norm_num))) hp
      _ = _ := by ring
  unfold singularBoxMean distinctTruncatedBoxMean
  rw [← sub_div, abs_div, abs_of_nonneg (by positivity : 0≤(h:ℝ)^s), ← Finset.sum_sub_distrib]
  calc
    _ ≤ (∑ n ∈ distinctBox a, |singularSeries (Finset.univ.image (boxTuple a n))-
        siftedTuple (boxTuple a n) (primorial y)|)/(h:ℝ)^s :=
      div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) (by positivity)
    _ ≤ (∑ n ∈ distinctBox a, 2*uniformSingularTailBound s M y*
        siftedTuple (boxTuple a n) (primorial y))/(h:ℝ)^s :=
      div_le_div_of_nonneg_right (Finset.sum_le_sum hpoint) (by positivity)
    _ = _ := by rw [← Finset.mul_sum]; ring

theorem singularBoxMean_error {s h M y : ℕ} (a : Fin s → ℤ) (hh : 0<h)
    (hM : 0<M) (hy : 1<y) (hys : 2*s≤y) (hd : boxDiameterBound (h:=h) a M)
    (hB : uniformSingularTailBound s M y≤1) (hq : primorial y≤h) :
    |singularBoxMean (h:=h) a-1| ≤ boxTruncationError s h (primorial y) +
      2*uniformSingularTailBound s M y*(1+(primorial y:ℝ)/h)^s := by
  let : NeZero (primorial y) := ⟨(primorial_pos y).ne'⟩
  have hb := uniformSingularTailBound_nonneg s hM hy
  calc
    _ ≤ |singularBoxMean (h:=h) a-distinctTruncatedBoxMean (h:=h) a (primorial y)| +
        |distinctTruncatedBoxMean (h:=h) a (primorial y)-1| := abs_sub_le _ _ _
    _ ≤ 2*uniformSingularTailBound s M y*distinctTruncatedBoxMean (h:=h) a (primorial y) +
        boxTruncationError s h (primorial y) := add_le_add
      (singularBoxMean_sub_truncation a hy hys hd hB) (distinctTruncatedBoxMean_error hh hq a)
    _ ≤ 2*uniformSingularTailBound s M y*(1+(primorial y:ℝ)/h)^s +
        boxTruncationError s h (primorial y) := add_le_add_left
      (mul_le_mul_of_nonneg_left ((distinctTruncatedBoxMean_le (q:=primorial y) a).trans (truncatedBoxMean_bounds hh hq a).2)
        (show 0 ≤ 2*uniformSingularTailBound s M y from mul_nonneg (by norm_num) hb)) _
    _ = _ := by ring

theorem singularCutoffScale_pos (s : ℕ) : 0<singularCutoffScale s := by
  unfold singularCutoffScale
  positivity

theorem singularCutoff_tendsto (s : ℕ) : Tendsto (singularCutoff s) atTop atTop :=
  tendsto_nat_floor_atTop.comp (Tendsto.atTop_div_const (singularCutoffScale_pos s)
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop))

theorem singularCutoff_ratio_tendsto (s : ℕ) :
    Tendsto (fun h : ℕ => (singularCutoff s h:ℝ)/Real.log h) atTop (𝓝 (1/singularCutoffScale s)) := by
  have hh := (tendsto_nat_floor_mul_div_atTop (a:=1/singularCutoffScale s)
    (one_div_nonneg.mpr (singularCutoffScale_pos s).le)).comp
    (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ)))
  simpa only [singularCutoff, one_div_mul_eq_div, Function.comp_def] using hh

theorem log_div_singularCutoff_tendsto (s : ℕ) :
    Tendsto (fun h : ℕ => Real.log h/(singularCutoff s h:ℝ)) atTop (𝓝 (singularCutoffScale s)) := by
  simpa only [inv_div, one_div, inv_inv] using (singularCutoff_ratio_tendsto s).inv₀
    (one_div_ne_zero (singularCutoffScale_pos s).ne')

theorem primorial_singularCutoff_power_bound (s : ℕ) {h : ℕ} (hh : 0<h) :
    (primorial (singularCutoff s h):ℝ)^(s+1) ≤ (h:ℝ)^(1/2:ℝ) := by
  have hhR : (0:ℝ)<h := by exact_mod_cast hh
  have hlog : 0≤Real.log (h:ℝ) := Real.log_nonneg (by exact_mod_cast hh)
  have hfloor := Nat.floor_le (div_nonneg hlog (singularCutoffScale_pos s).le)
  change (singularCutoff s h:ℝ) ≤ Real.log h/singularCutoffScale s at hfloor
  have hb := (le_div_iff₀ (singularCutoffScale_pos s)).mp hfloor
  have hexp : ((singularCutoff s h:ℝ)*((s:ℝ)+1))*Real.log 4 ≤ Real.log h*(1/2) := by
    unfold singularCutoffScale at hb
    nlinarith
  calc
    _ ≤ ((4:ℝ)^(singularCutoff s h))^(s+1) := pow_le_pow_left₀ (by positivity)
      (by exact_mod_cast primorial_le_four_pow (singularCutoff s h)) _
    _ = Real.exp (((singularCutoff s h:ℝ)*((s:ℝ)+1))*Real.log 4) := by
      rw [← pow_mul, ← Real.exp_log (by norm_num : (0:ℝ)<4), ← Real.exp_nat_mul]
      rw [Real.log_exp]
      push_cast
      congr 1
    _ ≤ _ := by rw [Real.rpow_def_of_pos hhR]; exact Real.exp_le_exp.mpr hexp

theorem primorial_singularCutoff_ratio_tendsto (s r : ℕ) (hr : r ≤ s+1) :
    Tendsto (fun h : ℕ => (primorial (singularCutoff s h):ℝ)^r/(h:ℝ)) atTop (𝓝 0) := by
  have ht : Tendsto (fun h : ℕ => (h:ℝ)^(-(1/2:ℝ))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1/2)).comp tendsto_natCast_atTop_atTop
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ht
  · exact Filter.Eventually.of_forall fun h => by positivity
  · filter_upwards [eventually_ge_atTop 1] with h hh
    have hhR : (0:ℝ)<h := by exact_mod_cast hh
    calc
      _ ≤ (primorial (singularCutoff s h):ℝ)^(s+1)/(h:ℝ) :=
        div_le_div_of_nonneg_right (by exact_mod_cast (Nat.pow_le_pow_right
          (primorial_pos (singularCutoff s h)) hr)) hhR.le
      _ ≤ (h:ℝ)^(1/2:ℝ)/(h:ℝ) := div_le_div_of_nonneg_right
        (primorial_singularCutoff_power_bound s (by omega)) hhR.le
      _ = _ := by
        have he := Real.rpow_sub hhR (1/2:ℝ) 1
        norm_num only [Real.rpow_one, show (1/2:ℝ)-1=-(1/2) by norm_num] at he
        exact he.symm

theorem primorial_singularCutoff_div_tendsto (s : ℕ) :
    Tendsto (fun h : ℕ => (primorial (singularCutoff s h):ℝ)/(h:ℝ)) atTop (𝓝 0) := by
  simpa only [pow_one] using primorial_singularCutoff_ratio_tendsto s 1 (by omega)

theorem log_mul_div_singularCutoff_tendsto (s : ℕ) {K : ℕ} (hK : 0<K) :
    Tendsto (fun h : ℕ => Real.log (K*h:ℕ)/(singularCutoff s h:ℝ)) atTop (𝓝 (singularCutoffScale s)) := by
  have hy := tendsto_natCast_atTop_atTop (R:=ℝ) |>.comp (singularCutoff_tendsto s)
  have hz : Tendsto (fun h : ℕ => Real.log (K:ℝ)/(singularCutoff s h:ℝ)) atTop (𝓝 0) := by
    simpa only [mul_zero, div_eq_mul_inv, Pi.inv_apply, Function.comp_apply] using hy.inv_tendsto_atTop.const_mul (Real.log (K:ℝ))
  have ht := hz.add (log_div_singularCutoff_tendsto s)
  rw [zero_add] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 1] with h hh
  rw [Nat.cast_mul, Real.log_mul (by exact_mod_cast hK.ne') (by exact_mod_cast (show h≠0 by omega)), add_div]

theorem uniformSingularTailBound_tendsto (s : ℕ) {K : ℕ} (hK : 0<K) :
    Tendsto (fun h : ℕ => uniformSingularTailBound s (K*h) (singularCutoff s h)) atTop (𝓝 0) := by
  have hy := tendsto_natCast_atTop_atTop (R:=ℝ) |>.comp (singularCutoff_tendsto s)
  have hl := Real.tendsto_log_atTop.comp hy
  have ht := (hy.inv_tendsto_atTop.const_mul (2*((s:ℝ)^2*(2:ℝ)^s))).add
    (((log_mul_div_singularCutoff_tendsto s hK).mul hl.inv_tendsto_atTop).const_mul
      (4*(s:ℝ)*((s*(s-1):ℕ):ℝ)))
  simp only [mul_zero, add_zero] at ht
  convert ht using 1
  ext h
  unfold uniformSingularTailBound
  simp only [div_eq_mul_inv, mul_inv_rev, Pi.inv_apply, Function.comp_apply]
  ring

theorem boxTruncationError_tendsto (s : ℕ) :
    Tendsto (fun h : ℕ => boxTruncationError s h (primorial (singularCutoff s h))) atTop (𝓝 0) := by
  have hq := primorial_singularCutoff_div_tendsto s
  have hl := ((tendsto_const_nhds (x:=(1:ℝ)).sub hq).pow s).sub (tendsto_const_nhds (x:=(1:ℝ)))
  have hu := ((tendsto_const_nhds (x:=(1:ℝ)).add hq).pow s).sub (tendsto_const_nhds (x:=(1:ℝ)))
  have hd := (primorial_singularCutoff_ratio_tendsto s s (by omega)).const_mul ((s:ℝ)^2)
  have ht := (hl.abs.add hu.abs).add hd
  simp only [sub_zero, one_pow, sub_self, add_zero, abs_zero, mul_zero] at ht
  convert ht using 1
  ext h
  unfold boxTruncationError
  ring

theorem singularBoxError_tendsto (s : ℕ) {K : ℕ} (hK : 0<K) :
    Tendsto (singularBoxError s K) atTop (𝓝 0) := by
  have ht := (boxTruncationError_tendsto s).add
    (((uniformSingularTailBound_tendsto s hK).const_mul 2).mul
      ((tendsto_const_nhds (x:=(1:ℝ))).add (primorial_singularCutoff_div_tendsto s) |>.pow s))
  simp only [mul_zero, zero_mul, add_zero] at ht
  exact ht

theorem singularBoxMean_error_eventually (s : ℕ) {K : ℕ} (hK : 0<K) :
    ∀ᶠ h : ℕ in atTop, ∀ a : Fin s → ℤ, boxDiameterBound (h:=h) a (K*h) →
      |singularBoxMean (h:=h) a-1| ≤ singularBoxError s K h := by
  have hB := (uniformSingularTailBound_tendsto s hK).eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1))
  have hq := (primorial_singularCutoff_div_tendsto s).eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1))
  filter_upwards [eventually_ge_atTop 1, (singularCutoff_tendsto s).eventually_ge_atTop 2,
      (singularCutoff_tendsto s).eventually_ge_atTop (2*s), hB, hq] with h hh hy hys hB hq
  intro a hd
  have hqh : primorial (singularCutoff s h) ≤ h := by
    have hhR : (0:ℝ)<h := by exact_mod_cast hh
    have ht := (div_lt_one hhR).mp hq
    exact_mod_cast ht.le
  exact singularBoxMean_error a (by omega) (Nat.mul_pos hK (by omega)) (by omega) hys hd hB.le hqh

theorem singularBoxMean_uniform (s : ℕ) {K : ℕ} (hK : 0<K) {ε : ℝ} (hε : 0<ε) :
    ∃ h₀ : ℕ, ∀ h≥h₀, ∀ a : Fin s → ℤ, boxDiameterBound (h:=h) a (K*h) →
      |singularBoxMean (h:=h) a-1| < ε := by
  have he := (singularBoxError_tendsto s hK).eventually (gt_mem_nhds hε)
  have hb := (singularBoxMean_error_eventually s hK).and he
  obtain ⟨h₀, hh₀⟩ := Filter.eventually_atTop.mp hb
  exact ⟨h₀, fun h hh a hd => ((hh₀ h hh).1 a hd).trans_lt (hh₀ h hh).2⟩

end LargePrimeGaps

end OAI
end

section
-- module Solutions.OAIW2_P344.PrimeGaps_ZetaKernel
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

theorem mangoldt_log_term_nonneg (s : ℝ) (n : ℕ) :
    0 ≤ ArithmeticFunction.vonMangoldt n / ((n:ℝ)^s*Real.log n) := by
  positivity

theorem mangoldt_log_term_le (s : ℝ) (n : ℕ) :
    ArithmeticFunction.vonMangoldt n / ((n:ℝ)^s*Real.log n) ≤ 1/(n:ℝ)^s := by
  by_cases hn : n≤1
  · interval_cases n <;> simp
    positivity
  have hnR : (1:ℝ)<n := by exact_mod_cast (show 1<n by omega)
  have hlog : 0<Real.log (n:ℝ) := Real.log_pos hnR
  have hpow : 0<(n:ℝ)^s := Real.rpow_pos_of_pos (by linarith) _
  calc
    _ ≤ Real.log (n:ℝ)/((n:ℝ)^s*Real.log n) :=
      div_le_div_of_nonneg_right ArithmeticFunction.vonMangoldt_le_log (mul_pos hpow hlog).le
    _ = _ := by field_simp

theorem prime_power_sum_le_log_zeta (X : ℕ) {s : ℝ} (hs : 1<s) :
    (∑ p ∈ Nat.primesLE X, 1/(p:ℝ)^s) ≤ Real.log (riemannZeta (s:ℂ)).re := by
  have hsum : Summable (fun n : ℕ => ArithmeticFunction.vonMangoldt n / ((n:ℝ)^s*Real.log n)) :=
    (Real.summable_one_div_nat_rpow.mpr hs).of_nonneg_of_le
      (mangoldt_log_term_nonneg s) (mangoldt_log_term_le s)
  rw [log_riemannZeta_eq hs]
  calc
    _ = ∑ p ∈ Nat.primesLE X, ArithmeticFunction.vonMangoldt p / ((p:ℝ)^s*Real.log p) := by
      apply Finset.sum_congr rfl
      intro p hp
      have hpP := (Nat.mem_primesLE.mp hp).2
      have hl : Real.log (p:ℝ)≠0 := (Real.log_pos (by exact_mod_cast hpP.one_lt)).ne'
      rw [ArithmeticFunction.vonMangoldt_apply_prime hpP]
      field_simp
    _ ≤ _ := Summable.sum_le_tsum _ (fun n _ => mangoldt_log_term_nonneg s n) hsum

theorem prime_reciprocal_rankin (X : ℕ) (hX : 2≤X) :
    (∑ p ∈ Nat.primesLE X, (1:ℝ)/p) ≤
      Real.exp 1*Real.log (riemannZeta ((1+1/Real.log X:ℝ):ℂ)).re := by
  have hlog : 0<Real.log (X:ℝ) := Real.log_pos (by exact_mod_cast hX)
  have hs : 1<(1:ℝ)+1/Real.log X := lt_add_of_pos_right 1 (one_div_pos.mpr hlog)
  calc
    _ ≤ ∑ p ∈ Nat.primesLE X, Real.exp 1*(1/(p:ℝ)^(1+1/Real.log X)) := by
      apply Finset.sum_le_sum
      intro p hp
      have hpP := (Nat.mem_primesLE.mp hp).2
      have hpX := (Nat.mem_primesLE.mp hp).1
      have hp0 : (0:ℝ)<p := by exact_mod_cast hpP.pos
      have hpY : Real.log (p:ℝ)≤Real.log (X:ℝ) := Real.log_le_log hp0 (by exact_mod_cast hpX)
      have he : (p:ℝ)^(1/Real.log X:ℝ) ≤ Real.exp 1 := by
        rw [Real.rpow_def_of_pos hp0]
        apply Real.exp_le_exp.mpr
        simpa only [mul_one_div] using (div_le_one hlog).mpr hpY
      calc
        _ = (p:ℝ)^(1/Real.log X:ℝ)/(p:ℝ)^(1+1/Real.log X:ℝ) := by
          rw [Real.rpow_add hp0, Real.rpow_one]
          field_simp
        _ ≤ Real.exp 1/(p:ℝ)^(1+1/Real.log X:ℝ) := div_le_div_of_nonneg_right he (by positivity)
        _ = _ := by ring
    _ = Real.exp 1*(∑ p ∈ Nat.primesLE X, 1/(p:ℝ)^(1+1/Real.log X:ℝ)) := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (prime_power_sum_le_log_zeta X hs) (Real.exp_pos _).le

theorem eventually_prime_reciprocal_bound :
    ∀ᶠ X : ℕ in atTop, (∑ p ∈ Nat.primesLE X, (1:ℝ)/p) ≤
      Real.exp 1*(1+Real.log (Real.log X)) := by
  have hlog := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  have hx : Tendsto (fun X : ℕ => (1:ℝ)+1/Real.log X) atTop (𝓝[>] 1) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_,?_⟩
    · simpa only [one_div, add_zero, Pi.inv_apply, Function.comp_def] using tendsto_const_nhds.add hlog.inv_tendsto_atTop
    · filter_upwards [eventually_ge_atTop 2] with X hX
      exact lt_add_of_pos_right 1 (one_div_pos.mpr (Real.log_pos (by exact_mod_cast hX)))
  have hζ : Tendsto (fun s : ℝ => Real.log (riemannZeta (s:ℂ)).re + Real.log (s-1))
      (𝓝[>] 1) (𝓝 0) :=
    log_riemannZeta_add_log_sub_isLittleO_ofReal.tendsto_zero_of_tendsto tendsto_const_nhds
  have hb := (hζ.comp hx).eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1))
  filter_upwards [hb, eventually_ge_atTop 2] with X hζX hX
  have he : Real.log (riemannZeta ((1+1/Real.log X:ℝ):ℂ)).re ≤ 1+Real.log (Real.log X) := by
    dsimp only [Function.comp_apply] at hζX
    rw [add_sub_cancel_left, one_div, Real.log_inv] at hζX
    simp only [one_div] at *
    linarith
  exact (prime_reciprocal_rankin X hX).trans (mul_le_mul_of_nonneg_left he (Real.exp_pos _).le)

open Asymptotics

theorem zeta_pole_linear_error :
    ∃ c>0, ∃ ε>0, ∀ z : ℂ, z≠0 → ‖z‖<ε →
      ‖z*riemannZeta (1+z)-1‖ ≤ c*‖z‖ := by
  obtain ⟨c,hc,hbound⟩ := (differentiable_riemannZeta₁ 1).isBigO_sub.exists_pos
  have hb := hbound.bound
  rw [Metric.eventually_nhds_iff] at hb
  obtain ⟨ε,hε,hεb⟩ := hb
  refine ⟨c,hc,ε,hε,fun z hz hze => ?_⟩
  have hs : (1:ℂ)+z≠1 := by simpa using hz
  have ht := @hεb (1+z) (by simpa only [dist_eq_norm, add_sub_cancel_left] using hze)
  have he : z*riemannZeta (1+z) = riemannZeta₁ (1+z) := by
    rw [riemannZeta_eq_inv_sub_mul hs, add_sub_cancel_left, ← mul_assoc, mul_inv_cancel₀ hz, one_mul]
  simpa only [riemannZeta₁_one, add_sub_cancel_left, he] using ht

theorem zeta_pole_two_sided :
    ∃ c>0, ∃ ε>0, ∀ z : ℂ, z≠0 → ‖z‖<ε →
      ‖z*riemannZeta (1+z)-1‖ ≤ c*‖z‖ ∧
      1/2 ≤ ‖z*riemannZeta (1+z)‖ ∧ ‖z*riemannZeta (1+z)‖ ≤ 3/2 := by
  obtain ⟨c,hc,ε,hε,hb⟩ := zeta_pole_linear_error
  refine ⟨c,hc,min ε (1/(2*c)), lt_min hε (by positivity), fun z hz hze => ?_⟩
  have he := hb z hz (hze.trans_le (min_le_left _ _))
  have hzbound : c*‖z‖<1/2 := by
    have hh := hze.trans_le (min_le_right _ _)
    have hm := (lt_div_iff₀ (show 0<2*c by positivity)).mp hh
    nlinarith
  refine ⟨he,?_,?_⟩
  · have ht := norm_sub_norm_le (1:ℂ) (z*riemannZeta (1+z))
    rw [norm_one, norm_sub_rev] at ht
    linarith
  · have ht := norm_sub_norm_le (z*riemannZeta (1+z)) (1:ℂ)
    rw [norm_one] at ht
    linarith

theorem norm_prod_sub_prod_le {ι : Type*} (s : Finset ι) (f g : ι → ℂ)
    (B e : ι → ℝ) (hB : ∀ i∈s, 1≤B i)
    (hf : ∀ i∈s, ‖f i‖≤B i) (hg : ∀ i∈s, ‖g i‖≤B i)
    (he : ∀ i∈s, ‖f i-g i‖≤e i) :
    ‖(∏ i∈s, f i)-(∏ i∈s, g i)‖ ≤ (∏ i∈s, B i)*(∑ i∈s, e i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hBas : ∀ i∈s, 1≤B i := fun i hi => hB i (Finset.mem_insert_of_mem hi)
    have hfs : ∀ i∈s, ‖f i‖≤B i := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hgs : ∀ i∈s, ‖g i‖≤B i := fun i hi => hg i (Finset.mem_insert_of_mem hi)
    have hes : ∀ i∈s, ‖f i-g i‖≤e i := fun i hi => he i (Finset.mem_insert_of_mem hi)
    have hBa := hB a (Finset.mem_insert_self _ _)
    have hga := hg a (Finset.mem_insert_self _ _)
    have hea := he a (Finset.mem_insert_self _ _)
    have hea0 : 0≤e a := (norm_nonneg _).trans hea
    have hprod0 : 0≤∏ i∈s, B i := Finset.prod_nonneg (fun i hi => (hBas i hi).trans' zero_le_one)
    have hsum0 : 0≤∑ i∈s, e i := Finset.sum_nonneg fun i hi => (norm_nonneg _).trans (hes i hi)
    have hprod : ‖∏ i∈s, f i‖≤∏ i∈s, B i := by
      rw [norm_prod]
      exact Finset.prod_le_prod (fun i _ => norm_nonneg _) hfs
    have hi := ih hBas hfs hgs hes
    simp only [Finset.prod_insert ha, Finset.sum_insert ha]
    calc
      _ = ‖(f a-g a)*(∏ i∈s, f i)+g a*((∏ i∈s, f i)-(∏ i∈s, g i))‖ := by congr 1; ring
      _ ≤ ‖f a-g a‖*‖∏ i∈s, f i‖+‖g a‖*‖(∏ i∈s, f i)-(∏ i∈s, g i)‖ := by
        simpa only [norm_mul] using norm_add_le ((f a-g a)*(∏ i∈s, f i)) (g a*((∏ i∈s, f i)-(∏ i∈s, g i)))
      _ ≤ e a*(∏ i∈s, B i)+B a*((∏ i∈s, B i)*(∑ i∈s, e i)) := by
        gcongr
      _ ≤ (B a*(∏ i∈s, B i))*(e a+∑ i∈s, e i) := by
        nlinarith [mul_nonneg hea0 hprod0, mul_nonneg (sub_nonneg.mpr hBa) (mul_nonneg hea0 hprod0)]

theorem norm_prod_sub_one_le {ι : Type*} (s : Finset ι) (f : ι → ℂ)
    {B e : ℝ} (hB : 1≤B) (hf : ∀ i∈s, ‖f i‖≤B) (he : ∀ i∈s, ‖f i-1‖≤e) :
    ‖(∏ i∈s, f i)-1‖ ≤ B^s.card*(s.card*e) := by
  simpa only [Finset.prod_const, Finset.sum_const, nsmul_eq_mul, Finset.prod_const_one, one_pow]
    using norm_prod_sub_prod_le s f (fun _ => 1) (fun _ => B) (fun _ => e)
      (fun _ _ => hB) hf (by simpa using fun _ _ => hB) he

theorem mem_nonemptySubsets {ι : Type*} {s S : Finset ι} :
    S∈nonemptySubsets s ↔ S.Nonempty ∧ S⊆s := by
  classical
  simp [nonemptySubsets, Finset.nonempty_iff_ne_empty]

theorem sum_nonemptySubsets_sign {ι : Type*} {s : Finset ι} (hs : s.Nonempty) :
    (∑ S∈nonemptySubsets s, (-1:ℤ)^S.card) = -1 := by
  classical
  have h := Finset.sum_erase_add s.powerset (fun S => (-1:ℤ)^S.card) (Finset.empty_mem_powerset s)
  rw [Finset.sum_powerset_neg_one_pow_card_of_nonempty hs] at h
  simpa only [Finset.card_empty, pow_zero, add_eq_zero_iff_eq_neg, nonemptySubsets] using h

theorem prod_const_zpow {ι : Type*} (s : Finset ι) (f : ι → ℤ) {c : ℂ} (hc : c≠0) :
    (∏ i∈s, c^(f i)) = c^(∑ i∈s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp only [Finset.prod_insert ha, Finset.sum_insert ha, zpow_add₀ hc, ih]

theorem norm_inv_sub_one_le {a : ℂ} (ha : 1/2≤‖a‖) : ‖a⁻¹-1‖≤2*‖a-1‖ := by
  have ha0 : a≠0 := norm_pos_iff.mp (by linarith)
  have he : a⁻¹-1 = -(a-1)/a := by field_simp; ring
  rw [he, norm_div, norm_neg]
  apply (div_le_iff₀ (by linarith : 0<‖a‖)).mpr
  nlinarith [norm_nonneg (a-1)]

theorem frequencyW_norm (u : ℝ) : ‖frequencyW u‖≤1+|u| := by
  simpa [frequencyW] using norm_add_le (1:ℂ) (Complex.I*(u:ℂ))

theorem frequencySum_re {ι : Type*} (S : Finset ι) (u : ι → ℝ) :
    (∑ i∈S, frequencyW (u i)).re=(S.card:ℝ) := by simp

theorem frequencySum_norm_lower {ι : Type*} {S : Finset ι} (hS : S.Nonempty) (u : ι → ℝ) :
    1≤‖∑ i∈S, frequencyW (u i)‖ := by
  have hc : (1:ℝ)≤S.card := by exact_mod_cast hS.card_pos
  have hr := Complex.re_le_norm (∑ i∈S, frequencyW (u i))
  rw [frequencySum_re] at hr
  exact hc.trans hr

theorem frequencySum_ne_zero {ι : Type*} {S : Finset ι} (hS : S.Nonempty) (u : ι → ℝ) :
    ∑ i∈S, frequencyW (u i)≠0 :=
  norm_pos_iff.mp ((by norm_num : (0:ℝ)<1).trans_le (frequencySum_norm_lower hS u))

theorem frequencySum_norm_upper {ι : Type*} (S : Finset ι) (u : ι → ℝ)
    {U : ℝ} (hu : ∀ i∈S, |u i|≤U) :
    ‖∑ i∈S, frequencyW (u i)‖ ≤ S.card*(1+U) := by
  calc
    _ ≤ ∑ i∈S, ‖frequencyW (u i)‖ := norm_sum_le _ _
    _ ≤ ∑ _i∈S, (1+U) := Finset.sum_le_sum fun i hi => (frequencyW_norm _).trans (by linarith [hu i hi])
    _ = _ := by simp; ring

end LargePrimeGaps

end OAI
end

section
-- module Solutions.OAIW2_P344.PrimeGaps_EulerFactors
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

open Asymptotics

theorem norm_prod_linear_remainder {ι : Type*} (s : Finset ι) (f : ι → ℂ)
    {e : ℝ} (he : 0≤e) (hf : ∀ i∈s, ‖f i‖≤2) (hd : ∀ i∈s, ‖f i-1‖≤e) :
    ‖(∏ i∈s, f i)-1-(∑ i∈s, (f i-1))‖ ≤ (s.card:ℝ)^2*2^s.card*e^2 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hfs : ∀ i∈s, ‖f i‖≤2 := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hds : ∀ i∈s, ‖f i-1‖≤e := fun i hi => hd i (Finset.mem_insert_of_mem hi)
    have hfa := hf a (Finset.mem_insert_self _ _)
    have hda := hd a (Finset.mem_insert_self _ _)
    have hi := ih hfs hds
    have hsum : ‖∑ i∈s, (f i-1)‖≤ s.card*e := by
      exact (norm_sum_le _ _).trans (by simpa using Finset.sum_le_sum hds)
    have hcard : 0≤(s.card:ℝ) := Nat.cast_nonneg _
    have hpow : (1:ℝ)≤2^s.card := one_le_pow₀ (by norm_num)
    simp only [Finset.prod_insert ha, Finset.sum_insert ha, Finset.card_insert_of_notMem ha,
      Nat.cast_add, Nat.cast_one, pow_succ]
    calc
      _ = ‖f a*((∏ i∈s, f i)-1-(∑ i∈s, (f i-1)))+(f a-1)*(∑ i∈s, (f i-1))‖ := by congr 1; ring
      _ ≤ ‖f a‖*‖(∏ i∈s, f i)-1-(∑ i∈s, (f i-1))‖+‖f a-1‖*‖∑ i∈s, (f i-1)‖ := by
        simpa only [norm_mul] using norm_add_le (f a*((∏ i∈s, f i)-1-(∑ i∈s, (f i-1)))) ((f a-1)*(∑ i∈s, (f i-1)))
      _ ≤ 2*((s.card:ℝ)^2*2^s.card*e^2)+e*(s.card*e) := by gcongr
      _ ≤ ((s.card:ℝ)+1)^2*(2^s.card*2)*e^2 := by
        have hcoeff : (s.card:ℝ)≤(4*(s.card:ℝ)+2)*2^s.card := by nlinarith
        nlinarith [mul_le_mul_of_nonneg_right hcoeff (sq_nonneg e)]

theorem norm_one_sub_lower {a : ℂ} {r : ℝ} (ha : ‖a‖≤r) :
    1-r≤‖1-a‖ := by
  have hh := norm_sub_norm_le (1:ℂ) a
  rw [norm_one] at hh
  linarith

theorem norm_one_sub_zpow_sub_one {a : ℂ} {r : ℝ} (hr : r≤1/2) (ha : ‖a‖≤r)
    {σ : ℤ} (hσ : σ=1 ∨ σ= -1) :
    ‖(1-a)^σ-1‖≤2*r := by
  have hr0 : 0≤r := (norm_nonneg _).trans ha
  have hl := norm_one_sub_lower ha
  have hn : 1-a≠0 := norm_pos_iff.mp (by linarith)
  obtain rfl | rfl := hσ
  · simpa only [zpow_one, sub_sub_cancel_left, norm_neg] using ha.trans (by linarith : r≤2*r)
  · rw [zpow_neg_one]
    have hid : (1-a)⁻¹-1=a/(1-a) := by field_simp; ring
    rw [hid, norm_div]
    apply (div_le_iff₀ (by linarith : 0<‖1-a‖)).mpr
    nlinarith

theorem norm_one_sub_zpow_linear {a : ℂ} {r : ℝ} (hr : r≤1/2) (ha : ‖a‖≤r)
    {σ : ℤ} (hσ : σ=1 ∨ σ= -1) :
    ‖(1-a)^σ-1+(σ:ℂ)*a‖≤2*r^2 := by
  have hr0 : 0≤r := (norm_nonneg _).trans ha
  have hl := norm_one_sub_lower ha
  have hn : 1-a≠0 := norm_pos_iff.mp (by linarith)
  obtain rfl | rfl := hσ
  · simp; positivity
  · simp only [zpow_neg_one, Int.cast_neg, Int.cast_one, neg_one_mul]
    have hid : (1-a)⁻¹-1+-a=a^2/(1-a) := by field_simp; ring
    rw [hid, norm_div, norm_pow]
    apply (div_le_iff₀ (by linarith : 0<‖1-a‖)).mpr
    nlinarith [sq_nonneg r, norm_nonneg a, sq_nonneg (r-‖a‖)]

theorem genericLocalQuotient_error {ι : Type*} (s : Finset ι) (σ : ι → ℤ)
    (a : ι → ℂ) {ρ r : ℝ} (hr0 : 0≤r) (hr : r≤1/2)
    (hρ0 : 0≤ρ) (hρ : ρ≤2) (hρ1 : |ρ-1|≤2*r)
    (hσ : ∀ i∈s, σ i=1 ∨ σ i= -1) (ha : ∀ i∈s, ‖a i‖≤r) :
    ‖genericLocalQuotient s σ a ρ-1‖ ≤
      ((1+s.card)*(4*(s.card:ℝ)^2*2^s.card+2*s.card)+2*s.card+2*(s.card:ℝ)^2)*r^2 := by
  classical
  let A : ℂ := ∑ i∈s, (σ i:ℂ)*a i
  let T : ℂ := ∏ i∈s, (1-a i)^(σ i)
  have hsig (i : ι) (hi : i∈s) : ‖(σ i:ℂ)‖=1 := by
    rcases hσ i hi with hh | hh <;> simp [hh]
  have hA : ‖A‖≤ s.card*r := by
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ _i∈s, r := Finset.sum_le_sum fun i hi => by rw [norm_mul, hsig i hi, one_mul]; exact ha i hi
      _ = _ := by simp
  have he : ‖T-1+A‖≤(4*(s.card:ℝ)^2*2^s.card+2*s.card)*r^2 := by
    have hf : ∀ i∈s, ‖(1-a i)^(σ i)‖≤2 := by
      intro i hi
      have hh := norm_one_sub_zpow_sub_one hr (ha i hi) (hσ i hi)
      have hn := norm_sub_norm_le ((1-a i)^(σ i)) (1:ℂ)
      rw [norm_one] at hn
      linarith
    have hprod := norm_prod_linear_remainder s (fun i => (1-a i)^(σ i)) (by positivity : 0≤2*r)
      hf (fun i hi => norm_one_sub_zpow_sub_one hr (ha i hi) (hσ i hi))
    have herr : ‖∑ i∈s, ((1-a i)^(σ i)-1+(σ i:ℂ)*a i)‖≤ s.card*(2*r^2) := by
      exact (norm_sum_le _ _).trans (by simpa using Finset.sum_le_sum (fun i hi => norm_one_sub_zpow_linear hr (ha i hi) (hσ i hi)))
    have hid : T-1+A = (T-1-(∑ i∈s, ((1-a i)^(σ i)-1)))+
        (∑ i∈s, ((1-a i)^(σ i)-1+(σ i:ℂ)*a i)) := by
      rw [Finset.sum_add_distrib]; dsimp [A]; ring
    rw [hid]
    exact (norm_add_le _ _).trans ((add_le_add hprod herr).trans (by ring_nf; rfl))
  have hP : ‖1+(ρ:ℂ)*A‖≤1+s.card := by
    calc
      _ ≤ 1+ρ*‖A‖ := by simpa only [norm_one, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hρ0] using norm_add_le (1:ℂ) ((ρ:ℂ)*A)
      _ ≤ 1+2*(s.card*r) := by gcongr
      _ ≤ 1+s.card := by nlinarith [Nat.cast_nonneg (α:=ℝ) s.card]
  have hid : genericLocalQuotient s σ a ρ-1 =
      (1+(ρ:ℂ)*A)*(T-1+A)+((ρ:ℂ)-1)*A-(ρ:ℂ)*A^2 := by dsimp [genericLocalQuotient, A, T]; ring
  rw [hid]
  calc
    _ ≤ ‖1+(ρ:ℂ)*A‖*‖T-1+A‖+‖(ρ:ℂ)-1‖*‖A‖+‖(ρ:ℂ)‖*‖A‖^2 := by
      have h1 := norm_sub_le ((1+(ρ:ℂ)*A)*(T-1+A)+((ρ:ℂ)-1)*A) ((ρ:ℂ)*A^2)
      have h2 := norm_add_le ((1+(ρ:ℂ)*A)*(T-1+A)) (((ρ:ℂ)-1)*A)
      simp only [norm_mul, norm_pow] at h1 h2
      linarith

    _ ≤ (1+s.card)*((4*(s.card:ℝ)^2*2^s.card+2*s.card)*r^2)+(2*r)*(s.card*r)+2*(s.card*r)^2 := by
      have hρn : ‖(ρ:ℂ)‖≤2 := by simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hρ0] using hρ
      have hρd : ‖(ρ:ℂ)-1‖≤2*r := by exact_mod_cast hρ1
      gcongr
    _ = _ := by ring

theorem norm_exp_sub_one_le_of_re_nonpos {z : ℂ} (hz : z.re≤0) :
    ‖Complex.exp z-1‖ ≤ ‖z‖ := by
  have hd (t : ℝ) : HasDerivAt (fun t : ℝ => Complex.exp ((t:ℂ)*z))
      (Complex.exp ((t:ℂ)*z)*z) t := by
    simpa using ((Complex.ofRealCLM.hasDerivAt (x := t)).mul_const z).cexp
  have hb (t : ℝ) (ht : t∈Set.Ico (0:ℝ) 1) :
      ‖Complex.exp ((t:ℂ)*z)*z‖ ≤ ‖z‖ := by
    rw [norm_mul, Complex.norm_exp]
    have he : Real.exp ((t:ℂ)*z).re ≤ 1 := by
      rw [Real.exp_le_one_iff]
      simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
        using mul_nonpos_of_nonneg_of_nonpos ht.1 hz
    exact mul_le_of_le_one_left (norm_nonneg z) he
  simpa only [Complex.ofReal_one, one_mul, Complex.ofReal_zero, zero_mul,
    Complex.exp_zero] using norm_image_sub_le_of_norm_deriv_le_segment_01'
      (fun t _ => (hd t).hasDerivWithinAt) hb

theorem primeMonomial_norm_le {ι : Type*} {p : ℕ} (hp : 1≤p)
    (z : ι → ℂ) (S : Finset ι) (hz : ∀ i∈S, 0≤(z i).re) :
    ‖primeMonomial p z S‖ ≤ 1 := by
  rw [primeMonomial, Complex.norm_exp, Real.exp_le_one_iff]
  have hlog : 0≤Real.log (p:ℝ) := Real.log_nonneg (by exact_mod_cast hp)
  have hs : 0≤∑ i∈S, (z i).re := Finset.sum_nonneg hz
  simpa only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.neg_im,
    Complex.ofReal_im, neg_zero, zero_mul, sub_zero, Complex.re_sum]
    using mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hlog) hs

theorem primeMonomial_sub_one {ι : Type*} {p : ℕ} (hp : 1≤p)
    (z : ι → ℂ) (S : Finset ι) (hz : ∀ i∈S, 0≤(z i).re) :
    ‖primeMonomial p z S-1‖ ≤ Real.log p*(∑ i∈S, ‖z i‖) := by
  have hlog : 0≤Real.log (p:ℝ) := Real.log_nonneg (by exact_mod_cast hp)
  have hexp : (-(Real.log p : ℂ)*(∑ i∈S, z i)).re≤0 := by
    have hs : 0≤∑ i∈S, (z i).re := Finset.sum_nonneg hz
    simpa only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.neg_im,
      Complex.ofReal_im, neg_zero, zero_mul, sub_zero, Complex.re_sum]
      using mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hlog) hs
  calc
    _ ≤ ‖-(Real.log p : ℂ)*(∑ i∈S, z i)‖ := norm_exp_sub_one_le_of_re_nonpos hexp
    _ = Real.log p*‖∑ i∈S, z i‖ := by rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlog]
    _ ≤ _ := mul_le_mul_of_nonneg_left (norm_sum_le _ _) hlog

theorem sign_zpow_cases (n : ℕ) : (-1:ℤ)^n=1 ∨ (-1:ℤ)^n= -1 := by
  rcases Nat.even_or_odd n with h | h
  · exact Or.inl h.neg_one_pow
  · exact Or.inr h.neg_one_pow

theorem primeMonomial_scaled_norm {ι : Type*} {p : ℕ} (hp : 1≤p)
    (z : ι → ℂ) (S : Finset ι) (hz : ∀ i∈S, 0≤(z i).re) :
    ‖(p:ℂ)⁻¹*primeMonomial p z S‖ ≤ (p:ℝ)⁻¹ := by
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  exact mul_le_of_le_one_right (by positivity) (primeMonomial_norm_le hp z S hz)

theorem delta_bounds {p δ : ℕ} (hp : 2≤p) (hδ : δ≤1) :
    0<(p:ℝ)-δ ∧ ((p:ℝ)-δ)⁻¹≤2*(p:ℝ)⁻¹ ∧
      0≤(p:ℝ)/((p:ℝ)-δ) ∧ (p:ℝ)/((p:ℝ)-δ)≤2 ∧
        |(p:ℝ)/((p:ℝ)-δ)-1|≤2*(p:ℝ)⁻¹ := by
  have hpR : (2:ℝ)≤p := by exact_mod_cast hp
  have hdR : (δ:ℝ)≤1 := by exact_mod_cast hδ
  have hd0 : (0:ℝ)≤δ := by positivity
  have hp0 : (0:ℝ)<p := by linarith
  have hpd : (0:ℝ)<p-δ := by linarith
  refine ⟨hpd,?_,by positivity,?_,?_⟩
  · rw [inv_eq_one_div, ← div_eq_mul_inv]
    apply (div_le_div_iff₀ hpd hp0).mpr
    linarith
  · exact (div_le_iff₀ hpd).mpr (by linarith)
  · have hid : (p:ℝ)/(p-δ)-1 = δ/(p-δ) := by field_simp; ring
    rw [hid, abs_of_nonneg (by positivity)]
    change (δ:ℝ)/((p:ℝ)-δ)≤2/(p:ℝ)
    apply (div_le_div_iff₀ hpd hp0).mpr
    nlinarith

theorem eulerH_generic_eq {ι : Type*} {p δ : ℕ} (hp : 2≤p) (hδ : δ≤1)
    (A : Finset (Finset ι)) (z : ι → ℂ) :
    eulerH p δ A A z = genericLocalQuotient A
      (fun S => (-1:ℤ)^S.card) (fun S => (p:ℂ)⁻¹*primeMonomial p z S)
      ((p:ℝ)/((p:ℝ)-δ)) := by
  have hp0 : (p:ℂ)≠0 := by exact_mod_cast (by omega : p≠0)
  have hpd : (p:ℂ)-(δ:ℂ)≠0 := by exact_mod_cast (delta_bounds hp hδ).1.ne'
  unfold eulerH eulerP genericLocalQuotient
  congr 1
  push_cast
  rw [Finset.mul_sum, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro S _
  field_simp

theorem eulerH_generic_error {ι : Type*} {p δ : ℕ} (hp : 2≤p) (hδ : δ≤1)
    (A : Finset (Finset ι)) (z : ι → ℂ) (hz : ∀ S∈A, ∀ i∈S, 0≤(z i).re) :
    ‖eulerH p δ A A z-1‖ ≤
      ((1+A.card)*(4*(A.card:ℝ)^2*2^A.card+2*A.card)+2*A.card+2*(A.card:ℝ)^2)/(p:ℝ)^2 := by
  rw [eulerH_generic_eq hp hδ]
  have hd := delta_bounds hp hδ
  have hr : (p:ℝ)⁻¹≤1/2 := by
    rw [inv_eq_one_div]
    apply (div_le_div_iff₀ (by exact_mod_cast (by omega : 0<p)) (by norm_num)).mpr
    have hh : (2:ℝ)≤p := by exact_mod_cast hp
    linarith
  simpa only [inv_pow, div_eq_mul_inv] using
    genericLocalQuotient_error A (fun S => (-1:ℤ)^S.card)
      (fun S => (p:ℂ)⁻¹*primeMonomial p z S) (by positivity) hr hd.2.2.1 hd.2.2.2.1 hd.2.2.2.2
      (fun S _ => sign_zpow_cases S.card)
      (fun S hS => primeMonomial_scaled_norm (by omega) z S (hz S hS))

theorem norm_one_sub_zpow_sub {a b : ℂ} (ha : ‖a‖≤1/2) (hb : ‖b‖≤1/2)
    {σ : ℤ} (hσ : σ=1 ∨ σ= -1) :
    ‖(1-a)^σ-(1-b)^σ‖≤4*‖a-b‖ := by
  have hla := norm_one_sub_lower ha
  have hlb := norm_one_sub_lower hb
  have hna : 1-a≠0 := norm_pos_iff.mp (by linarith)
  have hnb : 1-b≠0 := norm_pos_iff.mp (by linarith)
  obtain rfl | rfl := hσ
  · simp only [zpow_one]
    have hid : (1-a)-(1-b)= -(a-b) := by ring
    rw [hid, norm_neg]
    nlinarith [norm_nonneg (a-b)]
  · simp only [zpow_neg_one]
    have hid : (1-a)⁻¹-(1-b)⁻¹=(a-b)/((1-a)*(1-b)) := by field_simp; ring
    rw [hid, norm_div, norm_mul]
    have hp : 1/4≤‖1-a‖*‖1-b‖ := by nlinarith
    apply (div_le_iff₀ (by positivity : 0<‖1-a‖*‖1-b‖)).mpr
    nlinarith [norm_nonneg (a-b)]

theorem prime_inv_le_half {p : ℕ} (hp : 2≤p) : (p:ℝ)⁻¹≤1/2 := by
  rw [inv_eq_one_div]
  apply (div_le_div_iff₀ (by exact_mod_cast (by omega : 0<p)) (by norm_num)).mpr
  have hh : (2:ℝ)≤p := by exact_mod_cast hp
  linarith

theorem norm_eulerP_le {ι : Type*} {p δ : ℕ} (hp : 2≤p) (hδ : δ≤1)
    (A : Finset (Finset ι)) (z : ι → ℂ) (hz : ∀ S∈A, ∀ i∈S, 0≤(z i).re) :
    ‖eulerP p δ A z‖ ≤ Real.exp (2*A.card*(p:ℝ)⁻¹) := by
  have hsum : ‖∑ S∈A, (-1:ℂ)^S.card*primeMonomial p z S‖≤A.card := by
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ _S∈A, (1:ℝ) := Finset.sum_le_sum fun S hS => by
        simpa only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
          using primeMonomial_norm_le (by omega) z S (hz S hS)
      _ = _ := by simp
  have hd := delta_bounds hp hδ
  have hn : ‖((p:ℂ)-δ)⁻¹‖≤2*(p:ℝ)⁻¹ := by
    rw [norm_inv, ← Complex.ofReal_natCast p, ← Complex.ofReal_natCast δ,
      ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd.1]
    exact hd.2.1
  calc
    _ ≤ 1+‖((p:ℂ)-δ)⁻¹‖*‖∑ S∈A, (-1:ℂ)^S.card*primeMonomial p z S‖ := by
      simpa only [eulerP, norm_one, norm_mul] using norm_add_le (1:ℂ)
        (((p:ℂ)-δ)⁻¹*(∑ S∈A, (-1:ℂ)^S.card*primeMonomial p z S))
    _ ≤ 1+(2*(p:ℝ)⁻¹)*A.card := by gcongr
    _ = 2*A.card*(p:ℝ)⁻¹+1 := by ring
    _ ≤ _ := Real.add_one_le_exp _

theorem norm_eulerT_le {ι : Type*} {p : ℕ} (hp : 2≤p)
    (B : Finset (Finset ι)) (z : ι → ℂ) (hz : ∀ S∈B, ∀ i∈S, 0≤(z i).re) :
    ‖∏ S∈B, (1-(p:ℂ)⁻¹*primeMonomial p z S)^((-1:ℤ)^S.card)‖ ≤
      Real.exp (2*B.card*(p:ℝ)⁻¹) := by
  have hb (S : Finset ι) (hS : S∈B) :
      ‖(1-(p:ℂ)⁻¹*primeMonomial p z S)^((-1:ℤ)^S.card)‖≤Real.exp (2*(p:ℝ)⁻¹) := by
    have hh := norm_one_sub_zpow_sub_one (prime_inv_le_half hp)
      (primeMonomial_scaled_norm (by omega) z S (hz S hS)) (sign_zpow_cases S.card)
    have hn := norm_sub_norm_le ((1-(p:ℂ)⁻¹*primeMonomial p z S)^((-1:ℤ)^S.card)) (1:ℂ)
    rw [norm_one] at hn
    exact (show _ ≤ 2*(p:ℝ)⁻¹+1 by linarith).trans (Real.add_one_le_exp _)
  calc
    _ ≤ ∏ _S∈B, Real.exp (2*(p:ℝ)⁻¹) := by
      rw [norm_prod]
      exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) hb
    _ = Real.exp (2*B.card*(p:ℝ)⁻¹) := by
      rw [← Real.exp_sum]
      congr 1
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring

theorem norm_eulerH_le {ι : Type*} {p δ : ℕ} (hp : 2≤p) (hδ : δ≤1)
    (A B : Finset (Finset ι)) (z : ι → ℂ) (hz : ∀ i, 0≤(z i).re) :
    ‖eulerH p δ A B z‖ ≤ Real.exp (2*(A.card+B.card)*(p:ℝ)⁻¹) := by
  rw [eulerH, norm_mul]
  calc
    _ ≤ Real.exp (2*A.card*(p:ℝ)⁻¹)*Real.exp (2*B.card*(p:ℝ)⁻¹) :=
      mul_le_mul (norm_eulerP_le hp hδ A z (fun _ _ i _ => hz i))
        (norm_eulerT_le hp B z (fun _ _ i _ => hz i)) (norm_nonneg _) (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem norm_eulerP_sub_zero_le {ι : Type*} [Fintype ι] {p δ : ℕ}
    (hp : 2≤p) (hδ : δ≤1) (A : Finset (Finset ι))
    (z : ι → ℂ) (hz : ∀ i, 0≤(z i).re) :
    ‖eulerP p δ A z-eulerP p δ A (fun _ => 0)‖ ≤
      2*A.card*(p:ℝ)⁻¹*Real.log p*(∑ i, ‖z i‖) := by
  classical
  have hlog : 0≤Real.log (p:ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1≤p))
  have hs (S : Finset ι) : ∑ i∈S, ‖z i‖≤∑ i, ‖z i‖ :=
    Finset.sum_le_univ_sum_of_nonneg (fun _ => norm_nonneg _)
  have he (S : Finset ι) : ‖primeMonomial p z S-1‖≤Real.log p*(∑ i, ‖z i‖) :=
    (primeMonomial_sub_one (by omega) z S (fun i _ => hz i)).trans (mul_le_mul_of_nonneg_left (hs S) hlog)
  have hd := delta_bounds hp hδ
  have hn : ‖((p:ℂ)-δ)⁻¹‖≤2*(p:ℝ)⁻¹ := by
    rw [norm_inv, ← Complex.ofReal_natCast p, ← Complex.ofReal_natCast δ,
      ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd.1]
    exact hd.2.1
  have hid : eulerP p δ A z-eulerP p δ A (fun _ => 0) =
      ((p:ℂ)-δ)⁻¹*∑ S∈A, (-1:ℂ)^S.card*(primeMonomial p z S-1) := by
    simp only [eulerP, primeMonomial_zero, mul_one, Finset.sum_sub_distrib, mul_sub]
    ring
  rw [hid, norm_mul]
  have hsum : ‖∑ S∈A, (-1:ℂ)^S.card*(primeMonomial p z S-1)‖≤
      A.card*(Real.log p*(∑ i, ‖z i‖)) := by
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ _S∈A, Real.log p*(∑ i, ‖z i‖) := Finset.sum_le_sum fun S _ => by
        simpa only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul] using he S
      _ = _ := by simp
  calc
    _ ≤ (2*(p:ℝ)⁻¹)*(A.card*(Real.log p*(∑ i, ‖z i‖))) := by gcongr
    _ = _ := by ring

theorem norm_eulerT_sub_zero_le {ι : Type*} [Fintype ι] {p : ℕ}
    (hp : 2≤p) (B : Finset (Finset ι)) (z : ι → ℂ) (hz : ∀ i, 0≤(z i).re) :
    ‖(∏ S∈B, (1-(p:ℂ)⁻¹*primeMonomial p z S)^((-1:ℤ)^S.card)) -
      (∏ S∈B, (1-(p:ℂ)⁻¹)^((-1:ℤ)^S.card))‖ ≤
      Real.exp (2*B.card*(p:ℝ)⁻¹)*(4*B.card*(p:ℝ)⁻¹*Real.log p*(∑ i, ‖z i‖)) := by
  classical
  have hlog : 0≤Real.log (p:ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1≤p))
  have hs (S : Finset ι) : ∑ i∈S, ‖z i‖≤∑ i, ‖z i‖ :=
    Finset.sum_le_univ_sum_of_nonneg (fun _ => norm_nonneg _)
  have he (S : Finset ι) : ‖primeMonomial p z S-1‖≤Real.log p*(∑ i, ‖z i‖) :=
    (primeMonomial_sub_one (by omega) z S (fun i _ => hz i)).trans (mul_le_mul_of_nonneg_left (hs S) hlog)
  have hbn (w : ι → ℂ) (hw : ∀ i, 0≤(w i).re) (S : Finset ι) :
      ‖(1-(p:ℂ)⁻¹*primeMonomial p w S)^((-1:ℤ)^S.card)‖≤Real.exp (2*(p:ℝ)⁻¹) := by
    have hh := norm_one_sub_zpow_sub_one (prime_inv_le_half hp)
      (primeMonomial_scaled_norm (by omega) w S (fun i _ => hw i)) (sign_zpow_cases S.card)
    have hn := norm_sub_norm_le ((1-(p:ℂ)⁻¹*primeMonomial p w S)^((-1:ℤ)^S.card)) (1:ℂ)
    rw [norm_one] at hn
    exact (show _ ≤ 2*(p:ℝ)⁻¹+1 by linarith).trans (Real.add_one_le_exp _)
  have hg (S : Finset ι) : ‖(1-(p:ℂ)⁻¹)^((-1:ℤ)^S.card)‖≤Real.exp (2*(p:ℝ)⁻¹) := by
    simpa only [primeMonomial_zero, mul_one] using hbn (fun _ => 0) (by simp) S
  have hd (S : Finset ι) :
      ‖(1-(p:ℂ)⁻¹*primeMonomial p z S)^((-1:ℤ)^S.card)-(1-(p:ℂ)⁻¹)^((-1:ℤ)^S.card)‖≤
        4*(p:ℝ)⁻¹*Real.log p*(∑ i, ‖z i‖) := by
    have ha := (primeMonomial_scaled_norm (by omega : 1≤p) z S (fun i _ => hz i)).trans (prime_inv_le_half hp)
    have hb : ‖(p:ℂ)⁻¹‖≤1/2 := by simpa only [norm_inv, Complex.norm_natCast] using prime_inv_le_half hp
    calc
      _ ≤ 4*‖(p:ℂ)⁻¹*primeMonomial p z S-(p:ℂ)⁻¹‖ := norm_one_sub_zpow_sub ha hb (sign_zpow_cases S.card)
      _ = 4*(p:ℝ)⁻¹*‖primeMonomial p z S-1‖ := by
        rw [← mul_sub_one, norm_mul, norm_inv, Complex.norm_natCast, mul_assoc]
      _ ≤ 4*(p:ℝ)⁻¹*(Real.log p*(∑ i, ‖z i‖)) := mul_le_mul_of_nonneg_left (he S) (by positivity)
      _ = _ := by ring
  have hh := norm_prod_sub_prod_le B
    (fun S => (1-(p:ℂ)⁻¹*primeMonomial p z S)^((-1:ℤ)^S.card))
    (fun S => (1-(p:ℂ)⁻¹)^((-1:ℤ)^S.card))
    (fun _ => Real.exp (2*(p:ℝ)⁻¹)) (fun _ => 4*(p:ℝ)⁻¹*Real.log p*(∑ i, ‖z i‖))
    (fun _ _ => Real.one_le_exp (by positivity)) (fun S _ => hbn z hz S)
    (fun S _ => hg S) (fun S _ => hd S)
  have ht : ∏ _S∈B, Real.exp (2*(p:ℝ)⁻¹)=Real.exp (2*B.card*(p:ℝ)⁻¹) := by
    rw [← Real.exp_sum]
    congr 1
    simp only [Finset.sum_const, nsmul_eq_mul]
    ring
  rw [ht] at hh
  convert hh using 1
  simp only [Finset.sum_const, nsmul_eq_mul]
  ring

theorem norm_eulerH_sub_zero_le {ι : Type*} [Fintype ι] {p δ : ℕ}
    (hp : 2≤p) (hδ : δ≤1) (A B : Finset (Finset ι))
    (z : ι → ℂ) (hz : ∀ i, 0≤(z i).re) :
    ‖eulerH p δ A B z-eulerH p δ A B (fun _ => 0)‖ ≤
      Real.exp (2*(A.card+B.card)*(p:ℝ)⁻¹)*
        ((2*A.card+4*B.card)*(p:ℝ)⁻¹*Real.log p*(∑ i, ‖z i‖)) := by
  let T := fun w : ι → ℂ => ∏ S∈B, (1-(p:ℂ)⁻¹*primeMonomial p w S)^((-1:ℤ)^S.card)
  have hT := norm_eulerT_le hp B z (fun _ _ i _ => hz i)
  have hdT : ‖T z-T (fun _ => 0)‖≤
      Real.exp (2*B.card*(p:ℝ)⁻¹)*(4*B.card*(p:ℝ)⁻¹*Real.log p*(∑ i, ‖z i‖)) := by
    simpa only [T, primeMonomial_zero, mul_one] using norm_eulerT_sub_zero_le hp B z hz
  have hp0 := norm_eulerP_le hp hδ A (fun _ => 0) (by simp)
  have hPd := norm_eulerP_sub_zero_le hp hδ A z hz
  have hlog : 0≤Real.log (p:ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1≤p))
  have hAe : 1≤Real.exp (2*A.card*(p:ℝ)⁻¹) := Real.one_le_exp (by positivity)
  have hid : eulerH p δ A B z-eulerH p δ A B (fun _ => 0) =
      (eulerP p δ A z-eulerP p δ A (fun _ => 0))*T z +
        eulerP p δ A (fun _ => 0)*(T z-T (fun _ => 0)) := by dsimp [eulerH, T]; ring
  rw [hid]
  calc
    _ ≤ ‖eulerP p δ A z-eulerP p δ A (fun _ => 0)‖*‖T z‖ +
        ‖eulerP p δ A (fun _ => 0)‖*‖T z-T (fun _ => 0)‖ := by
      simpa only [norm_mul] using norm_add_le
        ((eulerP p δ A z-eulerP p δ A (fun _ => 0))*T z)
        (eulerP p δ A (fun _ => 0)*(T z-T (fun _ => 0)))
    _ ≤ (2*A.card*(p:ℝ)⁻¹*Real.log p*(∑ i, ‖z i‖))*Real.exp (2*B.card*(p:ℝ)⁻¹)+
        Real.exp (2*A.card*(p:ℝ)⁻¹)*(Real.exp (2*B.card*(p:ℝ)⁻¹)*
          (4*B.card*(p:ℝ)⁻¹*Real.log p*(∑ i, ‖z i‖))) := by gcongr
    _ ≤ Real.exp (2*A.card*(p:ℝ)⁻¹)*
        ((2*A.card*(p:ℝ)⁻¹*Real.log p*(∑ i, ‖z i‖))*Real.exp (2*B.card*(p:ℝ)⁻¹))+
        Real.exp (2*A.card*(p:ℝ)⁻¹)*(Real.exp (2*B.card*(p:ℝ)⁻¹)*
          (4*B.card*(p:ℝ)⁻¹*Real.log p*(∑ i, ‖z i‖))) := by
      have hnn : 0 ≤ (2*(A.card:ℝ)*(p:ℝ)⁻¹*Real.log p*(∑ i, ‖z i‖))*Real.exp (2*B.card*(p:ℝ)⁻¹) := by positivity
      exact add_le_add (le_mul_of_one_le_left hnn hAe) le_rfl
    _ = _ := by
      rw [show 2*((A.card:ℝ)+B.card)*(p:ℝ)⁻¹=2*A.card*(p:ℝ)⁻¹+2*B.card*(p:ℝ)⁻¹ by ring,
        Real.exp_add]
      ring

end LargePrimeGaps

end OAI
end

section
-- module Solutions.OAIW2_P344.PrimeGaps_EulerProducts
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

open Asymptotics

open scoped Classical

theorem mem_fiberSubsetFamily {ι α : Type*} [Fintype ι] (b : ι → α)
    (R : Finset α) (S : Finset ι) :
    S∈fiberSubsetFamily b R ↔ S.Nonempty ∧ ∃ r∈R, ∀ i∈S, b i=r := by
  classical
  simp only [fiberSubsetFamily, Finset.mem_biUnion, mem_nonemptySubsets]
  constructor
  · rintro ⟨r,hr,hS,hsub⟩
    exact ⟨hS,r,hr,fun i hi => (Finset.mem_filter.mp (hsub hi)).2⟩
  · rintro ⟨hS,r,hr,hsub⟩
    exact ⟨r,hr,hS,fun i hi => Finset.mem_filter.mpr ⟨Finset.mem_univ _,hsub i hi⟩⟩

theorem disjoint_nonemptySubsets_fibers {ι α : Type*} [Fintype ι] (b : ι → α)
    {r s : α} (hrs : r≠s) :
    Disjoint (nonemptySubsets (Finset.univ.filter fun i => b i=r))
      (nonemptySubsets (Finset.univ.filter fun i => b i=s)) := by
  classical
  apply Finset.disjoint_left.mpr
  intro S hSr hSs
  rcases mem_nonemptySubsets.mp hSr with ⟨hS,hR⟩
  have hT := (mem_nonemptySubsets.mp hSs).2
  rcases hS with ⟨i,hi⟩
  exact hrs ((Finset.mem_filter.mp (hR hi)).2.symm.trans (Finset.mem_filter.mp (hT hi)).2)

theorem fiberSubsetFamily_sign_sum {ι α : Type*} [Fintype ι] (b : ι → α)
    (R : Finset α) (hR : ∀ r∈R, ∃ i, b i=r) :
    (∑ S∈fiberSubsetFamily b R, (-1:ℤ)^S.card) = -(R.card:ℤ) := by
  classical
  rw [fiberSubsetFamily, Finset.sum_biUnion]
  · have hs (r : α) (hr : r∈R) : (Finset.univ.filter fun i => b i=r).Nonempty := by
      rcases hR r hr with ⟨i,hi⟩
      exact ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩⟩
    calc
      _ = ∑ _r∈R, (-1:ℤ) := Finset.sum_congr rfl (fun r hr => sum_nonemptySubsets_sign (hs r hr))
      _ = _ := by simp
  · intro r _ s _ hrs
    exact disjoint_nonemptySubsets_fibers b hrs

theorem mem_fiberSubsetFamily_image {ι α : Type*} [Fintype ι] [DecidableEq α] (b : ι → α)
    (S : Finset ι) :
    S∈fiberSubsetFamily b (Finset.univ.image b) ↔
      S.Nonempty ∧ ∀ i∈S, ∀ j∈S, b i=b j := by
  classical
  rw [mem_fiberSubsetFamily]
  constructor
  · rintro ⟨hS,r,_,hb⟩
    exact ⟨hS,fun i hi j hj => (hb i hi).trans (hb j hj).symm⟩
  · rintro ⟨hS,hb⟩
    rcases hS with ⟨i,hi⟩
    exact ⟨⟨i,hi⟩,b i,Finset.mem_image_of_mem _ (Finset.mem_univ _),fun j hj => hb j hj i hi⟩

theorem eulerP_zero_fiber_family {ι α : Type*} [Fintype ι]
    (p δ : ℕ) (b : ι → α) (R : Finset α) (hR : ∀ r∈R, ∃ i, b i=r) :
    eulerP p δ (fiberSubsetFamily b R) (fun _ => 0) =
      1-((p:ℂ)-δ)⁻¹*(R.card:ℂ) := by
  have hs : (∑ S∈fiberSubsetFamily b R, (-1:ℂ)^S.card) = -(R.card:ℂ) := by
    exact_mod_cast fiberSubsetFamily_sign_sum b R hR
  simp only [eulerP, primeMonomial_zero, mul_one, hs]
  ring

theorem eulerH_zero_fiber_families {ι α β : Type*} [Fintype ι]
    (p δ : ℕ) (b : ι → α) (R : Finset α) (c : ι → β) (T : Finset β)
    (hR : ∀ r∈R, ∃ i, b i=r) (hT : ∀ t∈T, ∃ i, c i=t)
    (hp : 1-(p:ℂ)⁻¹≠0) :
    eulerH p δ (fiberSubsetFamily b R) (fiberSubsetFamily c T) (fun _ => 0) =
      (1-((p:ℂ)-δ)⁻¹*(R.card:ℂ))*(1-(p:ℂ)⁻¹)^(-(T.card:ℤ)) := by
  rw [eulerH, eulerP_zero_fiber_family p δ b R hR]
  simp only [primeMonomial_zero, mul_one]
  rw [prod_const_zpow _ _ hp, fiberSubsetFamily_sign_sum c T hT]

theorem residueFamily_eq_shiftFamily {ι : Type*} [Fintype ι] (b : ι → ℤ) (p : ℕ)
    (h : ∀ i j, b i%(p:ℤ)=b j%(p:ℤ) → b i=b j) : residueFamily b p=shiftFamily b := by
  apply Finset.ext
  intro S
  constructor
  · intro hs
    rcases (mem_fiberSubsetFamily_image (fun i => b i%(p:ℤ)) S).mp hs with ⟨hn,he⟩
    exact (mem_fiberSubsetFamily_image b S).mpr ⟨hn,fun i hi j hj => h i j (he i hi j hj)⟩
  · intro hs
    rcases (mem_fiberSubsetFamily_image b S).mp hs with ⟨hn,he⟩
    exact (mem_fiberSubsetFamily_image (fun i => b i%(p:ℤ)) S).mpr
      ⟨hn,fun i hi j hj => congrArg (fun a => a%(p:ℤ)) (he i hi j hj)⟩

theorem one_sub_prime_inv_ne_zero {p : ℕ} (hp : 2≤p) : 1-(p:ℂ)⁻¹≠0 := by
  have hpR : (2:ℝ)≤p := by exact_mod_cast hp
  have hr : 1-(p:ℝ)⁻¹≠0 := by
    have := (inv_lt_one₀ (by linarith : 0<(p:ℝ))).mpr (by linarith : 1<(p:ℝ))
    linarith
  have hc : ((1-(p:ℝ)⁻¹:ℝ):ℂ)≠0 := by exact_mod_cast hr
  simpa using hc

theorem eulerH_unmarked_zero {ι : Type*} [Fintype ι] (b : ι → ℤ) {p : ℕ} (hp : 2≤p) :
    eulerH p 0 (residueFamily b p) (shiftFamily b) (fun _ => 0) =
      (singularLocal (Finset.univ.image b) p : ℂ) := by
  rw [residueFamily, shiftFamily, eulerH_zero_fiber_families p 0 _ _ _ _
    (fun r hr => by rcases Finset.mem_image.mp hr with ⟨i,_,hi⟩; exact ⟨i,hi⟩)
    (fun r hr => by rcases Finset.mem_image.mp hr with ⟨i,_,hi⟩; exact ⟨i,hi⟩)
    (one_sub_prime_inv_ne_zero hp)]
  simp only [Nat.cast_zero, sub_zero, zpow_neg, zpow_natCast, singularLocal, residueCount,
    Finset.image_image, Function.comp_def]
  push_cast
  simp only [div_eq_mul_inv]
  ring

theorem multipliable_of_summable_norm_sub_one {ι : Type*} {f : ι → ℂ}
    (hf : Summable (fun i => ‖f i-1‖)) : Multipliable f := by
  simpa only [add_sub_cancel] using multipliable_one_add_of_summable hf

theorem norm_tprod_sub_one_le_exp {ι : Type*} {f : ι → ℂ}
    (hf : Summable (fun i => ‖f i-1‖)) :
    ‖(∏' i, f i)-1‖≤Real.exp (∑' i, ‖f i-1‖)-1 := by
  have hm := multipliable_of_summable_norm_sub_one hf
  apply le_of_tendsto ((hm.hasProd.sub_const 1).norm)
  filter_upwards [] with S
  calc
    _ ≤ Real.exp (∑ i∈S, ‖f i-1‖)-1 := by
      simpa only [add_sub_cancel] using Finset.norm_prod_one_add_sub_one_le S (fun i => f i-1)
    _ ≤ _ := sub_le_sub_right (Real.exp_le_exp.mpr (hf.sum_le_tsum S (fun _ _ => norm_nonneg _))) 1

theorem tprod_eq_prod_mul_tail {ι : Type*} (S : Finset ι) {f : ι → ℂ}
    (hf : Summable (fun i => ‖f i-1‖)) :
    (∏' i, f i) = (∏ i∈S, f i)*(∏' i : {i // i∉S}, f i) := by
  classical
  have hs := multipliable_of_summable_norm_sub_one (hf.subtype (fun i => i∈S))
  have ht := multipliable_of_summable_norm_sub_one (hf.subtype (fun i => i∉S))
  have hh := hs.tprod_mul_tprod_compl ht
  rw [Finset.tprod_subtype'] at hh
  exact hh.symm

theorem norm_tprod_sub_prod_le {ι : Type*} (S : Finset ι) {f : ι → ℂ}
    (hf : Summable (fun i => ‖f i-1‖)) :
    ‖(∏' i, f i)-(∏ i∈S, f i)‖ ≤
      ‖∏ i∈S, f i‖*(Real.exp (∑' i : {i // i∉S}, ‖f i-1‖)-1) := by
  rw [tprod_eq_prod_mul_tail S hf, ← mul_sub_one, norm_mul]
  exact mul_le_mul_of_nonneg_left
    (norm_tprod_sub_one_le_exp (hf.subtype (fun i => i∉S))) (norm_nonneg _)

theorem norm_tprod_sub_tprod_le {ι : Type*} (S : Finset ι) {f g : ι → ℂ}
    (hf : Summable (fun i => ‖f i-1‖)) (hg : Summable (fun i => ‖g i-1‖))
    (B e : ι → ℝ) (hB : ∀ i∈S, 1≤B i)
    (hfn : ∀ i∈S, ‖f i‖≤B i) (hgn : ∀ i∈S, ‖g i‖≤B i)
    (he : ∀ i∈S, ‖f i-g i‖≤e i) :
    ‖(∏' i, f i)-(∏' i, g i)‖ ≤ (∏ i∈S, B i)*
      ((∑ i∈S, e i)+(Real.exp (∑' i : {i // i∉S}, ‖f i-1‖)-1)+
        (Real.exp (∑' i : {i // i∉S}, ‖g i-1‖)-1)) := by
  have hpf : ‖∏ i∈S, f i‖≤∏ i∈S, B i := by
    rw [norm_prod]
    exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) hfn
  have hpg : ‖∏ i∈S, g i‖≤∏ i∈S, B i := by
    rw [norm_prod]
    exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) hgn
  have hdf := norm_tprod_sub_prod_le S hf
  have hdg := norm_tprod_sub_prod_le S hg
  have hp := norm_prod_sub_prod_le S f g B e hB hfn hgn he
  have hfp : 0≤Real.exp (∑' i : {i // i∉S}, ‖f i-1‖)-1 :=
    sub_nonneg.mpr (Real.one_le_exp (tsum_nonneg fun _ => norm_nonneg _))
  have hgp : 0≤Real.exp (∑' i : {i // i∉S}, ‖g i-1‖)-1 :=
    sub_nonneg.mpr (Real.one_le_exp (tsum_nonneg fun _ => norm_nonneg _))
  have htri := norm_sub_le_norm_sub_add_norm_sub (∏' i, f i) (∏ i∈S, f i) (∏' i, g i)
  have htri' := norm_sub_le_norm_sub_add_norm_sub (∏ i∈S, f i) (∏ i∈S, g i) (∏' i, g i)
  rw [norm_sub_rev (∏ i∈S, g i)] at htri'
  calc
    _ ≤ ‖(∏' i, f i)-(∏ i∈S, f i)‖+‖(∏ i∈S, f i)-(∏ i∈S, g i)‖+
        ‖(∏' i, g i)-(∏ i∈S, g i)‖ := by linarith
    _ ≤ (∏ i∈S, B i)*(Real.exp (∑' i : {i // i∉S}, ‖f i-1‖)-1)+
        (∏ i∈S, B i)*(∑ i∈S, e i)+
        (∏ i∈S, B i)*(Real.exp (∑' i : {i // i∉S}, ‖g i-1‖)-1) := by
      exact add_le_add (add_le_add (hdf.trans (mul_le_mul_of_nonneg_right hpf hfp)) hp)
        (hdg.trans (mul_le_mul_of_nonneg_right hpg hgp))
    _ = _ := by ring

theorem sum_reciprocal_sq_injective_le {ι : Type*} (S : Finset ι) (n : ι → ℕ)
    (hn : Function.Injective n) {y : ℕ} (hy : 0<y) (hl : ∀ i∈S, y<n i) :
    (∑ i∈S, (1:ℝ)/(n i:ℝ)^2) ≤ 1/(y:ℝ) := by
  classical
  rw [← Finset.sum_image (f := fun k : ℕ => (1:ℝ)/(k:ℝ)^2) (fun _ _ _ _ h => hn h)]
  apply sum_reciprocal_sq_le hy
  intro k hk
  rcases Finset.mem_image.mp hk with ⟨i,hi,rfl⟩
  exact hl i hi

theorem summable_tsum_le_of_reciprocal_sq {ι : Type*} (n : ι → ℕ)
    (hn : Function.Injective n) {y : ℕ} (hy : 0<y) (hl : ∀ i, y<n i)
    (f : ι → ℝ) {K : ℝ} (hK : 0≤K) (hf : ∀ i, 0≤f i)
    (hbound : ∀ i, f i≤K/(n i:ℝ)^2) :
    Summable f ∧ (∑' i, f i)≤K/(y:ℝ) := by
  have hh (S : Finset ι) : (∑ i∈S, f i)≤K/(y:ℝ) := by
    calc
      _ ≤ ∑ i∈S, K/(n i:ℝ)^2 := Finset.sum_le_sum fun i _ => hbound i
      _ = K*(∑ i∈S, (1:ℝ)/(n i:ℝ)^2) := by rw [Finset.mul_sum]; simp [div_eq_mul_inv]
      _ ≤ K*(1/(y:ℝ)) := mul_le_mul_of_nonneg_left
        (sum_reciprocal_sq_injective_le S n hn hy (fun i _ => hl i)) hK
      _ = _ := by ring
  exact ⟨summable_of_sum_le hf hh, Real.tsum_le_of_sum_le hf hh⟩

end LargePrimeGaps

end OAI
end

section
-- module Solutions.OAIW2_P344.PrimeGaps_FourierNormalization
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

open Asymptotics

open scoped Classical

section FourierNormalization

open scoped FourierTransform SchwartzMap

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

theorem radianFourier_inversion (G : SchwartzMap V ℂ) (v : V) :
    (∫ u : V, radianFourier G u * Complex.exp (-Complex.I*(inner ℝ u v : ℂ))) = G v := by
  let A : ℝ := 2*Real.pi
  have hA : 0<A := by dsimp [A]; positivity
  let f := fun u : V => (𝓕⁻ G) u * Complex.exp (-Complex.I*((A*inner ℝ u v : ℝ):ℂ))
  have hscale : (∫ u : V, f (A⁻¹ • u)) = A^Module.finrank ℝ V • ∫ u : V, f u := by
    simpa only [inv_pow, inv_inv] using Measure.integral_comp_smul_of_nonneg volume f A⁻¹ (hR:= (inv_pos.mpr hA).le)
  have hinv : (∫ u : V, f u) = G v := by
    have hh := congrArg (fun H : SchwartzMap V ℂ => H v) (FourierTransform.fourier_fourierInv_eq (F := SchwartzMap V ℂ) G)
    rw [SchwartzMap.fourier_coe, Real.fourier_eq'] at hh
    convert hh using 1
    apply integral_congr_ae
    filter_upwards [] with u
    dsimp only [f, A]
    rw [smul_eq_mul, mul_comm]
    congr 2
    push_cast
    ring_nf
  calc
    _ = ∫ u : V, (A^Module.finrank ℝ V)⁻¹ • f (A⁻¹ • u) := by
      apply integral_congr_ae
      filter_upwards [] with u
      simp only [radianFourier, smul_apply,
        SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
        frequencyDilation_apply]
      dsimp only [f, A]
      rw [real_inner_smul_left]
      have ht : 2*Real.pi*((2*Real.pi)⁻¹*inner ℝ u v) = inner ℝ u v := by field_simp
      rw [ht]
      simp only [Complex.real_smul, mul_assoc]
    _ = (A^Module.finrank ℝ V)⁻¹ • ∫ u : V, f (A⁻¹ • u) := integral_smul _ _
    _ = (A^Module.finrank ℝ V)⁻¹ • (A^Module.finrank ℝ V • G v) := by rw [hscale, hinv]
    _ = G v := by rw [smul_smul, inv_mul_cancel₀ (pow_ne_zero _ hA.ne'), one_smul]

theorem sourceFourier_inversion (ℓ : V →L[ℝ] ℝ) (F : V → ℂ)
    (hF : HasCompactSupport F) (hFs : ContDiff ℝ ∞ F) (v : V) :
    (∫ u : V, sourceFourier ℓ F hF hFs u *
      Complex.exp (-(ℓ v : ℂ)-Complex.I*(inner ℝ u v : ℂ))) = F v := by
  calc
    _ = Complex.exp (-(ℓ v : ℂ)) *
        ∫ u : V, sourceFourier ℓ F hF hFs u *
          Complex.exp (-Complex.I*(inner ℝ u v : ℂ)) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with u
      rw [sub_eq_add_neg, Complex.exp_add]
      ring_nf
    _ = Complex.exp (-(ℓ v : ℂ)) * (Complex.exp (ℓ v : ℂ)*F v) := by
      rw [sourceFourier, radianFourier_inversion, laplaceSchwartz_apply]
    _ = F v := by rw [← mul_assoc, ← Complex.exp_add]; simp

end FourierNormalization

theorem genericEulerConstant_nonneg (m : ℕ) : 0≤genericEulerConstant m := by
  unfold genericEulerConstant
  positivity

theorem eulerH_summable_error {ι : Type*} {δ : ℕ} (hδ : δ≤1)
    (A : ℕ → Finset (Finset ι)) (B : Finset (Finset ι))
    (z : ι → ℂ) (hz : ∀ i, 0≤(z i).re) {y : ℕ} (hy : 0<y)
    (hgen : ∀ p : Nat.Primes, y<(p:ℕ) → A p=B) :
    Summable (fun p : Nat.Primes => ‖eulerH p δ (A p) B z-1‖) := by
  apply (primePrefix y).summable_compl_iff.mp
  apply (summable_tsum_le_of_reciprocal_sq
    (fun p : {p : Nat.Primes // p∉primePrefix y} => (p.val:ℕ))
    (fun _ _ he => Subtype.ext (Subtype.ext he)) hy
    (fun p => by have := p.property; simp only [mem_primePrefix, not_le] at this; exact this)
    (fun p => ‖eulerH p.val δ (A p.val) B z-1‖)
    (genericEulerConstant_nonneg B.card) (fun _ => norm_nonneg _) ?_).1
  intro p
  have hp : y<(p.val:ℕ) := by
    have := p.property
    simpa only [mem_primePrefix, not_le] using this
  rw [hgen p.val hp]
  exact eulerH_generic_error p.val.property.two_le hδ B z (fun _ _ i _ => hz i)

theorem eulerH_tail_sum {ι : Type*} {δ : ℕ} (hδ : δ≤1)
    (A : ℕ → Finset (Finset ι)) (B : Finset (Finset ι))
    (z : ι → ℂ) (hz : ∀ i, 0≤(z i).re) {y : ℕ} (hy : 0<y)
    (hgen : ∀ p : Nat.Primes, y<(p:ℕ) → A p=B) :
    (∑' p : {p : Nat.Primes // p∉primePrefix y}, ‖eulerH p.val δ (A p.val) B z-1‖) ≤
      genericEulerConstant B.card/(y:ℝ) := by
  apply (summable_tsum_le_of_reciprocal_sq
    (fun p : {p : Nat.Primes // p∉primePrefix y} => (p.val:ℕ))
    (fun _ _ he => Subtype.ext (Subtype.ext he)) hy
    (fun p => by have := p.property; simp only [mem_primePrefix, not_le] at this; exact this)
    (fun p => ‖eulerH p.val δ (A p.val) B z-1‖)
    (genericEulerConstant_nonneg B.card) (fun _ => norm_nonneg _) ?_).2
  intro p
  have hp : y<(p.val:ℕ) := by
    have := p.property
    simpa only [mem_primePrefix, not_le] using this
  rw [hgen p.val hp]
  exact eulerH_generic_error p.val.property.two_le hδ B z (fun _ _ i _ => hz i)

theorem eulerGlobal_comparison {ι : Type*} [Fintype ι] {δ : ℕ} (hδ : δ≤1)
    (A : ℕ → Finset (Finset ι)) (B : Finset (Finset ι))
    (z : ι → ℂ) (hz : ∀ i, 0≤(z i).re) {y R : ℕ} (hy : 2≤y)
    (hA : ∀ p : Nat.Primes, (A p).card≤R) (hB : B.card≤R)
    (hgen : ∀ p : Nat.Primes, y<(p:ℕ) → A p=B) :
    ‖eulerGlobal δ A B z-eulerGlobal δ A B (fun _ => 0)‖ ≤
      Real.exp (4*R*primeReciprocalPrefix y)*
        (Real.exp (2*R)*6*R*Real.log y*(∑ i, ‖z i‖)*primeReciprocalPrefix y+
          2*(Real.exp (genericEulerConstant B.card/(y:ℝ))-1)) := by
  let Z : ℝ := ∑ i, ‖z i‖
  have hZ : 0≤Z := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hy0 : 0<y := by omega
  have hyR : (0:ℝ)<y := by exact_mod_cast hy0
  have hly : 0≤Real.log (y:ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1≤y))
  have hf := eulerH_summable_error hδ A B z hz hy0 hgen
  have hg := eulerH_summable_error hδ A B (fun _ => 0) (by simp) hy0 hgen
  let b : Nat.Primes → ℝ := fun p => Real.exp (4*R*(p:ℝ)⁻¹)
  let e : Nat.Primes → ℝ := fun p => Real.exp (2*R)*6*R*Real.log y*Z*(p:ℝ)⁻¹
  have hbn (p : Nat.Primes) : 1≤b p := Real.one_le_exp (by positivity)
  have hnorm (w : ι → ℂ) (hw : ∀ i, 0≤(w i).re) (p : Nat.Primes) :
      ‖eulerH p δ (A p) B w‖≤b p := by
    apply (norm_eulerH_le p.property.two_le hδ (A p) B w hw).trans
    apply Real.exp_le_exp.mpr
    have haR : ((A p).card:ℝ)≤R := by exact_mod_cast hA p
    have hbR : (B.card:ℝ)≤R := by exact_mod_cast hB
    have hp0 : 0≤(p:ℝ)⁻¹ := by positivity
    nlinarith
  have hd (p : Nat.Primes) (hp : p∈primePrefix y) :
      ‖eulerH p δ (A p) B z-eulerH p δ (A p) B (fun _ => 0)‖≤e p := by
    have haR : ((A p).card:ℝ)≤R := by exact_mod_cast hA p
    have hbR : (B.card:ℝ)≤R := by exact_mod_cast hB
    have hp0 : (0:ℝ)<p := by exact_mod_cast p.property.pos
    have hpl : 0≤Real.log (p:ℝ) := Real.log_nonneg (by exact_mod_cast p.property.one_le)
    have hpu : Real.log (p:ℝ)≤Real.log (y:ℝ) :=
      Real.log_le_log hp0 (by exact_mod_cast (mem_primePrefix y p).mp hp)
    have hp2 : (p:ℝ)⁻¹≤1/2 := prime_inv_le_half p.property.two_le
    have hpe : 2*((A p).card+B.card)*(p:ℝ)⁻¹≤2*R := by
      nlinarith [mul_nonneg (by positivity : (0:ℝ)≤R) (sub_nonneg.mpr hp2),
        mul_nonneg (show 0≤(p:ℝ)⁻¹ by positivity) (show (0:ℝ)≤2*R-((A p).card+B.card) by linarith)]
    have hpc : (2*(A p).card+4*B.card:ℝ)≤6*R := by linarith
    calc
      _ ≤ Real.exp (2*((A p).card+B.card)*(p:ℝ)⁻¹)*
          ((2*(A p).card+4*B.card)*(p:ℝ)⁻¹*Real.log p*Z) :=
        norm_eulerH_sub_zero_le p.property.two_le hδ (A p) B z hz
      _ ≤ Real.exp (2*R)*((6*R)*(p:ℝ)⁻¹*Real.log y*Z) := by gcongr
      _ = e p := by dsimp only [e]; ring
  have hh := norm_tprod_sub_tprod_le (primePrefix y) hf hg b e
    (fun p _ => hbn p) (fun p _ => hnorm z hz p)
    (fun p _ => hnorm (fun _ => 0) (by simp) p) hd
  have hbprod : (∏ p∈primePrefix y, b p) = Real.exp (4*R*primeReciprocalPrefix y) := by
    dsimp only [b, primeReciprocalPrefix]
    rw [← Real.exp_sum, Finset.mul_sum]
  have hesum : (∑ p∈primePrefix y, e p) =
      Real.exp (2*R)*6*R*Real.log y*Z*primeReciprocalPrefix y := by
    simp only [e, primeReciprocalPrefix, Finset.mul_sum]
  have htf := eulerH_tail_sum hδ A B z hz hy0 hgen
  have htg := eulerH_tail_sum hδ A B (fun _ => 0) (by simp) hy0 hgen
  rw [hbprod, hesum] at hh
  calc
    _ ≤ Real.exp (4*R*primeReciprocalPrefix y)*
        (Real.exp (2*R)*6*R*Real.log y*Z*primeReciprocalPrefix y+
          (Real.exp (genericEulerConstant B.card/(y:ℝ))-1)+
          (Real.exp (genericEulerConstant B.card/(y:ℝ))-1)) := by
      apply hh.trans
      gcongr
    _ = _ := by dsimp only [Z]; ring

theorem eq_of_emod_eq_of_bound {a b : ℤ} {D p : ℕ}
    (ha : a.natAbs≤D) (hb : b.natAbs≤D) (hp : 2*D<p)
    (hab : a%(p:ℤ)=b%(p:ℤ)) : a=b := by
  have hd : (p:ℤ)∣a-b := Int.dvd_of_emod_eq_zero
    (Int.emod_eq_emod_iff_emod_sub_eq_zero.mp hab)
  have hdN : p∣(a-b).natAbs := by
    simpa only [Int.natAbs_natCast] using Int.natAbs_dvd_natAbs.mpr hd
  have hlt : (a-b).natAbs<p := by have := Int.natAbs_sub_le a b; omega
  exact sub_eq_zero.mp (Int.natAbs_eq_zero.mp (Nat.eq_zero_of_dvd_of_lt hdN hlt))

theorem residueFamily_generic_of_bound {ι : Type*} [Fintype ι] (b : ι → ℤ)
    {D p : ℕ} (hb : ∀ i, (b i).natAbs≤D) (hp : 2*D<p) :
    residueFamily b p=shiftFamily b :=
  residueFamily_eq_shiftFamily b p (fun i j he => eq_of_emod_eq_of_bound (hb i) (hb j) hp he)

theorem subsetFamily_card_le {ι : Type*} [Fintype ι] (S : Finset (Finset ι)) :
    S.card≤2^Fintype.card ι := by
  classical
  simpa only [Fintype.card_finset] using Finset.card_le_univ S

theorem singularSeries_cast_hasProd (H : Finset ℤ) :
    HasProd (fun p : Nat.Primes => (singularLocal H p : ℂ)) (singularSeries H : ℂ) := by
  exact (singularSeries_multipliable H).hasProd.map Complex.ofRealHom.toMonoidHom
    Complex.continuous_ofReal

theorem unmarked_eulerGlobal_zero {ι : Type*} [Fintype ι] (b : ι → ℤ) :
    eulerGlobal 0 (residueFamily b) (shiftFamily b) (fun _ => 0) =
      (singularSeries (Finset.univ.image b) : ℂ) := by
  rw [eulerGlobal]
  exact ((singularSeries_cast_hasProd _).congr_fun fun p =>
    eulerH_unmarked_zero b p.property.two_le).tprod_eq

theorem primeMonomial_cpow {ι : Type*} {p : ℕ} (hp : 0<p)
    (z : ι → ℂ) (S : Finset ι) :
    (p:ℂ)^(-(1+∑ i∈S, z i)) = (p:ℂ)⁻¹*primeMonomial p z S := by
  have hp0 : (p:ℂ)≠0 := by exact_mod_cast hp.ne'
  rw [Complex.cpow_def_of_ne_zero hp0, ← Complex.natCast_log]
  rw [show (Real.log p : ℂ)*(-(1+∑ i∈S, z i)) =
    -(Real.log p : ℂ)+(-(Real.log p : ℂ)*(∑ i∈S, z i)) by ring,
    Complex.exp_add, Complex.exp_neg, Complex.natCast_log, Complex.exp_log hp0]
  simp only [primeMonomial, Complex.natCast_log]

theorem eulerZetaProduct_hasProd {ι : Type*} (B : Finset (Finset ι)) (z : ι → ℂ)
    (hB : ∀ S∈B, S.Nonempty) (hz : ∀ i, 0<(z i).re) :
    HasProd (fun p : Nat.Primes =>
      ∏ S∈B, (1-(p:ℂ)⁻¹*primeMonomial p z S)^(-((-1:ℤ)^S.card)))
      (eulerZetaProduct B z) := by
  apply hasProd_prod
  intro S hS
  have hs : 1<(1+∑ i∈S, z i).re := by
    simp only [Complex.add_re, Complex.one_re, Complex.re_sum]
    exact lt_add_of_pos_right _ (Finset.sum_pos (fun i _ => hz i) (hB S hS))
  have he := riemannZeta_eulerProduct_hasProd hs
  have hc (p : Nat.Primes) : (p:ℂ)^(-(1+∑ i∈S, z i)) =
      (p:ℂ)⁻¹*primeMonomial p z S := primeMonomial_cpow p.property.pos z S
  rcases sign_zpow_cases S.card with hp | hn
  · simpa only [hp, zpow_neg_one, zpow_one, hc] using he
  · have he' := he.inv₀ (riemannZeta_ne_zero_of_one_lt_re hs)
    simpa only [hn, neg_neg, zpow_one, zpow_neg_one, inv_inv, hc] using he'

theorem local_zeta_factor_ne_zero {ι : Type*} {p : ℕ} (hp : 2≤p)
    (z : ι → ℂ) (S : Finset ι) (hz : ∀ i∈S, 0≤(z i).re) :
    1-(p:ℂ)⁻¹*primeMonomial p z S ≠ 0 := by
  have hpR : (1:ℝ)<p := by exact_mod_cast (by omega : 1<p)
  have hb := (primeMonomial_scaled_norm (by omega) z S hz).trans_lt
    ((inv_lt_one₀ (by positivity : (0:ℝ)<p)).mpr hpR)
  intro he
  rw [← sub_eq_zero.mp he, norm_one] at hb
  exact hb.false

theorem eulerP_eq_eulerH_mul {ι : Type*} {p : ℕ} (hp : 2≤p) (δ : ℕ)
    (A B : Finset (Finset ι)) (z : ι → ℂ) (hz : ∀ i, 0≤(z i).re) :
    eulerP p δ A z = eulerH p δ A B z *
      ∏ S∈B, (1-(p:ℂ)⁻¹*primeMonomial p z S)^(-((-1:ℤ)^S.card)) := by
  rw [eulerH, mul_assoc, ← Finset.prod_mul_distrib]
  have he : (∏ S∈B, (1-(p:ℂ)⁻¹*primeMonomial p z S)^((-1:ℤ)^S.card) *
      (1-(p:ℂ)⁻¹*primeMonomial p z S)^(-((-1:ℤ)^S.card))) = 1 := by
    apply Finset.prod_eq_one
    intro S _
    rw [← zpow_add₀ (local_zeta_factor_ne_zero hp z S (fun i _ => hz i)), add_neg_cancel,
      zpow_zero]
  rw [he, mul_one]

theorem eulerP_hasProd {ι : Type*} (δ : ℕ)
    (A : ℕ → Finset (Finset ι)) (B : Finset (Finset ι)) (z : ι → ℂ)
    (hB : ∀ S∈B, S.Nonempty) (hz : ∀ i, 0<(z i).re) {H : ℂ}
    (hH : HasProd (fun p : Nat.Primes => eulerH p δ (A p) B z) H) :
    HasProd (fun p : Nat.Primes => eulerP p δ (A p) z) (H*eulerZetaProduct B z) := by
  exact (hH.mul (eulerZetaProduct_hasProd B z hB hz)).congr_fun fun p =>
    eulerP_eq_eulerH_mul p.property.two_le δ (A p) B z (fun i => (hz i).le)

theorem eulerChoiceNorm_nonneg {κ : Type*} [DecidableEq κ] {A : κ → Type*} [∀ p, Fintype (A p)]
    (w : (p : κ) → A p → ℂ) (p : κ) : 0≤eulerChoiceNorm w p :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem eulerChoice_sum_norm {κ : Type*} [DecidableEq κ] {A : κ → Type*} [∀ p, Fintype (A p)]
    (w : (p : κ) → A p → ℂ) (P : Finset κ) :
    (∑ c : (p : P) → A p, ‖eulerChoiceTerm w ⟨P,c⟩‖) = ∏ p∈P, eulerChoiceNorm w p := by
  classical
  simp only [eulerChoiceTerm, norm_prod, eulerChoiceNorm]
  rw [← Fintype.prod_sum (fun (p : P) (a : A p) => ‖w p a‖)]
  exact Finset.prod_coe_sort P (fun p => ∑ a, ‖w p a‖)

theorem eulerChoice_sum {κ : Type*} [DecidableEq κ] {A : κ → Type*} [∀ p, Fintype (A p)]
    (w : (p : κ) → A p → ℂ) (P : Finset κ) :
    (∑ c : (p : P) → A p, eulerChoiceTerm w ⟨P,c⟩) = ∏ p∈P, ∑ a, w p a := by
  classical
  simp only [eulerChoiceTerm]
  rw [← Fintype.prod_sum (fun (p : P) (a : A p) => w p a)]
  exact Finset.prod_coe_sort P (fun p => ∑ a, w p a)

theorem eulerChoice_summable_norm {κ : Type*} [DecidableEq κ] {A : κ → Type*} [∀ p, Fintype (A p)]
    (w : (p : κ) → A p → ℂ) (hw : Summable (eulerChoiceNorm w)) :
    Summable (fun c : EulerChoices A => ‖eulerChoiceTerm w c‖) := by
  classical
  apply (summable_sigma_of_nonneg (fun _ => norm_nonneg _)).mpr
  refine ⟨fun _ => (hasSum_fintype _).summable, ?_⟩
  simp_rw [tsum_fintype, eulerChoice_sum_norm]
  exact summable_finsetProd_of_summable_nonneg (eulerChoiceNorm_nonneg w) hw

theorem eulerChoices_hasProd {κ : Type*} [DecidableEq κ] {A : κ → Type*} [∀ p, Fintype (A p)]
    (w : (p : κ) → A p → ℂ) (hw : Summable (eulerChoiceNorm w)) :
    HasProd (fun p => 1+∑ a, w p a) (∑' c : EulerChoices A, eulerChoiceTerm w c) := by
  classical
  have hs := (eulerChoice_summable_norm w hw).of_norm
  apply hasProd_one_add_of_hasSum_prod
  exact hs.hasSum.sigma fun P => by
    simpa only [eulerChoice_sum] using
      hasSum_fintype (fun c : (p : P) → A p => eulerChoiceTerm w ⟨P,c⟩)

end LargePrimeGaps

end OAI
end

section
-- module Solutions.OAIW2_P344.PrimeGaps_EulerChoices
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

open Asymptotics

open scoped Classical

theorem eulerChoices_norm_tsum_le {κ : Type*} [DecidableEq κ] {A : κ → Type*} [∀ p, Fintype (A p)]
    (w : (p : κ) → A p → ℂ) (hw : Summable (eulerChoiceNorm w)) :
    (∑' c : EulerChoices A, ‖eulerChoiceTerm w c‖) ≤ Real.exp (∑' p, eulerChoiceNorm w p) := by
  classical
  have hc := eulerChoice_summable_norm w hw
  rw [hc.tsum_sigma]
  simp_rw [tsum_fintype, eulerChoice_sum_norm]
  have hs := summable_finsetProd_of_summable_nonneg (eulerChoiceNorm_nonneg w) hw
  apply hs.tsum_le_of_sum_le
  intro T
  calc
    _ ≤ ∑ s∈(T.biUnion id).powerset, ∏ p∈s, eulerChoiceNorm w p :=
      Finset.sum_le_sum_of_subset_of_nonneg (fun s hs => Finset.mem_powerset.mpr
        (Finset.subset_biUnion_of_mem id hs))
        (fun s _ _ => Finset.prod_nonneg fun _ _ => eulerChoiceNorm_nonneg w _)
    _ = ∏ p∈T.biUnion id, (1+eulerChoiceNorm w p) := (Finset.prod_one_add _).symm
    _ ≤ Real.exp (∑ p∈T.biUnion id, eulerChoiceNorm w p) :=
      Real.prod_one_add_le_exp_sum _ (eulerChoiceNorm_nonneg w)
    _ ≤ _ := Real.exp_le_exp.mpr (hw.sum_le_tsum _ fun p _ => eulerChoiceNorm_nonneg w p)

theorem primeMonomial_norm_le_rpow {ι : Type*} {p : ℕ} (hp : 1≤p)
    (z : ι → ℂ) (S : Finset ι) (hS : S.Nonempty) {ε : ℝ} (hε : 0≤ε)
    (hz : ∀ i∈S, ε≤(z i).re) :
    ‖primeMonomial p z S‖ ≤ (p:ℝ)^(-ε) := by
  have hpR : (0:ℝ)<p := by exact_mod_cast (by omega : 0<p)
  have hl : 0≤Real.log (p:ℝ) := Real.log_nonneg (by exact_mod_cast hp)
  obtain ⟨i,hi⟩ := hS
  have hs : ε≤∑ j∈S, (z j).re := (hz i hi).trans
    (Finset.single_le_sum (fun j hj => hε.trans (hz j hj)) hi)
  rw [primeMonomial, Complex.norm_exp, Real.rpow_def_of_pos hpR]
  apply Real.exp_le_exp.mpr
  simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.neg_im,
    Complex.ofReal_im, neg_zero, zero_mul, sub_zero, Complex.re_sum]
  nlinarith

theorem primeChoiceWeight_norm_bound {ι : Type*} {δ : ℕ} (hδ : δ≤1)
    (z : ι → ℂ) (p : Nat.Primes) (S : Finset ι) (hS : S.Nonempty)
    {ε : ℝ} (hε : 0≤ε) (hz : ∀ i∈S, ε≤(z i).re) :
    ‖primeChoiceWeight δ z p S‖ ≤ 2/(p:ℝ)^(1+ε) := by
  have hd := delta_bounds p.property.two_le hδ
  have he' : ‖(p:ℂ)-δ‖ = (p:ℝ)-δ := by
    have h := Complex.norm_of_nonneg hd.1.le
    simpa using h
  have hp0 : (0:ℝ)<p := by exact_mod_cast p.property.pos
  calc
    _ = ((p:ℝ)-δ)⁻¹*‖primeMonomial p z S‖ := by
      simp only [primeChoiceWeight, norm_mul, norm_inv, he', norm_pow, norm_neg,
        norm_one, one_pow, one_mul]
    _ ≤ (2*(p:ℝ)⁻¹)*(p:ℝ)^(-ε) :=
      mul_le_mul hd.2.1 (primeMonomial_norm_le_rpow p.property.one_le z S hS hε hz)
        (norm_nonneg _) (by positivity)
    _ = _ := by rw [Real.rpow_neg hp0.le, Real.rpow_add hp0, Real.rpow_one]; field_simp

theorem prime_power_tsum_le_log_zeta {s : ℝ} (hs : 1<s) :
    (∑' p : Nat.Primes, 1/(p:ℝ)^s) ≤ Real.log (riemannZeta (s:ℂ)).re := by
  have hsum : Summable (fun n : ℕ => ArithmeticFunction.vonMangoldt n / ((n:ℝ)^s*Real.log n)) :=
    (Real.summable_one_div_nat_rpow.mpr hs).of_nonneg_of_le
      (mangoldt_log_term_nonneg s) (mangoldt_log_term_le s)
  have hprime := (Real.summable_one_div_nat_rpow.mpr hs).comp_injective
    (fun p q : Nat.Primes => Subtype.ext)
  have he (p : Nat.Primes) :
      ArithmeticFunction.vonMangoldt (p:ℕ)/((p:ℝ)^s*Real.log (p:ℝ)) = 1/(p:ℝ)^s := by
    have hl : Real.log (p:ℝ)≠0 := (Real.log_pos (by exact_mod_cast p.property.one_lt)).ne'
    rw [ArithmeticFunction.vonMangoldt_apply_prime p.property]
    field_simp
  rw [log_riemannZeta_eq hs]
  apply hprime.tsum_le_tsum_of_inj (fun p : Nat.Primes => (p:ℕ)) (fun _ _ => Subtype.ext)
    (fun n _ => mangoldt_log_term_nonneg s n) (fun p => (he p).symm.le) hsum

theorem primeAllowedWeight_norm_le {ι : Type*} {δ R : ℕ} (hδ : δ≤1)
    (A : ℕ → Finset (Finset ι)) (z : ι → ℂ) {ε : ℝ} (hε : 0≤ε)
    (hA : ∀ p : Nat.Primes, ∀ S∈A p, S.Nonempty)
    (hR : ∀ p : Nat.Primes, (A p).card≤R) (hz : ∀ i, ε≤(z i).re) (p : Nat.Primes) :
    eulerChoiceNorm (primeAllowedWeight δ A z) p ≤ (2*R)/(p:ℝ)^(1+ε) := by
  classical
  have hb : ∀ S : {S // S∈A p}, ‖primeAllowedWeight δ A z p S‖ ≤ 2/(p:ℝ)^(1+ε) :=
    fun S => primeChoiceWeight_norm_bound hδ z p S (hA p S S.property) hε (fun _ _ => hz _)
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun S _ => hb S)
  have hs : ((A p).card:ℝ) ≤ R := by exact_mod_cast hR p
  simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_coe] at hh
  exact hh.trans (by calc
    _ ≤ (R:ℝ)*(2/(p:ℝ)^(1+ε)) := mul_le_mul_of_nonneg_right hs (by positivity)
    _ = _ := by ring)

theorem primeAllowedWeight_summable_norm {ι : Type*} {δ R : ℕ} (hδ : δ≤1)
    (A : ℕ → Finset (Finset ι)) (z : ι → ℂ) {ε : ℝ} (hε : 0<ε)
    (hA : ∀ p : Nat.Primes, ∀ S∈A p, S.Nonempty)
    (hR : ∀ p : Nat.Primes, (A p).card≤R) (hz : ∀ i, ε≤(z i).re) :
    Summable (eulerChoiceNorm (primeAllowedWeight δ A z)) := by
  have hs := (Real.summable_one_div_nat_rpow.mpr (by linarith : 1<1+ε)).comp_injective
    (fun p q : Nat.Primes => Subtype.ext)
  have hs' : Summable (fun p : Nat.Primes => (2*R)/(p:ℝ)^(1+ε)) := by
    simpa only [Function.comp_def, mul_one_div] using hs.mul_left (2*R:ℝ)
  exact hs'.of_nonneg_of_le (eulerChoiceNorm_nonneg _) (primeAllowedWeight_norm_le hδ A z
    hε.le hA hR hz)

theorem primeEulerChoices_hasProd {ι : Type*} {δ R : ℕ} (hδ : δ≤1)
    (A : ℕ → Finset (Finset ι)) (z : ι → ℂ) {ε : ℝ} (hε : 0<ε)
    (hA : ∀ p : Nat.Primes, ∀ S∈A p, S.Nonempty)
    (hR : ∀ p : Nat.Primes, (A p).card≤R) (hz : ∀ i, ε≤(z i).re) :
    HasProd (fun p : Nat.Primes => eulerP p δ (A p) z)
      (∑' c : EulerChoices (fun p : Nat.Primes => {S // S∈A p}),
        eulerChoiceTerm (primeAllowedWeight δ A z) c) := by
  apply (eulerChoices_hasProd _ (primeAllowedWeight_summable_norm hδ A z hε hA hR hz)).congr_fun
  intro p
  simp only [eulerP, primeAllowedWeight, primeChoiceWeight, ← Finset.mul_sum,
    ]
  congr 2
  exact (Finset.sum_coe_sort (A p) (fun S => (-1:ℂ)^S.card*primeMonomial p z S)).symm

theorem primeEulerChoices_norm_tsum_le {ι : Type*} {δ R : ℕ} (hδ : δ≤1)
    (A : ℕ → Finset (Finset ι)) (z : ι → ℂ) {ε : ℝ} (hε : 0<ε)
    (hA : ∀ p : Nat.Primes, ∀ S∈A p, S.Nonempty)
    (hR : ∀ p : Nat.Primes, (A p).card≤R) (hz : ∀ i, ε≤(z i).re) :
    (∑' c : EulerChoices (fun p : Nat.Primes => {S // S∈A p}),
        ‖eulerChoiceTerm (primeAllowedWeight δ A z) c‖) ≤
      Real.exp ((2*R)*Real.log (riemannZeta ((1+ε:ℝ):ℂ)).re) := by
  have hsum := primeAllowedWeight_summable_norm hδ A z hε hA hR hz
  refine (eulerChoices_norm_tsum_le _ hsum).trans (Real.exp_le_exp.mpr ?_)
  have hs := (Real.summable_one_div_nat_rpow.mpr (by linarith : 1<1+ε)).comp_injective
    (fun p q : Nat.Primes => Subtype.ext)
  have hs' : Summable (fun p : Nat.Primes => (2*R)/(p:ℝ)^(1+ε)) := by
    simpa only [Function.comp_def, mul_one_div] using hs.mul_left (2*R:ℝ)
  calc
    _ ≤ ∑' p : Nat.Primes, (2*R)/(p:ℝ)^(1+ε) :=
      hsum.tsum_le_tsum (primeAllowedWeight_norm_le hδ A z hε.le hA hR hz) hs'
    _ = (2*R:ℝ)*(∑' p : Nat.Primes, 1/(p:ℝ)^(1+ε)) := by
      simp only [← tsum_mul_left, mul_one_div]
    _ ≤ _ := mul_le_mul_of_nonneg_left (prime_power_tsum_le_log_zeta (by linarith)) (by positivity)

theorem choice_primeSupport {ι : Type*} [Fintype ι] {A : ℕ → Finset (Finset ι)}
    (hA : ∀ p : Nat.Primes, ∀ S∈A p, S.Nonempty)
    (c : EulerChoices (fun p : Nat.Primes => {S // S∈A p})) :
    tuplePrimeSupport (choiceDivisors c) = c.1 := by
  classical
  ext p
  rw [← tuplePrimeSubset_nonempty_iff _ (fun i => (choiceDivisors_squarefree c i).ne_zero),
    choice_primeSubset]
  by_cases hp : p∈c.1
  · simp only [hp, iff_true, choiceSubset_of_mem c hp]
    exact hA p _ (c.2 ⟨p,hp⟩).property
  · simp [hp]

theorem choice_double_prod {ι : Type*} [Fintype ι] {A : ℕ → Finset (Finset ι)}
    {M : Type*} [CommMonoid M]
    (c : EulerChoices (fun p : Nat.Primes => {S // S∈A p})) (f : Nat.Primes → ι → M) :
    (∏ i, ∏ p∈c.1.filter (fun p => i∈choiceSubset c p), f p i) =
      ∏ p∈c.1, ∏ i∈choiceSubset c p, f p i := by
  classical
  simp_rw [Finset.prod_filter]
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro p _
  rw [← Finset.prod_filter]
  congr 1
  ext i
  simp

theorem moebius_choiceDivisors {ι : Type*} {A : ℕ → Finset (Finset ι)}
    (c : EulerChoices (fun p : Nat.Primes => {S // S∈A p})) (i : ι) :
    ArithmeticFunction.moebius (choiceDivisors c i) =
      ∏ _p∈c.1.filter (fun p => i∈choiceSubset c p), (-1:ℤ) := by
  classical
  unfold choiceDivisors
  rw [ArithmeticFunction.IsMultiplicative.map_prod (fun p : Nat.Primes => (p:ℕ))
    ArithmeticFunction.isMultiplicative_moebius _ (fun p _ q _ hpq =>
      (Nat.coprime_primes p.property q.property).mpr (fun h => hpq (Subtype.ext h)))]
  apply Finset.prod_congr rfl
  intro p _
  exact ArithmeticFunction.moebius_apply_prime p.property

theorem moebius_choiceDivisors_prod {ι : Type*} [Fintype ι] {A : ℕ → Finset (Finset ι)}
    (c : EulerChoices (fun p : Nat.Primes => {S // S∈A p})) :
    (∏ i, ArithmeticFunction.moebius (choiceDivisors c i)) =
      ∏ p∈c.1, (-1:ℤ)^(choiceSubset c p).card := by
  classical
  simp_rw [moebius_choiceDivisors]
  rw [choice_double_prod c (fun _ _ => (-1:ℤ))]
  simp only [Finset.prod_const]

theorem choiceDivisors_log {ι : Type*} {A : ℕ → Finset (Finset ι)}
    (c : EulerChoices (fun p : Nat.Primes => {S // S∈A p})) (i : ι) :
    Real.log (choiceDivisors c i) =
      ∑ p∈c.1.filter (fun p => i∈choiceSubset c p), Real.log (p:ℕ) := by
  classical
  rw [choiceDivisors, Nat.cast_prod]
  exact Real.log_prod (fun p _ => by exact_mod_cast p.property.ne_zero)

theorem primeMonomial_as_product {ι : Type*} (p : ℕ) (z : ι → ℂ) (S : Finset ι) :
    primeMonomial p z S = ∏ i∈S, Complex.exp (-(Real.log p : ℂ)*z i) := by
  rw [primeMonomial, Finset.mul_sum, Complex.exp_sum]

theorem choiceMonomial_prod {ι : Type*} [Fintype ι] {A : ℕ → Finset (Finset ι)}
    (c : EulerChoices (fun p : Nat.Primes => {S // S∈A p})) (z : ι → ℂ) :
    (∏ p∈c.1, primeMonomial p z (choiceSubset c p)) =
      Complex.exp (-∑ i, (Real.log (choiceDivisors c i) : ℂ)*z i) := by
  classical
  simp_rw [primeMonomial_as_product]
  rw [← choice_double_prod c (fun p i => Complex.exp (-(Real.log (p:ℕ) : ℂ)*z i)),
    ← Finset.sum_neg_distrib, Complex.exp_sum]
  apply Finset.prod_congr rfl
  intro i _
  rw [← Complex.exp_sum, choiceDivisors_log, Complex.ofReal_sum]
  congr 1
  simp only [Finset.sum_mul, ← Finset.sum_neg_distrib, neg_mul]

theorem choiceTerm_eq_tupleFourierCoefficient {ι : Type*} [Fintype ι]
    {A : ℕ → Finset (Finset ι)} (hA : ∀ p : Nat.Primes, ∀ S∈A p, S.Nonempty)
    (δ : ℕ) (c : EulerChoices (fun p : Nat.Primes => {S // S∈A p})) (z : ι → ℂ) :
    eulerChoiceTerm (primeAllowedWeight δ A z) c =
      tupleFourierCoefficient δ (choiceDivisors c) z := by
  classical
  have hcast : (∏ i, (ArithmeticFunction.moebius (choiceDivisors c i):ℂ)) =
      ∏ p∈c.1, (-1:ℂ)^(choiceSubset c p).card := by
    exact_mod_cast moebius_choiceDivisors_prod c
  rw [tupleFourierCoefficient, tuplePrimeDensity, choice_primeSupport hA c, hcast,
    ← choiceMonomial_prod c z, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  unfold eulerChoiceTerm primeAllowedWeight primeChoiceWeight
  rw [← Finset.prod_coe_sort c.1]
  apply Finset.prod_congr rfl
  intro p _
  rw [← choiceSubset_of_mem c p.property]
  ring

theorem tupleFourier_summable_norm {ι : Type*} [Fintype ι] {δ R : ℕ} (hδ : δ≤1)
    (A : ℕ → Finset (Finset ι)) (z : ι → ℂ) {ε : ℝ} (hε : 0<ε)
    (hA : ∀ p : Nat.Primes, ∀ S∈A p, S.Nonempty)
    (hR : ∀ p : Nat.Primes, (A p).card≤R) (hz : ∀ i, ε≤(z i).re) :
    Summable (fun d : AllowedDivisorTuple A => ‖tupleFourierCoefficient δ d.val z‖) := by
  apply (primeChoicesEquivTuple A hA).summable_iff.mp
  change Summable (fun c => ‖tupleFourierCoefficient δ (choiceDivisors c) z‖)
  simp_rw [← choiceTerm_eq_tupleFourierCoefficient hA δ]
  exact eulerChoice_summable_norm _ (primeAllowedWeight_summable_norm hδ A z hε hA hR hz)

theorem tupleFourier_hasProd {ι : Type*} [Fintype ι] {δ R : ℕ} (hδ : δ≤1)
    (A : ℕ → Finset (Finset ι)) (z : ι → ℂ) {ε : ℝ} (hε : 0<ε)
    (hA : ∀ p : Nat.Primes, ∀ S∈A p, S.Nonempty)
    (hR : ∀ p : Nat.Primes, (A p).card≤R) (hz : ∀ i, ε≤(z i).re) :
    HasProd (fun p : Nat.Primes => eulerP p δ (A p) z)
      (∑' d : AllowedDivisorTuple A, tupleFourierCoefficient δ d.val z) := by
  rw [← (primeChoicesEquivTuple A hA).tsum_eq
    (fun d => tupleFourierCoefficient δ d.val z)]
  change HasProd _ (∑' c, tupleFourierCoefficient δ (choiceDivisors c) z)
  simp_rw [← choiceTerm_eq_tupleFourierCoefficient hA δ]
  exact primeEulerChoices_hasProd hδ A z hε hA hR hz

theorem tupleFourier_norm_tsum_le {ι : Type*} [Fintype ι] {δ R : ℕ} (hδ : δ≤1)
    (A : ℕ → Finset (Finset ι)) (z : ι → ℂ) {ε : ℝ} (hε : 0<ε)
    (hA : ∀ p : Nat.Primes, ∀ S∈A p, S.Nonempty)
    (hR : ∀ p : Nat.Primes, (A p).card≤R) (hz : ∀ i, ε≤(z i).re) :
    (∑' d : AllowedDivisorTuple A, ‖tupleFourierCoefficient δ d.val z‖) ≤
      Real.exp ((2*R)*Real.log (riemannZeta ((1+ε:ℝ):ℂ)).re) := by
  rw [← (primeChoicesEquivTuple A hA).tsum_eq
    (fun d => ‖tupleFourierCoefficient δ d.val z‖)]
  change (∑' c, ‖tupleFourierCoefficient δ (choiceDivisors c) z‖) ≤ _
  simp_rw [← choiceTerm_eq_tupleFourierCoefficient hA δ]
  exact primeEulerChoices_norm_tsum_le hδ A z hε hA hR hz

theorem tupleFourier_eq_H_zeta {ι : Type*} [Fintype ι] {δ R : ℕ} (hδ : δ≤1)
    (A : ℕ → Finset (Finset ι)) (B : Finset (Finset ι)) (z : ι → ℂ) {ε : ℝ} (hε : 0<ε)
    (hA : ∀ p : Nat.Primes, ∀ S∈A p, S.Nonempty)
    (hR : ∀ p : Nat.Primes, (A p).card≤R) (hz : ∀ i, ε≤(z i).re)
    (hB : ∀ S∈B, S.Nonempty) {H : ℂ}
    (hH : HasProd (fun p : Nat.Primes => eulerH p δ (A p) B z) H) :
    (∑' d : AllowedDivisorTuple A, tupleFourierCoefficient δ d.val z) =
      H*eulerZetaProduct B z := by
  exact (tupleFourier_hasProd hδ A z hε hA hR hz).unique
    (eulerP_hasProd δ A B z hB (fun i => hε.trans_le (hz i)) hH)

theorem prime_dvd_finset_lcm {ι : Type*} (s : Finset ι) (d : ι → ℕ)
    {p : ℕ} (hp : Nat.Prime p) : p∣s.lcm d ↔ ∃ i∈s, p∣d i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hp.not_dvd_one]
  | @insert i s hi ih =>
    rw [Finset.lcm_insert]
    change p∣Nat.lcm (d i) (s.lcm d) ↔ _
    simp only [hp.dvd_lcm, ih, Finset.mem_insert, exists_eq_or_imp]

theorem tuplePrimeSupport_eq_modulus {ι : Type*} [Fintype ι] {d : ι → ℕ}
    (hd : ∀ i, d i≠0) :
    tuplePrimeSupport d = (tupleModulus d).primeFactors.subtype Nat.Prime := by
  ext p
  change p∈tuplePrimeSupport d ↔
    (⟨p.val,p.property⟩ : {n : ℕ // Nat.Prime n})∈(tupleModulus d).primeFactors.subtype Nat.Prime
  rw [mem_tuplePrimeSupport hd p, Finset.mem_subtype, Nat.mem_primeFactors]
  have hq0 : Finset.univ.lcm d ≠ 0 :=
    (tupleModulus_pos (fun i => Nat.pos_of_ne_zero (hd i))).ne'
  simp only [p.property, true_and, tupleModulus, prime_dvd_finset_lcm _ _ p.property,
    Finset.mem_univ, true_and]
  exact ⟨fun h => ⟨h,hq0⟩, fun h => h.1⟩

theorem tupleModulus_eq_primeSupport_prod {ι : Type*} [Fintype ι] {d : ι → ℕ}
    (hd : ∀ i, Squarefree (d i)) : tupleModulus d = ∏ p∈tuplePrimeSupport d, (p:ℕ) := by
  rw [tuplePrimeSupport_eq_modulus (fun i => (hd i).ne_zero)]
  change tupleModulus d = Finset.prod ((tupleModulus d).primeFactors.subtype Nat.Prime)
    (fun p : {n : ℕ // Nat.Prime n} => p.val)
  rw [Finset.prod_subtype_of_mem (fun p : ℕ => p)
    (fun p hp => Nat.prime_of_mem_primeFactors hp)]
  exact (Nat.prod_primeFactors_of_squarefree (tupleModulus_squarefree hd)).symm

theorem tuplePrimeDensity_zero {ι : Type*} [Fintype ι] {d : ι → ℕ}
    (hd : ∀ i, Squarefree (d i)) : tuplePrimeDensity 0 d = (tupleModulus d : ℂ)⁻¹ := by
  simp only [tuplePrimeDensity, Nat.cast_zero, sub_zero, Finset.prod_inv_distrib]
  rw [tupleModulus_eq_primeSupport_prod hd, Nat.cast_prod]

open scoped ContDiff

end LargePrimeGaps

end OAI
end

section
-- module Solutions.OAIW2_P344.PrimeGaps_ContourSums
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

open Asymptotics

open scoped Classical

open scoped ContDiff

theorem tupleFourierCoefficient_norm_eq_of_re {ι : Type*} [Fintype ι] (δ : ℕ) (d : ι → ℕ)
    (z w : ι → ℂ) (h : ∀ i, (z i).re=(w i).re) :
    ‖tupleFourierCoefficient δ d z‖ = ‖tupleFourierCoefficient δ d w‖ := by
  simp only [tupleFourierCoefficient, norm_mul, Complex.norm_exp, Complex.neg_re,
    Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero, h]

theorem tupleFourierCoefficient_contour_norm {ι : Type*} [Fintype ι] (δ : ℕ) (d : ι → ℕ)
    (L : ℝ) (u : EuclideanSpace ℝ ι) :
    ‖tupleFourierCoefficient δ d (fourierContour L u)‖ =
      ‖tupleFourierCoefficient δ d (fun _ => (L⁻¹:ℝ))‖ := by
  apply tupleFourierCoefficient_norm_eq_of_re
  intro i
  simp

theorem continuous_tupleFourierCoefficient_contour {ι : Type*} [Fintype ι]
    (δ : ℕ) (d : ι → ℕ) (L : ℝ) :
    Continuous (fun u : EuclideanSpace ℝ ι => tupleFourierCoefficient δ d (fourierContour L u)) := by
  unfold tupleFourierCoefficient fourierContour
  fun_prop

theorem contour_sum_log_eq {ι : Type*} [Fintype ι] (L : ℝ) (d : ι → ℕ)
    (u : EuclideanSpace ℝ ι) :
    (∑ i, (Real.log (d i):ℂ)*fourierContour L u i) =
      (fourierCoordinateSum ι (divisorLogVector L d) : ℂ) +
        Complex.I*(inner ℝ u (divisorLogVector L d) : ℂ) := by
  simp only [fourierCoordinateSum_apply, Complex.ofReal_sum, PiLp.inner_apply,
    Real.inner_apply, divisorLogVector_apply, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [fourierContour, Complex.ofReal_mul, Complex.ofReal_inv, div_eq_mul_inv]
  ring

theorem integral_sourceFourier_tupleCoefficient {ι : Type*} [Fintype ι]
    (δ : ℕ) (d : ι → ℕ) (L : ℝ) (F : EuclideanSpace ℝ ι → ℂ)
    (hF : HasCompactSupport F) (hFs : ContDiff ℝ ∞ F) :
    (∫ u : EuclideanSpace ℝ ι, sourceFourier (fourierCoordinateSum ι) F hF hFs u *
      tupleFourierCoefficient δ d (fourierContour L u)) =
    tuplePrimeDensity δ d * (∏ i, (ArithmeticFunction.moebius (d i):ℂ)) *
      F (divisorLogVector L d) := by
  simp only [tupleFourierCoefficient, contour_sum_log_eq, neg_add_rev]
  rw [← sourceFourier_inversion (fourierCoordinateSum ι) F hF hFs (divisorLogVector L d),
    ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with u
  rw [sub_eq_add_neg]
  ring_nf

theorem integrable_sourceFourier_tupleCoefficient {ι : Type*} [Fintype ι]
    (δ : ℕ) (d : ι → ℕ) (L : ℝ) (Φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ) :
    Integrable (fun u => Φ u * tupleFourierCoefficient δ d (fourierContour L u)) := by
  apply Φ.integrable.mul_bdd (continuous_tupleFourierCoefficient_contour δ d L).aestronglyMeasurable
  filter_upwards [] with u
  exact (tupleFourierCoefficient_contour_norm δ d L u).le

theorem analyticDensity_eq_integral {ι : Type*} [Fintype ι] {δ R : ℕ} (hδ : δ≤1)
    (A : ℕ → Finset (Finset ι)) {L : ℝ} (hL : 0<L)
    (hA : ∀ p : Nat.Primes, ∀ S∈A p, S.Nonempty)
    (hR : ∀ p : Nat.Primes, (A p).card≤R)
    (F : EuclideanSpace ℝ ι → ℂ) (hF : HasCompactSupport F) (hFs : ContDiff ℝ ∞ F) :
    analyticDensity δ A L F =
      ∫ u : EuclideanSpace ℝ ι, sourceFourier (fourierCoordinateSum ι) F hF hFs u *
        ∑' d : AllowedDivisorTuple A, tupleFourierCoefficient δ d.val (fourierContour L u) := by
  let : Countable (AllowedDivisorTuple A) := by unfold AllowedDivisorTuple; infer_instance
  let Φ := sourceFourier (fourierCoordinateSum ι) F hF hFs
  have hs := tupleFourier_summable_norm hδ A (fun _ => (L⁻¹:ℝ)) (inv_pos.mpr hL)
    hA hR (fun _ => le_rfl)
  have hint (d : AllowedDivisorTuple A) :
      Integrable (fun u => Φ u * tupleFourierCoefficient δ d.val (fourierContour L u)) :=
    integrable_sourceFourier_tupleCoefficient δ d.val L Φ
  have hsum : Summable (fun d : AllowedDivisorTuple A =>
      ∫ u : EuclideanSpace ℝ ι, ‖Φ u*tupleFourierCoefficient δ d.val (fourierContour L u)‖) := by
    simp_rw [norm_mul, tupleFourierCoefficient_contour_norm, integral_mul_const]
    exact hs.mul_left _
  have he := (hasSum_integral_of_summable_integral_norm hint hsum).tsum_eq
  simp only [integral_sourceFourier_tupleCoefficient, Φ] at he
  rw [analyticDensity, he]
  apply integral_congr_ae
  filter_upwards [] with u
  exact tsum_mul_left

theorem allowed_residue_iff {ι : Type*} [Fintype ι] (d b : ι → ℕ) :
    (∀ p : Nat.Primes, (tuplePrimeSubset d p).Nonempty →
      tuplePrimeSubset d p∈residueFamily (fun i => (b i:ℤ)) p) ↔ localCompatible d b := by
  constructor
  · intro h p hp _ i j hi hj
    have hm := h ⟨p,hp⟩ ⟨i,by simp [tuplePrimeSubset,hi]⟩
    rw [residueFamily, mem_fiberSubsetFamily_image] at hm
    have he := hm.2 i (by simp [tuplePrimeSubset,hi]) j (by simp [tuplePrimeSubset,hj])
    change b i % p = b j % p
    exact_mod_cast he
  · intro h p hp
    rw [residueFamily, mem_fiberSubsetFamily_image]
    refine ⟨hp,?_⟩
    intro i hi j hj
    have hi' : p.val∣d i := by simpa [tuplePrimeSubset] using hi
    have hj' : p.val∣d j := by simpa [tuplePrimeSubset] using hj
    have hq : p.val∣tupleModulus d := hi'.trans (Finset.dvd_lcm (Finset.mem_univ i))
    have he : b i % p.val=b j % p.val := h p.val p.property hq i j hi' hj'
    exact_mod_cast he

theorem analyticDensity_eq_unmarked_tsum {n : ℕ} (X : ℕ)
    (F : (Fin n → ℝ) → ℝ) (b : Fin n → ℕ) :
    analyticDensity 0 (residueFamily (fun i => (b i:ℤ))) (Real.log X)
      (fun v => (F v.ofLp:ℂ)) =
      ∑' d : Fin n → ℕ, ((divisorCoefficient X F d * tupleDensity d b : ℝ):ℂ) := by
  let P := fun d : Fin n → ℕ => (∀ i, Squarefree (d i)) ∧
    ∀ p : Nat.Primes, (tuplePrimeSubset d p).Nonempty →
      tuplePrimeSubset d p∈residueFamily (fun i => (b i:ℤ)) p
  change (∑' d : {d // P d}, tuplePrimeDensity 0 d.val *
    (∏ i, (ArithmeticFunction.moebius (d.val i):ℂ)) *
      (F (divisorLogVector (Real.log X) d.val).ofLp:ℂ)) = _
  refine (tsum_subtype {d | P d} (fun d => tuplePrimeDensity 0 d *
    (∏ i, (ArithmeticFunction.moebius (d i):ℂ)) *
      (F (divisorLogVector (Real.log X) d).ofLp:ℂ))).trans ?_
  apply tsum_congr
  intro d
  by_cases hd : P d
  · rw [Set.indicator_of_mem (show d ∈ {d | P d} from hd), tuplePrimeDensity_zero hd.1]
    have hc := (tupleCompatible_iff_localCompatible hd.1).mpr ((allowed_residue_iff d b).mp hd.2)
    simp only [divisorCoefficient,tupleDensity,ite_eq_left hc,Complex.ofReal_mul,
      Complex.ofReal_prod,Complex.ofReal_intCast,Complex.ofReal_inv,Complex.ofReal_natCast]
    change (tupleModulus d : ℂ)⁻¹ * (∏ i, (ArithmeticFunction.moebius (d i):ℂ)) *
      (F (logCoordinates X d):ℂ) = _
    ring
  · rw [Set.indicator_of_notMem (show d ∉ {d | P d} from hd)]
    have hv : divisorCoefficient X F d * tupleDensity d b = 0 := by
      by_contra hv
      have hf := (divisorCoefficient_ne_zero_iff.mp (mul_ne_zero_iff.mp hv).1).1
      have hc : tupleCompatible d b := by
        by_contra hc
        exact (mul_ne_zero_iff.mp hv).2 (by simp [tupleDensity,hc])
      exact hd ⟨hf,(allowed_residue_iff d b).mpr
        ((tupleCompatible_iff_localCompatible hf).mp hc)⟩
    rw [hv,Complex.ofReal_zero]

theorem divisorCoefficient_support {n X : ℕ} (hX : 2≤X)
    {F : (Fin n → ℝ) → ℝ} {rho : ℝ} (hbudget : HasBudget F rho)
    {d : Fin n → ℕ} (hd : divisorCoefficient X F d≠0) :
    d ∈ positiveProductTuples n ⌊Real.exp (rho * Real.log (X : ℝ))⌋₊ := by
  obtain ⟨hsq,hF⟩ := divisorCoefficient_ne_zero_iff.mp hd
  have hp : ∀ i, 0<d i := fun i => Nat.pos_of_ne_zero (hsq i).ne_zero
  refine Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr ?_,?_⟩
  · intro i
    exact Finset.mem_Icc.mpr ⟨hp i,divisor_coordinate_bound hX hbudget hp hF i⟩
  · exact (Nat.le_floor_iff (Real.exp_pos _).le).mpr (divisor_product_bound hX hbudget hp hF)

theorem analyticDensity_eq_unmarkedDensitySum {n X : ℕ} (hX : 2≤X)
    {F : (Fin n → ℝ) → ℝ} {rho : ℝ} (hbudget : HasBudget F rho) (b : Fin n → ℕ) :
    analyticDensity 0 (residueFamily (fun i => (b i:ℤ))) (Real.log X)
      (fun v => (F v.ofLp:ℂ)) = (unmarkedDensitySum X F rho b : ℂ) := by
  rw [analyticDensity_eq_unmarked_tsum,unmarkedDensitySum,Complex.ofReal_sum]
  apply tsum_eq_sum
  intro d hd
  have hc : divisorCoefficient X F d=0 := by
    by_contra hc
    exact hd (divisorCoefficient_support hX hbudget hc)
  simp only [hc,zero_mul,Complex.ofReal_zero]

theorem schwartz_integral_tail_bound {ι : Type*} [Fintype ι]
    (Φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ) (K : EuclideanSpace ℝ ι → ℂ)
    {R B : ℝ} (hR : 0<R) (hB : 0≤B) (hKm : AEStronglyMeasurable K volume)
    (hK : ∀ u, ‖K u‖≤B) (k : ℕ) :
    ‖∫ u in {u | R<‖u‖}, Φ u*K u‖ ≤
      (B/R^k) * ∫ u, ‖u‖^k*‖Φ u‖ := by
  let S : Set (EuclideanSpace ℝ ι) := {u | R<‖u‖}
  have hS : MeasurableSet S := (isOpen_lt continuous_const continuous_norm).measurableSet
  have hp : Integrable (fun u => Φ u*K u) :=
    Φ.integrable.mul_bdd hKm (Filter.Eventually.of_forall hK)
  have ht : Integrable (fun u : EuclideanSpace ℝ ι => ‖u‖^k*‖Φ u‖) :=
    SchwartzMap.integrable_pow_mul volume Φ k
  have hm : ∀ᵐ u ∂volume.restrict S,
      ‖Φ u*K u‖ ≤ (B/R^k)*(‖u‖^k*‖Φ u‖) := by
    filter_upwards [ae_restrict_mem hS] with u hu
    have hpow : R^k≤‖u‖^k := pow_le_pow_left₀ hR.le hu.le k
    rw [norm_mul]
    have hpower : 1≤‖u‖^k/R^k := (one_le_div (pow_pos hR k)).mpr hpow
    calc
      ‖Φ u‖*‖K u‖ ≤ ‖Φ u‖*B := mul_le_mul_of_nonneg_left (hK u) (norm_nonneg _)
      _ ≤ (‖Φ u‖*B)*(‖u‖^k/R^k) := le_mul_of_one_le_right (by positivity) hpower
      _ = (B/R^k)*(‖u‖^k*‖Φ u‖) := by ring
  calc
    _ ≤ ∫ u in S, ‖Φ u*K u‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ u in S, (B/R^k)*(‖u‖^k*‖Φ u‖) :=
      integral_mono_ae hp.integrableOn.norm ((ht.const_mul _).integrableOn) hm
    _ ≤ ∫ u, (B/R^k)*(‖u‖^k*‖Φ u‖) :=
      setIntegral_le_integral (ht.const_mul _) (by filter_upwards [] with u; positivity)
    _ = _ := integral_const_mul _ _

theorem continuous_tupleFourier_tsum {ι : Type*} [Fintype ι] {δ R : ℕ} (hδ : δ≤1)
    (A : ℕ → Finset (Finset ι)) {L : ℝ} (hL : 0<L)
    (hA : ∀ p : Nat.Primes, ∀ S∈A p, S.Nonempty)
    (hR : ∀ p : Nat.Primes, (A p).card≤R) :
    Continuous (fun u : EuclideanSpace ℝ ι =>
      ∑' d : AllowedDivisorTuple A, tupleFourierCoefficient δ d.val (fourierContour L u)) := by
  refine continuous_tsum (fun d => continuous_tupleFourierCoefficient_contour δ d.val L)
    (tupleFourier_summable_norm hδ A (fun _ => (L⁻¹:ℝ)) (inv_pos.mpr hL) hA hR
      (fun _ => by simp)) ?_
  intro d u
  exact (tupleFourierCoefficient_contour_norm δ d.val L u).le

theorem tupleFourier_tsum_norm_bound {ι : Type*} [Fintype ι] {δ R : ℕ} (hδ : δ≤1)
    (A : ℕ → Finset (Finset ι)) {L : ℝ} (hL : 0<L)
    (hA : ∀ p : Nat.Primes, ∀ S∈A p, S.Nonempty)
    (hR : ∀ p : Nat.Primes, (A p).card≤R) (u : EuclideanSpace ℝ ι) :
    ‖∑' d : AllowedDivisorTuple A, tupleFourierCoefficient δ d.val (fourierContour L u)‖ ≤
    Real.exp ((2*R)*Real.log (riemannZeta ((1+L⁻¹:ℝ):ℂ)).re) := by
  exact (norm_tsum_le_tsum_norm (tupleFourier_summable_norm hδ A _ (inv_pos.mpr hL)
    hA hR (by intro i; simp))).trans
    (tupleFourier_norm_tsum_le hδ A _ (inv_pos.mpr hL) hA hR (by intro i; simp))

theorem tupleFourier_schwartz_tail {ι : Type*} [Fintype ι] {δ R : ℕ} (hδ : δ≤1)
    (A : ℕ → Finset (Finset ι)) {L U : ℝ} (hL : 0<L) (hU : 0<U)
    (hA : ∀ p : Nat.Primes, ∀ S∈A p, S.Nonempty)
    (hR : ∀ p : Nat.Primes, (A p).card≤R)
    (Φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ) (k : ℕ) :
    ‖∫ u in {u | U<‖u‖}, Φ u *
      (∑' d : AllowedDivisorTuple A, tupleFourierCoefficient δ d.val (fourierContour L u))‖ ≤
      (Real.exp ((2*R)*Real.log (riemannZeta ((1+L⁻¹:ℝ):ℂ)).re)/U^k) *
        ∫ u, ‖u‖^k*‖Φ u‖ := by
  apply schwartz_integral_tail_bound Φ _ hU (Real.exp_pos _).le
    (continuous_tupleFourier_tsum hδ A hL hA hR).aestronglyMeasurable
    (tupleFourier_tsum_norm_bound hδ A hL hA hR)

theorem zeta_contour_majorant_polynomial :
    ∃ L₀>0, ∀ L : ℝ, L₀≤L → ∀ R : ℕ,
      Real.exp ((2*R)*Real.log (riemannZeta ((1+L⁻¹:ℝ):ℂ)).re) ≤ ((3/2)*L)^(2*R) := by
  obtain ⟨c,hc,ε,hε,hpole⟩ := zeta_pole_two_sided
  refine ⟨1+ε⁻¹,by positivity,fun L hL R => ?_⟩
  have hL0 : 0<L := lt_of_lt_of_le (by positivity) hL
  have heL : L⁻¹<ε := (inv_lt_comm₀ hL0 hε).mpr (by linarith)
  have hnorm : ‖(L⁻¹:ℂ)‖=L⁻¹ := by
    rw [show (L⁻¹:ℂ)=((L⁻¹:ℝ):ℂ) by simp,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hL0)]
  have hb := (hpole (L⁻¹:ℂ) (inv_ne_zero (by exact_mod_cast hL0.ne')) (by rw [hnorm]; exact heL)).2.2
  rw [norm_mul,hnorm] at hb
  have hz : (riemannZeta ((1+L⁻¹:ℝ):ℂ)).re ≤ (3/2)*L := by
    have hcast : ((1+L⁻¹:ℝ):ℂ)=1+(L⁻¹:ℂ) := by simp
    rw [hcast]
    apply (Complex.re_le_norm _).trans
    calc
      _ = L * (L⁻¹ * ‖riemannZeta (1+(L⁻¹:ℂ))‖) := by field_simp
      _ ≤ L*(3/2) := mul_le_mul_of_nonneg_left hb hL0.le
      _ = _ := by ring
  have hzpos : 0<(riemannZeta ((1+L⁻¹:ℝ):ℂ)).re :=
    riemannZeta_re_pos_of_one_lt (by linarith [inv_pos.mpr hL0])
  calc
    _ = (riemannZeta ((1+L⁻¹:ℝ):ℂ)).re^(2*R) := by
      rw [show (2:ℝ)*R=((2*R:ℕ):ℝ) by norm_cast,Real.exp_nat_mul,Real.exp_log hzpos]
    _ ≤ _ := pow_le_pow_left₀ hzpos.le hz _

theorem genericEulerConstant_mono : Monotone genericEulerConstant := by
  intro m n hmn
  unfold genericEulerConstant
  gcongr
  norm_num

theorem primeReciprocalPrefix_nonneg (y : ℕ) : 0≤primeReciprocalPrefix y := by
  unfold primeReciprocalPrefix
  exact Finset.sum_nonneg (fun _ _ => by positivity)

theorem exp_sub_one_le_two_mul {x : ℝ} (hx : 0≤x) (hx1 : x≤1) :
    Real.exp x-1≤2*x := by
  have h := Real.norm_exp_sub_one_sub_id_le (x:=x) (by simpa only [Real.norm_eq_abs,abs_of_nonneg hx] using hx1)
  rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg hx] at h
  have hh := (abs_le.mp h).2
  nlinarith [mul_nonneg hx (sub_nonneg.mpr hx1)]

theorem eulerGlobal_uniform_error {ι : Type*} [Fintype ι] {δ : ℕ} (hδ : δ≤1)
    (A : ℕ → Finset (Finset ι)) (B : Finset (Finset ι))
    (z : ι → ℂ) (hz : ∀ i, 0≤(z i).re) {y R : ℕ} (hy : 2≤y)
    (hA : ∀ p : Nat.Primes, (A p).card≤R) (hB : B.card≤R)
    (hgen : ∀ p : Nat.Primes, y<(p:ℕ) → A p=B) {s : ℝ}
    (hzsmall : ∑ i, ‖z i‖ ≤ (y:ℝ)^(-s)) :
    ‖eulerGlobal δ A B z-eulerGlobal δ A B (fun _ => 0)‖ ≤ uniformEulerError R s y := by
  apply (eulerGlobal_comparison hδ A B z hz hy hA hB hgen).trans
  unfold uniformEulerError
  have hlog : 0≤Real.log (y:ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1≤y))
  have hr := primeReciprocalPrefix_nonneg y
  have hK := genericEulerConstant_mono hB
  gcongr

end LargePrimeGaps

end OAI
end

section
-- module Solutions.OAIW2_P344.PrimeGaps_FourierDerivatives
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

open Asymptotics

open scoped Classical

open scoped ContDiff

theorem tendsto_log_rpow_div_nat_rpow (a : ℝ) {s : ℝ} (hs : 0<s) :
    Tendsto (fun y : ℕ => (Real.log (y:ℝ))^a/(y:ℝ)^s) atTop (𝓝 0) :=
  (isLittleO_log_rpow_rpow_atTop a hs).tendsto_div_nhds_zero.comp
    (tendsto_natCast_atTop_atTop (R:=ℝ))

theorem uniformEulerError_tendsto (R : ℕ) {s : ℝ} (hs : 0<s) :
    Tendsto (uniformEulerError R s) atTop (𝓝 0) := by
  let c : ℝ := Real.exp 1
  let a : ℝ := 4*R*c
  let M : ℝ := Real.exp a
  let K : ℝ := genericEulerConstant R
  let E₁ : ℕ → ℝ := fun y => (M*Real.exp (2*R)*6*R*c)*
    ((Real.log (y:ℝ))^(a+2)/(y:ℝ)^s)
  let E₂ : ℕ → ℝ := fun y => (4*M*K)*((Real.log (y:ℝ))^a/(y:ℝ))
  have h₁ : Tendsto E₁ atTop (𝓝 0) := by
    simpa only [mul_zero,E₁] using (tendsto_log_rpow_div_nat_rpow (a+2) hs).const_mul _
  have h₂ : Tendsto E₂ atTop (𝓝 0) := by
    simpa only [mul_zero,Real.rpow_one,E₂] using
      (tendsto_log_rpow_div_nat_rpow a (s:=1) zero_lt_one).const_mul (4*M*K)
  have he : ∀ᶠ y : ℕ in atTop, 0≤uniformEulerError R s y ∧
      uniformEulerError R s y ≤ E₁ y+E₂ y := by
    have ht := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
    filter_upwards [eventually_prime_reciprocal_bound, ht.eventually_ge_atTop 1,
      (tendsto_natCast_atTop_atTop (R:=ℝ)).eventually_ge_atTop (max K 1)] with y hr hl hy
    change 1 ≤ Real.log (y:ℝ) at hl
    have hy0 : (0:ℝ)<y := lt_of_lt_of_le zero_lt_one ((le_max_right _ _).trans hy)
    have hK0 : 0≤K := genericEulerConstant_nonneg R
    have hKy : K/(y:ℝ)≤1 := (div_le_one hy0).mpr ((le_max_left _ _).trans hy)
    have hp0 := primeReciprocalPrefix_nonneg y
    have hr' : primeReciprocalPrefix y ≤ c*(1+Real.log (Real.log y)) := by
      simpa only [primeReciprocalPrefix_eq,c] using hr
    have hr'' : primeReciprocalPrefix y ≤ c*Real.log y := by
      apply hr'.trans
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      linarith [Real.log_le_sub_one_of_pos (show 0<Real.log (y:ℝ) by linarith)]
    have hp : Real.exp (4*R*primeReciprocalPrefix y) ≤ M*(Real.log (y:ℝ))^a := by
      calc
        _ ≤ Real.exp (4*R*(c*(1+Real.log (Real.log y)))) := by gcongr
        _ = _ := by
          rw [Real.rpow_def_of_pos (show 0<Real.log (y:ℝ) by linarith)]
          dsimp only [M,a]
          rw [← Real.exp_add]
          congr 1
          ring
    have hex : Real.exp (K/(y:ℝ))-1 ≤ 2*(K/(y:ℝ)) :=
      exp_sub_one_le_two_mul (by positivity) hKy
    have hnonneg : 0≤Real.exp (K/(y:ℝ))-1 := sub_nonneg.mpr (Real.one_le_exp (by positivity))
    constructor
    · unfold uniformEulerError
      exact mul_nonneg (Real.exp_pos _).le (add_nonneg (by positivity) (mul_nonneg (by norm_num) hnonneg))
    · calc
        _ ≤ (M*(Real.log (y:ℝ))^a)*
              (Real.exp (2*R)*6*R*Real.log y*(y:ℝ)^(-s)*(c*Real.log y)+4*K/(y:ℝ)) := by
            unfold uniformEulerError
            apply mul_le_mul hp ?_ (add_nonneg (by positivity) (mul_nonneg (by norm_num) hnonneg))
              (by positivity)
            gcongr
            calc
              _ ≤ 2*(2*(K/(y:ℝ))) := mul_le_mul_of_nonneg_left hex (by norm_num)
              _ = _ := by ring
        _ = E₁ y+E₂ y := by
          dsimp only [E₁,E₂]
          rw [Real.rpow_neg hy0.le,Real.rpow_add (show 0<Real.log (y:ℝ) by linarith),Real.rpow_two]
          ring
  apply squeeze_zero'
  · exact he.mono (fun _ => And.left)
  · exact he.mono (fun _ => And.right)
  · simpa only [add_zero] using h₁.add h₂

theorem familyKernel_homogeneous {ι : Type*} (B : Finset (Finset ι))
    (w : ι → ℂ) {c : ℂ} (hc : c≠0) {t : ℕ}
    (ht : (∑ S∈B, (-1:ℤ)^S.card) = -(t:ℤ)) :
    familyKernel B (fun i => c*w i) = c^t*familyKernel B w := by
  classical
  unfold familyKernel
  simp_rw [← Finset.mul_sum,mul_zpow]
  rw [Finset.prod_mul_distrib,prod_const_zpow _ _ hc,Finset.sum_neg_distrib,ht,
    neg_neg,zpow_natCast]

theorem eulerZetaProduct_factorization {ι : Type*} (B : Finset (Finset ι)) (z : ι → ℂ)
    (hz : ∀ S∈B, ∑ i∈S, z i≠0) :
    eulerZetaProduct B z=familyKernel B z*normalizedZetaProduct B z := by
  classical
  unfold eulerZetaProduct familyKernel normalizedZetaProduct
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro S hS
  rw [mul_zpow,← mul_assoc,← zpow_add₀ (hz S hS),neg_add_cancel,zpow_zero,one_mul]

theorem familyKernel_norm_polynomial {ι : Type*} [Fintype ι]
    (B : Finset (Finset ι)) (hB : ∀ S∈B, S.Nonempty) (u : ι → ℝ)
    {U : ℝ} (hU : 0≤U) (hu : ∀ i, |u i|≤U) :
    ‖familyKernel B (fun i => frequencyW (u i))‖ ≤
      ((max (Fintype.card ι) 1:ℕ)*(1+U):ℝ)^B.card := by
  have hbase : (1:ℝ)≤(max (Fintype.card ι) 1:ℕ)*(1+U) := by
    have h : (1:ℝ)≤(max (Fintype.card ι) 1:ℕ) := by exact_mod_cast le_max_right _ _
    nlinarith
  rw [familyKernel,norm_prod]
  calc
    _ ≤ ∏ _S∈B, ((max (Fintype.card ι) 1:ℕ)*(1+U):ℝ) := by
      apply Finset.prod_le_prod (fun _ _ => norm_nonneg _)
      intro S hS
      rcases neg_one_pow_eq_or ℤ S.card with h | h
      · rw [h,zpow_neg_one,norm_inv]
        exact (inv_le_one_of_one_le₀ (frequencySum_norm_lower (hB S hS) u)).trans hbase
      · rw [h,neg_neg,zpow_one]
        apply (frequencySum_norm_upper S u (fun i _ => hu i)).trans
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact_mod_cast (Finset.card_le_univ S).trans (le_max_left _ _)
    _ = _ := by simp

theorem normalizedZetaProduct_error {ι : Type*} (B : Finset (Finset ι)) (z : ι → ℂ)
    {c ε : ℝ} (hc : 0<c) (hε : 0≤ε)
    (hz : ∀ S∈B,
      ‖(∑ i∈S, z i)*riemannZeta (1+∑ i∈S, z i)-1‖≤c*ε ∧
      1/2≤‖(∑ i∈S, z i)*riemannZeta (1+∑ i∈S, z i)‖ ∧
      ‖(∑ i∈S, z i)*riemannZeta (1+∑ i∈S, z i)‖≤3/2) :
    ‖normalizedZetaProduct B z-1‖ ≤ 2^B.card*(B.card*(2*c*ε)) := by
  apply norm_prod_sub_one_le _ _ (by norm_num : (1:ℝ)≤2)
  · intro S hS
    rcases neg_one_pow_eq_or ℤ S.card with h | h
    · rw [h,zpow_one]
      linarith [(hz S hS).2.2]
    · rw [h,zpow_neg_one,norm_inv]
      exact (inv_le_comm₀ (by linarith [(hz S hS).2.1] :
        0<‖(∑ i∈S, z i)*riemannZeta (1+∑ i∈S, z i)‖) (by norm_num)).mpr
        (by simpa only [one_div] using (hz S hS).2.1)
  · intro S hS
    rcases neg_one_pow_eq_or ℤ S.card with h | h
    · rw [h,zpow_one]
      nlinarith [(hz S hS).1]
    · rw [h,zpow_neg_one]
      exact (norm_inv_sub_one_le (hz S hS).2.1).trans (by nlinarith [(hz S hS).1])

theorem eulerZeta_norm_contour_error :
    ∃ c>0, ∃ ε>0, ∀ {ι : Type*} [Fintype ι] (B : Finset (Finset ι)),
      (∀ S∈B, S.Nonempty) → ∀ u : ι → ℝ, ∀ {L U : ℝ}, 0<L → 0≤U →
      (∀ i, |u i|≤U) → (Fintype.card ι:ℝ)*(1+U)/L<ε →
      ‖normalizedZetaProduct B (fun i => frequencyW (u i)/(L:ℂ))-1‖ ≤
        2^B.card*(B.card*(2*c*((Fintype.card ι:ℝ)*(1+U)/L))) := by
  obtain ⟨c,hc,ε,hε,hpole⟩ := zeta_pole_two_sided
  refine ⟨c,hc,ε,hε,?_⟩
  intro ι _ B hB u L U hL hU hu hsmall
  apply normalizedZetaProduct_error B _ hc (by positivity)
  intro S hS
  have hsum : (∑ i∈S, frequencyW (u i)/(L:ℂ)) =
      (∑ i∈S, frequencyW (u i))/(L:ℂ) := (Finset.sum_div _ _ _).symm
  have hnz : (∑ i∈S, frequencyW (u i)/(L:ℂ))≠0 := by
    rw [hsum]
    exact div_ne_zero (frequencySum_ne_zero (hB S hS) u) (by exact_mod_cast hL.ne')
  have hn : ‖∑ i∈S, frequencyW (u i)/(L:ℂ)‖ ≤ (Fintype.card ι:ℝ)*(1+U)/L := by
    rw [hsum,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hL]
    apply div_le_div_of_nonneg_right _ hL.le
    apply (frequencySum_norm_upper S u (fun i _ => hu i)).trans
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_le_univ S) (by positivity)
  have hp := hpole _ hnz (hn.trans_lt hsmall)
  exact ⟨hp.1.trans (mul_le_mul_of_nonneg_left hn hc.le), hp.2⟩

theorem eulerZetaProduct_scaled_factorization {ι : Type*}
    (B : Finset (Finset ι)) (hB : ∀ S∈B, S.Nonempty) (u : ι → ℝ)
    {t : ℕ} (ht : (∑ S∈B, (-1:ℤ)^S.card) = -(t:ℤ)) {L : ℝ} (hL : 0<L) :
    (L:ℂ)^t*eulerZetaProduct B (fun i => frequencyW (u i)/(L:ℂ)) =
      familyKernel B (fun i => frequencyW (u i))*
        normalizedZetaProduct B (fun i => frequencyW (u i)/(L:ℂ)) := by
  have hLc : (L:ℂ)≠0 := by exact_mod_cast hL.ne'
  have hnz : ∀ S∈B, ∑ i∈S, frequencyW (u i)/(L:ℂ)≠0 := by
    intro S hS
    rw [← Finset.sum_div]
    exact div_ne_zero (frequencySum_ne_zero (hB S hS) u) hLc
  have hk : familyKernel B (fun i => frequencyW (u i)/(L:ℂ)) =
      (L:ℂ)⁻¹^t*familyKernel B (fun i => frequencyW (u i)) := by
    simpa only [div_eq_mul_inv,mul_comm] using
      familyKernel_homogeneous B (fun i => frequencyW (u i)) (inv_ne_zero hLc) ht
  rw [eulerZetaProduct_factorization _ _ hnz,hk,inv_pow,← mul_assoc,← mul_assoc,
    mul_inv_cancel₀ (pow_ne_zero t hLc),one_mul]

theorem norm_eulerGlobal_le {ι : Type*} {δ : ℕ} (hδ : δ≤1)
    (A : ℕ → Finset (Finset ι)) (B : Finset (Finset ι))
    (z : ι → ℂ) (hz : ∀ i, 0≤(z i).re) {y R : ℕ} (hy : 0<y)
    (hA : ∀ p : Nat.Primes, (A p).card≤R) (hB : B.card≤R)
    (hgen : ∀ p : Nat.Primes, y<(p:ℕ) → A p=B) :
    ‖eulerGlobal δ A B z‖ ≤ eulerGlobalMajorant R y := by
  have hf := eulerH_summable_error hδ A B z hz hy hgen
  have ht := norm_tprod_sub_one_le_exp (hf.subtype (fun p => p∉primePrefix y))
  have htail := eulerH_tail_sum hδ A B z hz hy hgen
  have hpref : ‖∏ p∈primePrefix y, eulerH p δ (A p) B z‖ ≤
      Real.exp (4*R*primeReciprocalPrefix y) := by
    rw [norm_prod]
    calc
      _ ≤ ∏ p∈primePrefix y, Real.exp (4*R*(p:ℝ)⁻¹) := by
        apply Finset.prod_le_prod (fun _ _ => norm_nonneg _)
        intro p _
        apply (norm_eulerH_le p.property.two_le hδ (A p) B z hz).trans
        apply Real.exp_le_exp.mpr
        have haR : ((A p).card:ℝ)≤R := by exact_mod_cast hA p
        have hbR : (B.card:ℝ)≤R := by exact_mod_cast hB
        have hp0 : 0≤(p:ℝ)⁻¹ := by positivity
        nlinarith
      _ = _ := by rw [← Real.exp_sum]; congr 1; simp [primeReciprocalPrefix,Finset.mul_sum]
  have hn : ‖∏' p : {p : Nat.Primes // p∉primePrefix y}, eulerH p.val δ (A p.val) B z‖ ≤
      Real.exp (genericEulerConstant R/(y:ℝ)) := by
    have hh := norm_le_norm_sub_add (∏' p : {p : Nat.Primes // p∉primePrefix y},
      eulerH p.val δ (A p.val) B z) 1
    rw [norm_one] at hh
    have he : Real.exp (∑' p : {p : Nat.Primes // p∉primePrefix y},
      ‖eulerH p.val δ (A p.val) B z-1‖) ≤ Real.exp (genericEulerConstant R/(y:ℝ)) := by
      apply Real.exp_le_exp.mpr
      apply htail.trans
      exact div_le_div_of_nonneg_right (genericEulerConstant_mono hB) (by positivity)
    linarith
  unfold eulerGlobal
  rw [tprod_eq_prod_mul_tail (primePrefix y) hf,norm_mul]
  apply (mul_le_mul hpref hn (norm_nonneg _) (Real.exp_pos _).le).trans_eq
  exact (Real.exp_add _ _).symm

theorem tupleFourier_scaled_factorization {ι : Type*} [Fintype ι] {δ R : ℕ} (hδ : δ≤1)
    (A : ℕ → Finset (Finset ι)) (B : Finset (Finset ι))
    (hA : ∀ p : Nat.Primes, ∀ S∈A p, S.Nonempty)
    (hR : ∀ p : Nat.Primes, (A p).card≤R)
    (hB : ∀ S∈B, S.Nonempty) {y : ℕ} (hy : 0<y)
    (hgen : ∀ p : Nat.Primes, y<(p:ℕ) → A p=B)
    (u : ι → ℝ) {t : ℕ} (ht : (∑ S∈B, (-1:ℤ)^S.card) = -(t:ℤ))
    {L : ℝ} (hL : 0<L) :
    (L:ℂ)^t*(∑' d : AllowedDivisorTuple A,
      tupleFourierCoefficient δ d.val (fun i => frequencyW (u i)/(L:ℂ))) =
      eulerGlobal δ A B (fun i => frequencyW (u i)/(L:ℂ))*
      familyKernel B (fun i => frequencyW (u i))*
      normalizedZetaProduct B (fun i => frequencyW (u i)/(L:ℂ)) := by
  have hz (i : ι) : (frequencyW (u i)/(L:ℂ)).re = 1/L := by
    simp [frequencyW,Complex.div_re]
  have hn (i : ι) : 0≤(frequencyW (u i)/(L:ℂ)).re := by rw [hz]; positivity
  have hH := multipliable_of_summable_norm_sub_one
    (eulerH_summable_error hδ A B _ hn hy hgen)
  rw [tupleFourier_eq_H_zeta hδ A B _ (by positivity : 0<1/L) hA hR
    (fun i => (hz i).ge) hB hH.hasProd]
  have he := eulerZetaProduct_scaled_factorization B hB u ht hL
  change (L:ℂ)^t*(eulerGlobal δ A B _*_) = _
  calc
    _ = eulerGlobal δ A B _*((L:ℂ)^t*eulerZetaProduct B _) := by ring
    _ = _ := by rw [he]; ring

theorem norm_mul_mul_sub_le {H H₀ K N : ℂ} {E M Z : ℝ}
    (hE : ‖H-H₀‖≤E) (hM : ‖H₀‖≤M) (hZ : ‖N-1‖≤Z) :
    ‖H*K*N-H₀*K‖ ≤ ‖K‖*(E*(1+Z)+M*Z) := by
  have he0 : 0≤E := (norm_nonneg _).trans hE
  have hM0 : 0≤M := (norm_nonneg _).trans hM
  have hN : ‖N‖≤1+Z := by
    have := norm_le_norm_sub_add N 1
    rw [norm_one] at this
    linarith
  calc
    _ = ‖K*((H-H₀)*N+H₀*(N-1))‖ := by congr 1; ring
    _ ≤ ‖K‖*(‖H-H₀‖*‖N‖+‖H₀‖*‖N-1‖) := by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (by
        simpa only [norm_mul] using (norm_add_le ((H-H₀)*N) (H₀*(N-1)))) (norm_nonneg _)
    _ ≤ _ := by gcongr

theorem tupleFourier_scaled_core_error :
    ∃ c>0, ∃ ε>0, ∀ {ι : Type*} [Fintype ι] {δ R : ℕ}, δ≤1 →
      ∀ (A : ℕ → Finset (Finset ι)) (B : Finset (Finset ι)),
      (∀ p : Nat.Primes, ∀ S∈A p, S.Nonempty) →
      (∀ p : Nat.Primes, (A p).card≤R) →
      (∀ S∈B, S.Nonempty) → B.card≤R → ∀ {y : ℕ}, 2≤y →
      (∀ p : Nat.Primes, y<(p:ℕ) → A p=B) →
      ∀ (u : ι → ℝ) {t : ℕ}, (∑ S∈B, (-1:ℤ)^S.card) = -(t:ℤ) →
      ∀ {L U s : ℝ}, 0<L → 0≤U → (∀ i, |u i|≤U) →
      (Fintype.card ι:ℝ)*(1+U)/L<ε →
      (∑ i, ‖frequencyW (u i)/(L:ℂ)‖)≤(y:ℝ)^(-s) →
      ‖(L:ℂ)^t*(∑' d : AllowedDivisorTuple A,
        tupleFourierCoefficient δ d.val (fun i => frequencyW (u i)/(L:ℂ))) -
        eulerGlobal δ A B (fun _ => 0)*familyKernel B (fun i => frequencyW (u i))‖ ≤
      ‖familyKernel B (fun i => frequencyW (u i))‖*
        (uniformEulerError R s y*(1+2^B.card*(B.card*(2*c*((Fintype.card ι:ℝ)*(1+U)/L))))+
         eulerGlobalMajorant R y*(2^B.card*(B.card*(2*c*((Fintype.card ι:ℝ)*(1+U)/L))))) := by
  obtain ⟨c,hc,ε,hε,hpole⟩ := eulerZeta_norm_contour_error
  refine ⟨c,hc,ε,hε,?_⟩
  intro ι _ δ R hδ A B hA hR hB hBR y hy hgen u t ht L U s hL hU hu hsmall hzsmall
  rw [tupleFourier_scaled_factorization hδ A B hA hR hB (by omega) hgen u ht hL]
  apply norm_mul_mul_sub_le
  · exact eulerGlobal_uniform_error hδ A B _
      (fun i => by simp [frequencyW,Complex.div_re]; positivity) hy hR hBR hgen hzsmall
  · exact norm_eulerGlobal_le hδ A B _ (by simp) (by omega) hR hBR hgen
  · exact hpole B hB u hL hU hu hsmall

theorem continuous_contourKernel {ι : Type*} [Fintype ι]
    (B : Finset (Finset ι)) (hB : ∀ S∈B, S.Nonempty) : Continuous (contourKernel B) := by
  unfold contourKernel familyKernel
  apply continuous_finsetProd
  intro S hS
  apply Continuous.zpow₀
  · apply continuous_finsetSum
    intro i _
    unfold frequencyW
    fun_prop
  · intro u
    exact Or.inl (frequencySum_ne_zero (hB S hS) (fun i => u i))

theorem contourKernel_norm_polynomial {ι : Type*} [Fintype ι]
    (B : Finset (Finset ι)) (hB : ∀ S∈B, S.Nonempty) (u : EuclideanSpace ℝ ι) :
    ‖contourKernel B u‖ ≤ ((max (Fintype.card ι) 1:ℕ):ℝ)^B.card*
      2^(B.card-1)*(1+‖u‖^B.card) := by
  apply (familyKernel_norm_polynomial B hB (fun i => u i) (norm_nonneg _)
    (fun i => by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le u i)).trans
  rw [mul_pow,mul_assoc]
  gcongr
  simpa only [one_pow] using add_pow_le (by norm_num : (0:ℝ)≤1) (norm_nonneg u) B.card

theorem schwartz_integrable_polynomial_majorant {ι : Type*} [Fintype ι]
    (Φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ) (k : ℕ) :
    Integrable (fun u => ‖Φ u‖*(1+‖u‖^k)) := by
  have hi := Φ.integrable.norm.add (SchwartzMap.integrable_pow_mul volume Φ k)
  apply hi.congr
  filter_upwards [] with u
  dsimp; ring

end LargePrimeGaps

end OAI
end

section
-- module Solutions.OAIW2_P344.PrimeGaps_ContourIntegrals
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

open Asymptotics

open scoped Classical

open scoped ContDiff

theorem integrable_schwartz_contourKernel {ι : Type*} [Fintype ι]
    (Φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ)
    (B : Finset (Finset ι)) (hB : ∀ S∈B, S.Nonempty) :
    Integrable (fun u => Φ u*contourKernel B u) := by
  have hm := (schwartz_integrable_polynomial_majorant Φ B.card).const_mul
    (((max (Fintype.card ι) 1:ℕ):ℝ)^B.card*2^(B.card-1))
  apply hm.mono' ((Φ.continuous.mul (continuous_contourKernel B hB)).aestronglyMeasurable)
  filter_upwards [] with u
  simp only [Pi.mul_apply]
  rw [norm_mul]
  calc
    _ ≤ ‖Φ u‖*(((max (Fintype.card ι) 1:ℕ):ℝ)^B.card*2^(B.card-1)*(1+‖u‖^B.card)) :=
      mul_le_mul_of_nonneg_left (contourKernel_norm_polynomial B hB u) (norm_nonneg _)
    _ = _ := by ring

theorem kernel_integral_on_error {ι : Type*} [Fintype ι]
    (Φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ)
    (B : Finset (Finset ι)) (hB : ∀ S∈B, S.Nonempty)
    (S : Set (EuclideanSpace ℝ ι)) (hS : MeasurableSet S)
    (f : EuclideanSpace ℝ ι → ℂ) (hf : IntegrableOn (fun u => Φ u*f u) S)
    (H : ℂ) {E : ℝ} (hE : 0≤E)
    (he : ∀ u∈S, ‖f u-H*contourKernel B u‖≤‖contourKernel B u‖*E) :
    ‖(∫ u in S, Φ u*f u)-H*(∫ u in S, Φ u*contourKernel B u)‖ ≤
      kernelAbsoluteConstant Φ B*E := by
  have hi := integrable_schwartz_contourKernel Φ B hB
  have hH : IntegrableOn (fun u => Φ u*(H*contourKernel B u)) S := by
    simpa only [mul_left_comm] using (hi.const_mul H).integrableOn (s:=S)
  have hiH : H*(∫ u in S, Φ u*contourKernel B u) =
      ∫ u in S, Φ u*(H*contourKernel B u) := by
    rw [← integral_const_mul]
    congr 1; ext u; ring
  rw [hiH,← integral_sub hf hH]
  calc
    _ ≤ ∫ u in S, ‖Φ u*f u-Φ u*(H*contourKernel B u)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ u in S, ‖Φ u*contourKernel B u‖*E := by
      apply integral_mono_ae (hf.sub hH).norm (hi.norm.mul_const E).integrableOn
      filter_upwards [ae_restrict_mem hS] with u hu
      simp only [Pi.sub_apply]
      rw [← mul_sub,norm_mul,norm_mul]
      nlinarith [mul_le_mul_of_nonneg_left (he u hu) (norm_nonneg (Φ u))]
    _ ≤ ∫ u, ‖Φ u*contourKernel B u‖*E :=
      setIntegral_le_integral (hi.norm.mul_const E) (by filter_upwards [] with u; positivity)
    _ = kernelAbsoluteConstant Φ B*E := by rw [integral_mul_const]; rfl

theorem eulerGlobalMajorant_div_rpow_tendsto (R : ℕ) {s : ℝ} (hs : 0<s) :
    Tendsto (fun y : ℕ => eulerGlobalMajorant R y/(y:ℝ)^s) atTop (𝓝 0) := by
  let c : ℝ := Real.exp 1
  let a : ℝ := 4*R*c
  let M : ℝ := Real.exp (a+genericEulerConstant R)
  have hlim := (tendsto_log_rpow_div_nat_rpow a hs).const_mul M
  apply squeeze_zero' _ _ (by simpa only [mul_zero] using hlim)
  · filter_upwards [] with y
    unfold eulerGlobalMajorant
    positivity
  · have ht := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
    filter_upwards [eventually_prime_reciprocal_bound,
      ht.eventually_ge_atTop 1,
      (tendsto_natCast_atTop_atTop (R:=ℝ)).eventually_ge_atTop 1] with y hr hl hy
    change 1≤Real.log (y:ℝ) at hl
    have hly : 0<Real.log (y:ℝ) := by linarith
    have hr' : primeReciprocalPrefix y ≤ c*(1+Real.log (Real.log y)) := by
      simpa only [primeReciprocalPrefix_eq,c] using hr
    have hK : genericEulerConstant R/(y:ℝ)≤genericEulerConstant R :=
      div_le_self (genericEulerConstant_nonneg R) hy
    have hb : eulerGlobalMajorant R y ≤ M*(Real.log (y:ℝ))^a := by
      calc
        _ ≤ Real.exp (4*R*(c*(1+Real.log (Real.log y)))+genericEulerConstant R) := by
          unfold eulerGlobalMajorant
          gcongr
        _ = _ := by
          rw [Real.rpow_def_of_pos hly]
          dsimp only [M,a]
          rw [← Real.exp_add]
          congr 1
          ring
    calc
      _ ≤ (M*(Real.log (y:ℝ))^a)/(y:ℝ)^s :=
        div_le_div_of_nonneg_right hb (Real.rpow_nonneg (by positivity) _)
      _ = M*((Real.log (y:ℝ))^a/(y:ℝ)^s) := by ring

theorem uniformCoreError_tendsto (R : ℕ) (c : ℝ) {s : ℝ} (hs : 0<s) :
    Tendsto (uniformCoreError R c s) atTop (𝓝 0) := by
  have hy : Tendsto (fun y : ℕ => (y:ℝ)^(-s)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop hs).comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  have h₁ := (uniformEulerError_tendsto R hs).mul
    ((tendsto_const_nhds (x:=(1:ℝ))).add (hy.const_mul (2^R*(R*(2*c)))))
  have h₂ := (eulerGlobalMajorant_div_rpow_tendsto R hs).mul_const (2^R*(R*(2*c)))
  have he : (fun y : ℕ => eulerGlobalMajorant R y/(y:ℝ)^s*(2^R*(R*(2*c)))) =
      (fun y : ℕ => eulerGlobalMajorant R y*(2^R*(R*(2*c)))*(y:ℝ)^(-s)) := by
    ext y
    rw [Real.rpow_neg (by positivity : (0:ℝ)≤y)]
    ring
  rw [he] at h₂
  unfold uniformCoreError
  simpa only [zero_mul,mul_zero,add_zero,zero_add] using h₁.add h₂

theorem integrable_pow_mul_schwartz_contourKernel {ι : Type*} [Fintype ι]
    (Φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ)
    (B : Finset (Finset ι)) (hB : ∀ S∈B, S.Nonempty) (k : ℕ) :
    Integrable (fun u => ‖u‖^k*‖Φ u*contourKernel B u‖) := by
  have hi := ((SchwartzMap.integrable_pow_mul volume Φ k).add
    (SchwartzMap.integrable_pow_mul volume Φ (k+B.card))).const_mul
    (((max (Fintype.card ι) 1:ℕ):ℝ)^B.card*2^(B.card-1))
  apply hi.mono' ((continuous_norm.pow k).mul
    ((Φ.continuous.mul (continuous_contourKernel B hB)).norm)).aestronglyMeasurable
  filter_upwards [] with u
  simp only [Pi.mul_apply,Pi.pow_apply,Pi.add_apply]
  rw [Real.norm_of_nonneg (by positivity),norm_mul]
  calc
    _ ≤ ‖u‖^k*(‖Φ u‖*((((max (Fintype.card ι) 1:ℕ):ℝ)^B.card*
      2^(B.card-1))*(1+‖u‖^B.card))) := by
      gcongr; exact contourKernel_norm_polynomial B hB u
    _ = _ := by rw [pow_add]; ring

theorem norm_integral_norm_tail_le {V : Type*} [NormedAddCommGroup V]
    [MeasurableSpace V] [BorelSpace V] (μ : Measure V) (f : V → ℂ)
    (hf : Integrable f μ) (k : ℕ) (hk : Integrable (fun u => ‖u‖^k*‖f u‖) μ)
    {U : ℝ} (hU : 0<U) :
    ‖∫ u in {u | U<‖u‖}, f u ∂μ‖ ≤ (∫ u, ‖u‖^k*‖f u‖ ∂μ)/U^k := by
  let S : Set V := {u | U<‖u‖}
  have hS : MeasurableSet S := measurableSet_lt measurable_const continuous_norm.measurable
  have hbound : ∀ᵐ u ∂μ.restrict S, ‖f u‖≤(U^k)⁻¹*(‖u‖^k*‖f u‖) := by
    filter_upwards [ae_restrict_mem hS] with u hu
    have hp : U^k≤‖u‖^k := pow_le_pow_left₀ hU.le hu.le k
    have hdiv : 1≤(U^k)⁻¹*‖u‖^k := by
      rw [← div_eq_inv_mul]
      exact (one_le_div (pow_pos hU k)).mpr hp
    calc
      _ ≤ ((U^k)⁻¹*‖u‖^k)*‖f u‖ := by nlinarith [norm_nonneg (f u)]
      _ = _ := by ring
  calc
    _ ≤ ∫ u in S, ‖f u‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ u in S, (U^k)⁻¹*(‖u‖^k*‖f u‖) ∂μ :=
      integral_mono_ae hf.integrableOn.norm ((hk.const_mul _).integrableOn) hbound
    _ ≤ ∫ u, (U^k)⁻¹*(‖u‖^k*‖f u‖) ∂μ :=
      setIntegral_le_integral (hk.const_mul _) (by filter_upwards [] with u; positivity)
    _ = _ := by rw [integral_const_mul]; ring

theorem kernel_integral_tail_bound {ι : Type*} [Fintype ι]
    (Φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ)
    (B : Finset (Finset ι)) (hB : ∀ S∈B, S.Nonempty) (k : ℕ)
    {U : ℝ} (hU : 0<U) :
    ‖∫ u in {u | U<‖u‖}, Φ u*contourKernel B u‖ ≤
      (∫ u, ‖u‖^k*‖Φ u*contourKernel B u‖)/U^k :=
  norm_integral_norm_tail_le volume _ (integrable_schwartz_contourKernel Φ B hB) k
    (integrable_pow_mul_schwartz_contourKernel Φ B hB k) hU

theorem uniformEulerError_nonneg (R : ℕ) (s : ℝ) {y : ℕ} (hy : 1≤y) :
    0≤uniformEulerError R s y := by
  have hl : 0≤Real.log (y:ℝ) := Real.log_nonneg (by exact_mod_cast hy)
  have hp := primeReciprocalPrefix_nonneg y
  have he : 0≤Real.exp (genericEulerConstant R/(y:ℝ))-1 :=
    sub_nonneg.mpr (Real.one_le_exp (by
      exact div_nonneg (genericEulerConstant_nonneg R) (by positivity)))
  unfold uniformEulerError
  positivity

theorem uniformCoreError_nonneg (R : ℕ) {c : ℝ} (hc : 0≤c) (s : ℝ)
    {y : ℕ} (hy : 1≤y) : 0≤uniformCoreError R c s y := by
  have he := uniformEulerError_nonneg R s hy
  have hm : 0≤eulerGlobalMajorant R y := (Real.exp_pos _).le
  unfold uniformCoreError
  positivity

theorem frequencyW_div_norm_sum_le {ι : Type*} [Fintype ι] (u : ι → ℝ)
    {L U : ℝ} (hL : 0<L) (hu : ∀ i, |u i|≤U) :
    (∑ i, ‖frequencyW (u i)/(L:ℂ)‖) ≤ (Fintype.card ι:ℝ)*(1+U)/L := by
  calc
    _ ≤ ∑ _i : ι, (1+U)/L := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hL]
      apply div_le_div_of_nonneg_right _ hL.le
      exact (frequencyW_norm (u i)).trans (by linarith [hu i])
    _ = _ := by simp; ring

theorem tupleFourier_scaled_uniform_core_error :
    ∃ c>0, ∃ ε>0, ∀ {ι : Type*} [Fintype ι] {δ R : ℕ}, δ≤1 →
      ∀ (A : ℕ → Finset (Finset ι)) (B : Finset (Finset ι)),
      (∀ p : Nat.Primes, ∀ S∈A p, S.Nonempty) →
      (∀ p : Nat.Primes, (A p).card≤R) →
      (∀ S∈B, S.Nonempty) → B.card≤R → ∀ {y : ℕ}, 2≤y →
      (∀ p : Nat.Primes, y<(p:ℕ) → A p=B) →
      ∀ (u : ι → ℝ) {t : ℕ}, (∑ S∈B, (-1:ℤ)^S.card) = -(t:ℤ) →
      ∀ {L U s : ℝ}, 0<L → 0≤U → (∀ i, |u i|≤U) →
      (Fintype.card ι:ℝ)*(1+U)/L<ε →
      (Fintype.card ι:ℝ)*(1+U)/L≤(y:ℝ)^(-s) →
      ‖(L:ℂ)^t*(∑' d : AllowedDivisorTuple A,
        tupleFourierCoefficient δ d.val (fun i => frequencyW (u i)/(L:ℂ))) -
        eulerGlobal δ A B (fun _ => 0)*familyKernel B (fun i => frequencyW (u i))‖ ≤
      ‖familyKernel B (fun i => frequencyW (u i))‖*uniformCoreError R c s y := by
  obtain ⟨c,hc,ε,hε,hcore⟩ := tupleFourier_scaled_core_error
  refine ⟨c,hc,ε,hε,?_⟩
  intro ι _ δ R hδ A B hA hR hB hBR y hy hgen u t ht L U s hL hU hu hsmall hzsmall
  apply (hcore hδ A B hA hR hB hBR hy hgen u ht hL hU hu hsmall
    ((frequencyW_div_norm_sum_le u hL hu).trans hzsmall)).trans
  have hE := uniformEulerError_nonneg R s (show 1≤y by omega)
  have hCB : (B.card:ℝ)≤R := by exact_mod_cast hBR
  have h2 : (2:ℝ)^B.card≤2^R := pow_le_pow_right₀ (by norm_num) hBR
  have hζ : 2^B.card*(B.card*(2*c*((Fintype.card ι:ℝ)*(1+U)/L))) ≤
      (2^R*(R*(2*c)))*(y:ℝ)^(-s) := by
    calc
      _ ≤ 2^R*(R*(2*c*(y:ℝ)^(-s))) := by gcongr
      _ = _ := by ring
  unfold uniformCoreError
  have hM : 0≤eulerGlobalMajorant R y := (Real.exp_pos _).le
  have hmul := mul_le_mul_of_nonneg_left hζ hM
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply add_le_add
  · exact mul_le_mul_of_nonneg_left (add_le_add_right hζ 1) hE
  · calc
      _ ≤ eulerGlobalMajorant R y*((2^R*(R*(2*c)))*(y:ℝ)^(-s)) := hmul
      _ = _ := by ring

theorem integrable_schwartz_tupleFourier {ι : Type*} [Fintype ι] {δ R : ℕ}
    (hδ : δ≤1) (A : ℕ → Finset (Finset ι)) {L : ℝ} (hL : 0<L)
    (hA : ∀ p : Nat.Primes, ∀ S∈A p, S.Nonempty)
    (hR : ∀ p : Nat.Primes, (A p).card≤R)
    (Φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ) :
    Integrable (fun u => Φ u * (∑' d : AllowedDivisorTuple A,
      tupleFourierCoefficient δ d.val (fourierContour L u))) := by
  exact Φ.integrable.mul_bdd
    (continuous_tupleFourier_tsum hδ A hL hA hR).aestronglyMeasurable
    (Filter.Eventually.of_forall (tupleFourier_tsum_norm_bound hδ A hL hA hR))

theorem integral_core_tail_error {V : Type*} [MeasurableSpace V]
    (μ : Measure V) (f g : V → ℂ) (hf : Integrable f μ) (hg : Integrable g μ)
    (S : Set V) (hS : MeasurableSet S) (H : ℂ) {E : ℝ}
    (he : ‖(∫ u in S, f u ∂μ)-H*(∫ u in S, g u ∂μ)‖≤E) :
    ‖(∫ u, f u ∂μ)-H*(∫ u, g u ∂μ)‖ ≤
      E + ‖∫ u in Sᶜ, f u ∂μ‖ + ‖H‖*‖∫ u in Sᶜ, g u ∂μ‖ := by
  rw [← integral_add_compl hS hf,← integral_add_compl hS hg]
  calc
    _ = ‖((∫ u in S, f u ∂μ)-H*(∫ u in S, g u ∂μ)) +
      ((∫ u in Sᶜ, f u ∂μ)-H*(∫ u in Sᶜ, g u ∂μ))‖ := by congr 1; ring
    _ ≤ ‖(∫ u in S, f u ∂μ)-H*(∫ u in S, g u ∂μ)‖ +
      ‖(∫ u in Sᶜ, f u ∂μ)-H*(∫ u in Sᶜ, g u ∂μ)‖ := norm_add_le _ _
    _ ≤ E + (‖∫ u in Sᶜ, f u ∂μ‖ + ‖H‖*‖∫ u in Sᶜ, g u ∂μ‖) := by
      apply add_le_add he
      simpa only [norm_mul] using norm_sub_le (∫ u in Sᶜ, f u ∂μ)
        (H*(∫ u in Sᶜ, g u ∂μ))
    _ = _ := by ring

theorem tupleFourier_integral_uniform_error :
    ∃ c>0, ∃ ε>0, ∀ {ι : Type*} [Fintype ι] {δ R : ℕ}, δ≤1 →
      ∀ (A : ℕ → Finset (Finset ι)) (B : Finset (Finset ι)),
      (∀ p : Nat.Primes, ∀ S∈A p, S.Nonempty) →
      (∀ p : Nat.Primes, (A p).card≤R) →
      (∀ S∈B, S.Nonempty) → B.card≤R → ∀ {y : ℕ}, 2≤y →
      (∀ p : Nat.Primes, y<(p:ℕ) → A p=B) →
      ∀ (Φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ) {t : ℕ},
      (∑ S∈B, (-1:ℤ)^S.card) = -(t:ℤ) →
      ∀ {L U s : ℝ}, 0<L → 0<U →
      (Fintype.card ι:ℝ)*(1+U)/L<ε →
      (Fintype.card ι:ℝ)*(1+U)/L≤(y:ℝ)^(-s) → ∀ k₁ k₂ : ℕ,
      ‖(L:ℂ)^t*(∫ u, Φ u*(∑' d : AllowedDivisorTuple A,
        tupleFourierCoefficient δ d.val (fourierContour L u))) -
        eulerGlobal δ A B (fun _ => 0)*kernelConstant Φ B‖ ≤
      kernelAbsoluteConstant Φ B*uniformCoreError R c s y +
      L^t*(Real.exp ((2*R)*Real.log (riemannZeta ((1+L⁻¹:ℝ):ℂ)).re)/U^k₁)*
        (∫ u, ‖u‖^k₁*‖Φ u‖) +
      eulerGlobalMajorant R y*(∫ u, ‖u‖^k₂*‖Φ u*contourKernel B u‖)/U^k₂ := by
  obtain ⟨c,hc,ε,hε,hcore⟩ := tupleFourier_scaled_uniform_core_error
  refine ⟨c,hc,ε,hε,?_⟩
  intro ι _ δ R hδ A B hA hR hB hBR y hy hgen Φ t ht L U s hL hU hsmall hysmall k₁ k₂
  let T := fun u : EuclideanSpace ℝ ι => ∑' d : AllowedDivisorTuple A,
    tupleFourierCoefficient δ d.val (fourierContour L u)
  let S : Set (EuclideanSpace ℝ ι) := {u | ‖u‖≤U}
  have hS : MeasurableSet S := measurableSet_le continuous_norm.measurable measurable_const
  have hSc : Sᶜ={u | U<‖u‖} := by ext u; simp [S]
  have hT : Integrable (fun u => Φ u*T u) := integrable_schwartz_tupleFourier hδ A hL hA hR Φ
  have hcT : Integrable (fun u => Φ u*((L:ℂ)^t*T u)) := by
    simpa only [mul_left_comm] using hT.const_mul ((L:ℂ)^t)
  have hK := integrable_schwartz_contourKernel Φ B hB
  have hpoint : ∀ u∈S, ‖(L:ℂ)^t*T u-eulerGlobal δ A B (fun _ => 0)*
      contourKernel B u‖≤‖contourKernel B u‖*uniformCoreError R c s y := by
    intro u hu
    have hui : ∀ i, |u i|≤U := by
      intro i
      have hh : |u i|≤‖u‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le u i
      exact hh.trans hu
    exact hcore hδ A B hA hR hB hBR hy hgen (fun i => u i) ht hL hU.le hui hsmall hysmall
  have he := kernel_integral_on_error Φ B hB S hS (fun u => (L:ℂ)^t*T u)
    hcT.integrableOn (eulerGlobal δ A B (fun _ => 0))
    (uniformCoreError_nonneg R hc.le s (y:=y) (by omega)) hpoint
  have hall := integral_core_tail_error volume (fun u => Φ u*((L:ℂ)^t*T u))
    (fun u => Φ u*contourKernel B u) hcT hK S hS
    (eulerGlobal δ A B (fun _ => 0)) he
  have hid : ∀ D : Set (EuclideanSpace ℝ ι),
      (∫ u in D, Φ u*((L:ℂ)^t*T u)) = (L:ℂ)^t*∫ u in D, Φ u*T u := by
    intro D
    rw [← integral_const_mul]
    congr 1; ext u; ring
  have hidall : (∫ u, Φ u*((L:ℂ)^t*T u))=(L:ℂ)^t*∫ u, Φ u*T u := by
    rw [← integral_const_mul]
    congr 1; ext u; ring
  rw [hidall,hid,hSc] at hall
  apply hall.trans
  rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hL]
  apply add_le_add
  · apply add_le_add_right
    have hb := tupleFourier_schwartz_tail hδ A hL hU hA hR Φ k₁
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hb (pow_nonneg hL.le t)
  · have hH := norm_eulerGlobal_le hδ A B (fun _ => (0:ℂ)) (by intro i; simp)
      (y:=y) (by omega) hR hBR hgen
    have hb := kernel_integral_tail_bound Φ B hB k₂ hU
    calc
      _ ≤ eulerGlobalMajorant R y*((∫ u, ‖u‖^k₂*‖Φ u*contourKernel B u‖)/U^k₂) :=
        mul_le_mul hH hb (norm_nonneg _) (Real.exp_pos _).le
      _ = _ := by ring

theorem densityCoreExponent_pos {b : ℕ} (hb : 0<b) : 0<densityCoreExponent b := by
  unfold densityCoreExponent
  positivity

theorem densityCutoff_tendsto {b : ℕ} (hb : 0<b) :
    Tendsto (densityCutoff b) atTop atTop :=
  tendsto_nat_floor_atTop.comp (tendsto_pow_atTop (by omega : b≠0))

theorem sqrt_core_rate (C : ℝ) {L : ℝ} (hL : 0<L) :
    C*(1+Real.sqrt L)/L = C*(L^(-1:ℝ)+L^(-(1/2):ℝ)) := by
  have hp : L^(1/2:ℝ)/L = L^(-(1/2):ℝ) := by
    calc
      _ = L^(1/2:ℝ)/L^(1:ℝ) := by rw [Real.rpow_one]
      _ = L^((1/2:ℝ)-1) := (Real.rpow_sub hL _ _).symm
      _ = _ := by norm_num
  rw [Real.sqrt_eq_rpow,Real.rpow_neg_one,← hp]
  ring

theorem sqrt_core_rate_tendsto (C : ℝ) :
    Tendsto (fun L : ℝ => C*(1+Real.sqrt L)/L) atTop (𝓝 0) := by
  have h₁ := tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1)
  have h₂ := tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1/2)
  have hh := (h₁.add h₂).const_mul C
  simp only [add_zero,mul_zero] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with L hL
  exact (sqrt_core_rate C hL).symm

theorem sqrt_core_quarter_rate (C : ℝ) {L : ℝ} (hL : 0<L) :
    (C*(1+Real.sqrt L)/L)/(L^(-(1/4):ℝ)) =
      C*(L^(-(3/4):ℝ)+L^(-(1/4):ℝ)) := by
  rw [sqrt_core_rate C hL,mul_div_assoc,add_div,← Real.rpow_sub hL,← Real.rpow_sub hL]
  norm_num

theorem eventually_sqrt_core_le_quarter (C : ℝ) :
    ∀ᶠ L : ℝ in atTop, C*(1+Real.sqrt L)/L≤L^(-(1/4):ℝ) := by
  have h₁ := tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<3/4)
  have h₂ := tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1/4)
  have hh := (h₁.add h₂).const_mul C
  simp only [add_zero,mul_zero] at hh
  filter_upwards [hh.eventually_lt_const zero_lt_one,eventually_gt_atTop (0:ℝ)] with L h hL
  apply (div_le_one (Real.rpow_pos_of_pos hL _)).mp
  rw [sqrt_core_quarter_rate C hL]
  exact h.le

theorem densityCutoff_neg_rpow {b : ℕ} (hb : 0<b) {L : ℝ} (hL : 1≤L) :
    L^(-(1/4):ℝ) ≤ (densityCutoff b L:ℝ)^(-densityCoreExponent b) := by
  have hLb : 1≤L^b := one_le_pow₀ hL
  have hy : 0<(densityCutoff b L:ℝ) := by
    have : 1≤densityCutoff b L := (Nat.one_le_floor_iff _).mpr hLb
    exact_mod_cast (show 0<densityCutoff b L by omega)
  have hyle : (densityCutoff b L:ℝ)≤L^b := Nat.floor_le (by positivity)
  have hb0 : (b:ℝ)≠0 := by exact_mod_cast hb.ne'
  have hexp : (b:ℝ)*(-densityCoreExponent b)=-(1/4:ℝ) := by
    unfold densityCoreExponent
    field_simp
  calc
    _ = L^((b:ℝ)*(-densityCoreExponent b)) := by rw [hexp]
    _ = (L^b)^(-densityCoreExponent b) := by
      rw [Real.rpow_mul (by linarith),Real.rpow_natCast]
    _ ≤ _ := Real.rpow_le_rpow_of_nonpos hy hyle (by
      have := densityCoreExponent_pos hb; linarith)

theorem eventually_density_core_scale {b : ℕ} (hb : 0<b) (C : ℝ) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ L : ℝ in atTop, 0<L ∧ 2≤densityCutoff b L ∧
      C*(1+Real.sqrt L)/L<ε ∧
      C*(1+Real.sqrt L)/L≤(densityCutoff b L:ℝ)^(-densityCoreExponent b) := by
  filter_upwards [eventually_ge_atTop (1:ℝ),
    (densityCutoff_tendsto hb).eventually (eventually_ge_atTop 2),
    (sqrt_core_rate_tendsto C).eventually_lt_const hε,
    eventually_sqrt_core_le_quarter C] with L hL hy hεL hbound
  exact ⟨by linarith,hy,hεL,hbound.trans (densityCutoff_neg_rpow hb hL)⟩

theorem eventually_nat_rate_le_index (a : ℕ → ℝ)
    (ha : Tendsto (fun y : ℕ => a y/(y:ℝ)) atTop (𝓝 0)) :
    ∀ᶠ y : ℕ in atTop, a y≤y := by
  filter_upwards [ha.eventually_lt_const zero_lt_one,eventually_ge_atTop 1] with y h hy
  exact ((div_le_one (by exact_mod_cast hy : 0<(y:ℝ))).mp h.le)

theorem eventually_rate_densityCutoff_le_pow (a : ℕ → ℝ)
    (ha : Tendsto (fun y : ℕ => a y/(y:ℝ)) atTop (𝓝 0))
    {b : ℕ} (hb : 0<b) :
    ∀ᶠ L : ℝ in atTop, a (densityCutoff b L)≤L^b := by
  filter_upwards [(densityCutoff_tendsto hb).eventually (eventually_nat_rate_le_index a ha),
    eventually_ge_atTop (0:ℝ)] with L h hL
  exact h.trans (Nat.floor_le (pow_nonneg hL b))

theorem sqrt_pow_even {L : ℝ} (hL : 0≤L) (n : ℕ) :
    (Real.sqrt L)^(2*n) = L^n := by rw [pow_mul,Real.sq_sqrt hL]

theorem scaled_polynomial_tail {L Z I : ℝ} (hL : 0<L) (hI : 0≤I) (R t : ℕ)
    (hZ : Z≤((3/2:ℝ)*L)^(2*R)) :
    L^t*(Z/(Real.sqrt L)^(2*(2*R+t+1)))*I≤((3/2:ℝ)^(2*R)*I)/L := by
  rw [sqrt_pow_even hL.le]
  calc
    _ ≤ L^t*((((3/2:ℝ)*L)^(2*R))/L^(2*R+t+1))*I := by gcongr
    _ = _ := by rw [mul_pow,pow_add,pow_add,pow_one]; field_simp

theorem kernel_polynomial_tail {L Z I : ℝ} (hL : 0<L) (hI : 0≤I) (b : ℕ)
    (hZ : Z≤L^b) :
    Z*I/(Real.sqrt L)^(2*(b+1))≤I/L := by
  rw [sqrt_pow_even hL.le]
  calc
    _ ≤ L^b*I/L^(b+1) := by gcongr
    _ = _ := by rw [pow_succ]; field_simp

theorem tupleFourier_integral_uniform_asymptotic {ι : Type*} [Fintype ι]
    (Φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ) (B : Finset (Finset ι))
    (hB : ∀ S∈B, S.Nonempty) (R t b : ℕ) (hBR : B.card≤R) (hb : 0<b)
    (ht : (∑ S∈B, (-1:ℤ)^S.card) = -(t:ℤ)) :
    ∃ E : ℝ → ℝ, Tendsto E atTop (𝓝 0) ∧
      ∀ᶠ L : ℝ in atTop, ∀ δ : ℕ, δ≤1 → ∀ A : ℕ → Finset (Finset ι),
      (∀ p : Nat.Primes, ∀ S∈A p, S.Nonempty) →
      (∀ p : Nat.Primes, (A p).card≤R) →
      (∀ p : Nat.Primes, densityCutoff b L<(p:ℕ) → A p=B) →
      ‖(L:ℂ)^t*(∫ u, Φ u*(∑' d : AllowedDivisorTuple A,
        tupleFourierCoefficient δ d.val (fourierContour L u))) -
        eulerGlobal δ A B (fun _ => 0)*kernelConstant Φ B‖ ≤ E L := by
  obtain ⟨c,hc,ε,hε,hformula⟩ := tupleFourier_integral_uniform_error
  obtain ⟨L₀,hL₀,hz⟩ := zeta_contour_majorant_polynomial
  let I₁ : ℝ := (3/2:ℝ)^(2*R)*(∫ u, ‖u‖^(2*(2*R+t+1))*‖Φ u‖)
  let I₂ : ℝ := ∫ u, ‖u‖^(2*(b+1))*‖Φ u*contourKernel B u‖
  let E : ℝ → ℝ := fun L => kernelAbsoluteConstant Φ B*
    uniformCoreError R c (densityCoreExponent b) (densityCutoff b L) + I₁/L + I₂/L
  refine ⟨E,?_,?_⟩
  · have hcore := ((uniformCoreError_tendsto R c (densityCoreExponent_pos hb)).comp
      (densityCutoff_tendsto hb)).const_mul (kernelAbsoluteConstant Φ B)
    have h₁ : Tendsto (fun L : ℝ => I₁/L) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
    have h₂ : Tendsto (fun L : ℝ => I₂/L) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
    simpa only [mul_zero,add_zero,Function.comp_def,E] using (hcore.add h₁).add h₂
  · have hM : Tendsto (fun y : ℕ => eulerGlobalMajorant R y/(y:ℝ)) atTop (𝓝 0) := by
      simpa only [Real.rpow_one] using eulerGlobalMajorant_div_rpow_tendsto R zero_lt_one
    filter_upwards [eventually_density_core_scale hb (Fintype.card ι:ℝ) hε,
      eventually_rate_densityCutoff_le_pow (eulerGlobalMajorant R) hM hb,
      eventually_ge_atTop L₀] with L hscale hmajor hLL₀
    intro δ hδ A hA hR hgen
    obtain ⟨hL,hy,hsmall,hysmall⟩ := hscale
    have hbound := hformula hδ A B hA hR hB hBR hy hgen Φ ht hL
      (Real.sqrt_pos.mpr hL) hsmall hysmall (2*(2*R+t+1)) (2*(b+1))
    apply hbound.trans
    apply add_le_add
    · apply add_le_add_right
      exact scaled_polynomial_tail hL (integral_nonneg (fun _ => by positivity)) R t (hz L hLL₀ R)
    · exact kernel_polynomial_tail hL (integral_nonneg (fun _ => by positivity)) b hmajor

end LargePrimeGaps

end OAI
end

section
-- module Solutions.OAIW2_P344.PrimeGaps_LaplaceTransform
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

open Asymptotics

open scoped Classical

open scoped ContDiff

theorem shiftFamily_nonempty {ι : Type*} [Fintype ι] (b : ι → ℤ) :
    ∀ S∈shiftFamily b, S.Nonempty := by
  intro S hS
  exact ((mem_fiberSubsetFamily b (Finset.univ.image b) S).mp hS).1

theorem residueFamily_nonempty {ι : Type*} [Fintype ι] (b : ι → ℤ) (p : ℕ) :
    ∀ S∈residueFamily b p, S.Nonempty := by
  intro S hS
  exact ((mem_fiberSubsetFamily _ _ S).mp hS).1

theorem shiftFamily_sign_sum {ι : Type*} [Fintype ι] (b : ι → ℤ) :
    (∑ S∈shiftFamily b, (-1:ℤ)^S.card) = -((Finset.univ.image b).card:ℤ) := by
  apply fiberSubsetFamily_sign_sum
  intro r hr
  obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hr
  exact ⟨i,hi⟩

theorem unmarked_analyticDensity_uniform_asymptotic {ι : Type*} [Fintype ι]
    (F : EuclideanSpace ℝ ι → ℂ) (hF : HasCompactSupport F) (hFs : ContDiff ℝ ∞ F)
    (B : Finset (Finset ι)) (hB : ∀ S∈B, S.Nonempty) (t β : ℕ) (hβ : 0<β)
    (ht : (∑ S∈B, (-1:ℤ)^S.card) = -(t:ℤ)) :
    ∃ E : ℝ → ℝ, Tendsto E atTop (𝓝 0) ∧
      ∀ᶠ L : ℝ in atTop, ∀ b : ι → ℤ, shiftFamily b=B → ∀ D : ℕ,
      (∀ i, (b i).natAbs≤D) → 2*D≤densityCutoff β L →
      ‖(L:ℂ)^t*analyticDensity 0 (residueFamily b) L F -
        (singularSeries (Finset.univ.image b):ℂ)*
          kernelConstant (sourceFourier (fourierCoordinateSum ι) F hF hFs) B‖ ≤ E L := by
  obtain ⟨E,hE,hbound⟩ := tupleFourier_integral_uniform_asymptotic
    (sourceFourier (fourierCoordinateSum ι) F hF hFs) B hB
    (2^Fintype.card ι) t β (subsetFamily_card_le B) hβ ht
  refine ⟨E,hE,?_⟩
  filter_upwards [hbound,eventually_gt_atTop (0:ℝ)] with L hbound hL
  intro b hb D hD hDL
  have hA := fun p : Nat.Primes => residueFamily_nonempty b p
  have hR := fun p : Nat.Primes => subsetFamily_card_le (residueFamily b p)
  have hgen : ∀ p : Nat.Primes, densityCutoff β L<(p:ℕ) → residueFamily b p=B := by
    intro p hp
    exact (residueFamily_generic_of_bound b hD (hDL.trans_lt hp)).trans hb
  have h := hbound 0 (by omega) (residueFamily b) hA hR hgen
  rw [← analyticDensity_eq_integral (by omega) (residueFamily b) hL hA hR F hF hFs] at h
  rw [← hb,unmarked_eulerGlobal_zero] at h
  simpa only [hb] using h

theorem unmarked_average_uniform_asymptotic {n : ℕ}
    (F : (Fin (n+1) → ℝ) → ℝ) (rho : ℝ)
    (hrho : 0≤rho) (hrho1 : rho<1) (hbudget : HasBudget F rho)
    (hF : HasCompactSupport (fun v : EuclideanSpace ℝ (Fin (n+1)) => (F v.ofLp:ℂ)))
    (hFs : ContDiff ℝ ∞ (fun v : EuclideanSpace ℝ (Fin (n+1)) => (F v.ofLp:ℂ)))
    (M : ℝ) (hM : 0≤M) (hbound : ∀ v, (∀ i, 0≤v i) → |F v|≤M)
    (B : Finset (Finset (Fin (n+1)))) (hB : ∀ S∈B, S.Nonempty)
    (t β : ℕ) (hβ : 0<β) (ht : (∑ S∈B, (-1:ℤ)^S.card) = -(t:ℤ)) :
    ∃ E : ℕ → ℝ, Tendsto E atTop (𝓝 0) ∧
      ∀ᶠ X : ℕ in atTop, ∀ b : Fin (n+1) → ℕ,
      shiftFamily (fun i => (b i:ℤ))=B → ∀ D : ℕ,
      (∀ i, b i≤D) → 2*D≤densityCutoff β (Real.log X) →
      ‖(Real.log X:ℂ)^t*(average X (fun m => divisorSum X F m b):ℂ) -
        (singularSeries (Finset.univ.image fun i => (b i:ℤ)):ℂ)*
          kernelConstant (sourceFourier (fourierCoordinateSum (Fin (n+1)))
            (fun v => (F v.ofLp:ℂ)) hF hFs) B‖ ≤ E X := by
  obtain ⟨E,hE,hEbound⟩ := unmarked_analyticDensity_uniform_asymptotic
    (fun v : EuclideanSpace ℝ (Fin (n+1)) => (F v.ofLp:ℂ)) hF hFs B hB t β hβ ht
  let err : ℝ → ℝ := fun L => (2*M*(1+rho)^n)*L^(n+t)*Real.exp (-(1-rho)*L)
  have herr : Tendsto err atTop (𝓝 0) := by
    have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
      (n+t:ℕ) (1-rho) (by linarith)).const_mul (2*M*(1+rho)^n)
    simpa only [Real.rpow_natCast,mul_zero,mul_assoc,err] using h
  have hlog : Tendsto (fun X : ℕ => Real.log (X:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  refine ⟨fun X => err (Real.log X)+E (Real.log X),?_,?_⟩
  · simpa only [Function.comp_def,add_zero] using (herr.comp hlog).add (hE.comp hlog)
  filter_upwards [hlog.eventually hEbound,eventually_ge_atTop 2,
    hlog.eventually (eventually_ge_atTop (1:ℝ))] with X hEX hX hL
  intro b hb D hD hDL
  have hb' : ∀ i, ((b i:ℤ)).natAbs≤D := by simpa only [Int.natAbs_natCast] using hD
  have hden := hEX (fun i => (b i:ℤ)) hb D hb' hDL
  rw [analyticDensity_eq_unmarkedDensitySum hX hbudget b] at hden
  have hcomp : ‖(Real.log X:ℂ)^t*(average X (fun m => divisorSum X F m b):ℂ)-
      (Real.log X:ℂ)^t*(unmarkedDensitySum X F rho b:ℂ)‖ ≤ err (Real.log X) := by
    rw [← mul_sub,← Complex.ofReal_sub,norm_mul,norm_pow,Complex.norm_real,
      Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (by linarith : 0≤Real.log X)]
    have hh := mul_le_mul_of_nonneg_left
      (unmarked_arithmetic_error_exponential hX hL hrho hbudget hM hbound b)
      (pow_nonneg (by linarith : 0≤Real.log X) t)
    convert hh using 1
    all_goals first | rfl | (simp only [err,pow_add]; ring)
  apply le_trans ?_ (add_le_add hcomp hden)
  simpa only [dist_eq_norm] using (dist_triangle
    ((Real.log X:ℂ)^t*(average X (fun m => divisorSum X F m b):ℂ))
    ((Real.log X:ℂ)^t*(unmarkedDensitySum X F rho b:ℂ)) _)

open Topology

open scoped Convolution ContDiff Pointwise

end LargePrimeGaps

end OAI
end

section
-- module Solutions.OAIW2_P344.PrimeGaps_CumulativeProfiles
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

open Asymptotics

open scoped Classical

open scoped ContDiff

open Topology

open scoped Convolution ContDiff Pointwise

theorem cumulativeExtension_tail {ι : Type*} [Fintype ι]
    (T : ℝ) (f : EuclideanSpace ℝ ι → ℝ)
    (hf : ∀ y, f y≠0 → ∀ i, y i≤T)
    (v : EuclideanSpace ℝ ι) (hv : ∀ i, 0≤v i) :
    cumulativeExtension T f v = cumulativeTail f v := by
  have hs : MeasurableSet {y : EuclideanSpace ℝ ι | ∀ i, v i≤y i} := by
    rw [Set.ofPred_forall]
    exact (isClosed_iInter fun i => isClosed_le (continuous_const (y := v i)) (PiLp.continuous_apply 2 (fun _ : ι => ℝ) i)).measurableSet
  unfold cumulativeExtension cumulativeTail
  rw [convolution_def]
  change (∫ t, cubeIndicator T t * f (v-t)) = _
  rw [← integral_sub_left_eq_self (fun t => cubeIndicator T t * f (v-t)) volume v]
  rw [← integral_indicator hs]
  apply integral_congr_ae
  filter_upwards [] with y
  simp only [sub_sub_cancel]
  by_cases hfy : f y=0
  · simp [Set.indicator,hfy]
  · by_cases hy : ∀ i, v i≤y i
    · rw [Set.indicator_of_mem (s := {y : EuclideanSpace ℝ ι | ∀ i, v i≤y i}) hy]
      have hcube : v-y∈negativeCube T := by
        intro i
        change -T≤v i-y i ∧ v i-y i≤0
        constructor <;> linarith [hf y hfy i,hv i,hy i]
      simp [cubeIndicator,Set.indicator_of_mem hcube]
    · rw [Set.indicator_of_notMem (s := {y : EuclideanSpace ℝ ι | ∀ i, v i≤y i}) hy]
      have hcube : v-y∉negativeCube T := by
        intro h
        apply hy
        intro i
        have := (h i).2
        change v i-y i≤0 at this
        linarith
      simp [cubeIndicator,Set.indicator_of_notMem hcube]

theorem profile_coordinate_upper {n : ℕ} {tau : ℝ} {f : (Fin n → ℝ) → ℝ}
    (hf : tsupport f ⊆ positiveSimplex n tau) (y : Fin n → ℝ) (hy : y∈tsupport f)
    (i : Fin n) : y i≤tau := by
  have hh := hf hy
  exact (Finset.single_le_sum (fun j _ => (hh.1 j).le) (Finset.mem_univ i)).trans hh.2.le

theorem cumulativeProfile_tail {n : ℕ} (tau : ℝ) (f : (Fin n → ℝ) → ℝ)
    (hf : tsupport f ⊆ positiveSimplex n tau) (v : Fin n → ℝ) (hv : ∀ i, 0≤v i) :
    cumulativeProfile tau f v = ∫ y in Ici v, f y := by
  unfold cumulativeProfile
  rw [cumulativeExtension_tail tau _ _ _ hv]
  · unfold cumulativeTail
    have hm := (PiLp.volume_preserving_ofLp (Fin n)).setIntegral_preimage_emb
      (MeasurableEquiv.toLp 2 (Fin n → ℝ)).symm.measurableEmbedding f (Ici v)
    exact hm
  · intro y hy i
    exact profile_coordinate_upper hf y.ofLp (subset_tsupport f hy) i

end LargePrimeGaps

end OAI
end

section
-- module Solutions.OAIW2_P344.PrimeGaps_TensorProfiles
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

open Asymptotics

open scoped Classical

open scoped ContDiff

open Topology

open scoped Convolution ContDiff Pointwise

theorem cumulativeProfile_budget {n : ℕ} (tau : ℝ) (f : (Fin n → ℝ) → ℝ)
    (hf : tsupport f ⊆ positiveSimplex n tau) : HasBudget (cumulativeProfile tau f) tau := by
  intro v hv hsum
  rw [cumulativeProfile_tail tau f hf v hv]
  apply setIntegral_eq_zero_of_forall_eq_zero
  intro y hy
  by_contra hne
  have hh := hf (subset_tsupport f hne)
  have he : tau≤coordinateSum y :=
    hsum.le.trans (Finset.sum_le_sum (fun i _ => hy i))
  exact (not_lt_of_ge he) hh.2

theorem divisorSum_tensor (X M : ℕ) {n m : ℕ}
    (F : (Fin n → ℝ) → ℝ) (G : (Fin m → ℝ) → ℝ) (b : Fin n → ℕ) (c : Fin m → ℕ) :
    divisorSum X (tensorProfile F G) M (Fin.append b c)=
      divisorSum X F M b*divisorSum X G M c := by
  classical
  unfold divisorSum
  rw [Finset.sum_mul_sum, ←Finset.sum_product']
  symm
  apply Finset.sum_equiv (Fin.appendEquiv n m)
  · intro p
    simp only [Finset.mem_product,Fintype.mem_piFinset,Fin.appendEquiv_apply]
    constructor
    · rintro ⟨h1,h2⟩ i
      cases i using Fin.addCases with
      | left i => simpa using h1 i
      | right i => simpa using h2 i
    · intro h
      exact ⟨fun i => by simpa using h (i.castAdd m),fun i => by simpa using h (i.natAdd n)⟩
  · intro p _
    exact (divisorCoefficient_tensor X F G p.1 p.2).symm

end LargePrimeGaps

end OAI
end

section
-- module Solutions.OAIW2_P344.PrimeGaps_EqualityPatterns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

open Asymptotics

open scoped Classical

open scoped ContDiff

open Topology

open scoped Convolution ContDiff Pointwise

theorem sum_patterns {ι α K : Type*} [Fintype ι] [Fintype α] [AddCommMonoid K]
    (f : (ι → α) → K) :
    (∑ r : Setoid ι, ∑ b∈patternClass (α:=α) r, f b)=∑ b : ι → α, f b := by
  classical
  simp only [patternClass]
  exact Finset.sum_fiberwise_of_maps_to (fun _ _ => Finset.mem_univ _) _

theorem blockLength_ratio_tendsto {lam : ℝ} (hlam : 0≤lam) :
    Tendsto (fun X : ℕ => (blockLength lam X:ℝ)/Real.log X) atTop (𝓝 lam) := by
  have hlog : Tendsto (fun X : ℕ => Real.log (X:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hinv := tendsto_inv_atTop_zero.comp hlog
  have hlo : Tendsto (fun X : ℕ => lam-(Real.log (X:ℝ))⁻¹) atTop (𝓝 lam) := by
    simpa using tendsto_const_nhds.sub hinv
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo tendsto_const_nhds
  · filter_upwards [eventually_ge_atTop 2] with X hX
    have hL := log_pos_of_two_le hX
    apply (le_div_iff₀ hL).mpr
    have hh := (Nat.lt_floor_add_one (lam*Real.log (X:ℝ))).le
    dsimp [blockLength]
    have he : (lam-(Real.log (X:ℝ))⁻¹)*Real.log X=lam*Real.log X-1 := by
      field_simp
    rw [he]
    linarith
  · filter_upwards [eventually_ge_atTop 2] with X hX
    exact (div_le_iff₀ (log_pos_of_two_le hX)).mpr (blockLength_le_mul_log hlam hX)

theorem blockLength_tendsto {lam : ℝ} (hlam : 0<lam) :
    Tendsto (blockLength lam) atTop atTop := by
  exact tendsto_nat_floor_atTop.comp ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop hlam)

theorem blockLength_densityCutoff_eventually {lam : ℝ} (hlam : 0≤lam) (K : ℕ) :
    ∀ᶠ X : ℕ in atTop, K*blockLength lam X≤densityCutoff 2 (Real.log X) := by
  have hlog : Tendsto (fun X : ℕ => Real.log (X:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop 2,hlog.eventually_ge_atTop ((K:ℝ)*lam)] with X hX hL
  apply (Nat.le_floor_iff (by positivity : 0≤(Real.log (X:ℝ))^2)).mpr
  push_cast
  have hh := blockLength_le_mul_log hlam hX
  nlinarith [mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg K),
    mul_le_mul_of_nonneg_right hL (log_pos_of_two_le hX).le]

theorem uniform_singularBoxMean_tendsto (s : ℕ) {K : ℕ} (hK : 0<K)
    (H : ℕ → ℕ) (a : ℕ → Fin s → ℤ) (hH : Tendsto H atTop atTop)
    (hdiam : ∀ᶠ X : ℕ in atTop, boxDiameterBound (h:=H X) (a X) (K*H X)) :
    Tendsto (fun X => singularBoxMean (h:=H X) (a X)) atTop (𝓝 1) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨h₀,hh₀⟩ := singularBoxMean_uniform s hK hε
  filter_upwards [hH.eventually_ge_atTop h₀,hdiam] with X hX hd
  exact (by simpa only [Real.dist_eq] using hh₀ (H X) hX (a X) hd)

end LargePrimeGaps

end OAI
end

section
-- module Solutions.OAIW2_P344.PrimeGaps_Detectors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

open Asymptotics

open scoped Classical

open scoped ContDiff

open Topology

open scoped Convolution ContDiff Pointwise

theorem shiftFamily_eq_of_ker {ι : Type*} [Fintype ι] (b c : ι → ℤ)
    (h : Setoid.ker b=Setoid.ker c) : shiftFamily b=shiftFamily c := by
  classical
  ext S
  simp only [shiftFamily,mem_fiberSubsetFamily_image]
  have hc (i j : ι) : b i=b j ↔ c i=c j := by
    change (Setoid.ker b) i j ↔ (Setoid.ker c) i j
    rw [h]
  constructor <;> rintro ⟨hS,he⟩
  · exact ⟨hS,fun i hi j hj => (hc i j).mp (he i hi j hj)⟩
  · exact ⟨hS,fun i hi j hj => (hc i j).mpr (he i hi j hj)⟩

theorem divisorSum_fin_zero (X M : ℕ) (F : (Fin 0 → ℝ) → ℝ) (b : Fin 0 → ℕ) :
    divisorSum X F M b=F 0 := by
  classical
  have h : Fintype.piFinset (fun i => (M+b i).divisors)={(0 : Fin 0 → ℕ)} := by
    ext d
    simp [funext_iff]
  rw [divisorSum,h,Finset.sum_singleton]
  simp only [divisorCoefficient,Fin.prod_univ_zero,one_mul]
  congr 1
  ext i
  exact Fin.elim0 i

theorem patternBoxShifts_family {n s h : ℕ} (p : Fin n → Fin s)
    (a : Fin s → ℕ) (u : Fin s → Fin h)
    (hu : u∈distinctBox (fun j => (a j:ℤ))) :
    shiftFamily (fun i => (patternBoxShifts p a u i:ℤ))=
      shiftFamily (fun i => ((p i).val:ℤ)) := by
  apply shiftFamily_eq_of_ker
  apply Setoid.ext
  intro i j
  have hi := (Finset.mem_filter.mp hu).2
  change ((patternBoxShifts p a u i:ℤ)=(patternBoxShifts p a u j:ℤ)) ↔
    ((p i).val:ℤ)=((p j).val:ℤ)
  have he (i : Fin n) : (patternBoxShifts p a u i:ℤ)=boxTuple (fun j => (a j:ℤ)) u (p i) := by
    simp only [patternBoxShifts,boxTuple,Nat.cast_add]
  rw [he,he,hi.eq_iff]
  constructor
  · intro h; rw [h]
  · intro h; apply Fin.ext; exact_mod_cast h

theorem patternBoxShifts_image {n s h : ℕ} (p : Fin n → Fin s)
    (hp : Function.Surjective p) (a : Fin s → ℕ) (u : Fin s → Fin h) :
    (Finset.univ.image fun i => (patternBoxShifts p a u i:ℤ))=
      Finset.univ.image (boxTuple (fun j => (a j:ℤ)) u) := by
  classical
  ext x
  simp only [Finset.mem_image,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨i,rfl⟩
    exact ⟨p i,by simp only [boxTuple,patternBoxShifts,Nat.cast_add]⟩
  · rintro ⟨j,rfl⟩
    obtain ⟨i,rfl⟩ := hp j
    exact ⟨i,by simp only [boxTuple,patternBoxShifts,Nat.cast_add]⟩

theorem surjective_shiftFamily_sign_sum {n s : ℕ} (p : Fin n → Fin s)
    (hp : Function.Surjective p) :
    (∑ S∈shiftFamily (fun i => ((p i).val:ℤ)),(-1:ℤ)^S.card)=-(s:ℤ) := by
  classical
  rw [shiftFamily_sign_sum]
  have he : (Finset.univ.image fun i => ((p i).val:ℤ))=
      Finset.univ.image (fun j : Fin s => (j.val:ℤ)) := by
    ext x
    simp only [Finset.mem_image,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨i,rfl⟩; exact ⟨p i,rfl⟩
    · rintro ⟨j,rfl⟩; obtain ⟨i,rfl⟩ := hp j; exact ⟨i,rfl⟩
  rw [he,Finset.card_image_of_injective]
  · simp only [Finset.card_univ,Fintype.card_fin]
  · intro i j hij; apply Fin.ext; exact_mod_cast (show (i.val:ℤ)=(j.val:ℤ) from hij)

theorem box_sum_scaled_norm_le {s h : ℕ} (a : Fin s → ℤ)
    (f g : (Fin s → Fin h) → ℂ) {L E : ℝ} (hL : 0<L) (hE : 0≤E)
    (herr : ∀ u∈distinctBox a, ‖(L:ℂ)^s*f u-g u‖≤E) :
    ‖(∑ u∈distinctBox a,f u)-(∑ u∈distinctBox a,g u)/(L:ℂ)^s‖≤((h:ℝ)/L)^s*E := by
  classical
  have hb : ‖∑ u∈distinctBox a,((L:ℂ)^s*f u-g u)‖≤(h:ℝ)^s*E := by
    calc
      _ ≤ ∑ _u∈distinctBox (h:=h) a,E := norm_sum_le_of_le _ herr
      _ = ((distinctBox (h:=h) a).card:ℝ)*E := by simp
      _ ≤ (h:ℝ)^s*E := by
        apply mul_le_mul_of_nonneg_right _ hE
        have hc := Finset.card_le_card (show distinctBox (h:=h) a⊆Finset.univ from Finset.subset_univ _)
        simpa only [Finset.card_univ,Fintype.card_fun,Fintype.card_fin,Nat.cast_pow] using
          (show ((distinctBox (h:=h) a).card:ℝ)≤(Fintype.card (Fin s → Fin h):ℝ) from by exact_mod_cast hc)
  rw [Finset.sum_sub_distrib,←Finset.mul_sum] at hb
  have hLc : (L:ℂ)≠0 := by exact_mod_cast ne_of_gt hL
  have he : (∑ u∈distinctBox a,f u)-(∑ u∈distinctBox a,g u)/(L:ℂ)^s=
      ((L:ℂ)^s*(∑ u∈distinctBox a,f u)-∑ u∈distinctBox a,g u)/(L:ℂ)^s := by
    field_simp [hLc]
  rw [he,norm_div,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hL]
  apply (div_le_iff₀ (pow_pos hL _)).mpr
  apply le_trans hb
  apply le_of_eq
  rw [div_pow]
  field_simp

theorem box_sum_errors_tendsto_zero (s : ℕ) (H : ℕ → ℕ) (a : ℕ → Fin s → ℤ)
    (L E : ℕ → ℝ) (lam : ℝ)
    (f g : (X : ℕ) → (Fin s → Fin (H X)) → ℂ)
    (hL : ∀ᶠ X in atTop,0<L X)
    (hHL : Tendsto (fun X => (H X:ℝ)/L X) atTop (𝓝 lam))
    (hE : Tendsto E atTop (𝓝 0))
    (herr : ∀ᶠ X in atTop, ∀ u∈distinctBox (a X),‖(L X:ℂ)^s*f X u-g X u‖≤E X) :
    Tendsto (fun X => (∑ u∈distinctBox (a X),f X u)-
      (∑ u∈distinctBox (a X),g X u)/(L X:ℂ)^s) atTop (𝓝 0) := by
  apply squeeze_zero_norm' (a:=fun X => ((H X:ℝ)/L X)^s*|E X|)
  · filter_upwards [hL,herr] with X hLX hX
    exact box_sum_scaled_norm_le (a X) (f X) (g X) hLX (abs_nonneg _) (fun u hu =>
      (hX u hu).trans (le_abs_self _))
  · simpa only [abs_zero,mul_zero] using (hHL.pow s).mul hE.abs

theorem natural_boxDiameterBound {s h K : ℕ} (a : Fin s → ℕ) (ha : ∀ j,a j≤K*h) :
    boxDiameterBound (h:=h) (fun j => (a j:ℤ)) ((K+1)*h) := by
  intro u i j
  dsimp [boxTuple]
  have hi := (u i).isLt
  have hj := (u j).isLt
  have hai := ha i
  have haj := ha j
  have hk : K*h+h=(K+1)*h := by ring
  omega

theorem unmarked_box_pattern_limit {n s K : ℕ} {lam : ℝ} (hlam : 0<lam)
    (p : Fin (n+1) → Fin s) (hp : Function.Surjective p)
    (a : ℕ → Fin s → ℕ)
    (ha : ∀ᶠ X : ℕ in atTop, ∀ j,a X j≤K*blockLength lam X)
    (F : (Fin (n+1) → ℝ) → ℝ) (rho : ℝ)
    (hrho : 0≤rho) (hrho1 : rho<1) (hbudget : HasBudget F rho)
    (hF : HasCompactSupport (fun v : EuclideanSpace ℝ (Fin (n+1)) => (F v.ofLp:ℂ)))
    (hFs : ContDiff ℝ ∞ (fun v : EuclideanSpace ℝ (Fin (n+1)) => (F v.ofLp:ℂ)))
    (M : ℝ) (hM : 0≤M) (hbound : ∀ v, (∀ i,0≤v i) → |F v|≤M) :
    Tendsto (fun X : ℕ => ∑ u∈distinctBox (h:=blockLength lam X) (fun j => (a X j:ℤ)),
      (average X (fun m => divisorSum X F m (patternBoxShifts p (a X) u)):ℂ)) atTop
      (𝓝 ((lam:ℂ)^s*kernelConstant
        (sourceFourier (fourierCoordinateSum (Fin (n+1)))
          (fun v => (F v.ofLp:ℂ)) hF hFs) (shiftFamily (fun i => ((p i).val:ℤ))))) := by
  classical
  let B := shiftFamily (fun i => ((p i).val:ℤ))
  let c := kernelConstant (sourceFourier (fourierCoordinateSum (Fin (n+1)))
    (fun v => (F v.ofLp:ℂ)) hF hFs) B
  let H := blockLength lam
  let az := fun X j => (a X j:ℤ)
  let f := fun X (u : Fin s → Fin (H X)) =>
    (average X (fun m => divisorSum X F m (patternBoxShifts p (a X) u)):ℂ)
  let g := fun X (u : Fin s → Fin (H X)) =>
    (singularSeries (Finset.univ.image (boxTuple (az X) u)):ℂ)*c
  obtain ⟨E,hE,herr⟩ := unmarked_average_uniform_asymptotic F rho hrho hrho1 hbudget
    hF hFs M hM hbound B (shiftFamily_nonempty _) s 2 (by omega)
    (surjective_shiftFamily_sign_sum p hp)
  have herror : ∀ᶠ X in atTop, ∀ u∈distinctBox (az X),
      ‖(Real.log X:ℂ)^s*f X u-g X u‖≤E X := by
    filter_upwards [herr,ha,blockLength_densityCutoff_eventually hlam.le (2*(K+1))]
      with X hX haX hcut
    intro u hu
    have hb (i : Fin (n+1)) : patternBoxShifts p (a X) u i≤(K+1)*H X := by
      have hi := (u (p i)).isLt
      have hh := haX (p i)
      dsimp [H] at hi
      dsimp [patternBoxShifts,H]
      rw [Nat.add_mul,one_mul]
      omega
    have hz := hX (patternBoxShifts p (a X) u) (patternBoxShifts_family p (a X) u hu)
       ((K+1)*H X) hb (by simpa only [Nat.mul_assoc] using hcut)
    rw [patternBoxShifts_image p hp] at hz
    exact hz
  have hL : ∀ᶠ X : ℕ in atTop,0<Real.log X := by
    filter_upwards [eventually_ge_atTop 2] with X hX
    exact log_pos_of_two_le hX
  have hHL := blockLength_ratio_tendsto hlam.le
  have he := box_sum_errors_tendsto_zero s H az (fun X => Real.log X) E lam f g hL hHL hE herror
  have hmean : Tendsto (fun X => singularBoxMean (h:=H X) (az X)) atTop (𝓝 1) := by
    apply uniform_singularBoxMean_tendsto s (K:=K+1) (by omega) H az (blockLength_tendsto hlam)
    filter_upwards [ha] with X hX
    exact natural_boxDiameterBound (a X) hX
  have hmain : Tendsto (fun X => (∑ u∈distinctBox (az X),g X u)/(Real.log X:ℂ)^s)
      atTop (𝓝 ((lam:ℂ)^s*c)) := by
    have hh := ((Complex.continuous_ofReal.continuousAt.tendsto.comp hHL).pow s).mul
      (Complex.continuous_ofReal.continuousAt.tendsto.comp hmean)
    have hh' := hh.mul_const c
    simp only [Complex.ofReal_one,mul_one] at hh'
    apply hh'.congr'
    filter_upwards [hL,(blockLength_tendsto hlam).eventually_ge_atTop 1] with X hLX hHX
    have hHC : ((H X:ℕ):ℂ)≠0 := by exact_mod_cast (show H X≠0 by dsimp [H]; omega)
    have hLC : (Real.log X:ℂ)≠0 := by exact_mod_cast ne_of_gt hLX
    change (((H X:ℝ)/(Real.log X):ℝ):ℂ)^s * (singularBoxMean (h:=H X) (az X):ℂ)*c =
      (∑ u∈distinctBox (az X),g X u)/(Real.log X:ℂ)^s
    simp only [g,←Finset.sum_mul,←Complex.ofReal_sum,singularBoxMean,
      Complex.ofReal_div,Complex.ofReal_pow,Complex.ofReal_natCast]
    rw [div_pow]
    field_simp
  have h := he.add hmain
  simp only [sub_add_cancel,zero_add] at h
  exact h

theorem average_mono {X : ℕ} (f g : ℕ → ℝ)
    (h : ∀ m∈Finset.Ioc X (2*X),f m≤g m) : average X f≤average X g := by
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum h) (Nat.cast_nonneg X)

theorem average_const_mul (X : ℕ) (c : ℝ) (f : ℕ → ℝ) :
    average X (fun m => c*f m)=c*average X f := by
  simp only [average,←Finset.mul_sum,mul_div_assoc]

theorem average_finset_sum {α : Type*} (X : ℕ) (S : Finset α) (f : α → ℕ → ℝ) :
    average X (fun m => ∑ i∈S,f i m)=∑ i∈S,average X (f i) := by
  unfold average
  rw [Finset.sum_comm,Finset.sum_div]

end LargePrimeGaps

end OAI
end

section
-- module Solutions.OAIW2_P344.PrimeGaps_PatternMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

open Asymptotics

open scoped Classical

open scoped ContDiff

open Topology

open scoped Convolution ContDiff Pointwise

theorem patternLabels_surjective {ι : Type*} [Fintype ι] (r : Setoid ι) :
    Function.Surjective (patternLabels r) := by
  intro j
  obtain ⟨i,hi⟩ := Quotient.mk_surjective ((Fintype.equivFin (Quotient r)).symm j)
  refine ⟨i,?_⟩
  simp only [patternLabels,hi,Equiv.apply_symm_apply]

theorem patternTupleEquiv_labels {n : ℕ} (r : Setoid (Fin n)) (h a : ℕ)
    (b : {b // b∈patternClass (α:=Fin h) r}) :
    patternBoxShifts (patternLabels r) (fun _ => a)
      (patternTupleEquiv r h a b).val=(fun i => a+(b.val i:ℕ)) := by
  funext i
  simp only [patternBoxShifts,patternLabels,patternTupleEquiv_apply,Equiv.symm_apply_apply]
  rfl

theorem pattern_sum_average_eq_box {n : ℕ} (r : Setoid (Fin n)) (h a X : ℕ)
    (F : (Fin n → ℝ) → ℝ) :
    (∑ b∈patternClass (α:=Fin h) r,
      (average X (fun m => divisorSum X F m (fun i => a+(b i:ℕ))):ℂ))=
    ∑ u∈distinctBox (s:=Fintype.card (Quotient r)) (h:=h) (fun _ => (a:ℤ)),
      (average X (fun m => divisorSum X F m (patternBoxShifts (patternLabels r) (fun _ => a) u)):ℂ) := by
  classical
  conv_lhs => rw [←Finset.sum_coe_sort]
  conv_rhs => rw [←Finset.sum_coe_sort]
  apply Fintype.sum_equiv (patternTupleEquiv r h a)
  intro b
  rw [patternTupleEquiv_labels]

theorem unmarked_pattern_limit {n K : ℕ} {lam : ℝ} (hlam : 0<lam)
    (r : Setoid (Fin (n+1))) (a : ℕ → ℕ)
    (ha : ∀ᶠ X : ℕ in atTop,a X≤K*blockLength lam X)
    (F : (Fin (n+1) → ℝ) → ℝ) (rho : ℝ)
    (hrho : 0≤rho) (hrho1 : rho<1) (hbudget : HasBudget F rho)
    (hF : HasCompactSupport (fun v : EuclideanSpace ℝ (Fin (n+1)) => (F v.ofLp:ℂ)))
    (hFs : ContDiff ℝ ∞ (fun v : EuclideanSpace ℝ (Fin (n+1)) => (F v.ofLp:ℂ)))
    (M : ℝ) (hM : 0≤M) (hbound : ∀ v, (∀ i,0≤v i) → |F v|≤M) :
    Tendsto (fun X : ℕ => ∑ b∈patternClass (α:=Fin (blockLength lam X)) r,
      (average X (fun m => divisorSum X F m (fun i => a X+(b i:ℕ))):ℂ)) atTop
      (𝓝 ((lam:ℂ)^Fintype.card (Quotient r)*kernelConstant
        (sourceFourier (fourierCoordinateSum (Fin (n+1)))
          (fun v => (F v.ofLp:ℂ)) hF hFs)
        (shiftFamily (fun i => (numericPattern r i:ℤ))))) := by
  have hh := unmarked_box_pattern_limit hlam (patternLabels r) (patternLabels_surjective r)
    (fun X _ => a X) (ha.mono (fun _ h _ => h)) F rho hrho hrho1 hbudget hF hFs M hM hbound
  have he : (fun X : ℕ => ∑ b∈patternClass (α:=Fin (blockLength lam X)) r,
      (average X (fun m => divisorSum X F m (fun i => a X+(b i:ℕ))):ℂ))=
      (fun X : ℕ => ∑ u∈distinctBox (h:=blockLength lam X) (fun _ => (a X:ℤ)),
        (average X (fun m => divisorSum X F m (patternBoxShifts (patternLabels r) (fun _ => a X) u)):ℂ)) := by
    funext X
    exact pattern_sum_average_eq_box r _ _ _ F
  rw [he]
  exact hh

theorem unmarked_labeled_expansion_limit {n K : ℕ} {lam : ℝ} (hlam : 0<lam)
    (a : ℕ → ℕ) (ha : ∀ᶠ X : ℕ in atTop,a X≤K*blockLength lam X)
    (F : (Fin (n+1) → ℝ) → ℝ) (rho : ℝ)
    (hrho : 0≤rho) (hrho1 : rho<1) (hbudget : HasBudget F rho)
    (hF : HasCompactSupport (fun v : EuclideanSpace ℝ (Fin (n+1)) => (F v.ofLp:ℂ)))
    (hFs : ContDiff ℝ ∞ (fun v : EuclideanSpace ℝ (Fin (n+1)) => (F v.ofLp:ℂ)))
    (M : ℝ) (hM : 0≤M) (hbound : ∀ v, (∀ i,0≤v i) → |F v|≤M)
    (k : Setoid (Fin (n+1)) → ℂ) :
    Tendsto (fun X : ℕ => ∑ b : Fin (n+1) → Fin (blockLength lam X),
      k (Setoid.ker b)*(average X (fun m => divisorSum X F m (fun i => a X+(b i:ℕ))):ℂ)) atTop
      (𝓝 (∑ r : Setoid (Fin (n+1)),k r*((lam:ℂ)^Fintype.card (Quotient r)*kernelConstant
        (sourceFourier (fourierCoordinateSum (Fin (n+1)))
          (fun v => (F v.ofLp:ℂ)) hF hFs)
        (shiftFamily (fun i => (numericPattern r i:ℤ)))))) := by
  classical
  have hh := tendsto_finsetSum Finset.univ (fun r _ =>
    (unmarked_pattern_limit hlam r a ha F rho hrho hrho1 hbudget hF hFs M hM hbound).const_mul (k r))
  apply hh.congr'
  exact Eventually.of_forall (fun X => by
    dsimp only
    calc
      (∑ r : Setoid (Fin (n+1)), k r*∑ b∈patternClass (α:=Fin (blockLength lam X)) r,
        (average X (fun m => divisorSum X F m (fun i => a X+(b i:ℕ))):ℂ)) =
        ∑ r : Setoid (Fin (n+1)), ∑ b∈patternClass (α:=Fin (blockLength lam X)) r,
          k (Setoid.ker b)*(average X (fun m => divisorSum X F m (fun i => a X+(b i:ℕ))):ℂ) := by
        apply Finset.sum_congr rfl
        intro r _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro b hb
        rw [(mem_patternClass r b).mp hb]
      _ = _ := sum_patterns _
    apply Finset.sum_congr (by ext b; simp)
    intro b _
    rfl)

theorem injective_same_range_perm {n : ℕ} {α : Type*}
    (a b : Fin n → α) (hb : Function.Injective b)
    (hab : Set.range a=Set.range b) : ∃ e : Equiv.Perm (Fin n), b=a ∘ e := by
  classical
  have hs : ∀ i,∃ j,a j=b i := by
    intro i
    have : b i ∈ Set.range a := hab.symm ▸ Set.mem_range_self i
    exact this
  choose e he using hs
  have hei : Function.Injective e := by
    intro i j hij
    apply hb
    rw [←he i,←he j,hij]
  exact ⟨Equiv.ofBijective e ⟨hei,Finite.surjective_of_injective hei⟩,by funext i; exact (he i).symm⟩

theorem weightedBlock_mul {n p : ℕ} (X h a m : ℕ)
    (F : (Fin n → ℝ) → ℝ) (G : (Fin p → ℝ) → ℝ)
    (k : Setoid (Fin n) → ℝ) (l : Setoid (Fin p) → ℝ) :
    weightedBlock X h a F k m * weightedBlock X h a G l m =
    weightedBlock X h a (tensorProfile F G) (tensorCoefficient k l) m := by
  classical
  unfold weightedBlock
  rw [Finset.sum_mul_sum,←Finset.sum_product']
  apply Finset.sum_equiv (Fin.appendEquiv n p)
  · intro bc; simp
  intro bc _
  rw [show (Fin.appendEquiv n p) bc=Fin.append bc.1 bc.2 from rfl]
  simp only [tensorCoefficient,append_ker_left,append_ker_right]
  have he : (fun i => a+((Fin.append bc.1 bc.2 i :Fin h):ℕ))=
      Fin.append (fun i => a+(bc.1 i:ℕ)) (fun i => a+(bc.2 i:ℕ)) := by
    funext i
    cases i using Fin.addCases <;> simp
  rw [he,divisorSum_tensor]
  ring

theorem average_weightedBlock (X h a : ℕ) {n : ℕ}
    (F : (Fin n → ℝ) → ℝ) (k : Setoid (Fin n) → ℝ) :
    average X (weightedBlock X h a F k)=
    ∑ b : Fin n → Fin h, k (Setoid.ker b)*average X (fun m => divisorSum X F m (fun i => a+(b i:ℕ))) := by
  unfold weightedBlock
  rw [average_finset_sum]
  simp only [average_const_mul]

end LargePrimeGaps

end OAI
end

section
-- module Solutions.OAIW2_P344.PrimeGaps_WeightMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

open Asymptotics

open scoped Classical

open scoped ContDiff

open Topology

open scoped Convolution ContDiff Pointwise

theorem weightedBlock_average_limit {n K : ℕ} {lam : ℝ} (hlam : 0<lam)
    (a : ℕ → ℕ) (ha : ∀ᶠ X : ℕ in atTop,a X≤K*blockLength lam X)
    (F : (Fin (n+1) → ℝ) → ℝ) (rho : ℝ)
    (hrho : 0≤rho) (hrho1 : rho<1) (hbudget : HasBudget F rho)
    (hF : HasCompactSupport (fun v : EuclideanSpace ℝ (Fin (n+1)) => (F v.ofLp:ℂ)))
    (hFs : ContDiff ℝ ∞ (fun v : EuclideanSpace ℝ (Fin (n+1)) => (F v.ofLp:ℂ)))
    (M : ℝ) (hM : 0≤M) (hbound : ∀ v, (∀ i,0≤v i) → |F v|≤M)
    (k : Setoid (Fin (n+1)) → ℝ) :
    Tendsto (fun X : ℕ => (average X (weightedBlock X (blockLength lam X) (a X) F k):ℂ)) atTop
      (𝓝 (∑ r : Setoid (Fin (n+1)),(k r:ℂ)*((lam:ℂ)^Fintype.card (Quotient r)*kernelConstant
        (sourceFourier (fourierCoordinateSum (Fin (n+1)))
          (fun v => (F v.ofLp:ℂ)) hF hFs)
        (shiftFamily (fun i => (numericPattern r i:ℤ)))))) := by
  simpa only [average_weightedBlock,Complex.ofReal_sum,Complex.ofReal_mul] using
    unmarked_labeled_expansion_limit hlam a ha F rho hrho hrho1 hbudget hF hFs M hM hbound
      (fun r => (k r:ℂ))

theorem average_const {X : ℕ} (hX : X≠0) (c : ℝ) : average X (fun _ => c)=c := by
  unfold average
  simp only [Finset.sum_const,Nat.card_Ioc,nsmul_eq_mul]
  rw [show 2*X-X=X by omega]
  simp [hX]

@[simp] theorem weightedBlock_zero (X h a m : ℕ)
    (F : (Fin 0 → ℝ) → ℝ) (k : Setoid (Fin 0) → ℝ) :
    weightedBlock X h a F k m=k ⊥*F 0 := by
  unfold weightedBlock
  simp only [divisorSum_fin_zero]
  have he (b : Fin 0 → Fin h) : Setoid.ker b=⊥ := by
    apply Setoid.ext
    intro i
    exact Fin.elim0 i
  simp only [he,Finset.sum_const,Finset.card_univ,Fintype.card_fun,Fintype.card_fin,pow_zero,one_nsmul]

theorem weightedBlock_average_converges {n K : ℕ} {lam : ℝ} (hlam : 0<lam)
    (a : ℕ → ℕ) (ha : ∀ᶠ X : ℕ in atTop,a X≤K*blockLength lam X)
    (F : (Fin n → ℝ) → ℝ) (rho : ℝ)
    (hrho : 0≤rho) (hrho1 : rho<1) (hbudget : HasBudget F rho)
    (hF : HasCompactSupport F) (hFs : ContDiff ℝ ∞ F)
    (k : Setoid (Fin n) → ℝ) :
    ∃ c : ℝ,Tendsto (fun X : ℕ => average X (weightedBlock X (blockLength lam X) (a X) F k))
      atTop (𝓝 c) := by
  cases n with
  | zero =>
    refine ⟨k ⊥*F 0,?_⟩
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop 1] with X hX
    have he : weightedBlock X (blockLength lam X) (a X) F k=(fun _ => k ⊥*F 0) :=
      funext (fun m => weightedBlock_zero X _ _ m F k)
    rw [he,average_const (by omega : X≠0)]
  | succ n =>
    have hc : HasCompactSupport (fun v : EuclideanSpace ℝ (Fin (n+1)) => (F v.ofLp:ℂ)) :=
      (hF.comp_isClosedEmbedding (EuclideanSpace.equiv (Fin (n+1)) ℝ).toHomeomorph.isClosedEmbedding).comp_left
        Complex.ofReal_zero
    have hs : ContDiff ℝ ∞ (fun v : EuclideanSpace ℝ (Fin (n+1)) => (F v.ofLp:ℂ)) :=
      Complex.ofRealCLM.contDiff.comp (hFs.comp (EuclideanSpace.equiv (Fin (n+1)) ℝ).contDiff)
    obtain ⟨M,hM⟩ := hFs.continuous.bounded_above_of_compact_support hF
    have hM0 : 0≤M := (norm_nonneg (F 0)).trans (hM 0)
    have hh := weightedBlock_average_limit hlam a ha F rho hrho hrho1 hbudget hc hs M hM0
      (fun v _ => by simpa only [Real.norm_eq_abs] using hM v) k
    exact ⟨_,Complex.continuous_re.continuousAt.tendsto.comp hh⟩

theorem HasBudget.tensor {n p : ℕ} {F : (Fin n → ℝ) → ℝ} {G : (Fin p → ℝ) → ℝ}
    {a b : ℝ} (hF : HasBudget F a) (hG : HasBudget G b) :
    HasBudget (tensorProfile F G) (a+b) := by
  intro v hv hsum
  unfold tensorProfile
  rw [Fin.sum_univ_add] at hsum
  by_cases hf : a<∑ i : Fin n,v (i.castAdd p)
  · rw [hF _ (fun i => hv (i.castAdd p)) hf,zero_mul]
  · rw [hG _ (fun i => hv (i.natAdd n)) (by linarith),mul_zero]

theorem weightedBlock_fourth_converges {n K : ℕ} {lam : ℝ} (hlam : 0<lam)
    (a : ℕ → ℕ) (ha : ∀ᶠ X : ℕ in atTop,a X≤K*blockLength lam X)
    (F : (Fin n → ℝ) → ℝ) (rho : ℝ)
    (hrho : 0≤rho) (hrho4 : 4*rho<1) (hbudget : HasBudget F rho)
    (hF : HasCompactSupport F) (hFs : ContDiff ℝ ∞ F)
    (k : Setoid (Fin n) → ℝ) :
    ∃ c : ℝ,Tendsto (fun X : ℕ => average X
      (fun m => weightedBlock X (blockLength lam X) (a X) F k m^4)) atTop (𝓝 c) := by
  let F2 := tensorProfile F F
  let k2 := tensorCoefficient k k
  have hc2 := tensorProfile_compact F F hF hF
  have hs2 := tensorProfile_smooth F F hFs hFs
  obtain ⟨c,hc⟩ := weightedBlock_average_converges hlam a ha (tensorProfile F2 F2)
    ((rho+rho)+(rho+rho)) (by positivity) (by linarith)
    ((hbudget.tensor hbudget).tensor (hbudget.tensor hbudget))
    (tensorProfile_compact F2 F2 hc2 hc2) (tensorProfile_smooth F2 F2 hs2 hs2)
    (tensorCoefficient k2 k2)
  refine ⟨c,?_⟩
  convert hc using 1
  ext X
  congr 1
  funext m
  rw [←weightedBlock_mul,←weightedBlock_mul]
  ring

theorem fourth_power_sum_le {α : Type*} (S : Finset α) (f : α → ℝ) :
    (∑ i∈S,f i)^4≤(S.card:ℝ)^3*∑ i∈S,f i^4 := by
  have h1 := sq_sum_le_card_mul_sum_sq (s:=S) (f:=f)
  have h2 := sq_sum_le_card_mul_sum_sq (s:=S) (f:=fun i => f i^2)
  have h3 := mul_self_le_mul_self (sq_nonneg (∑ i∈S,f i)) h1
  have h4 := mul_le_mul_of_nonneg_left h2 (sq_nonneg (S.card:ℝ))
  simp only [←pow_mul] at h3 h4
  nlinarith only [h3,h4]

theorem blockOffset_eventually {lam : ℝ} (hlam : 0<lam) :
    ∀ᶠ X : ℕ in atTop,blockLength lam X+1≤2*blockLength lam X := by
  filter_upwards [(blockLength_tendsto hlam).eventually_ge_atTop 1] with X hX
  omega

theorem finite_sum_fourth_bound {α : Type*} [Fintype α]
    (f : α → ℕ → ℕ → ℝ)
    (h : ∀ j,∃ c : ℝ,Tendsto (fun X => average X (fun m => f j X m^4)) atTop (𝓝 c)) :
    ∃ M : ℝ,0<M ∧ ∀ᶠ X : ℕ in atTop,
      average X (fun m => (∑ j,f j X m)^4)≤M := by
  classical
  choose c hc using h
  let C := (Fintype.card α:ℝ)^3*∑ j,c j
  have ht : Tendsto (fun X => (Fintype.card α:ℝ)^3*∑ j,average X (fun m => f j X m^4))
      atTop (𝓝 C) := (tendsto_finsetSum Finset.univ (fun j _ => hc j)).const_mul _
  refine ⟨|C|+1,by positivity,?_⟩
  filter_upwards [(tendsto_order.mp ht).2 (|C|+1) (by linarith [le_abs_self C])] with X hX
  apply le_trans ?_ hX.le
  calc
    _ ≤ average X (fun m => (Fintype.card α:ℝ)^3*∑ j,f j X m^4) :=
      average_mono _ _ (fun m _ => by
        simpa only [Finset.card_univ] using
          (fourth_power_sum_le Finset.univ (fun j => f j X m)))
    _ = _ := by rw [average_const_mul,average_finset_sum]

theorem orderedWeight_fourth_bound {tau lam : ℝ} {k : ℕ}
    (f : (j : ℕ) → (Fin j → ℝ) → ℝ) (hf : AdmissibleFamily tau k f)
    (htau : 0≤tau) (htau4 : 4*tau<1) (hlam : 0<lam) :
    ∃ M : ℝ,0<M ∧ ∀ᶠ X : ℕ in atTop,
      average X (fun m => orderedWeight tau lam k f X m^4)≤M := by
  apply finite_sum_fourth_bound
  intro j
  have hfj := hf.2.1 j (by omega : (j:ℕ)≤k)
  exact weightedBlock_fourth_converges hlam (fun X => blockLength lam X+1)
    (blockOffset_eventually hlam) (cumulativeProfile tau (f j)) tau htau htau4
    (cumulativeProfile_budget tau (f j) hfj.2.2.1)
    (cumulativeProfile_compact tau (f j) hfj.2.1)
    (cumulativeProfile_smooth tau (f j) hfj.2.1 hfj.1) (subsetCoefficient j)

@[simp] theorem cumulativeProfile_fin_zero {tau : ℝ} (f : (Fin 0 → ℝ) → ℝ)
    (hsf : tsupport f⊆positiveSimplex 0 tau) (v : Fin 0 → ℝ) :
    cumulativeProfile tau f v=f 0 := by
  rw [cumulativeProfile_tail tau f hsf v (fun i => Fin.elim0 i)]
  rw [Measure.volume_pi_eq_dirac (0 : Fin 0 → ℝ)]
  have he : Ici v=(Set.univ : Set (Fin 0 → ℝ)) := by
    ext x
    simp only [Set.mem_Ici,Set.mem_univ,iff_true]
    exact fun i => Fin.elim0 i
  rw [he,setIntegral_univ]
  exact integral_dirac f 0

end LargePrimeGaps

end OAI
end

section
-- module Solutions.OAIW2_P344.PrimeGaps_ProfileSymmetry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

open Asymptotics

open scoped Classical

open scoped ContDiff

open Topology

open scoped Convolution ContDiff Pointwise

theorem cumulativeProfile_perm_orthant {n : ℕ} {tau : ℝ}
    (f : (Fin n → ℝ) → ℝ) (hsupp : tsupport f⊆positiveSimplex n tau)
    (hsym : SymmetricFunction f) (e : Equiv.Perm (Fin n))
    (v : Fin n → ℝ) (hv : ∀ i,0≤v i) :
    cumulativeProfile tau f (v ∘ e)=cumulativeProfile tau f v := by
  change cumulativeProfile tau f (fun i => v (e i))=cumulativeProfile tau f v
  rw [cumulativeProfile_tail tau f hsupp _ (fun i => hv (e i)),
    cumulativeProfile_tail tau f hsupp _ hv]
  let q := MeasurableEquiv.piCongrLeft (fun _ : Fin n => ℝ) e.symm
  have hq : MeasurePreserving q volume volume :=
    volume_measurePreserving_piCongrLeft (fun _ : Fin n => ℝ) e.symm
  have hq_apply (x : Fin n → ℝ) : q x=x ∘ e := by
    funext i
    simp [q,MeasurableEquiv.coe_piCongrLeft,Equiv.piCongrLeft_apply]
  have he : q ⁻¹' {x : Fin n → ℝ | ∀ i,v (e i)≤x i}={x : Fin n → ℝ | ∀ i,v i≤x i} := by
    ext x
    simp only [Set.mem_preimage,Set.mem_ofPred_eq,hq_apply,Function.comp_apply]
    constructor
    · intro h i
      simpa using h (e.symm i)
    · intro h i
      exact h (e i)
  have hh := hq.integral_comp' (fun x => ({x : Fin n → ℝ | ∀ i,v (e i)≤x i}).indicator f x)
  have hefun : (fun x => ({x : Fin n → ℝ | ∀ i,v (e i)≤x i}).indicator f (q x))=
      ({x : Fin n → ℝ | ∀ i,v i≤x i}).indicator f := by
    funext x
    have hx : (∀ i,v (e i)≤q x i) ↔ ∀ i,v i≤x i := by
      simpa only [Set.mem_preimage,Set.mem_ofPred_eq] using
        (Set.ext_iff.mp he x)
    have hm : q x∈{x : Fin n → ℝ | ∀ i,v (e i)≤x i} ↔ x∈{x : Fin n → ℝ | ∀ i,v i≤x i} := hx
    by_cases hvx : x∈{x : Fin n → ℝ | ∀ i,v i≤x i}
    · rw [Set.indicator_of_mem (hm.mpr hvx),Set.indicator_of_mem hvx,hq_apply,hsym]
    · rw [Set.indicator_of_notMem (fun h => hvx (hm.mp h)),Set.indicator_of_notMem hvx]
  rw [hefun,integral_indicator (by measurability), integral_indicator (by measurability)] at hh
  exact hh.symm

theorem divisorSum_perm_orthant {n X m : ℕ} (hX : 2≤X)
    (F : (Fin n → ℝ) → ℝ)
    (hF : ∀ (e : Equiv.Perm (Fin n)) v,(∀ i,0≤v i) → F (v ∘ e)=F v)
    (e : Equiv.Perm (Fin n)) (b : Fin n → ℕ) :
    divisorSum X F m (b ∘ e)=divisorSum X F m b := by
  classical
  unfold divisorSum
  symm
  apply Finset.sum_equiv (functionPerm e)
  · intro d
    simp only [Fintype.mem_piFinset,functionPerm,Equiv.coe_fn_mk,Function.comp_apply]
    exact e.surjective.forall
  · intro d hd
    change divisorCoefficient X F d=divisorCoefficient X F (d ∘ e)
    unfold divisorCoefficient
    have hp : ∀ i,0<d i := fun i => Nat.pos_of_mem_divisors ((Fintype.mem_piFinset.mp hd) i)
    have he : logCoordinates X (d ∘ e)=(logCoordinates X d) ∘ e := rfl
    rw [he,hF e _ (logCoordinates_nonneg hX hp)]
    congr 1
    exact (Fintype.prod_equiv e _ _ (fun _ => rfl)).symm

theorem subsetEnumeration_image {h n : ℕ} (S : {S : Finset (Fin h) // S.card=n}) :
    Finset.univ.image (subsetEnumeration S)=S.1 := by
  classical
  ext x
  simp only [Finset.mem_image,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨i,rfl⟩
    exact (S.1.orderIsoOfFin S.2 i).2
  · intro hx
    refine ⟨(S.1.orderIsoOfFin S.2).symm ⟨x,hx⟩,?_⟩
    change ((S.1.orderIsoOfFin S.2) ((S.1.orderIsoOfFin S.2).symm ⟨x,hx⟩)).val=x
    simp

theorem enumeratePerm_image {h n : ℕ}
    (t : {S : Finset (Fin h) // S.card=n} × Equiv.Perm (Fin n)) :
    Finset.univ.image (enumeratePerm t).val=t.1.1 := by
  classical
  rw [←subsetEnumeration_image t.1]
  ext x
  simp only [Finset.mem_image,Finset.mem_univ,true_and,enumeratePerm,Function.comp_apply]
  constructor
  · rintro ⟨i,hi⟩
    exact ⟨t.2 i,hi⟩
  · rintro ⟨i,hi⟩
    exact ⟨t.2.symm i,by simpa using hi⟩

theorem enumeratePerm_bijective (h n : ℕ) :
    Function.Bijective (enumeratePerm (h:=h) (n:=n)) := by
  classical
  constructor
  · rintro ⟨S,e⟩ ⟨T,d⟩ he
    have hST : S=T := by
      apply Subtype.ext
      rw [←enumeratePerm_image (S,e),←enumeratePerm_image (T,d),he]
    subst T
    have hed : e=d := by
      apply Equiv.ext
      intro i
      apply (subsetEnumeration S).injective
      exact congrFun (congrArg Subtype.val he) i
    subst d
    rfl
  · intro b
    let S : {S : Finset (Fin h) // S.card=n} :=
      ⟨Finset.univ.image b.val,by rw [Finset.card_image_of_injective _ b.2]; simp⟩
    have he : Set.range (subsetEnumeration S)=Set.range b.val := by
      ext x
      have hh := Finset.ext_iff.mp (subsetEnumeration_image S) x
      simpa only [Finset.mem_image,Finset.mem_univ,true_and,S,Set.mem_range] using hh
    obtain ⟨e,he⟩ := injective_same_range_perm (subsetEnumeration S) b.val b.2 he
    exact ⟨(S,e),Subtype.ext he.symm⟩

theorem weightedBlock_eq_unordered {n X h a m : ℕ} (hX : 2≤X)
    (F : (Fin n → ℝ) → ℝ)
    (hsym : ∀ (e : Equiv.Perm (Fin n)) v,(∀ i,0≤v i) → F (v ∘ e)=F v) :
    weightedBlock X h a F (subsetCoefficient n) m=unorderedBlock X h a F m := by
  classical
  unfold weightedBlock
  have he : (∑ b : Fin n → Fin h, subsetCoefficient n (Setoid.ker b)*
      divisorSum X F m (fun i => a+(b i:ℕ)))=
      ∑ b : {b : Fin n → Fin h // Function.Injective b},
        (n.factorial:ℝ)⁻¹*divisorSum X F m (fun i => a+(b.val i:ℕ)) := by
    simp only [subsetCoefficient,Setoid.ker_eq_bot_iff,ite_mul,zero_mul]
    rw [←Finset.sum_filter]
    exact Finset.sum_subtype (p:=fun b : Fin n → Fin h => Function.Injective b)
      (Finset.univ.filter fun b : Fin n → Fin h => Function.Injective b) (by simp) _
  rw [he]
  rw [←Fintype.sum_equiv (Equiv.ofBijective enumeratePerm (enumeratePerm_bijective h n))
    (fun t => (n.factorial:ℝ)⁻¹*divisorSum X F m (fun i => a+((enumeratePerm t).val i:ℕ)))
    _ (fun _ => rfl)]
  rw [Fintype.sum_prod_type]
  unfold unorderedBlock
  apply Finset.sum_congr rfl
  intro S _
  have hd (e : Equiv.Perm (Fin n)) :
      divisorSum X F m (fun i => a+((enumeratePerm (S,e)).val i:ℕ))=
      divisorSum X F m (fun i => a+(subsetEnumeration S i:ℕ)) :=
    divisorSum_perm_orthant hX F hsym e (fun i => a+(subsetEnumeration S i:ℕ))
  simp only [hd,Finset.sum_const,Finset.card_univ,Fintype.card_perm,Fintype.card_fin,nsmul_eq_mul]
  have hn : (n.factorial:ℝ)≠0 := by exact_mod_cast Nat.factorial_ne_zero n
  field_simp

theorem orderedWeight_eq_unordered {tau lam : ℝ} {k X : ℕ}
    (f : (j : ℕ) → (Fin j → ℝ) → ℝ) (hf : AdmissibleFamily tau k f)
    (hX : 2≤X) (m : ℕ) : orderedWeight tau lam k f X m=unorderedWeight tau lam k f X m := by
  unfold orderedWeight unorderedWeight
  apply Finset.sum_congr rfl
  intro j _
  have hfj := hf.2.1 j (by omega : (j:ℕ)≤k)
  exact weightedBlock_eq_unordered hX _ (cumulativeProfile_perm_orthant _ hfj.2.2.1 hfj.2.2.2)

theorem unorderedWeight_fourth_bound_oai {tau lam : ℝ} {k : ℕ}
    (f : (j : ℕ) → (Fin j → ℝ) → ℝ) (hf : AdmissibleFamily tau k f)
    (htau : 0≤tau) (htau4 : 4*tau<1) (hlam : 0<lam) :
    ∃ M : ℝ,0<M ∧ ∀ᶠ X : ℕ in atTop,
      average X (fun m => unorderedWeight tau lam k f X m^4)≤M := by
  obtain ⟨M,hM,h⟩ := orderedWeight_fourth_bound f hf htau htau4 hlam
  refine ⟨M,hM,?_⟩
  filter_upwards [h,eventually_ge_atTop 2] with X hX hX2
  simpa only [orderedWeight_eq_unordered f hf hX2] using hX

end LargePrimeGaps

end OAI
end

theorem solution : type_of% @OAI.LargePrimeGaps.unorderedWeight_fourth_bound_oai := @OAI.LargePrimeGaps.unorderedWeight_fourth_bound_oai
