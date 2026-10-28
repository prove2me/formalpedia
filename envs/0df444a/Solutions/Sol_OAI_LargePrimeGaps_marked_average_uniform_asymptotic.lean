-- Prove2me | solution 1 for OAI.LargePrimeGaps.marked_average_uniform_asymptotic
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T04:54:41.415867+00:00
-- url     : https://prove2.me/submissions/2ab607c5-9c33-4c35-9809-f826060b0dcc

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

theorem theta_nonneg (n : ℕ) : 0 ≤ theta n := by
  by_cases hn : Nat.Prime n
  · simp only [theta, ite_eq_left hn]
    exact (log_pos_of_two_le hn.two_le).le
  · simp [theta, hn]

open Filter

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

theorem tupleModulus_le_prod {ι : Type*} [Fintype ι] {d : ι → ℕ}
    (hd : ∀ i, 0 < d i) : tupleModulus d ≤ ∏ i, d i :=
  Nat.le_of_dvd (Finset.prod_pos fun i _ => hd i) (tupleModulus_dvd_prod d)

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

theorem not_prime_on_nonreduced_class {m c a q : ℕ} (hq : 0 < q)
    (hmc : Nat.ModEq q m c) (hcop : ¬ Nat.Coprime (c + a) q) (hlt : q < m + a) :
    ¬ Nat.Prime (m + a) := by
  intro hp
  have hnq : Nat.Coprime (m + a) q := hp.coprime_iff_not_dvd.mpr
    (Nat.not_dvd_of_pos_of_lt hq hlt)
  apply hcop
  rw [Nat.coprime_iff_gcd_eq_one, ← (hmc.add_right a).gcd_eq]
  exact hnq.gcd_eq_one

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

theorem card_divisors_of_squarefree {q : ℕ} (hq : Squarefree q) :
    q.divisors.card = 2 ^ q.primeFactors.card := by
  rw [Nat.card_divisors hq.ne_zero]
  calc
    _ = ∏ _p ∈ q.primeFactors, (2 : ℕ) := by
      apply Finset.prod_congr rfl
      intro p hp
      have h := Nat.mem_primeFactors.mp hp
      rw [Nat.factorization_eq_one_of_squarefree hq h.1 h.2.1]
    _ = _ := by simp

theorem squarefreeModulusFiber_card_le (n Y q : ℕ) (hq : 0 < q) :
    (squarefreeModulusFiber n Y q).card ≤ (q.divisors.card) ^ n := by
  classical
  calc
    _ ≤ (Fintype.piFinset (fun _ : Fin n => q.divisors)).card := by
      apply Finset.card_le_card
      intro d hd
      have hd' := (Finset.mem_filter.mp hd).2
      apply Fintype.mem_piFinset.mpr
      intro i
      apply Nat.mem_divisors.mpr
      exact ⟨hd'.2 ▸ Finset.dvd_lcm (Finset.mem_univ i), hq.ne'⟩
    _ = _ := by simp

theorem squarefreeModulusFiber_card_le_pow (n Y q : ℕ) (hq : Squarefree q) :
    (squarefreeModulusFiber n Y q).card ≤ (2 ^ n) ^ q.primeFactors.card := by
  have h := squarefreeModulusFiber_card_le n Y q (Nat.pos_of_ne_zero hq.ne_zero)
  rw [card_divisors_of_squarefree hq, ← pow_mul, Nat.mul_comm, pow_mul] at h
  exact h

theorem markedClassError_le {X H q a c : ℕ} (ha : a ≤ H) (hc : c < q)
    (hcop : Nat.Coprime (c + a) q) :
    |(∑ m ∈ residueStarts X q c, theta (m + a)) - (X : ℝ) / q.totient| ≤
      (markedError X H q : ℝ) := by
  have hm : (a, c) ∈ (Finset.range (H + 1)) ×ˢ (Finset.range q) := by simp; omega
  have h := Finset.le_sup (f := fun ac : ℕ × ℕ =>
    if Nat.Coprime (ac.2 + ac.1) q then
      NNReal.mk (|(∑ m ∈ residueStarts X q ac.2, theta (m + ac.1)) -
        (X : ℝ) / q.totient|) (abs_nonneg _) else 0) hm
  have hr := NNReal.coe_le_coe.mpr h
  simpa only [Prod.fst, Prod.snd, ite_eq_left hcop, NNReal.coe_mk, markedError] using hr

theorem markedTupleCompatible_iff_coprime {ι : Type*} [Fintype ι]
    {d b : ι → ℕ} {a c : ℕ} (hc : c < tupleModulus d)
    (hsol : ∀ i, d i ∣ c + b i) :
    markedTupleCompatible d b a ↔ Nat.Coprime (c + a) (tupleModulus d) := by
  constructor
  · rintro ⟨c', hc', hsol', hcop'⟩
    have hmod := (tuple_divisibility_iff_modEq d b hsol c').mp hsol'
    change c' % tupleModulus d = c % tupleModulus d at hmod
    rw [Nat.mod_eq_of_lt hc', Nat.mod_eq_of_lt hc] at hmod
    simpa [hmod] using hcop'
  · intro hcop
    exact ⟨c, hc, hsol, hcop⟩

theorem markedTupleCompatible_imp {ι : Type*} [Fintype ι]
    {d b : ι → ℕ} {a : ℕ} (h : markedTupleCompatible d b a) : tupleCompatible d b := by
  obtain ⟨c, hc, hs, _⟩ := h
  exact ⟨c, hc, hs⟩

theorem markedTuple_density_error {ι : Type*} [Fintype ι]
    {X H a : ℕ} {d b : ι → ℕ} (hd : ∀ i, 0 < d i)
    (hmod : tupleModulus d ≤ X) (ha : a ≤ H) :
    |(∑ m ∈ tupleStarts X d b, theta (m + a)) - (X : ℝ) * markedTupleDensity d b a| ≤
      (markedError X H (tupleModulus d) : ℝ) := by
  classical
  by_cases h : tupleCompatible d b
  · obtain ⟨c, hc, hsol⟩ := h
    by_cases hcop : Nat.Coprime (c + a) (tupleModulus d)
    · rw [tupleStarts_eq_residueStarts X d b hc hsol, markedTupleDensity,
        ite_eq_left ((markedTupleCompatible_iff_coprime hc hsol).mpr hcop)]
      simpa only [div_eq_mul_inv] using markedClassError_le (X := X) ha hc hcop
    · have hr : ¬ markedTupleCompatible d b a :=
        fun hr => hcop ((markedTupleCompatible_iff_coprime hc hsol).mp hr)
      have hz : ∑ m ∈ tupleStarts X d b, theta (m + a) = 0 := by
        apply Finset.sum_eq_zero
        intro m hm
        obtain ⟨hmX, hmdiv⟩ := Finset.mem_filter.mp hm
        have hmX' := (Finset.mem_Ioc.mp hmX).1
        have hn := not_prime_on_nonreduced_class (tupleModulus_pos hd)
          ((tuple_divisibility_iff_modEq d b hsol m).mp hmdiv) hcop (by omega)
        simp [theta, hn]
      simp only [hz, markedTupleDensity, ite_eq_right hr, mul_zero, sub_zero, abs_zero]
      exact NNReal.coe_nonneg _
  · rw [tupleStarts_eq_empty_of_incompatible X hd h]
    have hr : ¬ markedTupleCompatible d b a := fun hr => h (markedTupleCompatible_imp hr)
    simp only [Finset.sum_empty, markedTupleDensity, ite_eq_right hr, mul_zero, sub_zero, abs_zero]
    exact NNReal.coe_nonneg _

theorem markedTupleCompatible_iff_local {ι : Type*} [Fintype ι]
    {d b : ι → ℕ} {a : ℕ} (hd : ∀ i, Squarefree (d i)) :
    markedTupleCompatible d b a ↔ markedLocalCompatible d b a := by
  constructor
  · intro h
    refine ⟨localCompatible_of_tupleCompatible (markedTupleCompatible_imp h), ?_⟩
    obtain ⟨c, _, hsol, hcop⟩ := h
    intro p hp hpq i hpi hba
    have hcb : Nat.ModEq p (c + b i) 0 := Nat.modEq_zero_iff_dvd.mpr (hpi.trans (hsol i))
    have hca : p ∣ c + a := Nat.modEq_zero_iff_dvd.mp ((hba.add_left c).symm.trans hcb)
    exact (Nat.not_coprime_of_dvd_of_dvd hp.one_lt hca hpq) hcop
  · rintro ⟨hlocal, hexcl⟩
    obtain ⟨c, hc, hsol⟩ := tupleCompatible_of_localCompatible hd hlocal
    refine ⟨c, hc, hsol, ?_⟩
    by_contra hcop
    obtain ⟨p, hp, hpca, hpq⟩ := Nat.Prime.not_coprime_iff_dvd.mp hcop
    obtain ⟨i, _, hpi⟩ := (hp.prime.dvd_finsetProd_iff d).mp
      (hpq.trans (tupleModulus_dvd_prod d))
    apply hexcl p hp hpq i hpi
    have hcb : Nat.ModEq p (c + b i) 0 := Nat.modEq_zero_iff_dvd.mpr (hpi.trans (hsol i))
    have hca : Nat.ModEq p (c + a) 0 := Nat.modEq_zero_iff_dvd.mpr hpca
    exact Nat.ModEq.add_left_cancel (Nat.ModEq.refl c) (hcb.trans hca.symm)

theorem sum_marked_divisibility_eq {ι : Type*} [Fintype ι]
    (X a : ℕ) (s : Finset (ι → ℕ)) (A : (ι → ℕ) → ℝ) (b : ι → ℕ) :
    (∑ m ∈ Finset.Ioc X (2 * X),
      (∑ d ∈ s, if ∀ i, d i ∣ m + b i then A d else 0) * theta (m + a)) =
      ∑ d ∈ s, A d * ∑ m ∈ tupleStarts X d b, theta (m + a) := by
  classical
  simp only [Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  rw [← Finset.sum_filter, ← Finset.mul_sum]
  rfl

theorem finite_marked_density_sum_error {ι : Type*} [Fintype ι]
    {X H a : ℕ} (hX : 0 < X) (ha : a ≤ H)
    (s : Finset (ι → ℕ)) (A : (ι → ℕ) → ℝ) (b : ι → ℕ)
    (hs : ∀ d ∈ s, (∀ i, 0 < d i) ∧ tupleModulus d ≤ X) :
    |average X (fun m =>
        (∑ d ∈ s, if ∀ i, d i ∣ m + b i then A d else 0) * theta (m + a)) -
      ∑ d ∈ s, A d * markedTupleDensity d b a| ≤
      (X : ℝ)⁻¹ * ∑ d ∈ s, |A d| * (markedError X H (tupleModulus d) : ℝ) := by
  classical
  have hXR : (0 : ℝ) < X := by exact_mod_cast hX
  have hexp : average X (fun m =>
      (∑ d ∈ s, if ∀ i, d i ∣ m + b i then A d else 0) * theta (m + a)) -
        ∑ d ∈ s, A d * markedTupleDensity d b a =
      (X : ℝ)⁻¹ * ∑ d ∈ s, A d * ((∑ m ∈ tupleStarts X d b, theta (m + a)) -
        (X : ℝ) * markedTupleDensity d b a) := by
    unfold average
    rw [sum_marked_divisibility_eq]
    let T : (ι → ℕ) → ℝ := fun d => ∑ m ∈ tupleStarts X d b, theta (m + a)
    change (∑ d ∈ s, A d * T d) / X - (∑ d ∈ s, A d * markedTupleDensity d b a) =
      (X : ℝ)⁻¹ * ∑ d ∈ s, A d * (T d - (X : ℝ) * markedTupleDensity d b a)
    rw [Finset.sum_div, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro d _
    field_simp [hXR.ne']
  rw [hexp, abs_mul, abs_of_pos (inv_pos.mpr hXR)]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hXR.le)
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro d hd
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (markedTuple_density_error (hs d hd).1 (hs d hd).2 ha)
    (abs_nonneg _)

theorem squarefree_tuple_modulus_sum_bound (n Y : ℕ) (s : Finset (Fin n → ℕ))
    (E : ℕ → ℝ) (hE : ∀ q, 0 ≤ E q)
    (hbox : ∀ d ∈ s, ∀ i, d i ∈ Finset.Icc 1 Y)
    (hsq : ∀ d ∈ s, ∀ i, Squarefree (d i))
    (hmod : ∀ d ∈ s, tupleModulus d ≤ Y) :
    (∑ d ∈ s, E (tupleModulus d)) ≤
      ∑ q ∈ Finset.Icc 1 Y, if Squarefree q then
        (((2 ^ n) ^ q.primeFactors.card : ℕ) : ℝ) * E q else 0 := by
  classical
  have hmap : ∀ d ∈ s, tupleModulus d ∈ Finset.Icc 1 Y := by
    intro d hd
    exact Finset.mem_Icc.mpr ⟨tupleModulus_pos
      (fun i => (Finset.mem_Icc.mp (hbox d hd i)).1), hmod d hd⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmap]
  apply Finset.sum_le_sum
  intro q _hqY
  let T := s.filter fun d => tupleModulus d = q
  have hT : T ⊆ squarefreeModulusFiber n Y q := by
    intro d hd
    obtain ⟨hds, hdq⟩ := Finset.mem_filter.mp hd
    simp only [squarefreeModulusFiber, Finset.mem_filter, Fintype.mem_piFinset]
    exact ⟨hbox d hds, hsq d hds, hdq⟩
  have heq : (∑ d ∈ T, E (tupleModulus d)) = (T.card : ℝ) * E q := by
    calc
      _ = ∑ _d ∈ T, E q := Finset.sum_congr rfl fun d hd => by
        rw [(Finset.mem_filter.mp hd).2]
      _ = _ := by simp
  change (∑ d ∈ T, E (tupleModulus d)) ≤ _
  rw [heq]
  by_cases hq : Squarefree q
  · rw [ite_eq_left hq]
    have hcard := (Finset.card_le_card hT).trans (squarefreeModulusFiber_card_le_pow n Y q hq)
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (hE q)
  · rw [ite_eq_right hq]
    have hT0 : T = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro d hd
      obtain ⟨hds, hdq⟩ := Finset.mem_filter.mp hd
      exact hq (hdq ▸ tupleModulus_squarefree (hsq d hds))
    simp [hT0]

theorem divisorSum_eq_squarefree_product_bounded {n X : ℕ} (hX : 2 ≤ X)
    {F : (Fin n → ℝ) → ℝ} {rho : ℝ} (hbudget : HasBudget F rho)
    (m : ℕ) (hm : 0 < m) (b : Fin n → ℕ) :
    divisorSum X F m b =
      ∑ d ∈ squarefreeProductTuples n ⌊Real.exp (rho * Real.log (X : ℝ))⌋₊,
        if ∀ i, d i ∣ m + b i then divisorCoefficient X F d else 0 := by
  classical
  rw [divisorSum_eq_product_bounded hX hbudget m hm b]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro d hd hnot
  have hz : divisorCoefficient X F d = 0 := by
    by_contra hne
    exact hnot (Finset.mem_filter.mpr ⟨hd, (divisorCoefficient_ne_zero_iff.mp hne).1⟩)
  simp only [hz, ite_self]

theorem floor_support_le_X {X : ℕ} (hX : 2 ≤ X) {rho : ℝ} (hrho1 : rho ≤ 1) :
    ⌊Real.exp (rho * Real.log (X : ℝ))⌋₊ ≤ X := by
  have hXR : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  apply Nat.floor_le_of_le
  calc
    Real.exp (rho * Real.log (X : ℝ)) ≤ Real.exp (Real.log (X : ℝ)) := by
      apply Real.exp_le_exp.mpr
      nlinarith [log_pos_of_two_le hX]
    _ = _ := Real.exp_log hXR

theorem marked_arithmetic_error {n X H a : ℕ} (hX : 2 ≤ X) (ha : a ≤ H)
    {F : (Fin n → ℝ) → ℝ} {rho M : ℝ} (hrho1 : rho ≤ 1)
    (hbudget : HasBudget F rho) (hM : 0 ≤ M)
    (hbound : ∀ v, (∀ i, 0 ≤ v i) → |F v| ≤ M) (b : Fin n → ℕ) :
    |average X (fun m => divisorSum X F m b * theta (m + a)) -
      markedDensitySum X F rho b a| ≤
      M / (X : ℝ) * ∑ q ∈ Finset.Icc 1 ⌊Real.exp (rho * Real.log (X : ℝ))⌋₊,
        if Squarefree q then (((2 ^ n) ^ q.primeFactors.card : ℕ) : ℝ) *
          (markedError X H q : ℝ) else 0 := by
  classical
  let Y : ℕ := ⌊Real.exp (rho * Real.log (X : ℝ))⌋₊
  let s := squarefreeProductTuples n Y
  have hbox : ∀ d ∈ s, ∀ i, d i ∈ Finset.Icc 1 Y := by
    intro d hd i
    exact Fintype.mem_piFinset.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hd).1).1 i
  have hpos : ∀ d ∈ s, ∀ i, 0 < d i := fun d hd i => (Finset.mem_Icc.mp (hbox d hd i)).1
  have hsq : ∀ d ∈ s, ∀ i, Squarefree (d i) := fun d hd => (Finset.mem_filter.mp hd).2
  have hmod : ∀ d ∈ s, tupleModulus d ≤ Y := by
    intro d hd
    exact (tupleModulus_le_prod (hpos d hd)).trans (Finset.mem_filter.mp (Finset.mem_filter.mp hd).1).2
  have hs : ∀ d ∈ s, (∀ i, 0 < d i) ∧ tupleModulus d ≤ X :=
    fun d hd => ⟨hpos d hd, (hmod d hd).trans (floor_support_le_X hX hrho1)⟩
  have he := finite_marked_density_sum_error (by omega : 0 < X) ha s (divisorCoefficient X F) b hs
  have hexp : average X (fun m => divisorSum X F m b * theta (m + a)) =
      average X (fun m => (∑ d ∈ s, if ∀ i, d i ∣ m + b i then
        divisorCoefficient X F d else 0) * theta (m + a)) := by
    unfold average
    congr 1
    apply Finset.sum_congr rfl
    intro m hm
    dsimp only
    rw [divisorSum_eq_squarefree_product_bounded hX hbudget m (by
      have := (Finset.mem_Ioc.mp hm).1
      omega) b]
  rw [hexp]
  have he' : |average X (fun m => (∑ d ∈ s, if ∀ i, d i ∣ m + b i then
        divisorCoefficient X F d else 0) * theta (m + a)) - markedDensitySum X F rho b a| ≤
      (X : ℝ)⁻¹ * ∑ d ∈ s, |divisorCoefficient X F d| *
        (markedError X H (tupleModulus d) : ℝ) := by
    convert he using 1
    congr 2
    unfold average
    congr 1
    apply Finset.sum_congr rfl
    intro m _
    dsimp only
    congr 1
    apply Finset.sum_congr rfl
    intro d _
    split_ifs <;> rfl
  apply he'.trans
  have hcoeff : ∑ d ∈ s, |divisorCoefficient X F d| *
      (markedError X H (tupleModulus d) : ℝ) ≤
      M * ∑ d ∈ s, (markedError X H (tupleModulus d) : ℝ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro d hd
    exact mul_le_mul_of_nonneg_right
      ((abs_divisorCoefficient_le X F d).trans (hbound _ (logCoordinates_nonneg hX (hpos d hd))))
      (NNReal.coe_nonneg _)
  have hgroup := squarefree_tuple_modulus_sum_bound n Y s
    (fun q => (markedError X H q : ℝ)) (fun q => NNReal.coe_nonneg _) hbox hsq hmod
  calc
    (X : ℝ)⁻¹ * ∑ d ∈ s, |divisorCoefficient X F d| *
        (markedError X H (tupleModulus d) : ℝ) ≤
      (X : ℝ)⁻¹ * (M * ∑ d ∈ s, (markedError X H (tupleModulus d) : ℝ)) :=
        mul_le_mul_of_nonneg_left hcoeff (by positivity)
    _ ≤ (X : ℝ)⁻¹ * (M * ∑ q ∈ Finset.Icc 1 Y, if Squarefree q then
        (((2 ^ n) ^ q.primeFactors.card : ℕ) : ℝ) * (markedError X H q : ℝ) else 0) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hgroup hM) (by positivity)
    _ = _ := by ring

end LargePrimeGaps

end OAI
end

section
-- module Solutions.OAIW2_P344.PrimeGaps_OrthantIntegrals
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

theorem divisorMultiplicity_one (k : ℕ) : divisorMultiplicity k 1 = 1 := by
  exact (ArithmeticFunction.isMultiplicative_zeta.pow).1

theorem divisorMultiplicity_succ (k n : ℕ) :
    divisorMultiplicity (k+1) n = ∑ d ∈ n.divisors, divisorMultiplicity k d := by
  simp only [divisorMultiplicity, pow_succ, ArithmeticFunction.mul_zeta_apply]

theorem divisorMultiplicity_prime (k : ℕ) {p : ℕ} (hp : Nat.Prime p) :
    divisorMultiplicity k p = k := by
  induction k with
  | zero => simp [divisorMultiplicity, hp.ne_one]
  | succ k ih =>
    rw [divisorMultiplicity_succ, hp.divisors]
    simp [hp.ne_one.symm, divisorMultiplicity_one, ih, Nat.add_comm]

theorem divisorMultiplicity_squarefree (k : ℕ) {q : ℕ} (hq : Squarefree q) :
    divisorMultiplicity k q = k ^ q.primeFactors.card := by
  rw [divisorMultiplicity, ← ArithmeticFunction.IsMultiplicative.prod_primeFactors
    (ArithmeticFunction.isMultiplicative_zeta.pow) hq]
  calc
    _ = ∏ p ∈ q.primeFactors, k := Finset.prod_congr rfl fun p hp =>
      divisorMultiplicity_prime k (Nat.prime_of_mem_primeFactors hp)
    _ = _ := by simp

theorem reciprocal_divisor_sum_le (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n) (Q : ℕ) :
    (∑ q ∈ Finset.Icc 1 Q, (∑ d ∈ q.divisors, f d) / (q : ℝ)) ≤
      (∑ d ∈ Finset.Icc 1 Q, f d / (d : ℝ)) * (harmonic Q : ℝ) := by
  classical
  let s := (Finset.Icc 1 Q).sigma fun q => q.divisors
  let t := (Finset.Icc 1 Q) ×ˢ (Finset.Icc 1 Q)
  let e : (a : ℕ) × ℕ → ℕ × ℕ := fun x => (x.2, x.1/x.2)
  have he_mem : ∀ x ∈ s, e x ∈ t := by
    rintro ⟨q,d⟩ hx
    obtain ⟨hq, hd⟩ := Finset.mem_sigma.mp hx
    obtain ⟨hq1,hqQ⟩ := Finset.mem_Icc.mp hq
    obtain ⟨hdq,hq0⟩ := Nat.mem_divisors.mp hd
    have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdq hq1
    have hdle : d ≤ q := Nat.le_of_dvd hq1 hdq
    have hdivpos : 0 < q/d := Nat.div_pos hdle hd0
    exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨hd0, hdle.trans hqQ⟩,
      Finset.mem_Icc.mpr ⟨hdivpos, (Nat.div_le_self q d).trans hqQ⟩⟩
  have he_inj : Set.InjOn e s := by
    rintro ⟨q,d⟩ hx ⟨q',d'⟩ hy he
    obtain ⟨hq,hd⟩ := Finset.mem_sigma.mp hx
    obtain ⟨hq',hd'⟩ := Finset.mem_sigma.mp hy
    have hed : d = d' := congrArg Prod.fst he
    have heq : q/d = q'/d' := congrArg Prod.snd he
    have hdq : d ∣ q := (Nat.mem_divisors.mp hd).1
    have hdq' : d' ∣ q' := (Nat.mem_divisors.mp hd').1
    have hqq : q = q' := by
      rw [← Nat.div_mul_cancel hdq, ← Nat.div_mul_cancel hdq', heq, hed]
    subst d'
    subst q'
    rfl
  have hsum : (∑ q ∈ Finset.Icc 1 Q, (∑ d ∈ q.divisors, f d) / (q : ℝ)) =
      ∑ x ∈ s, f (e x).1 / (e x).1 / (e x).2 := by
    dsimp only [s]
    rw [Finset.sum_sigma]
    apply Finset.sum_congr rfl
    intro q hq
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro d hd
    have hdq := (Nat.mem_divisors.mp hd).1
    dsimp only [e]
    rw [div_div, ← Nat.cast_mul, Nat.mul_div_cancel' hdq]
  rw [hsum]
  calc
    _ = ∑ x ∈ s.image e, f x.1 / (x.1 : ℝ) / (x.2 : ℝ) := by
      rw [Finset.sum_image he_inj]
    _ ≤ ∑ x ∈ t, f x.1 / (x.1 : ℝ) / (x.2 : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.image_subset_iff.mpr he_mem)
        (fun x _ _ => div_nonneg (div_nonneg (hf _) (Nat.cast_nonneg _)) (Nat.cast_nonneg _))
    _ = _ := by
      simp only [t, Finset.sum_product, div_eq_mul_inv, Finset.sum_mul, Finset.mul_sum,
        harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
      rw [Finset.sum_comm]

theorem sum_divisorMultiplicity_reciprocal_le (k Q : ℕ) :
    (∑ q ∈ Finset.Icc 1 Q, (divisorMultiplicity k q : ℝ) / (q : ℝ)) ≤
      (harmonic Q : ℝ) ^ k := by
  induction k with
  | zero =>
    by_cases hQ : Q = 0
    · subst Q; simp
    · have hQ1 : 1 ≤ Q := Nat.one_le_iff_ne_zero.mpr hQ
      simp [divisorMultiplicity, ArithmeticFunction.one_apply, ite_div, hQ1]
  | succ k ih =>
    have h := reciprocal_divisor_sum_le (fun n => (divisorMultiplicity k n : ℝ))
      (fun n => Nat.cast_nonneg _) Q
    simp only [divisorMultiplicity_succ, Nat.cast_sum] at ⊢
    apply h.trans
    rw [pow_succ]
    exact mul_le_mul_of_nonneg_right ih (by
      simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
      exact Finset.sum_nonneg fun _ _ => inv_nonneg.mpr (Nat.cast_nonneg _))

theorem squarefree_reciprocal_weight_bound (T Q : ℕ) :
    (∑ q ∈ Finset.Icc 1 Q, if Squarefree q then (T : ℝ)^q.primeFactors.card / q else 0) ≤
      (harmonic Q : ℝ)^T := by
  classical
  apply (Finset.sum_le_sum (g := fun q => (divisorMultiplicity T q : ℝ)/(q:ℝ)) ?_).trans
    (sum_divisorMultiplicity_reciprocal_le T Q)
  intro q _
  split_ifs with hq
  · rw [divisorMultiplicity_squarefree T hq, Nat.cast_pow]
  · positivity

theorem squarefree_totient_lower {q : ℕ} (hq : Squarefree q) :
    q ≤ 2 ^ q.primeFactors.card * q.totient := by
  rw [Nat.totient_eq_div_primeFactors_mul, Nat.prod_primeFactors_of_squarefree hq,
    Nat.div_self (Nat.pos_of_ne_zero hq.ne_zero), one_mul]
  calc
    q = ∏ p ∈ q.primeFactors, p := (Nat.prod_primeFactors_of_squarefree hq).symm
    _ ≤ ∏ p ∈ q.primeFactors, 2 * (p-1) := by
      apply Finset.prod_le_prod'
      intro p hp
      have := (Nat.prime_of_mem_primeFactors hp).two_le
      omega
    _ = _ := by rw [Finset.prod_mul_distrib, Finset.prod_const]

theorem weighted_error_square_bound (K Q : ℕ) (E : ℕ → ℝ) (hE : ∀ q, 0 ≤ E q)
    {X L : ℝ} (hX : 0 ≤ X) (hL : 0 ≤ L)
    (hb : ∀ q ∈ Finset.Icc 1 Q, Squarefree q →
      E q ≤ X/(q:ℝ) * (L + 2^q.primeFactors.card)) :
    (∑ q ∈ Finset.Icc 1 Q, if Squarefree q then (K:ℝ)^q.primeFactors.card * E q else 0)^2 ≤
      (∑ q ∈ Finset.Icc 1 Q, E q) * X *
        (L * (harmonic Q : ℝ)^(K^2) + (harmonic Q : ℝ)^(2*K^2)) := by
  classical
  let s := Finset.Icc 1 Q
  let w : ℕ → ℝ := fun q => if Squarefree q then (K:ℝ)^q.primeFactors.card else 0
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq s (fun q => Real.sqrt (E q))
    (fun q => w q * Real.sqrt (E q))
  have heq1 : ∀ q, Real.sqrt (E q) * (w q * Real.sqrt (E q)) = w q * E q := by
    intro q
    calc
      _ = w q * (Real.sqrt (E q))^2 := by ring
      _ = _ := by rw [Real.sq_sqrt (hE q)]
  simp only [heq1, mul_pow, Real.sq_sqrt (hE _)] at hcs
  have hsecond : (∑ q ∈ s, w q ^ 2 * E q) ≤
      X * (L * (harmonic Q : ℝ)^(K^2) + (harmonic Q : ℝ)^(2*K^2)) := by
    have hterm : ∀ q ∈ s, w q^2 * E q ≤
        X * (L * (if Squarefree q then ((K^2:ℕ):ℝ)^q.primeFactors.card / q else 0) +
          (if Squarefree q then ((2*K^2:ℕ):ℝ)^q.primeFactors.card / q else 0)) := by
      intro q hq
      have hqR : (0 : ℝ) < q := by exact_mod_cast (Finset.mem_Icc.mp hq).1
      by_cases hsq : Squarefree q
      · simp only [w, ite_eq_left hsq]
        calc
          _ ≤ ((K:ℝ)^q.primeFactors.card)^2 * (X/(q:ℝ) * (L+2^q.primeFactors.card)) :=
            mul_le_mul_of_nonneg_left (hb q hq hsq) (sq_nonneg _)
          _ = _ := by
            rw [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow, mul_pow, ← pow_mul, Nat.mul_comm,
              pow_mul]
            ring
      · simp [w, hsq]
    calc
      _ ≤ ∑ q ∈ s, X * (L *
          (if Squarefree q then ((K^2:ℕ):ℝ)^q.primeFactors.card / q else 0) +
          (if Squarefree q then ((2*K^2:ℕ):ℝ)^q.primeFactors.card / q else 0)) :=
        Finset.sum_le_sum hterm
      _ = X * (L * (∑ q ∈ s, if Squarefree q then ((K^2:ℕ):ℝ)^q.primeFactors.card/q else 0) +
          ∑ q ∈ s, if Squarefree q then ((2*K^2:ℕ):ℝ)^q.primeFactors.card/q else 0) := by
        simp only [Finset.mul_sum, Finset.sum_add_distrib, mul_add]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (add_le_add (mul_le_mul_of_nonneg_left (squarefree_reciprocal_weight_bound (K^2) Q) hL)
          (squarefree_reciprocal_weight_bound (2*K^2) Q)) hX
  have hsumE : 0 ≤ ∑ q ∈ s, E q := Finset.sum_nonneg fun q _ => hE q
  have h := hcs.trans (mul_le_mul_of_nonneg_left hsecond hsumE)
  simp only [w, ite_mul, zero_mul] at h
  simpa only [mul_assoc] using h

theorem markedClassError_trivial {X H q a c : ℕ} (hX : 1 ≤ X) (hq : 0 < q)
    (hqX : q ≤ X) (ha : a ≤ H) (hc : c < q) (hsq : Squarefree q) :
    |(∑ m ∈ residueStarts X q c, theta (m+a)) - (X:ℝ)/q.totient| ≤
      (X:ℝ)/(q:ℝ) * (3 * Real.log (2*X+H) + 2^q.primeFactors.card) := by
  have hqR : (0:ℝ) < q := by exact_mod_cast hq
  have hphi : (0:ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
  have hXq : (1:ℝ) ≤ (X:ℝ)/q := (le_div_iff₀ hqR).mpr (by simpa using (show (q:ℝ) ≤ X by exact_mod_cast hqX))
  have hboundpos : (1:ℝ) ≤ 2*X+H := by exact_mod_cast (show 1 ≤ 2*X+H by omega)
  have hlog : 0 ≤ Real.log (2*X+H) := Real.log_nonneg hboundpos
  have htheta : ∀ m ∈ residueStarts X q c, theta (m+a) ≤ Real.log (2*X+H) := by
    intro m hm
    have hmhi := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hm).1).2
    by_cases hp : Nat.Prime (m+a)
    · rw [theta, ite_eq_left hp]
      exact Real.log_le_log (by exact_mod_cast hp.pos) (by exact_mod_cast (show m+a ≤ 2*X+H by omega))
    · simpa [theta, hp]
  have hsum : (∑ m ∈ residueStarts X q c, theta (m+a)) ≤
      3 * ((X:ℝ)/q) * Real.log (2*X+H) := by
    calc
      _ ≤ ∑ m ∈ residueStarts X q c, Real.log (2*X+H) := Finset.sum_le_sum htheta
      _ = ((residueStarts X q c).card:ℝ) * Real.log (2*X+H) := by simp
      _ ≤ ((X:ℝ)/q+2) * Real.log (2*X+H) := by
        apply mul_le_mul_of_nonneg_right _ hlog
        have hh := (abs_le.mp (residueStarts_card_error X hq hc)).2
        linarith
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) hlog
  have htot : (X:ℝ)/q.totient ≤ (X:ℝ)/q * (2:ℝ)^q.primeFactors.card := by
    have ht : (q:ℝ) ≤ (2:ℝ)^q.primeFactors.card * q.totient := by
      exact_mod_cast squarefree_totient_lower hsq
    apply (div_le_iff₀ hphi).mpr
    have hx := mul_le_mul_of_nonneg_left ht (show 0 ≤ (X:ℝ)/q by positivity)
    field_simp at hx ⊢
    nlinarith
  calc
    _ ≤ (∑ m ∈ residueStarts X q c, theta (m+a)) + (X:ℝ)/q.totient := by
      have hs0 : 0 ≤ ∑ m ∈ residueStarts X q c, theta (m+a) :=
        Finset.sum_nonneg fun m _ => theta_nonneg (m+a)
      have ht0 : 0 ≤ (X:ℝ)/q.totient := by positivity
      exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩
    _ ≤ 3 * ((X:ℝ)/q) * Real.log (2*X+H) + (X:ℝ)/q * 2^q.primeFactors.card :=
      add_le_add hsum htot
    _ = _ := by ring

theorem markedError_trivial {X H q : ℕ} (hX : 1 ≤ X) (hq : 0 < q)
    (hqX : q ≤ X) (hsq : Squarefree q) :
    (markedError X H q : ℝ) ≤
      (X:ℝ)/(q:ℝ) * (3 * Real.log (2*X+H) + 2^q.primeFactors.card) := by
  have hnonneg : 0 ≤ (X:ℝ)/(q:ℝ) *
      (3 * Real.log (2*X+H) + 2^q.primeFactors.card) := by
    have : 0 ≤ Real.log (2*X+H) := Real.log_nonneg (by
      exact_mod_cast (show 1 ≤ 2*X+H by omega))
    positivity
  change markedError X H q ≤ NNReal.mk _ hnonneg
  apply Finset.sup_le
  rintro ⟨a,c⟩ hac
  have ha : a ≤ H := by simpa using (Finset.mem_product.mp hac).1
  have hc : c < q := Finset.mem_range.mp (Finset.mem_product.mp hac).2
  dsimp only
  split_ifs
  · exact markedClassError_trivial hX hq hqX ha hc hsq
  · exact zero_le

theorem residuePrefix_sub (f : ℕ → ℝ) {L U : ℕ} (hLU : L ≤ U) (q c : ℕ) :
    residuePrefix f U q c - residuePrefix f L q c = residueSlice f L U q c := by
  classical
  have hunion : Finset.Ioc 0 U = Finset.Ioc 0 L ∪ Finset.Ioc L U := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_union]
    omega
  have hd : Disjoint ((Finset.Ioc 0 L).filter fun n => n % q = c)
      ((Finset.Ioc L U).filter fun n => n % q = c) := by
    apply Finset.disjoint_left.mpr
    intro n hn hm
    have hl := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hn).1).2
    have hu := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hm).1).1
    omega
  simp only [residuePrefix, residueSlice, hunion, Finset.filter_union, Finset.sum_union hd]
  ring

theorem shifted_sum_eq_residueSlice (f : ℕ → ℝ) (X q a : ℕ) {c : ℕ} (hc : c < q) :
    (∑ m ∈ residueStarts X q c, f (m+a)) =
      residueSlice f (X+a) (2*X+a) q ((c+a)%q) := by
  classical
  apply Finset.sum_bij (fun m _ => m+a)
  · intro m hm
    obtain ⟨hm,hmc⟩ := Finset.mem_filter.mp hm
    obtain ⟨hmlo,hmhi⟩ := Finset.mem_Ioc.mp hm
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Ioc.mpr ⟨by omega, by omega⟩, ?_⟩
    have hh : Nat.ModEq q m c := by
      change m % q = c % q
      rw [hmc, Nat.mod_eq_of_lt hc]
    exact hh.add_right a
  · intro m _ n _ heq
    omega
  · intro n hn
    obtain ⟨hn,hnc⟩ := Finset.mem_filter.mp hn
    obtain ⟨hnlo,hnhi⟩ := Finset.mem_Ioc.mp hn
    have ha : a ≤ n := by omega
    refine ⟨n-a, Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨by omega, by omega⟩, ?_⟩,
      Nat.sub_add_cancel ha⟩
    have hh : Nat.ModEq q ((n-a)+a) (c+a) := by
      change ((n-a)+a) % q = (c+a) % q
      simpa only [Nat.sub_add_cancel ha] using hnc
    have hhc := Nat.ModEq.add_right_cancel' a hh
    simpa only [Nat.ModEq, Nat.mod_eq_of_lt hc] using hhc
  · intro m _
    rfl

end LargePrimeGaps

end OAI
end

section
-- module Solutions.OAIW2_P344.PrimeGaps_MangoldtBounds
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

theorem theta_le_vonMangoldt (n : ℕ) : theta n ≤ ArithmeticFunction.vonMangoldt n := by
  by_cases hn : Nat.Prime n
  · simp [theta, hn, ArithmeticFunction.vonMangoldt_apply_prime hn]
  · simp [theta, hn]

theorem sum_vonMangoldt_sub_theta (Y : ℕ) :
    (∑ n ∈ Finset.Ioc 0 Y, (ArithmeticFunction.vonMangoldt n - theta n)) =
      Chebyshev.psi Y - Chebyshev.theta Y := by
  simp only [Finset.sum_sub_distrib, Chebyshev.psi, Chebyshev.theta, Nat.floor_natCast,
    theta, Finset.sum_filter]

theorem residueSlice_nonneg (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n) (L U q c : ℕ) :
    0 ≤ residueSlice f L U q c := Finset.sum_nonneg fun n _ => hf n

theorem residueSlice_primepower_error {U : ℕ} (hU : 1 ≤ U) (L q c : ℕ) :
    |residueSlice ArithmeticFunction.vonMangoldt L U q c - residueSlice theta L U q c| ≤
      2 * Real.sqrt U * Real.log U := by
  have hdiff : 0 ≤ residueSlice ArithmeticFunction.vonMangoldt L U q c -
      residueSlice theta L U q c := by
    rw [residueSlice, residueSlice, ← Finset.sum_sub_distrib]
    exact Finset.sum_nonneg fun n _ => sub_nonneg.mpr (theta_le_vonMangoldt n)
  rw [abs_of_nonneg hdiff, residueSlice, residueSlice, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ n ∈ Finset.Ioc 0 U, (ArithmeticFunction.vonMangoldt n - theta n) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro n hn
        obtain ⟨hn,_⟩ := Finset.mem_filter.mp hn
        obtain ⟨hnL,hnU⟩ := Finset.mem_Ioc.mp hn
        exact Finset.mem_Ioc.mpr ⟨by omega, hnU⟩
      · intro n _ _
        exact sub_nonneg.mpr (theta_le_vonMangoldt n)
    _ = Chebyshev.psi U - Chebyshev.theta U := sum_vonMangoldt_sub_theta U
    _ ≤ _ := Chebyshev.psi_sub_theta_le (by exact_mod_cast hU)

theorem residueSlice_theta_le {L U bound : ℕ} (hU : U ≤ bound) (hb : 1 ≤ bound)
    (q c : ℕ) : residueSlice theta L U q c ≤ (U-L:ℕ) * Real.log bound := by
  have hlog : 0 ≤ Real.log (bound:ℝ) := Real.log_nonneg (by exact_mod_cast hb)
  calc
    _ ≤ ∑ n ∈ (Finset.Ioc L U).filter (fun n => n % q = c), Real.log bound := by
      apply Finset.sum_le_sum
      intro n hn
      have hnU := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hn).1).2
      by_cases hp : Nat.Prime n
      · rw [theta, ite_eq_left hp]
        exact Real.log_le_log (by exact_mod_cast hp.pos) (by exact_mod_cast hnU.trans hU)
      · simpa [theta, hp]
    _ = (((Finset.Ioc L U).filter (fun n => n % q = c)).card:ℝ) * Real.log bound := by simp
    _ ≤ (U-L:ℕ) * Real.log bound := by
      apply mul_le_mul_of_nonneg_right _ hlog
      exact_mod_cast (Finset.card_filter_le (Finset.Ioc L U) (fun n => n % q = c)).trans_eq
        (Nat.card_Ioc L U)

theorem residueSlice_theta_shift_error {X H a : ℕ} (hX : 1 ≤ X) (ha : a ≤ H) (q c : ℕ) :
    |residueSlice theta (X+a) (2*X+a) q c - residueSlice theta X (2*X) q c| ≤
      2*(H:ℝ) * Real.log (2*X+H) := by
  have hid : residueSlice theta (X+a) (2*X+a) q c - residueSlice theta X (2*X) q c =
      residueSlice theta (2*X) (2*X+a) q c - residueSlice theta X (X+a) q c := by
    rw [← residuePrefix_sub theta (by omega), ← residuePrefix_sub theta (by omega),
      ← residuePrefix_sub theta (by omega), ← residuePrefix_sub theta (by omega)]
    ring
  rw [hid]
  have hA := residueSlice_theta_le (L := 2*X) (U := 2*X+a) (bound := 2*X+H)
    (by omega) (by omega) q c
  have hB := residueSlice_theta_le (L := X) (U := X+a) (bound := 2*X+H)
    (by omega) (by omega) q c
  simp only [Nat.add_sub_cancel_left, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hA hB
  have hA0 := residueSlice_nonneg theta theta_nonneg (2*X) (2*X+a) q c
  have hB0 := residueSlice_nonneg theta theta_nonneg X (X+a) q c
  have haR : (a:ℝ) ≤ H := by exact_mod_cast ha
  have hlog : 0 ≤ Real.log (2*(X:ℝ)+H) := Real.log_nonneg (by
    exact_mod_cast (show 1 ≤ 2*X+H by omega))
  have hah := mul_le_mul_of_nonneg_right haR hlog
  exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩

theorem endpointClassError_le (X : ℕ) {q c : ℕ} (hc : c < q) (hcop : Nat.Coprime c q) :
    |residuePrefix ArithmeticFunction.vonMangoldt X q c - (X:ℝ)/q.totient| ≤
      (endpointError X q : ℝ) := by
  have h := Finset.le_sup (f := fun c => if Nat.Coprime c q then
    NNReal.mk (|residuePrefix ArithmeticFunction.vonMangoldt ⌊(X:ℝ)⌋₊ q c -
      (X:ℝ)/q.totient|) (abs_nonneg _) else 0) (Finset.mem_range.mpr hc)
  have hr := NNReal.coe_le_coe.mpr h
  simpa only [ite_eq_left hcop, NNReal.coe_mk, Nat.floor_natCast, endpointError] using hr

theorem residueSlice_vonMangoldt_endpoint_error (X : ℕ) {q c : ℕ}
    (hc : c < q) (hcop : Nat.Coprime c q) :
    |residueSlice ArithmeticFunction.vonMangoldt X (2*X) q c - (X:ℝ)/q.totient| ≤
      (endpointError (2*X:ℕ) q : ℝ) + (endpointError X q : ℝ) := by
  rw [← residuePrefix_sub _ (by omega)]
  have hid : residuePrefix ArithmeticFunction.vonMangoldt (2*X) q c -
      residuePrefix ArithmeticFunction.vonMangoldt X q c - (X:ℝ)/q.totient =
      (residuePrefix ArithmeticFunction.vonMangoldt (2*X) q c - ((2*X:ℕ):ℝ)/q.totient) -
      (residuePrefix ArithmeticFunction.vonMangoldt X q c - (X:ℝ)/q.totient) := by
    push_cast
    ring
  rw [hid]
  exact (abs_sub _ _).trans (add_le_add (endpointClassError_le (2*X) hc hcop)
    (endpointClassError_le X hc hcop))

theorem markedClassError_le_endpointErrors {X H q a c : ℕ} (hX : 1 ≤ X)
    (ha : a ≤ H) (hc : c < q) (hcop : Nat.Coprime (c+a) q) :
    |(∑ m ∈ residueStarts X q c, theta (m+a)) - (X:ℝ)/q.totient| ≤
      (endpointError (2*X:ℕ) q : ℝ) + (endpointError X q : ℝ) +
        2 * Real.sqrt (2*(X:ℝ)) * Real.log (2*(X:ℝ)) +
        2*(H:ℝ) * Real.log (2*X+H) := by
  let r := (c+a)%q
  have hq : 0 < q := by omega
  have hr : r < q := Nat.mod_lt _ hq
  have hrcop : Nat.Coprime r q := by
    change Nat.gcd ((c+a)%q) q = 1
    rw [← Nat.gcd_rec q (c+a), Nat.gcd_comm]
    exact hcop
  rw [shifted_sum_eq_residueSlice theta X q a hc]
  have hs := residueSlice_theta_shift_error hX ha q r
  have hp := residueSlice_primepower_error (U := 2*X) (by omega) X q r
  have he := residueSlice_vonMangoldt_endpoint_error X hr hrcop
  have htri := abs_sub_le (residueSlice theta (X+a) (2*X+a) q r)
    (residueSlice theta X (2*X) q r) ((X:ℝ)/q.totient)
  have htri' := abs_sub_le (residueSlice theta X (2*X) q r)
    (residueSlice ArithmeticFunction.vonMangoldt X (2*X) q r) ((X:ℝ)/q.totient)
  rw [abs_sub_comm (residueSlice ArithmeticFunction.vonMangoldt _ _ _ _)] at hp
  norm_cast at hp
  simpa only [r] using (show |residueSlice theta (X+a) (2*X+a) q r - (X:ℝ)/q.totient| ≤
      (endpointError (2*X:ℕ) q : ℝ) + (endpointError X q : ℝ) +
        2 * Real.sqrt (2*(X:ℝ)) * Real.log (2*(X:ℝ)) +
        2*(H:ℝ) * Real.log (2*X+H) by
    push_cast at hp
    linarith)

theorem markedError_le_endpointErrors {X H q : ℕ} (hX : 1 ≤ X) :
    (markedError X H q : ℝ) ≤
      (endpointError (2*X:ℕ) q : ℝ) + (endpointError X q : ℝ) +
        2 * Real.sqrt (2*(X:ℝ)) * Real.log (2*(X:ℝ)) +
        2*(H:ℝ) * Real.log (2*X+H) := by
  have hlog : 0 ≤ Real.log (2*(X:ℝ)) := Real.log_nonneg (by
    exact_mod_cast (show 1 ≤ 2*X by omega))
  have hlog' : 0 ≤ Real.log (2*(X:ℝ)+H) := Real.log_nonneg (by
    exact_mod_cast (show 1 ≤ 2*X+H by omega))
  have hnonneg : 0 ≤ (endpointError (2*X:ℕ) q : ℝ) + (endpointError X q : ℝ) +
      2 * Real.sqrt (2*(X:ℝ)) * Real.log (2*(X:ℝ)) +
      2*(H:ℝ) * Real.log (2*X+H) := by positivity
  change markedError X H q ≤ NNReal.mk _ hnonneg
  apply Finset.sup_le
  rintro ⟨a,c⟩ hac
  have ha : a ≤ H := by simpa using (Finset.mem_product.mp hac).1
  have hc : c < q := Finset.mem_range.mp (Finset.mem_product.mp hac).2
  dsimp only
  split_ifs with hcop
  · exact markedClassError_le_endpointErrors hX ha hc hcop
  · exact zero_le

theorem sum_markedError_le_endpointErrors {X : ℕ} (hX : 1 ≤ X) (H Q : ℕ) :
    (∑ q ∈ Finset.Icc 1 Q, (markedError X H q : ℝ)) ≤
      (∑ q ∈ Finset.Icc 1 Q, (endpointError (2*X:ℕ) q : ℝ)) +
      (∑ q ∈ Finset.Icc 1 Q, (endpointError X q : ℝ)) +
      (Q:ℝ) * (2 * Real.sqrt (2*(X:ℝ)) * Real.log (2*(X:ℝ)) +
        2*(H:ℝ) * Real.log (2*X+H)) := by
  apply (Finset.sum_le_sum (fun q _ => markedError_le_endpointErrors (H:=H) (q:=q) hX)).trans_eq
  simp only [Finset.sum_add_distrib, Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel,
    nsmul_eq_mul]
  ring

theorem eventually_rpow_le_BV_range {rho : ℝ} (hrho : rho < 1/2) (b : ℝ) :
    ∀ᶠ x : ℝ in atTop, x^rho ≤ x^(1/2:ℝ) * (Real.log x)^(-b) := by
  have h := (isLittleO_log_rpow_rpow_atTop b (show (0:ℝ) < 1/2-rho by linarith)).bound
    (show (0:ℝ) < 1 by norm_num)
  filter_upwards [h, eventually_gt_atTop 1] with x hx hx1
  have hx0 : 0 < x := by linarith
  have hL : 0 < Real.log x := Real.log_pos hx1
  simp only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hL.le _),
    abs_of_nonneg (Real.rpow_nonneg hx0.le _), one_mul] at hx
  rw [Real.rpow_neg hL.le, ← div_eq_mul_inv]
  apply (le_div_iff₀ (Real.rpow_pos_of_pos hL b)).mpr
  calc
    _ ≤ x^rho * x^(1/2-rho) := mul_le_mul_of_nonneg_left hx (Real.rpow_nonneg hx0.le _)
    _ = _ := by rw [← Real.rpow_add hx0]; congr 1; ring

theorem endpoint_error_sum_nonneg (x : ℝ) (Q : ℕ) :
    0 ≤ ∑ q ∈ Finset.Icc 1 Q, (endpointError x q : ℝ) := by positivity

theorem endpoint_sum_log_decay (hBV : BombieriVinogradov) {rho : ℝ}
    (hrho : 0 ≤ rho) (hrhohalf : rho < 1/2) {k : ℕ} (hk : 1 ≤ k) (A : ℕ) :
    Tendsto (fun X : ℕ =>
      ((∑ q ∈ Finset.Icc 1 (powerModulus rho X), (endpointError (k*X:ℕ) q : ℝ)) / X) *
        (Real.log (X:ℝ))^A) atTop (nhds 0) := by
  obtain ⟨b,hb,M,hM,x₀,hx₀,hest⟩ := hBV (A+1) (by positivity)
  have hkR : (0:ℝ) < k := by exact_mod_cast (show 0<k by omega)
  have hXlim : Tendsto (fun X : ℕ => (X:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hkXlim : Tendsto (fun X : ℕ => ((k*X:ℕ):ℝ)) atTop atTop := by
    simpa only [Nat.cast_mul] using hXlim.const_mul_atTop hkR
  have hLlim : Tendsto (fun X : ℕ => Real.log (X:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp hXlim
  have hlim : Tendsto (fun X : ℕ => (M*(k:ℝ)) / Real.log (X:ℝ)) atTop (nhds 0) := by
    simpa only [div_eq_mul_inv, mul_zero, Function.comp_def] using
      (tendsto_inv_atTop_zero.comp hLlim).const_mul (M*(k:ℝ))
  apply squeeze_zero' _ _ hlim
  · filter_upwards [eventually_ge_atTop 2] with X hX
    exact mul_nonneg (div_nonneg (endpoint_error_sum_nonneg _ _) (Nat.cast_nonneg _))
      (pow_nonneg (log_pos_of_two_le hX).le _)
  · filter_upwards [eventually_ge_atTop 2, hkXlim.eventually (eventually_ge_atTop x₀),
        hkXlim.eventually (eventually_rpow_le_BV_range hrhohalf b)] with X hX hx hcut
    have hX0 : (0:ℝ) < X := by exact_mod_cast (show 0<X by omega)
    have hLX : 0 < Real.log (X:ℝ) := log_pos_of_two_le hX
    have hkX0 : (0:ℝ) < ((k*X:ℕ):ℝ) := by positivity
    have hXkX : (X:ℝ) ≤ ((k*X:ℕ):ℝ) := by exact_mod_cast (Nat.le_mul_of_pos_left X hk)
    have hLle : Real.log (X:ℝ) ≤ Real.log ((k*X:ℕ):ℝ) := Real.log_le_log hX0 hXkX
    have hQ : powerModulus rho X ≤
        ⌊(((k*X:ℕ):ℝ))^(1/2:ℝ) * (Real.log ((k*X:ℕ):ℝ))^(-b)⌋₊ :=
      Nat.floor_le_floor ((Real.rpow_le_rpow hX0.le hXkX hrho).trans hcut)
    have hsum : (∑ q ∈ Finset.Icc 1 (powerModulus rho X),
        (endpointError (k*X:ℕ) q : ℝ)) ≤
        M * ((k*X:ℕ):ℝ) * (Real.log ((k*X:ℕ):ℝ))^(-(A+1:ℝ)) := by
      apply le_trans _ (hest _ hx)
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc le_rfl hQ)
      intro q _ _
      exact NNReal.coe_nonneg _
    have hlogpow : (Real.log ((k*X:ℕ):ℝ))^(-(A+1:ℝ)) ≤
        (Real.log (X:ℝ))^(-(A+1:ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hLX hLle (by have := Nat.cast_nonneg (α:=ℝ) A; linarith)
    calc
      _ ≤ (M * ((k*X:ℕ):ℝ) * (Real.log ((k*X:ℕ):ℝ))^(-(A+1:ℝ)) / X) *
          (Real.log (X:ℝ))^A :=
        mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hsum hX0.le) (by positivity)
      _ ≤ (M * ((k*X:ℕ):ℝ) * (Real.log (X:ℝ))^(-(A+1:ℝ)) / X) *
          (Real.log (X:ℝ))^A := by gcongr
      _ = (M*(k:ℝ)) / Real.log (X:ℝ) := by
        rw [Real.rpow_neg hLX.le]
        have hnat : (A:ℝ)+1 = ((A+1:ℕ):ℝ) := by push_cast; rfl
        rw [hnat, Real.rpow_natCast, pow_succ, Nat.cast_mul]
        field_simp

theorem polylog_shift_eventually_le (H : ℕ → ℕ) {D B : ℝ}
    (hH : ∀ᶠ X : ℕ in atTop, (H X:ℝ) ≤ D*(Real.log (X:ℝ))^B) :
    ∀ᶠ X : ℕ in atTop, H X ≤ X := by
  have hlim : Tendsto (fun X : ℕ => D * ((Real.log (X:ℝ))^B / (X:ℝ)))
      atTop (nhds 0) := by
    have hh := ((isLittleO_log_rpow_rpow_atTop B (show (0:ℝ)<1 by norm_num)).tendsto_div_nhds_zero
      ).comp tendsto_natCast_atTop_atTop
    simpa only [Real.rpow_one, Function.comp_def, mul_zero] using hh.const_mul D
  filter_upwards [hH, hlim.eventually (gt_mem_nhds (show (0:ℝ)<1 by norm_num)),
    eventually_ge_atTop 1] with X hHX hsmall hX
  have hX0 : (0:ℝ)<X := by exact_mod_cast (show 0<X by omega)
  have hh : D*(Real.log (X:ℝ))^B ≤ (X:ℝ) := by
    rw [← mul_div_assoc] at hsmall
    exact (div_lt_one hX0).mp hsmall |>.le
  exact_mod_cast hHX.trans hh

theorem log_shift_bound {X H : ℕ} (hX : 3 ≤ X) (hH : H ≤ X) :
    Real.log (2*(X:ℝ)+H) ≤ 2 * Real.log (X:ℝ) := by
  have hX3 : (3:ℝ) ≤ X := by exact_mod_cast hX
  have hHle : (H:ℝ) ≤ X := by exact_mod_cast hH
  have hX0 : (0:ℝ)<X := by linarith
  calc
    _ ≤ Real.log ((X:ℝ)^2) := Real.log_le_log (by positivity) (by nlinarith)
    _ = _ := by rw [Real.log_pow]; norm_num

theorem power_log_identity {x L : ℝ} (hx : 0<x) (rho b : ℝ) :
    x^rho * x^b * L / x = L / x^(1-rho-b) := by
  rw [div_eq_mul_inv L, ← Real.rpow_neg hx.le]
  have he : -(1-rho-b) = rho+b-1 := by ring
  rw [he, Real.rpow_sub hx, Real.rpow_add hx, Real.rpow_one]
  ring

theorem primepower_shift_tail_log_decay (H : ℕ → ℕ) {rho D B : ℝ}
    (hrhohalf : rho < 1/2) (hD : 0 < D)
    (hH : ∀ᶠ X : ℕ in atTop, (H X:ℝ) ≤ D*(Real.log (X:ℝ))^B) (A : ℕ) :
    Tendsto (fun X : ℕ =>
      ((powerModulus rho X:ℝ) *
        (2*Real.sqrt (2*(X:ℝ))*Real.log (2*(X:ℝ)) +
          2*(H X:ℝ)*Real.log (2*(X:ℝ)+H X)) / X) *
        (Real.log (X:ℝ))^A) atTop (nhds 0) := by
  have hlim1 : Tendsto (fun X : ℕ =>
      (Real.log (X:ℝ))^((A:ℝ)+1) / (X:ℝ)^(1/2-rho)) atTop (nhds 0) := by
    exact ((isLittleO_log_rpow_rpow_atTop ((A:ℝ)+1) (by linarith)).tendsto_div_nhds_zero
      ).comp tendsto_natCast_atTop_atTop
  have hlim2 : Tendsto (fun X : ℕ =>
      (Real.log (X:ℝ))^(B+(A:ℝ)+1) / (X:ℝ)^(1-rho)) atTop (nhds 0) := by
    exact ((isLittleO_log_rpow_rpow_atTop (B+(A:ℝ)+1) (by linarith)).tendsto_div_nhds_zero
      ).comp tendsto_natCast_atTop_atTop
  have hlim := (hlim1.const_mul 8).add (hlim2.const_mul (4*D))
  simp only [mul_zero, add_zero] at hlim
  apply squeeze_zero' _ _ hlim
  · filter_upwards [eventually_ge_atTop 3] with X hX
    have hlog1 : 0 ≤ Real.log (2*(X:ℝ)) := Real.log_nonneg (by
      exact_mod_cast (show 1 ≤ 2*X by omega))
    have hlog2 : 0 ≤ Real.log (2*(X:ℝ)+H X) := Real.log_nonneg (by
      exact_mod_cast (show 1 ≤ 2*X+H X by omega))
    have hlog : 0 ≤ Real.log (X:ℝ) := (log_pos_of_two_le (by omega)).le
    positivity
  · filter_upwards [hH, polylog_shift_eventually_le H hH,
      eventually_ge_atTop 3] with X hHX hHX' hX
    have hX0 : (0:ℝ)<X := by exact_mod_cast (show 0<X by omega)
    have hL : 0<Real.log (X:ℝ) := log_pos_of_two_le (by omega)
    have hlog1 : Real.log (2*(X:ℝ)) ≤ 2*Real.log (X:ℝ) := by
      simpa only [Nat.cast_zero, add_zero] using log_shift_bound (H:=0) hX (Nat.zero_le X)
    have hlog2 := log_shift_bound hX hHX'
    have hlog1' : 0 ≤ Real.log (2*(X:ℝ)) := Real.log_nonneg (by
      exact_mod_cast (show 1 ≤ 2*X by omega))
    have hlog2' : 0 ≤ Real.log (2*(X:ℝ)+H X) := Real.log_nonneg (by
      exact_mod_cast (show 1 ≤ 2*X+H X by omega))
    have hroot : Real.sqrt (2*(X:ℝ)) ≤ 2*(X:ℝ)^(1/2:ℝ) := by
      rw [← Real.sqrt_eq_rpow]
      apply (Real.sqrt_le_left (by positivity)).mpr
      nlinarith [Real.sq_sqrt hX0.le]
    have hQ : (powerModulus rho X:ℝ) ≤ (X:ℝ)^rho :=
      Nat.floor_le (Real.rpow_nonneg hX0.le _)
    calc
      _ ≤ ((X:ℝ)^rho *
          (2*(2*(X:ℝ)^(1/2:ℝ))*(2*Real.log (X:ℝ)) +
            2*(D*(Real.log (X:ℝ))^B)*(2*Real.log (X:ℝ))) / X) *
          (Real.log (X:ℝ))^A := by gcongr
      _ = 8*((Real.log (X:ℝ))^((A:ℝ)+1)/(X:ℝ)^(1/2-rho)) +
          (4*D)*((Real.log (X:ℝ))^(B+(A:ℝ)+1)/(X:ℝ)^(1-rho)) := by
        have hLA : (Real.log (X:ℝ))^((A:ℝ)+1) = (Real.log (X:ℝ))^A * Real.log (X:ℝ) := by
          rw [Real.rpow_add hL, Real.rpow_natCast, Real.rpow_one]
        have hLBA : (Real.log (X:ℝ))^(B+(A:ℝ)+1) =
            (Real.log (X:ℝ))^B * (Real.log (X:ℝ))^A * Real.log (X:ℝ) := by
          rw [Real.rpow_add hL, Real.rpow_add hL, Real.rpow_natCast, Real.rpow_one]
        rw [hLA, hLBA]
        have h1 := power_log_identity (L:=Real.log (X:ℝ)) hX0 rho (1/2)
        have h2 := power_log_identity (L:=Real.log (X:ℝ)) hX0 rho 0
        simp only [Real.rpow_zero, mul_one, sub_zero] at h2
        have hex : (1:ℝ)-rho-1/2 = 1/2-rho := by ring
        rw [hex] at h1
        calc
          _ = 8 * (Real.log (X:ℝ))^A *
                ((X:ℝ)^rho*(X:ℝ)^(1/2:ℝ)*Real.log (X:ℝ)/(X:ℝ)) +
              (4*D)*(Real.log (X:ℝ))^B*(Real.log (X:ℝ))^A *
                ((X:ℝ)^rho*Real.log (X:ℝ)/(X:ℝ)) := by ring
          _ = _ := by rw [h1,h2]; ring

theorem marked_error_sum_log_decay (hBV : BombieriVinogradov) (H : ℕ → ℕ)
    {rho D B : ℝ} (hrho : 0 ≤ rho) (hrhohalf : rho < 1/2) (hD : 0 < D)
    (hH : ∀ᶠ X : ℕ in atTop, (H X:ℝ) ≤ D*(Real.log (X:ℝ))^B) (A : ℕ) :
    Tendsto (fun X : ℕ =>
      ((∑ q ∈ Finset.Icc 1 (powerModulus rho X), (markedError X (H X) q : ℝ)) / X) *
        (Real.log (X:ℝ))^A) atTop (nhds 0) := by
  have h1 := endpoint_sum_log_decay hBV hrho hrhohalf (k:=1) (by norm_num) A
  have h2 := endpoint_sum_log_decay hBV hrho hrhohalf (k:=2) (by norm_num) A
  have htail := primepower_shift_tail_log_decay H hrhohalf hD hH A
  have hlim := (h2.add h1).add htail
  simp only [add_zero, one_mul] at hlim
  apply squeeze_zero' _ _ hlim
  · filter_upwards [eventually_ge_atTop 2] with X hX
    have hL := (log_pos_of_two_le hX).le
    positivity
  · filter_upwards [eventually_ge_atTop 2] with X hX
    have hh := mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right (sum_markedError_le_endpointErrors (X:=X) (by omega)
        (H X) (powerModulus rho X)) (show (0:ℝ)≤X by positivity))
      (pow_nonneg (log_pos_of_two_le hX).le A)
    convert hh using 1
    · rfl
    ring

theorem harmonic_nonneg_real (Q : ℕ) : 0 ≤ (harmonic Q : ℝ) := by
  simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  positivity

theorem harmonic_le_twice_log {Q X : ℕ} (hQX : Q ≤ X) (hL : 1 ≤ Real.log (X:ℝ)) :
    (harmonic Q : ℝ) ≤ 2 * Real.log (X:ℝ) := by
  have hmono : (harmonic Q : ℝ) ≤ (harmonic X : ℝ) := by
    simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hQX) (by intros; positivity)
  have hh := harmonic_le_one_add_log X
  linarith

theorem powerModulus_le {rho : ℝ} (hrho : rho ≤ 1) {X : ℕ} (hX : 1 ≤ X) :
    powerModulus rho X ≤ X := by
  have hX1 : (1:ℝ) ≤ X := by exact_mod_cast hX
  have hh := Real.rpow_le_rpow_of_exponent_le hX1 hrho
  rw [Real.rpow_one] at hh
  have hfloor := Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg X) rho)
  exact_mod_cast hfloor.trans hh

theorem marked_error_weight_budget (K : ℕ) {X H Q : ℕ}
    (hX : 3 ≤ X) (hH : H ≤ X) (hQ : Q ≤ X) (hL : 1 ≤ Real.log (X:ℝ)) :
    3*Real.log (2*(X:ℝ)+H)*(harmonic Q:ℝ)^(K^2) +
      (harmonic Q:ℝ)^(2*K^2) ≤
    (6*(2:ℝ)^(K^2)+(2:ℝ)^(2*K^2)) * (Real.log (X:ℝ))^(2*K^2+1) := by
  have hL0 : 0 ≤ Real.log (X:ℝ) := by linarith
  have hhar := harmonic_le_twice_log hQ hL
  have hlog := log_shift_bound hX hH
  have hpow1 : (Real.log (X:ℝ))^(K^2+1) ≤ (Real.log (X:ℝ))^(2*K^2+1) :=
    pow_le_pow_right₀ hL (by omega)
  have hpow2 : (Real.log (X:ℝ))^(2*K^2) ≤ (Real.log (X:ℝ))^(2*K^2+1) :=
    pow_le_pow_right₀ hL (by omega)
  calc
    _ ≤ (3*(2*Real.log (X:ℝ)))*(2*Real.log (X:ℝ))^(K^2) +
        (2*Real.log (X:ℝ))^(2*K^2) := by
      apply add_le_add
      · apply mul_le_mul
        · linarith
        · exact pow_le_pow_left₀ (harmonic_nonneg_real Q) hhar _
        · exact pow_nonneg (harmonic_nonneg_real Q) _
        · positivity
      · exact pow_le_pow_left₀ (harmonic_nonneg_real Q) hhar _
    _ = 6*(2:ℝ)^(K^2)*(Real.log (X:ℝ))^(K^2+1) +
        (2:ℝ)^(2*K^2)*(Real.log (X:ℝ))^(2*K^2) := by rw [mul_pow, mul_pow, pow_succ]; ring
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hpow1 (show (0:ℝ)≤6*2^(K^2) by positivity),
      mul_le_mul_of_nonneg_left hpow2 (show (0:ℝ)≤2^(2*K^2) by positivity)]

theorem weightedErrorSum_nonneg (K X H Q : ℕ) : 0 ≤ weightedErrorSum K X H Q := by
  classical
  apply Finset.sum_nonneg
  intro q _
  split_ifs <;> positivity

theorem weightedErrorSum_sq_bound (K : ℕ) {X H Q : ℕ}
    (hX : 3 ≤ X) (hH : H ≤ X) (hQ : Q ≤ X) (hL : 1 ≤ Real.log (X:ℝ)) :
    (weightedErrorSum K X H Q)^2 ≤
      (∑ q ∈ Finset.Icc 1 Q, (markedError X H q : ℝ)) * X *
      ((6*(2:ℝ)^(K^2)+(2:ℝ)^(2*K^2)) * (Real.log (X:ℝ))^(2*K^2+1)) := by
  have hlog : 0 ≤ 3 * Real.log (2*(X:ℝ)+H) := by
    have hh : 0 ≤ Real.log (2*(X:ℝ)+H) := Real.log_nonneg (by
      exact_mod_cast (show 1 ≤ 2*X+H by omega))
    positivity
  apply (weighted_error_square_bound K Q (fun q => (markedError X H q : ℝ))
    (fun q => NNReal.coe_nonneg _) (Nat.cast_nonneg X) hlog ?_).trans
  · apply mul_le_mul_of_nonneg_left (marked_error_weight_budget K hX hH hQ hL)
    positivity
  · intro q hq hsq
    obtain ⟨hq1,hqQ⟩ := Finset.mem_Icc.mp hq
    exact markedError_trivial (by omega) hq1 (hqQ.trans hQ) hsq

theorem weightedErrorSum_log_decay (hBV : BombieriVinogradov) (K : ℕ) (H : ℕ → ℕ)
    {rho D B : ℝ} (hrho : 0 ≤ rho) (hrhohalf : rho < 1/2) (hD : 0 < D)
    (hH : ∀ᶠ X : ℕ in atTop, (H X:ℝ) ≤ D*(Real.log (X:ℝ))^B) (A : ℕ) :
    Tendsto (fun X : ℕ => (weightedErrorSum K X (H X) (powerModulus rho X) / X) *
      (Real.log (X:ℝ))^A) atTop (nhds 0) := by
  let c : ℝ := 6*(2:ℝ)^(K^2)+(2:ℝ)^(2*K^2)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hlim := (marked_error_sum_log_decay hBV H hrho hrhohalf hD hH
    (2*K^2+1+2*A)).const_mul c
  simp only [mul_zero] at hlim
  have hsqrt := hlim.sqrt
  simp only [Real.sqrt_zero] at hsqrt
  have hLlim : Tendsto (fun X : ℕ => Real.log (X:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  apply squeeze_zero' _ _ hsqrt
  · filter_upwards [eventually_ge_atTop 2] with X hX
    exact mul_nonneg (div_nonneg (weightedErrorSum_nonneg _ _ _ _) (Nat.cast_nonneg _))
      (pow_nonneg (log_pos_of_two_le hX).le _)
  · filter_upwards [eventually_ge_atTop 3, polylog_shift_eventually_le H hH,
      hLlim.eventually (eventually_ge_atTop 1)] with X hX hHX hLX
    have hX0 : (0:ℝ)<X := by exact_mod_cast (show 0<X by omega)
    have hs := weightedErrorSum_sq_bound K hX hHX
      (powerModulus_le (by linarith : rho ≤ 1) (by omega)) hLX
    have hh : ((weightedErrorSum K X (H X) (powerModulus rho X) / X) *
        (Real.log (X:ℝ))^A)^2 ≤
        c * (((∑ q ∈ Finset.Icc 1 (powerModulus rho X), (markedError X (H X) q : ℝ)) / X) *
          (Real.log (X:ℝ))^(2*K^2+1+2*A)) := by
      have hm := mul_le_mul_of_nonneg_right hs
        (show 0 ≤ (Real.log (X:ℝ))^(2*A)/(X:ℝ)^2 by positivity)
      dsimp only [c]
      convert hm using 1
      · rfl
      · rw [mul_pow, div_pow, ← pow_mul, Nat.mul_comm A 2]
        ring
      · rw [pow_add]
        field_simp
    have hnonneg : 0 ≤ (weightedErrorSum K X (H X) (powerModulus rho X) / X) *
        (Real.log (X:ℝ))^A := by
      apply mul_nonneg (div_nonneg (weightedErrorSum_nonneg _ _ _ _) hX0.le)
      exact pow_nonneg (by linarith) _
    have hh' := Real.sqrt_le_sqrt hh
    simpa only [Real.sqrt_sq hnonneg] using hh'

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

theorem mem_markedResidueFamily {ι : Type*} [Fintype ι] (b : ι → ℤ) (p : ℕ) (a : ℤ) (S : Finset ι) :
    S∈markedResidueFamily b p a ↔ S.Nonempty ∧
      (∀ i∈S, ∀ j∈S, b i%(p:ℤ)=b j%(p:ℤ)) ∧ ∀ i∈S, b i%(p:ℤ)≠a%(p:ℤ) := by
  rw [markedResidueFamily, mem_fiberSubsetFamily]
  constructor
  · rintro ⟨hS,r,hr,hb⟩
    exact ⟨hS,(fun i hi j hj => (hb i hi).trans (hb j hj).symm),fun i hi =>
      (hb i hi) ▸ (Finset.mem_erase.mp hr).1⟩
  · rintro ⟨hS,hb,ha⟩
    rcases hS with ⟨i,hi⟩
    exact ⟨⟨i,hi⟩, b i%(p:ℤ),Finset.mem_erase.mpr ⟨ha i hi,
      Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩,fun j hj => hb j hj i hi⟩

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

theorem markedResidueFamily_eq_shiftFamily {ι : Type*} [Fintype ι] (b : ι → ℤ) (p : ℕ) (a : ℤ)
    (h : ∀ i j, b i%(p:ℤ)=b j%(p:ℤ) → b i=b j) (ha : ∀ i, b i%(p:ℤ)≠a%(p:ℤ)) :
    markedResidueFamily b p a=shiftFamily b := by
  rw [markedResidueFamily]
  have hn : a%(p:ℤ)∉(Finset.univ.image fun i => b i%(p:ℤ)) := by
    intro hm
    rcases Finset.mem_image.mp hm with ⟨i,_,hi⟩
    exact ha i hi
  rw [Finset.erase_eq_of_notMem hn]
  exact residueFamily_eq_shiftFamily b p h

theorem one_sub_prime_inv_ne_zero {p : ℕ} (hp : 2≤p) : 1-(p:ℂ)⁻¹≠0 := by
  have hpR : (2:ℝ)≤p := by exact_mod_cast hp
  have hr : 1-(p:ℝ)⁻¹≠0 := by
    have := (inv_lt_one₀ (by linarith : 0<(p:ℝ))).mpr (by linarith : 1<(p:ℝ))
    linarith
  have hc : ((1-(p:ℝ)⁻¹:ℝ):ℂ)≠0 := by exact_mod_cast hr
  simpa using hc

theorem residueCount_insert_eq (H : Finset ℤ) (p : ℕ) (a : ℤ) :
    residueCount (insert a H) p = ((H.image fun b => b%(p:ℤ)).erase (a%(p:ℤ))).card+1 := by
  unfold residueCount
  rw [Finset.image_insert]
  have h := Finset.card_erase_add_one (Finset.mem_insert_self (a%(p:ℤ))
    (H.image fun b => b%(p:ℤ)))
  simpa only [Finset.erase_insert_eq_erase] using h.symm

theorem eulerH_marked_zero {ι : Type*} [Fintype ι] (b : ι → ℤ) (a : ℤ)
    (ha : ∀ i, b i≠a) {p : ℕ} (hp : 2≤p) :
    eulerH p 1 (markedResidueFamily b p a) (shiftFamily b) (fun _ => 0) =
      (singularLocal (insert a (Finset.univ.image b)) p : ℂ) := by
  have ha' : a∉Finset.univ.image b := by
    simpa only [Finset.mem_image, Finset.mem_univ, true_and, not_exists] using ha
  rw [markedResidueFamily, shiftFamily, eulerH_zero_fiber_families p 1 _ _ _ _
    (fun r hr => by
      rcases Finset.mem_image.mp (Finset.mem_erase.mp hr).2 with ⟨i,_,hi⟩
      exact ⟨i,hi⟩)
    (fun r hr => by rcases Finset.mem_image.mp hr with ⟨i,_,hi⟩; exact ⟨i,hi⟩)
    (one_sub_prime_inv_ne_zero hp)]
  have hp0 : (p:ℂ)≠0 := by exact_mod_cast (by omega : p≠0)
  have hp1 : (p:ℂ)-1≠0 := by
    intro he
    have hh : (p:ℂ)=1 := sub_eq_zero.mp he
    have : p=1 := by exact_mod_cast hh
    omega
  have hpinv := one_sub_prime_inv_ne_zero hp
  simp only [Nat.cast_one, zpow_neg, zpow_natCast, singularLocal,
    residueCount_insert_eq, Finset.card_insert_of_notMem ha', Finset.image_image, Function.comp_def]
  push_cast
  rw [pow_succ]
  field_simp
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

theorem markedResidueFamily_generic_of_bound {ι : Type*} [Fintype ι] (b : ι → ℤ)
    (a : ℤ) (ha : ∀ i, b i≠a) {D p : ℕ} (hb : ∀ i, (b i).natAbs≤D)
    (haD : a.natAbs≤D) (hp : 2*D<p) :
    markedResidueFamily b p a=shiftFamily b :=
  markedResidueFamily_eq_shiftFamily b p a
    (fun i j he => eq_of_emod_eq_of_bound (hb i) (hb j) hp he)
    (fun i he => ha i (eq_of_emod_eq_of_bound (hb i) haD hp he))

theorem subsetFamily_card_le {ι : Type*} [Fintype ι] (S : Finset (Finset ι)) :
    S.card≤2^Fintype.card ι := by
  classical
  simpa only [Fintype.card_finset] using Finset.card_le_univ S

theorem singularSeries_cast_hasProd (H : Finset ℤ) :
    HasProd (fun p : Nat.Primes => (singularLocal H p : ℂ)) (singularSeries H : ℂ) := by
  exact (singularSeries_multipliable H).hasProd.map Complex.ofRealHom.toMonoidHom
    Complex.continuous_ofReal

theorem marked_eulerGlobal_zero {ι : Type*} [Fintype ι] (b : ι → ℤ) (a : ℤ)
    (ha : ∀ i, b i≠a) :
    eulerGlobal 1 (fun p => markedResidueFamily b p a) (shiftFamily b) (fun _ => 0) =
      (singularSeries (insert a (Finset.univ.image b)) : ℂ) := by
  rw [eulerGlobal]
  exact ((singularSeries_cast_hasProd _).congr_fun fun p =>
    eulerH_marked_zero b a ha p.property.two_le).tprod_eq

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

theorem tupleTotient_eq_primeSupport_prod {ι : Type*} [Fintype ι] {d : ι → ℕ}
    (hd : ∀ i, Squarefree (d i)) :
    (tupleModulus d).totient = ∏ p∈tuplePrimeSupport d, ((p:ℕ)-1) := by
  rw [tuplePrimeSupport_eq_modulus (fun i => (hd i).ne_zero)]
  change (tupleModulus d).totient = Finset.prod ((tupleModulus d).primeFactors.subtype Nat.Prime)
    (fun p : {n : ℕ // Nat.Prime n} => p.val-1)
  rw [Finset.prod_subtype_of_mem (fun p : ℕ => p-1)
    (fun p hp => Nat.prime_of_mem_primeFactors hp)]
  rw [Nat.totient_eq_div_primeFactors_mul,
    Nat.prod_primeFactors_of_squarefree (tupleModulus_squarefree hd),
    Nat.div_self (tupleModulus_pos (fun i => Nat.pos_of_ne_zero (hd i).ne_zero)), one_mul]

theorem tuplePrimeDensity_one {ι : Type*} [Fintype ι] {d : ι → ℕ}
    (hd : ∀ i, Squarefree (d i)) : tuplePrimeDensity 1 d = ((tupleModulus d).totient : ℂ)⁻¹ := by
  simp only [tuplePrimeDensity, Nat.cast_one, Finset.prod_inv_distrib]
  rw [tupleTotient_eq_primeSupport_prod hd, Nat.cast_prod]
  congr 1
  apply Finset.prod_congr rfl
  intro p _
  simp only [Nat.cast_sub p.property.one_le, Nat.cast_one]

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

theorem allowed_marked_residue_iff {ι : Type*} [Fintype ι] (d b : ι → ℕ) (a : ℕ) :
    (∀ p : Nat.Primes, (tuplePrimeSubset d p).Nonempty →
      tuplePrimeSubset d p∈markedResidueFamily (fun i => (b i:ℤ)) p a) ↔
      markedLocalCompatible d b a := by
  constructor
  · intro h
    refine ⟨?_,?_⟩
    · apply (allowed_residue_iff d b).mp
      intro p hp
      have hm := (mem_markedResidueFamily _ _ _ _).mp (h p hp)
      rw [residueFamily,mem_fiberSubsetFamily_image]
      exact ⟨hm.1,hm.2.1⟩
    · intro p hp _ i hi he
      have hm := (mem_markedResidueFamily _ _ _ _).mp
        (h ⟨p,hp⟩ ⟨i,by simp [tuplePrimeSubset,hi]⟩)
      apply hm.2.2 i (by simp [tuplePrimeSubset,hi])
      change b i % p=a % p at he
      exact_mod_cast he
  · rintro ⟨h,hmark⟩ p hp
    rw [mem_markedResidueFamily]
    have hu := (allowed_residue_iff d b).mpr h p hp
    rw [residueFamily,mem_fiberSubsetFamily_image] at hu
    refine ⟨hu.1,hu.2,?_⟩
    intro i hi he
    have hi' : p.val∣d i := by simpa [tuplePrimeSubset] using hi
    apply hmark p.val p.property (hi'.trans (Finset.dvd_lcm (Finset.mem_univ i))) i hi'
    change b i % p.val=a % p.val
    exact_mod_cast he

theorem analyticDensity_eq_marked_tsum {n : ℕ} (X : ℕ)
    (F : (Fin n → ℝ) → ℝ) (b : Fin n → ℕ) (a : ℕ) :
    analyticDensity 1 (fun p => markedResidueFamily (fun i => (b i:ℤ)) p a) (Real.log X)
      (fun v => (F v.ofLp:ℂ)) =
      ∑' d : Fin n → ℕ, ((divisorCoefficient X F d * markedTupleDensity d b a : ℝ):ℂ) := by
  let P := fun d : Fin n → ℕ => (∀ i, Squarefree (d i)) ∧
    ∀ p : Nat.Primes, (tuplePrimeSubset d p).Nonempty →
      tuplePrimeSubset d p∈markedResidueFamily (fun i => (b i:ℤ)) p a
  change (∑' d : {d // P d}, tuplePrimeDensity 1 d.val *
    (∏ i, (ArithmeticFunction.moebius (d.val i):ℂ)) *
      (F (divisorLogVector (Real.log X) d.val).ofLp:ℂ)) = _
  refine (tsum_subtype {d | P d} (fun d => tuplePrimeDensity 1 d *
    (∏ i, (ArithmeticFunction.moebius (d i):ℂ)) *
      (F (divisorLogVector (Real.log X) d).ofLp:ℂ))).trans ?_
  apply tsum_congr
  intro d
  by_cases hd : P d
  · rw [Set.indicator_of_mem (show d ∈ {d | P d} from hd), tuplePrimeDensity_one hd.1]
    have hc := (markedTupleCompatible_iff_local hd.1).mpr ((allowed_marked_residue_iff d b a).mp hd.2)
    simp only [divisorCoefficient,markedTupleDensity,ite_eq_left hc,Complex.ofReal_mul,
      Complex.ofReal_prod,Complex.ofReal_intCast,Complex.ofReal_inv,Complex.ofReal_natCast]
    change ((tupleModulus d).totient : ℂ)⁻¹ * (∏ i, (ArithmeticFunction.moebius (d i):ℂ)) *
      (F (logCoordinates X d):ℂ) = _
    ring
  · rw [Set.indicator_of_notMem (show d ∉ {d | P d} from hd)]
    have hv : divisorCoefficient X F d * markedTupleDensity d b a = 0 := by
      by_contra hv
      have hf := (divisorCoefficient_ne_zero_iff.mp (mul_ne_zero_iff.mp hv).1).1
      have hc : markedTupleCompatible d b a := by
        by_contra hc
        exact (mul_ne_zero_iff.mp hv).2 (by simp [markedTupleDensity,hc])
      exact hd ⟨hf,(allowed_marked_residue_iff d b a).mpr
        ((markedTupleCompatible_iff_local hf).mp hc)⟩
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

theorem analyticDensity_eq_markedDensitySum {n X : ℕ} (hX : 2≤X)
    {F : (Fin n → ℝ) → ℝ} {rho : ℝ} (hbudget : HasBudget F rho) (b : Fin n → ℕ) (a : ℕ) :
    analyticDensity 1 (fun p => markedResidueFamily (fun i => (b i:ℤ)) p a) (Real.log X)
      (fun v => (F v.ofLp:ℂ)) = (markedDensitySum X F rho b a : ℂ) := by
  rw [analyticDensity_eq_marked_tsum,markedDensitySum,Complex.ofReal_sum]
  apply tsum_eq_sum
  intro d hd
  have hc : divisorCoefficient X F d=0 := by
    by_contra hc
    exact hd (Finset.mem_filter.mpr ⟨divisorCoefficient_support hX hbudget hc,
      (divisorCoefficient_ne_zero_iff.mp hc).1⟩)
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

theorem markedResidueFamily_nonempty {ι : Type*} [Fintype ι] (b : ι → ℤ) (p : ℕ) (a : ℤ) :
    ∀ S∈markedResidueFamily b p a, S.Nonempty := by
  intro S hS
  exact ((mem_markedResidueFamily b p a S).mp hS).1

theorem marked_analyticDensity_uniform_asymptotic {ι : Type*} [Fintype ι]
    (F : EuclideanSpace ℝ ι → ℂ) (hF : HasCompactSupport F) (hFs : ContDiff ℝ ∞ F)
    (B : Finset (Finset ι)) (hB : ∀ S∈B, S.Nonempty) (t β : ℕ) (hβ : 0<β)
    (ht : (∑ S∈B, (-1:ℤ)^S.card) = -(t:ℤ)) :
    ∃ E : ℝ → ℝ, Tendsto E atTop (𝓝 0) ∧
      ∀ᶠ L : ℝ in atTop, ∀ b : ι → ℤ, shiftFamily b=B → ∀ a : ℤ,
      (∀ i, b i≠a) → ∀ D : ℕ, (∀ i, (b i).natAbs≤D) → a.natAbs≤D →
      2*D≤densityCutoff β L →
      ‖(L:ℂ)^t*analyticDensity 1 (fun p => markedResidueFamily b p a) L F -
        (singularSeries (insert a (Finset.univ.image b)):ℂ)*
          kernelConstant (sourceFourier (fourierCoordinateSum ι) F hF hFs) B‖ ≤ E L := by
  obtain ⟨E,hE,hbound⟩ := tupleFourier_integral_uniform_asymptotic
    (sourceFourier (fourierCoordinateSum ι) F hF hFs) B hB
    (2^Fintype.card ι) t β (subsetFamily_card_le B) hβ ht
  refine ⟨E,hE,?_⟩
  filter_upwards [hbound,eventually_gt_atTop (0:ℝ)] with L hbound hL
  intro b hb a ha D hD haD hDL
  have hA := fun p : Nat.Primes => markedResidueFamily_nonempty b p a
  have hR := fun p : Nat.Primes => subsetFamily_card_le (markedResidueFamily b p a)
  have hgen : ∀ p : Nat.Primes, densityCutoff β L<(p:ℕ) → markedResidueFamily b p a=B := by
    intro p hp
    exact (markedResidueFamily_generic_of_bound b a ha hD haD (hDL.trans_lt hp)).trans hb
  have h := hbound 1 (by omega) (fun p => markedResidueFamily b p a) hA hR hgen
  rw [← analyticDensity_eq_integral (by omega) (fun p => markedResidueFamily b p a)
    hL hA hR F hF hFs] at h
  rw [← hb,marked_eulerGlobal_zero b a ha] at h
  simpa only [hb] using h

theorem marked_average_uniform_asymptotic_oai (hBV : BombieriVinogradov) {n : ℕ}
    (F : (Fin n → ℝ) → ℝ) (rho : ℝ)
    (hrho : 0≤rho) (hrhohalf : rho<1/2) (hbudget : HasBudget F rho)
    (hF : HasCompactSupport (fun v : EuclideanSpace ℝ (Fin n) => (F v.ofLp:ℂ)))
    (hFs : ContDiff ℝ ∞ (fun v : EuclideanSpace ℝ (Fin n) => (F v.ofLp:ℂ)))
    (M : ℝ) (hM : 0≤M) (hbound : ∀ v, (∀ i, 0≤v i) → |F v|≤M)
    (B : Finset (Finset (Fin n))) (hB : ∀ S∈B, S.Nonempty)
    (t β : ℕ) (hβ : 0<β) (ht : (∑ S∈B, (-1:ℤ)^S.card) = -(t:ℤ))
    (H : ℕ → ℕ) {D₀ B₀ : ℝ} (hD₀ : 0<D₀)
    (hH : ∀ᶠ X : ℕ in atTop, (H X:ℝ)≤D₀*(Real.log (X:ℝ))^B₀) :
    ∃ E : ℕ → ℝ, Tendsto E atTop (𝓝 0) ∧
      ∀ᶠ X : ℕ in atTop, ∀ b : Fin n → ℕ,
      shiftFamily (fun i => (b i:ℤ))=B → ∀ a : ℕ, a≤H X →
      (∀ i, b i≠a) → ∀ D : ℕ, (∀ i, b i≤D) → a≤D →
      2*D≤densityCutoff β (Real.log X) →
      ‖(Real.log X:ℂ)^t*(average X (fun m => divisorSum X F m b*theta (m+a)):ℂ) -
        (singularSeries (insert (a:ℤ) (Finset.univ.image fun i => (b i:ℤ))):ℂ)*
          kernelConstant (sourceFourier (fourierCoordinateSum (Fin n))
            (fun v => (F v.ofLp:ℂ)) hF hFs) B‖ ≤ E X := by
  obtain ⟨E,hE,hEbound⟩ := marked_analyticDensity_uniform_asymptotic
    (fun v : EuclideanSpace ℝ (Fin n) => (F v.ofLp:ℂ)) hF hFs B hB t β hβ ht
  let err : ℕ → ℝ := fun X => M*(weightedErrorSum (2^n) X (H X) (powerModulus rho X)/X)*
    (Real.log (X:ℝ))^t
  have herr : Tendsto err atTop (𝓝 0) := by
    have h := (weightedErrorSum_log_decay hBV (2^n) H hrho hrhohalf hD₀ hH t).const_mul M
    simpa only [mul_zero,mul_assoc,err] using h
  have hlog : Tendsto (fun X : ℕ => Real.log (X:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  refine ⟨fun X => err X+E (Real.log X),?_,?_⟩
  · simpa only [Function.comp_def,add_zero] using herr.add (hE.comp hlog)
  filter_upwards [hlog.eventually hEbound,eventually_ge_atTop 2] with X hEX hX
  intro b hb a haH ha D hD haD hDL
  have hb' : ∀ i, ((b i:ℤ)).natAbs≤D := by simpa only [Int.natAbs_natCast] using hD
  have ha' : ∀ i, (b i:ℤ)≠(a:ℤ) := fun i he => ha i (by exact_mod_cast he)
  have hden := hEX (fun i => (b i:ℤ)) hb a ha' D hb'
    (by simpa only [Int.natAbs_natCast] using haD) hDL
  rw [analyticDensity_eq_markedDensitySum hX hbudget b a] at hden
  have hXR : (0:ℝ)<X := by exact_mod_cast (by omega : 0<X)
  have hY : ⌊Real.exp (rho*Real.log (X:ℝ))⌋₊ = powerModulus rho X := by
    unfold powerModulus
    rw [Real.rpow_def_of_pos hXR,mul_comm rho]
  have he := marked_arithmetic_error hX haH (by linarith : rho≤1) hbudget hM hbound b
  rw [hY] at he
  have he' : |average X (fun m => divisorSum X F m b*theta (m+a))-
      markedDensitySum X F rho b a| ≤
      M/X*weightedErrorSum (2^n) X (H X) (powerModulus rho X) := by
    simpa only [weightedErrorSum,Nat.cast_pow] using he
  have hcomp : ‖(Real.log X:ℂ)^t*(average X (fun m => divisorSum X F m b*theta (m+a)):ℂ)-
      (Real.log X:ℂ)^t*(markedDensitySum X F rho b a:ℂ)‖ ≤ err X := by
    rw [← mul_sub,← Complex.ofReal_sub,norm_mul,norm_pow,Complex.norm_real,
      Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs,
      abs_of_nonneg (log_pos_of_two_le hX).le]
    have hh := mul_le_mul_of_nonneg_left he' (pow_nonneg (log_pos_of_two_le hX).le t)
    convert hh using 1
    all_goals first | rfl | (simp only [err]; ring)
  apply le_trans ?_ (add_le_add hcomp hden)
  simpa only [dist_eq_norm] using (dist_triangle
    ((Real.log X:ℂ)^t*(average X (fun m => divisorSum X F m b*theta (m+a)):ℂ))
    ((Real.log X:ℂ)^t*(markedDensitySum X F rho b a:ℂ)) _)

open Topology

open scoped Convolution ContDiff Pointwise

end LargePrimeGaps

end OAI
end

theorem solution : type_of% @OAI.LargePrimeGaps.marked_average_uniform_asymptotic_oai := @OAI.LargePrimeGaps.marked_average_uniform_asymptotic_oai
