-- Prove2me | solution 1 for OAI.QuarticPowerFree.allDegrees
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T15:07:20.227607+00:00
-- url     : https://prove2.me/submissions/e1f18c91-b051-4b55-a875-b04f53c166d8

import Mathlib
import Definitions.Def_PowerFreeValues
import Definitions.Def_OAIB3Qp000
import Theorems.Thm_OAI_QuarticPowerFree_medium_degree_dyadic_tail
import Theorems.Thm_OAI_QuarticPowerFree_physical_affine_count
import Theorems.Thm_OAI_QuarticPowerFree_quartic_dyadic_tail

section
-- module Solutions.OAIB3_Qpf.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIB3_Qpf.PowerFree_Sieve
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter Asymptotics
open scoped Topology
namespace QuarticPowerFree

open Polynomial

theorem resultant_derivative_ne_zero (f : Polynomial ℤ)
    (hf : Irreducible (f.map (Int.castRingHom ℚ))) :
    f.resultant f.derivative ≠ 0 := by
  have h := Polynomial.resultant_ne_zero _ _ hf.separable
  rw [Polynomial.derivative_map,
    Polynomial.natDegree_map_eq_of_injective Int.cast_injective,
    Polynomial.natDegree_map_eq_of_injective Int.cast_injective,
    Polynomial.resultant_map_map] at h
  intro hz
  apply h
  rw [hz]
  rfl

theorem derivative_not_dvd_of_good (f : Polynomial ℤ) (hdeg : f.natDegree ≠ 0)
    {p : ℕ} (hp : ¬ (p : ℤ) ∣ f.resultant f.derivative) {a : ℤ}
    (ha : (p : ℤ) ∣ f.eval a) : ¬ (p : ℤ) ∣ f.derivative.eval a := by
  obtain ⟨u, v, _, _, h⟩ := Polynomial.exists_mul_add_mul_eq_C_resultant f
    f.derivative le_rfl le_rfl (Or.inl hdeg)
  have he := congrArg (Polynomial.eval a) h
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C] at he
  intro hd
  apply hp
  rw [← he]
  exact dvd_add (dvd_mul_of_dvd_left ha (u.eval a)) (dvd_mul_of_dvd_left hd (v.eval a))

theorem divided_difference_eval (f : Polynomial ℤ) (a : ℤ) :
    (f /ₘ (X - C a)).eval a = f.derivative.eval a := by
  have h := congrArg (Polynomial.eval a)
    (Polynomial.divByMonic_add_X_sub_C_mul_derivative_divByMonic_eq_derivative f a)
  simpa only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C, sub_self, zero_mul, add_zero] using h

theorem eval_sub_eq_mul_divided_difference (f : Polynomial ℤ) (a b : ℤ) :
    f.eval b - f.eval a = (b - a) * (f /ₘ (X - C a)).eval b := by
  have h := congrArg (Polynomial.eval b)
    (Polynomial.X_sub_C_mul_divByMonic_eq_sub_modByMonic f a)
  simpa only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_C, Polynomial.modByMonic_X_sub_C_eq_C_eval] using h.symm

theorem prime_power_root_unique (f : Polynomial ℤ) {p k : ℕ} (hp : p.Prime)
    {a b : ℤ} (ha : (p : ℤ) ^ k ∣ f.eval a) (hb : (p : ℤ) ^ k ∣ f.eval b)
    (hab : (p : ℤ) ∣ b - a) (hd : ¬ (p : ℤ) ∣ f.derivative.eval a) :
    (p : ℤ) ^ k ∣ b - a := by
  let q := f /ₘ (X - C a)
  have hq : ¬ (p : ℤ) ∣ q.eval b := by
    intro hqb
    have hdiff : (p : ℤ) ∣ q.eval b - q.eval a :=
      hab.trans (Polynomial.sub_dvd_eval_sub b a q)
    have hqa : (p : ℤ) ∣ q.eval a := by
      simpa only [sub_sub_cancel] using dvd_sub hqb hdiff
    exact hd (by simpa only [q, divided_difference_eval] using hqa)
  have hp' : Prime (p : ℤ) := Int.prime_iff_natAbs_prime.mpr (by simpa using hp)
  have hcop : IsCoprime ((p : ℤ) ^ k) (q.eval b) :=
    (hp'.coprime_iff_not_dvd.mpr hq).pow_left
  apply hcop.dvd_of_dvd_mul_left
  rw [mul_comm, ← eval_sub_eq_mul_divided_difference]
  exact dvd_sub hb ha

theorem map_zmod_ne_zero_of_good (f : Polynomial ℤ) (hdeg : f.natDegree ≠ 0)
    {p : ℕ} (hp : ¬ (p : ℤ) ∣ f.resultant f.derivative) :
    f.map (Int.castRingHom (ZMod p)) ≠ 0 := by
  intro hz
  have hd : f.derivative.map (Int.castRingHom (ZMod p)) = 0 := by
    rw [← Polynomial.derivative_map, hz, Polynomial.derivative_zero]
  have he : (p : ℤ) ∣ f.eval 0 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    have h := congrArg (Polynomial.eval (0 : ZMod p)) hz
    simpa [Polynomial.eval_zero] using h
  apply derivative_not_dvd_of_good f hdeg hp he
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  have h := congrArg (Polynomial.eval (0 : ZMod p)) hd
  simpa [Polynomial.eval_zero] using h

theorem rho_prime_pow_le_degree (f : Polynomial ℤ) (hdeg : f.natDegree ≠ 0)
    {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0)
    (hgood : ¬ (p : ℤ) ∣ f.resultant f.derivative) :
    rho f (p ^ k) ≤ f.natDegree := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  let F := f.map (Int.castRingHom (ZMod p))
  have hF : F ≠ 0 := map_zmod_ne_zero_of_good f hdeg hgood
  let s := (Finset.range (p ^ k)).filter fun a : ℕ =>
    ((p ^ k : ℕ) : ℤ) ∣ f.eval (a : ℤ)
  have hmap : Set.MapsTo (fun a : ℕ => (a : ZMod p)) (↑s) (↑F.roots.toFinset) := by
    intro a ha
    obtain ⟨_, ha⟩ := Finset.mem_filter.mp ha
    have ha' : (p : ℤ) ∣ f.eval (a : ℤ) :=
      (dvd_pow_self (p : ℤ) hk).trans (by simpa only [Nat.cast_pow] using ha)
    rw [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots hF]
    change F.eval (a : ZMod p) = 0
    rw [show F = f.map (Int.castRingHom (ZMod p)) from rfl,
      Polynomial.eval_map, ← Int.cast_natCast a (R := ZMod p)]
    change f.eval₂ (Int.castRingHom (ZMod p))
      ((Int.castRingHom (ZMod p)) (a : ℤ)) = 0
    rw [Polynomial.eval₂_at_apply]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd (f.eval (a : ℤ)) p).mpr ha'
  have hinj : Set.InjOn (fun a : ℕ => (a : ZMod p)) (↑s) := by
    intro a ha b hb hab
    obtain ⟨ha_lt, ha_root⟩ := Finset.mem_filter.mp ha
    obtain ⟨hb_lt, hb_root⟩ := Finset.mem_filter.mp hb
    rw [Finset.mem_range] at ha_lt hb_lt
    have hab' : (p : ℤ) ∣ (b : ℤ) - (a : ℤ) := by
      apply (ZMod.intCast_eq_intCast_iff_dvd_sub (a : ℤ) (b : ℤ) p).mp
      simpa only [Int.cast_natCast] using hab
    have ha' : (p : ℤ) ∣ f.eval (a : ℤ) :=
      (dvd_pow_self (p : ℤ) hk).trans (by simpa only [Nat.cast_pow] using ha_root)
    have hlarge := prime_power_root_unique f hp
      (by simpa only [Nat.cast_pow] using ha_root)
      (by simpa only [Nat.cast_pow] using hb_root) hab'
      (derivative_not_dvd_of_good f hdeg hgood ha')
    have hmod : a ≡ b [MOD p ^ k] := by
      apply Int.natCast_modEq_iff.mp
      rw [Int.modEq_iff_dvd]
      simpa only [Nat.cast_pow] using hlarge
    exact hmod.eq_of_lt_of_lt ha_lt hb_lt
  calc
    rho f (p ^ k) = s.card := rfl
    _ ≤ F.roots.toFinset.card := Finset.card_le_card_of_injOn _ hmap hinj
    _ ≤ F.roots.card := Multiset.toFinset_card_le _
    _ ≤ F.natDegree := Polynomial.card_roots' _
    _ ≤ f.natDegree := Polynomial.natDegree_map_le

theorem finite_resultant_primes (f : Polynomial ℤ)
    (hf : Irreducible (f.map (Int.castRingHom ℚ))) :
    {p : Nat.Primes | (p.val : ℤ) ∣ f.resultant f.derivative}.Finite := by
  have hn := resultant_derivative_ne_zero f hf
  have hbound : (Subtype.val ⁻¹' Set.Iic (f.resultant f.derivative).natAbs :
      Set Nat.Primes).Finite :=
    Set.Finite.preimage Subtype.val_injective.injOn (Set.finite_Iic _)
  apply hbound.subset
  intro p hp
  change p.val ≤ (f.resultant f.derivative).natAbs
  apply Nat.le_of_dvd (Int.natAbs_pos.mpr hn)
  simpa only [Int.natAbs_natCast] using Int.natAbs_dvd_natAbs.mpr hp

theorem summable_local_proportion (f : Polynomial ℤ)
    (hf : Irreducible (f.map (Int.castRingHom ℚ))) (hdeg : f.natDegree ≠ 0)
    {k : ℕ} (hk : 1 < k) :
    Summable (fun p : Nat.Primes => (rho f (p.val ^ k) : ℝ) / (p.val : ℝ) ^ k) := by
  have hs : Summable (fun p : Nat.Primes => (f.natDegree : ℝ) / (p.val : ℝ) ^ k) := by
    have hprime : Summable (fun p : Nat.Primes => (1 : ℝ) / (p.val : ℝ) ^ k) :=
      (Real.summable_one_div_nat_pow.mpr hk).comp_injective
        (i := fun p : Nat.Primes => p.val) Subtype.val_injective
    simpa only [mul_one_div] using hprime.mul_left (f.natDegree : ℝ)
  apply hs.of_norm_bounded_eventually
  filter_upwards [(finite_resultant_primes f hf).eventually_cofinite_notMem] with p hp
  have hr := rho_prime_pow_le_degree f hdeg (k := k) p.property (by omega) hp
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  apply div_le_div_of_nonneg_right (by exact_mod_cast hr) (by positivity)

theorem localFactor_pos (f : Polynomial ℤ) (k : ℕ)
    (h : LocallyAdmissible f k) (p : Nat.Primes) : 0 < localFactor f k p := by
  have hp : 0 < (p.val : ℝ) ^ k := pow_pos (by exact_mod_cast p.property.pos) _
  dsimp [localFactor]
  rw [sub_pos, div_lt_one hp]
  exact_mod_cast h p.val p.property

theorem densityConstant_converges_pos (f : Polynomial ℤ)
    (hf : Irreducible (f.map (Int.castRingHom ℚ))) (hdeg : f.natDegree ≠ 0)
    {k : ℕ} (hk : 1 < k) (hlocal : LocallyAdmissible f k) :
    Multipliable (localFactor f k) ∧ 0 < densityConstant f k := by
  have hs := (summable_local_proportion f hf hdeg hk).neg
  have hlog : Summable (fun p : Nat.Primes => Real.log (localFactor f k p)) := by
    simpa only [localFactor, sub_eq_add_neg] using
      Real.summable_log_one_add_of_summable hs
  refine ⟨Real.multipliable_of_summable_log (localFactor_pos f k hlocal) hlog, ?_⟩
  unfold densityConstant
  rw [← Real.rexp_tsum_eq_tprod (localFactor_pos f k hlocal) hlog]
  exact Real.exp_pos _

open scoped BigOperators Count

theorem count_mul_periodic (P : ℕ → Prop) [DecidablePred P] (q : ℕ)
    (hP : Function.Periodic P q) (a : ℕ) :
    Nat.count P (q * a) = a * Nat.count P q := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [Nat.mul_succ, Nat.count_add, ih]
    have hshift : (fun n => P (q * a + n)) = P := by
      funext n
      simpa [nsmul_eq_mul, mul_comm, add_comm] using hP.nsmul a n
    simp only [hshift]
    ring

theorem count_periodic_div_mod (P : ℕ → Prop) [DecidablePred P] (q N : ℕ)
    (hP : Function.Periodic P q) :
    Nat.count P N = (N / q) * Nat.count P q + Nat.count P (N % q) := by
  have hshift : (fun n => P (q * (N / q) + n)) = P := by
    funext n
    simpa [nsmul_eq_mul, mul_comm, add_comm] using hP.nsmul (N / q) n
  conv_lhs => rw [← Nat.div_add_mod N q]
  rw [Nat.count_add, count_mul_periodic P q hP]
  simp only [hshift]

theorem count_periodic_error (P : ℕ → Prop) [DecidablePred P] (q N : ℕ)
    (hq : 0 < q) (hP : Function.Periodic P q) :
    |(Nat.count P N : ℝ) - (Nat.count P q : ℝ) / q * N| ≤ q := by
  have hrem := Nat.count_le P (n := N % q)
  have hrlt := Nat.mod_lt N hq
  have hcnt := Nat.count_le P (n := q)
  have hq' : 0 < (q : ℝ) := Nat.cast_pos.mpr hq
  have hrem' : (Nat.count P (N % q) : ℝ) ≤ (N % q : ℕ) := by exact_mod_cast hrem
  have hrlt' : (N % q : ℕ) < (q : ℝ) := by exact_mod_cast hrlt
  have hcnt' : (Nat.count P q : ℝ) ≤ q := by exact_mod_cast hcnt
  have hvalue : (Nat.count P N : ℝ) - (Nat.count P q : ℝ) / q * N =
      Nat.count P (N % q) - (Nat.count P q : ℝ) / q * (N % q : ℕ) := by
    rw [count_periodic_div_mod P q N hP]
    push_cast
    have hN : (N : ℝ) = (q : ℝ) * (N / q : ℕ) + (N % q : ℕ) := by
      exact_mod_cast (Nat.div_add_mod N q).symm
    field_simp
    nlinarith [congrArg (fun x : ℝ => (Nat.count P q : ℝ) * x) hN]
  rw [hvalue, abs_le]
  have hrnon : (0 : ℝ) ≤ (N % q : ℕ) := Nat.cast_nonneg _
  have hremnon : (0 : ℝ) ≤ Nat.count P (N % q) := Nat.cast_nonneg _
  have hprop : 0 ≤ (Nat.count P q : ℝ) / q := by positivity
  have hprop' : (Nat.count P q : ℝ) / q ≤ 1 := (div_le_one hq').mpr hcnt'
  have hmul : (Nat.count P q : ℝ) / q * (N % q : ℕ) ≤ (N % q : ℕ) := by
    nlinarith
  constructor <;> nlinarith [mul_nonneg hprop hrnon]

theorem count_residues (q : ℕ) [NeZero q] (P : ZMod q → Prop)
    [DecidablePred P] :
    Nat.count (fun n : ℕ => P (n : ZMod q)) q = Fintype.card {a : ZMod q // P a} := by
  classical
  rw [Nat.count_eq_card_fintype]
  apply Fintype.card_congr
  refine {
    toFun := fun n => ⟨(n.val : ZMod q), n.property.2⟩
    invFun := fun a => ⟨a.val.val, ZMod.val_lt a.val, by simpa using a.property⟩
    left_inv := ?_
    right_inv := ?_ }
  · intro n
    apply Subtype.ext
    exact ZMod.val_natCast_of_lt n.property.1
  · intro a
    apply Subtype.ext
    exact ZMod.natCast_zmod_val a.val

theorem count_crt {ι : Type*} [Fintype ι] (m : ι → ℕ)
    (hm : ∀ i, 0 < m i) (hcoprime : Pairwise (fun i j => (m i).Coprime (m j)))
    (P : ∀ i, ZMod (m i) → Prop) [∀ i, DecidablePred (P i)] :
    Nat.count (fun n : ℕ => ∀ i, P i (n : ZMod (m i))) (∏ i, m i) =
      ∏ i, Nat.card {a : ZMod (m i) // P i a} := by
  classical
  let : ∀ i, NeZero (m i) := fun i => ⟨ne_of_gt (hm i)⟩
  let M := ∏ i, m i
  have hM : 0 < M := Finset.prod_pos (fun i _ => hm i)
  let : NeZero M := ⟨ne_of_gt hM⟩
  let e := ZMod.prodEquivPi m hcoprime
  let Q : ZMod M → Prop := fun a => ∀ i, P i (e a i)
  have hQ : (fun n : ℕ => ∀ i, P i (n : ZMod (m i))) =
      (fun n : ℕ => Q (n : ZMod M)) := by
    funext n
    dsimp [Q]
    simp only [map_natCast, Pi.natCast_apply]
  simp only [hQ]
  rw [count_residues M Q]
  calc
    _ = Fintype.card {a : (∀ i, ZMod (m i)) // ∀ i, P i (a i)} := by
      apply Fintype.card_congr
      exact e.toEquiv.subtypeEquiv (fun _ => Iff.rfl)
    _ = Fintype.card (∀ i, {a : ZMod (m i) // P i a}) :=
      Fintype.card_congr Equiv.subtypePiEquivPi
    _ = _ := by simp only [Fintype.card_pi, Nat.card_eq_fintype_card]

theorem eval_zmod_eq_zero_iff (f : Polynomial ℤ) (q n : ℕ) :
    f.eval₂ (Int.castRingHom (ZMod q)) (n : ZMod q) = 0 ↔
      (q : ℤ) ∣ f.eval (n : ℤ) := by
  rw [← Int.cast_natCast n (R := ZMod q)]
  change f.eval₂ (Int.castRingHom (ZMod q))
    ((Int.castRingHom (ZMod q)) (n : ℤ)) = 0 ↔ _
  rw [Polynomial.eval₂_at_apply]
  exact ZMod.intCast_zmod_eq_zero_iff_dvd _ _

theorem rho_le (f : Polynomial ℤ) (q : ℕ) : rho f q ≤ q :=
  (Finset.card_filter_le _ _).trans_eq (Finset.card_range q)

theorem card_good_residues (f : Polynomial ℤ) (q : ℕ) [NeZero q] :
    Fintype.card {a : ZMod q // f.eval₂ (Int.castRingHom (ZMod q)) a ≠ 0} =
      q - rho f q := by
  classical
  rw [Fintype.card_subtype_compl, ZMod.card, ← count_residues]
  simp only [eval_zmod_eq_zero_iff, Nat.count_eq_card_filter_range, rho]

theorem finite_sieve_full_period (f : Polynomial ℤ) (k : ℕ) (s : Finset Nat.Primes) :
    Nat.count (AvoidPrimes f k s) (∏ p ∈ s, p.val ^ k) =
      ∏ p ∈ s, (p.val ^ k - rho f (p.val ^ k)) := by
  classical
  have hp : ∀ p : s, 0 < p.val.val ^ k := fun p => pow_pos p.val.property.pos _
  have hcp : Pairwise (fun p q : s => (p.val.val ^ k).Coprime (q.val.val ^ k)) := by
    intro p q hpq
    apply Nat.coprime_pow_primes k k p.val.property q.val.property
    intro heq
    exact hpq (Subtype.ext (Subtype.ext heq))
  let P : ∀ p : s, ZMod (p.val.val ^ k) → Prop :=
    fun p a => f.eval₂ (Int.castRingHom (ZMod (p.val.val ^ k))) a ≠ 0
  have h := count_crt (fun p : s => p.val.val ^ k) hp hcp P
  let : ∀ p : s, NeZero (p.val.val ^ k) := fun p => ⟨ne_of_gt (hp p)⟩
  have hpred : (fun n : ℕ => ∀ p : s, P p (n : ZMod (p.val.val ^ k))) =
      AvoidPrimes f k s := by
    funext n
    dsimp [P, AvoidPrimes]
    simp only [eval_zmod_eq_zero_iff, Nat.cast_pow, Subtype.forall]
  have hqprod : (∏ p : s, p.val.val ^ k) = ∏ p ∈ s, p.val ^ k :=
    Finset.prod_coe_sort s (fun p : Nat.Primes => p.val ^ k)
  have hrprod : (∏ p : s, (p.val.val ^ k - rho f (p.val.val ^ k))) =
      ∏ p ∈ s, (p.val ^ k - rho f (p.val ^ k)) :=
    Finset.prod_coe_sort s (fun p : Nat.Primes => p.val ^ k - rho f (p.val ^ k))
  simpa only [hpred, Nat.card_eq_fintype_card, P, card_good_residues,
    hqprod, hrprod] using h

theorem finite_sieve_periodic (f : Polynomial ℤ) (k : ℕ) (s : Finset Nat.Primes) :
    Function.Periodic (AvoidPrimes f k s) (∏ p ∈ s, p.val ^ k) := by
  intro n
  apply propext
  unfold AvoidPrimes
  apply forall_congr'
  intro p
  apply forall_congr'
  intro hp
  have hd : p.val ^ k ∣ ∏ q ∈ s, q.val ^ k := Finset.dvd_prod_of_mem _ hp
  have hz : ((∏ q ∈ s, q.val ^ k : ℕ) : ZMod (p.val ^ k)) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr hd
  have heq : f.eval₂ (Int.castRingHom (ZMod (p.val ^ k)))
      ((n + ∏ q ∈ s, q.val ^ k : ℕ) : ZMod (p.val ^ k)) =
      f.eval₂ (Int.castRingHom (ZMod (p.val ^ k))) (n : ZMod (p.val ^ k)) := by
    simp only [Nat.cast_add, hz, add_zero]
  rw [← Nat.cast_pow, ← eval_zmod_eq_zero_iff,
    ← eval_zmod_eq_zero_iff, heq]

theorem finite_sieve_error (f : Polynomial ℤ) (k : ℕ) (s : Finset Nat.Primes) (N : ℕ) :
    |(Nat.count (AvoidPrimes f k s) N : ℝ) -
      (∏ p ∈ s, (1 - (rho f (p.val ^ k) : ℝ) / (p.val : ℝ) ^ k)) * N| ≤
        (∏ p ∈ s, p.val ^ k : ℕ) := by
  classical
  have hq : 0 < ∏ p ∈ s, p.val ^ k := Finset.prod_pos (fun p _ => pow_pos p.property.pos _)
  have h := count_periodic_error (AvoidPrimes f k s) (∏ p ∈ s, p.val ^ k) N hq
    (finite_sieve_periodic f k s)
  rw [finite_sieve_full_period] at h
  have hprod : ((∏ p ∈ s, (p.val ^ k - rho f (p.val ^ k)) : ℕ) : ℝ) /
      (∏ p ∈ s, p.val ^ k : ℕ) =
        ∏ p ∈ s, (1 - (rho f (p.val ^ k) : ℝ) / (p.val : ℝ) ^ k) := by
    push_cast
    rw [← Finset.prod_div_distrib]
    apply Finset.prod_congr rfl
    intro p hp
    rw [Nat.cast_sub (rho_le _ _), Nat.cast_pow, sub_div, div_self]
    exact pow_ne_zero _ (Nat.cast_ne_zero.mpr p.property.ne_zero)
  rw [hprod] at h
  exact h

theorem count_or_le (P Q : ℕ → Prop) [DecidablePred P] [DecidablePred Q] (N : ℕ) :
    Nat.count (fun n => P n ∨ Q n) N ≤ Nat.count P N + Nat.count Q N := by
  simp only [Nat.count_eq_card_filter_range, Finset.filter_or]
  exact Finset.card_union_le _ _

theorem count_exists_le {α : Type*} (s : Finset α) (P : α → ℕ → Prop)
    [∀ a, DecidablePred (P a)] (N : ℕ) :
    Nat.count (fun n => ∃ a ∈ s, P a n) N ≤ ∑ a ∈ s, Nat.count (P a) N := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    simp only [Finset.mem_insert, exists_eq_or_imp, Finset.sum_insert ha]
    exact (count_or_le _ _ _).trans (Nat.add_le_add_left ih _)

theorem root_predicate_periodic (f : Polynomial ℤ) (q : ℕ) :
    Function.Periodic (fun n : ℕ => (q : ℤ) ∣ f.eval (n : ℤ)) q := by
  intro n
  apply propext
  change (q : ℤ) ∣ f.eval ((n + q : ℕ) : ℤ) ↔ (q : ℤ) ∣ f.eval (n : ℤ)
  rw [← eval_zmod_eq_zero_iff, ← eval_zmod_eq_zero_iff]
  simp only [Nat.cast_add, ZMod.natCast_self, add_zero]

theorem count_roots_le (f : Polynomial ℤ) {q : ℕ} (hq : 0 < q) (N : ℕ) :
    (Nat.count (fun n : ℕ => (q : ℤ) ∣ f.eval (n : ℤ)) N : ℝ) ≤
      (rho f q : ℝ) * ((N : ℝ) / q + 1) := by
  rw [count_periodic_div_mod _ _ _ (root_predicate_periodic f q)]
  have hrem := Nat.count_monotone (fun n : ℕ => (q : ℤ) ∣ f.eval (n : ℤ))
    (Nat.mod_lt N hq).le
  have hcnt : Nat.count (fun n : ℕ => (q : ℤ) ∣ f.eval (n : ℤ)) q = rho f q := by
    rw [Nat.count_eq_card_filter_range]; rfl
  rw [hcnt] at hrem ⊢
  have hrem' : (Nat.count (fun n : ℕ => (q : ℤ) ∣ f.eval (n : ℤ)) (N % q) : ℝ) ≤
      (rho f q : ℝ) := by exact_mod_cast hrem
  have hdiv : ((N / q : ℕ) : ℝ) ≤ (N : ℝ) / q := by
    rw [le_div_iff₀ (by exact_mod_cast hq)]
    exact_mod_cast Nat.div_mul_le_self N q
  push_cast
  nlinarith [mul_le_mul_of_nonneg_right hdiv (Nat.cast_nonneg (rho f q) : (0 : ℝ) ≤ _)]

theorem card_primesUpTo (N : ℕ) : (primesUpTo N).card = Nat.primeCounting N := by
  calc
    _ = ((Nat.primesLE N).filter Nat.Prime).card := Finset.card_subtype _ _
    _ = (Nat.primesLE N).card := congrArg Finset.card (Finset.filter_true_of_mem
      (fun _ hp => (Nat.mem_primesLE.mp hp).2))
    _ = _ := Nat.primesLE_card_eq_primeCounting _

theorem primeCounting_ratio_tendsto :
    Tendsto (fun N : ℕ => (Nat.primeCounting N : ℝ) / N) atTop (nhds 0) := by
  have hcast : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hupper := hcast.eventually (Chebyshev.eventually_primeCounting_le (ε := 1) zero_lt_one)
  apply squeeze_zero' (Filter.Eventually.of_forall (fun _ => by positivity))
    (g := fun N : ℕ => (Real.log 4 + 1) / Real.log (N : ℝ))
  · filter_upwards [hupper, eventually_gt_atTop 0] with N hN hpos
    have hN' : (Nat.primeCounting N : ℝ) ≤
        (Real.log 4 + 1) * N / Real.log (N : ℝ) := by simpa using hN
    rw [div_le_iff₀ (Nat.cast_pos.mpr hpos)]
    calc
      _ ≤ _ := hN'
      _ = _ := by ring
  · simpa only [div_eq_mul_inv, mul_zero, Function.comp_apply, Pi.inv_apply] using
      ((Real.tendsto_log_atTop.comp hcast).inv_tendsto_atTop).const_mul (Real.log 4 + 1)

theorem tendsto_primesUpTo : Tendsto primesUpTo atTop atTop := by
  apply tendsto_atTop.2
  intro s
  refine Filter.eventually_atTop.2 ⟨s.sup (fun p => p.val), ?_⟩
  intro N hN p hp
  exact mem_primesUpTo.mpr ((Finset.le_sup (f := fun p => p.val) hp).trans hN)

theorem finite_product_tendsto (f : Polynomial ℤ) (k : ℕ)
    (h : Multipliable (localFactor f k)) :
    Tendsto (fun N : ℕ => ∏ p ∈ primesUpTo N, localFactor f k p)
      atTop (nhds (densityConstant f k)) :=
  h.hasProd.comp tendsto_primesUpTo

theorem finite_local_tail_small (f : Polynomial ℤ) {k : ℕ}
    (h : Summable (fun p : Nat.Primes => (rho f (p.val ^ k) : ℝ) / (p.val : ℝ) ^ k))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ Y : ℕ, ∀ s : Finset Nat.Primes, (∀ p ∈ s, Y < p.val) →
      ∑ p ∈ s, (rho f (p.val ^ k) : ℝ) / (p.val : ℝ) ^ k < ε := by
  classical
  obtain ⟨t, ht⟩ := summable_iff_vanishing_norm.mp h ε hε
  refine ⟨t.sup (fun p => p.val), ?_⟩
  intro s hs
  have hd : Disjoint s t := by
    apply Finset.disjoint_left.mpr
    intro p hp hpt
    exact (not_lt_of_ge (Finset.le_sup (f := fun p => p.val) hpt)) (hs p hp)
  have hb := ht s hd
  rwa [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg (fun _ _ => by positivity))] at hb

theorem natCount_le_finite (f : Polynomial ℤ) (k N : ℕ) (s : Finset Nat.Primes) :
    natCount f k N ≤ Nat.count (AvoidPrimes f k s) N := by
  classical
  apply Nat.count_mono_left
  intro n _ hn p _
  exact hn p.val p.property

theorem finite_sieve_difference_le (f : Polynomial ℤ) (k Y N : ℕ) :
    Nat.count (AvoidPrimes f k (primesUpTo Y)) N ≤ natCount f k N +
      (∑ p ∈ (primesUpTo N).filter (fun p => Y < p.val),
        Nat.count (fun n : ℕ => (p.val : ℤ) ^ k ∣ f.eval (n : ℤ)) N) +
      tailCount f k N := by
  classical
  let P := fun n : ℕ => PowerFree k (f.eval (n : ℤ))
  let I := fun n : ℕ => ∃ p ∈ (primesUpTo N).filter (fun p => Y < p.val),
    (p.val : ℤ) ^ k ∣ f.eval (n : ℤ)
  let T := fun n : ℕ => ∃ p : ℕ, p.Prime ∧ N < p ∧ (p : ℤ) ^ k ∣ f.eval (n : ℤ)
  have hsub : ∀ n < N, AvoidPrimes f k (primesUpTo Y) n → (P n ∨ I n) ∨ T n := by
    intro n _ hn
    by_cases hP : P n
    · exact Or.inl (Or.inl hP)
    · obtain ⟨p, hp, hdiv⟩ : ∃ p : ℕ, p.Prime ∧ (p : ℤ) ^ k ∣ f.eval (n : ℤ) := by
        simpa only [P, PowerFree, not_forall, Classical.not_imp, not_not, exists_prop] using hP
      by_cases hlarge : N < p
      · exact Or.inr ⟨p, hp, hlarge, hdiv⟩
      · have hY : Y < p := by
          by_contra h
          exact hn ⟨p, hp⟩ (mem_primesUpTo.mpr (Nat.le_of_not_gt h)) hdiv
        exact Or.inl (Or.inr ⟨⟨p, hp⟩, Finset.mem_filter.mpr
          ⟨mem_primesUpTo.mpr (Nat.le_of_not_gt hlarge), hY⟩, hdiv⟩)
  calc
    _ ≤ Nat.count (fun n => (P n ∨ I n) ∨ T n) N := Nat.count_mono_left hsub
    _ ≤ (Nat.count P N + Nat.count I N) + Nat.count T N :=
      (count_or_le _ _ _).trans (Nat.add_le_add_right (count_or_le _ _ _) _)
    _ ≤ _ := Nat.add_le_add_right (Nat.add_le_add_left (count_exists_le _ _ N) _) _

theorem intermediate_sieve_bound (f : Polynomial ℤ) (hdeg : f.natDegree ≠ 0)
    {k Y N : ℕ} (hk : 0 < k)
    (hY : ∀ p : Nat.Primes, (p.val : ℤ) ∣ f.resultant f.derivative → p.val ≤ Y) :
    (∑ p ∈ (primesUpTo N).filter (fun p => Y < p.val),
      (Nat.count (fun n : ℕ => (p.val : ℤ) ^ k ∣ f.eval (n : ℤ)) N : ℝ)) ≤
      (N : ℝ) * (∑ p ∈ (primesUpTo N).filter (fun p => Y < p.val),
        (rho f (p.val ^ k) : ℝ) / (p.val : ℝ) ^ k) +
      (f.natDegree : ℝ) * Nat.primeCounting N := by
  classical
  let s := (primesUpTo N).filter (fun p => Y < p.val)
  have hr (p : Nat.Primes) (hp : p ∈ s) : rho f (p.val ^ k) ≤ f.natDegree := by
    apply rho_prime_pow_le_degree f hdeg p.property (Nat.ne_of_gt hk)
    intro hbad
    exact (not_lt_of_ge (hY p hbad)) (Finset.mem_filter.mp hp).2
  calc
    _ ≤ ∑ p ∈ s, ((rho f (p.val ^ k) : ℝ) * ((N : ℝ) / p.val ^ k + 1)) := by
      apply Finset.sum_le_sum
      intro p _
      simpa only [Nat.cast_pow] using count_roots_le f (pow_pos p.property.pos k) N
    _ = (N : ℝ) * (∑ p ∈ s, (rho f (p.val ^ k) : ℝ) / (p.val : ℝ) ^ k) +
        ∑ p ∈ s, (rho f (p.val ^ k) : ℝ) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro p _
      ring
    _ ≤ (N : ℝ) * (∑ p ∈ s, (rho f (p.val ^ k) : ℝ) / (p.val : ℝ) ^ k) +
        (f.natDegree : ℝ) * Nat.primeCounting N := by
      apply add_le_add_right
      calc
        _ ≤ ∑ _p ∈ s, (f.natDegree : ℝ) :=
          Finset.sum_le_sum (fun p hp => by exact_mod_cast hr p hp)
        _ = (f.natDegree : ℝ) * s.card := by simp [mul_comm]
        _ ≤ _ := mul_le_mul_of_nonneg_left (by
          exact_mod_cast (Finset.card_filter_le _ _).trans_eq (card_primesUpTo N))
          (Nat.cast_nonneg _)

theorem finite_sieve_ratio_tendsto (f : Polynomial ℤ) (k : ℕ) (s : Finset Nat.Primes) :
    Tendsto (fun N : ℕ => (Nat.count (AvoidPrimes f k s) N : ℝ) / N)
      atTop (nhds (∏ p ∈ s, localFactor f k p)) := by
  classical
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero' (Filter.Eventually.of_forall (fun _ => norm_nonneg _))
    (g := fun N : ℕ => (∏ p ∈ s, p.val ^ k : ℕ) / (N : ℝ))
  · filter_upwards [eventually_gt_atTop 0] with N hN
    have hN' : (0 : ℝ) < N := Nat.cast_pos.mpr hN
    have heq : (Nat.count (AvoidPrimes f k s) N : ℝ) / N -
        (∏ p ∈ s, localFactor f k p) =
        ((Nat.count (AvoidPrimes f k s) N : ℝ) -
          (∏ p ∈ s, localFactor f k p) * N) / N := by
      field_simp
    rw [Real.norm_eq_abs, heq, abs_div, abs_of_pos hN']
    exact div_le_div_of_nonneg_right (finite_sieve_error f k s N) (le_of_lt hN')
  · exact tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop

theorem exists_bad_prime_cutoff (f : Polynomial ℤ)
    (hf : Irreducible (f.map (Int.castRingHom ℚ))) :
    ∃ Y : ℕ, ∀ p : Nat.Primes, (p.val : ℤ) ∣ f.resultant f.derivative → p.val ≤ Y := by
  classical
  let s : Finset Nat.Primes := (finite_resultant_primes f hf).toFinset
  refine ⟨s.sup (fun p => p.val), ?_⟩
  intro p hp
  exact Finset.le_sup (f := fun p : Nat.Primes => p.val) (by simpa [s] using hp)

theorem finite_ratio_difference_le (f : Polynomial ℤ) (hdeg : f.natDegree ≠ 0)
    {k Y N : ℕ} (hk : 0 < k) (hN : 0 < N)
    (hY : ∀ p : Nat.Primes, (p.val : ℤ) ∣ f.resultant f.derivative → p.val ≤ Y) :
    (Nat.count (AvoidPrimes f k (primesUpTo Y)) N : ℝ) / N -
        (natCount f k N : ℝ) / N ≤
      (∑ p ∈ (primesUpTo N).filter (fun p => Y < p.val),
        (rho f (p.val ^ k) : ℝ) / (p.val : ℝ) ^ k) +
      (f.natDegree : ℝ) * ((Nat.primeCounting N : ℝ) / N) +
      (tailCount f k N : ℝ) / N := by
  classical
  have hN' : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hd := finite_sieve_difference_le f k Y N
  have hd' : (Nat.count (AvoidPrimes f k (primesUpTo Y)) N : ℝ) ≤
      (natCount f k N : ℝ) +
      (∑ p ∈ (primesUpTo N).filter (fun p => Y < p.val),
        (Nat.count (fun n : ℕ => (p.val : ℤ) ^ k ∣ f.eval (n : ℤ)) N : ℝ)) +
      (tailCount f k N : ℝ) := by exact_mod_cast hd
  have hi := intermediate_sieve_bound f hdeg hk hY (N := N)
  have hdv := div_le_div_of_nonneg_right hd' (le_of_lt hN')
  have hiv := div_le_div_of_nonneg_right hi (le_of_lt hN')
  simp only [add_div, mul_div_assoc] at hdv hiv
  rw [mul_div_cancel₀ _ (ne_of_gt hN')] at hiv
  linarith

theorem nat_density_from_large_prime_tail (f : Polynomial ℤ)
    (hf : Irreducible (f.map (Int.castRingHom ℚ))) (hdeg : f.natDegree ≠ 0)
    {k : ℕ} (hk : 1 < k) (hloc : LocallyAdmissible f k)
    (htail : Tendsto (fun N : ℕ => (tailCount f k N : ℝ) / N) atTop (nhds 0)) :
    Tendsto (fun N : ℕ => (natCount f k N : ℝ) / N)
      atTop (nhds (densityConstant f k)) := by
  classical
  have hconv := (densityConstant_converges_pos f hf hdeg hk hloc).1
  have hsum := summable_local_proportion f hf hdeg hk
  obtain ⟨Ybad, hbad⟩ := exists_bad_prime_cutoff f hf
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hε6 : 0 < ε / 6 := by positivity
  obtain ⟨Ylocal, hlocal⟩ := finite_local_tail_small f hsum hε6
  obtain ⟨Yprod, hprod⟩ := Metric.tendsto_atTop.mp (finite_product_tendsto f k hconv)
    (ε / 6) hε6
  let Y := max Ybad (max Ylocal Yprod)
  have hYbad : Ybad ≤ Y := le_max_left _ _
  have hYlocal : Ylocal ≤ Y := (le_max_left _ _).trans (le_max_right _ _)
  have hYprod : Yprod ≤ Y := (le_max_right _ _).trans (le_max_right _ _)
  have hprod' := hprod Y hYprod
  have hfinite := Metric.tendsto_nhds.mp (finite_sieve_ratio_tendsto f k (primesUpTo Y))
    (ε / 6) hε6
  have hprime : Tendsto (fun N : ℕ => (f.natDegree : ℝ) *
      ((Nat.primeCounting N : ℝ) / N)) atTop (nhds 0) := by
    simpa only [mul_zero, Function.comp_def] using primeCounting_ratio_tendsto.const_mul (f.natDegree : ℝ)
  have hprime' := Metric.tendsto_nhds.mp hprime (ε / 6) hε6
  have htail' := Metric.tendsto_nhds.mp htail (ε / 6) hε6
  filter_upwards [hfinite, hprime', htail', eventually_gt_atTop 0] with N hF hP hT hN
  have hmid := hlocal ((primesUpTo N).filter (fun p => Y < p.val)) (fun p hp =>
    lt_of_le_of_lt hYlocal (Finset.mem_filter.mp hp).2)
  have hd := finite_ratio_difference_le f hdeg (lt_trans Nat.zero_lt_one hk) hN
    (fun p hp => (hbad p hp).trans hYbad)
  have hle : (natCount f k N : ℝ) / N ≤
      (Nat.count (AvoidPrimes f k (primesUpTo Y)) N : ℝ) / N :=
    div_le_div_of_nonneg_right (by exact_mod_cast natCount_le_finite f k N (primesUpTo Y))
      (Nat.cast_nonneg _)
  simp only [Real.dist_eq, sub_zero] at hF hP hT hprod' ⊢
  have hP' := (le_abs_self _).trans_lt hP
  have hT' := (le_abs_self _).trans_lt hT
  have hF' := abs_sub_lt_iff.mp hF
  have hprod'' := abs_sub_lt_iff.mp hprod'
  apply abs_sub_lt_iff.mpr
  constructor <;> linarith

theorem count_interval_compare (P : ℕ → Prop) [DecidablePred P] (N : ℕ) :
    ((Finset.Icc 1 N).filter P).card ≤ Nat.count P N + 1 ∧
      Nat.count P N ≤ ((Finset.Icc 1 N).filter P).card + 1 := by
  constructor
  · have hs : (Finset.Icc 1 N).filter P ⊆ insert N ((Finset.range N).filter P) := by
      intro n hn
      obtain ⟨hin, hP⟩ := Finset.mem_filter.mp hn
      obtain ⟨_, hnN⟩ := Finset.mem_Icc.mp hin
      by_cases heq : n = N
      · exact Finset.mem_insert.mpr (Or.inl heq)
      · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_filter.mpr
          ⟨Finset.mem_range.mpr (lt_of_le_of_ne hnN heq), hP⟩))
    calc
      _ ≤ (insert N ((Finset.range N).filter P)).card := Finset.card_le_card hs
      _ ≤ _ := by simp [Nat.count_eq_card_filter_range]
  · have hs : (Finset.range N).filter P ⊆ insert 0 ((Finset.Icc 1 N).filter P) := by
      intro n hn
      obtain ⟨hin, hP⟩ := Finset.mem_filter.mp hn
      have hnN := Finset.mem_range.mp hin
      by_cases heq : n = 0
      · exact Finset.mem_insert.mpr (Or.inl heq)
      · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_filter.mpr
          ⟨Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr heq, hnN.le⟩, hP⟩))
    calc
      _ ≤ (insert 0 ((Finset.Icc 1 N).filter P)).card := by
        simpa only [Nat.count_eq_card_filter_range] using Finset.card_le_card hs
      _ ≤ _ := by simp

theorem count_natCount_error (f : Polynomial ℤ) (k N : ℕ) :
    |(count f k (N : ℝ) : ℝ) - (natCount f k N : ℝ)| ≤ 1 := by
  classical
  have h := count_interval_compare (fun n : ℕ => PowerFree k (f.eval (n : ℤ))) N
  change |(((Finset.Icc 1 ⌊(N : ℝ)⌋₊).filter _).card : ℝ) - (Nat.count _ N : ℝ)| ≤ 1
  rw [Nat.floor_natCast]
  have h₁ : (((Finset.Icc 1 N).filter (fun n : ℕ => PowerFree k (f.eval (n : ℤ)))).card : ℝ) ≤
      (Nat.count (fun n : ℕ => PowerFree k (f.eval (n : ℤ))) N : ℝ) + 1 := by
    exact_mod_cast h.1
  have h₂ : (Nat.count (fun n : ℕ => PowerFree k (f.eval (n : ℤ))) N : ℝ) ≤
      (((Finset.Icc 1 N).filter (fun n : ℕ => PowerFree k (f.eval (n : ℤ)))).card : ℝ) + 1 := by
    exact_mod_cast h.2
  rw [abs_le]
  constructor <;> linarith

theorem real_asymptotic_from_nat_ratio (f : Polynomial ℤ) (k : ℕ) (c : ℝ)
    (h : Tendsto (fun N : ℕ => (natCount f k N : ℝ) / N) atTop (nhds c)) :
    (fun X : ℝ => (count f k X : ℝ) - c * X) =o[atTop] (fun X : ℝ => X) := by
  classical
  have herr : Tendsto (fun N : ℕ =>
      ((count f k (N : ℝ) : ℝ) - (natCount f k N : ℝ)) / N) atTop (nhds 0) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simp only [sub_zero, Real.norm_eq_abs]
    apply squeeze_zero' (Filter.Eventually.of_forall (fun _ => abs_nonneg _))
      (g := fun N : ℕ => 1 / (N : ℝ))
    · filter_upwards [eventually_gt_atTop 0] with N hN
      rw [abs_div, abs_of_nonneg (Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
      exact div_le_div_of_nonneg_right (count_natCount_error f k N) (Nat.cast_nonneg _)
    · exact tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hnat : Tendsto (fun N : ℕ => (count f k (N : ℝ) : ℝ) / N)
      atTop (nhds c) := by
    have hh := herr.add h
    simpa only [sub_div, sub_add_cancel, zero_add] using hh
  have hfloor := hnat.comp (tendsto_nat_floor_atTop (α := ℝ))
  have hreal : Tendsto (fun X : ℝ => (count f k X : ℝ) / X) atTop (nhds c) := by
    have hh := hfloor.mul (tendsto_nat_floor_div_atTop (R := ℝ))
    rw [mul_one] at hh
    apply hh.congr'
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with X hX
    have hfloorpos : (⌊X⌋₊ : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_zero_of_lt (Nat.floor_pos.mpr hX))
    have hc : count f k (⌊X⌋₊ : ℝ) = count f k X := by
      simp only [count, Nat.floor_natCast]
    simp only [Function.comp_apply, hc]
    field_simp
  apply (isLittleO_iff_tendsto' (by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
    exact fun hzero => False.elim (ne_of_gt hX hzero))).mpr
  have hh := hreal.sub_const c
  rw [sub_self] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
  field_simp

theorem densityStatement_from_large_prime_tail (f : Polynomial ℤ)
    (hf : Irreducible (f.map (Int.castRingHom ℚ))) (hdeg : f.natDegree ≠ 0)
    {k : ℕ} (hk : 1 < k) (hloc : LocallyAdmissible f k)
    (htail : Tendsto (fun N : ℕ => (tailCount f k N : ℝ) / N) atTop (nhds 0)) :
    DensityStatement f k := by
  obtain ⟨hprod, hpos⟩ := densityConstant_converges_pos f hf hdeg hk hloc
  exact ⟨hprod, hpos, real_asymptotic_from_nat_ratio f k _
    (nat_density_from_large_prime_tail f hf hdeg hk hloc htail)⟩

theorem linear_envelope_of_halving (a b : ℕ → ℝ) (ε : ℝ) (hε : 0 ≤ ε)
    (M : ℕ) (hM : 0 < M)
    (ha : ∀ n, a n ≤ n)
    (hstep : ∀ n, 2 ≤ n → a n ≤ a (n / 2) + b (n / 2))
    (hb : ∀ n, M ≤ n → b n ≤ ε * n) :
    ∀ n, a n ≤ ε * n + 2 * M := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n < 2 * M
    · have hcast : (n : ℝ) < 2 * M := by exact_mod_cast hn
      have hnonneg : 0 ≤ ε * n := mul_nonneg hε (Nat.cast_nonneg n)
      linarith [ha n]
    · have hhalf : M ≤ n / 2 := by omega
      have htwo : 2 ≤ n := by omega
      have hsmall : n / 2 < n := Nat.div_lt_self (by omega) (by omega)
      have hle : 2 * (n / 2 : ℕ) ≤ n := by omega
      have hcast : 2 * (n / 2 : ℕ) ≤ (n : ℝ) := by exact_mod_cast hle
      have hmul := mul_le_mul_of_nonneg_left hcast hε
      have hs := hstep n htwo
      have hi := ih (n / 2) hsmall
      have hh := hb (n / 2) hhalf
      nlinarith

theorem tendsto_zero_of_halving (a b : ℕ → ℝ)
    (ha0 : ∀ n, 0 ≤ a n) (ha : ∀ n, a n ≤ n)
    (hstep : ∀ n, 2 ≤ n → a n ≤ a (n / 2) + b (n / 2))
    (hb : Tendsto (fun n : ℕ => b n / n) atTop (nhds 0)) :
    Tendsto (fun n : ℕ => a n / n) atTop (nhds 0) := by
  rw [Metric.tendsto_atTop] at hb ⊢
  intro ε hε
  obtain ⟨M₀, hM₀⟩ := hb (ε / 2) (by positivity)
  let M := max M₀ 1
  have hM : 0 < M := by dsimp [M]; omega
  have hbound : ∀ n, M ≤ n → b n ≤ (ε / 2) * n := by
    intro n hn
    have hn0 : 0 < n := hM.trans_le hn
    have hh := hM₀ n ((le_max_left M₀ 1).trans hn)
    rw [Real.dist_eq, sub_zero] at hh
    have hlt := (abs_lt.mp hh).2
    have hnr : (0 : ℝ) < n := by exact_mod_cast hn0
    exact (div_lt_iff₀ hnr).mp hlt |>.le
  have henv := linear_envelope_of_halving a b (ε / 2) (by positivity) M hM
    ha hstep hbound
  have hconst : Tendsto (fun n : ℕ => (2 * M : ℝ) / n) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  rw [Metric.tendsto_atTop] at hconst
  obtain ⟨N, hN⟩ := hconst (ε / 2) (by positivity)
  refine ⟨max N 1, ?_⟩
  intro n hn
  have hn0 : 0 < n := by omega
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn0
  have hh := hN n ((le_max_left N 1).trans hn)
  rw [Real.dist_eq, sub_zero] at hh ⊢
  rw [abs_of_nonneg (div_nonneg (ha0 n) hnr.le)]
  have hc := (abs_lt.mp hh).2
  have he := (div_le_div_iff_of_pos_right hnr).mpr (henv n)
  rw [add_div, mul_div_cancel_right₀ _ (ne_of_gt hnr)] at he
  linarith

theorem tailCount_halving (f : Polynomial ℤ) (k N : ℕ) :
    tailCount f k N ≤ tailCount f k (N / 2) + dyadicTailCount f k (N / 2) + 1 := by
  classical
  let E := fun M n : ℕ => ∃ p : ℕ, p.Prime ∧ M < p ∧ (p : ℤ)^k ∣ f.eval (n : ℤ)
  have hsub : (Finset.range N).filter (E N) ⊆
      ((Finset.range (N / 2)).filter (E (N / 2))) ∪
      insert (N / 2) ((Finset.Ioc (N / 2) (2 * (N / 2))).filter (E (N / 2))) := by
    intro n hn
    obtain ⟨hnN, p, hp, hNp, hdiv⟩ := Finset.mem_filter.mp hn
    have hnN' := Finset.mem_range.mp hnN
    have he : E (N / 2) n := ⟨p, hp, lt_of_le_of_lt (Nat.div_le_self N 2) hNp, hdiv⟩
    by_cases hsmall : n < N / 2
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hsmall, he⟩)
    · apply Finset.mem_union_right
      by_cases heq : n = N / 2
      · exact Finset.mem_insert.mpr (Or.inl heq)
      · apply Finset.mem_insert.mpr
        exact Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr (by omega), he⟩)
  have hcard := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hi := Finset.card_insert_le (N / 2)
    ((Finset.Ioc (N / 2) (2 * (N / 2))).filter (E (N / 2)))
  simp only [tailCount, dyadicTailCount, Nat.count_eq_card_filter_range]
  change ((Finset.range N).filter (E N)).card ≤ _
  change ((Finset.range N).filter (E N)).card ≤
    ((Finset.range (N / 2)).filter (E (N / 2))).card +
      ((Finset.Ioc (N / 2) (2 * (N / 2))).filter (E (N / 2))).card + 1
  omega

theorem global_tail_of_dyadic_tail (f : Polynomial ℤ) (k : ℕ)
    (h : Tendsto (fun M : ℕ => (dyadicTailCount f k M : ℝ) / M) atTop (nhds 0)) :
    Tendsto (fun N : ℕ => (tailCount f k N : ℝ) / N) atTop (nhds 0) := by
  classical
  apply tendsto_zero_of_halving (fun n => (tailCount f k n : ℝ))
    (fun n => (dyadicTailCount f k n : ℝ) + 1)
  · intro n; positivity
  · intro n
    have hn : tailCount f k n ≤ n := Nat.count_le _
    exact_mod_cast hn
  · intro n _
    have hh := tailCount_halving f k n
    exact_mod_cast hh
  · have hh := h.add (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop :
        Tendsto (fun n : ℕ => (1 : ℝ) / n) atTop (nhds 0))
    simpa only [← add_div, add_zero] using hh

theorem exists_primitive_positive_normalization (f : Polynomial ℤ)
    (hf : Irreducible (f.map (Int.castRingHom ℚ))) :
    ∃ (a : ℤ) (g : Polynomial ℤ), a ≠ 0 ∧ f = C a * g ∧
      g.IsPrimitive ∧ 0 < g.leadingCoeff ∧ g.natDegree = f.natDegree ∧
      Irreducible (g.map (Int.castRingHom ℚ)) := by
  have hf0 : f ≠ 0 := fun he => hf.ne_zero (by simp [he])
  have hc : f.content ≠ 0 := content_eq_zero_iff.not.mpr hf0
  have hu : IsUnit (C (f.content : ℚ)) := isUnit_C.mpr
    (isUnit_iff_ne_zero.mpr (by exact_mod_cast hc))
  have hq : Irreducible (f.primPart.map (Int.castRingHom ℚ)) := by
    have he := congrArg (Polynomial.map (Int.castRingHom ℚ)) f.eq_C_content_mul_primPart
    simp only [Polynomial.map_mul, Polynomial.map_C] at he
    rw [he] at hf
    exact (irreducible_isUnit_mul hu).mp hf
  by_cases hpos : 0 < f.primPart.leadingCoeff
  · exact ⟨f.content, f.primPart, hc, f.eq_C_content_mul_primPart,
      f.isPrimitive_primPart, hpos, f.natDegree_primPart, hq⟩
  · refine ⟨-f.content, -f.primPart, neg_ne_zero.mpr hc, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [map_neg, neg_mul_neg] using f.eq_C_content_mul_primPart
    · exact isPrimitive_of_dvd f.isPrimitive_primPart (by simp)
    · rw [leadingCoeff_neg]
      have hne := leadingCoeff_ne_zero.mpr f.primPart_ne_zero
      omega
    · simp [f.natDegree_primPart]
    · rw [Polynomial.map_neg]
      have hi := (irreducible_isUnit_mul (show IsUnit (-1 : Polynomial ℚ) from
        isUnit_neg_one)).mpr hq
      simpa only [neg_one_mul] using hi

theorem prime_power_dvd_scalar_iff (a b : ℤ) (ha : a ≠ 0) (k : ℕ)
    {p : ℕ} (hp : p.Prime) (hpa : a.natAbs < p) :
    (p : ℤ)^k ∣ a * b ↔ (p : ℤ)^k ∣ b := by
  have hcp : p.Coprime a.natAbs := hp.coprime_iff_not_dvd.mpr
    (Nat.not_dvd_of_pos_of_lt (Int.natAbs_pos.mpr ha) hpa)
  have hci : IsCoprime (p : ℤ) a := Int.isCoprime_iff_nat_coprime.mpr (by simpa using hcp)
  exact ⟨hci.pow_left.dvd_of_dvd_mul_left, fun h => dvd_mul_of_dvd_right h a⟩

theorem tailCount_scalar_eq (a : ℤ) (ha : a ≠ 0) (g : Polynomial ℤ)
    (k N : ℕ) (hN : a.natAbs ≤ N) :
    tailCount (C a * g) k N = tailCount g k N := by
  classical
  unfold tailCount
  congr 1
  funext n
  apply propext
  constructor <;> rintro ⟨p, hp, hNp, hd⟩
  · refine ⟨p, hp, hNp, ?_⟩
    rw [eval_mul, eval_C] at hd
    exact (prime_power_dvd_scalar_iff a _ ha k hp (hN.trans_lt hNp)).mp hd
  · refine ⟨p, hp, hNp, ?_⟩
    rw [eval_mul, eval_C]
    exact dvd_mul_of_dvd_right hd a

theorem global_tail_scalar_iff (a : ℤ) (ha : a ≠ 0) (g : Polynomial ℤ) (k : ℕ) :
    Tendsto (fun N : ℕ => (tailCount (C a * g) k N : ℝ) / N) atTop (nhds 0) ↔
    Tendsto (fun N : ℕ => (tailCount g k N : ℝ) / N) atTop (nhds 0) := by
  apply tendsto_congr'
  filter_upwards [eventually_ge_atTop a.natAbs] with N hN
  rw [tailCount_scalar_eq a ha g k N hN]

theorem dyadic_tail_limit_of_power_saving (f : Polynomial ℤ) (k : ℕ)
    (δ C : ℝ) (hδ : 0 < δ)
    (hbound : ∀ᶠ M : ℕ in atTop,
      (dyadicTailCount f k M : ℝ) ≤ C * (M : ℝ) ^ (1 - δ)) :
    Tendsto (fun M : ℕ => (dyadicTailCount f k M : ℝ) / M) atTop (nhds 0) := by
  apply squeeze_zero' (Eventually.of_forall (fun M => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg M)))
    (g := fun M : ℕ => C * (M : ℝ) ^ (-δ))
  · filter_upwards [hbound, eventually_gt_atTop 0] with M hM hM0
    have hm : (0 : ℝ) < M := by exact_mod_cast hM0
    calc
      _ ≤ (C * (M : ℝ) ^ (1 - δ)) / M := div_le_div_of_nonneg_right hM hm.le
      _ = C * (M : ℝ) ^ (-δ) := by
        rw [show 1 - δ = -δ + 1 by ring, Real.rpow_add hm, Real.rpow_one]
        field_simp
  · simpa only [mul_zero, Function.comp_def] using
      ((tendsto_rpow_neg_atTop hδ).comp tendsto_natCast_atTop_atTop).const_mul C

theorem densityStatement_from_normalized_dyadic_tail (f g : Polynomial ℤ)
    (hf : Irreducible (f.map (Int.castRingHom ℚ))) (hdeg : f.natDegree ≠ 0)
    {k : ℕ} (hk : 1 < k) (hloc : LocallyAdmissible f k)
    (a : ℤ) (ha : a ≠ 0) (hfg : f = C a * g)
    (htail : Tendsto (fun M : ℕ => (dyadicTailCount g k M : ℝ) / M) atTop (nhds 0)) :
    DensityStatement f k := by
  apply densityStatement_from_large_prime_tail f hf hdeg hk hloc
  have hg := global_tail_of_dyadic_tail g k htail
  rw [hfg]
  exact (global_tail_scalar_iff a ha g k).mpr hg

end QuarticPowerFree

end OAI
end

section
-- module Solutions.OAIB3_Qpf.PowerFree_HilbertSimplex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators
open Matrix
open scoped BigOperators
open scoped BigOperators

namespace QuarticPowerFree

section
open scoped BigOperators

open scoped BigOperators
open MvPolynomial

theorem mem_weightedMonomials {σ : Type*} [Fintype σ]
    (ω : σ → ℝ) (hω : ∀ i, 0 < ω i) (T : ℝ) (a : σ →₀ ℕ) :
    a ∈ weightedMonomials ω T ↔ monomialWeight ω a ≤ T := by
  classical
  constructor
  · exact fun h => (Finset.mem_filter.mp h).2
  · intro ha
    refine Finset.mem_filter.mpr ⟨Finset.mem_Iic.mpr ?_,ha⟩
    intro i
    change a i ≤ ⌊T/ω i⌋₊
    apply Nat.le_floor
    apply (le_div_iff₀ (hω i)).mpr
    have hi := Finset.single_le_sum
      (fun j _ => mul_nonneg (hω j).le (Nat.cast_nonneg (a j))) (Finset.mem_univ i)
    simpa only [mul_comm (a i : ℝ)] using hi.trans ha

end

open scoped BigOperators
open MvPolynomial

end QuarticPowerFree

end OAI
end

section
-- module Solutions.OAIB3_Qpf.PowerFree_WeightedSlabs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace QuarticPowerFree

section
open scoped BigOperators

theorem card_simplexPairs (N : ℕ) :
    2*(simplexPairs N).card = (N+1)*(N+2) := by
  rw [simplexPairs, Finset.card_biUnion]
  · simp_rw [Finset.Nat.card_antidiagonal]
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ]
      nlinarith
  · intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro x hi hj
    exact hij ((Finset.HasAntidiagonal.mem_antidiagonal.mp hi).symm.trans (Finset.HasAntidiagonal.mem_antidiagonal.mp hj))

theorem mem_weightedPairs {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (x : ℕ × ℕ) (T : ℕ) :
    x ∈ weightedPairs a b T ↔ a*x.1+b*x.2 ≤ T := by
  simp only [weightedPairs, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  constructor
  · exact fun h => h.2
  · intro h
    have hx : x.1 ≤ a*x.1 := by nlinarith
    have hy : x.2 ≤ b*x.2 := by nlinarith
    exact ⟨⟨by omega, by omega⟩, h⟩

private theorem pair_divmod_injective (a b : ℕ) :
    Function.Injective (fun x : ℕ × ℕ => ((x.1/b,x.2/a),(x.1%b,x.2%a))) := by
  intro x y h
  have hq := congrArg Prod.fst h
  have hr := congrArg Prod.snd h
  have hq1 := congrArg Prod.fst hq
  have hq2 := congrArg Prod.snd hq
  have hr1 := congrArg Prod.fst hr
  have hr2 := congrArg Prod.snd hr
  apply Prod.ext
  · have hx := Nat.mod_add_div x.1 b
    have hy := Nat.mod_add_div y.1 b
    dsimp at hq1 hr1
    rw [hq1, hr1] at hx
    omega
  · have hx := Nat.mod_add_div x.2 a
    have hy := Nat.mod_add_div y.2 a
    dsimp at hq2 hr2
    rw [hq2, hr2] at hx
    omega

theorem weightedPairs_upper {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (T : ℕ) :
    (weightedPairs a b T).card ≤
      (simplexPairs (T/(a*b))).card * (a*b) := by
  let f := fun x : ℕ × ℕ => ((x.1/b,x.2/a),(x.1%b,x.2%a))
  have hin (x : ℕ × ℕ) (hx : x ∈ weightedPairs a b T) :
      f x ∈ (simplexPairs (T/(a*b))) ×ˢ
        ((Finset.range b) ×ˢ (Finset.range a)) := by
    rw [Finset.mem_product]
    refine ⟨?_, ?_⟩
    · apply (mem_simplexPairs _ _).mpr
      apply (Nat.le_div_iff_mul_le (by positivity : 0 < a*b)).mpr
      have h := (mem_weightedPairs ha hb x T).mp hx
      have hx1 := Nat.div_mul_le_self x.1 b
      have hx2 := Nat.div_mul_le_self x.2 a
      dsimp [f]
      nlinarith [Nat.mul_le_mul_left a hx1, Nat.mul_le_mul_left b hx2]
    · simp [f, Nat.mod_lt _ ha, Nat.mod_lt _ hb]
  have h := Finset.card_le_card_of_injOn f hin
    (fun _ _ _ _ he => pair_divmod_injective a b he)
  simpa [Finset.card_product, mul_comm a b] using h

theorem weightedPairs_lower {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (T N : ℕ) (hTN : a*b*(N+2) ≤ T) :
    (simplexPairs N).card * (a*b) ≤ (weightedPairs a b T).card := by
  let S := (simplexPairs N) ×ˢ ((Finset.range b) ×ˢ (Finset.range a))
  let f := fun x : (ℕ × ℕ) × (ℕ × ℕ) => (b*x.1.1+x.2.1,a*x.1.2+x.2.2)
  have hin (x : (ℕ × ℕ) × (ℕ × ℕ)) (hx : x ∈ S) :
      f x ∈ weightedPairs a b T := by
    rcases Finset.mem_product.mp hx with ⟨hn, hr⟩
    have hn' := (mem_simplexPairs _ _).mp hn
    rcases Finset.mem_product.mp hr with ⟨hr1, hr2⟩
    have hr1' := Finset.mem_range.mp hr1
    have hr2' := Finset.mem_range.mp hr2
    apply (mem_weightedPairs ha hb _ T).mpr
    dsimp [f]
    nlinarith [Nat.mul_le_mul_left (a*b) hn', Nat.mul_le_mul_left a (Nat.le_of_lt hr1'),
      Nat.mul_le_mul_left b (Nat.le_of_lt hr2')]
  have hinj : Set.InjOn f (S : Set ((ℕ × ℕ) × (ℕ × ℕ))) := by
    intro x hx y hy he
    have hx' := Finset.mem_product.mp (Finset.mem_product.mp hx).2
    have hy' := Finset.mem_product.mp (Finset.mem_product.mp hy).2
    have hleft := congrArg Prod.fst he
    have hright := congrArg Prod.snd he
    have hm1 := congrArg (fun n => n % b) hleft
    have hm2 := congrArg (fun n => n % a) hright
    dsimp [f] at hleft hright hm1 hm2
    simp [Nat.add_mod, Nat.mod_eq_of_lt (Finset.mem_range.mp hx'.1),
      Nat.mod_eq_of_lt (Finset.mem_range.mp hy'.1)] at hm1
    simp [Nat.add_mod, Nat.mod_eq_of_lt (Finset.mem_range.mp hx'.2),
      Nat.mod_eq_of_lt (Finset.mem_range.mp hy'.2)] at hm2
    apply Prod.ext
    · apply Prod.ext <;> nlinarith
    · exact Prod.ext hm1 hm2
  have h := Finset.card_le_card_of_injOn f hin hinj
  simpa [S, Finset.card_product, mul_comm a b] using h

end

theorem weightedPairs_quadratic_bounds {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (T : ℕ) :
    T^2 ≤ 2*(a*b)*(weightedPairs a b T).card + 3*(a*b)*T + 7*(a*b)^2 ∧
    2*(a*b)*(weightedPairs a b T).card ≤ T^2 + 3*(a*b)*T + 2*(a*b)^2 := by
  let L := a*b
  let q := T/L
  have hL : 0 < L := Nat.mul_pos ha hb
  have hq : L*q ≤ T := by
    dsimp [q]
    nlinarith [Nat.div_mul_le_self T L]
  have hT : T ≤ L*(q+1) := by
    have hr := Nat.mod_lt T hL
    have hm := Nat.mod_add_div T L
    dsimp [q]
    nlinarith
  constructor
  · by_cases hq2 : 2 ≤ q
    · let N := q-2
      have hN : q = N+2 := by omega
      have hTN : a*b*(N+2) ≤ T := by simpa only [L, ← hN] using hq
      have hl := weightedPairs_lower ha hb T N hTN
      have hc := card_simplexPairs N
      have h0 : L*(N+1)*(N+2) ≤ 2*(weightedPairs a b T).card := by
        dsimp [L]
        nlinarith [Nat.mul_le_mul_left 2 hl]
      have h1 := Nat.mul_le_mul_left L h0
      have h2 : T^2 ≤ (L*(N+3))^2 := by
        exact Nat.pow_le_pow_left (by nlinarith [hT]) 2
      have h3 : L*N ≤ T := by nlinarith [hq]
      have h4 := Nat.mul_le_mul_left (3*L) h3
      change T^2 ≤ 2*L*(weightedPairs a b T).card + 3*L*T+7*L^2
      nlinarith
    · have hsmall : T ≤ 2*L := by nlinarith [hT]
      have hsquare := Nat.pow_le_pow_left hsmall 2
      change T^2 ≤ 2*L*(weightedPairs a b T).card + 3*L*T+7*L^2
      nlinarith
  · have hu := weightedPairs_upper ha hb T
    have hc := card_simplexPairs q
    have h0 : 2*(weightedPairs a b T).card ≤ (q+1)*(q+2)*L := by
      change (weightedPairs a b T).card ≤ (simplexPairs q).card * L at hu
      nlinarith [Nat.mul_le_mul_left 2 hu]
    have h1 := Nat.mul_le_mul_left L h0
    have hprod := Nat.mul_le_mul (Nat.add_le_add_right hq L)
      (Nat.add_le_add_right hq (2*L))
    change 2*L*(weightedPairs a b T).card ≤ T^2+3*L*T+2*L^2
    nlinarith

theorem weightedPairs_volume_error {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (T : ℕ) :
    |((weightedPairs a b T).card : ℝ) - (T:ℝ)^2/(2*(a*b : ℕ))| ≤
      3/2*(T:ℝ) + 7/2*(a*b : ℕ) := by
  have hL : (0:ℝ) < (a*b : ℕ) := by exact_mod_cast Nat.mul_pos ha hb
  have ⟨hlo, hhi⟩ := weightedPairs_quadratic_bounds ha hb T
  have hlo' : (T:ℝ)^2 ≤ 2*(a*b : ℕ)*(weightedPairs a b T).card +
      3*(a*b : ℕ)*T+7*(a*b : ℕ)^2 := by exact_mod_cast hlo
  have hhi' : 2*(a*b : ℕ)*(weightedPairs a b T).card ≤ (T:ℝ)^2 +
      3*(a*b : ℕ)*T+2*(a*b : ℕ)^2 := by exact_mod_cast hhi
  have hden : (0:ℝ) < 2*(a*b : ℕ) := by positivity
  have heq := div_mul_cancel₀ ((T:ℝ)^2) (ne_of_gt hden)
  apply abs_le.mpr
  constructor
  · apply (mul_le_mul_iff_right₀ hden).mp
    nlinarith
  · apply (mul_le_mul_iff_right₀ hden).mp
    nlinarith [sq_nonneg (a*b : ℕ)]

theorem mem_weightedTriples {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (x : NatTriple) (T : ℕ) : x ∈ weightedTriples a b c T ↔ tripleWeight a b c x ≤ T := by
  simp only [weightedTriples, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  constructor
  · exact fun h => h.2
  · intro h
    have hx : x.1 ≤ a*x.1 := by nlinarith
    have hy : x.2.1 ≤ b*x.2.1 := by nlinarith
    have hz : x.2.2 ≤ c*x.2.2 := by nlinarith
    dsimp [tripleWeight] at h
    exact ⟨⟨by omega, by omega, by omega⟩, h⟩

theorem tripleWeight_shift (a b c : ℕ) (m x : NatTriple) :
    tripleWeight a b c (tripleShift m x) = tripleWeight a b c m + tripleWeight a b c x := by
  change a*(m.1+x.1)+b*(m.2.1+x.2.1)+c*(m.2.2+x.2.2) = _
  dsimp [tripleWeight]
  ring

theorem weightedNormal_card_add {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (m : NatTriple) (T : ℕ) (hT : tripleWeight a b c m ≤ T) :
    (weightedNormal a b c m T).card +
      (weightedTriples a b c (T-tripleWeight a b c m)).card = (weightedTriples a b c T).card := by
  have he : (weightedTriples a b c T).filter (tripleDivides m) =
      (weightedTriples a b c (T-tripleWeight a b c m)).map (tripleShift m) := by
    ext x
    simp only [Finset.mem_filter, mem_weightedTriples ha hb hc, Finset.mem_map]
    constructor
    · rintro ⟨hx, hm⟩
      let y : NatTriple := (x.1-m.1,x.2.1-m.2.1,x.2.2-m.2.2)
      have hy : tripleShift m y = x := by
        rcases hm with ⟨h1,h2,h3⟩
        change (m.1+(x.1-m.1),m.2.1+(x.2.1-m.2.1),m.2.2+(x.2.2-m.2.2)) = x
        simp [Nat.add_sub_cancel' h1, Nat.add_sub_cancel' h2, Nat.add_sub_cancel' h3]
      refine ⟨y, ?_, hy⟩
      rw [← hy, tripleWeight_shift] at hx
      omega
    · rintro ⟨y, hy, rfl⟩
      constructor
      · rw [tripleWeight_shift]
        omega
      · change m.1 ≤ m.1+y.1 ∧ m.2.1 ≤ m.2.1+y.2.1 ∧ m.2.2 ≤ m.2.2+y.2.2
        omega
  have hh := Finset.card_filter_add_card_filter_not (s := weightedTriples a b c T) (p := tripleDivides m)
  rw [he, Finset.card_map] at hh
  change _ + ((weightedTriples a b c T).filter (fun x => ¬ tripleDivides m x)).card = _ at hh
  dsimp [weightedNormal]
  omega

end QuarticPowerFree

end OAI
end

section
-- module Solutions.OAIB3_Qpf.PowerFree_WeightedHypersurfaces
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace QuarticPowerFree

section
open scoped BigOperators

theorem mem_firstSlabs {a b c u T : ℕ} (_ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hT : a*u ≤ T) (x : NatTriple) :
    x ∈ firstSlabs a b c u T ↔ x.1 < u ∧ tripleWeight a b c x ≤ T := by
  simp only [firstSlabs, Finset.mem_biUnion, Finset.mem_range, Finset.mem_map]
  constructor
  · rintro ⟨i, hi, y, hy, rfl⟩
    have hs : a*i ≤ T := (Nat.mul_le_mul_left a (Nat.le_of_lt hi)).trans hT
    have hy' := (mem_weightedPairs hb hc y (T-a*i)).mp hy
    simp only [firstSlab_apply, tripleWeight]
    exact ⟨hi, by omega⟩
  · rintro ⟨hx, hw⟩
    refine ⟨x.1, hx, (x.2.1,x.2.2), ?_, by simp⟩
    apply (mem_weightedPairs hb hc _ _).mpr
    dsimp [tripleWeight] at hw
    dsimp
    omega

theorem mem_secondSlabs {a b c u v T : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hT : a*u+b*v ≤ T) (x : NatTriple) :
    x ∈ secondSlabs a b c u v T ↔ u ≤ x.1 ∧ x.2.1 < v ∧ tripleWeight a b c x ≤ T := by
  simp only [secondSlabs, Finset.mem_biUnion, Finset.mem_range, Finset.mem_map]
  constructor
  · rintro ⟨j, hj, y, hy, rfl⟩
    have hs : a*u+b*j ≤ T := by nlinarith [Nat.mul_le_mul_left b (Nat.le_of_lt hj)]
    have hy' := (mem_weightedPairs ha hc y _).mp hy
    simp only [secondSlab_apply, tripleWeight]
    refine ⟨by omega, hj, ?_⟩
    nlinarith [Nat.sub_add_cancel hs]
  · rintro ⟨hu, hx, hw⟩
    refine ⟨x.2.1, hx, (x.1-u,x.2.2), ?_, ?_⟩
    · apply (mem_weightedPairs ha hc _ _).mpr
      dsimp [tripleWeight] at hw
      dsimp
      have he := Nat.sub_add_cancel hu
      have hs : a*u+b*x.2.1 ≤ T := by nlinarith [Nat.mul_le_mul_left a hu]
      nlinarith [Nat.sub_add_cancel hs]
    · simp [Nat.add_sub_cancel' hu]

theorem mem_thirdSlabs {a b c u v w T : ℕ} (ha : 0 < a) (hb : 0 < b) (_hc : 0 < c)
    (hT : a*u+b*v+c*w ≤ T) (x : NatTriple) :
    x ∈ thirdSlabs a b c u v w T ↔
      u ≤ x.1 ∧ v ≤ x.2.1 ∧ x.2.2 < w ∧ tripleWeight a b c x ≤ T := by
  simp only [thirdSlabs, Finset.mem_biUnion, Finset.mem_range, Finset.mem_map]
  constructor
  · rintro ⟨k, hk, y, hy, rfl⟩
    have hs : a*u+b*v+c*k ≤ T := by nlinarith [Nat.mul_le_mul_left c (Nat.le_of_lt hk)]
    have hy' := (mem_weightedPairs ha hb y _).mp hy
    simp only [thirdSlab_apply, tripleWeight]
    refine ⟨by omega, by omega, hk, ?_⟩
    nlinarith [Nat.sub_add_cancel hs]
  · rintro ⟨hu, hv, hx, hw⟩
    refine ⟨x.2.2, hx, (x.1-u,x.2.1-v), ?_, ?_⟩
    · apply (mem_weightedPairs ha hb _ _).mpr
      dsimp [tripleWeight] at hw
      dsimp
      have he := Nat.sub_add_cancel hu
      have he' := Nat.sub_add_cancel hv
      have hs : a*u+b*v+c*x.2.2 ≤ T := by
        nlinarith [Nat.mul_le_mul_left a hu, Nat.mul_le_mul_left b hv]
      nlinarith [Nat.sub_add_cancel hs]
    · simp [Nat.add_sub_cancel' hu, Nat.add_sub_cancel' hv]

private theorem card_indexedSlabs {α β : Type*} [DecidableEq β]
    (q : ℕ → Finset α) (e : ℕ → α ↪ β) (f : β → ℕ)
    (hf : ∀ i x, f (e i x) = i) (n : ℕ) :
    ((Finset.range n).biUnion fun i => (q i).map (e i)).card = ∑ i ∈ Finset.range n, (q i).card := by
  rw [Finset.card_biUnion]
  · simp
  · intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro z hz hz'
    obtain ⟨x, _, hx⟩ := Finset.mem_map.mp hz
    obtain ⟨y, _, hy⟩ := Finset.mem_map.mp hz'
    exact hij ((hf i x).symm.trans ((congrArg f (hx.trans hy.symm)).trans (hf j y)))

theorem weightedNormal_card_slabs {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (m : NatTriple) (T : ℕ) (hT : tripleWeight a b c m ≤ T) :
    (weightedNormal a b c m T).card =
      (∑ i ∈ Finset.range m.1, (weightedPairs b c (T-a*i)).card) +
      (∑ j ∈ Finset.range m.2.1, (weightedPairs a c (T-(a*m.1+b*j))).card) +
      (∑ k ∈ Finset.range m.2.2, (weightedPairs a b (T-(a*m.1+b*m.2.1+c*k))).card) := by
  have h1 : a*m.1 ≤ T := by dsimp [tripleWeight] at hT; omega
  have h2 : a*m.1+b*m.2.1 ≤ T := by dsimp [tripleWeight] at hT; omega
  have he : weightedNormal a b c m T =
      (firstSlabs a b c m.1 T ∪ secondSlabs a b c m.1 m.2.1 T) ∪
        thirdSlabs a b c m.1 m.2.1 m.2.2 T := by
    ext x
    rw [weightedNormal, Finset.mem_filter]
    simp only [mem_weightedTriples ha hb hc,
      Finset.mem_union, mem_firstSlabs ha hb hc h1, mem_secondSlabs ha hb hc h2,
      mem_thirdSlabs ha hb hc hT, tripleDivides]
    omega
  have hd12 : Disjoint (firstSlabs a b c m.1 T) (secondSlabs a b c m.1 m.2.1 T) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    have hx' := (mem_firstSlabs ha hb hc h1 x).mp hx
    have hy' := (mem_secondSlabs ha hb hc h2 x).mp hy
    omega
  have hd3 : Disjoint (firstSlabs a b c m.1 T ∪ secondSlabs a b c m.1 m.2.1 T)
      (thirdSlabs a b c m.1 m.2.1 m.2.2 T) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    have hy' := (mem_thirdSlabs ha hb hc hT x).mp hy
    rcases Finset.mem_union.mp hx with hx | hx
    · have hx' := (mem_firstSlabs ha hb hc h1 x).mp hx; omega
    · have hx' := (mem_secondSlabs ha hb hc h2 x).mp hx; omega
  rw [he, Finset.card_union_of_disjoint hd3, Finset.card_union_of_disjoint hd12]
  congr 2
  · exact card_indexedSlabs _ firstSlab Prod.fst (fun _ _ => rfl) _
  · exact card_indexedSlabs _ (secondSlab m.1) (fun x => x.2.1) (fun _ _ => rfl) _
  · exact card_indexedSlabs _ (thirdSlab m.1 m.2.1) (fun x => x.2.2) (fun _ _ => rfl) _

theorem weightedPairs_shift_volume_error {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (s T : ℕ) (hs : s ≤ T) :
    |((weightedPairs a b (T-s)).card : ℝ) - (T:ℝ)^2/(2*(a*b : ℕ))| ≤
      ((s:ℝ)+2)*T + 4*(a*b : ℕ) := by
  have hL : (1:ℝ) ≤ (a*b : ℕ) := by exact_mod_cast Nat.mul_pos ha hb
  have hd : (0:ℝ) < 2*(a*b : ℕ) := by positivity
  have ht : (T-s : ℕ) + s = T := Nat.sub_add_cancel hs
  have ht' : (T-s : ℕ) + (s:ℝ) = T := by exact_mod_cast ht
  have hp := weightedPairs_volume_error ha hb (T-s)
  have hdiff : |((T-s : ℕ):ℝ)^2/(2*(a*b : ℕ))-(T:ℝ)^2/(2*(a*b : ℕ))| ≤
      (s:ℝ)*T := by
    have hn : ((T-s : ℕ):ℝ)^2-(T:ℝ)^2 ≤ 0 := by nlinarith
    rw [← sub_div, abs_div, abs_of_nonpos hn, abs_of_pos hd]
    apply (div_le_iff₀ hd).mpr
    have hx := mul_le_mul_of_nonneg_right hL (show (0:ℝ) ≤ (s:ℝ)*T by positivity)
    nlinarith
  calc
    _ ≤ |((weightedPairs a b (T-s)).card : ℝ) - ((T-s : ℕ):ℝ)^2/(2*(a*b : ℕ))| +
        |((T-s : ℕ):ℝ)^2/(2*(a*b : ℕ))-(T:ℝ)^2/(2*(a*b : ℕ))| := abs_sub_le ..
    _ ≤ _ := by nlinarith

theorem weightedPairs_shift_sum_error {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (n E T : ℕ) (hT : E ≤ T) (q : ℕ → ℕ) (hq : ∀ i < n, q i ≤ E) :
    |((∑ i ∈ Finset.range n, (weightedPairs a b (T-q i)).card : ℕ) : ℝ) -
      (n:ℝ)*(T:ℝ)^2/(2*(a*b : ℕ))| ≤
      (n:ℝ)*((E:ℝ)+2+4*(a*b : ℕ))*((T:ℝ)+1) := by
  have he : (∑ i ∈ Finset.range n,
      (((weightedPairs a b (T-q i)).card : ℝ) - (T:ℝ)^2/(2*(a*b : ℕ)))) =
      ((∑ i ∈ Finset.range n, (weightedPairs a b (T-q i)).card : ℕ) : ℝ) -
      (n:ℝ)*(T:ℝ)^2/(2*(a*b : ℕ)) := by
    simp [Finset.sum_sub_distrib, mul_div_assoc]
  rw [← he]
  calc
    _ ≤ ∑ i ∈ Finset.range n,
        |((weightedPairs a b (T-q i)).card : ℝ) - (T:ℝ)^2/(2*(a*b : ℕ))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ Finset.range n, (((E:ℝ)+2+4*(a*b : ℕ))*((T:ℝ)+1)) := by
      apply Finset.sum_le_sum
      intro i hi
      have hqi := hq i (Finset.mem_range.mp hi)
      have hqi' : (q i:ℝ) ≤ E := by exact_mod_cast hqi
      have hb' := weightedPairs_shift_volume_error ha hb (q i) T (hqi.trans hT)
      have hx := mul_le_mul_of_nonneg_right hqi' (show (0:ℝ) ≤ T by positivity)
      nlinarith
    _ = _ := by simp; ring

theorem weightedNormal_volume_error {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (m : NatTriple) (T : ℕ) (hT : tripleWeight a b c m ≤ T) :
    |((weightedNormal a b c m T).card : ℝ) -
      (tripleWeight a b c m : ℝ)*(T:ℝ)^2/(2*(a*b*c : ℕ))| ≤
      normalErrorConst a b c m * ((T:ℝ)+1) := by
  have h1 := weightedPairs_shift_sum_error hb hc m.1 (tripleWeight a b c m) T hT
    (fun i => a*i) (by intro i hi; dsimp [tripleWeight]; nlinarith [Nat.mul_le_mul_left a (Nat.le_of_lt hi)])
  have h2 := weightedPairs_shift_sum_error ha hc m.2.1 (tripleWeight a b c m) T hT
    (fun j => a*m.1+b*j) (by intro j hj; dsimp [tripleWeight]; nlinarith [Nat.mul_le_mul_left b (Nat.le_of_lt hj)])
  have h3 := weightedPairs_shift_sum_error ha hb m.2.2 (tripleWeight a b c m) T hT
    (fun k => a*m.1+b*m.2.1+c*k)
    (by intro k hk; dsimp [tripleWeight]; nlinarith [Nat.mul_le_mul_left c (Nat.le_of_lt hk)])
  have he := weightedNormal_card_slabs ha hb hc m T hT
  have ha' : (a:ℝ) ≠ 0 := by positivity
  have hb' : (b:ℝ) ≠ 0 := by positivity
  have hc' : (c:ℝ) ≠ 0 := by positivity
  have hcoeff : (tripleWeight a b c m : ℝ)*(T:ℝ)^2/(2*(a*b*c : ℕ)) =
      (m.1:ℝ)*(T:ℝ)^2/(2*(b*c : ℕ)) + (m.2.1:ℝ)*(T:ℝ)^2/(2*(a*c : ℕ)) +
      (m.2.2:ℝ)*(T:ℝ)^2/(2*(a*b : ℕ)) := by
    simp only [tripleWeight, Nat.cast_add, Nat.cast_mul]
    field_simp
  rw [he, Nat.cast_add, Nat.cast_add, hcoeff]
  have habs (x y z u v w : ℝ) : |x+y+z-(u+v+w)| ≤ |x-u|+|y-v|+|z-w| := by
    calc
      _ = |(x-u)+(y-v)+(z-w)| := by congr 1; ring
      _ ≤ |(x-u)+(y-v)|+|z-w| := abs_add_le _ _
      _ ≤ _ := by linarith [abs_add_le (x-u) (y-v)]
  have hh := habs
    (((∑ i ∈ Finset.range m.1, (weightedPairs b c (T-a*i)).card : ℕ) : ℝ))
    (((∑ j ∈ Finset.range m.2.1, (weightedPairs a c (T-(a*m.1+b*j))).card : ℕ) : ℝ))
    (((∑ k ∈ Finset.range m.2.2, (weightedPairs a b (T-(a*m.1+b*m.2.1+c*k))).card : ℕ) : ℝ))
    ((m.1:ℝ)*(T:ℝ)^2/(2*(b*c : ℕ)))
    ((m.2.1:ℝ)*(T:ℝ)^2/(2*(a*c : ℕ)))
    ((m.2.2:ℝ)*(T:ℝ)^2/(2*(a*b : ℕ)))
  dsimp [normalErrorConst]
  linarith

end

open MvPolynomial
open scoped BigOperators

theorem weightedLift_monomial {σ R : Type*} [CommSemiring R] (w : σ → ℕ)
    (m : σ →₀ ℕ) (r : R) :
    weightedLift w (monomial m r) =
      Polynomial.C (monomial m r) * Polynomial.X ^ (Finsupp.weight w m) := by
  classical
  simp only [weightedLift, eval₂Hom_monomial, RingHom.comp_apply]
  simp only [Finsupp.prod, mul_pow, ← map_pow, Finset.prod_mul_distrib,
    ← map_prod]
  rw [← mul_assoc, ← Polynomial.C_mul]
  congr 1
  · rw [monomial_eq, Finsupp.prod]
  · simp only [← pow_mul, Finset.prod_pow_eq_pow_sum]
    congr 1
    simp [Finsupp.weight, Finsupp.linearCombination_apply, Finsupp.sum, mul_comm]

theorem weightedLift_coeff {σ R : Type*} [CommSemiring R] (w : σ → ℕ)
    (p : MvPolynomial σ R) (t : ℕ) :
    (weightedLift w p).coeff t = weightedHomogeneousComponent w t p := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial m r =>
    rw [weightedLift_monomial, Polynomial.coeff_C_mul_X_pow]
    ext s
    by_cases hs : m = s
    · subst s
      split_ifs <;> simp_all [coeff_weightedHomogeneousComponent, coeff_monomial, eq_comm]
    · split_ifs <;> simp_all [coeff_weightedHomogeneousComponent, coeff_monomial]
  | add p q hp hq => simp [map_add, Polynomial.coeff_add, hp, hq]

theorem weightedLift_eval_one {σ R : Type*} [CommSemiring R] (w : σ → ℕ)
    (p : MvPolynomial σ R) : (weightedLift w p).eval 1 = p := by
  induction p using MvPolynomial.induction_on' with
  | monomial m r => simp [weightedLift_monomial]
  | add p q hp hq => simp [map_add, hp, hq]

theorem weightedLift_injective {σ R : Type*} [CommSemiring R] (w : σ → ℕ) :
    Function.Injective (weightedLift (R := R) w) := by
  intro p q h
  simpa only [weightedLift_eval_one] using congrArg (Polynomial.eval 1) h

theorem weightedLift_natDegree {σ R : Type*} [CommSemiring R] (w : σ → ℕ)
    (p : MvPolynomial σ R) :
    (weightedLift w p).natDegree = weightedTotalDegree w p := by
  classical
  apply le_antisymm
  · apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro t ht
    rw [weightedLift_coeff]
    exact weightedHomogeneousComponent_eq_zero t p ht
  · unfold weightedTotalDegree
    apply Finset.sup_le
    intro m hm
    have hc : (weightedLift w p).coeff (Finsupp.weight w m) ≠ 0 := by
      rw [weightedLift_coeff]
      intro he
      have h := congrArg (fun polynomial => polynomial.coeff m) he
      simp [coeff_weightedHomogeneousComponent, mem_support_iff.mp hm] at h
    exact Polynomial.le_natDegree_of_ne_zero hc

theorem weightedTotalDegree_mul_exact {σ R : Type*} [CommSemiring R] [IsDomain R]
    (w : σ → ℕ) (p q : MvPolynomial σ R) (hp : p ≠ 0) (hq : q ≠ 0) :
    weightedTotalDegree w (p * q) = weightedTotalDegree w p + weightedTotalDegree w q := by
  rw [← weightedLift_natDegree, map_mul, Polynomial.natDegree_mul]
  · rw [weightedLift_natDegree, weightedLift_natDegree]
  · intro h
    apply hp
    apply weightedLift_injective w
    simpa using h
  · intro h
    apply hq
    apply weightedLift_injective w
    simpa using h

theorem finrank_of_exact {K L M N : Type*} [Field K]
    [AddCommGroup L] [Module K L] [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] [Module.Finite K M]
    (g : L →ₗ[K] M) (f : M →ₗ[K] N) (hg : Function.Injective g)
    (he : LinearMap.range g = LinearMap.ker f) :
    Module.finrank K (LinearMap.range f) + Module.finrank K L = Module.finrank K M := by
  rw [← LinearMap.finrank_range_of_inj hg, he]
  exact f.finrank_range_add_finrank_ker

theorem filtered_principal_finrank {K R : Type*} [Field K] [CommRing R]
    [IsDomain R] [Algebra K R] (F G : Submodule K R)
    [Module.Finite K F] (c : R) (hc : c ≠ 0)
    (hdegree : ∀ x : R, c * x ∈ F ↔ x ∈ G) :
    Module.finrank K (F.map (Ideal.Quotient.mkₐ K (Ideal.span {c})).toLinearMap) +
      Module.finrank K G = Module.finrank K F := by
  let f := (Ideal.Quotient.mkₐ K (Ideal.span {c})).toLinearMap.domRestrict F
  let g : G →ₗ[K] F :=
    { toFun := fun x => ⟨c * x.val, (hdegree x.val).mpr x.property⟩
      map_add' := by intros; ext; simp [mul_add]
      map_smul' := by intros; ext; simp }
  have hg : Function.Injective g := by
    intro x y h
    apply Subtype.ext
    exact mul_left_cancel₀ hc (congrArg Subtype.val h)
  have he : LinearMap.range g = LinearMap.ker f := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      change (Ideal.Quotient.mk (Ideal.span {c})) (c * y.val) = 0
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      exact Ideal.mem_span_singleton.mpr ⟨y.val, rfl⟩
    · intro hx
      have hmem : x.val ∈ Ideal.span {c} := Ideal.Quotient.eq_zero_iff_mem.mp hx
      obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.mp hmem
      refine ⟨⟨y, (hdegree y).mp (hy ▸ x.property)⟩, ?_⟩
      apply Subtype.ext
      exact hy.symm
  have hr : LinearMap.range f = F.map (Ideal.Quotient.mkₐ K (Ideal.span {c})).toLinearMap := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x.val, x.property, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  rw [← hr]
  exact finrank_of_exact g f hg he

theorem weightedSpace_finite {σ K : Type*} [Finite σ] [CommSemiring K]
    (w : σ → ℕ) (hw : ∀ i, w i ≠ 0) (T : ℕ) :
    Module.Finite K (weightedSpace (K := K) w T) := by
  have := (Finsupp.finite_of_nat_weight_le w hw T).to_subtype
  exact Module.Finite.of_basis (basisRestrictSupport K _)

theorem weightedSpace_finrank {σ K : Type*} [Finite σ] [Field K]
    (w : σ → ℕ) (hw : ∀ i, w i ≠ 0) (T : ℕ) :
    Module.finrank K (weightedSpace (K := K) w T) =
      Nat.card {m : σ →₀ ℕ // Finsupp.weight w m ≤ T} := by
  have := (Finsupp.finite_of_nat_weight_le w hw T).to_subtype
  exact Module.finrank_eq_nat_card_basis (basisRestrictSupport K _)

theorem weighted_hypersurface_finrank {σ K : Type*} [Finite σ] [Field K]
    (w : σ → ℕ) (hw : ∀ i, w i ≠ 0) (F : MvPolynomial σ K) (hF : F ≠ 0)
    (T : ℕ) (hT : weightedTotalDegree w F ≤ T) :
    Module.finrank K ((weightedSpace w T).map
      (Ideal.Quotient.mkₐ K (Ideal.span {F})).toLinearMap) +
      Nat.card {m : σ →₀ ℕ // Finsupp.weight w m ≤ T - weightedTotalDegree w F} =
      Nat.card {m : σ →₀ ℕ // Finsupp.weight w m ≤ T} := by
  have := weightedSpace_finite (K := K) w hw T
  have hd (p : MvPolynomial σ K) : F * p ∈ weightedSpace w T ↔
      p ∈ weightedSpace w (T - weightedTotalDegree w F) := by
    rw [mem_weightedSpace, mem_weightedSpace]
    by_cases hp : p = 0
    · subst p
      simp [weightedTotalDegree]
    · rw [weightedTotalDegree_mul_exact w F p hF hp]
      omega
  have h := filtered_principal_finrank (weightedSpace w T)
    (weightedSpace w (T - weightedTotalDegree w F)) F hF hd
  rwa [weightedSpace_finrank w hw, weightedSpace_finrank w hw] at h

end QuarticPowerFree

end OAI
end

section
-- module Solutions.OAIB3_Qpf.PowerFree_ComplexValues
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace QuarticPowerFree
open MvPolynomial

theorem weight_eq_tripleWeight (a b c : ℕ) (m : Fin 3 →₀ ℕ) :
    Finsupp.weight (tripleWeights a b c) m = tripleWeight a b c (tripleFinsuppEquiv m) := by
  rw [Finsupp.weight_eq_sum]
  simp [Fin.sum_univ_succ, tripleWeights, tripleWeight, tripleFinsuppEquiv, mul_comm, add_assoc]

theorem tripleWeights_ne_zero {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    ∀ i, tripleWeights a b c i ≠ 0 := by
  intro i
  fin_cases i <;> simp [tripleWeights, ne_of_gt ha, ne_of_gt hb, ne_of_gt hc]

theorem weightedExponents_card {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (T : ℕ) :
    Nat.card {m : Fin 3 →₀ ℕ // Finsupp.weight (tripleWeights a b c) m ≤ T} =
      (weightedTriples a b c T).card := by
  let e : {m : Fin 3 →₀ ℕ // Finsupp.weight (tripleWeights a b c) m ≤ T} ≃
      {x : NatTriple // x ∈ weightedTriples a b c T} :=
    tripleFinsuppEquiv.subtypeEquiv (by intro m; rw [mem_weightedTriples ha hb hc, weight_eq_tripleWeight])
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe]

theorem weighted_hypersurface_normal_card {K : Type*} [Field K]
    {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (F : MvPolynomial (Fin 3) K) (hF : F ≠ 0) (m : NatTriple)
    (hm : tripleWeight a b c m = weightedTotalDegree (tripleWeights a b c) F)
    (T : ℕ) (hT : weightedTotalDegree (tripleWeights a b c) F ≤ T) :
    Module.finrank K ((weightedSpace (tripleWeights a b c) T).map
      (Ideal.Quotient.mkₐ K (Ideal.span {F})).toLinearMap) =
      (weightedNormal a b c m T).card := by
  have hh := weighted_hypersurface_finrank (tripleWeights a b c)
    (tripleWeights_ne_zero ha hb hc) F hF T hT
  rw [weightedExponents_card ha hb hc, weightedExponents_card ha hb hc] at hh
  have hn := weightedNormal_card_add ha hb hc m T (hm ▸ hT)
  rw [hm] at hn
  omega

theorem surface_hilbert_error {K : Type*} [Field K]
    {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (F : MvPolynomial (Fin 3) K) (hF : F ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℕ, weightedTotalDegree (tripleWeights a b c) F ≤ T →
      |(Module.finrank K ((weightedSpace (tripleWeights a b c) T).map
        (Ideal.Quotient.mkₐ K (Ideal.span {F})).toLinearMap) : ℝ) -
        ((weightedTotalDegree (tripleWeights a b c) F : ℕ) : ℝ)*(T:ℝ)^2/(2*(a*b*c : ℕ))|
          ≤ C*((T:ℝ)+1) := by
  classical
  obtain ⟨m, _, hm⟩ := Finset.exists_mem_eq_sup F.support (support_nonempty.mpr hF)
    (Finsupp.weight (tripleWeights a b c))
  have hm' : tripleWeight a b c (tripleFinsuppEquiv m) =
      weightedTotalDegree (tripleWeights a b c) F := by
    rw [← weight_eq_tripleWeight]
    exact hm.symm
  refine ⟨normalErrorConst a b c (tripleFinsuppEquiv m), by unfold normalErrorConst; positivity,
    fun T hT => ?_⟩
  rw [weighted_hypersurface_normal_card ha hb hc F hF _ hm' T hT]
  rw [← hm']
  exact weightedNormal_volume_error ha hb hc _ T (hm' ▸ hT)

end QuarticPowerFree


open Polynomial Matrix
open scoped BigOperators

namespace QuarticPowerFree.ComplexValues

theorem denominator_value_dvd_resultant (A B : ℤ[X])
    (hB : B.natDegree ≠ 0) {s : ℤ} (hs : B.eval s ∣ A.eval s) :
    B.eval s ∣ A.resultant B := by
  obtain ⟨u, v, _, _, h⟩ := Polynomial.exists_mul_add_mul_eq_C_resultant A B
    le_rfl le_rfl (Or.inr hB)
  have he := congrArg (Polynomial.eval s) h
  simp only [eval_add, eval_mul, eval_C] at he
  rw [← he]
  exact dvd_add (dvd_mul_of_dvd_left hs _) (dvd_mul_right _ _)

theorem card_fibre_eval_le (B : ℤ[X]) (hB : 0 < B.natDegree)
    (S : Finset ℤ) (q : ℤ) :
    (S.filter (fun s => B.eval s = q)).card ≤ B.natDegree := by
  have hnz : B - C q ≠ 0 := by
    intro hz
    have hh := congrArg Polynomial.natDegree hz
    rw [natDegree_sub_C, natDegree_zero] at hh
    omega
  have hh : (S.filter (fun s => B.eval s = q)).val ⊆ (B - C q).roots := by
    intro s hs
    have he := (Finset.mem_filter.mp hs).2
    exact Polynomial.mem_roots hnz |>.mpr (by simp [he])
  simpa only [natDegree_sub_C] using Polynomial.card_le_degree_of_subset_roots hh

theorem mem_signedDivisors {r q : ℤ} (hr : r ≠ 0) (hq : q ∣ r) :
    q ∈ signedDivisors r := by
  have hn : q.natAbs ∈ r.natAbs.divisors :=
    Nat.mem_divisors.mpr ⟨Int.natAbs_dvd_natAbs.mpr hq, Int.natAbs_ne_zero.mpr hr⟩
  rcases le_total 0 q with h | h
  · exact Finset.mem_union_left _ (Finset.mem_image.mpr
      ⟨_, hn, by simp [abs_of_nonneg h]⟩)
  · exact Finset.mem_union_right _ (Finset.mem_image.mpr
      ⟨_, hn, by simp [abs_of_nonpos h]⟩)

theorem card_signedDivisors_le (r : ℤ) :
    (signedDivisors r).card ≤ 2 * r.natAbs.divisors.card := by
  exact (Finset.card_union_le _ _).trans (by
    have h₁ := Finset.card_image_le (s := r.natAbs.divisors) (f := fun n => (n : ℤ))
    have h₂ := Finset.card_image_le (s := r.natAbs.divisors) (f := fun n => -(n : ℤ))
    omega)

theorem rational_values_card_le_divisors (A B : ℤ[X])
    (hB : 0 < B.natDegree) (hres : A.resultant B ≠ 0) (S : Finset ℤ) :
    (S.filter (fun s => B.eval s ∣ A.eval s)).card ≤
      2 * B.natDegree * (A.resultant B).natAbs.divisors.card := by
  classical
  let T := S.filter (fun s => B.eval s ∣ A.eval s)
  have himage : T.image B.eval ⊆ signedDivisors (A.resultant B) := by
    intro q hq
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hq
    exact mem_signedDivisors hres (denominator_value_dvd_resultant A B
      (Nat.ne_zero_of_lt hB) (Finset.mem_filter.mp hs).2)
  calc
    T.card = ∑ q ∈ T.image B.eval, (T.filter (fun s => B.eval s = q)).card :=
      (Finset.card_eq_sum_card_image B.eval T)
    _ ≤ ∑ q ∈ T.image B.eval, B.natDegree := by
      apply Finset.sum_le_sum
      intro q _
      exact card_fibre_eval_le B hB T q
    _ = (T.image B.eval).card * B.natDegree := by simp
    _ ≤ (signedDivisors (A.resultant B)).card * B.natDegree :=
      Nat.mul_le_mul_right _ (Finset.card_le_card himage)
    _ ≤ (2 * (A.resultant B).natAbs.divisors.card) * B.natDegree :=
      Nat.mul_le_mul_right _ (card_signedDivisors_le _)
    _ = 2 * B.natDegree * (A.resultant B).natAbs.divisors.card := by ring

theorem rational_function_interpolation_cross {F : Type*} [Field F]
    (A B A₁ B₁ : F[X]) (S : Finset F)
    (hA : A₁.natDegree ≤ A.natDegree) (hB : B₁.natDegree ≤ B.natDegree)
    (hcard : A.natDegree + B.natDegree < S.card)
    (heval : ∀ s ∈ S, A₁.eval s * B.eval s = A.eval s * B₁.eval s) :
    A₁ * B = A * B₁ := by
  apply sub_eq_zero.mp
  apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' _ S
  · intro s hs
    simpa only [eval_sub, eval_mul, sub_eq_zero] using heval s hs
  · have hd := Polynomial.natDegree_sub_le (A₁ * B) (A * B₁)
    have h₁ := Polynomial.natDegree_mul_le (p := A₁) (q := B)
    have h₂ := Polynomial.natDegree_mul_le (p := A) (q := B₁)
    exact lt_of_le_of_lt (hd.trans (max_le (by omega) (by omega))) hcard

theorem rational_function_interpolation_unique {F : Type*} [Field F]
    (A B A₁ B₁ : F[X]) (hcop : IsCoprime A B) (hBn : B ≠ 0)
    (hB : B₁.natDegree ≤ B.natDegree) (heq : A₁ * B = A * B₁) :
    ∃ c : F, A₁ = C c * A ∧ B₁ = C c * B := by
  have hdvd : B ∣ B₁ := hcop.symm.dvd_of_dvd_mul_left (heq ▸ dvd_mul_left B A₁)
  obtain ⟨Q, hQ⟩ := hdvd
  by_cases hQz : Q = 0
  · refine ⟨0, ?_, ?_⟩
    · have hz : A₁ = 0 := by
        apply (mul_eq_zero.mp ?_).resolve_right hBn
        rw [heq, hQ, hQz, mul_zero, mul_zero]
      simpa using hz
    · simp [hQ, hQz]
  · have hdeg : Q.natDegree = 0 := by
      rw [hQ, Polynomial.natDegree_mul hBn hQz] at hB
      omega
    have hQc : Q = C (Q.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hdeg
    refine ⟨Q.coeff 0, ?_, ?_⟩
    · apply mul_right_cancel₀ hBn
      conv_lhs => rw [heq, hQ, hQc]
      ring
    · calc B₁ = B * Q := hQ
           _ = B * C (Q.coeff 0) := congrArg (B * ·) hQc
           _ = C (Q.coeff 0) * B := mul_comm _ _

theorem interpolationRow_some_dot {R ι : Type*} [CommRing R] [DecidableEq R] {a b : ℕ}
    (s v : ι → R) (t : ι) (c : Fin (a + 1) ⊕ Fin (b + 1) → R) :
    interpolationRow s v (some t) ⬝ᵥ c =
      (Polynomial.ofFn (a + 1) (fun j => c (Sum.inl j))).eval (s t) -
      v t * (Polynomial.ofFn (b + 1) (fun j => c (Sum.inr j))).eval (s t) := by
  classical
  simp only [interpolationRow, dotProduct, Fintype.sum_sum_type,
    Sum.elim_inl, Sum.elim_inr, Polynomial.ofFn_eq_sum_monomial,
    Polynomial.eval_finsetSum, Polynomial.eval_monomial, Finset.mul_sum,
    neg_mul, Finset.sum_neg_distrib, sub_eq_add_neg]
  congr 1
  · exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)
  · congr 1
    exact Finset.sum_congr rfl (fun j _ => by ring)

theorem interpolationRow_none_dot {R ι : Type*} [CommRing R] {a b : ℕ}
    (s v : ι → R) (c : Fin (a + 1) ⊕ Fin (b + 1) → R) :
    interpolationRow s v none ⬝ᵥ c = c (Sum.inr ⟨b, Nat.lt_succ_self b⟩) := by
  rw [interpolationRow, single_dotProduct, one_mul]

theorem interpolationMatrix_det_ne_zero {F ι : Type*} [Field F] [Fintype ι]
    (A B : F[X]) (hcop : IsCoprime A B) (hBn : B ≠ 0)
    (s v : ι → F) (hs : Function.Injective s)
    (hcard : A.natDegree + B.natDegree < Fintype.card ι)
    (heval : ∀ i, A.eval (s i) = v i * B.eval (s i))
    (e : (Fin (A.natDegree + 1) ⊕ Fin (B.natDegree + 1)) ≃ Option ι) :
    (interpolationMatrix s v e).det ≠ 0 := by
  classical
  let M := interpolationMatrix s v e
  have hker : ∀ c, M *ᵥ c = 0 → c = 0 := by
    intro c hc
    let P := Polynomial.ofFn (A.natDegree + 1) (fun j => c (Sum.inl j))
    let Q := Polynomial.ofFn (B.natDegree + 1) (fun j => c (Sum.inr j))
    have hpdeg : P.natDegree ≤ A.natDegree := by
      have h := Polynomial.ofFn_natDegree_lt (R := F) (Nat.succ_pos A.natDegree)
        (fun j => c (Sum.inl j))
      exact Nat.le_of_lt_succ h
    have hqdeg : Q.natDegree ≤ B.natDegree := by
      have h := Polynomial.ofFn_natDegree_lt (R := F) (Nat.succ_pos B.natDegree)
        (fun j => c (Sum.inr j))
      exact Nat.le_of_lt_succ h
    have hpeval (i : ι) : P.eval (s i) = v i * Q.eval (s i) := by
      have hh := congrFun hc (e.symm (some i))
      change interpolationRow s v (e (e.symm (some i))) ⬝ᵥ c = 0 at hh
      rw [e.apply_symm_apply, interpolationRow_some_dot] at hh
      exact sub_eq_zero.mp hh
    have hcross : P * B = A * Q := by
      apply rational_function_interpolation_cross A B P Q (Finset.univ.image s) hpdeg hqdeg
      · simpa only [Finset.card_image_of_injective _ hs, Finset.card_univ] using hcard
      · intro x hx
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
        rw [hpeval, heval]
        ring
    obtain ⟨r, hP, hQ⟩ := rational_function_interpolation_unique A B P Q hcop hBn hqdeg hcross
    have hqzero : Q.coeff B.natDegree = 0 := by
      have hh := congrFun hc (e.symm none)
      change interpolationRow s v (e (e.symm none)) ⬝ᵥ c = 0 at hh
      rw [e.apply_symm_apply, interpolationRow_none_dot] at hh
      simpa only [Q, Polynomial.ofFn_coeff_eq_val_of_lt _ (Nat.lt_succ_self _)] using hh
    have hr : r = 0 := by
      rw [hQ, Polynomial.coeff_C_mul] at hqzero
      exact (mul_eq_zero.mp hqzero).resolve_right (Polynomial.leadingCoeff_ne_zero.mpr hBn)
    have hpzero : P = 0 := by simp [hP, hr]
    have hqzero' : Q = 0 := by simp [hQ, hr]
    funext j
    rcases j with j | j
    · have hh := congrArg (fun p : F[X] => p.coeff j.val) hpzero
      simpa only [P, Polynomial.ofFn_coeff_eq_val_of_lt _ j.isLt, Polynomial.coeff_zero,
        Pi.zero_apply] using hh
    · have hh := congrArg (fun p : F[X] => p.coeff j.val) hqzero'
      simpa only [Q, Polynomial.ofFn_coeff_eq_val_of_lt _ j.isLt, Polynomial.coeff_zero,
        Pi.zero_apply] using hh
  have hi : Function.Injective (Matrix.mulVecLin M) :=
    LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.mpr hker)
  exact (M.isUnit_iff_isUnit_det.mp (Matrix.mulVec_injective_iff_isUnit.mp hi)).ne_zero

theorem interpolationMatrix_map {R S ι : Type*} [CommRing R] [CommRing S]
    {a b : ℕ} (f : R →+* S) (s v : ι → R)
    (e : (Fin (a + 1) ⊕ Fin (b + 1)) ≃ Option ι) :
    (interpolationMatrix s v e).map f =
      interpolationMatrix (fun i => f (s i)) (fun i => f (v i)) e := by
  classical
  ext i j
  change f (interpolationRow s v (e i) j) = _
  change _ = interpolationRow (fun i => f (s i)) (fun i => f (v i)) (e i) j
  rcases h : e i with _ | t
  · simp only [interpolationRow]
    by_cases hj : j = Sum.inr ⟨b, Nat.lt_succ_self b⟩
    · subst j
      simp
    · simp [Pi.single_eq_of_ne hj]
  · rcases j with j | j <;> simp [interpolationRow]

theorem rational_interpolation_integral_pair {ι : Type*} [Fintype ι]
    (A B : ℂ[X]) (hcop : IsCoprime A B) (hBn : B ≠ 0)
    (s v : ι → ℤ) (hs : Function.Injective s)
    (hcard : A.natDegree + B.natDegree < Fintype.card ι)
    (heval : ∀ i, A.eval (s i : ℂ) = (v i : ℂ) * B.eval (s i : ℂ))
    (e : (Fin (A.natDegree + 1) ⊕ Fin (B.natDegree + 1)) ≃ Option ι) :
    ∃ P Q : ℤ[X], ∃ r : ℂ, r ≠ 0 ∧
      P.map (Int.castRingHom ℂ) = C r * A ∧
      Q.map (Int.castRingHom ℂ) = C r * B ∧
      P.natDegree ≤ A.natDegree ∧ Q.natDegree ≤ B.natDegree ∧
      P = Polynomial.ofFn (A.natDegree + 1)
        (fun j => interpolationCramer s v e (Sum.inl j)) ∧
      Q = Polynomial.ofFn (B.natDegree + 1)
        (fun j => interpolationCramer s v e (Sum.inr j)) := by
  classical
  let M := interpolationMatrix s v e
  let u : Fin (A.natDegree + 1) ⊕ Fin (B.natDegree + 1) → ℤ :=
    fun j => if e j = none then 1 else 0
  let c := M.cramer u
  let P := Polynomial.ofFn (A.natDegree + 1) (fun j => c (Sum.inl j))
  let Q := Polynomial.ofFn (B.natDegree + 1) (fun j => c (Sum.inr j))
  have hdet : M.det ≠ 0 := by
    have h := interpolationMatrix_det_ne_zero A B hcop hBn
      (fun i => (s i : ℂ)) (fun i => (v i : ℂ))
      (Int.cast_injective.comp hs) hcard heval e
    intro hz
    apply h
    have hm := interpolationMatrix_map (Int.castRingHom ℂ) s v e
    simp only [Int.coe_castRingHom] at hm
    rw [← hm, ← Int.cast_det,
      show (interpolationMatrix s v e).det = 0 from hz, Int.cast_zero]
  have hc : M *ᵥ c = M.det • u := M.mulVec_cramer u
  have hpdeg : P.natDegree ≤ A.natDegree := Nat.le_of_lt_succ
    (Polynomial.ofFn_natDegree_lt (R := ℤ) (Nat.succ_pos _) _)
  have hqdeg : Q.natDegree ≤ B.natDegree := Nat.le_of_lt_succ
    (Polynomial.ofFn_natDegree_lt (R := ℤ) (Nat.succ_pos _) _)
  let f := Int.castRingHom ℂ
  have heval' (i : ι) : (P.map f).eval (s i : ℂ) = (v i : ℂ) * (Q.map f).eval (s i : ℂ) := by
    have hh := congrFun hc (e.symm (some i))
    change interpolationRow s v (e (e.symm (some i))) ⬝ᵥ c = _ at hh
    rw [e.apply_symm_apply, interpolationRow_some_dot] at hh
    have hz : P.eval (s i) - v i * Q.eval (s i) = 0 := by
      simpa [P, Q, u] using hh
    have he := congrArg f (sub_eq_zero.mp hz)
    simpa only [Polynomial.eval_intCast_map, Int.cast_id, map_mul, f, Int.coe_castRingHom] using he
  have hcross : (P.map f) * B = A * (Q.map f) := by
    apply rational_function_interpolation_cross A B _ _
      (Finset.univ.image (fun i => (s i : ℂ)))
    · rwa [Polynomial.natDegree_map_eq_of_injective Int.cast_injective]
    · rwa [Polynomial.natDegree_map_eq_of_injective Int.cast_injective]
    · have hsQ : Function.Injective (fun i => (s i : ℂ)) := Int.cast_injective.comp hs
      rw [Finset.card_image_of_injective _ hsQ, Finset.card_univ]
      exact hcard
    · intro x hx
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
      rw [heval', heval]
      ring
  obtain ⟨r, hP, hQ⟩ := rational_function_interpolation_unique A B _ _ hcop hBn
    (by rwa [Polynomial.natDegree_map_eq_of_injective Int.cast_injective]) hcross
  have hr : r ≠ 0 := by
    intro hr
    have hzero : Q.map f = 0 := by simp [hQ, hr]
    have hcoef : Q.coeff B.natDegree = M.det := by
      have hh := congrFun hc (e.symm none)
      change interpolationRow s v (e (e.symm none)) ⬝ᵥ c = _ at hh
      rw [e.apply_symm_apply, interpolationRow_none_dot] at hh
      simpa [Q, u, Polynomial.ofFn_coeff_eq_val_of_lt _ (Nat.lt_succ_self _)] using hh
    have hz := congrArg (fun p : ℂ[X] => p.coeff B.natDegree) hzero
    simp only [Polynomial.coeff_map, Polynomial.coeff_zero, hcoef] at hz
    exact hdet (Int.cast_eq_zero.mp hz)
  exact ⟨P, Q, r, hr, hP, hQ, hpdeg, hqdeg, rfl, rfl⟩

theorem det_abs_le_row_product {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (B : ι → ℝ)
    (hA : ∀ i j, |A i j| ≤ B i) :
    |A.det| ≤ (Nat.factorial (Fintype.card ι) : ℝ) * ∏ i, B i := by
  calc
    |A.det| = |∑ σ : Equiv.Perm ι, Equiv.Perm.sign σ • ∏ i, A (σ i) i| := by
      rw [Matrix.det_apply]
    _ ≤ ∑ σ : Equiv.Perm ι, |Equiv.Perm.sign σ • ∏ i, A (σ i) i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ σ : Equiv.Perm ι, ∏ i, |A (σ i) i| := by
      apply Finset.sum_congr rfl
      intro σ _
      rw [show |Equiv.Perm.sign σ • ∏ i, A (σ i) i| = |∏ i, A (σ i) i| from
        AbsoluteValue.abs.map_units_int_smul _ _, Finset.abs_prod]
    _ ≤ ∑ σ : Equiv.Perm ι, ∏ i, B (σ i) := by
      apply Finset.sum_le_sum
      intro σ _
      exact Finset.prod_le_prod (fun i _ => abs_nonneg _) (fun i _ => hA (σ i) i)
    _ = (Nat.factorial (Fintype.card ι) : ℝ) * ∏ i, B i := by
      simp_rw [Equiv.prod_comp]
      simp [Fintype.card_perm]

theorem det_abs_le_uniform {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℤ) (B : ℝ) (hA : ∀ i j, |(A i j : ℝ)| ≤ B) :
    |(A.det : ℝ)| ≤ (Nat.factorial (Fintype.card ι) : ℝ) * B ^ Fintype.card ι := by
  rw [Int.cast_det]
  simpa only [Finset.prod_const, Finset.card_univ] using
    det_abs_le_row_product (A.map fun x => (x : ℝ)) (fun _ => B) hA

theorem interpolationRow_abs_le {ι : Type*} {a b : ℕ} (s v : ι → ℤ)
    (H : ℝ) (hH : 1 ≤ H) (hs : ∀ i, |(s i : ℝ)| ≤ H)
    (hv : ∀ i, |(v i : ℝ)| ≤ H) (i : Option ι)
    (j : Fin (a + 1) ⊕ Fin (b + 1)) :
    |((interpolationRow s v i j : ℤ) : ℝ)| ≤ H ^ (max a b + 1) := by
  classical
  have h0 : 0 ≤ H := zero_le_one.trans hH
  cases i with
  | none =>
    by_cases hj : j = Sum.inr ⟨b, Nat.lt_succ_self b⟩
    · subst j
      simpa [interpolationRow] using one_le_pow₀ hH (n := max a b + 1)
    · simp [interpolationRow, Pi.single_eq_of_ne hj, pow_nonneg h0]
  | some i =>
    cases j with
    | inl j =>
      simp only [interpolationRow, Sum.elim_inl, Int.cast_pow, abs_pow]
      exact (pow_le_pow_left₀ (abs_nonneg _) (hs i) _).trans
        (pow_le_pow_right₀ hH (by have := j.isLt; omega))
    | inr j =>
      simp only [interpolationRow, Sum.elim_inr, Int.cast_neg, Int.cast_mul,
        Int.cast_pow, abs_neg, abs_mul, abs_pow]
      calc
        |(v i : ℝ)| * |(s i : ℝ)| ^ j.val ≤ H * H ^ j.val :=
          mul_le_mul (hv i) (pow_le_pow_left₀ (abs_nonneg _) (hs i) _)
            (by positivity) h0
        _ = H ^ (j.val + 1) := by rw [pow_succ]; ring
        _ ≤ H ^ (max a b + 1) := pow_le_pow_right₀ hH (by have := j.isLt; omega)

theorem interpolationCramer_abs_le {ι : Type*} [Fintype ι] {a b : ℕ}
    (s v : ι → ℤ) (e : (Fin (a + 1) ⊕ Fin (b + 1)) ≃ Option ι)
    (H : ℝ) (hH : 1 ≤ H) (hs : ∀ i, |(s i : ℝ)| ≤ H)
    (hv : ∀ i, |(v i : ℝ)| ≤ H) (j : Fin (a + 1) ⊕ Fin (b + 1)) :
    |(interpolationCramer s v e j : ℝ)| ≤
      (Nat.factorial (a + b + 2) : ℝ) * H ^ ((max a b + 1) * (a + b + 2)) := by
  classical
  unfold interpolationCramer
  rw [Matrix.cramer_apply]
  have h := det_abs_le_uniform
    ((interpolationMatrix s v e).updateCol j (fun j => if e j = none then 1 else 0))
    (H ^ (max a b + 1)) (fun i j' => ?_)
  · simpa only [Fintype.card_sum, Fintype.card_fin, ← pow_mul,
      show a + 1 + (b + 1) = a + b + 2 by omega] using h
  · by_cases hj : j' = j
    · subst j'
      simp only [Matrix.updateCol_self]
      split_ifs
      · simpa using one_le_pow₀ hH (n := max a b + 1)
      · simp [pow_nonneg (zero_le_one.trans hH)]
    · rw [Matrix.updateCol_ne hj]
      exact interpolationRow_abs_le s v H hH hs hv (e i) j'

theorem interpolationHeight_one_le (D : ℕ) {H : ℝ} (hH : 1 ≤ H) :
    1 ≤ interpolationHeight D H := by
  exact one_le_mul_of_one_le_of_one_le (by exact_mod_cast Nat.factorial_pos (2 * D + 2))
    (one_le_pow₀ hH)

theorem interpolationCramer_abs_le_degree_bound {ι : Type*} [Fintype ι] {a b : ℕ}
    (s v : ι → ℤ) (e : (Fin (a + 1) ⊕ Fin (b + 1)) ≃ Option ι)
    (D : ℕ) (ha : a ≤ D) (hb : b ≤ D)
    (H : ℝ) (hH : 1 ≤ H) (hs : ∀ i, |(s i : ℝ)| ≤ H)
    (hv : ∀ i, |(v i : ℝ)| ≤ H) (j : Fin (a + 1) ⊕ Fin (b + 1)) :
    |(interpolationCramer s v e j : ℝ)| ≤ interpolationHeight D H := by
  apply (interpolationCramer_abs_le s v e H hH hs hv j).trans
  apply mul_le_mul
  · exact_mod_cast Nat.factorial_le (show a + b + 2 ≤ 2 * D + 2 by omega)
  · exact pow_le_pow_right₀ hH (Nat.mul_le_mul (by omega) (by omega))
  · positivity
  · positivity

theorem resultant_abs_le_coeff_bound (P Q : ℤ[X]) (H : ℝ) (hH : 0 ≤ H)
    (hP : ∀ j, |(P.coeff j : ℝ)| ≤ H) (hQ : ∀ j, |(Q.coeff j : ℝ)| ≤ H) :
    |(P.resultant Q : ℝ)| ≤ (Nat.factorial (P.natDegree + Q.natDegree) : ℝ) *
      H ^ (P.natDegree + Q.natDegree) := by
  unfold Polynomial.resultant
  apply (det_abs_le_uniform _ H ?_).trans_eq
  · simp only [Fintype.card_fin]
  · intro i j
    refine Fin.addCases ?_ ?_ j
    · intro j'
      simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_left]
      split_ifs
      · exact hQ _
      · simpa using hH
    · intro j'
      simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_right]
      split_ifs
      · exact hP _
      · simpa using hH

theorem resultant_ne_zero_of_scalar_maps (A B : ℂ[X]) (P Q : ℤ[X])
    (hcop : IsCoprime A B) (r : ℂ) (hr : r ≠ 0)
    (hP : P.map (Int.castRingHom ℂ) = C r * A)
    (hQ : Q.map (Int.castRingHom ℂ) = C r * B) : P.resultant Q ≠ 0 := by
  have hcop' : IsCoprime (P.map (Int.castRingHom ℂ)) (Q.map (Int.castRingHom ℂ)) := by
    rw [hP, hQ]
    obtain ⟨u, v, huv⟩ := hcop
    refine ⟨C r⁻¹ * u, C r⁻¹ * v, ?_⟩
    calc
      C r⁻¹ * u * (C r * A) + C r⁻¹ * v * (C r * B) =
          C r⁻¹ * C r * (u * A + v * B) := by ring
      _ = 1 := by rw [huv, ← Polynomial.C_mul]; simp [hr]
  have hh := Polynomial.resultant_ne_zero _ _ hcop'
  rw [Polynomial.natDegree_map_eq_of_injective Int.cast_injective,
    Polynomial.natDegree_map_eq_of_injective Int.cast_injective,
    Polynomial.resultant_map_map] at hh
  exact fun hz => hh (by simp only [hz, map_zero])

theorem rational_interpolation_height {ι : Type*} [Fintype ι]
    (A B : ℂ[X]) (hcop : IsCoprime A B) (hBn : B ≠ 0)
    (s v : ι → ℤ) (hs : Function.Injective s)
    (hcard : A.natDegree + B.natDegree < Fintype.card ι)
    (heval : ∀ i, A.eval (s i : ℂ) = (v i : ℂ) * B.eval (s i : ℂ))
    (e : (Fin (A.natDegree + 1) ⊕ Fin (B.natDegree + 1)) ≃ Option ι)
    (D : ℕ) (hA : A.natDegree ≤ D) (hB : B.natDegree ≤ D)
    (H : ℝ) (hH : 1 ≤ H) (hsH : ∀ i, |(s i : ℝ)| ≤ H)
    (hvH : ∀ i, |(v i : ℝ)| ≤ H) :
    ∃ P Q : ℤ[X], ∃ r : ℂ, r ≠ 0 ∧
      P.map (Int.castRingHom ℂ) = C r * A ∧
      Q.map (Int.castRingHom ℂ) = C r * B ∧
      P.natDegree ≤ D ∧ Q.natDegree = B.natDegree ∧
      P.resultant Q ≠ 0 ∧
      (∀ j, |(P.coeff j : ℝ)| ≤ interpolationHeight D H) ∧
      (∀ j, |(Q.coeff j : ℝ)| ≤ interpolationHeight D H) := by
  obtain ⟨P, Q, r, hr, hP, hQ, hpdeg, _, hPc, hQc⟩ :=
    rational_interpolation_integral_pair A B hcop hBn s v hs hcard heval e
  have hqdeg : Q.natDegree = B.natDegree := by
    rw [← Polynomial.natDegree_map_eq_of_injective (p := Q) (f := Int.castRingHom ℂ) Int.cast_injective,
      hQ, Polynomial.natDegree_C_mul hr]
  refine ⟨P, Q, r, hr, hP, hQ, hpdeg.trans hA, hqdeg,
    resultant_ne_zero_of_scalar_maps A B P Q hcop r hr hP hQ, ?_, ?_⟩
  · intro j
    rw [hPc]
    by_cases hj : j < A.natDegree + 1
    · rw [Polynomial.ofFn_coeff_eq_val_of_lt _ hj]
      exact interpolationCramer_abs_le_degree_bound s v e D hA hB H hH hsH hvH _
    · rw [Polynomial.ofFn_coeff_eq_zero_of_ge _ (by omega)]
      exact_mod_cast (zero_le_one.trans (interpolationHeight_one_le D hH))
  · intro j
    rw [hQc]
    by_cases hj : j < B.natDegree + 1
    · rw [Polynomial.ofFn_coeff_eq_val_of_lt _ hj]
      exact interpolationCramer_abs_le_degree_bound s v e D hA hB H hH hsH hvH _
    · rw [Polynomial.ofFn_coeff_eq_zero_of_ge _ (by omega)]
      exact_mod_cast (zero_le_one.trans (interpolationHeight_one_le D hH))

theorem eval_eq_mul_of_scalar_maps (A B : ℂ[X]) (P Q : ℤ[X]) (r : ℂ)
    (hP : P.map (Int.castRingHom ℂ) = C r * A)
    (hQ : Q.map (Int.castRingHom ℂ) = C r * B) (s v : ℤ)
    (hv : A.eval (s : ℂ) = (v : ℂ) * B.eval (s : ℂ)) :
    P.eval s = v * Q.eval s := by
  apply Int.cast_injective (α := ℂ)
  have hp := congrArg (Polynomial.eval (s : ℂ)) hP
  have hq := congrArg (Polynomial.eval (s : ℂ)) hQ
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_intCast_map, Int.coe_castRingHom, Int.cast_id] at hp hq
  push_cast
  rw [hp, hq, hv]
  ring

theorem rational_values_height_representative
    (A B : ℂ[X]) (hcop : IsCoprime A B) (hBn : B ≠ 0)
    (S : Finset ℤ) (v : ℤ → ℤ)
    (heval : ∀ s ∈ S, A.eval (s : ℂ) = (v s : ℂ) * B.eval (s : ℂ))
    (hcard : A.natDegree + B.natDegree < S.card)
    (D : ℕ) (hA : A.natDegree ≤ D) (hB : B.natDegree ≤ D)
    (H : ℝ) (hH : 1 ≤ H) (hsH : ∀ s ∈ S, |(s : ℝ)| ≤ H)
    (hvH : ∀ s ∈ S, |(v s : ℝ)| ≤ H) :
    ∃ P Q : ℤ[X], P.natDegree ≤ D ∧ Q.natDegree = B.natDegree ∧
      P.resultant Q ≠ 0 ∧
      (∀ j, |(P.coeff j : ℝ)| ≤ interpolationHeight D H) ∧
      (∀ j, |(Q.coeff j : ℝ)| ≤ interpolationHeight D H) ∧
      ∀ s ∈ S, P.eval s = v s * Q.eval s := by
  classical
  obtain ⟨T, hTS, hTc⟩ := Finset.exists_subset_card_eq (Nat.succ_le_of_lt hcard)
  let e : (Fin (A.natDegree + 1) ⊕ Fin (B.natDegree + 1)) ≃ Option T :=
    Fintype.equivOfCardEq (by simp [hTc]; omega)
  obtain ⟨P, Q, r, _, hP, hQ, hpdeg, hqdeg, hres, hpH, hqH⟩ :=
    rational_interpolation_height A B hcop hBn
      (fun s : T => s.val) (fun s : T => v s.val) Subtype.val_injective
      (by simp [hTc])
      (fun s => heval s.val (hTS s.property)) e D hA hB H hH
      (fun s => hsH s.val (hTS s.property)) (fun s => hvH s.val (hTS s.property))
  refine ⟨P, Q, hpdeg, hqdeg, hres, hpH, hqH, ?_⟩
  intro s hs
  exact eval_eq_mul_of_scalar_maps A B P Q r hP hQ s (v s) (heval s hs)

theorem rationalResultantConstant_pos (D : ℕ) : 0 < rationalResultantConstant D := by
  unfold rationalResultantConstant
  positivity

theorem rationalResultantExponent_pos {D : ℕ} (hD : 0 < D) :
    0 < rationalResultantExponent D := by
  unfold rationalResultantExponent
  positivity

theorem resultant_abs_le_interpolation_height (P Q : ℤ[X]) (D : ℕ)
    (hPdeg : P.natDegree ≤ D) (hQdeg : Q.natDegree ≤ D)
    (H : ℝ) (hH : 1 ≤ H)
    (hP : ∀ j, |(P.coeff j : ℝ)| ≤ interpolationHeight D H)
    (hQ : ∀ j, |(Q.coeff j : ℝ)| ≤ interpolationHeight D H) :
    |(P.resultant Q : ℝ)| ≤ rationalResultantConstant D * H ^ rationalResultantExponent D := by
  have hi := interpolationHeight_one_le D hH
  apply (resultant_abs_le_coeff_bound P Q (interpolationHeight D H)
    (zero_le_one.trans hi) hP hQ).trans
  calc
    _ ≤ (Nat.factorial (2 * D) : ℝ) * interpolationHeight D H ^ (2 * D) := by
      apply mul_le_mul
      · exact_mod_cast Nat.factorial_le (show P.natDegree + Q.natDegree ≤ 2 * D by omega)
      · exact pow_le_pow_right₀ hi (by omega)
      · positivity
      · positivity
    _ = rationalResultantConstant D * H ^ rationalResultantExponent D := by
      simp only [interpolationHeight, rationalResultantConstant, rationalResultantExponent,
        mul_pow, ← pow_mul]
      rw [Nat.mul_comm ((D + 1) * (2 * D + 2)) (2 * D)]
      ring

open Filter

theorem succ_le_geometric (r : ℝ) (hr : 1 < r) (a : ℕ) :
    (a : ℝ) + 1 ≤ (1 + (r - 1)⁻¹) * r ^ a := by
  have h₁ := a.cast_le_pow_div_sub hr
  have h₂ : (1 : ℝ) ≤ r ^ a := one_le_pow₀ hr.le
  calc
    (a : ℝ) + 1 ≤ r ^ a / (r - 1) + r ^ a := add_le_add h₁ h₂
    _ = (1 + (r - 1)⁻¹) * r ^ a := by ring

theorem divisors_card_le_rpow (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, (n.divisors.card : ℝ) ≤ C * (n : ℝ) ^ ε := by
  let r : ℝ := (2 : ℝ) ^ ε
  have hr : 1 < r := Real.one_lt_rpow (by norm_num) hε
  let c : ℝ := 1 + (r - 1)⁻¹
  have hc : 1 ≤ c := by
    have hh : 0 ≤ (r - 1)⁻¹ := inv_nonneg.mpr (sub_nonneg.mpr hr.le)
    dsimp [c]
    linarith
  have hc0 : 0 < c := lt_of_lt_of_le zero_lt_one hc
  have ht : Tendsto (fun p : ℕ => (p : ℝ) ^ ε) atTop atTop :=
    (tendsto_rpow_atTop hε).comp tendsto_natCast_atTop_atTop
  obtain ⟨N, hN⟩ := eventually_atTop.mp (ht.eventually (eventually_ge_atTop (2 : ℝ)))
  refine ⟨c ^ N, pow_pos hc0 _, ?_⟩
  intro n
  by_cases hn : n = 0
  · simp [hn, Real.zero_rpow hε.ne']
  have hfactor (p : ℕ) (hp : p ∈ n.primeFactors) :
      (n.factorization p : ℝ) + 1 ≤
        (if p < N then c else 1) * ((p : ℝ) ^ ε) ^ n.factorization p := by
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    by_cases hsmall : p < N
    · rw [ite_eq_left hsmall]
      exact (succ_le_geometric r hr _).trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) (Real.rpow_le_rpow (by norm_num) hp2 hε.le) _)
        hc0.le)
    · rw [ite_eq_right hsmall, one_mul]
      have hh : (n.factorization p : ℝ) + 1 ≤ (2 : ℝ) ^ n.factorization p := by
        exact_mod_cast Nat.succ_le_of_lt (Nat.lt_two_pow_self (n := n.factorization p))
      exact hh.trans (pow_le_pow_left₀ (by norm_num) (hN p (Nat.le_of_not_gt hsmall)) _)
  have hconstant : (∏ p ∈ n.primeFactors, if p < N then c else 1) ≤ c ^ N := by
    rw [Finset.prod_ite]
    simp only [Finset.prod_const_one, mul_one, Finset.prod_const]
    apply pow_le_pow_right₀ hc
    exact (Finset.card_le_card (show n.primeFactors.filter (fun p => p < N) ⊆
      Finset.range N from fun p hp => Finset.mem_range.mpr (Finset.mem_filter.mp hp).2)).trans
        (by rw [Finset.card_range])
  have hpowers : (∏ p ∈ n.primeFactors, ((p : ℝ) ^ ε) ^ n.factorization p) =
      (n : ℝ) ^ ε := by
    simp_rw [← Real.rpow_mul_natCast (Nat.cast_nonneg _) ε,
      mul_comm ε, Real.rpow_natCast_mul (Nat.cast_nonneg _) _ ε]
    rw [Real.finsetProd_rpow _ _ (fun _ _ => by positivity)]
    congr 1
    exact_mod_cast (Nat.prod_primeFactors_pow_factorization hn).symm
  calc
    (n.divisors.card : ℝ) = ∏ p ∈ n.primeFactors, ((n.factorization p : ℝ) + 1) := by
      rw [Nat.card_divisors hn]
      push_cast
      rfl
    _ ≤ ∏ p ∈ n.primeFactors,
        (if p < N then c else 1) * ((p : ℝ) ^ ε) ^ n.factorization p :=
      Finset.prod_le_prod (fun p _ => by positivity) hfactor
    _ = (∏ p ∈ n.primeFactors, if p < N then c else 1) * (n : ℝ) ^ ε := by
      rw [Finset.prod_mul_distrib, hpowers]
    _ ≤ c ^ N * (n : ℝ) ^ ε := mul_le_mul_of_nonneg_right hconstant (by positivity)

theorem rational_values_card_le_rpow (D : ℕ) (hD : 0 < D) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A B : ℂ[X]), IsCoprime A B →
      0 < B.natDegree → A.natDegree ≤ D → B.natDegree ≤ D →
      ∀ (S : Finset ℤ) (v : ℤ → ℤ) (H : ℝ), 1 ≤ H →
      (∀ s ∈ S, A.eval (s : ℂ) = (v s : ℂ) * B.eval (s : ℂ)) →
      (∀ s ∈ S, |(s : ℝ)| ≤ H) → (∀ s ∈ S, |(v s : ℝ)| ≤ H) →
      (S.card : ℝ) ≤ C * H ^ ε := by
  let E := rationalResultantExponent D
  have hE : (0 : ℝ) < E := by exact_mod_cast rationalResultantExponent_pos hD
  let δ := ε / (E : ℝ)
  have hδ : 0 < δ := div_pos hε hE
  obtain ⟨c, hc, hdiv⟩ := divisors_card_le_rpow δ hδ
  let K := rationalResultantConstant D
  have hK : 0 < K := rationalResultantConstant_pos D
  let C : ℝ := (2 * D : ℕ) + (2 * D : ℕ) * c * K ^ δ
  have h2D : (0 : ℝ) < (2 * D : ℕ) := by exact_mod_cast (by omega : 0 < 2 * D)
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro A B hcop hBpos hAdeg hBdeg S v H hH heval hsH hvH
  have hHε : 1 ≤ H ^ ε := Real.one_le_rpow hH hε.le
  by_cases hcard : A.natDegree + B.natDegree < S.card
  · have hBn : B ≠ 0 := by
      intro hz
      simp only [hz, Polynomial.natDegree_zero, lt_self_iff_false] at hBpos
    obtain ⟨P, Q, hPdeg, hQdeg, hres, hP, hQ, hpq⟩ :=
      rational_values_height_representative A B hcop hBn S v heval hcard D hAdeg hBdeg
        H hH hsH hvH
    have hi : S.filter (fun s => Q.eval s ∣ P.eval s) = S := by
      apply Finset.filter_eq_self.mpr
      intro s hs
      rw [hpq s hs]
      exact dvd_mul_left _ _
    have hτ := rational_values_card_le_divisors P Q (by omega) hres S
    rw [hi] at hτ
    have hR : ((P.resultant Q).natAbs : ℝ) ≤ K * H ^ E := by
      have hab : ((P.resultant Q).natAbs : ℝ) = |(P.resultant Q : ℝ)| := by
        rw [Nat.cast_natAbs, Int.cast_abs]
      rw [hab]
      exact resultant_abs_le_interpolation_height P Q D hPdeg (hQdeg ▸ hBdeg) H hH hP hQ
    have hpowers : (K * H ^ E) ^ δ = K ^ δ * H ^ ε := by
      rw [Real.mul_rpow hK.le (pow_nonneg (zero_le_one.trans hH) _),
        ← Real.rpow_natCast_mul (zero_le_one.trans hH)]
      congr 1
      dsimp [δ]
      rw [mul_div_cancel₀ _ hE.ne']
    calc
      (S.card : ℝ) ≤ ((2 * Q.natDegree : ℕ) : ℝ) *
          ((P.resultant Q).natAbs.divisors.card : ℝ) := by exact_mod_cast hτ
      _ ≤ ((2 * D : ℕ) : ℝ) * (c * (((P.resultant Q).natAbs : ℝ) ^ δ)) := by
        apply mul_le_mul
        · exact_mod_cast Nat.mul_le_mul_left 2 (hQdeg ▸ hBdeg)
        · exact hdiv _
        · positivity
        · positivity
      _ ≤ ((2 * D : ℕ) : ℝ) * (c * ((K * H ^ E) ^ δ)) := by
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (Nat.cast_nonneg _) hR hδ.le) hc.le) h2D.le
      _ = (((2 * D : ℕ) : ℝ) * c * K ^ δ) * H ^ ε := by rw [hpowers]; ring
      _ ≤ C * H ^ ε := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        dsimp [C]
        linarith
  · have hsmall : (S.card : ℝ) ≤ (2 * D : ℕ) := by exact_mod_cast (by omega : S.card ≤ 2 * D)
    calc
      (S.card : ℝ) ≤ (2 * D : ℕ) := hsmall
      _ ≤ ((2 * D : ℕ) : ℝ) * H ^ ε := le_mul_of_one_le_right h2D.le hHε
      _ ≤ C * H ^ ε := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        dsimp [C]
        have hnonneg : 0 ≤ ((2 * D : ℕ) : ℝ) * c * K ^ δ := by positivity
        linarith

theorem rational_integer_values_uniform (D : ℕ) (hD : 0 < D)
    (a b C₀ : ℝ) (ha : 0 < a) (_hb : 0 < b) (_hC₀ : 0 < C₀)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A B : ℂ[X]), IsCoprime A B →
      0 < B.natDegree → A.natDegree ≤ D → B.natDegree ≤ D →
      ∀ (S : Finset ℤ) (v : ℤ → ℤ) (X : ℝ), 2 ≤ X →
      (∀ s ∈ S, A.eval (s : ℂ) = (v s : ℂ) * B.eval (s : ℂ)) →
      (∀ s ∈ S, |(s : ℝ)| ≤ C₀ * X ^ a) →
      (∀ s ∈ S, |(v s : ℝ)| ≤ C₀ * X ^ b) →
      (S.card : ℝ) ≤ C * X ^ ε := by
  let M := max a b
  have hM : 0 < M := lt_of_lt_of_le ha (le_max_left _ _)
  let K := max 1 C₀
  have hK : 1 ≤ K := le_max_left _ _
  let δ := ε / M
  have hδ : 0 < δ := div_pos hε hM
  obtain ⟨c, hc, h⟩ := rational_values_card_le_rpow D hD δ hδ
  refine ⟨c * K ^ δ, by positivity, ?_⟩
  intro A B hcop hBpos hAdeg hBdeg S v X hX heval hsX hvX
  have hX1 : 1 ≤ X := by linarith
  have hX0 : 0 ≤ X := by linarith
  have hXM : 1 ≤ X ^ M := Real.one_le_rpow hX1 hM.le
  have hH : 1 ≤ K * X ^ M := one_le_mul_of_one_le_of_one_le hK hXM
  have hbound (c₁ : ℝ) (hc₁ : c₁ ≤ M) : C₀ * X ^ c₁ ≤ K * X ^ M := by
    exact mul_le_mul (le_max_right _ _) (Real.rpow_le_rpow_of_exponent_le hX1 hc₁)
      (by positivity) (zero_le_one.trans hK)
  have hh := h A B hcop hBpos hAdeg hBdeg S v (K * X ^ M) hH heval
    (fun s hs => (hsX s hs).trans (hbound a (le_max_left _ _)))
    (fun s hs => (hvX s hs).trans (hbound b (le_max_right _ _)))
  have hp : (K * X ^ M) ^ δ = K ^ δ * X ^ ε := by
    rw [Real.mul_rpow (zero_le_one.trans hK) (Real.rpow_nonneg hX0 _),
      ← Real.rpow_mul hX0]
    congr 1
    dsimp [δ]
    rw [mul_div_cancel₀ _ hM.ne']
  simpa only [hp, mul_assoc] using hh

end QuarticPowerFree.ComplexValues

end OAI
end

section
-- module Solutions.OAIB3_Qpf.PowerFree_CurveAlternatives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace QuarticPowerFree
open MvPolynomial
open scoped BigOperators Classical

theorem algebraic_coordinate_constant {K A : Type*} [Field K] [IsAlgClosed K]
    [CommRing A] [IsDomain A] [Algebra K A] (x : A) (hx : IsAlgebraic K x) :
    ∃ c : K, algebraMap K A c = x := by
  have hi := hx.isIntegral
  have hd := IsAlgClosed.degree_eq_one_of_irreducible K (minpoly.irreducible hi)
  have he := minpoly.aeval K x
  rw [Polynomial.eq_X_add_C_of_degree_eq_one hd,
    (minpoly.monic hi).leadingCoeff, Polynomial.C_1, one_mul,
    Polynomial.aeval_add, Polynomial.aeval_X, Polynomial.aeval_C,
    add_eq_zero_iff_eq_neg] at he
  exact ⟨-(minpoly K x).coeff 0, by rw [map_neg]; exact he.symm⟩

theorem curve_coordinate_relation {n : ℕ} {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    (hI : affineDimension I ≤ 1) (x y : Fin n)
    (hx : Transcendental K (Ideal.Quotient.mk I (X x))) :
    ∃ q : MvPolynomial (Fin 2) K, Irreducible q ∧ q.degreeOf 0 ≠ 0 ∧
      (q.totalDegree:ℚ) ≤ affineDegree I ∧
      (∀ p, Ideal.Quotient.mk I (rename ![y,x] p) = 0 ↔ q ∣ p) := by
  have hind : AlgebraicIndependent K
      (fun a : Fin 1 => Ideal.Quotient.mk I (X (![y,x] a.succ))) := by
    apply algebraicIndependent_unique_type_iff.mpr
    simpa using hx
  have hdim : affineDimension I = 1 := by
    have htr := hilbert_natDegree_eq_trdeg I (coordinateHilbert I) (coordinateHilbert_eventually I)
    have hh := hind.lift_cardinalMk_le_trdeg
    rw [← htr] at hh
    have hl : 1 ≤ affineDimension I := by simpa [affineDimension] using hh
    omega
  obtain ⟨q,hq,hd,hb,hker⟩ := bounded_projection_relation I (coordinateHilbert I)
    hI (coordinateHilbert_eventually I) ![y,x] hind
  refine ⟨q,hq,hd,?_,hker⟩
  simpa only [affineDegree,hdim] using hb

theorem binaryPolynomialEquiv_eval {K A : Type*} [CommSemiring K] [CommSemiring A]
    (f : K →+* A) (x y : A) (q : MvPolynomial (Fin 2) K) :
    Polynomial.eval₂ (Polynomial.eval₂RingHom f x) y (binaryPolynomialEquiv K q) =
      MvPolynomial.eval₂ f ![y,x] q := by
  let e : MvPolynomial (Fin 2) K →+* A :=
    (Polynomial.eval₂RingHom (Polynomial.eval₂RingHom f x) y).comp
      (binaryPolynomialEquiv K).toRingHom
  have he : e = MvPolynomial.eval₂Hom f ![y,x] := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [e,binaryPolynomialEquiv,finSuccEquiv_apply,uniqueAlgEquiv]
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [e,binaryPolynomialEquiv,finSuccEquiv_apply,uniqueAlgEquiv]
      · simp [e,binaryPolynomialEquiv,finSuccEquiv_apply,uniqueAlgEquiv]
  exact congrArg (fun g : MvPolynomial (Fin 2) K →+* A => g q) he

theorem uniquePolynomial_natDegree_le {K : Type*} [CommSemiring K]
    (q : MvPolynomial (Fin 1) K) : (uniqueAlgEquiv K (Fin 1) q).natDegree ≤ q.totalDegree := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro m hm
  rw [coeff_uniqueAlgEquiv]
  apply coeff_eq_zero_of_totalDegree_lt
  change q.totalDegree < (Finsupp.single (default : Fin 1) m).sum (fun _ e => e)
  rw [Finsupp.sum_single_index (by simp)]
  exact hm

theorem binaryPolynomial_coeff_degree {K : Type*} [CommSemiring K]
    (q : MvPolynomial (Fin 2) K) (i : ℕ) :
    ((binaryPolynomialEquiv K q).coeff i).natDegree ≤ q.totalDegree := by
  simp only [binaryPolynomialEquiv,AlgEquiv.trans_apply,Polynomial.coe_mapAlgEquiv,Polynomial.coeff_map]

  by_cases hz : (finSuccEquiv K 1 q).coeff i = 0
  · simp [hz]
  · exact (uniquePolynomial_natDegree_le _).trans
      (Nat.le_sub_of_add_le (totalDegree_coeff_finSuccEquiv_add_le q i hz) |>.trans (Nat.sub_le _ _))

theorem linear_projection_rational {K : Type*} [Field K]
    (q : MvPolynomial (Fin 2) K) (hq : Irreducible q) (hd : q.degreeOf 0 = 1) :
    ∃ A B : Polynomial K, IsCoprime A B ∧ B ≠ 0 ∧ A.natDegree ≤ q.totalDegree ∧
      B.natDegree ≤ q.totalDegree ∧
      ∀ {S : Type*} [CommRing S] (f : K →+* S) (x y : S),
        MvPolynomial.eval₂ f ![y,x] q = 0 ↔
          A.eval₂ f x = y * B.eval₂ f x := by
  let p := binaryPolynomialEquiv K q
  have hp : Irreducible p := (MulEquiv.irreducible_iff (binaryPolynomialEquiv K)).mpr hq
  have hpd : p.natDegree = 1 := (binaryPolynomialEquiv_natDegree q).trans hd
  have he : p = Polynomial.C (p.coeff 1) * Polynomial.X + Polynomial.C (p.coeff 0) := by
    simpa only [hpd] using Polynomial.eq_X_add_C_of_degree_le_one (Polynomial.degree_le_of_natDegree_le (le_of_eq hpd))
  have hbn : p.coeff 1 ≠ 0 := by
    rw [← hpd]
    exact Polynomial.leadingCoeff_ne_zero.mpr hp.ne_zero
  have prim := hp.isPrimitive (by rw [hpd]; decide)
  have hcop : IsCoprime (p.coeff 0) (p.coeff 1) := by
    apply IsRelPrime.isCoprime
    intro d hd0 hd1
    apply Polynomial.isPrimitive_iff_isUnit_of_C_dvd.mp prim
    rw [Polynomial.C_dvd_iff_dvd_coeff]
    intro i
    by_cases hi : i = 0
    · subst i; exact hd0
    by_cases hi1 : i = 1
    · subst i; exact hd1
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
    exact dvd_zero _
  refine ⟨-p.coeff 0,p.coeff 1,hcop.neg_left,hbn,?_,binaryPolynomial_coeff_degree q 1,?_⟩
  · simpa using binaryPolynomial_coeff_degree q 0
  · intro S _ f x y
    rw [← binaryPolynomialEquiv_eval,show binaryPolynomialEquiv K q = p from rfl]
    conv_lhs => rw [he]
    simp only [Polynomial.eval₂_add,Polynomial.eval₂_mul,Polynomial.eval₂_C,
      Polynomial.eval₂_X,Polynomial.coe_eval₂RingHom,Polynomial.eval₂_neg]
    constructor <;> intro h <;> linear_combination -h

theorem binaryStripExponent_injective (M : ℕ) :
    Function.Injective (binaryStripExponent (M := M)) := by
  intro i j h
  have h0 := congrArg (fun a : Fin 2 →₀ ℕ => a 0) h
  have h1 := congrArg (fun a : Fin 2 →₀ ℕ => a 1) h
  simp only [binaryStripExponent,Finsupp.coe_add,Pi.add_apply,Finsupp.single_eq_same,
    Finsupp.single_eq_of_ne (show (0:Fin 2) ≠ 1 by decide),
    Finsupp.single_eq_of_ne (show (1:Fin 2) ≠ 0 by decide),add_zero,zero_add] at h0 h1
  exact Prod.ext (Fin.ext h0) (Fin.ext h1)

theorem projection_strip_independent {n : ℕ} {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) (x y : Fin n)
    (q : MvPolynomial (Fin 2) K) (hq : 2 ≤ q.degreeOf 0)
    (hker : ∀ p, Ideal.Quotient.mk I (rename ![y,x] p) = 0 ↔ q ∣ p) (M : ℕ) :
    LinearIndependent K (fun i : Fin 2 × Fin (M+1) =>
      Ideal.Quotient.mk I (rename ![y,x] (monomial (binaryStripExponent i) (1:K)))) := by
  classical
  apply linearIndependent_iff'.mpr
  intro s c hc i hi
  let p : MvPolynomial (Fin 2) K := ∑ j ∈ s, c j • monomial (binaryStripExponent j) 1
  have hpker : Ideal.Quotient.mk I (rename ![y,x] p) = 0 := by
    change (Ideal.Quotient.mkₐ K I) (rename ![y,x] p) = 0
    simpa only [p,map_sum,map_smul,Ideal.Quotient.mkₐ_eq_mk] using hc
  have hpdeg : p.degreeOf 0 ≤ 1 := by
    apply (degreeOf_sum_le 0 s _).trans
    apply Finset.sup_le
    intro j _
    rw [smul_monomial,smul_eq_mul,mul_one]
    by_cases hz : c j = 0
    · simp [hz]
    · rw [degreeOf_monomial_eq _ _ hz]
      simp only [binaryStripExponent,Finsupp.coe_add,Pi.add_apply,Finsupp.single_eq_same,
        Finsupp.single_eq_of_ne (show (0:Fin 2) ≠ 1 by decide),add_zero]
      omega
  have hp : p = 0 := by
    by_contra hp
    obtain ⟨t,ht⟩ := (hker p).mp hpker
    have hmul : q*t ≠ 0 := ht ▸ hp
    have hd := degreeOf_mul_eq (left_ne_zero_of_mul hmul) (right_ne_zero_of_mul hmul) (n := 0)
    rw [← ht] at hd
    omega
  have hl := (basisMonomials (Fin 2) K).linearIndependent.comp
    (binaryStripExponent (M := M)) (binaryStripExponent_injective M)
  simp only [coe_basisMonomials,Function.comp_def] at hl
  exact linearIndependent_iff'.mp hl s c hp i hi

theorem coordinate_power_mem_weighted {n : ℕ} {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) (ω : Fin n → ℝ) (hω : ∀ j, 0 < ω j)
    (x y : Fin n) (a b : ℕ) (T : ℝ) (hb : ω y*a+ω x*b ≤ T) :
    Ideal.Quotient.mk I ((X y)^a*(X x)^b) ∈ weightedFunctions I ω T := by
  classical
  have hweight : monomialWeight ω (Finsupp.single y a + Finsupp.single x b) = ω y*a+ω x*b := by
    simp only [monomialWeight,Finsupp.coe_add,Pi.add_apply,Nat.cast_add,mul_add,Finset.sum_add_distrib]
    simp [Finsupp.single_apply]
  rw [X_pow_eq_monomial,X_pow_eq_monomial,monomial_mul_monomial,one_mul]
  apply Submodule.subset_span
  refine ⟨_,(mem_weightedMonomials ω hω T _).mpr (hweight ▸ hb),rfl⟩

theorem projection_strip_hilbert {n : ℕ} {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) (ω : Fin n → ℝ) (hω : ∀ j, 0 < ω j)
    (x y : Fin n) (hx : ω x = 1)
    (q : MvPolynomial (Fin 2) K) (hq : 2 ≤ q.degreeOf 0)
    (hker : ∀ p, Ideal.Quotient.mk I (rename ![y,x] p) = 0 ↔ q ∣ p)
    (M : ℕ) (T : ℝ) (hT : (M:ℝ)+ω y ≤ T) :
    2*(M+1) ≤ weightedHilbert I ω T := by
  classical
  let v := fun i : Fin 2 × Fin (M+1) =>
    Ideal.Quotient.mk I (rename ![y,x] (monomial (binaryStripExponent i) (1:K)))
  have hv (i : Fin 2 × Fin (M+1)) : v i ∈ weightedFunctions I ω T := by
    have he : rename ![y,x] (monomial (binaryStripExponent i) (1:K)) = (X y)^i.1.val*(X x)^i.2.val := by
      rw [binaryStripExponent,← one_mul (1:K),← monomial_mul_monomial,← X_pow_eq_monomial,← X_pow_eq_monomial]
      simp
    dsimp only [v]
    rw [he]
    apply coordinate_power_mem_weighted I ω hω x y _ _ T
    rw [hx,one_mul]
    have h1 : (i.1.val:ℝ) ≤ 1 := by exact_mod_cast (show i.1.val ≤ 1 by omega)
    have h2 : (i.2.val:ℝ) ≤ M := by exact_mod_cast (show i.2.val ≤ M by omega)
    have hh := mul_le_mul_of_nonneg_left h1 (hω y).le
    linarith
  let u : (Fin 2 × Fin (M+1)) → weightedFunctions I ω T := fun i => ⟨v i,hv i⟩
  have hu : LinearIndependent K u := LinearIndependent.of_comp (weightedFunctions I ω T).subtype
    (projection_strip_independent I x y q hq hker M)
  simpa only [Fintype.card_prod,Fintype.card_fin,weightedHilbert] using hu.fintype_card_le_finrank

theorem projection_curve_hilbert_gain {n : ℕ} {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) (ω : Fin n → ℝ) (hω : ∀ j, 0 < ω j)
    (x y : Fin n) (hx : ω x = 1)
    (q : MvPolynomial (Fin 2) K) (hq : 2 ≤ q.degreeOf 0)
    (hker : ∀ p, Ideal.Quotient.mk I (rename ![y,x] p) = 0 ↔ q ∣ p) :
    ∀ T : ℝ, 0 ≤ T → 2*T-2*(ω y+1) ≤ weightedHilbert I ω T := by
  intro T _
  by_cases hT : ω y ≤ T
  · have hf : (⌊T-ω y⌋₊:ℝ)+ω y ≤ T := by linarith [Nat.floor_le (sub_nonneg.mpr hT)]
    have hb := projection_strip_hilbert I ω hω x y hx q hq hker ⌊T-ω y⌋₊ T hf
    have hbr : 2*((⌊T-ω y⌋₊:ℝ)+1) ≤ weightedHilbert I ω T := by exact_mod_cast hb
    have hl := Nat.lt_floor_add_one (T-ω y)
    linarith
  · have hh : (0:ℝ) ≤ weightedHilbert I ω T := Nat.cast_nonneg _
    linarith

theorem polynomial_of_constant_denominator {K R : Type*} [Field K] [CommRing R]
    (φ : K →+* R) (x y : R) (A B : Polynomial K) (hB : B ≠ 0)
    (hdeg : B.natDegree = 0) (he : A.eval₂ φ x = y*B.eval₂ φ x) :
    ∃ P : Polynomial K, P.eval₂ φ x = y := by
  have hBc : B = Polynomial.C (B.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hdeg
  have hb : B.coeff 0 ≠ 0 := by intro h; apply hB; rw [hBc,h,Polynomial.C_0]
  refine ⟨Polynomial.C (B.coeff 0)⁻¹ * A,?_⟩
  have hev : B.eval₂ φ x = φ (B.coeff 0) := by
    conv_lhs => rw [hBc]
    rw [Polynomial.eval₂_C]
  rw [Polynomial.eval₂_mul,Polynomial.eval₂_C,he,hev,← mul_assoc,mul_comm (φ _),mul_assoc,
    ← map_mul,inv_mul_cancel₀ hb,map_one,mul_one]

theorem squarefree_surface_polynomial_coordinate {K R : Type*} [Field K]
    [CommRing R] [Algebra K R] (f Y Z : Polynomial K) (k : ℕ) (hk : 2 ≤ k)
    (hf : Squarefree f) (x y z : R) (hx : Transcendental K x)
    (hY : Polynomial.aeval x Y = y) (hZ : Polynomial.aeval x Z = z)
    (he : Polynomial.aeval x f = y*z^k) :
    ∃ c : K, algebraMap K R c = z := by
  have hid : f = Y*Z^k := (transcendental_iff_injective.mp hx) (by simpa only [map_mul,map_pow,hY,hZ] using he)
  have hu : IsUnit Z := by
    by_contra hn
    have hs : Squarefree (Z^k) := hf.squarefree_of_dvd ⟨Y,by rw [hid]; ring⟩
    have hh := hs.eq_zero_or_one_of_pow_of_not_isUnit hn
    omega
  have hz := Polynomial.eq_C_of_natDegree_eq_zero (Polynomial.natDegree_eq_zero_of_isUnit hu)
  refine ⟨Z.coeff 0,?_⟩
  rw [← hZ]
  conv_rhs => rw [hz]
  rw [Polynomial.aeval_C]

theorem projection_equation_quotient {n : ℕ} {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) (x y : Fin n)
    (q : MvPolynomial (Fin 2) K)
    (hq : Ideal.Quotient.mk I (rename ![y,x] q) = 0) :
    MvPolynomial.eval₂ (algebraMap K (MvPolynomial (Fin n) K ⧸ I))
      ![Ideal.Quotient.mk I (X y),Ideal.Quotient.mk I (X x)] q = 0 := by
  have he : MvPolynomial.aeval ![Ideal.Quotient.mk I (X y),Ideal.Quotient.mk I (X x)] =
      (Ideal.Quotient.mkₐ K I).comp (rename ![y,x]) := by
    ext i
    fin_cases i <;> simp
  change (MvPolynomial.aeval _) q = 0
  rw [he]
  exact hq

theorem direct_curve_alternative (I : Ideal (MvPolynomial (Fin 3) ℂ)) [I.IsPrime]
    (hI : affineDimension I ≤ 1) (e : ℕ) (hdeg : affineDegree I ≤ e)
    (ω : Fin 3 → ℝ) (hω : ∀ j, 0 < ω j) (hω0 : ω 0 = 1)
    (f : Polynomial ℂ) (hf : Squarefree f) (k : ℕ) (hk : 2 ≤ k)
    (he : Polynomial.aeval (Ideal.Quotient.mk I (X 0)) f =
      Ideal.Quotient.mk I (X 1) * (Ideal.Quotient.mk I (X 2))^k) :
    (∃ c : ℂ, algebraMap ℂ (MvPolynomial (Fin 3) ℂ ⧸ I) c = Ideal.Quotient.mk I (X 0)) ∨
    (∃ (j : Fin 3) (A B : Polynomial ℂ), (j = 1 ∨ j = 2) ∧ IsCoprime A B ∧
      0 < B.natDegree ∧ A.natDegree ≤ e ∧ B.natDegree ≤ e ∧
      Polynomial.aeval (Ideal.Quotient.mk I (X 0)) A =
        Ideal.Quotient.mk I (X j) * Polynomial.aeval (Ideal.Quotient.mk I (X 0)) B) ∨
    (∃ c : ℂ, algebraMap ℂ (MvPolynomial (Fin 3) ℂ ⧸ I) c = Ideal.Quotient.mk I (X 2)) ∨
    (∀ T : ℝ, 1 ≤ T → 2*T-2*(ω 1+ω 2+1) ≤ weightedHilbert I ω T) := by
  by_cases hx : IsAlgebraic ℂ (Ideal.Quotient.mk I (X 0))
  · exact Or.inl (algebraic_coordinate_constant _ hx)
  have relations (j : Fin 3) := curve_coordinate_relation I hI 0 j hx
  obtain ⟨qY,hqY,hdY,hbY,hkerY⟩ := relations 1
  obtain ⟨qZ,hqZ,hdZ,hbZ,hkerZ⟩ := relations 2
  have hbY' : qY.totalDegree ≤ e := by exact_mod_cast hbY.trans hdeg
  have hbZ' : qZ.totalDegree ≤ e := by exact_mod_cast hbZ.trans hdeg
  by_cases h2Y : 2 ≤ qY.degreeOf 0
  · right; right; right
    intro T hT
    have hh := projection_curve_hilbert_gain I ω hω 0 1 hω0 qY h2Y hkerY T (by linarith)
    linarith [hω 2]
  by_cases h2Z : 2 ≤ qZ.degreeOf 0
  · right; right; right
    intro T hT
    have hh := projection_curve_hilbert_gain I ω hω 0 2 hω0 qZ h2Z hkerZ T (by linarith)
    linarith [hω 1]
  obtain ⟨AY,BY,hcopY,hBY,hAYb,hBYb,hY⟩ := linear_projection_rational qY hqY (by omega)
  obtain ⟨AZ,BZ,hcopZ,hBZ,hAZb,hBZb,hZ⟩ := linear_projection_rational qZ hqZ (by omega)
  have heY := (hY (algebraMap ℂ (MvPolynomial (Fin 3) ℂ ⧸ I))
    (Ideal.Quotient.mk I (X 0)) (Ideal.Quotient.mk I (X 1))).mp
    (projection_equation_quotient I 0 1 qY ((hkerY qY).mpr (dvd_refl _)))
  have heZ := (hZ (algebraMap ℂ (MvPolynomial (Fin 3) ℂ ⧸ I))
    (Ideal.Quotient.mk I (X 0)) (Ideal.Quotient.mk I (X 2))).mp
    (projection_equation_quotient I 0 2 qZ ((hkerZ qZ).mpr (dvd_refl _)))
  by_cases hYpos : 0 < BY.natDegree
  · exact Or.inr (Or.inl ⟨1,AY,BY,Or.inl rfl,hcopY,hYpos,hAYb.trans hbY',hBYb.trans hbY',heY⟩)
  by_cases hZpos : 0 < BZ.natDegree
  · exact Or.inr (Or.inl ⟨2,AZ,BZ,Or.inr rfl,hcopZ,hZpos,hAZb.trans hbZ',hBZb.trans hbZ',heZ⟩)
  obtain ⟨Y,hY⟩ := polynomial_of_constant_denominator (algebraMap ℂ (MvPolynomial (Fin 3) ℂ ⧸ I))
    _ _ AY BY hBY (by omega) heY
  obtain ⟨Z,hZ⟩ := polynomial_of_constant_denominator (algebraMap ℂ (MvPolynomial (Fin 3) ℂ ⧸ I))
    _ _ AZ BZ hBZ (by omega) heZ
  exact Or.inr (Or.inr (Or.inl (squarefree_surface_polynomial_coordinate f Y Z k hk hf _ _ _ hx hY hZ he)))

end QuarticPowerFree

end OAI
end

section
-- module Solutions.OAIB3_Qpf.PowerFree_SelectedPrimes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace QuarticPowerFree

section
open Polynomial
open scoped BigOperators Classical

theorem primitive_map_zmod_ne_zero (f : Polynomial ℤ) (hf : f.IsPrimitive)
    (p : ℕ) (hp : p.Prime) : f.map (Int.castRingHom (ZMod p)) ≠ 0 := by
  intro hz
  have hd : Polynomial.C (p:ℤ) ∣ f := by
    rw [Polynomial.C_dvd_iff_dvd_coeff]
    intro i
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
    have hh := congrArg (fun g : Polynomial (ZMod p) => g.coeff i) hz
    simpa using hh
  have hu := Polynomial.isPrimitive_iff_isUnit_of_C_dvd.mp hf (p:ℤ) hd
  have he := Int.isUnit_iff_natAbs_eq.mp hu
  exact hp.ne_one (by simpa using he)

theorem selected_constant_prime_count (f : Polynomial ℤ) (hf : f.IsPrimitive)
    (p : ℕ) (hp : p.Prime) (X : ℝ) (hXp : X < p) (S : Finset (Fin 3 → ℤ))
    (hinj : Set.InjOn (fun z : Fin 3 → ℤ => z 0) (S:Set (Fin 3 → ℤ)))
    (hrange : ∀ z ∈ S, X < (z 0:ℝ) ∧ (z 0:ℝ) ≤ 2*X)
    (hroot : ∀ z ∈ S, (p:ℤ) ∣ f.eval (z 0)) : S.card ≤ f.natDegree := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  let F := f.map (Int.castRingHom (ZMod p))
  have hF : F ≠ 0 := primitive_map_zmod_ne_zero f hf p hp
  have hmap : Set.MapsTo (fun z : Fin 3 → ℤ => (z 0 : ZMod p)) (S:Set _) (F.roots.toFinset:Set _) := by
    intro z hz
    rw [Finset.mem_coe,Multiset.mem_toFinset,Polynomial.mem_roots hF]
    change F.eval (z 0 : ZMod p) = 0
    rw [show F = f.map (Int.castRingHom (ZMod p)) from rfl,Polynomial.eval_map]
    change f.eval₂ (Int.castRingHom (ZMod p)) ((Int.castRingHom (ZMod p)) (z 0)) = 0
    rw [Polynomial.eval₂_at_apply]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr (hroot z hz)
  have hmodinj : Set.InjOn (fun z : Fin 3 → ℤ => (z 0 : ZMod p)) (S:Set _) := by
    intro u hu v hv huv
    apply hinj hu hv
    have hd := (ZMod.intCast_eq_intCast_iff_dvd_sub (u 0) (v 0) p).mp huv
    obtain ⟨hu1,hu2⟩ := hrange u hu
    obtain ⟨hv1,hv2⟩ := hrange v hv
    have hh : |((v 0-u 0:ℤ):ℝ)| < (p:ℝ) := by
      push_cast
      rw [abs_lt]
      constructor <;> linarith
    have hh' : (v 0-u 0).natAbs < p := by
      exact_mod_cast (show ((v 0-u 0).natAbs:ℝ) < p by simpa only [Nat.cast_natAbs,Int.cast_abs] using hh)
    have he : v 0-u 0 = 0 := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hd (by simpa using hh')
    exact (sub_eq_zero.mp he).symm
  calc
    S.card ≤ F.roots.toFinset.card := Finset.card_le_card_of_injOn _ hmap hmodinj
    _ ≤ F.roots.card := Multiset.toFinset_card_le _
    _ ≤ F.natDegree := Polynomial.card_roots' _
    _ ≤ f.natDegree := Polynomial.natDegree_map_le

end
open MvPolynomial
open scoped BigOperators Classical

theorem coordinate_constant_at_point {n : ℕ} {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) (z : Fin n → ℤ) (hz : PointOn I z) (j : Fin n)
    (c : K) (hc : algebraMap K (MvPolynomial (Fin n) K ⧸ I) c = Ideal.Quotient.mk I (X j)) :
    (z j:K) = c := by
  have he := congrArg (pointEvaluation I z hz) hc
  simpa only [AlgHom.commutes,Algebra.algebraMap_self, RingHom.id_apply,pointEvaluation_X] using he.symm

theorem rational_coordinate_at_point {n : ℕ} {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) (z : Fin n → ℤ) (hz : PointOn I z) (x j : Fin n)
    (A B : Polynomial K)
    (he : Polynomial.aeval (Ideal.Quotient.mk I (X x)) A =
      Ideal.Quotient.mk I (X j)*Polynomial.aeval (Ideal.Quotient.mk I (X x)) B) :
    A.eval (z x:K) = (z j:K)*B.eval (z x:K) := by
  have hh := congrArg (pointEvaluation I z hz) he
  rw [map_mul,← Polynomial.aeval_algHom_apply,← Polynomial.aeval_algHom_apply] at hh
  simpa only [pointEvaluation_X,Polynomial.aeval_def,
    Algebra.algebraMap_self,Polynomial.eval₂_id] using hh

theorem rational_selected_count (D : ℕ) (hD : 0 < D) (ω : Fin 3 → ℝ)
    (hω : ∀ i, 0 < ω i) (hω0 : ω 0 = 1) (Cbox : ℝ) (hCbox : 0 < Cbox)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (X : ℝ), 2 ≤ X → ∀ (S : Finset (Fin 3 → ℤ)),
      Set.InjOn (fun z : Fin 3 → ℤ => z 0) (S:Set _) →
      (∀ z ∈ S, ∀ i, |(z i:ℝ)| ≤ Cbox*X^(ω i)) →
      ∀ (j : Fin 3) (A B : Polynomial ℂ), (j = 1 ∨ j = 2) → IsCoprime A B →
      0 < B.natDegree → A.natDegree ≤ D → B.natDegree ≤ D →
      (∀ z ∈ S, A.eval (z 0:ℂ) = (z j:ℂ)*B.eval (z 0:ℂ)) →
      (S.card:ℝ) ≤ C*X^ε := by
  classical
  obtain ⟨C,hC,hbound⟩ := ComplexValues.rational_integer_values_uniform D hD 1 (max (ω 1) (ω 2)) Cbox
    (by norm_num) (lt_of_lt_of_le (hω 1) (le_max_left _ _)) hCbox ε hε
  refine ⟨C,hC,?_⟩
  intro X hX S hinj hbox j A B hj hcop hB hAD hBD he
  let v : ℤ → ℤ := fun s => if hs : ∃ z ∈ S, z 0 = s then hs.choose j else 0
  have hv (z) (hz : z ∈ S) : v (z 0) = z j := by
    have hs : ∃ u ∈ S, u 0 = z 0 := ⟨z,hz,rfl⟩
    dsimp only [v]
    rw [dite_eq_left hs]
    have hu := hinj hs.choose_spec.1 hz hs.choose_spec.2
    exact congrArg (fun u => u j) hu
  have hcard : (S.image fun z => z 0).card = S.card := Finset.card_image_of_injOn hinj
  rw [← hcard]
  apply hbound A B hcop hB hAD hBD _ v X hX
  · intro s hs
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hs
    rw [hv z hz]
    exact he z hz
  · intro s hs
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hs
    simpa only [hω0] using hbox z hz 0
  · intro s hs
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hs
    rw [hv z hz]
    apply (hbox z hz j).trans
    gcongr
    · linarith
    · rcases hj with rfl | rfl
      · exact le_max_left _ _
      · exact le_max_right _ _

theorem direct_curve_count_or_hilbert (f : Polynomial ℤ) (hf : f.IsPrimitive)
    (hsq : Squarefree (f.map (Int.castRingHom ℂ))) (k : ℕ) (hk : 2 ≤ k)
    (e : ℕ) (ω : Fin 3 → ℝ) (hω : ∀ j, 0 < ω j) (hω0 : ω 0 = 1)
    (Cbox : ℝ) (hCbox : 0 < Cbox) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (X : ℝ), 2 ≤ X → ∀ (S : Finset (Fin 3 → ℤ)),
      Set.InjOn (fun z : Fin 3 → ℤ => z 0) (S:Set _) →
      (∀ z ∈ S, ∀ j, |(z j:ℝ)| ≤ Cbox*X^(ω j)) →
      (∀ z ∈ S, X < (z 0:ℝ) ∧ (z 0:ℝ) ≤ 2*X) →
      (∀ z ∈ S, ∃ p : ℕ, p.Prime ∧ z 2 = p ∧ X < p ∧ (p:ℤ) ∣ f.eval (z 0)) →
      ∀ (I : Ideal (MvPolynomial (Fin 3) ℂ)), I.IsPrime →
      affineDimension I ≤ 1 → affineDegree I ≤ e →
      (∀ z ∈ S, PointOn I z) →
      (Polynomial.aeval (Ideal.Quotient.mk I (MvPolynomial.X 0)) (f.map (Int.castRingHom ℂ)) =
        Ideal.Quotient.mk I (MvPolynomial.X 1)*(Ideal.Quotient.mk I (MvPolynomial.X 2))^k) →
      (S.card:ℝ) ≤ C*X^ε ∨
        (∀ T : ℝ, 1 ≤ T → 2*T-2*(ω 1+ω 2+1) ≤ weightedHilbert I ω T) := by
  classical
  obtain ⟨Cr,hCr,hcount⟩ := rational_selected_count (e+1) (by omega) ω hω hω0 Cbox hCbox ε hε
  let C : ℝ := 1+Cr+f.natDegree
  have hC : 1 ≤ C := by dsimp [C]; linarith [Nat.cast_nonneg (α := ℝ) f.natDegree]
  refine ⟨C,hC,?_⟩
  intro X hX S hinj hbox hrange hselected I hI hdim hdeg hon he
  let : I.IsPrime := hI
  have hpow : 1 ≤ X^ε := Real.one_le_rpow (by linarith) hε.le
  have hsmall (a : ℕ) (ha : S.card ≤ a) (haC : (a:ℝ) ≤ C) : (S.card:ℝ) ≤ C*X^ε := by
    have ha' : (S.card:ℝ) ≤ (a:ℝ) := by exact_mod_cast ha
    exact ha'.trans (haC.trans (le_mul_of_one_le_right (zero_le_one.trans hC) hpow))
  rcases direct_curve_alternative I hdim e hdeg ω hω hω0 (f.map (Int.castRingHom ℂ)) hsq k hk he with
    ⟨c,hc⟩ | ⟨j,A,B,hj,hcop,hB,hAD,hBD,hrel⟩ | ⟨c,hc⟩ | hH
  · left
    apply hsmall 1 _ (by simpa using hC)
    apply Finset.card_le_one.mpr
    intro u hu v hv
    apply hinj hu hv
    apply Int.cast_injective (α := ℂ)
    exact (coordinate_constant_at_point I u (hon u hu) 0 c hc).trans
      (coordinate_constant_at_point I v (hon v hv) 0 c hc).symm
  · left
    have hC' : Cr ≤ C := by dsimp [C]; linarith [Nat.cast_nonneg (α := ℝ) f.natDegree]
    exact (hcount X hX S hinj hbox j A B hj hcop hB (by omega) (by omega)
      (fun z hz => rational_coordinate_at_point I z (hon z hz) 0 j A B hrel)).trans
      (mul_le_mul_of_nonneg_right hC' (Real.rpow_nonneg (by linarith) _))
  · left
    by_cases hn : S.Nonempty
    · obtain ⟨u,hu⟩ := hn
      obtain ⟨p,hp,hup,hXp,_⟩ := hselected u hu
      have hroot (z) (hz : z ∈ S) : (p:ℤ) ∣ f.eval (z 0) := by
        obtain ⟨q,hq,hzq,_,hroot⟩ := hselected z hz
        have heq : z 2 = u 2 := Int.cast_injective ((coordinate_constant_at_point I z (hon z hz) 2 c hc).trans
          (coordinate_constant_at_point I u (hon u hu) 2 c hc).symm)
        rw [hup,hzq] at heq
        have hqp : q = p := by exact_mod_cast heq
        simpa only [hqp] using hroot
      apply hsmall f.natDegree (selected_constant_prime_count f hf p hp X hXp S hinj hrange hroot)
      dsimp [C]
      linarith
    · have hz : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
      subst S
      simp only [Finset.card_empty,Nat.cast_zero]
      positivity
  · exact Or.inr hH

theorem directSurfaceEquiv_apply {K : Type*} [CommRing K] (f : Polynomial K) (k : ℕ) :
    directSurfaceEquiv K (directSurface f k) =
      Polynomial.C (-(X 1)^k) * Polynomial.X + Polynomial.C (Polynomial.eval₂ C (X 0) f) := by
  have he : directSurfaceEquiv K (Polynomial.eval₂ C (X 0) f) =
      Polynomial.C (Polynomial.eval₂ C (X 0) f) := by
    induction f using Polynomial.induction_on' with
    | add p q hp hq => simp only [Polynomial.eval₂_add,map_add,hp,hq]
    | monomial n a => simp [Polynomial.eval₂_monomial,mul_comm]
  simp only [directSurface,map_sub,he,map_mul,map_pow,directSurfaceEquiv_X1,directSurfaceEquiv_X2,
    Polynomial.C_neg]
  ring

theorem directSurface_coeff_relprime {K : Type*} [Field K]
    (f : Polynomial K) (hf : f ≠ 0) (k : ℕ) :
    IsRelPrime (-(X (1:Fin 2))^k) (Polynomial.eval₂ C (X 0) f) := by
  have hn : ¬ (X (1:Fin 2) : MvPolynomial (Fin 2) K) ∣ Polynomial.eval₂ C (X 0) f := by
    intro hd
    let ψ : MvPolynomial (Fin 2) K →+* Polynomial K := eval₂Hom Polynomial.C ![Polynomial.X,0]
    have he : ψ (Polynomial.eval₂ C (X 0) f) = f := by
      clear hf hd
      induction f using Polynomial.induction_on' with
      | add p q hp hq => simp only [Polynomial.eval₂_add,map_add,hp,hq]
      | monomial n a => simp [Polynomial.eval₂_monomial,ψ,Polynomial.C_mul_X_pow_eq_monomial]
    have hh := map_dvd ψ hd
    apply hf
    simpa only [ψ,eval₂Hom_X',Matrix.cons_val_one,Matrix.cons_val_zero,zero_dvd_iff,he] using hh
  have hp := (MvPolynomial.X_prime (i := (1:Fin 2)) (R := K)).irreducible
  exact ((hp.isRelPrime_iff_not_dvd.mpr hn).pow_left).neg_left

theorem directSurface_irreducible {K : Type*} [Field K]
    (f : Polynomial K) (hf : f ≠ 0) (k : ℕ) : Irreducible (directSurface f k) := by
  apply (MulEquiv.irreducible_iff (directSurfaceEquiv K)).mp
  rw [directSurfaceEquiv_apply]
  exact Polynomial.irreducible_C_mul_X_add_C (neg_ne_zero.mpr (pow_ne_zero _ (X_ne_zero _)))
    (directSurface_coeff_relprime f hf k)

theorem coeff_single_eval₂_C_X {σ K : Type*} [CommSemiring K] (i : σ)
    (f : Polynomial K) (n : ℕ) :
    (Polynomial.eval₂ C (X i) f).coeff (Finsupp.single i n) = f.coeff n := by
  classical
  induction f using Polynomial.induction_on' with
  | add p q hp hq => simp only [Polynomial.eval₂_add,MvPolynomial.coeff_add,
      Finsupp.add_apply,Polynomial.coeff_add,hp,hq]
  | monomial m a =>
    simp [Polynomial.eval₂_monomial,C_mul_X_pow_eq_monomial,coeff_monomial,
      Polynomial.coeff_monomial,(Finsupp.single_injective i).eq_iff]

theorem directSurface_coeff_single {K : Type*} [CommRing K]
    (f : Polynomial K) (k n : ℕ) :
    (directSurface f k).coeff (Finsupp.single 0 n) = f.coeff n := by
  classical
  have hne : Finsupp.single (1:Fin 3) 1 + Finsupp.single 2 k ≠ Finsupp.single 0 n := by
    intro h
    have hh := congrArg (fun v : Fin 3 →₀ ℕ => v 1) h
    simp at hh
  rw [directSurface,coeff_sub,coeff_single_eval₂_C_X,X_pow_eq_monomial]
  rw [X,monomial_mul_monomial,one_mul,coeff_monomial,ite_eq_right hne,sub_zero]

theorem directSurface_weightedDegree_lower {K : Type*} [Field K]
    (f : Polynomial K) (hf : f ≠ 0) (k : ℕ) (w : Fin 3 → ℕ) :
    f.natDegree*w 0 ≤ weightedTotalDegree w (directSurface f k) := by
  have hm : Finsupp.single 0 f.natDegree ∈ (directSurface f k).support := by
    rw [mem_support_iff,directSurface_coeff_single]
    exact Polynomial.leadingCoeff_ne_zero.mpr hf
  have hh := Finset.le_sup (f := Finsupp.weight w) hm
  simpa only [weightedTotalDegree,Finsupp.weight_single,nsmul_eq_mul,Nat.cast_id] using hh

theorem totalDegree_pos_of_irreducible {σ K : Type*} [Field K]
    (F : MvPolynomial σ K) (hF : Irreducible F) : 0 < F.totalDegree := by
  by_contra hn
  have hd : F.totalDegree = 0 := by omega
  have he : F = C (F.coeff 0) := totalDegree_eq_zero_iff_eq_C.mp hd
  have hc : F.coeff 0 ≠ 0 := by intro hh; rw [he,hh,map_zero] at hF; exact hF.ne_zero rfl
  exact hF.not_isUnit (he ▸ (isUnit_iff_ne_zero.mpr hc).map C)

end QuarticPowerFree

end OAI
end

section
-- module Solutions.OAIB3_Qpf.PowerFree_SurfaceCounting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace QuarticPowerFree
open MvPolynomial
open scoped BigOperators Classical

theorem coordinateHilbert_hypersurface {n : ℕ} {K : Type*} [Field K]
    (F : MvPolynomial (Fin (n+1)) K) (hF : F ≠ 0) :
    coordinateHilbert (Ideal.span {F}) = hypersurfaceHilbertPolynomial n F.totalDegree := by
  apply polynomial_eq_of_eventually_nat_eval_eq
  filter_upwards [coordinateHilbert_eventually (Ideal.span {F}),
    Filter.eventually_ge_atTop F.totalDegree] with T he hT
  exact he.symm.trans (hypersurface_hilbert_polynomial F hF T hT)

theorem affineDimension_hypersurface {n : ℕ} {K : Type*} [Field K]
    (F : MvPolynomial (Fin (n+1)) K) (hF : F ≠ 0) (hdeg : 0 < F.totalDegree) :
    affineDimension (Ideal.span {F}) = n := by
  rw [affineDimension,coordinateHilbert_hypersurface F hF]
  apply le_antisymm (hypersurfaceHilbertPolynomial_degree n F.totalDegree)
  apply Polynomial.le_natDegree_of_ne_zero
  rw [hypersurfaceHilbertPolynomial_coeff]
  exact div_ne_zero (by exact_mod_cast hdeg.ne') (by exact_mod_cast Nat.factorial_ne_zero n)

theorem affineDegree_hypersurface {n : ℕ} {K : Type*} [Field K]
    (F : MvPolynomial (Fin (n+1)) K) (hF : F ≠ 0) (hdeg : 0 < F.totalDegree) :
    affineDegree (Ideal.span {F}) = F.totalDegree := by
  rw [affineDegree,affineDimension_hypersurface F hF hdeg,
    coordinateHilbert_hypersurface F hF,hypersurfaceHilbertPolynomial_coeff]
  field_simp

theorem affineDimension_lt_of_lt {n h : ℕ} {K : Type*} [Field K]
    (I J : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    (hIJ : I < J) (hd : affineDimension I = h+1) :
    affineDimension J ≤ h := by
  obtain ⟨p,hpJ,hpI⟩ := SetLike.exists_of_lt hIJ
  have hcut : I ⊔ Ideal.span {p} ≤ J := sup_le hIJ.le (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hpJ))
  have hdeg := (proper_cut_hilbert_polynomial I p hpI (coordinateHilbert I)
    (coordinateHilbert (I ⊔ Ideal.span {p}))
    ((coordinateHilbert_eventually I).mono (fun _ ht => ht.symm))
    ((coordinateHilbert_eventually _).mono (fun _ ht => ht.symm)) h hd.le).1
  have hnon : ∀ᶠ T : ℕ in Filter.atTop, 0 ≤ (coordinateHilbert J).eval (T:ℚ) := by
    filter_upwards [coordinateHilbert_eventually J] with T he
    rw [← he]; positivity
  have hle : ∀ᶠ T : ℕ in Filter.atTop,
      (coordinateHilbert J).eval (T:ℚ) ≤ (coordinateHilbert (I ⊔ Ideal.span {p})).eval (T:ℚ) := by
    filter_upwards [coordinateHilbert_eventually J,coordinateHilbert_eventually (I ⊔ Ideal.span {p})]
      with T hJ hI
    rw [← hJ,← hI]
    exact_mod_cast quotient_hilbert_le _ J hcut T
  exact (natDegree_le_of_eventually_nat_eval_bounds _ _ hnon hle).trans hdeg

theorem prime_same_dimension_eq {n h : ℕ} {K : Type*} [Field K]
    (I J : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    (hIJ : I ≤ J) (hdI : affineDimension I = h+1) (hdJ : affineDimension J = h+1) :
    I = J := by
  by_contra hne
  have h := affineDimension_lt_of_lt I J (lt_of_le_of_ne hIJ hne) hdI
  omega

theorem weightedSpace_map_le_weightedFunctions {n : ℕ} {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) (w : Fin n → ℕ) (ω : Fin n → ℝ)
    (hω : ∀ i, 0 < ω i) (L : ℝ) (hL : 0 < L)
    (hw : ∀ i, (w i : ℝ) = L*ω i) (T : ℝ) (hT : 0 ≤ T) :
    (weightedSpace w ⌊L*T⌋₊).map (Ideal.Quotient.mkₐ K I).toLinearMap ≤
      weightedFunctions I ω T := by
  classical
  rintro y ⟨p,hp,rfl⟩
  have hs : ∀ a ∈ p.support, monomialWeight ω a ≤ T := by
    intro a ha
    have hh : Finsupp.weight w a ≤ ⌊L*T⌋₊ :=
      hp ha
    have he : (Finsupp.weight w a : ℝ) = L*monomialWeight ω a := by
      rw [Finsupp.weight_eq_sum]
      simp only [Nat.cast_sum,monomialWeight,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [nsmul_eq_mul,Nat.cast_mul,hw]
      norm_cast
      ring
    have hhN : (Finsupp.weight w a : ℝ) ≤ (⌊L*T⌋₊:ℕ) := by exact_mod_cast hh
    have hh' : (Finsupp.weight w a : ℝ) ≤ L*T :=
      hhN.trans (Nat.floor_le (mul_nonneg hL.le hT))
    rw [he] at hh'
    exact (mul_le_mul_iff_right₀ hL).mp hh'
  rw [p.as_sum,map_sum]
  apply Submodule.sum_mem
  intro a ha
  have hm : Ideal.Quotient.mk I (monomial a (1:K)) ∈ weightedFunctions I ω T :=
    Submodule.subset_span ⟨a,(mem_weightedMonomials ω hω T a).mpr (hs a ha),rfl⟩
  have he : monomial a (p.coeff a) = (p.coeff a) • monomial a (1:K) := by
    rw [smul_monomial,smul_eq_mul,mul_one]
  rw [he]
  simpa using (weightedFunctions I ω T).smul_mem (p.coeff a) hm

theorem real_surface_hilbert_lower {K : Type*} [Field K]
    {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (F : MvPolynomial (Fin 3) K) (hF : F ≠ 0)
    (ω : Fin 3 → ℝ) (hω : ∀ i, 0 < ω i)
    (hw : ∀ i, (tripleWeights a b c i : ℝ) = (a:ℝ)*ω i) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 1 ≤ T →
      ((weightedTotalDegree (tripleWeights a b c) F : ℕ):ℝ)*(a:ℝ)^2 /
        (2*(a*b*c:ℕ)) * T^2 - C*T ≤ weightedHilbert (Ideal.span {F}) ω T := by
  classical
  obtain ⟨C,hC,hH⟩ := surface_hilbert_error ha hb hc F hF
  let D := weightedTotalDegree (tripleWeights a b c) F
  let A : ℝ := D/(2*(a*b*c:ℕ))
  have ha' : (0:ℝ) < a := by exact_mod_cast ha
  have habc : (0:ℝ) < (a*b*c:ℕ) := by exact_mod_cast Nat.mul_pos (Nat.mul_pos ha hb) hc
  have hA : 0 ≤ A := by dsimp [A]; positivity
  let E : ℝ := A*(2*a + (D:ℝ)^2) + C*(a+1)
  have hE : 0 ≤ E := by dsimp [E]; positivity
  refine ⟨E,hE,?_⟩
  intro T hT
  let N := ⌊(a:ℝ)*T⌋₊
  have hN : (N:ℝ) ≤ a*T := Nat.floor_le (by positivity)
  have hN' : a*T < (N:ℝ)+1 := Nat.lt_floor_add_one _
  have hrank := Submodule.finrank_mono (weightedSpace_map_le_weightedFunctions
    (Ideal.span {F}) (tripleWeights a b c) ω hω (a:ℝ) ha' hw T (by linarith))
  have htarget : ((weightedTotalDegree (tripleWeights a b c) F : ℕ):ℝ)*(a:ℝ)^2 /
      (2*(a*b*c:ℕ))*T^2 = A*((a:ℝ)*T)^2 := by dsimp [A,D]; ring
  rw [htarget]
  by_cases hDN : D ≤ N
  · have hh := (abs_le.mp (hH N hDN)).1
    have hr : (Module.finrank K ((weightedSpace (tripleWeights a b c) N).map
        (Ideal.Quotient.mkₐ K (Ideal.span {F})).toLinearMap):ℝ) ≤
        weightedHilbert (Ideal.span {F}) ω T := by exact_mod_cast hrank
    have hsq : ((a:ℝ)*T)^2 ≤ (N:ℝ)^2+2*a*T := by
      have hnn : (0:ℝ) ≤ N := Nat.cast_nonneg _
      nlinarith
    have hh' : A*(N:ℝ)^2-C*((N:ℝ)+1) ≤ weightedHilbert (Ideal.span {F}) ω T := by
      have hv : A*(N:ℝ)^2 =
          ((weightedTotalDegree (tripleWeights a b c) F : ℕ):ℝ)*(N:ℝ)^2/(2*(a*b*c:ℕ)) := by
        dsimp [A,D]; ring
      rw [← hv] at hh
      linarith only [hh,hr]
    have hCs : C*((N:ℝ)+1) ≤ C*(a+1)*T := by nlinarith
    have hAs := mul_le_mul_of_nonneg_left hsq hA
    have hDterm : 0 ≤ A*(D:ℝ)^2*T := by positivity
    dsimp [E]
    nlinarith only [hAs,hh',hCs,hDterm]
  · have hND : N+1 ≤ D := by omega
    have hbound : (a:ℝ)*T ≤ D := by
      have hND' : (N:ℝ)+1 ≤ D := by exact_mod_cast hND
      linarith
    have hsq : ((a:ℝ)*T)^2 ≤ (D:ℝ)^2 := sq_le_sq₀ (by positivity) (by positivity) |>.mpr hbound
    have hAs := mul_le_mul_of_nonneg_left hsq hA
    have hDterm : A*(D:ℝ)^2 ≤ A*(D:ℝ)^2*T := le_mul_of_one_le_right (by positivity) hT
    have hr : (0:ℝ) ≤ weightedHilbert (Ideal.span {F}) ω T := Nat.cast_nonneg _
    have hother : 0 ≤ (A*(2*a)+C*(a+1))*T := by positivity
    dsimp [E]
    nlinarith

theorem directSurface_equation {K : Type*} [Field K] (f : Polynomial K) (k : ℕ)
    (J : Ideal (MvPolynomial (Fin 3) K)) (hJ : Ideal.span {directSurface f k} ≤ J) :
    Polynomial.aeval (Ideal.Quotient.mk J (X 0)) f =
      Ideal.Quotient.mk J (X 1)*(Ideal.Quotient.mk J (X 2))^k := by
  have hz : Ideal.Quotient.mk J (directSurface f k) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (hJ (Ideal.subset_span (Set.mem_singleton _)))
  have he : Ideal.Quotient.mk J (Polynomial.eval₂ C (X 0) f) =
      Polynomial.aeval (Ideal.Quotient.mk J (X 0)) f := by
    change (Ideal.Quotient.mkₐ K J) (Polynomial.aeval (X 0) f) = _
    exact (Polynomial.aeval_algHom_apply (Ideal.Quotient.mkₐ K J) (X 0) f).symm
  simpa only [directSurface,map_sub,map_mul,map_pow,he,sub_eq_zero] using hz

theorem directSurface_hilbert_threshold {K : Type*} [Field K]
    (f : Polynomial K) (hf : f ≠ 0) (k : ℕ)
    {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (ω : Fin 3 → ℝ) (hω : ∀ i, 0 < ω i)
    (hw : ∀ i, (tripleWeights a b c i : ℝ) = (a:ℝ)*ω i)
    (δ : ℝ) (hδ : 0 < δ)
    (hmargin : (b:ℝ)*(c:ℝ) ≤ (f.natDegree:ℝ)*(a:ℝ)^2*δ^2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 1 ≤ T →
      T^2/(2*δ^2)-C*T ≤ weightedHilbert (Ideal.span {directSurface f k}) ω T := by
  have hF := (directSurface_irreducible f hf k).ne_zero
  obtain ⟨C,hC,hH⟩ := real_surface_hilbert_lower ha hb hc (directSurface f k) hF ω hω hw
  refine ⟨C,hC,?_⟩
  intro T hT
  have ha' : (0:ℝ) < a := by exact_mod_cast ha
  have hb' : (0:ℝ) < b := by exact_mod_cast hb
  have hc' : (0:ℝ) < c := by exact_mod_cast hc
  let D := weightedTotalDegree (tripleWeights a b c) (directSurface f k)
  have hD : (f.natDegree:ℝ)*(a:ℝ) ≤ (D:ℝ) := by
    have hh := directSurface_weightedDegree_lower f hf k (tripleWeights a b c)
    simpa only [tripleWeights,Matrix.cons_val_zero,Nat.cast_mul] using (show
      ((f.natDegree*tripleWeights a b c 0:ℕ):ℝ) ≤ D from by exact_mod_cast hh)
  have he : (D:ℝ)*(a:ℝ)^2/(2*(a*b*c:ℕ)) = (D:ℝ)*a/(2*(b:ℝ)*c) := by
    push_cast
    field_simp
  have hcoeff : 1/(2*δ^2) ≤ (D:ℝ)*(a:ℝ)^2/(2*(a*b*c:ℕ)) := by
    rw [he]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    have hm := mul_le_mul_of_nonneg_right hD (show 0 ≤ (a:ℝ)*δ^2 by positivity)
    nlinarith only [hmargin,hm]
  have hh := mul_le_mul_of_nonneg_right hcoeff (sq_nonneg T)
  have hH' := hH T hT
  dsimp only [D] at hh
  have heq : 1/(2*δ^2)*T^2 = T^2/(2*δ^2) := by ring
  rw [heq] at hh
  linarith only [hh,hH']

theorem direct_surface_selected_count (f : Polynomial ℤ) (hf : f.IsPrimitive)
    (hsq : Squarefree (f.map (Int.castRingHom ℂ))) (k : ℕ) (hk : 2 ≤ k)
    {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (ω : Fin 3 → ℝ) (hω : ∀ j, 0 < ω j) (hω0 : ω 0 = 1)
    (hw : ∀ i, (tripleWeights a b c i : ℝ) = (a:ℝ)*ω i)
    (δ : ℝ) (hδ : 0 < δ) (hδhalf : δ ≤ 1/2)
    (hmargin : (b:ℝ)*(c:ℝ) ≤ (f.natDegree:ℝ)*(a:ℝ)^2*δ^2)
    (Cbox : ℝ) (hCbox : 1 ≤ Cbox) (ε : ℝ) (hε : 0 < ε) :
    ∃ C X₀ : ℝ, 0 < C ∧ ∀ X : ℝ, X₀ < X → ∀ S : Finset (Fin 3 → ℤ),
      Set.InjOn (fun z : Fin 3 → ℤ => z 0) (S:Set _) →
      (∀ z ∈ S, ∀ j, |(z j:ℝ)| ≤ Cbox*X^(ω j)) →
      (∀ z ∈ S, X < (z 0:ℝ) ∧ (z 0:ℝ) ≤ 2*X) →
      (∀ z ∈ S, ∃ p : ℕ, p.Prime ∧ z 2 = p ∧ X < p ∧ (p:ℤ) ∣ f.eval (z 0)) →
      (∀ z ∈ S, (f.map (Int.castRingHom ℂ)).eval (z 0:ℂ) = (z 1:ℂ)*(z 2:ℂ)^k) →
      (S.card:ℝ) ≤ C*X^(δ+1/2+ε) := by
  classical
  let fc := f.map (Int.castRingHom ℂ)
  have hfc : fc ≠ 0 := (Polynomial.map_ne_zero_iff (Int.cast_injective)).mpr hf.ne_zero
  have hdegfc : fc.natDegree = f.natDegree := Polynomial.natDegree_map_eq_of_injective (Int.cast_injective) f
  let F := directSurface fc k
  have hFir : Irreducible F := directSurface_irreducible fc hfc k
  have hFdeg : 0 < F.totalDegree := totalDegree_pos_of_irreducible F hFir
  let I := Ideal.span {F}
  have hI : I.IsPrime := (Ideal.span_singleton_prime hFir.ne_zero).mpr hFir.prime
  let : I.IsPrime := hI
  have hdI : affineDimension I = 2 := affineDimension_hypersurface F hFir.ne_zero hFdeg
  have heI : affineDegree I = F.totalDegree := affineDegree_hypersurface F hFir.ne_zero hFdeg
  have hmarginc : (b:ℝ)*(c:ℝ) ≤ (fc.natDegree:ℝ)*(a:ℝ)^2*δ^2 := by rwa [hdegfc]
  obtain ⟨Cs,hCs,hHs⟩ := directSurface_hilbert_threshold fc hfc k ha hb hc ω hω hw δ hδ hmarginc
  choose Kex hKex hcurve using fun e => direct_curve_count_or_hilbert f hf hsq k hk e ω hω hω0
    Cbox (by linarith) (ε/4) (by linarith)
  let cc := fun _ : ℕ => Cs+2*(ω 1+ω 2+1)
  have hcc : ∀ e, 0 ≤ cc e := by intro e; dsimp [cc]; linarith [hω 1,hω 2]
  let av : Fin 2 → ℝ := ![δ,1/2-δ]
  let dv : Fin 2 → ℝ := ![δ,1/2]
  have hav : ∀ i, 0 ≤ av i := by intro i; fin_cases i <;> simp [av] <;> linarith
  have hdv : ∀ i, 0 < dv i := by intro i; fin_cases i <;> simp [dv,hδ]
  have hprefix : ∀ i, dv i ≤ ∑ j ∈ Finset.univ.filter (fun j : Fin 2 => j.val ≤ i.val), av j := by
    intro i
    fin_cases i <;> norm_num [av,dv,Fin.sum_univ_two,Finset.sum_filter]
  let w := 1+∑ j, ω j
  have hsum : 0 ≤ ∑ j, ω j := Finset.sum_nonneg (fun j _ => (hω j).le)
  have hwpos : 0 ≤ w := by dsimp [w]; linarith
  obtain ⟨C,Xcut,hC,hcount⟩ := physical_affine_count 3 2 0 F.totalDegree (by norm_num)
    ω hω Cbox w hCbox hwpos av dv hav hdv hprefix ε hε cc Kex hcc hKex
  refine ⟨C,max (max 2 Cbox) Xcut,hC,?_⟩
  intro X hX S hinj hbox hrange hselected heq
  have hX2 : 2 < X := lt_of_le_of_lt ((le_max_left _ _).trans (le_max_left _ _)) hX
  have hCX : Cbox ≤ X := le_of_lt (lt_of_le_of_lt ((le_max_right _ _).trans (le_max_left _ _)) hX)
  have hXcut : Xcut < X := lt_of_le_of_lt (le_max_right _ _) hX
  have hX1 : 1 ≤ X := by linarith
  have hXp : 0 < X := by linarith
  have hmax (j : Fin 3) : ω j ≤ ∑ l, ω l :=
    Finset.single_le_sum (fun l _ => (hω l).le) (Finset.mem_univ j)
  have hbound (z) (hz : z ∈ S) (j) : |(z j:ℝ)| ≤ X^w := by
    calc
      _ ≤ Cbox*X^(ω j) := hbox z hz j
      _ ≤ X*X^(∑ l, ω l) := mul_le_mul hCX (Real.rpow_le_rpow_of_exponent_le hX1 (hmax j))
        (Real.rpow_nonneg hXp.le _) (by linarith)
      _ = X^w := by dsimp [w]; rw [Real.rpow_add hXp,Real.rpow_one]
  let G : KernelGeometry 3 := ⟨S,X^w,Real.one_le_rpow hX1 hwpos,hbound⟩
  have hpoints : ∀ z ∈ G.points, PointOn I z := by
    intro z hz
    change I ≤ RingHom.ker (MvPolynomial.aeval (fun j => (z j:ℂ))).toRingHom
    apply Ideal.span_le.mpr
    intro p hp
    have hp' : p = F := Set.mem_singleton_iff.mp hp
    subst p
    change MvPolynomial.aeval (fun j => (z j:ℂ)) (directSurface fc k) = 0
    have hev : MvPolynomial.aeval (fun j => (z j:ℂ)) (Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X 0) fc) = fc.eval (z 0:ℂ) := by
      induction fc using Polynomial.induction_on' with
      | add p q hp hq => simp only [Polynomial.eval₂_add,map_add,Polynomial.eval_add,hp,hq]
      | monomial n a => simp [Polynomial.eval₂_monomial,Polynomial.eval_monomial]
    simpa only [directSurface,map_sub,map_mul,map_pow,MvPolynomial.aeval_X,hev,sub_eq_zero] using heq z hz
  have hh := hcount X hXcut G le_rfl hbox I hI hdI.le heI.le hpoints
  have hend := hh (by
    intro i e J hJ hIJ _ hJe hJdim _
    let : J.IsPrime := hJ
    fin_cases i
    · have heJI : I = J := prime_same_dimension_eq I J hIJ hdI hJdim
      subst J
      right
      intro T hT
      have hlo := hHs T hT
      have hn : 0 ≤ 2*(ω 1+ω 2+1)*T := by
        exact mul_nonneg (by linarith [hω 1,hω 2]) (by linarith)
      norm_num [dv,cc]
      linarith only [hlo,hn]
    · have hjdim : affineDimension J ≤ 1 := by simpa using hJdim.le
      have hS' : ∀ z ∈ S.filter (PointOn J), z ∈ S := fun z hz => (Finset.mem_filter.mp hz).1
      have hcur := hcurve e X hX2.le (S.filter (PointOn J)) (hinj.mono (Finset.filter_subset _ _))
        (fun z hz j => hbox z (hS' z hz) j) (fun z hz => hrange z (hS' z hz))
        (fun z hz => hselected z (hS' z hz)) J hJ hjdim hJe
        (fun z hz => (Finset.mem_filter.mp hz).2) (directSurface_equation fc k J hIJ)
      rcases hcur with hsmall | hH
      · exact Or.inl hsmall
      · right
        intro T hT
        have hlo := hH T hT
        have hn : 0 ≤ Cs := hCs
        norm_num [dv,cc]
        linarith only [hlo,hn])
  have hexp : (∑ i : Fin 2, ((2-i.val:ℕ):ℝ)*av i)+ε = δ+1/2+ε := by
    simp [av,Fin.sum_univ_two]
    ring
  simpa only [hexp] using hend

end QuarticPowerFree

end OAI
end

section
-- module Solutions.OAIB3_Qpf.PowerFree_HighDegree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace QuarticPowerFree

open scoped BigOperators

theorem polynomial_dyadic_eval_bound (f : Polynomial ℤ) :
    ∃ C : ℝ, 2 ≤ C ∧ ∀ (X : ℝ), 1 ≤ X → ∀ (n : ℤ), 0 ≤ n → (n:ℝ) ≤ 2*X →
      |((f.eval n:ℤ):ℝ)| ≤ C*X^(f.natDegree:ℝ) := by
  classical
  let A : ℝ := ∑ i ∈ f.support, |(f.coeff i:ℝ)|
  have hA : 0 ≤ A := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  let C := 2+A*2^f.natDegree
  have hC : 2 ≤ C := by dsimp [C]; nlinarith [pow_pos (show (0:ℝ)<2 by norm_num) f.natDegree]
  refine ⟨C,hC,fun X hX n hn hnX => ?_⟩
  have hXp : 0 ≤ X := by linarith
  have hn' : 0 ≤ (n:ℝ) := by exact_mod_cast hn
  have hh : |((f.eval n:ℤ):ℝ)| ≤ A*(2*X)^f.natDegree := by
    rw [Polynomial.eval_eq_sum,Polynomial.sum_def]
    push_cast
    calc
      _ ≤ ∑ i ∈ f.support, |(f.coeff i:ℝ)*(n:ℝ)^i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ f.support, |(f.coeff i:ℝ)| *(2*X)^f.natDegree := by
        apply Finset.sum_le_sum
        intro i hi
        rw [abs_mul,abs_pow,abs_of_nonneg hn']
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        exact (pow_le_pow_left₀ hn' hnX i).trans (pow_le_pow_right₀ (by linarith)
          (Polynomial.le_natDegree_of_mem_supp i hi))
      _ = A*(2*X)^f.natDegree := by rw [Finset.sum_mul]
  rw [mul_pow] at hh
  rw [Real.rpow_natCast]
  have hc : A*2^f.natDegree ≤ C := by dsimp [C]; linarith
  exact hh.trans (by rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hc (pow_nonneg hXp _))

theorem rational_irreducible_squarefree_complex (f : Polynomial ℤ)
    (hf : Irreducible (f.map (Int.castRingHom ℚ))) :
    Squarefree (f.map (Int.castRingHom ℂ)) := by
  have h := hf.separable.map (f := Rat.castHom ℂ)
  have he : (Rat.castHom ℂ).comp (Int.castRingHom ℚ) = Int.castRingHom ℂ := by ext; simp
  rw [Polynomial.map_map,he] at h
  exact h.squarefree

theorem rational_irreducible_eval_ne_zero (f : Polynomial ℤ)
    (hf : Irreducible (f.map (Int.castRingHom ℚ))) (hd : 2 ≤ f.natDegree) (n : ℤ) :
    f.eval n ≠ 0 := by
  intro hz
  have hr : (f.map (Int.castRingHom ℚ)).IsRoot (n:ℚ) := by
    change (f.map (Int.castRingHom ℚ)).eval (n:ℚ) = 0
    rw [Polynomial.eval_intCast_map]
    change (Int.castRingHom ℚ) (f.eval n) = 0
    rw [hz,map_zero]
  have hdvd := Polynomial.dvd_iff_isRoot.mpr hr
  have hu : ¬ IsUnit (Polynomial.X-Polynomial.C (n:ℚ)) := by
    exact Polynomial.not_isUnit_of_natDegree_pos _ (by rw [Polynomial.natDegree_X_sub_C]; decide)
  have ha := (hf.dvd_iff.mp hdvd).resolve_left hu
  have he := Polynomial.natDegree_le_of_dvd ha.dvd (Polynomial.X_sub_C_ne_zero (n:ℚ))
  rw [Polynomial.natDegree_map_eq_of_injective Int.cast_injective,
    Polynomial.natDegree_X_sub_C] at he
  omega

theorem high_degree_two_boxes {C X : ℝ} (hC : 2 ≤ C) (hX : 1 ≤ X)
    {d k : ℕ} (hd : 9 ≤ d) (hk : k = d-2)
    (y : ℤ) (p : ℕ) (hp : X < p)
    (hv : |(y:ℝ)| *(p:ℝ)^k ≤ C*X^(d:ℝ))
    (hy : y ≠ 0) :
    (|(y:ℝ)| ≤ C*X^(2:ℝ) ∧ (p:ℝ) ≤ C*X^(11/10:ℝ)) ∨
    (|(y:ℝ)| ≤ C*X^(13/10:ℝ) ∧ (p:ℝ) ≤ C*X^(13/10:ℝ)) := by
  have hXp : 0 < X := by linarith
  have hpp : (0:ℝ) < p := by linarith
  have hk0 : 0 < k := by omega
  have hkR : (0:ℝ) < k := by exact_mod_cast hk0
  have hdR : (9:ℝ) ≤ d := by exact_mod_cast hd
  have hdk : (d:ℝ) = (k:ℝ)+2 := by exact_mod_cast (show d=k+2 by omega)
  have hy1 : 1 ≤ |(y:ℝ)| := by exact_mod_cast (Int.one_le_abs hy)
  have hCp : 0 < C := by linarith
  have hpow : (p:ℝ)^k ≤ C*X^(d:ℝ) := by nlinarith [pow_pos hpp k]
  have hprime : (p:ℝ) ≤ C*X^(13/10:ℝ) := by
    apply (Real.rpow_le_rpow_iff hpp.le (by positivity) hkR).mp
    simp only [Real.rpow_natCast]
    rw [mul_pow,← Real.rpow_natCast (X^(13/10:ℝ)) k,← Real.rpow_mul hXp.le]
    have hexp : (d:ℝ) ≤ 13/10*(k:ℝ) := by linarith
    have hCC : C ≤ C^k := le_self_pow₀ (by linarith) hk0.ne'
    exact hpow.trans (mul_le_mul hCC (Real.rpow_le_rpow_of_exponent_le hX hexp)
      (Real.rpow_nonneg hXp.le _) (by positivity))
  by_cases hpbox : (p:ℝ) ≤ X^(11/10:ℝ)
  · left
    refine ⟨?_,hpbox.trans (le_mul_of_one_le_left (Real.rpow_nonneg hXp.le _) (by linarith))⟩
    have hxk : X^(k:ℝ) ≤ (p:ℝ)^k := by rw [Real.rpow_natCast]; exact pow_le_pow_left₀ hXp.le hp.le k
    have he : C*X^(d:ℝ) = (C*X^(2:ℝ))*X^(k:ℝ) := by
      rw [hdk,Real.rpow_add hXp]; ring
    have hv' := (mul_le_mul_of_nonneg_left hxk (abs_nonneg (y:ℝ))).trans hv
    rw [he] at hv'
    exact (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos hXp _)).mp hv'
  · right
    refine ⟨?_,hprime⟩
    have hpbox' : X^(11/10:ℝ) ≤ (p:ℝ) := (lt_of_not_ge hpbox).le
    have hxk : X^((11/10:ℝ)*(k:ℝ)) ≤ (p:ℝ)^k := by
      rw [Real.rpow_mul hXp.le,Real.rpow_natCast]
      exact pow_le_pow_left₀ (Real.rpow_nonneg hXp.le _) hpbox' k
    have hexp : (d:ℝ) ≤ 13/10+11/10*(k:ℝ) := by linarith
    have he : C*X^(d:ℝ) ≤ (C*X^(13/10:ℝ))*X^((11/10:ℝ)*(k:ℝ)) := by
      rw [mul_assoc,← Real.rpow_add hXp]
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hX hexp) hCp.le
    have hv' := (mul_le_mul_of_nonneg_left hxk (abs_nonneg (y:ℝ))).trans (hv.trans he)
    exact (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos hXp _)).mp hv'

section
open scoped BigOperators Classical

theorem high_degree_selected_count (f : Polynomial ℤ) (hf : f.IsPrimitive)
    (hirr : Irreducible (f.map (Int.castRingHom ℚ))) (hd : 9 ≤ f.natDegree) :
    ∃ C X₀ : ℝ, 0 < C ∧ ∀ X : ℝ, X₀ < X → ∀ S : Finset (Fin 3 → ℤ),
      Set.InjOn (fun z : Fin 3 → ℤ => z 0) (S:Set _) →
      (∀ z ∈ S, X < (z 0:ℝ) ∧ (z 0:ℝ) ≤ 2*X) →
      (∀ z ∈ S, ∃ p : ℕ, p.Prime ∧ z 2 = p ∧ X < p) →
      (∀ z ∈ S, f.eval (z 0) = z 1*(z 2)^(f.natDegree-2)) →
      (S.card:ℝ) ≤ C*X^(1-1/2000:ℝ) := by
  classical
  let k := f.natDegree-2
  have hk : 2 ≤ k := by dsimp [k]; omega
  have hsq := rational_irreducible_squarefree_complex f hirr
  obtain ⟨Cb,hCb,hpoly⟩ := polynomial_dyadic_eval_bound f
  let ω₁ : Fin 3 → ℝ := ![1,2,11/10]
  let ω₂ : Fin 3 → ℝ := ![1,13/10,13/10]
  have hω₁ : ∀ j, 0 < ω₁ j := by intro j; fin_cases j <;> norm_num [ω₁]
  have hω₂ : ∀ j, 0 < ω₂ j := by intro j; fin_cases j <;> norm_num [ω₂]
  have hw₁ : ∀ j, (tripleWeights 10 20 11 j:ℝ) = (10:ℝ)*ω₁ j := by
    intro j; fin_cases j <;> norm_num [tripleWeights,ω₁]
  have hw₂ : ∀ j, (tripleWeights 10 13 13 j:ℝ) = (10:ℝ)*ω₂ j := by
    intro j; fin_cases j <;> norm_num [tripleWeights,ω₂]
  have hd' : (9:ℝ) ≤ f.natDegree := by exact_mod_cast hd
  have hm₁ : (20:ℝ)*11 ≤ (f.natDegree:ℝ)*(10:ℝ)^2*(499/1000:ℝ)^2 := by nlinarith
  have hm₂ : (13:ℝ)*13 ≤ (f.natDegree:ℝ)*(10:ℝ)^2*(499/1000:ℝ)^2 := by nlinarith
  obtain ⟨C₁,X₁,hC₁,hcount₁⟩ := direct_surface_selected_count f hf hsq k hk
    (a := 10) (b := 20) (c := 11) (by norm_num) (by norm_num) (by norm_num)
    ω₁ hω₁ rfl hw₁ (499/1000) (by norm_num) (by norm_num) hm₁ Cb (by linarith)
    (1/2000) (by norm_num)
  obtain ⟨C₂,X₂,hC₂,hcount₂⟩ := direct_surface_selected_count f hf hsq k hk
    (a := 10) (b := 13) (c := 13) (by norm_num) (by norm_num) (by norm_num)
    ω₂ hω₂ rfl hw₂ (499/1000) (by norm_num) (by norm_num) hm₂ Cb (by linarith)
    (1/2000) (by norm_num)
  refine ⟨C₁+C₂,max 1 (max X₁ X₂),by linarith,?_⟩
  intro X hX S hinj hrange hprime heq
  have hX1 : 1 < X := lt_of_le_of_lt (le_max_left _ _) hX
  have hX₁ : X₁ < X := lt_of_le_of_lt ((le_max_left _ _).trans (le_max_right _ _)) hX
  have hX₂ : X₂ < X := lt_of_le_of_lt ((le_max_right _ _).trans (le_max_right _ _)) hX
  let B₁ := fun z : Fin 3 → ℤ => ∀ j, |(z j:ℝ)| ≤ Cb*X^(ω₁ j)
  let B₂ := fun z : Fin 3 → ℤ => ∀ j, |(z j:ℝ)| ≤ Cb*X^(ω₂ j)
  have hcover : ∀ z ∈ S, B₁ z ∨ B₂ z := by
    intro z hz
    obtain ⟨p,hp,hzp,hXp⟩ := hprime z hz
    have hz0 : 0 ≤ z 0 := by exact_mod_cast (show (0:ℝ) ≤ z 0 by linarith [(hrange z hz).1])
    have hb := hpoly X hX1.le (z 0) hz0 (hrange z hz).2
    have hev : ((f.eval (z 0):ℤ):ℝ) = (z 1:ℝ)*(p:ℝ)^k := by
      have hh := congrArg (fun a : ℤ => (a:ℝ)) (heq z hz)
      simpa only [Int.cast_mul,Int.cast_pow,hzp,Int.cast_natCast] using hh
    have hv : |(z 1:ℝ)| *(p:ℝ)^k ≤ Cb*X^(f.natDegree:ℝ) := by
      rw [hev,abs_mul,abs_of_nonneg (show (0:ℝ) ≤ (p:ℝ)^k from pow_nonneg (Nat.cast_nonneg p) k)] at hb
      exact hb
    have hy : z 1 ≠ 0 := by
      intro hy
      have hh := heq z hz
      rw [hy,zero_mul] at hh
      exact rational_irreducible_eval_ne_zero f hirr (by omega) (z 0) hh
    have hb0 : |(z 0:ℝ)| ≤ Cb*X := by
      rw [abs_of_nonneg (by exact_mod_cast hz0)]
      exact (hrange z hz).2.trans (mul_le_mul_of_nonneg_right hCb (by linarith))
    rcases high_degree_two_boxes hCb hX1.le hd rfl (z 1) p hXp hv hy with h₁ | h₂
    · left
      intro j
      fin_cases j
      · simpa [ω₁,Real.rpow_one] using hb0
      · change |(z 1:ℝ)| ≤ Cb*X^(2:ℝ)
        exact h₁.1
      · change |(z 2:ℝ)| ≤ Cb*X^(11/10:ℝ)
        rw [hzp,Int.cast_natCast,abs_of_nonneg (Nat.cast_nonneg p)]
        exact h₁.2
    · right
      intro j
      fin_cases j
      · simpa [ω₂,Real.rpow_one] using hb0
      · change |(z 1:ℝ)| ≤ Cb*X^(13/10:ℝ)
        exact h₂.1
      · change |(z 2:ℝ)| ≤ Cb*X^(13/10:ℝ)
        rw [hzp,Int.cast_natCast,abs_of_nonneg (Nat.cast_nonneg p)]
        exact h₂.2
  have hselected : ∀ z ∈ S, ∃ p : ℕ, p.Prime ∧ z 2 = p ∧ X < p ∧ (p:ℤ) ∣ f.eval (z 0) := by
    intro z hz
    obtain ⟨p,hp,hzp,hXp⟩ := hprime z hz
    refine ⟨p,hp,hzp,hXp,?_⟩
    rw [heq z hz,hzp]
    exact dvd_mul_of_dvd_right (dvd_pow_self (p:ℤ) (by omega)) _
  have hcomplex : ∀ z ∈ S, (f.map (Int.castRingHom ℂ)).eval (z 0:ℂ) =
      (z 1:ℂ)*(z 2:ℂ)^k := by
    intro z hz
    rw [Polynomial.eval_intCast_map]
    change (((f.eval (z 0):ℤ):ℂ)) = (z 1:ℂ)*(z 2:ℂ)^k
    exact_mod_cast heq z hz
  have hc₁ := hcount₁ X hX₁ (S.filter B₁) (hinj.mono (Finset.filter_subset _ _))
    (fun z hz => (Finset.mem_filter.mp hz).2)
    (fun z hz => hrange z (Finset.mem_filter.mp hz).1)
    (fun z hz => hselected z (Finset.mem_filter.mp hz).1)
    (fun z hz => hcomplex z (Finset.mem_filter.mp hz).1)
  have hc₂ := hcount₂ X hX₂ (S.filter B₂) (hinj.mono (Finset.filter_subset _ _))
    (fun z hz => (Finset.mem_filter.mp hz).2)
    (fun z hz => hrange z (Finset.mem_filter.mp hz).1)
    (fun z hz => hselected z (Finset.mem_filter.mp hz).1)
    (fun z hz => hcomplex z (Finset.mem_filter.mp hz).1)
  have hsub : S ⊆ (S.filter B₁) ∪ (S.filter B₂) := by
    intro z hz
    rcases hcover z hz with h₁ | h₂
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hz,h₁⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hz,h₂⟩)
  have hcard : (S.card:ℝ) ≤ ((S.filter B₁).card:ℝ)+((S.filter B₂).card:ℝ) := by
    exact_mod_cast (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  norm_num at hc₁ hc₂ ⊢
  nlinarith only [hcard,hc₁,hc₂]

end

open Filter
open scoped Topology Classical

theorem high_degree_dyadic_tail (f : Polynomial ℤ) (hf : f.IsPrimitive)
    (hirr : Irreducible (f.map (Int.castRingHom ℚ))) (hd : 9 ≤ f.natDegree) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ M : ℕ in atTop,
      (dyadicTailCount f (f.natDegree-2) M:ℝ) ≤ C*(M:ℝ)^(1-1/2000:ℝ) := by
  classical
  obtain ⟨C,X₀,hC,hcount⟩ := high_degree_selected_count f hf hirr hd
  refine ⟨C,hC,?_⟩
  have hlim : Tendsto (fun M : ℕ => (M:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  filter_upwards [hlim.eventually (eventually_gt_atTop X₀)] with M hM
  let D := (Finset.Ioc M (2*M)).filter fun n : ℕ =>
    ∃ p : ℕ, p.Prime ∧ M < p ∧ (p:ℤ)^(f.natDegree-2) ∣ f.eval (n:ℤ)
  have hD (n : D) : ∃ p : ℕ, p.Prime ∧ M < p ∧
      (p:ℤ)^(f.natDegree-2) ∣ f.eval (n.val:ℤ) := (Finset.mem_filter.mp n.property).2
  choose p hp hMp hdiv using hD
  choose y hy using hdiv
  let z := fun n : D => (![(n.val:ℤ),y n,(p n:ℤ)] : Fin 3 → ℤ)
  have hzinj : Function.Injective z := by
    intro u v huv
    apply Subtype.ext
    have hh := congrFun huv 0
    dsimp only [z,Matrix.cons_val_zero] at hh
    exact_mod_cast hh
  let S := Finset.univ.image z
  have hS : ∀ u ∈ S, ∃ n : D, z n = u := by
    intro u hu
    obtain ⟨n,_,hn⟩ := Finset.mem_image.mp hu
    exact ⟨n,hn⟩
  have hinj : Set.InjOn (fun u : Fin 3 → ℤ => u 0) (S:Set _) := by
    intro u hu v hv huv
    obtain ⟨i,rfl⟩ := hS u hu
    obtain ⟨j,rfl⟩ := hS v hv
    have hij : i = j := by
      apply Subtype.ext
      dsimp only [z,Matrix.cons_val_zero] at huv
      exact_mod_cast huv
    rw [hij]
  have hrange : ∀ u ∈ S, (M:ℝ) < (u 0:ℝ) ∧ (u 0:ℝ) ≤ 2*(M:ℝ) := by
    intro u hu
    obtain ⟨n,rfl⟩ := hS u hu
    have hn := Finset.mem_Ioc.mp (Finset.mem_filter.mp n.property).1
    dsimp only [z,Matrix.cons_val_zero]
    constructor
    · exact_mod_cast hn.1
    · exact_mod_cast hn.2
  have hprime : ∀ u ∈ S, ∃ q : ℕ, q.Prime ∧ u 2 = q ∧ (M:ℝ) < q := by
    intro u hu
    obtain ⟨n,rfl⟩ := hS u hu
    exact ⟨p n,hp n,rfl,by exact_mod_cast hMp n⟩
  have heq : ∀ u ∈ S, f.eval (u 0) = u 1*(u 2)^(f.natDegree-2) := by
    intro u hu
    obtain ⟨n,rfl⟩ := hS u hu
    change f.eval (n.val:ℤ) = y n*(p n:ℤ)^(f.natDegree-2)
    rw [hy n,mul_comm]
  have hc := hcount M hM S hinj hrange hprime heq
  have hcard : S.card = D.card := by
    rw [Finset.card_image_of_injective _ hzinj,Finset.card_univ,Fintype.card_coe]
  simpa only [hcard,dyadicTailCount,D] using hc

theorem density_ge_nine (f : Polynomial ℤ)
    (hirr : Irreducible (f.map (Int.castRingHom ℚ))) (hd : 9 ≤ f.natDegree)
    (hlocal : LocallyAdmissible f (f.natDegree-2)) :
    DensityStatement f (f.natDegree-2) := by
  obtain ⟨a,g,ha,hfg,hgprim,_hgpos,hgdeg,hgirr⟩ := exists_primitive_positive_normalization f hirr
  obtain ⟨C,_hC,hbound⟩ := high_degree_dyadic_tail g hgprim hgirr (by omega)
  have ht := dyadic_tail_limit_of_power_saving g (g.natDegree-2) (1/2000) C (by norm_num) hbound
  rw [hgdeg] at ht
  exact densityStatement_from_normalized_dyadic_tail f g hirr (by omega)
    (by omega) hlocal a ha hfg ht

end QuarticPowerFree

end OAI
end

section
-- module Solutions.OAIB3_Qpf.PowerFree_MediumDegree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace QuarticPowerFree

section
open Filter NumberField
open scoped Topology Classical

theorem density_ge_five (f : Polynomial ℤ)
    (hirr : Irreducible (f.map (Int.castRingHom ℚ))) (hd : 5 ≤ f.natDegree)
    (hlocal : LocallyAdmissible f (f.natDegree-2)) :
    DensityStatement f (f.natDegree-2) := by
  by_cases hd9 : 9 ≤ f.natDegree
  · exact density_ge_nine f hirr hd9 hlocal
  obtain ⟨a,g,ha,hfg,hgprim,hgpos,hgdeg,hgirr⟩ := exists_primitive_positive_normalization f hirr
  obtain ⟨C,_hC,hbound⟩ := medium_degree_dyadic_tail g hgprim hgirr hgpos (by omega) (by omega)
  have ht := dyadic_tail_limit_of_power_saving g (g.natDegree-2) (3/1000) C (by norm_num) hbound
  rw [hgdeg] at ht
  exact densityStatement_from_normalized_dyadic_tail f g hirr (by omega)
    (by omega) hlocal a ha hfg ht

end

open MvPolynomial
open scoped Classical BigOperators

attribute [instance] QuarticBoxSystem.field QuarticBoxSystem.charZero

end QuarticPowerFree

end OAI
end

section
-- module Solutions.OAIB3_Qpf.PowerFree_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace QuarticPowerFree

theorem density_ge_four (f : Polynomial ℤ)
    (hirr : Irreducible (f.map (Int.castRingHom ℚ))) (hd : 4 ≤ f.natDegree)
    (hlocal : LocallyAdmissible f (f.natDegree-2)) :
    DensityStatement f (f.natDegree-2) := by
  by_cases hd5 : 5 ≤ f.natDegree
  · exact density_ge_five f hirr hd5 hlocal
  obtain ⟨a,g,ha,hfg,hgprim,hgpos,hgdeg,hgirr⟩ := exists_primitive_positive_normalization f hirr
  obtain ⟨C,_hC,hbound⟩ := quartic_dyadic_tail g hgprim hgirr hgpos (by omega)
  have ht := dyadic_tail_limit_of_power_saving g (g.natDegree-2) (3/1000) C (by norm_num) hbound
  rw [hgdeg] at ht
  exact densityStatement_from_normalized_dyadic_tail f g hirr (by omega)
    (by omega) hlocal a ha hfg ht

theorem allDegrees_oai (f : Polynomial ℤ)
    (hirr : Irreducible (f.map (Int.castRingHom ℚ)))
    (hdeglo : 4 ≤ f.natDegree)
    (hlocal : LocallyAdmissible f (f.natDegree - 2)) :
    DensityStatement f (f.natDegree - 2) := by
  exact density_ge_four f hirr hdeglo hlocal

end QuarticPowerFree

end OAI
end

theorem solution : type_of% @OAI.QuarticPowerFree.allDegrees_oai := @OAI.QuarticPowerFree.allDegrees_oai
