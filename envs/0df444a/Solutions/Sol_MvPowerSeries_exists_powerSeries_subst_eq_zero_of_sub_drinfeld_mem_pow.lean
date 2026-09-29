-- Prove2me | solution 1 for MvPowerSeries.exists_powerSeries_subst_eq_zero_of_sub_drinfeld_mem_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/bb6dfe41-030c-5382-88af-2021df6be6f7

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvPowerSeries_exists_powerSeries_subst_eq_zero_of_sub_drinfeld_mem_pow

set_option autoImplicit false

open MvPowerSeries

namespace NewtonBranch

variable {k : Type*} [CommRing k]

def VB (n : ℕ) (x : PowerSeries k) : Prop := ∀ m : ℕ, m < n → PowerSeries.coeff m x = 0

theorem VB.zero_le {x : PowerSeries k} : VB 0 x := fun m hm => (Nat.not_lt_zero m hm).elim

theorem VB.mono {n n' : ℕ} {x : PowerSeries k} (h : VB n x) (hle : n' ≤ n) : VB n' x :=
  fun m hm => h m (lt_of_lt_of_le hm hle)

theorem VB.add {n : ℕ} {x y : PowerSeries k} (hx : VB n x) (hy : VB n y) : VB n (x + y) := by
  intro m hm; rw [map_add, hx m hm, hy m hm, add_zero]

theorem VB.sub {n : ℕ} {x y : PowerSeries k} (hx : VB n x) (hy : VB n y) : VB n (x - y) := by
  intro m hm; rw [map_sub, hx m hm, hy m hm, sub_zero]

theorem VB.neg {n : ℕ} {x : PowerSeries k} (hx : VB n x) : VB n (-x) := by
  intro m hm; rw [map_neg, hx m hm, neg_zero]

theorem VB.of_zero (n : ℕ) : VB n (0 : PowerSeries k) := fun m _ => by simp

theorem VB.smul {n : ℕ} {x : PowerSeries k} (hx : VB n x) (c : k) : VB n (c • x) := by
  intro m hm; rw [map_smul, hx m hm, smul_zero]

theorem VB.C_mul {n : ℕ} {x : PowerSeries k} (hx : VB n x) (c : k) : VB n (PowerSeries.C c * x) := by
  intro m hm; rw [PowerSeries.coeff_C_mul, hx m hm, mul_zero]

theorem VB.mul {n n' : ℕ} {x y : PowerSeries k} (hx : VB n x) (hy : VB n' y) : VB (n + n') (x * y) := by
  intro m hm
  rw [PowerSeries.coeff_mul]
  refine Finset.sum_eq_zero (fun p hp => ?_)
  have hpm : p.1 + p.2 = m := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  by_cases h1 : p.1 < n
  · rw [hx p.1 h1, zero_mul]
  · have h2 : p.2 < n' := by omega
    rw [hy p.2 h2, mul_zero]

theorem VB.mul_right {n : ℕ} {x : PowerSeries k} (hx : VB n x) (y : PowerSeries k) : VB n (x * y) := by
  have := VB.mul hx (VB.zero_le (x := y))
  simpa using this

theorem VB.mul_left {n : ℕ} {y : PowerSeries k} (x : PowerSeries k) (hy : VB n y) : VB n (x * y) := by
  have := VB.mul (VB.zero_le (x := x)) hy
  simpa using this

theorem VB.pow {n : ℕ} {x : PowerSeries k} (hx : VB n x) : ∀ j : ℕ, VB (n * j) (x ^ j)
  | 0 => by simpa using (VB.zero_le (x := (1 : PowerSeries k)))
  | j + 1 => by
    rw [pow_succ, Nat.mul_succ]
    exact VB.mul (VB.pow hx j) hx

theorem VB.of_X_pow (j : ℕ) : VB j ((PowerSeries.X : PowerSeries k) ^ j) := by
  intro m hm
  rw [PowerSeries.coeff_X_pow, if_neg (by omega)]

theorem VB.of_X : VB 1 (PowerSeries.X : PowerSeries k) := by
  simpa using VB.of_X_pow (k := k) 1

theorem VB.of_constantCoeff {x : PowerSeries k} (h : PowerSeries.constantCoeff x = 0) : VB 1 x := by
  intro m hm
  have : m = 0 := by omega
  subst this
  simpa using h

theorem VB.eq_zero {x : PowerSeries k} (h : ∀ n, VB n x) : x = 0 := by
  ext m; exact (h (m + 1)) m (Nat.lt_succ_self m)

theorem VB.pow_sub_pow {n : ℕ} {φ φ' : PowerSeries k} (hφ : VB 1 φ) (hφ' : VB 1 φ') (h : VB n (φ - φ')) :
    ∀ j : ℕ, 1 ≤ j → VB (n + j - 1) (φ ^ j - φ' ^ j)
  | 0 => fun h0 => absurd h0 (by omega)
  | 1 => fun _ => by simpa using h
  | j + 2 => fun _ => by
    have ih := VB.pow_sub_pow hφ hφ' h (j + 1) (by omega)
    have e : φ ^ (j + 2) - φ' ^ (j + 2) = φ * (φ ^ (j + 1) - φ' ^ (j + 1)) + (φ - φ') * φ' ^ (j + 1) := by ring
    rw [e]
    refine VB.add ?_ ?_
    · have := VB.mul hφ ih
      exact this.mono (by omega)
    · have := VB.mul h (VB.pow hφ' (j + 1))
      exact this.mono (by omega)

noncomputable abbrev Sb (φ : PowerSeries k) : Fin 2 → PowerSeries k := ![(PowerSeries.X : PowerSeries k), φ]

theorem hasSubst_Sb {φ : PowerSeries k} (hφ : PowerSeries.constantCoeff φ = 0) : HasSubst (Sb φ) := by
  apply hasSubst_of_constantCoeff_zero
  intro s
  fin_cases s
  · show MvPowerSeries.constantCoeff (PowerSeries.X : PowerSeries k) = 0
    exact PowerSeries.constantCoeff_X
  · show MvPowerSeries.constantCoeff φ = 0
    exact hφ

noncomputable abbrev Φ (f : MvPowerSeries (Fin 2) k) (φ : PowerSeries k) : PowerSeries k := subst (Sb φ) f

theorem prod_Sb (φ : PowerSeries k) (d : Fin 2 →₀ ℕ) :
    (d.prod fun s e => (Sb φ s) ^ e) = (PowerSeries.X : PowerSeries k) ^ (d 0) * φ ^ (d 1) := by
  rw [Finsupp.prod_fintype _ _ (fun i => by simp), Fin.prod_univ_two]
  rfl

theorem VB.subst_sub_subst {N n : ℕ} {f : MvPowerSeries (Fin 2) k} (hf : (N : ℕ∞) ≤ f.order)
    {φ φ' : PowerSeries k} (hφ : PowerSeries.constantCoeff φ = 0) (hφ' : PowerSeries.constantCoeff φ' = 0)
    (h : VB n (φ - φ')) : VB (n + N - 1) (Φ f φ - Φ f φ') := by
  classical
  intro m hm
  show MvPowerSeries.coeff (Finsupp.single () m) (Φ f φ - Φ f φ') = 0
  rw [map_sub, coeff_subst (hasSubst_Sb hφ), coeff_subst (hasSubst_Sb hφ'),
    ← finsum_sub_distrib (coeff_subst_finite (hasSubst_Sb hφ) f _) (coeff_subst_finite (hasSubst_Sb hφ') f _)]
  refine finsum_eq_zero_of_forall_eq_zero (fun d => ?_)
  by_cases hd : MvPowerSeries.coeff d f = 0
  · simp [hd]
  rw [← smul_sub, prod_Sb, prod_Sb]

  have hdeg : N ≤ d 0 + d 1 := by
    by_contra hlt
    push_neg at hlt
    apply hd
    apply MvPowerSeries.coeff_of_lt_order
    refine lt_of_lt_of_le ?_ hf
    have : (Finsupp.degree d : ℕ) = d 0 + d 1 := by
      have hd' : Finsupp.single (0 : Fin 2) (d 0) + Finsupp.single 1 (d 1) = d := by
        ext t; fin_cases t <;> simp
      conv_lhs => rw [← hd']
      rw [map_add, Finsupp.degree_single, Finsupp.degree_single]
    exact_mod_cast (this ▸ hlt : Finsupp.degree d < N)

  have hv : VB (n + N - 1) ((PowerSeries.X : PowerSeries k) ^ (d 0) * φ ^ (d 1) -
      (PowerSeries.X : PowerSeries k) ^ (d 0) * φ' ^ (d 1)) := by
    rcases Nat.eq_zero_or_pos (d 1) with h1 | h1
    · rw [h1, pow_zero, pow_zero, sub_self]; exact VB.of_zero _
    · rw [← mul_sub]
      have := VB.mul (VB.of_X_pow (k := k) (d 0))
        (VB.pow_sub_pow (VB.of_constantCoeff hφ) (VB.of_constantCoeff hφ') h (d 1) h1)
      exact this.mono (by omega)
  have := hv m hm
  rw [show PowerSeries.coeff m = MvPowerSeries.coeff (Finsupp.single () m) from rfl, map_sub] at this
  rw [this, smul_zero]

theorem le_order_of_mem_pow {R : Type*} [CommRing R] (m : ℕ) (g : MvPowerSeries (Fin 2) R)
    (hg : g ∈ Ideal.span {(X 0 : MvPowerSeries (Fin 2) R), X 1} ^ m) : (m : ℕ∞) ≤ g.order := by
  induction m generalizing g with
  | zero => simp
  | succ m ih =>
    rw [pow_succ] at hg
    refine Submodule.mul_induction_on hg (fun a ha b hb => ?_) (fun a b ha hb => ?_)
    · have h1 : (m : ℕ∞) ≤ a.order := ih a ha
      have h2 : (1 : ℕ∞) ≤ b.order := by
        rw [one_le_order_iff_constCoeff_eq_zero]
        obtain ⟨c₀, c₁, rfl⟩ := Ideal.mem_span_pair.mp hb
        simp
      calc ((m + 1 : ℕ) : ℕ∞) = m + 1 := by push_cast; rfl
        _ ≤ a.order + b.order := add_le_add h1 h2
        _ ≤ (a * b).order := le_order_mul
    · exact le_trans (le_min ha hb) min_order_le_add

theorem VB.subst_of_le_order {N : ℕ} {f : MvPowerSeries (Fin 2) k} (hf : (N : ℕ∞) ≤ f.order)
    {ψ : PowerSeries k} (hψ : PowerSeries.constantCoeff ψ = 0) : VB N (Φ f ψ) := by
  have hX : (1 : ℕ∞) ≤ MvPowerSeries.order (PowerSeries.X : PowerSeries k) := by
    rw [one_le_order_iff_constCoeff_eq_zero]; exact PowerSeries.constantCoeff_X
  have hψ1 : (1 : ℕ∞) ≤ MvPowerSeries.order ψ := by
    rw [one_le_order_iff_constCoeff_eq_zero]; exact hψ
  have h1 : (1 : ℕ∞) ≤ ⨅ i, MvPowerSeries.order (Sb ψ i) := by
    refine le_iInf (fun i => ?_)
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun l => l.elim0) j) i
    · simpa [Sb] using hX
    · simpa [Sb] using hψ1
  have hord : (N : ℕ∞) ≤ MvPowerSeries.order (Φ f ψ) := by
    refine le_trans ?_ (le_order_subst (hasSubst_Sb hψ) f)
    calc (N : ℕ∞) ≤ f.order := hf
      _ = 1 * f.order := (one_mul _).symm
      _ ≤ (⨅ i, MvPowerSeries.order (Sb ψ i)) * f.order := mul_le_mul_left h1 _
  intro m hm
  show MvPowerSeries.coeff (Finsupp.single () m) (Φ f ψ) = 0
  apply MvPowerSeries.coeff_of_lt_order
  refine lt_of_lt_of_le ?_ hord
  rw [Finsupp.degree_single]
  exact_mod_cast hm

theorem subst_form {φ : PowerSeries k} (hφ : PowerSeries.constantCoeff φ = 0) (q : ℕ) :
    Φ (X 0 * X 1 ^ q - X 0 ^ q * X 1) φ = PowerSeries.X * φ ^ q - PowerSeries.X ^ q * φ := by
  have ha := hasSubst_Sb hφ
  show subst (Sb φ) (X 0 * X 1 ^ q - X 0 ^ q * X 1) = _
  rw [subst_sub ha, subst_mul ha, subst_mul ha, subst_pow ha, subst_pow ha, subst_X ha, subst_X ha]
  rfl

section CharQ

variable (q : ℕ) [Fact q.Prime] [CharP k q]

theorem VB.perturb {f : MvPowerSeries (Fin 2) k}
    (hf : f - (X 0 * X 1 ^ q - X 0 ^ q * X 1) ∈ (Ideal.span {(X 0 : MvPowerSeries (Fin 2) k), X 1}) ^ (q + 2))
    {φ : PowerSeries k} (hφ : PowerSeries.constantCoeff φ = 0) (n : ℕ) (hn : 2 ≤ n) (δ : k) :
    VB (n + q + 1) (Φ f (φ + PowerSeries.C δ * PowerSeries.X ^ n) - Φ f φ +
      PowerSeries.C δ * PowerSeries.X ^ (n + q)) := by
  have hq2 : 2 ≤ q := (Fact.out : q.Prime).two_le
  set φ' := φ + PowerSeries.C δ * PowerSeries.X ^ n with hφ'def
  have hφ' : PowerSeries.constantCoeff φ' = 0 := by
    rw [hφ'def, map_add, hφ, map_mul, ← PowerSeries.coeff_zero_eq_constantCoeff_apply (PowerSeries.X ^ n),
      PowerSeries.coeff_X_pow, if_neg (by omega), mul_zero, add_zero]
  set g := f - (X 0 * X 1 ^ q - X 0 ^ q * X 1) with hg
  have hgord : ((q + 2 : ℕ) : ℕ∞) ≤ g.order := le_order_of_mem_pow (q + 2) g hf
  have hfg : f = (X 0 * X 1 ^ q - X 0 ^ q * X 1) + g := by rw [hg]; ring
  have hΦ : ∀ ψ : PowerSeries k, PowerSeries.constantCoeff ψ = 0 →
      Φ f ψ = (PowerSeries.X * ψ ^ q - PowerSeries.X ^ q * ψ) + Φ g ψ := by
    intro ψ hψ
    rw [← subst_form hψ q]
    show subst (Sb ψ) f = subst (Sb ψ) _ + subst (Sb ψ) g
    rw [← subst_add (hasSubst_Sb hψ), ← hfg]

  haveI : CharP (PowerSeries k) q := by
    refine charP_of_injective_algebraMap (R := k) (A := PowerSeries k) (fun a b h => ?_) q
    have := congrArg PowerSeries.constantCoeff h
    simpa using this
  have hfrob : φ' ^ q = φ ^ q + (PowerSeries.C δ * PowerSeries.X ^ n) ^ q := by
    rw [hφ'def]; exact add_pow_char _ _ q
  have key : Φ f φ' - Φ f φ + PowerSeries.C δ * PowerSeries.X ^ (n + q) =
      PowerSeries.C (δ ^ q) * PowerSeries.X ^ (n * q + 1) + (Φ g φ' - Φ g φ) := by
    rw [hΦ φ' hφ', hΦ φ hφ, hfrob, hφ'def, mul_pow, ← map_pow, ← pow_mul, pow_add, pow_succ]
    ring
  rw [key]
  refine VB.add ?_ ?_
  · have := (VB.of_X_pow (k := k) (n * q + 1)).C_mul (δ ^ q)
    refine this.mono ?_
    nlinarith
  · have hδ : VB n (φ' - φ) := by
      rw [hφ'def, add_sub_cancel_left]
      exact (VB.of_X_pow n).C_mul δ
    have := VB.subst_sub_subst hgord hφ' hφ hδ
    exact this.mono (by omega)

end CharQ

end NewtonBranch

open NewtonBranch in

theorem solution
    (q : ℕ) [Fact q.Prime] (k : Type*) [Field k] (hq : (q : k) = 0)
    (f : MvPowerSeries (Fin 2) k)
    (hf : f - (X 0 * X 1 ^ q - X 0 ^ q * X 1) ∈ (Ideal.span {(X 0 : MvPowerSeries (Fin 2) k), X 1}) ^ (q + 2))
    (a : k) (ha : a ^ q = a) :
    ∃ φ : PowerSeries k,
      PowerSeries.constantCoeff φ = 0 ∧ PowerSeries.coeff 1 φ = a ∧
      MvPowerSeries.subst ![(PowerSeries.X : PowerSeries k), φ] f = 0 := by
  classical
  have hqp : q.Prime := Fact.out
  have hq2 : 2 ≤ q := hqp.two_le
  haveI : CharP k q := (CharP.charP_iff_prime_eq_zero hqp).mpr hq

  have hford : (1 : ℕ∞) ≤ f.order := by
    rw [one_le_order_iff_constCoeff_eq_zero]
    have hg := le_order_of_mem_pow (q + 2) _ hf
    have h1 : (1 : ℕ∞) ≤ (f - (X 0 * X 1 ^ q - X 0 ^ q * X 1)).order :=
      le_trans (by exact_mod_cast (by omega : 1 ≤ q + 2)) hg
    rw [one_le_order_iff_constCoeff_eq_zero, map_sub] at h1
    have : MvPowerSeries.constantCoeff (X 0 * X 1 ^ q - X 0 ^ q * X 1 : MvPowerSeries (Fin 2) k) = 0 := by
      simp [show q ≠ 0 by omega]
    rw [this, sub_zero] at h1
    exact h1

  let step : PowerSeries k → ℕ → PowerSeries k := fun s n =>
    s + PowerSeries.C (PowerSeries.coeff (n + 2 + q) (Φ f s)) * PowerSeries.X ^ (n + 2)
  let sq : ℕ → PowerSeries k := fun n => Nat.rec (motive := fun _ => PowerSeries k)
    (PowerSeries.C a * PowerSeries.X) (fun n s => step s n) n
  have sq_zero : sq 0 = PowerSeries.C a * PowerSeries.X := rfl
  have sq_succ : ∀ n, sq (n + 1) =
      sq n + PowerSeries.C (PowerSeries.coeff (n + 2 + q) (Φ f (sq n))) * PowerSeries.X ^ (n + 2) := fun n => rfl

  have hI : ∀ n, PowerSeries.constantCoeff (sq n) = 0 ∧ PowerSeries.coeff 1 (sq n) = a ∧
      VB (n + q + 2) (Φ f (sq n)) := by
    intro n
    induction n with
    | zero =>
      have h0 : PowerSeries.constantCoeff (sq 0) = 0 := by
        rw [sq_zero, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_C_mul,
          PowerSeries.coeff_zero_X, mul_zero]
      refine ⟨h0, ?_, ?_⟩
      · rw [sq_zero, PowerSeries.coeff_C_mul, PowerSeries.coeff_one_X, mul_one]
      ·
        set g := f - (X 0 * X 1 ^ q - X 0 ^ q * X 1) with hg
        have hgord : ((q + 2 : ℕ) : ℕ∞) ≤ g.order := le_order_of_mem_pow (q + 2) g hf
        have hfg : f = (X 0 * X 1 ^ q - X 0 ^ q * X 1) + g := by rw [hg]; ring
        have hΦ : Φ f (sq 0) = (PowerSeries.X * (sq 0) ^ q - PowerSeries.X ^ q * (sq 0)) + Φ g (sq 0) := by
          rw [← subst_form h0 q]
          show subst (Sb (sq 0)) f = subst (Sb (sq 0)) _ + subst (Sb (sq 0)) g
          rw [← subst_add (hasSubst_Sb h0), ← hfg]
        have hvan : PowerSeries.X * (sq 0) ^ q - PowerSeries.X ^ q * (sq 0) = 0 := by
          rw [sq_zero, mul_pow, ← map_pow, ha]; ring
        rw [hΦ, hvan]
        have hh := VB.subst_of_le_order (N := q + 2) hgord h0
        simpa using hh
    | succ n ih =>
      obtain ⟨h0, h1, hv⟩ := ih
      set δ := PowerSeries.coeff (n + 2 + q) (Φ f (sq n)) with hδ
      have hs : sq (n + 1) = sq n + PowerSeries.C δ * PowerSeries.X ^ (n + 2) := sq_succ n
      have h0' : PowerSeries.constantCoeff (sq (n + 1)) = 0 := by
        rw [hs, map_add, h0, map_mul, ← PowerSeries.coeff_zero_eq_constantCoeff_apply (PowerSeries.X ^ (n + 2)),
          PowerSeries.coeff_X_pow, if_neg (by omega), mul_zero, add_zero]
      refine ⟨h0', ?_, ?_⟩
      · rw [hs, map_add, h1, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow, if_neg (by omega), mul_zero, add_zero]
      · have hp := VB.perturb q hf h0 (n + 2) (by omega) δ
        rw [← hs] at hp
        intro m hm
        have e : Φ f (sq (n + 1)) = (Φ f (sq (n + 1)) - Φ f (sq n) + PowerSeries.C δ * PowerSeries.X ^ (n + 2 + q)) +
            Φ f (sq n) - PowerSeries.C δ * PowerSeries.X ^ (n + 2 + q) := by ring
        rw [e, map_sub, map_add, hp m (by omega), zero_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]
        by_cases hmq : m = n + 2 + q
        · subst hmq
          rw [if_pos rfl, mul_one, ← hδ, sub_self]
        · rw [if_neg hmq, mul_zero, sub_zero]
          exact hv m (by omega)

  have hstab : ∀ m N, m ≤ N → PowerSeries.coeff m (sq N) = PowerSeries.coeff m (sq m) := by
    intro m N hmN
    induction N with
    | zero =>
      have : m = 0 := by omega
      subst this; rfl
    | succ N ih =>
      rcases Nat.eq_or_lt_of_le hmN with h | h
      · rw [h]
      · rw [sq_succ, map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow, if_neg (by omega), mul_zero,
          add_zero, ih (by omega)]

  let φ : PowerSeries k := PowerSeries.mk (fun m => PowerSeries.coeff m (sq m))
  have hφsq : ∀ N, VB (N + 1) (φ - sq N) := by
    intro N m hm
    rw [map_sub, PowerSeries.coeff_mk, hstab m N (by omega), sub_self]
  have hφ0 : PowerSeries.constantCoeff φ = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk]
    exact (PowerSeries.coeff_zero_eq_constantCoeff_apply (sq 0)).trans (hI 0).1
  refine ⟨φ, hφ0, ?_, ?_⟩
  · rw [PowerSeries.coeff_mk]; exact (hI 1).2.1
  · apply VB.eq_zero
    intro M
    have h1 := VB.subst_sub_subst (N := 1) hford hφ0 (hI M).1 (hφsq M)
    have h2 := (hI M).2.2
    have e : Φ f φ = (Φ f φ - Φ f (sq M)) + Φ f (sq M) := by ring
    show VB M (Φ f φ)
    rw [e]
    exact VB.add (h1.mono (by omega)) (h2.mono (by omega))

end S_MvPowerSeries_exists_powerSeries_subst_eq_zero_of_sub_drinfeld_mem_pow
end P2MW
export P2MW.S_MvPowerSeries_exists_powerSeries_subst_eq_zero_of_sub_drinfeld_mem_pow (solution)
