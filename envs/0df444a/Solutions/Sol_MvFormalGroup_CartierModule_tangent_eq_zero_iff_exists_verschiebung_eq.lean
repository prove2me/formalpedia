-- Prove2me | solution 1 for MvFormalGroup.CartierModule.tangent_eq_zero_iff_exists_verschiebung_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/4f39f875-dff3-5748-b668-1e8df4564d9d

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Theorems.Thm_MvFormalGroup_coeff_eq_zero_of_linearPart_eq_zero_of_subst_eq_charP
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvFormalGroup_CartierModule_tangent_eq_zero_iff_exists_verschiebung_eq

set_option autoImplicit false

universe u

noncomputable section

open MvPowerSeries

namespace CartierVReducedSol

variable {p : ℕ} [hp : Fact p.Prime] {R : Type u} [CommRing R] {d : ℕ}

def contract (p : ℕ) {σ : Type*} (F : MvPowerSeries σ R) : MvPowerSeries σ R :=
  fun e => coeff (p • e) F

omit hp in
theorem coeff_contract {σ : Type*} (F : MvPowerSeries σ R) (e : σ →₀ ℕ) :
    coeff e (contract p F) = coeff (p • e) F := rfl

theorem expand_contract {σ : Type*} (F : MvPowerSeries σ R)
    (hF : ∀ e : σ →₀ ℕ, (∃ i, ¬ p ∣ e i) → coeff e F = 0) :
    expand p hp.out.ne_zero (contract p F) = F := by
  ext e
  by_cases h : ∀ i, p ∣ e i
  · obtain ⟨m, rfl⟩ : ∃ m : σ →₀ ℕ, p • m = e :=
      ⟨e.mapRange (fun a => a / p) (by simp),
        by ext i; simp [Nat.mul_div_cancel' (h i)]⟩
    rw [coeff_expand_smul, coeff_contract]
  · push Not at h
    obtain ⟨i, hi⟩ := h
    rw [coeff_expand_of_not_dvd p hp.out.ne_zero _ hi, hF e ⟨i, hi⟩]

omit hp in
theorem constantCoeff_contract {σ : Type*} (F : MvPowerSeries σ R) (hF : F.constantCoeff = 0) :
    (contract p F).constantCoeff = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_contract, smul_zero,
    coeff_zero_eq_constantCoeff_apply, hF]

theorem expand_injective {σ : Type*} :
    Function.Injective (expand p hp.out.ne_zero : MvPowerSeries σ R → MvPowerSeries σ R) := by
  intro F G h
  ext e
  have := congrArg (coeff (p • e)) h
  rwa [coeff_expand_smul, coeff_expand_smul] at this

theorem pow_eq_expand_map_frobenius [CharP R p] {σ : Type*} (F : MvPowerSeries σ R) :
    F ^ p = expand p hp.out.ne_zero (map (frobenius R p) F) := by
  haveI : ExpChar R p := ExpChar.prime hp.out
  rw [← map_expand, map_frobenius_expand]

section Generic

variable {τ : Type*}

omit hp in
theorem weightedHomogeneousComponent_zero_one (w : τ → ℕ) :
    weightedHomogeneousComponent w 0 (1 : MvPowerSeries τ R) = 1 := by
  classical
  ext e
  rw [coeff_weightedHomogeneousComponent, coeff_one]
  by_cases he : e = 0
  · subst he
    rw [if_pos (map_zero _)]
  · rw [if_neg he, ite_self]

omit hp in
theorem weightedHomogeneousComponent_zero_mul (w : τ → ℕ) (F G : MvPowerSeries τ R) :
    weightedHomogeneousComponent w 0 (F * G) =
      weightedHomogeneousComponent w 0 F * weightedHomogeneousComponent w 0 G := by
  have := weightedHomogeneousComponent_mul_of_le_weightedOrder (w := w) (f := F) (g := G)
    (p := 0) (q := 0) bot_le bot_le
  simpa using this

omit hp in
theorem weightedHomogeneousComponent_zero_pow (w : τ → ℕ) (F : MvPowerSeries τ R) (n : ℕ) :
    weightedHomogeneousComponent w 0 (F ^ n) = weightedHomogeneousComponent w 0 F ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, weightedHomogeneousComponent_zero_one]
  | succ n ih => rw [pow_succ, pow_succ, weightedHomogeneousComponent_zero_mul, ih]

omit hp in
theorem weightedHomogeneousComponent_zero_prod {ι : Type*} (w : τ → ℕ) (s : Finset ι)
    (F : ι → MvPowerSeries τ R) :
    weightedHomogeneousComponent w 0 (∏ i ∈ s, F i) =
      ∏ i ∈ s, weightedHomogeneousComponent w 0 (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.prod_empty, weightedHomogeneousComponent_zero_one]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, weightedHomogeneousComponent_zero_mul, ih]

omit hp in

theorem coeff_eq_zero_of_weightedHomogeneousComponent_zero_eq (w : τ → ℕ) {F : MvPowerSeries τ R}
    (hF : weightedHomogeneousComponent w 0 F = F) {E : τ →₀ ℕ} (hE : Finsupp.weight w E ≠ 0) :
    coeff E F = 0 := by
  rw [← hF, coeff_weightedHomogeneousComponent, if_neg hE]

omit hp in
theorem homogeneousComponent_zero_one' :
    homogeneousComponent 0 (1 : MvPowerSeries τ R) = 1 :=
  weightedHomogeneousComponent_zero_one _

omit hp in
theorem one_le_order_of_constantCoeff_eq_zero {c : MvPowerSeries τ R} (hc : c.constantCoeff = 0) :
    (1 : ℕ∞) ≤ c.order := by
  have h := le_order_pow_of_constantCoeff_eq_zero 1 hc
  rwa [pow_one, Nat.cast_one] at h

omit hp in

theorem homogeneousComponent_pow_of_constantCoeff_eq_zero {c : MvPowerSeries τ R}
    (hc : c.constantCoeff = 0) (n : ℕ) :
    homogeneousComponent n (c ^ n) = homogeneousComponent 1 c ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, homogeneousComponent_zero_one']
  | succ n ih =>
    rw [pow_succ, pow_succ, homogeneousComponent_mul_of_le_order, ih]
    · exact le_order_pow_of_constantCoeff_eq_zero n hc
    · exact one_le_order_of_constantCoeff_eq_zero hc

omit hp in

theorem homogeneousComponent_finsuppProd {ι : Type*} {c : ι → MvPowerSeries τ R}
    (hc : ∀ i, (c i).constantCoeff = 0) (e : ι →₀ ℕ) :
    homogeneousComponent e.degree (e.prod fun i n => c i ^ n) =
      e.prod fun i n => homogeneousComponent 1 (c i) ^ n := by
  classical
  induction e using Finsupp.induction with
  | zero => rw [Finsupp.prod_zero_index, Finsupp.prod_zero_index, map_zero,
      homogeneousComponent_zero_one']
  | single_add a b f ha hb ih =>
    rw [Finsupp.prod_add_index' (h := fun i n => c i ^ n) (fun _ => pow_zero _)
        (fun _ _ _ => pow_add _ _ _),
      Finsupp.prod_add_index' (h := fun i n => homogeneousComponent 1 (c i) ^ n)
        (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _),
      Finsupp.prod_single_index (h := fun i n => c i ^ n) (pow_zero _),
      Finsupp.prod_single_index (h := fun i n => homogeneousComponent 1 (c i) ^ n) (pow_zero _),
      map_add, Finsupp.degree_single, homogeneousComponent_mul_of_le_order,
      homogeneousComponent_pow_of_constantCoeff_eq_zero (hc a), ih]
    · exact le_order_pow_of_constantCoeff_eq_zero b (hc a)
    · exact MvFormalGroup.le_order_finsuppProd_pow hc f

end Generic

section Pair

def pr (a b : ℕ →₀ ℕ) : Fin 2 × ℕ →₀ ℕ :=
  a.mapDomain (Prod.mk 0) + b.mapDomain (Prod.mk 1)

theorem not_mem_range_mk {i j : Fin 2} (h : i ≠ j) (k : ℕ) :
    ((i, k) : Fin 2 × ℕ) ∉ Set.range (Prod.mk j) := by
  rintro ⟨m, hm⟩
  exact h (congrArg Prod.fst hm).symm

@[scoped simp] theorem pr_apply_zero (a b : ℕ →₀ ℕ) (k : ℕ) : pr a b (0, k) = a k := by
  rw [pr, Finsupp.add_apply, Finsupp.mapDomain_apply (Prod.mk_right_injective 0),
    Finsupp.mapDomain_notin_range _ _ (not_mem_range_mk (by decide) k), add_zero]

@[scoped simp] theorem pr_apply_one (a b : ℕ →₀ ℕ) (k : ℕ) : pr a b (1, k) = b k := by
  rw [pr, Finsupp.add_apply, Finsupp.mapDomain_apply (Prod.mk_right_injective 1),
    Finsupp.mapDomain_notin_range _ _ (not_mem_range_mk (by decide) k), zero_add]

theorem pr_ext_iff {a b a' b' : ℕ →₀ ℕ} : pr a b = pr a' b' ↔ a = a' ∧ b = b' := by
  constructor
  · intro h
    refine ⟨Finsupp.ext fun k => ?_, Finsupp.ext fun k => ?_⟩
    · simpa using DFunLike.congr_fun h (0, k)
    · simpa using DFunLike.congr_fun h (1, k)
  · rintro ⟨rfl, rfl⟩; rfl

theorem pr_add (a b a' b' : ℕ →₀ ℕ) : pr a b + pr a' b' = pr (a + a') (b + b') := by
  ext ⟨i, k⟩
  fin_cases i <;> simp

theorem pr_le_iff {a b a' b' : ℕ →₀ ℕ} : pr a b ≤ pr a' b' ↔ a ≤ a' ∧ b ≤ b' := by
  constructor
  · intro h
    exact ⟨fun k => by simpa using h (0, k), fun k => by simpa using h (1, k)⟩
  · rintro ⟨ha, hb⟩ ⟨i, k⟩
    fin_cases i
    · simpa using ha k
    · simpa using hb k

theorem pr_tsub (a b a' b' : ℕ →₀ ℕ) : pr a b - pr a' b' = pr (a - a') (b - b') := by
  ext ⟨i, k⟩
  fin_cases i <;> simp

theorem pr_zero_zero : pr 0 0 = 0 := by
  ext ⟨i, k⟩; fin_cases i <;> simp

theorem single_zero_eq_pr (k n : ℕ) :
    Finsupp.single (((0 : Fin 2), k) : Fin 2 × ℕ) n = pr (Finsupp.single k n) 0 := by
  rw [pr, Finsupp.mapDomain_single, Finsupp.mapDomain_zero, add_zero]

theorem single_one_eq_pr (k n : ℕ) :
    Finsupp.single (((1 : Fin 2), k) : Fin 2 × ℕ) n = pr 0 (Finsupp.single k n) := by
  rw [pr, Finsupp.mapDomain_single, Finsupp.mapDomain_zero, zero_add]

theorem mapDomain_zero_eq_pr (a : ℕ →₀ ℕ) : a.mapDomain (Prod.mk (0 : Fin 2)) = pr a 0 := by
  rw [pr, Finsupp.mapDomain_zero, add_zero]

theorem mapDomain_one_eq_pr (b : ℕ →₀ ℕ) : b.mapDomain (Prod.mk (1 : Fin 2)) = pr 0 b := by
  rw [pr, Finsupp.mapDomain_zero, zero_add]

def wOne : Fin 2 × ℕ → ℕ := fun ik => (ik.1 : ℕ)

theorem weight_wOne_pr (a b : ℕ →₀ ℕ) : Finsupp.weight wOne (pr a b) = b.degree := by
  rw [pr, map_add, Finsupp.weight_apply, Finsupp.weight_apply,
    Finsupp.sum_mapDomain_index_inj (Prod.mk_right_injective 0),
    Finsupp.sum_mapDomain_index_inj (Prod.mk_right_injective 1)]
  simp [wOne, Finsupp.degree_apply, Finsupp.sum]

theorem degree_pr (a b : ℕ →₀ ℕ) : (pr a b).degree = a.degree + b.degree := by
  rw [pr, map_add, Finsupp.degree_mapDomain, Finsupp.degree_mapDomain]

end Pair

namespace WittAux

def killTo (i : Fin 2) : Fin 2 × ℕ → MvPolynomial ℕ ℤ :=
  fun ik => if ik.1 = i then MvPolynomial.X ik.2 else 0

theorem mapDomain_mk_tsub (i : Fin 2) (x y : ℕ →₀ ℕ) :
    (x - y).mapDomain (Prod.mk i) = x.mapDomain (Prod.mk i) - y.mapDomain (Prod.mk i) := by
  ext ⟨i', k⟩
  by_cases h : i' = i
  · subst h
    simp [Finsupp.mapDomain_apply (Prod.mk_right_injective i')]
  · have hnot : ∀ z : ℕ →₀ ℕ, z.mapDomain (Prod.mk i) (i', k) = 0 := fun z =>
      Finsupp.mapDomain_notin_range _ _ (not_mem_range_mk h k)
    simp [hnot]

theorem coeff_aeval_killTo (i : Fin 2) (P : MvPolynomial (Fin 2 × ℕ) ℤ) (x : ℕ →₀ ℕ) :
    MvPolynomial.coeff x (MvPolynomial.aeval (killTo i) P) =
      MvPolynomial.coeff (x.mapDomain (Prod.mk i)) P := by
  classical
  induction P using MvPolynomial.induction_on generalizing x with
  | C a =>
    rw [MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq, MvPolynomial.coeff_C,
      MvPolynomial.coeff_C]
    have hiff : (0 = x) ↔ (0 = x.mapDomain (Prod.mk i)) := by
      constructor
      · rintro rfl; rw [Finsupp.mapDomain_zero]
      · intro h
        exact (Finsupp.mapDomain_injective (Prod.mk_right_injective i)
          (by rw [Finsupp.mapDomain_zero]; exact h))
    by_cases hx : 0 = x
    · rw [if_pos hx, if_pos (hiff.mp hx)]
    · rw [if_neg hx, if_neg (mt hiff.mpr hx)]
  | add P Q hP hQ => simp only [map_add, MvPolynomial.coeff_add, hP, hQ]
  | mul_X P s hP =>
    rcases s with ⟨i', k⟩
    rw [map_mul, MvPolynomial.aeval_X, killTo]
    dsimp only
    split_ifs with h
    · subst h
      rw [MvPolynomial.coeff_mul_X', MvPolynomial.coeff_mul_X']
      have hiff : (i', k) ∈ (x.mapDomain (Prod.mk i')).support ↔ k ∈ x.support := by
        rw [Finsupp.mem_support_iff, Finsupp.mem_support_iff,
          Finsupp.mapDomain_apply (Prod.mk_right_injective i')]
      by_cases hle : k ∈ x.support
      · rw [if_pos hle, if_pos (hiff.mpr hle), hP, mapDomain_mk_tsub, Finsupp.mapDomain_single]
      · rw [if_neg hle, if_neg (mt hiff.mp hle)]
    · rw [mul_zero, MvPolynomial.coeff_zero, MvPolynomial.coeff_mul_X', if_neg]
      rw [Finsupp.mem_support_iff, not_ne_iff]
      exact Finsupp.mapDomain_notin_range _ _ (not_mem_range_mk h k)

theorem aeval_killTo_zero_wittAdd (k : ℕ) :
    MvPolynomial.aeval (killTo 0) (WittVector.wittAdd p k) = MvPolynomial.X k := by
  let A := MvPolynomial ℕ ℤ
  let x : WittVector p A := WittVector.mk p fun m => MvPolynomial.X m
  have key := congrArg (fun z : WittVector p A => z.coeff k) (add_zero x)
  rw [WittVector.add_coeff] at key
  have hval : Function.uncurry ![x.coeff, (0 : WittVector p A).coeff] = killTo 0 := by
    funext ⟨i, m⟩
    fin_cases i
    · rfl
    · simp [killTo, WittVector.zero_coeff]
  change MvPolynomial.aeval (Function.uncurry ![x.coeff, (0 : WittVector p A).coeff])
    (WittVector.wittAdd p k) = _ at key
  rw [hval] at key
  exact key

theorem aeval_killTo_one_wittAdd (k : ℕ) :
    MvPolynomial.aeval (killTo 1) (WittVector.wittAdd p k) = MvPolynomial.X k := by
  let A := MvPolynomial ℕ ℤ
  let x : WittVector p A := WittVector.mk p fun m => MvPolynomial.X m
  have key := congrArg (fun z : WittVector p A => z.coeff k) (zero_add x)
  rw [WittVector.add_coeff] at key
  have hval : Function.uncurry ![(0 : WittVector p A).coeff, x.coeff] = killTo 1 := by
    funext ⟨i, m⟩
    fin_cases i
    · simp [killTo, WittVector.zero_coeff]
    · rfl
  change MvPolynomial.aeval (Function.uncurry ![(0 : WittVector p A).coeff, x.coeff])
    (WittVector.wittAdd p k) = _ at key
  rw [hval] at key
  exact key

theorem coeff_single_wittAdd (i : Fin 2) (k' k : ℕ) :
    MvPolynomial.coeff (Finsupp.single (i, k') 1) (WittVector.wittAdd p k) =
      if k' = k then 1 else 0 := by
  classical
  have h := coeff_aeval_killTo i (WittVector.wittAdd p k) (Finsupp.single k' 1)
  rw [Finsupp.mapDomain_single] at h
  rw [← h]
  have hX : MvPolynomial.aeval (killTo i) (WittVector.wittAdd p k) = MvPolynomial.X k := by
    fin_cases i
    · exact aeval_killTo_zero_wittAdd k
    · exact aeval_killTo_one_wittAdd k
  rw [hX, MvPolynomial.coeff_X']
  by_cases hk : k' = k
  · subst hk; simp
  · rw [if_neg (fun h' => hk (Finsupp.single_left_injective one_ne_zero h').symm), if_neg hk]

variable (R)

theorem coeff_single_addFam (ik : Fin 2 × ℕ) (k : ℕ) :
    coeff (Finsupp.single ik 1) (MvFormalGroup.WittLaw.addFam p R k) =
      if ik.2 = k then 1 else 0 := by
  rcases ik with ⟨i, k'⟩
  rw [MvFormalGroup.WittLaw.addFam, MvPolynomial.coeff_coe, MvPolynomial.coeff_map,
    coeff_single_wittAdd]
  split_ifs <;> simp

def L (k : ℕ) : MvPowerSeries (Fin 2 × ℕ) R := X (0, k) + X (1, k)

omit hp in
theorem coeff_L (k : ℕ) (e : Fin 2 × ℕ →₀ ℕ) :
    coeff e (L R k) = (if e = Finsupp.single (0, k) 1 then 1 else 0) +
      if e = Finsupp.single (1, k) 1 then 1 else 0 := by
  classical
  rw [L, map_add, coeff_X, coeff_X]

theorem homogeneousComponent_one_addFam (k : ℕ) :
    homogeneousComponent 1 (MvFormalGroup.WittLaw.addFam p R k) = L R k := by
  classical
  ext e
  rw [coeff_homogeneousComponent, coeff_L]
  by_cases he : e.degree = 1
  · obtain ⟨ik, rfl⟩ : ∃ ik, Finsupp.single ik 1 = e := by
      have hmem : e ∈ {d' : Fin 2 × ℕ →₀ ℕ | d'.degree = 1} := he
      rwa [← Finsupp.range_single_one] at hmem
    rw [if_pos he, coeff_single_addFam]
    rcases ik with ⟨i, k'⟩
    have hinj : ∀ (u v : Fin 2 × ℕ), (Finsupp.single u 1 = Finsupp.single v 1) ↔ u = v :=
      fun u v => ⟨fun h => Finsupp.single_left_injective one_ne_zero h, fun h => by rw [h]⟩
    simp only [hinj, Prod.mk.injEq]
    fin_cases i
    · by_cases hk : k' = k <;> simp [hk]
    · by_cases hk : k' = k <;> simp [hk]
  · rw [if_neg he, if_neg, if_neg, add_zero]
    · rintro rfl; exact he (Finsupp.degree_single _ _)
    · rintro rfl; exact he (Finsupp.degree_single _ _)

def T (e : ℕ →₀ ℕ) : MvPowerSeries (Fin 2 × ℕ) R := e.prod fun k n => L R k ^ n

omit hp in
theorem T_add (e e' : ℕ →₀ ℕ) : T R (e + e') = T R e * T R e' :=
  Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)

omit hp in
theorem T_single (k n : ℕ) : T R (Finsupp.single k n) = L R k ^ n :=
  Finsupp.prod_single_index (pow_zero _)

omit hp in

theorem weightedHomogeneousComponent_zero_T (e : ℕ →₀ ℕ) :
    weightedHomogeneousComponent wOne 0 (T R e) = monomial (pr e 0) (1 : R) := by
  classical
  induction e using Finsupp.induction with
  | zero =>
    rw [T, Finsupp.prod_zero_index, weightedHomogeneousComponent_zero_one, pr_zero_zero,
      monomial_zero_one]
  | single_add k n f hk hn ih =>
    rw [T_add, T_single, weightedHomogeneousComponent_zero_mul,
      weightedHomogeneousComponent_zero_pow, ih]
    have hL : weightedHomogeneousComponent wOne 0 (L R k) = X (0, k) := by
      ext e
      rw [coeff_weightedHomogeneousComponent, coeff_L, coeff_X]
      by_cases h0 : e = Finsupp.single (0, k) 1
      · subst h0
        rw [if_pos (by rw [single_zero_eq_pr, weight_wOne_pr, map_zero]), if_pos rfl, if_neg,
          add_zero]
        intro h
        have := DFunLike.congr_fun h (0, k)
        simp at this
      · rw [if_neg h0, zero_add]
        by_cases h1 : e = Finsupp.single (1, k) 1
        · subst h1
          rw [if_neg]
          rw [single_one_eq_pr, weight_wOne_pr, Finsupp.degree_single]; exact one_ne_zero
        · rw [if_neg h1, ite_self]
    rw [hL, X_pow_eq, monomial_mul_monomial, one_mul, single_zero_eq_pr, pr_add, zero_add]

omit hp in

theorem coeff_T_eq_zero_of_notMem_support (e : ℕ →₀ ℕ) {m : ℕ} (hm : m ∉ e.support)
    {E : Fin 2 × ℕ →₀ ℕ} (hE : E (1, m) ≠ 0) : coeff E (T R e) = 0 := by
  classical
  set w' : Fin 2 × ℕ → ℕ := Pi.single ((1 : Fin 2), m) 1 with hw'
  have hL : ∀ k ∈ e.support, weightedHomogeneousComponent w' 0 (L R k) = L R k := by
    intro k hk
    have hkm : k ≠ m := fun h => hm (h ▸ hk)
    ext e'
    rw [coeff_weightedHomogeneousComponent]
    split_ifs with h
    · rfl
    · symm
      rw [coeff_L, if_neg, if_neg, add_zero]
      · rintro rfl
        apply h
        rw [Finsupp.weight_single_one_apply, Finsupp.single_apply, if_neg]
        intro h'; exact hkm (Prod.mk.inj h').2
      · rintro rfl
        apply h
        rw [Finsupp.weight_single_one_apply, Finsupp.single_apply, if_neg]
        intro h'; exact absurd (Prod.mk.inj h').1 (by decide)
  have hT : weightedHomogeneousComponent w' 0 (T R e) = T R e := by
    show weightedHomogeneousComponent w' 0 (∏ k ∈ e.support, L R k ^ e k) =
      ∏ k ∈ e.support, L R k ^ e k
    rw [weightedHomogeneousComponent_zero_prod]
    refine Finset.prod_congr rfl fun k hk => ?_
    rw [weightedHomogeneousComponent_zero_pow, hL k hk]
  refine coeff_eq_zero_of_weightedHomogeneousComponent_zero_eq w' hT ?_
  rwa [Finsupp.weight_single_one_apply]

omit hp in
theorem one_le_weightedOrder_X_one (k : ℕ) :
    (1 : ℕ∞) ≤ (X (((1 : Fin 2), k) : Fin 2 × ℕ) : MvPowerSeries (Fin 2 × ℕ) R).weightedOrder wOne := by
  classical
  refine nat_le_weightedOrder _ fun e he => ?_
  rw [coeff_X]
  split_ifs with h
  · subst h
    rw [single_one_eq_pr, weight_wOne_pr, Finsupp.degree_single] at he
    simp at he
  · rfl

omit hp in

theorem L_pow_succ (k n : ℕ) : ∃ Q : MvPowerSeries (Fin 2 × ℕ) R,
    (2 : ℕ∞) ≤ Q.weightedOrder wOne ∧
      L R k ^ (n + 1) = X (0, k) ^ (n + 1) + C ((n : R) + 1) * (X (0, k) ^ n * X (1, k)) + Q := by
  have hX1 := one_le_weightedOrder_X_one R k
  induction n with
  | zero =>
    refine ⟨0, by simp, ?_⟩
    simp [L]
  | succ n ih =>
    obtain ⟨Q, hQ, hL⟩ := ih
    refine ⟨C ((n : R) + 1) * (X (0, k) ^ n * X (1, k) * X (1, k)) + Q * L R k, ?_, ?_⟩
    · have hA : (2 : ℕ∞) ≤
          (X (0, k) ^ n * X (1, k) * X (1, k) : MvPowerSeries (Fin 2 × ℕ) R).weightedOrder wOne :=
        calc (2 : ℕ∞) = (0 + 1) + 1 := by norm_num
          _ ≤ ((X (0, k) ^ n : MvPowerSeries (Fin 2 × ℕ) R).weightedOrder wOne +
                (X (1, k) : MvPowerSeries (Fin 2 × ℕ) R).weightedOrder wOne) +
                (X (1, k) : MvPowerSeries (Fin 2 × ℕ) R).weightedOrder wOne :=
              add_le_add (add_le_add bot_le hX1) hX1
          _ ≤ _ := le_trans (add_le_add (le_weightedOrder_mul _) le_rfl) (le_weightedOrder_mul _)
      have hA' : (2 : ℕ∞) ≤ (C ((n : R) + 1) * (X (0, k) ^ n * X (1, k) * X (1, k)) :
          MvPowerSeries (Fin 2 × ℕ) R).weightedOrder wOne :=
        le_trans (le_trans hA le_add_self) (le_weightedOrder_mul _)
      have hB : (2 : ℕ∞) ≤ (Q * L R k).weightedOrder wOne :=
        le_trans (le_trans hQ le_self_add) (le_weightedOrder_mul _)
      exact le_trans (le_min hA' hB) (min_weightedOrder_le_add _)
    · rw [pow_succ, hL, L]
      simp only [map_add, map_one, map_natCast, Nat.cast_succ]
      ring

omit hp in

theorem coeff_pr_zero_T (e₀ x : ℕ →₀ ℕ) :
    coeff (pr x 0) (T R e₀) = if x = e₀ then 1 else 0 := by
  classical
  have h := congrArg (coeff (pr x 0)) (weightedHomogeneousComponent_zero_T R e₀)
  rw [coeff_weightedHomogeneousComponent, weight_wOne_pr, map_zero, if_pos rfl,
    coeff_monomial] at h
  rw [h]
  simp only [pr_ext_iff, and_true]

omit hp in

theorem coeff_T (e' a : ℕ →₀ ℕ) (m : ℕ) :
    coeff (pr a (Finsupp.single m 1)) (T R e') =
      if e' = a + Finsupp.single m 1 then (((a m + 1 : ℕ) : R)) else 0 := by
  classical

  obtain ⟨n, e₀, hm, rfl⟩ : ∃ (n : ℕ) (e₀ : ℕ →₀ ℕ), m ∉ e₀.support ∧
      e' = Finsupp.single m n + e₀ :=
    ⟨e' m, e'.erase m, by simp, (Finsupp.single_add_erase m e').symm⟩
  have he₀m : e₀ m = 0 := by simpa using hm
  rw [T_add, T_single]
  cases n with
  | zero =>

    rw [pow_zero, one_mul, coeff_T_eq_zero_of_notMem_support R e₀ hm (by simp), if_neg]
    intro h
    have := DFunLike.congr_fun h m
    simp [he₀m] at this
  | succ n' =>
    obtain ⟨Q, hQ, hL⟩ := L_pow_succ R m n'
    rw [hL, add_mul, add_mul, map_add, map_add]

    have h1 : coeff (pr a (Finsupp.single m 1)) (X (0, m) ^ (n' + 1) * T R e₀) = 0 := by
      rw [X_pow_eq, coeff_monomial_mul]
      split_ifs with hle
      · rw [one_mul, coeff_T_eq_zero_of_notMem_support R e₀ hm]
        rw [single_zero_eq_pr, pr_tsub, pr_apply_one]
        simp
      · rfl

    have h3 : coeff (pr a (Finsupp.single m 1)) (Q * T R e₀) = 0 := by
      refine coeff_eq_zero_of_lt_weightedOrder wOne ?_
      rw [weight_wOne_pr, Finsupp.degree_single]
      refine lt_of_lt_of_le (by norm_num : (1 : ℕ∞) < 2) (le_trans ?_ (le_weightedOrder_mul _))
      exact le_trans hQ le_self_add

    have hmono : (X (0, m) ^ n' * X (1, m) : MvPowerSeries (Fin 2 × ℕ) R) =
        monomial (pr (Finsupp.single m n') (Finsupp.single m 1)) 1 := by
      rw [X_pow_eq, show (X (1, m) : MvPowerSeries (Fin 2 × ℕ) R) = X (1, m) ^ 1 from
        (pow_one _).symm, X_pow_eq, monomial_mul_monomial, one_mul, single_zero_eq_pr,
        single_one_eq_pr, pr_add, add_zero, zero_add]
    rw [h1, h3, zero_add, add_zero, mul_assoc, coeff_C_mul, hmono, coeff_monomial_mul]
    simp only [pr_le_iff, pr_tsub, tsub_self, one_mul, coeff_pr_zero_T, Finsupp.single_le_iff,
      le_refl, and_true]

    by_cases hcase : Finsupp.single m (n' + 1) + e₀ = a + Finsupp.single m 1
    · have ham : a m = n' := by
        have := DFunLike.congr_fun hcase m
        simp only [Finsupp.add_apply, Finsupp.single_eq_same, he₀m] at this
        omega
      have hx : a - Finsupp.single m n' = e₀ := by
        ext k
        by_cases hk : k = m
        · subst hk; simp [he₀m, ham]
        · have := DFunLike.congr_fun hcase k
          simp only [Finsupp.add_apply, Finsupp.single_apply, if_neg (Ne.symm hk), zero_add,
            add_zero] at this
          simp [Ne.symm hk, this]
      rw [if_pos hcase, if_pos (by rw [ham]), if_pos hx, mul_one, ham, Nat.cast_succ]
    · rw [if_neg hcase]
      split_ifs with hle hx
      · exfalso
        apply hcase
        ext k
        by_cases hk : k = m
        · subst hk
          have := DFunLike.congr_fun hx k
          simp only [Finsupp.tsub_apply, Finsupp.single_eq_same, he₀m] at this
          simp only [Finsupp.add_apply, Finsupp.single_eq_same, he₀m]
          omega
        · have := DFunLike.congr_fun hx k
          simp only [Finsupp.tsub_apply, Finsupp.single_apply, if_neg (Ne.symm hk),
            tsub_zero] at this
          simp [Ne.symm hk, this]
      · rw [mul_zero]
      · rw [mul_zero]

end WittAux

namespace CartierModule

open MvFormalGroup MvFormalGroup.CartierModule

variable {Φ : MvFormalGroup d R} [Φ.IsComm]

omit hp in

theorem weightedHomogeneousComponent_zero_subst_blk_zero (F : MvPowerSeries ℕ R) :
    weightedHomogeneousComponent wOne 0 (subst (WittLaw.blk (R := R) 0) F) =
      subst (WittLaw.blk 0) F := by
  ext E
  rw [coeff_weightedHomogeneousComponent]
  split_ifs with h
  · rfl
  · symm
    by_contra hne
    obtain ⟨x, hx, -⟩ := WittLaw.exists_coeff_ne_zero_of_coeff_subst_blk_ne_zero 0 F hne
    apply h
    rw [← hx, mapDomain_zero_eq_pr, weight_wOne_pr, map_zero]

omit hp in

theorem two_le_weightedOrder_subst_blk_one (F : MvPowerSeries ℕ R) (h0 : F.constantCoeff = 0)
    (h1 : ∀ n, coeff (Finsupp.single n 1) F = 0) :
    (2 : ℕ∞) ≤ (subst (WittLaw.blk (R := R) 1) F).weightedOrder wOne := by
  suffices h : ((2 : ℕ) : ℕ∞) ≤ (subst (WittLaw.blk (R := R) 1) F).weightedOrder wOne by
    exact_mod_cast h
  refine nat_le_weightedOrder _ fun E hE => ?_
  by_contra hne
  obtain ⟨x, hx, hxc⟩ := WittLaw.exists_coeff_ne_zero_of_coeff_subst_blk_ne_zero 1 F hne
  rw [← hx, mapDomain_one_eq_pr, weight_wOne_pr] at hE
  rcases Nat.lt_trichotomy x.degree 1 with hlt | heq | hgt
  · have hx0 : x = 0 := (Finsupp.degree_eq_zero_iff x).mp (by omega)
    subst hx0
    exact hxc (by rwa [coeff_zero_eq_constantCoeff_apply])
  · obtain ⟨n, rfl⟩ : ∃ n, Finsupp.single n 1 = x := by
      have hmem : x ∈ {d' : ℕ →₀ ℕ | d'.degree = 1} := heq
      rwa [← Finsupp.range_single_one] at hmem
    exact hxc (h1 n)
  · omega

theorem coeff_addFam_prod_of_degree_eq {e' : ℕ →₀ ℕ} {E : Fin 2 × ℕ →₀ ℕ}
    (h : e'.degree = E.degree) :
    coeff E (e'.prod fun k n => WittLaw.addFam p R k ^ n) = coeff E (WittAux.T R e') := by
  have hc := congrArg (coeff E)
    (homogeneousComponent_finsuppProd (WittLaw.constantCoeff_addFam p R) e')
  simp only [WittAux.homogeneousComponent_one_addFam] at hc
  rw [coeff_homogeneousComponent, if_pos h.symm] at hc
  exact hc

omit [Φ.IsComm] in

theorem coeff_eq_zero_of_forall_coeff_single_eq_zero [CharP R p]
    (f : MvFormalGroup.CartierModule p Φ)
    (hlin : ∀ j n, coeff (Finsupp.single n 1) (f.toPowerSeries j) = 0)
    (j : Fin d) (e : ℕ →₀ ℕ) (he : ∃ n, ¬ p ∣ e n) : coeff e (f.toPowerSeries j) = 0 := by
  classical
  suffices H : ∀ D : ℕ, ∀ (j : Fin d) (e : ℕ →₀ ℕ), e.degree ≤ D → (∃ n, ¬ p ∣ e n) →
      coeff e (f.toPowerSeries j) = 0 from H _ j e le_rfl he
  intro D
  induction D with
  | zero =>
    rintro j e hD ⟨n, hn⟩
    have : e = 0 := (Finsupp.degree_eq_zero_iff e).mp (Nat.le_zero.mp hD)
    subst this
    exact absurd (dvd_zero p) hn
  | succ D IH =>
    rintro j e hD ⟨m, hm⟩
    by_cases hlt : e.degree ≤ D
    · exact IH j e hlt ⟨m, hm⟩
    have hdeg : e.degree = D + 1 := by omega
    have hem : 1 ≤ e m := Nat.one_le_iff_ne_zero.mpr fun h => hm (h ▸ dvd_zero p)

    obtain ⟨a, rfl⟩ : ∃ a, e = a + Finsupp.single m 1 :=
      ⟨e - Finsupp.single m 1, (tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr hem)).symm⟩
    have hdegA : a.degree = D := by
      rw [map_add, Finsupp.degree_single] at hdeg; omega
    by_cases hD0 : D = 0
    · subst hD0
      have ha0 : a = 0 := (Finsupp.degree_eq_zero_iff a).mp hdegA
      rw [ha0, zero_add]
      exact hlin j m

    have hunit : IsUnit (((a m + 1 : ℕ) : R)) := by
      have hnd : ¬ p ∣ (a m + 1) := by simpa [Finsupp.add_apply] using hm
      have hu : IsUnit (((a m + 1 : ℕ)) : ZMod p) := by
        rw [ZMod.isUnit_iff_coprime]
        exact ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hnd).symm
      have := hu.map (ZMod.castHom (dvd_refl p) R)
      rwa [map_natCast] at this

    set E : Fin 2 × ℕ →₀ ℕ := pr a (Finsupp.single m 1) with hEdef
    have hwE : Finsupp.weight wOne E = 1 := by
      rw [hEdef, weight_wOne_pr, Finsupp.degree_single]
    have hdE : E.degree = D + 1 := by
      rw [hEdef, degree_pr, Finsupp.degree_single, hdegA]
    have hf0 := f.constantCoeff_eq_zero

    have hR : coeff E (subst (Sum.elim (inBlk 0 f.toPowerSeries) (inBlk 1 f.toPowerSeries))
        (Φ.toPowerSeries j)) = 0 := by
      have hel := MvFormalGroup.hasSubst_elim (constantCoeff_inBlk 0 hf0)
        (constantCoeff_inBlk 1 hf0)
      rw [coeff_subst hel]
      refine finsum_eq_zero_of_forall_eq_zero fun γ => ?_
      suffices h : coeff E (γ.prod fun s k =>
          (Sum.elim (inBlk 0 f.toPowerSeries) (inBlk 1 f.toPowerSeries) s) ^ k) = 0 by
        rw [h, smul_zero]
      by_cases hβ : ∃ l, γ (Sum.inr l) ≠ 0
      · obtain ⟨l, hl⟩ := hβ
        refine coeff_eq_zero_of_lt_weightedOrder wOne ?_
        rw [hwE]
        have h2 : (2 : ℕ∞) ≤ ((Sum.elim (inBlk 0 f.toPowerSeries) (inBlk 1 f.toPowerSeries)
            (Sum.inr l)) ^ γ (Sum.inr l)).weightedOrder wOne := by
          refine le_trans ?_ (le_weightedOrder_pow _ _)
          have h2' := two_le_weightedOrder_subst_blk_one (f.toPowerSeries l) (hf0 l) (hlin l)
          calc (2 : ℕ∞) ≤ 1 • (subst (WittLaw.blk (R := R) 1) (f.toPowerSeries l)).weightedOrder
                wOne := by rwa [one_smul]
            _ ≤ γ (Sum.inr l) • (subst (WittLaw.blk (R := R) 1) (f.toPowerSeries l)).weightedOrder
                wOne := nsmul_le_nsmul_left bot_le (Nat.one_le_iff_ne_zero.mpr hl)
        refine lt_of_lt_of_le (by norm_num : (1 : ℕ∞) < 2) (le_trans h2 ?_)
        rw [Finsupp.prod]
        refine le_trans ?_ (le_weightedOrder_prod wOne _ _)
        exact Finset.single_le_sum (f := fun s => ((Sum.elim (inBlk 0 f.toPowerSeries)
          (inBlk 1 f.toPowerSeries) s) ^ γ s).weightedOrder wOne) (fun _ _ => bot_le)
          (Finsupp.mem_support_iff.mpr hl)
      · push Not at hβ
        refine coeff_eq_zero_of_weightedHomogeneousComponent_zero_eq wOne ?_
          (by rw [hwE]; exact one_ne_zero)
        rw [Finsupp.prod, weightedHomogeneousComponent_zero_prod]
        refine Finset.prod_congr rfl fun s hs => ?_
        rcases s with l | l
        · show weightedHomogeneousComponent wOne 0
              ((subst (WittLaw.blk (R := R) 0) (f.toPowerSeries l)) ^ γ (Sum.inl l)) = _
          rw [weightedHomogeneousComponent_zero_pow, weightedHomogeneousComponent_zero_subst_blk_zero]
          rfl
        · exact absurd (hβ l) (Finsupp.mem_support_iff.mp hs)

    have hL : coeff E (subst (WittLaw.addFam p R) (f.toPowerSeries j)) =
        coeff (a + Finsupp.single m 1) (f.toPowerSeries j) * ((a m + 1 : ℕ) : R) := by
      rw [coeff_subst (WittLaw.hasSubst_addFam p R), finsum_eq_single _ (a + Finsupp.single m 1)]
      · rw [smul_eq_mul, coeff_addFam_prod_of_degree_eq (hdeg.trans hdE.symm), WittAux.coeff_T,
          if_pos rfl]
      · intro e' hne
        by_cases hz : coeff e' (f.toPowerSeries j) = 0
        · rw [hz, zero_smul]
        rcases Nat.lt_trichotomy e'.degree (D + 1) with hlt' | heq' | hgt'
        ·
          have hdiv : ∀ n, p ∣ e' n := fun n => by
            by_contra hn
            exact hz (IH j e' (by omega) ⟨n, hn⟩)
          obtain ⟨e'', rfl⟩ : ∃ e'' : ℕ →₀ ℕ, e' = p • e'' :=
            ⟨e'.mapRange (fun a => a / p) (by simp),
              by ext i; simp [Nat.mul_div_cancel' (hdiv i)]⟩
          have hpow : ((p • e'').prod fun k n => WittLaw.addFam p R k ^ n) =
              (e''.prod fun k n => WittLaw.addFam p R k ^ n) ^ p := by
            rw [Finsupp.prod_of_support_subset _ Finsupp.support_smul _ (fun _ _ => pow_zero _),
              Finsupp.prod, ← Finset.prod_pow]
            refine Finset.prod_congr rfl fun k _ => ?_
            rw [Finsupp.smul_apply, smul_eq_mul, mul_comm, pow_mul]
          rw [hpow, pow_eq_expand_map_frobenius,
            coeff_expand_of_not_dvd _ _ _ (i := ((1 : Fin 2), m)) ?_, smul_zero]
          rw [hEdef, pr_apply_one, Finsupp.single_eq_same, Nat.dvd_one]
          exact hp.out.one_lt.ne'
        · rw [coeff_addFam_prod_of_degree_eq (heq'.trans hdE.symm), WittAux.coeff_T, if_neg hne,
            smul_zero]
        · have hord : ((E.degree : ℕ) : ℕ∞) <
              (e'.prod fun k n => WittLaw.addFam p R k ^ n).order :=
            lt_of_lt_of_le (by rw [hdE]; exact_mod_cast hgt')
              (MvFormalGroup.le_order_finsuppProd_pow (WittLaw.constantCoeff_addFam p R) e')
          rw [coeff_of_lt_order hord, smul_zero]
    have key := congrArg (coeff E) (f.subst_addFam j)
    rw [hL, hR] at key
    exact hunit.mul_left_eq_zero.mp key

end CartierModule

section MulP

variable (Φ : MvFormalGroup d R) [Φ.IsComm]

def pSeries (p : ℕ) [Fact p.Prime] (Φ : MvFormalGroup d R) : Fin d → MvPowerSeries (Fin d) R :=
  fun i => contract p (Φ.nthSeries p i)

theorem expand_pSeries [CharP R p] (i : Fin d) :
    expand p hp.out.ne_zero (pSeries p Φ i) = Φ.nthSeries p i := by
  refine expand_contract _ fun m hm => ?_
  have hlin : MvFormalGroup.linearPart (Φ.nthSeries p) = 0 := by
    rw [MvFormalGroup.linearPart_nthSeries]
    ext i j
    simp [Matrix.smul_apply]
  have hF := (p : MvFormalGroup.End Φ).subst_eq
  rw [MvFormalGroup.End.toPowerSeries_natCast] at hF
  exact MvFormalGroup.coeff_eq_zero_of_linearPart_eq_zero_of_subst_eq_charP p Φ Φ
    (Φ.nthSeries p) (MvFormalGroup.constantCoeff_nthSeries Φ p) hlin hF i m hm

omit [Φ.IsComm] in
theorem constantCoeff_pSeries (i : Fin d) : (pSeries p Φ i).constantCoeff = 0 :=
  constantCoeff_contract _ (MvFormalGroup.constantCoeff_nthSeries Φ p i)

omit [Φ.IsComm] in
theorem hasSubst_pSeries : HasSubst (pSeries p Φ) :=
  hasSubst_of_constantCoeff_zero (constantCoeff_pSeries Φ)

end MulP

namespace CartierModule

open MvFormalGroup MvFormalGroup.CartierModule

variable {Φ : MvFormalGroup d R} [Φ.IsComm]

def frobTwist [CharP R p] (f : MvFormalGroup.CartierModule p Φ) : Fin d → MvPowerSeries ℕ R :=
  fun l => map (frobenius R p) (f.toPowerSeries l)

omit [Φ.IsComm] in
theorem constantCoeff_frobTwist [CharP R p] (f : MvFormalGroup.CartierModule p Φ) (l : Fin d) :
    (frobTwist f l).constantCoeff = 0 := by
  rw [frobTwist, constantCoeff_map, f.constantCoeff_eq_zero, map_zero]

omit [Φ.IsComm] in
theorem hasSubst_frobTwist [CharP R p] (f : MvFormalGroup.CartierModule p Φ) :
    HasSubst (frobTwist f) :=
  hasSubst_of_constantCoeff_zero (constantCoeff_frobTwist f)

theorem toPowerSeries_nsmul_p (f : MvFormalGroup.CartierModule p Φ) (j : Fin d) :
    ((p : ℕ) • f).toPowerSeries j = subst f.toPowerSeries (Φ.nthSeries p j) := by
  rw [← endAct_natCast, endAct_apply, toPowerSeries_map, MvFormalGroup.End.toPowerSeries_natCast]

theorem toPowerSeries_frobenius_eq [CharP R p] (f : MvFormalGroup.CartierModule p Φ) (j : Fin d) :
    (frobenius f).toPowerSeries j = subst (frobTwist f) (pSeries p Φ j) := by
  apply expand_injective (p := p)
  have h1 : expand p hp.out.ne_zero ((frobenius f).toPowerSeries j) =
      ((p : ℕ) • f).toPowerSeries j := by
    rw [← verschiebung_frobenius, toPowerSeries_verschiebung_eq_expand]
  rw [h1, toPowerSeries_nsmul_p, ← expand_pSeries Φ j, expand, substAlgHom_apply,
    subst_comp_subst_apply (HasSubst.X_pow hp.out.ne_zero) f.hasSubst_toPowerSeries,
    ← substAlgHom_apply (hasSubst_frobTwist f), expand_substAlgHom, substAlgHom_apply]
  congr 1
  funext l
  rw [subst_pow f.hasSubst_toPowerSeries, subst_X f.hasSubst_toPowerSeries,
    pow_eq_expand_map_frobenius]
  rfl

theorem coeff_single_subst_verFam (F : MvPowerSeries ℕ R) (n : ℕ) :
    coeff (Finsupp.single n 1) (subst (WittLaw.verFam R) F) =
      coeff (Finsupp.single (n + 1) 1) F := by
  classical
  rw [coeff_subst WittLaw.hasSubst_verFam, finsum_eq_single _ (Finsupp.single (n + 1) 1)]
  · rw [Finsupp.prod_single_index (by simp), pow_one, WittLaw.verFam_succ, coeff_X, if_pos rfl,
      smul_eq_mul, mul_one]
  · intro e he

    rcases Nat.lt_trichotomy e.degree 1 with hlt | heq | hgt
    · have he0 : e = 0 := (Finsupp.degree_eq_zero_iff e).mp (by omega)
      subst he0
      rw [Finsupp.prod_zero_index, coeff_one, if_neg (Finsupp.single_ne_zero.mpr one_ne_zero),
        smul_zero]
    · obtain ⟨k, rfl⟩ : ∃ k, Finsupp.single k 1 = e := by
        have hmem : e ∈ {d' : ℕ →₀ ℕ | d'.degree = 1} := heq
        rwa [← Finsupp.range_single_one] at hmem
      rw [Finsupp.prod_single_index (by simp), pow_one]
      cases k with
      | zero => rw [WittLaw.verFam_zero, map_zero, smul_zero]
      | succ m =>
        rw [WittLaw.verFam_succ, coeff_X,
          if_neg (fun h => he (by rw [Finsupp.single_left_injective one_ne_zero h])), smul_zero]
    · have horder : (((Finsupp.single n 1).degree : ℕ) : ℕ∞) <
          (e.prod fun k m => WittLaw.verFam R k ^ m).order := by
        refine lt_of_lt_of_le ?_
          (MvFormalGroup.le_order_finsuppProd_pow WittLaw.constantCoeff_verFam e)
        rw [Finsupp.degree_single]
        exact_mod_cast hgt
      rw [coeff_of_lt_order horder, smul_zero]

theorem coeff_single_frobenius (f : MvFormalGroup.CartierModule p Φ) (j : Fin d) (n : ℕ) :
    coeff (Finsupp.single n 1) ((frobenius f).toPowerSeries j) =
      coeff (Finsupp.single (n + 1) 1) (f.toPowerSeries j) :=
  coeff_single_subst_verFam _ n

theorem coeff_single_succ [CharP R p] (f : MvFormalGroup.CartierModule p Φ) (j : Fin d) (n : ℕ) :
    coeff (Finsupp.single (n + 1) 1) (f.toPowerSeries j) =
      ∑ l : Fin d, coeff (Finsupp.single l 1) (pSeries p Φ j) *
        (coeff (Finsupp.single n 1) (f.toPowerSeries l)) ^ p := by
  rw [← coeff_single_frobenius, toPowerSeries_frobenius_eq,
    MvFormalGroup.coeff_single_subst (constantCoeff_frobTwist f)]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [frobTwist, coeff_map, frobenius_def]

theorem coeff_single_eq_zero_of_tangent_eq_zero [CharP R p] (f : MvFormalGroup.CartierModule p Φ)
    (hf : tangent f = 0) (j : Fin d) (n : ℕ) :
    coeff (Finsupp.single n 1) (f.toPowerSeries j) = 0 := by
  induction n generalizing j with
  | zero =>
    have := congrFun hf j
    rwa [tangent_apply] at this
  | succ n ih =>
    rw [coeff_single_succ]
    refine Finset.sum_eq_zero fun l _ => ?_
    rw [ih l, zero_pow hp.out.ne_zero, mul_zero]

section Construct

variable [CharP R p]

omit [Φ.IsComm] [CharP R p] in

theorem subst_blk_expand (i : Fin 2) (F : MvPowerSeries ℕ R) :
    subst (WittLaw.blk i) (expand p hp.out.ne_zero F) =
      expand p hp.out.ne_zero (subst (WittLaw.blk (R := R) i) F) := by
  rw [expand, substAlgHom_apply, expand, substAlgHom_apply,
    subst_comp_subst_apply (HasSubst.X_pow hp.out.ne_zero) (WittLaw.hasSubst_blk i),
    subst_comp_subst_apply (WittLaw.hasSubst_blk i) (HasSubst.X_pow hp.out.ne_zero)]
  congr 1
  funext k
  rw [subst_pow (WittLaw.hasSubst_blk i), subst_X (WittLaw.hasSubst_blk i), WittLaw.blk_apply,
    subst_X (HasSubst.X_pow hp.out.ne_zero)]

theorem addFam_pow (k : ℕ) :
    WittLaw.addFam p R k ^ p = expand p hp.out.ne_zero (WittLaw.addFam p R k) := by
  rw [WittLaw.addFam, ← MvPolynomial.coe_pow, ← WittLaw.expand_map_wittAdd, expand_eq_expand]

def contractElem (f : MvFormalGroup.CartierModule p Φ)
    (hf : ∀ j (e : ℕ →₀ ℕ), (∃ n, ¬ p ∣ e n) → coeff e (f.toPowerSeries j) = 0) :
    MvFormalGroup.CartierModule p Φ where
  toPowerSeries := fun j => contract p (f.toPowerSeries j)
  constantCoeff_eq_zero := fun j => constantCoeff_contract _ (f.constantCoeff_eq_zero j)
  subst_eq := by
    intro j
    have hexp : ∀ l, expand p hp.out.ne_zero (contract p (f.toPowerSeries l)) =
        f.toPowerSeries l := fun l => expand_contract _ (hf l)
    apply expand_injective (p := p)

    have hL : expand p hp.out.ne_zero (subst (WittLaw.addFam p R) (contract p (f.toPowerSeries j))) =
        subst (WittLaw.addFam p R) (f.toPowerSeries j) := by
      conv_rhs => rw [← hexp j]
      rw [expand, substAlgHom_apply, expand, substAlgHom_apply,
        subst_comp_subst_apply (WittLaw.hasSubst_addFam p R) (HasSubst.X_pow hp.out.ne_zero),
        subst_comp_subst_apply (HasSubst.X_pow hp.out.ne_zero) (WittLaw.hasSubst_addFam p R)]
      congr 1
      funext k
      rw [subst_pow (WittLaw.hasSubst_addFam p R), subst_X (WittLaw.hasSubst_addFam p R), addFam_pow,
        expand, substAlgHom_apply]

    have hc0 : ∀ l, (contract p (f.toPowerSeries l)).constantCoeff = 0 :=
      fun l => constantCoeff_contract _ (f.constantCoeff_eq_zero l)
    have hR : expand p hp.out.ne_zero (subst
        (Sum.elim (fun l => subst (fun m => (X (0, m) : MvPowerSeries (Fin 2 × ℕ) R))
            (contract p (f.toPowerSeries l)))
          fun l => subst (fun m => (X (1, m) : MvPowerSeries (Fin 2 × ℕ) R))
            (contract p (f.toPowerSeries l)))
        (Φ.toPowerSeries j)) =
      subst (Sum.elim (fun l => subst (fun m => (X (0, m) : MvPowerSeries (Fin 2 × ℕ) R))
            (f.toPowerSeries l))
          fun l => subst (fun m => (X (1, m) : MvPowerSeries (Fin 2 × ℕ) R)) (f.toPowerSeries l))
        (Φ.toPowerSeries j) := by
      have hel : HasSubst (Sum.elim (inBlk 0 fun l => contract p (f.toPowerSeries l))
          (inBlk 1 fun l => contract p (f.toPowerSeries l))) :=
        MvFormalGroup.hasSubst_elim (constantCoeff_inBlk 0 hc0) (constantCoeff_inBlk 1 hc0)
      show expand p hp.out.ne_zero (subst (Sum.elim (inBlk 0 fun l => contract p (f.toPowerSeries l))
          (inBlk 1 fun l => contract p (f.toPowerSeries l))) (Φ.toPowerSeries j)) =
        subst (Sum.elim (inBlk 0 f.toPowerSeries) (inBlk 1 f.toPowerSeries)) (Φ.toPowerSeries j)
      rw [expand_subst _ _ hel]
      congr 1
      funext s
      rcases s with l | l
      · show expand p hp.out.ne_zero (subst (WittLaw.blk 0) (contract p (f.toPowerSeries l))) =
          subst (WittLaw.blk 0) (f.toPowerSeries l)
        rw [← subst_blk_expand, hexp]
      · show expand p hp.out.ne_zero (subst (WittLaw.blk 1) (contract p (f.toPowerSeries l))) =
          subst (WittLaw.blk 1) (f.toPowerSeries l)
        rw [← subst_blk_expand, hexp]
    rw [hL, hR]
    exact f.subst_eq j

theorem verschiebung_contractElem (f : MvFormalGroup.CartierModule p Φ)
    (hf : ∀ j (e : ℕ →₀ ℕ), (∃ n, ¬ p ∣ e n) → coeff e (f.toPowerSeries j) = 0) :
    verschiebung (contractElem f hf) = f := by
  apply MvFormalGroup.CartierModule.ext
  funext j
  rw [toPowerSeries_verschiebung_eq_expand]
  exact expand_contract _ (hf j)

end Construct

theorem tangent_eq_zero_iff [CharP R p] (f : MvFormalGroup.CartierModule p Φ) :
    tangent f = 0 ↔ ∃ g : MvFormalGroup.CartierModule p Φ, verschiebung g = f := by
  refine ⟨fun hf => ?_, ?_⟩
  · have hlin := coeff_single_eq_zero_of_tangent_eq_zero f hf
    exact ⟨contractElem f (coeff_eq_zero_of_forall_coeff_single_eq_zero f hlin),
      verschiebung_contractElem f _⟩
  · rintro ⟨g, rfl⟩
    exact tangent_verschiebung g

end CartierModule

end CartierVReducedSol
p2m_reactivate "P2MW.S_MvFormalGroup_CartierModule_tangent_eq_zero_iff_exists_verschiebung_eq.CartierVReducedSol"

end
p2m_reactivate "P2MW.S_MvFormalGroup_CartierModule_tangent_eq_zero_iff_exists_verschiebung_eq.CartierVReducedSol"

theorem solution
    (p : ℕ) [Fact p.Prime] {R : Type u} [CommRing R] [CharP R p] {d : ℕ}
    (Φ : MvFormalGroup d R) [Φ.IsComm] (f : MvFormalGroup.CartierModule p Φ) :
    MvFormalGroup.CartierModule.tangent f = 0 ↔
      ∃ g : MvFormalGroup.CartierModule p Φ,
        MvFormalGroup.CartierModule.verschiebung g = f :=
  CartierVReducedSol.CartierModule.tangent_eq_zero_iff f

end S_MvFormalGroup_CartierModule_tangent_eq_zero_iff_exists_verschiebung_eq
end P2MW
export P2MW.S_MvFormalGroup_CartierModule_tangent_eq_zero_iff_exists_verschiebung_eq (solution)
