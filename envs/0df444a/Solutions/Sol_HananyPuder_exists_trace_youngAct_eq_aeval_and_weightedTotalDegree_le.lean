-- Prove2me | solution 1 for HananyPuder.exists_trace_youngAct_eq_aeval_and_weightedTotalDegree_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T19:42:33.393205+00:00
-- url     : https://prove2.me/submissions/a08bb59c-da3c-4399-8c38-dfdf6ec49e2a

import Mathlib
import Definitions.Def_StrongConv
import Definitions.Def_StrongConvG4
import Theorems.Thm_StrongConv_trace_youngAct_eq_sum_sign_mul_card_filter

section
open StrongConv
namespace HananyPuder.W2Q288.PartS

open MvPolynomial Finset

/-! ## Weighted degree bookkeeping -/

theorem wd_le_iff {p : MvPolynomial ℕ ℚ} {n : ℕ} :
    p.weightedTotalDegree (fun i : ℕ => i + 1) ≤ n ↔
      ∀ u ∈ p.support, Finsupp.weight (fun i : ℕ => i + 1) u ≤ n := by
  unfold weightedTotalDegree
  exact Finset.sup_le_iff

theorem wd_add {p q : MvPolynomial ℕ ℚ} {n : ℕ}
    (hp : p.weightedTotalDegree (fun i : ℕ => i + 1) ≤ n)
    (hq : q.weightedTotalDegree (fun i : ℕ => i + 1) ≤ n) :
    (p + q).weightedTotalDegree (fun i : ℕ => i + 1) ≤ n := by
  rw [wd_le_iff] at *
  intro u hu
  classical
  rcases Finset.mem_union.1 (support_add hu) with h | h
  · exact hp u h
  · exact hq u h

theorem wd_zero {n : ℕ} : (0 : MvPolynomial ℕ ℚ).weightedTotalDegree (fun i : ℕ => i + 1) ≤ n := by
  rw [wd_le_iff]; simp

theorem wd_sum {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial ℕ ℚ) {n : ℕ}
    (h : ∀ i ∈ s, (f i).weightedTotalDegree (fun i : ℕ => i + 1) ≤ n) :
    (∑ i ∈ s, f i).weightedTotalDegree (fun i : ℕ => i + 1) ≤ n := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using wd_zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact wd_add (h a (mem_insert_self _ _)) (ih fun i hi => h i (mem_insert_of_mem hi))

theorem wd_mul {p q : MvPolynomial ℕ ℚ} {a b : ℕ}
    (hp : p.weightedTotalDegree (fun i : ℕ => i + 1) ≤ a)
    (hq : q.weightedTotalDegree (fun i : ℕ => i + 1) ≤ b) :
    (p * q).weightedTotalDegree (fun i : ℕ => i + 1) ≤ a + b := by
  rw [wd_le_iff] at *
  intro u hu
  classical
  obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_add.1 (support_mul p q hu)
  rw [map_add]
  exact Nat.add_le_add (hp x hx) (hq y hy)

theorem wd_mono {p : MvPolynomial ℕ ℚ} {a b : ℕ}
    (hp : p.weightedTotalDegree (fun i : ℕ => i + 1) ≤ a) (hab : a ≤ b) :
    p.weightedTotalDegree (fun i : ℕ => i + 1) ≤ b := hp.trans hab

theorem wd_prod {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial ℕ ℚ) (n : ι → ℕ)
    (h : ∀ i ∈ s, (f i).weightedTotalDegree (fun i : ℕ => i + 1) ≤ n i) :
    (∏ i ∈ s, f i).weightedTotalDegree (fun i : ℕ => i + 1) ≤ ∑ i ∈ s, n i := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [prod_empty, sum_empty]
    rw [wd_le_iff]
    intro u hu
    rw [show (1 : MvPolynomial ℕ ℚ) = C 1 from rfl, mem_support_iff, coeff_C] at hu
    split_ifs at hu with h
    · subst h; simp
    · exact absurd rfl hu
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact wd_mul (h a (mem_insert_self _ _)) (ih fun i hi => h i (mem_insert_of_mem hi))

theorem wd_C (r : ℚ) : (C r : MvPolynomial ℕ ℚ).weightedTotalDegree (fun i : ℕ => i + 1) ≤ 0 := by
  rw [wd_le_iff]
  intro u hu
  rw [mem_support_iff, coeff_C] at hu
  split_ifs at hu with h
  · subst h; simp
  · exact absurd rfl hu

theorem wd_X (i : ℕ) : (X i : MvPolynomial ℕ ℚ).weightedTotalDegree (fun i : ℕ => i + 1) ≤ i + 1 := by
  rw [wd_le_iff]
  intro u hu
  classical
  rw [support_X, Finset.mem_singleton] at hu
  simp [hu, Finsupp.weight_single]

/-! ## Binomial polynomials -/

/-- `Ch s F = F (F - 1) ⋯ (F - s + 1) / s!`. -/
noncomputable def Ch (s : ℕ) (F : MvPolynomial ℕ ℚ) : MvPolynomial ℕ ℚ :=
  C ((s.factorial : ℚ)⁻¹) * ∏ j ∈ range s, (F - C (j : ℚ))

theorem wd_Ch (s : ℕ) (F : MvPolynomial ℕ ℚ) (e : ℕ)
    (hF : F.weightedTotalDegree (fun i : ℕ => i + 1) ≤ e) :
    (Ch s F).weightedTotalDegree (fun i : ℕ => i + 1) ≤ s * e := by
  unfold Ch
  have h1 := wd_mul (wd_C ((s.factorial : ℚ)⁻¹))
    (wd_prod (range s) (fun j => F - C (j : ℚ)) (fun _ => e) fun j _ => by
      rw [sub_eq_add_neg, ← map_neg]
      exact wd_add hF (wd_mono (wd_C _) (Nat.zero_le _)))
  simpa [mul_comm] using h1

theorem prod_sub_eq_descFactorial (c s : ℕ) :
    ∏ j ∈ range s, ((c : ℂ) - (j : ℂ)) = (c.descFactorial s : ℂ) := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [prod_range_succ, ih, Nat.descFactorial_succ]
    rcases le_or_gt s c with h | h
    · push_cast [Nat.cast_sub h]; ring
    · rw [(Nat.descFactorial_eq_zero_iff_lt).2 h]; simp

theorem aeval_Ch (v : ℕ → ℂ) (s : ℕ) (F : MvPolynomial ℕ ℚ) (c : ℕ) (hF : aeval v F = (c : ℂ)) :
    aeval v (Ch s F) = (c.choose s : ℂ) := by
  unfold Ch
  simp only [map_mul, map_prod, map_sub, aeval_C, hF]
  simp only [eq_ratCast, Rat.cast_inv, Rat.cast_natCast]
  rw [prod_sub_eq_descFactorial, Nat.descFactorial_eq_factorial_mul_choose]
  push_cast
  have : (s.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero s
  field_simp

/-! ## Points of a given minimal period -/

/-- The number of points of minimal period `d`. -/
noncomputable def per {N : ℕ} (σ : Equiv.Perm (Fin N)) (d : ℕ) : ℕ :=
  (univ.filter fun x => Function.minimalPeriod σ x = d).card

theorem xi_eq_sum_per {N : ℕ} (σ : Equiv.Perm (Fin N)) (j : ℕ) (hj : 0 < j) :
    xi j σ = ∑ d ∈ j.divisors, per σ d := by
  unfold xi per
  rw [card_eq_sum_card_fiberwise (f := fun x => Function.minimalPeriod σ x) (t := j.divisors)]
  · refine sum_congr rfl fun d hd => ?_
    congr 1
    ext x
    simp only [mem_filter, mem_univ, true_and, and_iff_right_iff_imp]
    intro hx
    have : Function.IsPeriodicPt σ j x := by
      rw [Function.isPeriodicPt_iff_minimalPeriod_dvd, hx]
      exact Nat.dvd_of_mem_divisors hd
    rw [Function.IsPeriodicPt, Function.IsFixedPt, Equiv.Perm.iterate_eq_pow] at this
    exact this
  · intro x hx
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hx
    simp only [mem_coe, Nat.mem_divisors]
    refine ⟨?_, hj.ne'⟩
    apply Function.IsPeriodicPt.minimalPeriod_dvd
    rw [Function.IsPeriodicPt, Function.IsFixedPt, Equiv.Perm.iterate_eq_pow]
    exact hx

theorem exists_per_poly (d : ℕ) (hd : 0 < d) :
    ∃ A : MvPolynomial ℕ ℚ, A.weightedTotalDegree (fun i : ℕ => i + 1) ≤ d ∧
      ∀ (N : ℕ) (σ : Equiv.Perm (Fin N)),
        aeval (fun i : ℕ => ((xi (i + 1) σ : ℕ) : ℂ)) A = (per σ d : ℂ) := by
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    have h' : ∀ e ∈ d.properDivisors, ∃ A : MvPolynomial ℕ ℚ,
        A.weightedTotalDegree (fun i : ℕ => i + 1) ≤ e ∧
        ∀ (N : ℕ) (σ : Equiv.Perm (Fin N)),
          aeval (fun i : ℕ => ((xi (i + 1) σ : ℕ) : ℂ)) A = (per σ e : ℂ) := by
      intro e he
      rw [Nat.mem_properDivisors] at he
      exact ih e he.2 (Nat.pos_of_dvd_of_pos he.1 hd)
    choose! A hA using h'
    refine ⟨X (d - 1) - ∑ e ∈ d.properDivisors, A e, ?_, ?_⟩
    · rw [sub_eq_add_neg, ← sum_neg_distrib]
      refine wd_add ?_ (wd_sum _ _ fun e he => ?_)
      · have := wd_X (d - 1); rwa [Nat.sub_add_cancel hd] at this
      · have h1 := (hA e he).1
        rw [wd_le_iff] at h1 ⊢
        intro u hu
        rw [support_neg] at hu
        exact (h1 u hu).trans
          (Nat.le_of_lt (Nat.mem_properDivisors.1 he).2)
    · intro N σ
      simp only [map_sub, map_sum, aeval_X]
      rw [Nat.sub_add_cancel hd, xi_eq_sum_per σ d hd,
        ← Nat.insert_self_properDivisors hd.ne', sum_insert Nat.self_notMem_properDivisors]
      rw [sum_congr rfl fun e he => (hA e he).2 N σ]
      push_cast; ring

/-! ## Truncation modulo monomials of high degree -/

/-- Polynomials with no monomial of degree `≤ k`. -/
def hiI (m k : ℕ) : Ideal (MvPolynomial (Fin m) ℚ) where
  carrier := {F | ∀ u : Fin m →₀ ℕ, u.degree ≤ k → coeff u F = 0}
  add_mem' := by
    intro a b ha hb u hu
    simp only [Set.mem_ofPred_eq] at ha hb
    rw [coeff_add, ha u hu, hb u hu, add_zero]
  zero_mem' := by
    intro u _
    simp
  smul_mem' := by
    intro c F hF u hu
    simp only [Set.mem_ofPred_eq] at hF
    rw [smul_eq_mul, coeff_mul]
    refine Finset.sum_eq_zero fun x hx => ?_
    rw [HasAntidiagonal.mem_antidiagonal] at hx
    have : x.2.degree ≤ k := by
      have h2 : (x.1 + x.2).degree = x.1.degree + x.2.degree := map_add _ _ _
      rw [hx] at h2
      omega
    rw [hF x.2 this, mul_zero]

theorem mem_hiI_of_hom {m k n : ℕ} {F : MvPolynomial (Fin m) ℚ} (hF : F.IsHomogeneous n)
    (hn : k < n) : F ∈ hiI m k := by
  intro u hu
  exact hF.coeff_eq_zero (by omega)

/-- The power sum `Σ Xᵢ^d`. -/
noncomputable def psum (m d : ℕ) : MvPolynomial (Fin m) ℚ := ∑ i, X i ^ d

theorem psum_hom (m d : ℕ) : (psum m d).IsHomogeneous d :=
  IsHomogeneous.sum _ _ _ fun i _ => isHomogeneous_X_pow i d

theorem one_add_pow_trunc {R : Type*} [CommRing R] (a : R) (K c : ℕ) (ha : a ^ (K + 1) = 0) :
    (1 + a) ^ c = ∑ s : Fin (K + 1), (c.choose s : R) * a ^ (s : ℕ) := by
  rw [Fin.sum_univ_eq_sum_range (fun s => (c.choose s : R) * a ^ s), add_comm, add_pow]
  simp only [one_pow, mul_one]
  have h1 : ∑ s ∈ range (c + 1), a ^ s * (c.choose s : R) =
      ∑ s ∈ range (c + K + 2), a ^ s * (c.choose s : R) := by
    refine Finset.sum_subset (range_subset_range.2 (by omega)) fun s _ hs => ?_
    rw [mem_range, not_lt] at hs
    rw [Nat.choose_eq_zero_of_lt (by omega)]; simp
  have h2 : ∑ s ∈ range (K + 1), (c.choose s : R) * a ^ s =
      ∑ s ∈ range (c + K + 2), (c.choose s : R) * a ^ s := by
    refine Finset.sum_subset (range_subset_range.2 (by omega)) fun s _ hs => ?_
    rw [mem_range, not_lt] at hs
    rw [pow_eq_zero_of_le hs ha, mul_zero]
  rw [h1, h2]
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

/-! ## Orbits of `⟨σ⟩` -/

section Orbits

open Classical

variable {N : ℕ} (σ : Equiv.Perm (Fin N))

/-- The orbits of `⟨σ⟩`. -/
abbrev Q := Quotient (MulAction.orbitRel (Subgroup.zpowers σ) (Fin N))

/-- The orbit of a point. -/
def mkQ (x : Fin N) : Q σ := Quotient.mk _ x

theorem mkQ_eq_iff (x y : Fin N) : mkQ σ y = mkQ σ x ↔ ∃ z : ℤ, (σ ^ z) x = y := by
  unfold mkQ
  rw [Quotient.eq, MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨⟨g, hg⟩, rfl⟩
    obtain ⟨z, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
    exact ⟨z, rfl⟩
  · rintro ⟨z, rfl⟩
    exact ⟨⟨σ ^ z, Subgroup.zpow_mem_zpowers σ z⟩, rfl⟩

theorem mkQ_apply (x : Fin N) : mkQ σ (σ x) = mkQ σ x :=
  (mkQ_eq_iff σ x (σ x)).2 ⟨1, by simp⟩

theorem inv_zpow {α : Type*} (f : Fin N → α) (hf : ∀ x, f (σ x) = f x) (z : ℤ) (x : Fin N) :
    f ((σ ^ z) x) = f x := by
  induction z using Int.induction_on generalizing x with
  | zero => simp
  | succ n ih => rw [zpow_add_one, Equiv.Perm.mul_apply, ih (σ x), hf]
  | pred n ih =>
    rw [zpow_sub_one, Equiv.Perm.mul_apply, ih]
    have := hf (σ⁻¹ x)
    simp only [Equiv.apply_symm_apply, Equiv.Perm.coe_inv] at this
    exact this.symm

/-- The size of an orbit. -/
noncomputable def sz (q : Q σ) : ℕ := (univ.filter fun x => mkQ σ x = q).card

theorem sz_mkQ (x : Fin N) : sz σ (mkQ σ x) = Function.minimalPeriod σ x := by
  have hfun : (fun y => σ • y) = ⇑σ := funext fun y => Equiv.Perm.smul_def σ y
  have h := MulAction.minimalPeriod_eq_card (a := σ) (b := x)
  rw [hfun] at h
  rw [h, ← Set.toFinset_card]
  unfold sz
  congr 1
  ext y
  simp only [mem_filter, mem_univ, true_and, Set.mem_toFinset]
  unfold mkQ
  rw [Quotient.eq, MulAction.orbitRel_apply]

theorem sz_pos (q : Q σ) : 0 < sz σ q := by
  obtain ⟨x, rfl⟩ := Quotient.exists_rep q
  exact Finset.card_pos.2 ⟨x, Finset.mem_filter.2 ⟨mem_univ _, rfl⟩⟩

/-- The number of orbits of size `d`. -/
noncomputable def cnt (d : ℕ) : ℕ := (univ.filter fun q : Q σ => sz σ q = d).card

theorem per_eq (d : ℕ) : per σ d = cnt σ d * d := by
  unfold per cnt
  have h1 : (univ.filter fun x => Function.minimalPeriod σ x = d) =
      univ.filter fun x => sz σ (mkQ σ x) = d := by
    ext x; simp [sz_mkQ]
  rw [h1, card_eq_sum_card_fiberwise (f := mkQ σ) (t := univ.filter fun q : Q σ => sz σ q = d)]
  · rw [← smul_eq_mul, ← Finset.sum_const]
    refine sum_congr rfl fun q hq => ?_
    rw [mem_filter] at hq
    rw [← hq.2]
    unfold sz
    congr 1
    ext x
    simp only [mem_filter, mem_univ, true_and, and_iff_right_iff_imp]
    rintro rfl
    rfl
  · intro x hx
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hx
    simpa using hx

/-- The weight of a colour: `1` for colour `0`, `Xᵢ` for colour `i + 1`. -/
noncomputable def wc (m : ℕ) : Fin (m + 1) → MvPolynomial (Fin m) ℚ := Fin.cons 1 (fun i => X i)

/-- The exponent of a colour. -/
noncomputable def ec (m : ℕ) : Fin (m + 1) → (Fin m →₀ ℕ) := Fin.cons 0 (fun i => Finsupp.single i 1)

theorem wc_eq {m : ℕ} (c : Fin (m + 1)) : wc m c = monomial (ec m c) 1 := by
  refine Fin.cases ?_ (fun i => ?_) c
  · simp [wc, ec]
  · simp only [wc, ec, Fin.cons_succ]; rfl

theorem ec_sum_apply {m : ℕ} (h : Fin N → Fin (m + 1)) (i : Fin m) :
    (∑ x, ec m (h x)) i = (univ.filter fun x => h x = i.succ).card := by
  rw [Finsupp.finsetSum_apply, Finset.card_eq_sum_ones, Finset.sum_filter]
  refine sum_congr rfl fun x _ => ?_
  generalize h x = c
  refine Fin.cases ?_ (fun j => ?_) c
  · simp [ec, (Fin.succ_ne_zero i).symm]
  · simp only [ec, Fin.cons_succ, Finsupp.single_apply, Fin.succ_inj]

theorem gen_coeff {m : ℕ} (t' : Fin m → ℕ) :
    ((univ.filter fun g : Q σ → Fin (m + 1) =>
        ∀ i, (univ.filter fun x => g (mkQ σ x) = i.succ).card = t' i).card : ℚ) =
      coeff (Finsupp.equivFunOnFinite.symm t') (∑ g : Q σ → Fin (m + 1), ∏ x, wc m (g (mkQ σ x))) := by
  rw [coeff_sum, natCast_card_filter]
  refine sum_congr rfl fun g _ => ?_
  simp_rw [wc_eq]
  rw [← monomial_sum_one, coeff_monomial]
  refine if_congr ?_ rfl rfl
  rw [DFunLike.ext_iff]
  simp only [ec_sum_apply, Finsupp.coe_equivFunOnFinite_symm]

theorem gen_prod {m : ℕ} :
    (∑ g : Q σ → Fin (m + 1), ∏ x, wc m (g (mkQ σ x))) = ∏ q : Q σ, (1 + psum m (sz σ q)) := by
  have h1 : ∀ g : Q σ → Fin (m + 1), ∏ x, wc m (g (mkQ σ x)) = ∏ q, wc m (g q) ^ sz σ q := by
    intro g
    rw [← Finset.prod_fiberwise univ (mkQ σ) (fun x => wc m (g (mkQ σ x)))]
    refine prod_congr rfl fun q _ => ?_
    rw [prod_congr rfl (fun x hx => by rw [(mem_filter.1 hx).2]), prod_const]
    rfl
  have h2 : ∀ n : ℕ, (∑ c : Fin (m + 1), wc m c ^ n) = 1 + psum m n := by
    intro n
    rw [Fin.sum_univ_succ]
    simp [wc, psum]
  simp_rw [h1, ← h2]
  rw [Fintype.prod_sum]

theorem coeff_gen_eq {m : ℕ} (k : ℕ) (t' : Fin m → ℕ) (hk : ∑ i, t' i = k) :
    coeff (Finsupp.equivFunOnFinite.symm t') (∑ g : Q σ → Fin (m + 1), ∏ x, wc m (g (mkQ σ x))) =
      ∑ S : Fin k → Fin (k + 1), (∏ d : Fin k, ((cnt σ (d + 1)).choose (S d) : ℚ)) *
        coeff (Finsupp.equivFunOnFinite.symm t') (∏ d : Fin k, psum m (d + 1) ^ (S d : ℕ)) := by
  set T := Finsupp.equivFunOnFinite.symm t'
  have hT : T.degree ≤ k := by
    rw [Finsupp.degree_eq_sum]; simp [T, hk]
  set E : MvPolynomial (Fin m) ℚ := ∑ S : Fin k → Fin (k + 1),
    ∏ d : Fin k, (((cnt σ (d + 1)).choose (S d) : ℕ) : MvPolynomial (Fin m) ℚ) *
      psum m (d + 1) ^ (S d : ℕ) with hEdef
  have hE : (∑ g : Q σ → Fin (m + 1), ∏ x, wc m (g (mkQ σ x))) - E ∈ hiI m k := by
    rw [← Ideal.Quotient.eq]
    set π := Ideal.Quotient.mk (hiI m k)
    have hz : ∀ d, k < d → π (psum m d) = 0 := fun d hd =>
      Ideal.Quotient.eq_zero_iff_mem.2 (mem_hiI_of_hom (psum_hom m d) hd)
    have hn : ∀ d, 0 < d → π (psum m d) ^ (k + 1) = 0 := fun d hd => by
      rw [← map_pow]
      exact Ideal.Quotient.eq_zero_iff_mem.2
        (mem_hiI_of_hom ((psum_hom m d).pow (k + 1)) (by nlinarith))
    rw [gen_prod]
    simp only [map_prod, map_add, map_one]
    rw [← prod_filter_of_ne (p := fun q => sz σ q ≤ k) (fun q _ hq => by
      by_contra h
      exact hq (by rw [hz _ (by omega), add_zero]))]
    rw [← prod_fiberwise_of_maps_to' (t := range (k + 1)) (g := sz σ)
      (f := fun d => 1 + π (psum m d)) (fun q hq => by
        rw [mem_filter] at hq; rw [mem_range]; omega)]
    have hc : ∀ d ∈ range (k + 1),
        ∏ q ∈ (univ.filter fun q => sz σ q ≤ k).filter (fun q => sz σ q = d),
          (1 + π (psum m d)) = (1 + π (psum m d)) ^ (cnt σ d) := by
      intro d hd
      rw [prod_const]
      congr 1
      unfold cnt
      rw [filter_filter]
      congr 1
      refine filter_congr fun q _ => ?_
      rw [mem_range] at hd
      constructor
      · exact fun h => h.2
      · intro h; exact ⟨by omega, h⟩
    rw [prod_congr rfl hc, prod_range_succ']
    have hc0 : cnt σ 0 = 0 := by
      unfold cnt
      rw [card_eq_zero, filter_eq_empty_iff]
      intro q _
      exact (sz_pos σ q).ne'
    rw [hc0, pow_zero, mul_one]
    rw [← Fin.prod_univ_eq_prod_range (fun d => (1 + π (psum m (d + 1))) ^ (cnt σ (d + 1)))]
    rw [prod_congr rfl (fun d _ => one_add_pow_trunc _ k _ (hn _ (Nat.succ_pos _)))]
    rw [Fintype.prod_sum]
    simp only [hEdef, map_sum, map_prod, map_mul, map_pow, map_natCast]
  have h := hE T hT
  rw [coeff_sub, sub_eq_zero] at h
  rw [h, hEdef, coeff_sum]
  refine sum_congr rfl fun S _ => ?_
  rw [prod_mul_distrib, ← Nat.cast_prod, ← map_natCast (C : ℚ →+* MvPolynomial (Fin m) ℚ),
    coeff_C_mul]
  push_cast
  rfl

theorem card_inv_eq {m : ℕ} (t' : Fin m → ℕ) :
    (univ.filter fun f : Fin N → Fin (m + 1) => (∀ x, f (σ x) = f x) ∧
        ∀ i : Fin m, (univ.filter fun x => f x = i.succ).card = t' i).card =
      (univ.filter fun g : Q σ → Fin (m + 1) =>
        ∀ i, (univ.filter fun x => g (mkQ σ x) = i.succ).card = t' i).card := by
  symm
  refine Finset.card_bij (fun g _ => g ∘ mkQ σ) ?_ ?_ ?_
  · intro g hg
    simp only [mem_filter, mem_univ, true_and] at hg ⊢
    exact ⟨fun x => by simp only [Function.comp_apply, mkQ_apply], hg⟩
  · intro g1 _ g2 _ h
    funext q
    obtain ⟨x, rfl⟩ := Quotient.exists_rep q
    exact congrFun h x
  · intro f hf
    simp only [mem_filter, mem_univ, true_and] at hf
    obtain ⟨hinv, hc⟩ := hf
    refine ⟨Quotient.lift f (fun a b hab => ?_), ?_, ?_⟩
    · obtain ⟨z, hz⟩ := (mkQ_eq_iff σ b a).1 (Quotient.sound hab)
      rw [← hz]
      exact inv_zpow σ f hinv z b
    · simp only [mem_filter, mem_univ, true_and]
      exact hc
    · rfl

end Orbits

/-! ## The main theorem -/

theorem permChar_poly (m : ℕ) (t : Fin m → ℤ) :
    ∃ P : MvPolynomial ℕ ℚ,
      MvPolynomial.weightedTotalDegree (fun i : ℕ => i + 1) P ≤ (∑ i, t i).toNat ∧
      ∀ (N : ℕ) (σ : Equiv.Perm (Fin N)), (∑ i, t i) ≤ (N : ℤ) →
        (((Finset.univ.filter fun f : Fin N → Fin (m + 1) =>
            (∀ x, f (σ x) = f x) ∧
              ∀ i, ((Finset.univ.filter fun x => f x = i).card : ℤ) =
                (Fin.cons ((N : ℤ) - ∑ i, t i) t : Fin (m + 1) → ℤ) i).card : ℕ) : ℂ) =
          MvPolynomial.aeval (fun i : ℕ => ((xi (i + 1) σ : ℕ) : ℂ)) P := by
  by_cases hneg : ∃ i, t i < 0
  · obtain ⟨i0, hi0⟩ := hneg
    refine ⟨0, wd_zero, fun N σ _ => ?_⟩
    rw [map_zero, Nat.cast_eq_zero, Finset.card_eq_zero, filter_eq_empty_iff]
    rintro f _ ⟨_, h⟩
    have := h i0.succ
    rw [Fin.cons_succ] at this
    omega
  push Not at hneg
  set t' : Fin m → ℕ := fun i => (t i).toNat with ht'
  have ht : ∀ i, t i = (t' i : ℤ) := fun i => (Int.toNat_of_nonneg (hneg i)).symm
  set k := ∑ i, t' i with hk
  have hsum : ∑ i, t i = (k : ℤ) := by rw [hk]; push_cast; exact sum_congr rfl fun i _ => ht i
  choose! B hB using exists_per_poly
  set T := Finsupp.equivFunOnFinite.symm t'
  have hT : T.degree = k := by rw [Finsupp.degree_eq_sum]; simp [T, hk]
  set Cs : (Fin k → Fin (k + 1)) → ℚ :=
    fun S => coeff T (∏ d : Fin k, psum m (d + 1) ^ (S d : ℕ)) with hCs
  refine ⟨∑ S : Fin k → Fin (k + 1), C (Cs S) *
      ∏ d : Fin k, Ch (S d) (C (((d : ℕ) + 1 : ℚ))⁻¹ * B ((d : ℕ) + 1)), ?_, ?_⟩
  · rw [hsum, Int.toNat_natCast]
    refine wd_sum _ _ fun S _ => ?_
    by_cases hS : Cs S = 0
    · rw [hS, C_0, zero_mul]; exact wd_zero
    have hom : (∏ d : Fin k, psum m (d + 1) ^ (S d : ℕ)).IsHomogeneous
        (∑ d : Fin k, ((d : ℕ) + 1) * (S d : ℕ)) :=
      IsHomogeneous.prod _ _ _ (fun d _ => (psum_hom m _).pow _)
    have hdeg : T.degree = ∑ d : Fin k, ((d : ℕ) + 1) * (S d : ℕ) := by
      by_contra hne
      exact hS (hom.coeff_eq_zero hne)
    have h1 := wd_mul (wd_C (Cs S)) (wd_prod univ _ (fun d : Fin k => (S d : ℕ) * ((d : ℕ) + 1))
      (fun d _ => wd_Ch _ _ _ (by
        simpa using wd_mul (wd_C (((d : ℕ) + 1 : ℚ))⁻¹) (hB ((d : ℕ) + 1) (Nat.succ_pos _)).1)))
    refine h1.trans (le_of_eq ?_)
    rw [zero_add]
    exact (sum_congr rfl fun d _ => mul_comm _ _).trans (hdeg.symm.trans hT)
  · intro N σ hN
    have htot : ∀ f : Fin N → Fin (m + 1),
        ∑ i : Fin (m + 1), (univ.filter fun x => f x = i).card = N := by
      intro f
      rw [← card_eq_sum_card_fiberwise (f := f) (s := univ) (t := univ) (by simp)]
      simp
    have hfilt : (Finset.univ.filter fun f : Fin N → Fin (m + 1) =>
            (∀ x, f (σ x) = f x) ∧
              ∀ i, ((Finset.univ.filter fun x => f x = i).card : ℤ) =
                (Fin.cons ((N : ℤ) - ∑ i, t i) t : Fin (m + 1) → ℤ) i) =
        univ.filter fun f : Fin N → Fin (m + 1) => (∀ x, f (σ x) = f x) ∧
          ∀ i : Fin m, (univ.filter fun x => f x = i.succ).card = t' i := by
      refine filter_congr fun f _ => and_congr_right fun _ => ?_
      constructor
      · intro h j
        have := h j.succ
        rw [Fin.cons_succ, ht] at this
        exact_mod_cast this
      · intro h i
        refine Fin.cases ?_ (fun j => ?_) i
        · rw [Fin.cons_zero, hsum]
          have := htot f
          rw [Fin.sum_univ_succ] at this
          simp_rw [h] at this
          rw [← hk] at this
          omega
        · rw [Fin.cons_succ, ht, h j]
    rw [hfilt, card_inv_eq]
    have hq := gen_coeff σ t'
    rw [coeff_gen_eq σ k t' hk.symm] at hq
    rw [show ((_ : ℕ) : ℂ) = (((_ : ℕ) : ℚ) : ℂ) from (Rat.cast_natCast _).symm, hq]
    simp only [map_sum, map_mul, aeval_C, map_prod, eq_ratCast]
    push_cast
    refine sum_congr rfl fun S _ => ?_
    rw [mul_comm]
    congr 1
    refine prod_congr rfl fun d _ => ?_
    rw [aeval_Ch _ _ _ (cnt σ ((d : ℕ) + 1))]
    rw [map_mul, aeval_C, (hB _ (Nat.succ_pos _)).2 N σ, per_eq]
    simp only [eq_ratCast]
    push_cast
    field_simp

end HananyPuder.W2Q288.PartS
end

section
/-!
# q288: the character polynomials from James's determinantal form

For `w ∈ S_{ℓ+1}` (`ℓ` the number of rows of `μ`), the `w`-term of the determinantal form of the
character of `μ[N]` counts `σ`-invariant maps with fibre sizes `(N - Σ t_w, t_w)`, where
`t_w i = μ_{i+1} - (i + 1) + w (i + 1)`; `permChar_poly` gives a polynomial for that count, and
`Σ t_w = |μ| - w 0 ≤ |μ|`.
-/

open StrongConv

namespace HananyPuder.W2Q288.PartG

open MvPolynomial

/-- Cells of a diagram, row by row. -/
def rowCellEquiv (μ : YoungDiagram) : μ.cells ≃ (i : Fin (μ.colLen 0)) × Fin (μ.rowLen i) where
  toFun c := ⟨⟨c.val.1, YoungDiagram.mem_iff_lt_colLen.mp
      (μ.up_left_mem le_rfl (Nat.zero_le _) c.property)⟩,
    ⟨c.val.2, YoungDiagram.mem_iff_lt_rowLen.mp c.property⟩⟩
  invFun c := ⟨(c.1.val, c.2.val), YoungDiagram.mem_iff_lt_rowLen.mpr c.2.isLt⟩
  left_inv c := Subtype.ext rfl
  right_inv c := by rcases c with ⟨⟨i, hi⟩, ⟨j, hj⟩⟩; rfl

lemma sum_rowLens (μ : YoungDiagram) : μ.rowLens.sum = μ.cells.card := by
  classical
  have h := Fintype.card_congr (rowCellEquiv μ)
  simp only [Fintype.card_coe, Fintype.card_sigma, Fintype.card_fin] at h
  rw [h, YoungDiagram.rowLens]
  rw [← List.sum_toFinset _ List.nodup_range]
  have he : (List.range (μ.colLen 0)).toFinset = Finset.range (μ.colLen 0) := by
    ext i; simp
  rw [he]
  exact (Fin.sum_univ_eq_sum_range μ.rowLen (μ.colLen 0)).symm

lemma stableRows_sortedGE (μ : YoungDiagram) (N : ℕ) (h : μ.cells.card + μ.rowLen 0 ≤ N) :
    (stableRows μ N).SortedGE := by
  apply List.Pairwise.sortedGE
  rw [stableRows, List.pairwise_cons]
  refine ⟨fun a ha => ?_, (YoungDiagram.rowLens_sorted μ).pairwise⟩
  rw [YoungDiagram.rowLens, List.mem_map] at ha
  obtain ⟨i, _, rfl⟩ := ha
  have := μ.rowLen_anti 0 i (Nat.zero_le _)
  omega

/-- The polynomial of `permChar_poly`. -/
noncomputable def P (m : ℕ) (t : Fin m → ℤ) : MvPolynomial ℕ ℚ :=
  Classical.choose (HananyPuder.W2Q288.PartS.permChar_poly m t)

lemma P_deg (m : ℕ) (t : Fin m → ℤ) :
    MvPolynomial.weightedTotalDegree (fun i : ℕ => i + 1) (P m t) ≤ (∑ i, t i).toNat :=
  (Classical.choose_spec (HananyPuder.W2Q288.PartS.permChar_poly m t)).1

lemma P_spec (m : ℕ) (t : Fin m → ℤ) (N : ℕ) (σ : Equiv.Perm (Fin N)) (h : (∑ i, t i) ≤ (N : ℤ)) :
    (((Finset.univ.filter fun f : Fin N → Fin (m + 1) =>
        (∀ x, f (σ x) = f x) ∧
          ∀ i, ((Finset.univ.filter fun x => f x = i).card : ℤ) =
            (Fin.cons ((N : ℤ) - ∑ i, t i) t : Fin (m + 1) → ℤ) i).card : ℕ) : ℂ) =
      MvPolynomial.aeval (fun i : ℕ => ((xi (i + 1) σ : ℕ) : ℂ)) (P m t) :=
  (Classical.choose_spec (HananyPuder.W2Q288.PartS.permChar_poly m t)).2 N σ h

lemma P_spec' (m : ℕ) (t : Fin m → ℤ) (N : ℕ) (σ : Equiv.Perm (Fin N)) (h : (∑ i, t i) ≤ (N : ℤ))
    (c : Fin (m + 1) → ℤ) (hc : c = Fin.cons ((N : ℤ) - ∑ i, t i) t) :
    (((Finset.univ.filter fun f : Fin N → Fin (m + 1) =>
        (∀ x, f (σ x) = f x) ∧
          ∀ i, ((Finset.univ.filter fun x => f x = i).card : ℤ) = c i).card : ℕ) : ℂ) =
      MvPolynomial.aeval (fun i : ℕ => ((xi (i + 1) σ : ℕ) : ℂ)) (P m t) := by
  subst hc
  exact P_spec m t N σ h

/-- The fibre sizes `t_w` of the `w`-term. -/
def tw (μ : YoungDiagram) (w : Equiv.Perm (Fin (μ.rowLens.length + 1))) :
    Fin μ.rowLens.length → ℤ :=
  fun i => (μ.rowLens.get i : ℤ) - (((i : ℕ) + 1 : ℕ) : ℤ) + ((w i.succ : ℕ) : ℤ)

lemma sum_tw (μ : YoungDiagram) (w : Equiv.Perm (Fin (μ.rowLens.length + 1))) :
    ∑ i, tw μ w i = (μ.cells.card : ℤ) - ((w 0 : ℕ) : ℤ) := by
  have h1 : ∑ j, ((w j : ℕ) : ℤ) = ∑ j : Fin (μ.rowLens.length + 1), ((j : ℕ) : ℤ) :=
    Equiv.sum_comp w (fun j => ((j : ℕ) : ℤ))
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ] at h1
  have h2 : ∑ i : Fin μ.rowLens.length, ((μ.rowLens.get i : ℕ) : ℤ) = (μ.cells.card : ℤ) := by
    rw [← sum_rowLens, ← Fin.sum_univ_getElem μ.rowLens]
    push_cast
    rfl
  simp only [tw, Finset.sum_add_distrib, Finset.sum_sub_distrib, h2]
  simp only [Fin.val_succ, Fin.val_zero, Nat.cast_zero, zero_add] at h1
  push_cast at h1 ⊢
  linarith

lemma entry_eq (μ : YoungDiagram) (N : ℕ) (h : μ.cells.card ≤ N)
    (w : Equiv.Perm (Fin (μ.rowLens.length + 1))) (j : Fin (μ.rowLens.length + 1)) :
    ((stableRows μ N).get j : ℤ) - ((j : ℕ) : ℤ) + ((w j : ℕ) : ℤ) =
      (Fin.cons ((N : ℤ) - ∑ i, tw μ w i) (tw μ w) : Fin (μ.rowLens.length + 1) → ℤ) j := by
  refine Fin.cases ?_ (fun i => ?_) j
  · rw [sum_tw]
    simp only [Fin.cons_zero, Fin.val_zero, Nat.cast_zero, sub_zero]
    change (((N - μ.cells.card : ℕ) : ℤ)) + _ = _
    push_cast [h]
    ring
  · simp only [Fin.cons_succ, tw, Fin.val_succ]
    rfl

/-- One term of the determinantal form. -/
lemma term_eq (μ : YoungDiagram) (N : ℕ) (hN : μ.cells.card + μ.rowLen 0 ≤ N)
    (σ : Equiv.Perm (Fin N)) (w : Equiv.Perm (Fin (μ.rowLens.length + 1))) :
    ((Equiv.Perm.sign w : ℤ) : ℂ) *
        ((Finset.univ.filter fun f : Fin N → Fin (stableRows μ N).length =>
          (∀ x, f (σ x) = f x) ∧
            ∀ i, ((Finset.univ.filter fun x => f x = i).card : ℤ) =
              ((stableRows μ N).get i : ℤ) - (i : ℕ) + (w i : ℕ)).card : ℂ) =
      MvPolynomial.aeval (fun i : ℕ => ((xi (i + 1) σ : ℕ) : ℂ))
        (((Equiv.Perm.sign w : ℤ) : ℚ) • P μ.rowLens.length (tw μ w)) := by
  have hle : (∑ i, tw μ w i) ≤ (N : ℤ) := by
    rw [sum_tw]
    omega
  rw [map_smul, ← P_spec' _ _ N σ hle
    (fun j => ((stableRows μ N).get j : ℤ) - ((j : ℕ) : ℤ) + ((w j : ℕ) : ℤ))
    (funext (entry_eq μ N (by omega) w)), Rat.smul_def]
  push_cast
  rfl

/-- The glue: the determinantal form and `permChar_poly` give the character polynomials with the
degree bound. -/
theorem wdeg_of_det_and_permChar :
    ∃ q : YoungDiagram → MvPolynomial ℕ ℚ,
      (∀ (μ : YoungDiagram) (N : ℕ), μ.cells.card + μ.rowLen 0 ≤ N →
        ∀ σ : Equiv.Perm (Fin N),
          LinearMap.trace ℂ (youngSpace N (stableRows μ N)) (youngAct N (stableRows μ N) σ) =
            MvPolynomial.aeval (fun i : ℕ => ((xi (i + 1) σ : ℕ) : ℂ)) (q μ)) ∧
      ∀ μ : YoungDiagram, MvPolynomial.weightedTotalDegree (fun i : ℕ => i + 1) (q μ) ≤ μ.cells.card := by
  refine ⟨fun μ => ∑ w : Equiv.Perm (Fin (μ.rowLens.length + 1)),
      ((Equiv.Perm.sign w : ℤ) : ℚ) • P μ.rowLens.length (tw μ w), ?_, ?_⟩
  · intro μ N hN σ
    have hsum : (stableRows μ N).sum = N := by
      rw [stableRows, List.sum_cons, sum_rowLens]
      omega
    rw [trace_youngAct_eq_sum_sign_mul_card_filter N (stableRows μ N)
      (stableRows_sortedGE μ N hN) hsum σ, map_sum]
    exact Finset.sum_congr rfl fun w _ => term_eq μ N hN σ w
  · intro μ
    rw [weightedTotalDegree]
    refine Finset.sup_le fun d hd => ?_
    obtain ⟨w, -, hw⟩ := Finset.mem_biUnion.mp (support_sum hd)
    have hd' := support_smul hw
    refine (le_weightedTotalDegree _ hd').trans ((P_deg _ _).trans ?_)
    rw [Int.toNat_le, sum_tw]
    omega

end HananyPuder.W2Q288.PartG
end

section
open StrongConv

namespace HananyPuder.W2Q288

/-- The character polynomials with the weighted-degree bound, from James's determinantal form. -/
theorem wdeg_main :
    ∃ q : YoungDiagram → MvPolynomial ℕ ℚ,
      (∀ (μ : YoungDiagram) (N : ℕ), μ.cells.card + μ.rowLen 0 ≤ N →
        ∀ σ : Equiv.Perm (Fin N),
          LinearMap.trace ℂ (youngSpace N (stableRows μ N)) (youngAct N (stableRows μ N) σ) =
            MvPolynomial.aeval (fun i : ℕ => ((xi (i + 1) σ : ℕ) : ℂ)) (q μ)) ∧
      ∀ μ : YoungDiagram, MvPolynomial.weightedTotalDegree (fun i : ℕ => i + 1) (q μ) ≤ μ.cells.card :=
  PartG.wdeg_of_det_and_permChar

end HananyPuder.W2Q288
end

open HananyPuder.W2Q288 in
theorem solution : type_of% @HananyPuder.W2Q288.wdeg_main := @HananyPuder.W2Q288.wdeg_main
