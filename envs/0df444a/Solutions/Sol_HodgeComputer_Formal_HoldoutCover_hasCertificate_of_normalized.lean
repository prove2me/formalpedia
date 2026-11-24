-- Prove2me | solution 1 for HodgeComputer.Formal.HoldoutCover.hasCertificate_of_normalized
-- status  : ACCEPTED   (prove)
-- author  : @benediamond
-- created : 2026-11-24T03:19:07.186283+00:00
-- url     : https://prove2.me/submissions/aa982040-e32e-401d-9e65-55f76ff2ef27

import Definitions.Def_DiamondCertificate
import Definitions.Def_HodgeComputerFormal_Algebra
import Mathlib.Algebra.GroupWithZero.Associated
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Polynomial.Eval.Irreducible
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace HodgeComputerFormalHomCertAux

section
/- Source component: HomogeneousOrder -/
section
/-!
Finite homogeneous-component calculus for clearing a rational field.
No formal power series or Laurent series occur in this construction.
These are intermediate lemmas, not a HasCertificate theorem.
-/

noncomputable section

namespace HoldoutConstruction

open MvPolynomial
open scoped BigOperators

variable {R σ : Type*} [CommRing R]

/-- Every monomial has degree at least `n`; the zero polynomial satisfies
this condition for every `n`. -/
def HasOrder (n : ℕ) (p : MvPolynomial σ R) : Prop :=
  ∀ m : σ →₀ ℕ, m.degree < n → p.coeff m = 0

theorem HasOrder.mono {n k : ℕ} {p : MvPolynomial σ R}
    (h : HasOrder n p) (hk : k ≤ n) : HasOrder k p :=
  fun m hm => h m (lt_of_lt_of_le hm hk)

theorem hasOrder_zero (n : ℕ) : HasOrder n (0 : MvPolynomial σ R) := by
  intro m _
  simp

theorem hasOrder_zero_degree (p : MvPolynomial σ R) : HasOrder 0 p := by
  intro m hm
  omega

theorem HasOrder.add {n : ℕ} {p q : MvPolynomial σ R}
    (hp : HasOrder n p) (hq : HasOrder n q) : HasOrder n (p+q) := by
  intro m hm
  simp [hp m hm, hq m hm]

theorem HasOrder.sub {n : ℕ} {p q : MvPolynomial σ R}
    (hp : HasOrder n p) (hq : HasOrder n q) : HasOrder n (p-q) := by
  intro m hm
  simp [hp m hm, hq m hm]

theorem HasOrder.neg {n : ℕ} {p : MvPolynomial σ R}
    (hp : HasOrder n p) : HasOrder n (-p) := by
  intro m hm
  simp [hp m hm]

theorem HasOrder.sum {ι : Type*} (s : Finset ι) {n : ℕ}
    (p : ι → MvPolynomial σ R) (hp : ∀ i ∈ s, HasOrder n (p i)) :
    HasOrder n (∑ i ∈ s, p i) := by
  intro m hm
  simp only [coeff_sum]
  exact Finset.sum_eq_zero fun i hi => hp i hi m hm

theorem HasOrder.mul {n k : ℕ} {p q : MvPolynomial σ R}
    (hp : HasOrder n p) (hq : HasOrder k q) : HasOrder (n+k) (p*q) := by
  classical
  intro m hm
  rw [coeff_mul]
  apply Finset.sum_eq_zero
  intro a ha
  have he := congrArg Finsupp.degree (Finset.mem_antidiagonal.mp ha)
  simp only [map_add] at he
  by_cases h : a.1.degree < n
  · rw [hp _ h, zero_mul]
  · have h' : a.2.degree < k := by omega
    rw [hq _ h', mul_zero]

theorem HasOrder.pow {n : ℕ} {p : MvPolynomial σ R}
    (hp : HasOrder n p) (k : ℕ) : HasOrder (k*n) (p^k) := by
  induction k with
  | zero => simpa using hasOrder_zero_degree (1 : MvPolynomial σ R)
  | succ k ih =>
    simpa only [pow_succ, Nat.succ_mul] using ih.mul hp

theorem HasOrder.pderiv {n : ℕ} {p : MvPolynomial σ R}
    (hp : HasOrder n p) (i : σ) : HasOrder (n-1) (pderiv i p) := by
  intro m hm
  rw [coeff_pderiv]
  have hd : (m + Finsupp.single i 1).degree < n := by
    simp only [map_add, Finsupp.degree_single]
    omega
  rw [hp _ hd, zero_mul]

theorem isHomogeneous_hasOrder {n : ℕ} {p : MvPolynomial σ R}
    (hp : p.IsHomogeneous n) : HasOrder n p := by
  intro m hm
  exact hp.coeff_eq_zero (ne_of_lt hm)

theorem HasOrder.component_eq_zero {n : ℕ} {p : MvPolynomial σ R}
    (hp : HasOrder n p) {k : ℕ} (hk : k < n) : homogeneousComponent k p = 0 := by
  classical
  ext m
  rw [coeff_homogeneousComponent]
  split_ifs with h
  · exact hp m (h ▸ hk)
  · rfl

theorem hasOrder_of_components_zero {n : ℕ} {p : MvPolynomial σ R}
    (hp : ∀ k < n, homogeneousComponent k p = 0) : HasOrder n p := by
  intro m hm
  have h := congrArg (·.coeff m) (hp m.degree hm)
  simpa [coeff_homogeneousComponent] using h

/-- Multiplication of the first possible homogeneous components. -/
theorem component_mul_initial {n k : ℕ} {p q : MvPolynomial σ R}
    (hp : HasOrder n p) (hq : HasOrder k q) :
    homogeneousComponent (n+k) (p*q) =
      homogeneousComponent n p * homogeneousComponent k q := by
  classical
  ext m
  rw [coeff_homogeneousComponent, coeff_mul, coeff_mul]
  rw [Finset.ite_sum_zero]
  apply Finset.sum_congr rfl
  intro a ha
  have he := congrArg Finsupp.degree (Finset.mem_antidiagonal.mp ha)
  simp only [map_add] at he
  rw [coeff_homogeneousComponent, coeff_homogeneousComponent]
  by_cases h1 : a.1.degree < n
  · simp [hp _ h1, ne_of_lt h1]
  by_cases h2 : a.2.degree < k
  · simp [hq _ h2, ne_of_lt h2]
  by_cases h1' : a.1.degree = n
  · by_cases h2' : a.2.degree = k
    · have hm : m.degree = n+k := by omega
      simp [h1', h2', hm]
    · have hm : m.degree ≠ n+k := by omega
      simp [h2', hm]
  · have hm : m.degree ≠ n+k := by omega
    simp [h1', hm]

theorem pderiv_component (n : ℕ) (p : MvPolynomial σ R) (i : σ) :
    pderiv i (homogeneousComponent (n+1) p) =
      homogeneousComponent n (pderiv i p) := by
  classical
  ext m
  simp only [coeff_pderiv, coeff_homogeneousComponent, map_add,
    Finsupp.degree_single, Nat.add_right_cancel_iff, ite_mul, zero_mul]

theorem component_mul_homogeneous {n : ℕ} {p : MvPolynomial σ R}
    (hp : p.IsHomogeneous n) (k : ℕ) (q : MvPolynomial σ R) :
    homogeneousComponent (n+k) (p*q) = p*homogeneousComponent k q := by
  classical
  induction q using MvPolynomial.induction_on' with
  | monomial m a =>
    have hm : (monomial m a : MvPolynomial σ R).IsHomogeneous m.degree :=
      isHomogeneous_monomial _ rfl
    rw [homogeneousComponent_of_mem (hp.mul hm), homogeneousComponent_of_mem hm]
    simp only [Nat.add_left_cancel_iff]
    split_ifs <;> simp
  | add q r hq hr => simp only [mul_add, map_add, hq, hr]

theorem pderiv_isHomogeneous {n : ℕ} {p : MvPolynomial σ R}
    (hp : p.IsHomogeneous (n+1)) (i : σ) : (pderiv i p).IsHomogeneous n := by
  have h := pderiv_component n p i
  rw [homogeneousComponent_eq_self hp] at h
  rw [h]
  exact homogeneousComponent_isHomogeneous n _

/-- Subtracting the least component raises the order strictly. -/
theorem order_sub_initial {n : ℕ} {p : MvPolynomial σ R}
    (hp : HasOrder n p) : HasOrder (n+1) (homogeneousComponent n p - p) := by
  classical
  intro m hm
  rw [coeff_sub, coeff_homogeneousComponent]
  by_cases h : m.degree = n
  · simp [h]
  · have hlt : m.degree < n := by omega
    simp [h, hp _ hlt]

end HoldoutConstruction

end
end

end

section
/- Source component: HomogeneousIdeal -/
section
/-!
Finite homogeneous ideal calculus and cancellation at a legal leading term.
These are intermediate construction lemmas, not a HasCertificate theorem.
-/

noncomputable section

namespace HoldoutConstruction

open MvPolynomial
open scoped BigOperators

variable {R σ : Type*} [CommRing R]

theorem component_component (n k : ℕ) (p : MvPolynomial σ R) :
    homogeneousComponent n (homogeneousComponent k p) =
      if n = k then homogeneousComponent k p else 0 :=
  homogeneousComponent_of_mem (homogeneousComponent_isHomogeneous k p)

/-- A homogeneous principal ideal contains every homogeneous component of
each of its elements. This proof uses only a finite decomposition. -/
theorem component_dvd_of_dvd {F p : MvPolynomial σ R} {f : ℕ}
    (hF : F.IsHomogeneous f) (hp : F ∣ p) (n : ℕ) :
    F ∣ homogeneousComponent n p := by
  classical
  obtain ⟨q, rfl⟩ := hp
  rw [← sum_homogeneousComponent q, Finset.mul_sum, map_sum]
  apply Finset.dvd_sum
  intro i _
  rw [homogeneousComponent_of_mem (hF.mul (homogeneousComponent_isHomogeneous i q))]
  split_ifs
  · exact dvd_mul_right F _
  · exact dvd_zero F

/-- Sum of the components of degree strictly below `n`. -/
def truncateBelow (n : ℕ) (p : MvPolynomial σ R) : MvPolynomial σ R :=
  ∑ k ∈ Finset.range n, homogeneousComponent k p

theorem component_truncateBelow (n k : ℕ) (p : MvPolynomial σ R) :
    homogeneousComponent k (truncateBelow n p) =
      if k < n then homogeneousComponent k p else 0 := by
  classical
  simp [truncateBelow, component_component]

theorem order_sub_truncateBelow (n : ℕ) (p : MvPolynomial σ R) :
    HasOrder n (p - truncateBelow n p) := by
  apply hasOrder_of_components_zero
  intro k hk
  simp [component_truncateBelow, hk]

theorem component_sub_truncateBelow (n : ℕ) (p : MvPolynomial σ R) :
    homogeneousComponent n (p - truncateBelow n p) = homogeneousComponent n p := by
  simp [component_truncateBelow]

/-- Cancellation of a denominator's legal initial component, proved by
induction over finitely many homogeneous components. -/
theorem component_dvd_of_product {F C B : MvPolynomial σ R} {f c : ℕ}
    (hF : F.IsHomogeneous f) (hprime : Prime F)
    (hC : HasOrder c C) (hlegal : ¬ F ∣ homogeneousComponent c C)
    (n : ℕ)
    (hproduct : ∀ k ≤ n, F ∣ homogeneousComponent (c+k) (C*B)) :
    F ∣ homogeneousComponent n B := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have htrunc : F ∣ truncateBelow n B := by
      apply Finset.dvd_sum
      intro k hk
      have hkn : k < n := Finset.mem_range.mp hk
      exact ih k hkn (fun j hj => hproduct j (le_trans hj (Nat.le_of_lt hkn)))
    have hprod : F ∣ homogeneousComponent (c+n) (C*(B-truncateBelow n B)) := by
      rw [mul_sub, map_sub]
      exact dvd_sub (hproduct n le_rfl)
        (component_dvd_of_dvd hF (dvd_mul_of_dvd_right htrunc C) (c+n))
    rw [component_mul_initial hC (order_sub_truncateBelow n B),
      component_sub_truncateBelow] at hprod
    exact (hprime.dvd_mul.mp hprod).resolve_left hlegal

/-- A polynomial nonzero modulo `F` can be replaced, modulo `F`, by one
whose least homogeneous component is already nonzero modulo `F`. Only the
finitely many preceding homogeneous components are discarded. -/
theorem exists_legal_initial_representative (F p : MvPolynomial σ R)
    (hp : ¬ F ∣ p) :
    ∃ d : ℕ, ∃ q : MvPolynomial σ R,
      F ∣ p-q ∧ HasOrder d q ∧ ¬ F ∣ homogeneousComponent d q := by
  classical
  have hex : ∃ d : ℕ, ¬ F ∣ homogeneousComponent d p := by
    by_contra h
    push Not at h
    apply hp
    rw [← sum_homogeneousComponent p]
    exact Finset.dvd_sum (fun i _ => h i)
  let d := Nat.find hex
  have hfirst : ¬ F ∣ homogeneousComponent d p := Nat.find_spec hex
  have hprevious : ∀ k < d, F ∣ homogeneousComponent k p := by
    intro k hk
    by_contra hbad
    have hmin : d ≤ k := Nat.find_min' hex hbad
    omega
  have htrunc : F ∣ truncateBelow d p := by
    apply Finset.dvd_sum
    intro k hk
    exact hprevious k (Finset.mem_range.mp hk)
  refine ⟨d, p-truncateBelow d p, ?_, order_sub_truncateBelow d p, ?_⟩
  · simpa only [sub_sub_cancel] using htrunc
  · rwa [component_sub_truncateBelow]

/-- Multiplication by a fixed homogeneous normal derivative preserves a
legal initial component and makes its degree positive. -/
theorem legal_initial_mul_homogeneous {F g q : MvPolynomial σ R} {k d : ℕ}
    (hprime : Prime F) (hg : g.IsHomogeneous k) (hglegal : ¬ F ∣ g)
    (hq : HasOrder d q) (hqlegal : ¬ F ∣ homogeneousComponent d q) :
    HasOrder (k+d) (g*q) ∧ ¬ F ∣ homogeneousComponent (k+d) (g*q) := by
  refine ⟨(isHomogeneous_hasOrder hg).mul hq, ?_⟩
  rw [component_mul_initial (isHomogeneous_hasOrder hg) hq,
    homogeneousComponent_eq_self hg]
  intro h
  exact (hprime.dvd_mul.mp h).elim hglegal hqlegal

end HoldoutConstruction

end
end

end

section
/- Source component: HomogeneousField -/
section
/-!
Finite denominator replacement and homogeneous projection of rational fields.
These are intermediate lemmas, not a HasCertificate theorem.
-/

noncomputable section

namespace HoldoutConstruction

open MvPolynomial
open scoped BigOperators

variable {R σ : Type*} [CommRing R] [Fintype σ]

def polynomialDirectional (p : MvPolynomial σ R) (N : σ → MvPolynomial σ R) :
    MvPolynomial σ R := ∑ i, N i * pderiv i p

def polynomialDivergence (N : σ → MvPolynomial σ R) : MvPolynomial σ R :=
  ∑ i, pderiv i (N i)

def polynomialDivNum (D : MvPolynomial σ R) (N : σ → MvPolynomial σ R) :
    MvPolynomial σ R := D*polynomialDivergence N - polynomialDirectional D N

theorem polynomialDirectional_mul (p q : MvPolynomial σ R)
    (N : σ → MvPolynomial σ R) :
    polynomialDirectional (p*q) N =
      p*polynomialDirectional q N + q*polynomialDirectional p N := by
  simp only [polynomialDirectional, pderiv_mul, mul_add,
    Finset.sum_add_distrib, Finset.mul_sum]
  conv_rhs => rw [add_comm]
  apply congrArg₂ (·+·) <;> apply Finset.sum_congr rfl <;> intro i _ <;> ring

theorem polynomialDirectional_scale (p S : MvPolynomial σ R)
    (N : σ → MvPolynomial σ R) :
    polynomialDirectional p (fun i => S*N i) = S*polynomialDirectional p N := by
  simp only [polynomialDirectional, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem polynomialDivergence_scale (S : MvPolynomial σ R)
    (N : σ → MvPolynomial σ R) :
    polynomialDivergence (fun i => S*N i) =
      polynomialDirectional S N + S*polynomialDivergence N := by
  simp only [polynomialDivergence, polynomialDirectional, pderiv_mul,
    Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The exact identity behind finite geometric-series replacement of a
denominator. The original divergence may be a nonzero multiple of `F`. -/
theorem denominator_replacement_divergence
    (D S H U : MvPolynomial σ R) (N : σ → MvPolynomial σ R)
    (hDS : D*S = H-U) :
    D^2*polynomialDivNum H (fun i => S*N i) =
      H*(H-U)*polynomialDivNum D N -
        D*(H*polynomialDirectional U N - U*polynomialDirectional H N) := by
  have hd := congrArg (fun p => polynomialDirectional p N) hDS
  rw [polynomialDirectional_mul] at hd
  simp only [polynomialDirectional, map_sub,
    mul_sub, Finset.sum_sub_distrib] at hd
  change D*polynomialDirectional S N + S*polynomialDirectional D N =
    polynomialDirectional H N - polynomialDirectional U N at hd
  simp only [polynomialDivNum, polynomialDivergence_scale, polynomialDirectional_scale]
  linear_combination D*H*hd +
    (D*polynomialDivergence N - polynomialDirectional D N)*H*hDS -
    D*polynomialDirectional H N*hDS

theorem order_polynomialDirectional {n : ℕ} {p : MvPolynomial σ R}
    (hp : HasOrder n p) (N : σ → MvPolynomial σ R) :
    HasOrder (n-1) (polynomialDirectional p N) := by
  apply HasOrder.sum
  intro i _
  simpa using (hasOrder_zero_degree (N i)).mul (hp.pderiv i)

/-- Projection of the divergence numerator when the new denominator is
already homogeneous. -/
theorem component_polynomialDivNum {d : ℕ} {H : MvPolynomial σ R}
    (hd : 0 < d) (hH : H.IsHomogeneous d) (N : σ → MvPolynomial σ R) :
    homogeneousComponent (2*d) (polynomialDivNum H N) =
      polynomialDivNum H (fun i => homogeneousComponent (d+1) (N i)) := by
  have hderiv (i : σ) : (pderiv i H).IsHomogeneous (d-1) := by
    apply pderiv_isHomogeneous
    have he : d-1+1 = d := by omega
    simpa only [he] using hH
  simp only [polynomialDivNum, polynomialDivergence, polynomialDirectional, map_sub, map_sum]
  rw [show 2*d = d+d by omega, component_mul_homogeneous hH]
  simp only [map_sum, ← pderiv_component]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_comm (N i), show d+d = (d-1)+(d+1) by omega,
    component_mul_homogeneous (hderiv i)]
  ring

theorem component_polynomialDirectional {f d : ℕ} {F : MvPolynomial σ R}
    (hF : F.IsHomogeneous (f+1)) (N : σ → MvPolynomial σ R) :
    homogeneousComponent (f+d) (polynomialDirectional F N) =
      polynomialDirectional F (fun i => homogeneousComponent d (N i)) := by
  simp only [polynomialDirectional, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_comm (N i), component_mul_homogeneous (pderiv_isHomogeneous hF i)]
  ring

/-- A finite geometric sum; no rational function is integrated here. -/
def finiteInverse (D h : MvPolynomial σ R) (p : ℕ) : MvPolynomial σ R :=
  ∑ i ∈ Finset.range p, h^i * (h-D)^(p-1-i)

omit [Fintype σ] in
theorem finiteInverse_identity (D h : MvPolynomial σ R) (p : ℕ) :
    D*finiteInverse D h p = h^p - (h-D)^p := by
  rw [mul_comm]
  simpa only [finiteInverse, sub_sub_cancel] using geom_sum₂_mul h (h-D) p

/-- A normalized rational field with a legal initial denominator component
has homogeneous polynomial certificate data. The degree estimate is finite:
`p > d+1` suffices, and the new denominator has degree `p*d`.

The hypotheses allow a nonzero divergence quotient `Q`; this is the full
pole-order-one identity, not only its strict variant. -/
theorem homogeneous_data_from_initial_denominator
    [IsDomain R]
    (F A D : MvPolynomial σ R) (N : σ → MvPolynomial σ R) (Q : MvPolynomial σ R)
    (hF : F.IsHomogeneous 6) (hA : A.IsHomogeneous 6) (hprime : Prime F)
    (normal : polynomialDirectional F N = A*D)
    (divergence : polynomialDivNum D N = F*Q)
    (d : ℕ) (hd : 0 < d) (hD : HasOrder d D)
    (hlegal : ¬ F ∣ homogeneousComponent d D)
    (p : ℕ) (hp : d+1 < p) :
    ∃ H : MvPolynomial σ R, ∃ M : σ → MvPolynomial σ R, ∃ Q' : MvPolynomial σ R,
      H ≠ 0 ∧ H.IsHomogeneous (p*d) ∧ (∀ i, (M i).IsHomogeneous (p*d+1)) ∧
      IsRelPrime F H ∧ polynomialDirectional F M = A*H ∧
      polynomialDivNum H M = F*Q' := by
  classical
  let h := homogeneousComponent d D
  let H := h^p
  let U := (h-D)^p
  let S := finiteInverse D h p
  let M : σ → MvPolynomial σ R := fun i => S*N i
  let M' : σ → MvPolynomial σ R := fun i => homogeneousComponent (p*d+1) (M i)
  have hp0 : 0 < p := by omega
  have hpd : 0 < p*d := Nat.mul_pos hp0 hd
  have hh : h.IsHomogeneous d := homogeneousComponent_isHomogeneous d D
  have hH : H.IsHomogeneous (p*d) := by
    simpa only [H, Nat.mul_comm] using hh.pow p
  have hH0 : H ≠ 0 := by
    intro hz
    have hdiv : F ∣ h^p := by
      rw [show h^p = 0 from hz]
      exact dvd_zero F
    exact hlegal (hprime.dvd_of_dvd_pow hdiv)
  have hHlegal : IsRelPrime F H := by
    apply hprime.irreducible.isRelPrime_iff_not_dvd.mpr
    intro hv
    exact hlegal (hprime.dvd_of_dvd_pow hv)
  have hU : HasOrder (p*(d+1)) U := (order_sub_initial hD).pow p
  have hHorder : HasOrder (p*d) H := isHomogeneous_hasOrder hH
  have hDS : D*S = H-U := finiteInverse_identity D h p
  have hnormal : polynomialDirectional F M = A*(H-U) := by
    rw [show M = (fun i => S*N i) from rfl, polynomialDirectional_scale, normal]
    calc
      S*(A*D) = A*(D*S) := by ring
      _ = A*(H-U) := by rw [hDS]
  have hnormal' : polynomialDirectional F M' = A*H := by
    have hhcomp := congrArg (homogeneousComponent (p*d+6)) hnormal
    have hgrade : p*d+6 = 5+(p*d+1) := by omega
    rw [hgrade, component_polynomialDirectional (show F.IsHomogeneous (5+1) from hF)]
      at hhcomp
    have hAU : homogeneousComponent (p*d+6) (A*U) = 0 :=
      ((isHomogeneous_hasOrder hA).mul hU).component_eq_zero (by
        simp only [Nat.mul_add, Nat.mul_one]
        omega)
    have hAH : (A*H).IsHomogeneous (p*d+6) := by
      convert hA.mul hH using 1
      omega
    rw [← hgrade, mul_sub, map_sub, homogeneousComponent_eq_self hAH, hAU, sub_zero]
      at hhcomp
    exact hhcomp
  have herror : HasOrder (2*d+2*(p*d)+1)
      (-D*(H*polynomialDirectional U N-U*polynomialDirectional H N)) := by
    have hleft : HasOrder (p*d+p*(d+1)-1) (H*polynomialDirectional U N) :=
      (hHorder.mul (order_polynomialDirectional hU N)).mono (by omega)
    have hright : HasOrder (p*d+p*(d+1)-1) (U*polynomialDirectional H N) :=
      (hU.mul (order_polynomialDirectional hHorder N)).mono (by omega)
    have h := (hD.neg).mul (hleft.sub hright)
    exact h.mono (by
      simp only [Nat.mul_add, Nat.mul_one]
      omega)
  have hdivreplace := denominator_replacement_divergence D S H U N hDS
  rw [divergence] at hdivreplace
  have hproduct (k : ℕ) (hk : k ≤ 2*(p*d)) :
      F ∣ homogeneousComponent (2*d+k) (D^2*polynomialDivNum H M) := by
    rw [show M = (fun i => S*N i) from rfl, hdivreplace, sub_eq_add_neg, map_add]
    have hzero : homogeneousComponent (2*d+k)
        (-(D*(H*polynomialDirectional U N-U*polynomialDirectional H N))) = 0 := by
      apply HasOrder.component_eq_zero (by simpa only [neg_mul] using herror)
      omega
    rw [hzero, add_zero]
    exact component_dvd_of_dvd hF (dvd_mul_of_dvd_right (dvd_mul_right F Q) _) _
  have hCorder : HasOrder (2*d) (D^2) := by
    simpa only [pow_two, two_mul] using hD.mul hD
  have hClegal : ¬ F ∣ homogeneousComponent (2*d) (D^2) := by
    rw [pow_two, two_mul, component_mul_initial hD hD]
    intro hv
    exact (hprime.dvd_mul.mp hv).elim hlegal hlegal
  have hB := component_dvd_of_product hF hprime hCorder hClegal (2*(p*d)) hproduct
  rw [component_polynomialDivNum hpd hH] at hB
  obtain ⟨Q', hQ'⟩ := hB
  refine ⟨H, M', Q', hH0, hH, ?_, hHlegal, hnormal', hQ'⟩
  intro i
  exact homogeneousComponent_isHomogeneous (p*d+1) (M i)

end HoldoutConstruction

end
end

end

section
/- Source component: HypersurfaceDomain -/
section
/-!
Domain lemmas for the Fermat-curve base and its weighted quotient hypersurface.
These are intermediate construction lemmas, not a HasCertificate theorem.
Prepared with OpenAI ChatGPT assistance for contribution through fqlx.
-/

noncomputable section

namespace HoldoutConstruction

open Polynomial

section MonicEmbedding

variable {R T : Type*} [CommRing R] [CommRing T]

/-- A monic polynomial quotient embeds after any injective coefficient map. -/
theorem adjoinRoot_map_injective (φ : R →+* T) (hφ : Function.Injective φ)
    (f : R[X]) (hf : f.Monic) :
    Function.Injective (AdjoinRoot.map φ f (f.map φ) (dvd_refl _)) := by
  rw [injective_iff_map_eq_zero]
  intro z hz
  induction z using AdjoinRoot.induction_on with
  | ih p =>
    have hp : (f.map φ) ∣ p.map φ := by
      change p.eval₂ ((AdjoinRoot.of (f.map φ)).comp φ)
        (AdjoinRoot.root (f.map φ)) = 0 at hz
      rw [← Polynomial.eval₂_map, ← AdjoinRoot.algebraMap_eq,
        ← Polynomial.aeval_def, AdjoinRoot.aeval_eq] at hz
      exact AdjoinRoot.mk_eq_zero.mp hz
    exact AdjoinRoot.mk_eq_zero.mpr ((Polynomial.map_dvd_map φ hφ hf).mp hp)

/-- Domainhood of a monic polynomial quotient descends along an injective
coefficient map. -/
theorem adjoinRoot_isDomain_of_monic_map (φ : R →+* T) (hφ : Function.Injective φ)
    (f : R[X]) (hf : f.Monic) [IsDomain (AdjoinRoot (f.map φ))] :
    IsDomain (AdjoinRoot f) :=
  (adjoinRoot_map_injective φ hφ f hf).isDomain _

end MonicEmbedding

section Eisenstein

variable {R : Type*} [CommRing R] [IsDomain R]

/-- A simple zero of the constant coefficient gives an elementary Eisenstein
criterion for the outer polynomial. The two occurrences of `X` belong to
different polynomial rings. -/
theorem irreducible_power_add_constant (g : R[X])
    (h0 : g.coeff 0 = 0) (h1 : g.coeff 1 ≠ 0) (n : ℕ) (hn : 0 < n) :
    Irreducible ((X : (R[X])[X])^n + C g) := by
  let P : Ideal R[X] := Ideal.span {X}
  have hP : P.IsPrime := (Ideal.span_singleton_prime (by simp)).mpr Polynomial.prime_X
  have hm : ((X : (R[X])[X])^n + C g).Monic :=
    monic_X_pow_add_C g (Nat.ne_of_gt hn)
  have he : ((X : (R[X])[X])^n + C g).IsEisensteinAt P :=
    hm.isEisensteinAt_of_mem_of_notMem hP.ne_top (by
      intro k hk
      rw [natDegree_X_pow_add_C] at hk
      simp only [coeff_add, coeff_X_pow, if_neg (Nat.ne_of_lt hk), zero_add, coeff_C]
      split_ifs
      · exact Ideal.mem_span_singleton.mpr (Polynomial.X_dvd_iff.mpr h0)
      · exact Ideal.zero_mem P) (by
      simp only [coeff_add, coeff_X_pow, if_neg (Nat.ne_of_lt hn), coeff_C_zero,
        zero_add]
      intro hg
      have hd : (X : R[X])^2 ∣ g := by
        simpa only [P, Ideal.span_singleton_pow, Ideal.mem_span_singleton] using hg
      exact h1 ((Polynomial.X_pow_dvd_iff.mp hd) 1 (by decide)))
  exact he.irreducible hP hm.isPrimitive (by simpa using hn)

end Eisenstein

section QuotientHypersurface

variable {R : Type*} [CommRing R]

/-- The weighted quotient equation, viewed as a monic polynomial in `X0`.
The four coefficient variables are `X1`, `X2`, `S`, and `P`, in this order. -/
def quotientPolynomial (alpha beta : R) : (MvPolynomial (Fin 4) R)[X] :=
  X^6 + (C (MvPolynomial.C alpha * MvPolynomial.X 0 * MvPolynomial.X 3) * X^3 +
    C (MvPolynomial.X 0^6 + MvPolynomial.X 1^6 +
      MvPolynomial.C beta * MvPolynomial.X 0^3 * MvPolynomial.X 1 * MvPolynomial.X 3 +
      MvPolynomial.X 2^3 - 3 * MvPolynomial.X 2 * MvPolynomial.X 3^2))

theorem quotientPolynomial_monic (alpha beta : R) :
    (quotientPolynomial alpha beta).Monic := by
  apply monic_X_pow_add
  apply lt_of_le_of_lt (degree_add_le _ _)
  apply max_lt
  · exact lt_of_le_of_lt (degree_C_mul_X_pow_le 3 _) (by decide)
  · exact lt_of_le_of_lt degree_C_le (by decide)

/-- This specialization fixes `S`, sets `X1=X2=0`, and sets `P=1`. -/
def quotientSpecialization : MvPolynomial (Fin 4) R →+* R[X] :=
  MvPolynomial.eval₂Hom C ![0, 0, X, 1]

theorem quotientPolynomial_specialization (alpha beta : R) :
    (quotientPolynomial alpha beta).map quotientSpecialization =
      (X : (R[X])[X])^6 + C (X^3 - 3*X) := by
  simp [quotientPolynomial, quotientSpecialization]

theorem quotientPolynomial_irreducible [IsDomain R] [CharZero R]
    (alpha beta : R) : Irreducible (quotientPolynomial alpha beta) := by
  apply (quotientPolynomial_monic alpha beta).irreducible_of_irreducible_map
    quotientSpecialization
  rw [quotientPolynomial_specialization]
  exact irreducible_power_add_constant (X^3 - 3*X : R[X])
    (by simp) (by norm_num) 6 (by decide)

theorem quotientPolynomial_map {T : Type*} [CommRing T]
    (φ : R →+* T) (alpha beta : R) :
    (quotientPolynomial alpha beta).map (MvPolynomial.map φ) =
      quotientPolynomial (φ alpha) (φ beta) := by
  simp [quotientPolynomial]

/-- The affine weighted quotient is integral over every characteristic-zero
coefficient domain, including the coordinate domain of the Fermat base curve.
Unique factorization is used only after passing to the coefficient fraction
field; monicity descends domainhood back to the original coefficient ring. -/
theorem quotient_adjoinRoot_isDomain [IsDomain R] [CharZero R]
    (alpha beta : R) : IsDomain (AdjoinRoot (quotientPolynomial alpha beta)) := by
  let φ : R →+* FractionRing R := algebraMap R (FractionRing R)
  have hφ : Function.Injective φ := IsFractionRing.injective R (FractionRing R)
  have hmap : IsDomain (AdjoinRoot
      ((quotientPolynomial alpha beta).map (MvPolynomial.map φ))) := by
    rw [quotientPolynomial_map]
    exact AdjoinRoot.isDomain_of_prime
      (quotientPolynomial_irreducible (φ alpha) (φ beta)).prime
  let := hmap
  exact adjoinRoot_isDomain_of_monic_map (MvPolynomial.map φ)
    (MvPolynomial.map_injective φ hφ) _ (quotientPolynomial_monic alpha beta)

end QuotientHypersurface

section FermatBase

variable {R : Type*} [CommRing R]

/-- The affine Fermat-curve equation `alpha^6 + beta^6 = 1`, viewed as a
monic polynomial in `alpha` with coefficients in `R[beta]`. -/
def fermatCurvePolynomial : (R[X])[X] := X^6 + C (X^6 - 1)

theorem fermatCurvePolynomial_monic : (fermatCurvePolynomial (R := R)).Monic :=
  monic_X_pow_add_C _ (by decide)

theorem fermatCurvePolynomial_irreducible [IsDomain R] [CharZero R] :
    Irreducible (fermatCurvePolynomial (R := R)) := by
  apply (fermatCurvePolynomial_monic (R := R)).irreducible_of_irreducible_map
    (Polynomial.eval₂RingHom C (X+1))
  have he : (fermatCurvePolynomial (R := R)).map
      (Polynomial.eval₂RingHom C (X+1)) = X^6 + C ((X+1)^6 - 1) := by
    simp [fermatCurvePolynomial]
  rw [he]
  exact irreducible_power_add_constant ((X+1)^6 - 1 : R[X])
    (by simp [coeff_X_add_one_pow]) (by norm_num [coeff_X_add_one_pow, coeff_one])
    6 (by decide)

theorem fermatCurvePolynomial_map {T : Type*} [CommRing T] (φ : R →+* T) :
    (fermatCurvePolynomial (R := R)).map (Polynomial.mapRingHom φ) =
      fermatCurvePolynomial (R := T) := by
  simp [fermatCurvePolynomial]

/-- The affine Fermat-curve coordinate ring is a domain over every
characteristic-zero coefficient domain. -/
theorem fermatCurve_adjoinRoot_isDomain [IsDomain R] [CharZero R] :
    IsDomain (AdjoinRoot (fermatCurvePolynomial (R := R))) := by
  let φ : R →+* FractionRing R := algebraMap R (FractionRing R)
  have hφ : Function.Injective φ := IsFractionRing.injective R (FractionRing R)
  have hmap : IsDomain (AdjoinRoot
      ((fermatCurvePolynomial (R := R)).map (Polynomial.mapRingHom φ))) := by
    rw [fermatCurvePolynomial_map]
    exact AdjoinRoot.isDomain_of_prime
      (fermatCurvePolynomial_irreducible (R := FractionRing R)).prime
  let := hmap
  exact adjoinRoot_isDomain_of_monic_map (Polynomial.mapRingHom φ)
    (Polynomial.map_injective φ hφ) _ fermatCurvePolynomial_monic

end FermatBase

end HoldoutConstruction

end
end

end

section
/- Source component: HypersurfaceCoordinates -/
section
/-!
Multivariate coordinate versions of the integral-domain lemmas. The original
holdout sextic is kept fixed throughout. These are intermediate construction
lemmas, not a HasCertificate theorem.
-/

noncomputable section

namespace HoldoutConstruction

open Polynomial

section WeightedQuotient

variable {R : Type*} [CommRing R]

/-- Coordinate order: `X0, X1, X2, S, P`. -/
def weightedHypersurface (alpha beta : R) : MvPolynomial (Fin 5) R :=
  MvPolynomial.X 0^6 + MvPolynomial.X 1^6 + MvPolynomial.X 2^6 +
    MvPolynomial.X 4 * (MvPolynomial.C alpha * MvPolynomial.X 0^3 * MvPolynomial.X 1 +
      MvPolynomial.C beta * MvPolynomial.X 1^3 * MvPolynomial.X 2) +
    MvPolynomial.X 3^3 - 3*MvPolynomial.X 3*MvPolynomial.X 4^2

theorem weightedHypersurface_univariate (alpha beta : R) :
    MvPolynomial.finSuccEquiv R 4 (weightedHypersurface alpha beta) =
      quotientPolynomial alpha beta := by
  have he : (Fin.cases (X : (MvPolynomial (Fin 4) R)[X]) (fun j => C (MvPolynomial.X j))) =
      ![X, C (MvPolynomial.X 0), C (MvPolynomial.X 1),
        C (MvPolynomial.X 2), C (MvPolynomial.X 3)] := by
    funext i
    fin_cases i <;> rfl
  simp [weightedHypersurface, quotientPolynomial, MvPolynomial.finSuccEquiv_apply, he,
    Polynomial.C_ofNat]
  ring

theorem weightedHypersurface_irreducible [IsDomain R] [CharZero R]
    (alpha beta : R) : Irreducible (weightedHypersurface alpha beta) := by
  apply (MulEquiv.irreducible_iff (MvPolynomial.finSuccEquiv R 4)).mp
  rw [weightedHypersurface_univariate]
  exact quotientPolynomial_irreducible alpha beta

theorem weightedHypersurface_quotient_isDomain [IsDomain R] [CharZero R]
    (alpha beta : R) :
    IsDomain (MvPolynomial (Fin 5) R ⧸ Ideal.span {weightedHypersurface alpha beta}) := by
  let hdomain : IsDomain ((MvPolynomial (Fin 4) R)[X] ⧸
      Ideal.span {quotientPolynomial alpha beta}) := by
    change IsDomain (AdjoinRoot (quotientPolynomial alpha beta))
    exact quotient_adjoinRoot_isDomain alpha beta
  let e := Ideal.quotientEquiv (Ideal.span {weightedHypersurface alpha beta})
    (Ideal.span {quotientPolynomial alpha beta})
    (MvPolynomial.finSuccEquiv R 4).toRingEquiv (by
      rw [Ideal.map_span, Set.image_singleton]
      change Ideal.span {quotientPolynomial alpha beta} =
        Ideal.span {MvPolynomial.finSuccEquiv R 4 (weightedHypersurface alpha beta)}
      rw [weightedHypersurface_univariate])
  exact e.injective.isDomain e.toRingHom

end WeightedQuotient

section OriginalHoldout

variable {R : Type*} [CommRing R]

/-- The exact holdout sextic, monic in `X0`. The coefficient variables are
`X1, X2, Y0, Y1, Y2`, in this order. -/
def holdoutPolynomial : (MvPolynomial (Fin 5) R)[X] :=
  X^6 + (C (MvPolynomial.X 0 * MvPolynomial.X 2 * MvPolynomial.X 3) * X^3 +
    C (MvPolynomial.X 0^6 + MvPolynomial.X 1^6 + MvPolynomial.X 2^6 +
      MvPolynomial.X 3^6 + MvPolynomial.X 4^6 +
      MvPolynomial.X 0^3 * MvPolynomial.X 1 * MvPolynomial.X 3 * MvPolynomial.X 4))

theorem holdoutPolynomial_monic : (holdoutPolynomial (R := R)).Monic := by
  apply monic_X_pow_add
  apply lt_of_le_of_lt (degree_add_le _ _)
  apply max_lt
  · exact lt_of_le_of_lt (degree_C_mul_X_pow_le 3 _) (by decide)
  · exact lt_of_le_of_lt degree_C_le (by decide)

/-- `eta` may be any sixth root of `-1`; over the complex numbers one can
take `eta = I`. -/
def holdoutSpecialization (eta : R) : MvPolynomial (Fin 5) R →+* R[X] :=
  MvPolynomial.eval₂Hom C ![0, 0, X+1, 0, C eta]

theorem holdoutPolynomial_specialization (eta : R) (heta : eta^6 = -1) :
    (holdoutPolynomial (R := R)).map (holdoutSpecialization eta) =
      (X : (R[X])[X])^6 + C ((X+1)^6 - 1) := by
  simp [holdoutPolynomial, holdoutSpecialization, ← map_pow, heta, sub_eq_add_neg]

theorem holdoutPolynomial_irreducible [IsDomain R] [CharZero R]
    (eta : R) (heta : eta^6 = -1) :
    Irreducible (holdoutPolynomial (R := R)) := by
  apply (holdoutPolynomial_monic (R := R)).irreducible_of_irreducible_map
    (holdoutSpecialization eta)
  rw [holdoutPolynomial_specialization eta heta]
  exact irreducible_power_add_constant ((X+1)^6 - 1 : R[X])
    (by simp [coeff_X_add_one_pow]) (by norm_num [coeff_X_add_one_pow, coeff_one])
    6 (by decide)

/-- Coordinate order: `X0, X1, X2, Y0, Y1, Y2`. -/
def holdoutSextic : MvPolynomial (Fin 6) R :=
  MvPolynomial.X 0^6 + MvPolynomial.X 0^3*MvPolynomial.X 1*MvPolynomial.X 3*MvPolynomial.X 4 +
    MvPolynomial.X 1^6 + MvPolynomial.X 1^3*MvPolynomial.X 2*MvPolynomial.X 4*MvPolynomial.X 5 +
    MvPolynomial.X 2^6 + MvPolynomial.X 3^6 + MvPolynomial.X 4^6 + MvPolynomial.X 5^6

theorem holdoutSextic_univariate :
    MvPolynomial.finSuccEquiv R 5 (holdoutSextic (R := R)) =
      holdoutPolynomial (R := R) := by
  have he : (Fin.cases (X : (MvPolynomial (Fin 5) R)[X]) (fun j => C (MvPolynomial.X j))) =
      ![X, C (MvPolynomial.X 0), C (MvPolynomial.X 1),
        C (MvPolynomial.X 2), C (MvPolynomial.X 3), C (MvPolynomial.X 4)] := by
    funext i
    fin_cases i <;> rfl
  simp [holdoutSextic, holdoutPolynomial, MvPolynomial.finSuccEquiv_apply, he]
  ring

theorem holdoutSextic_irreducible [IsDomain R] [CharZero R]
    (eta : R) (heta : eta^6 = -1) : Irreducible (holdoutSextic (R := R)) := by
  apply (MulEquiv.irreducible_iff (MvPolynomial.finSuccEquiv R 5)).mp
  rw [holdoutSextic_univariate]
  exact holdoutPolynomial_irreducible eta heta

/-- Restriction to the `X0` axis. -/
def holdoutAxis : MvPolynomial (Fin 6) R →+* R[X] :=
  MvPolynomial.eval₂Hom C ![X, 0, 0, 0, 0, 0]

theorem holdoutAxis_equation :
    holdoutAxis (holdoutSextic (R := R)) = X^6 := by
  simp [holdoutAxis, holdoutSextic]

theorem holdoutAxis_gradient :
    holdoutAxis (MvPolynomial.pderiv 0 (holdoutSextic (R := R))) = 6*X^5 := by
  norm_num [holdoutAxis, holdoutSextic, MvPolynomial.pderiv_pow,
    MvPolynomial.pderiv_mul, Polynomial.C_ofNat, Pi.single_apply,
    show (2 : Fin 6) ≠ 0 by decide, show (3 : Fin 6) ≠ 0 by decide,
    show (4 : Fin 6) ≠ 0 by decide, show (5 : Fin 6) ≠ 0 by decide]

/-- The distinguished normal derivative stays nonzero on the hypersurface.
No smoothness theorem is required: divisibility would survive restriction to
the `X0` axis, where `X0^6` cannot divide `6 X0^5`. -/
theorem holdoutSextic_not_dvd_pderiv_zero [CharZero R] :
    ¬ holdoutSextic (R := R) ∣ MvPolynomial.pderiv 0 (holdoutSextic (R := R)) := by
  intro hd
  have hm := map_dvd (holdoutAxis (R := R)) hd
  rw [holdoutAxis_equation, holdoutAxis_gradient] at hm
  have hc := (Polynomial.X_pow_dvd_iff.mp hm) 5 (by decide)
  norm_num at hc

end OriginalHoldout

section HoldoutQuotient

variable {R : Type*} [Field R] [CharZero R]

theorem holdoutSextic_quotient_isDomain
    (eta : R) (heta : eta^6 = -1) :
    IsDomain (MvPolynomial (Fin 6) R ⧸ Ideal.span {holdoutSextic (R := R)}) :=
  (Ideal.Quotient.isDomain_iff_prime _).mpr
    ((Ideal.span_singleton_prime
      (holdoutSextic_irreducible eta heta).ne_zero).mpr
        (holdoutSextic_irreducible eta heta).prime)

end HoldoutQuotient

end HoldoutConstruction

end
end

end

section
/- Source component: HomogeneousNormalization -/
section
/-!
Changing a denominator modulo the hypersurface, then extracting homogeneous
data. Every identity below is finite polynomial arithmetic. These lemmas
accept a normalized rational certificate with arbitrary legal denominator;
they are not a certificate for any particular sextic by themselves.
-/

noncomputable section

namespace HoldoutConstruction

open MvPolynomial
open scoped BigOperators

variable {R σ : Type*} [CommRing R] [Fintype σ]

theorem polynomialDirectional_add (p : MvPolynomial σ R)
    (N M : σ → MvPolynomial σ R) :
    polynomialDirectional p (fun i => N i + M i) =
      polynomialDirectional p N + polynomialDirectional p M := by
  simp only [polynomialDirectional, add_mul, Finset.sum_add_distrib]

theorem polynomialDirectional_add_source (p q : MvPolynomial σ R)
    (N : σ → MvPolynomial σ R) :
    polynomialDirectional (p+q) N =
      polynomialDirectional p N + polynomialDirectional q N := by
  simp only [polynomialDirectional, map_add, mul_add, Finset.sum_add_distrib]

theorem polynomialDivergence_add (N M : σ → MvPolynomial σ R) :
    polynomialDivergence (fun i => N i + M i) =
      polynomialDivergence N + polynomialDivergence M := by
  simp only [polynomialDivergence, map_add, Finset.sum_add_distrib]

theorem polynomialDirectional_single [DecidableEq σ]
    (p a : MvPolynomial σ R) (i : σ) :
    polynomialDirectional p (Pi.single i a) = a*pderiv i p := by
  simp [polynomialDirectional, Pi.single_apply]

theorem polynomialDivergence_single [DecidableEq σ]
    (a : MvPolynomial σ R) (i : σ) :
    polynomialDivergence (Pi.single i a) = pderiv i a := by
  simp [polynomialDivergence, Pi.single_apply, apply_ite]

/-- Moving a denominator by a multiple of `F` can be compensated by one
normal component, after multiplying every component by `∂ᵢF`. -/
theorem denominator_congruence_normal [DecidableEq σ]
    (F A D U : MvPolynomial σ R) (N : σ → MvPolynomial σ R) (i : σ)
    (normal : polynomialDirectional F N = A*D) :
    polynomialDirectional F
      (fun j => pderiv i F*N j + (Pi.single i (A*F*U) : σ → MvPolynomial σ R) j) =
      A*(pderiv i F*(D+F*U)) := by
  rw [polynomialDirectional_add, polynomialDirectional_scale,
    polynomialDirectional_single, normal]
  ring

/-- The correction of the divergence numerator is visibly divisible by
`F`. The original divergence quotient is allowed to be nonzero. -/
theorem denominator_congruence_divergence [DecidableEq σ]
    (F A D U : MvPolynomial σ R) (N : σ → MvPolynomial σ R) (i : σ)
    (normal : polynomialDirectional F N = A*D) :
    polynomialDivNum (pderiv i F*(D+F*U))
      (fun j => pderiv i F*N j + (Pi.single i (A*F*U) : σ → MvPolynomial σ R) j) =
      (pderiv i F)^2*polynomialDivNum D N + F*
        ((pderiv i F)^2*(U*polynomialDivergence N-polynomialDirectional U N) +
          pderiv i F*(D+F*U)*pderiv i A*U +
          pderiv i F*D*A*pderiv i U -
          A*U*(D+F*U)*pderiv i (pderiv i F) -
          A*U*pderiv i F*pderiv i D) := by
  simp only [polynomialDivNum, polynomialDivergence_add, polynomialDivergence_scale,
    polynomialDivergence_single, polynomialDirectional_add, polynomialDirectional_scale,
    polynomialDirectional_single, polynomialDirectional_mul,
    polynomialDirectional_add_source, pderiv_mul, map_add, normal]
  ring

/-- An arbitrary legal normalized denominator can be replaced by one whose
initial component is legal, with positive degree. This step does not use
residue fields, formal series, or a choice of representatives in a field. -/
theorem normalized_data_with_legal_initial [IsDomain R]
    (F A D : MvPolynomial σ R) (N : σ → MvPolynomial σ R) (Q : MvPolynomial σ R)
    (hF : F.IsHomogeneous 6) (hprime : Prime F) (hlegal : ¬ F ∣ D)
    (normal : polynomialDirectional F N = A*D)
    (divergence : polynomialDivNum D N = F*Q)
    (i : σ) (hchart : ¬ F ∣ pderiv i F) :
    ∃ d : ℕ, ∃ D' : MvPolynomial σ R, ∃ N' : σ → MvPolynomial σ R,
      ∃ Q' : MvPolynomial σ R,
        0 < d ∧ HasOrder d D' ∧ ¬ F ∣ homogeneousComponent d D' ∧
        polynomialDirectional F N' = A*D' ∧ polynomialDivNum D' N' = F*Q' := by
  classical
  obtain ⟨d, q, hdifference, horder, hqlegal⟩ :=
    exists_legal_initial_representative F D hlegal
  have hdifference' : F ∣ q-D := by
    simpa only [neg_sub] using (dvd_neg.mpr hdifference)
  obtain ⟨U, hU⟩ := hdifference'
  have hq : q = D+F*U := by linear_combination hU
  let g := pderiv i F
  let D' := g*q
  let N' : σ → MvPolynomial σ R :=
    fun j => g*N j+(Pi.single i (A*F*U) : σ → MvPolynomial σ R) j
  let V := g^2*(U*polynomialDivergence N-polynomialDirectional U N) +
    g*(D+F*U)*pderiv i A*U+g*D*A*pderiv i U-
      A*U*(D+F*U)*pderiv i g-A*U*g*pderiv i D
  have hg : g.IsHomogeneous 5 := pderiv_isHomogeneous hF i
  have hinitial := legal_initial_mul_homogeneous hprime hg hchart horder hqlegal
  refine ⟨5+d, D', N', g^2*Q+V, by omega, hinitial.1, hinitial.2, ?_, ?_⟩
  · dsimp [D', N', g]
    rw [hq]
    exact denominator_congruence_normal F A D U N i normal
  · dsimp [D', N', g, V]
    rw [hq, denominator_congruence_divergence F A D U N i normal, divergence]
    ring

/-- Finite homogeneous extraction for every normalized pole-order-one
certificate on a homogeneous sextic, once a nonzero normal chart is given.
No bound on the initial denominator degree is assumed. -/
theorem homogeneous_data_of_normalized [IsDomain R]
    (F A D : MvPolynomial σ R) (N : σ → MvPolynomial σ R) (Q : MvPolynomial σ R)
    (hF : F.IsHomogeneous 6) (hA : A.IsHomogeneous 6) (hprime : Prime F)
    (hlegal : ¬ F ∣ D)
    (normal : polynomialDirectional F N = A*D)
    (divergence : polynomialDivNum D N = F*Q)
    (i : σ) (hchart : ¬ F ∣ pderiv i F) :
    ∃ d : ℕ, ∃ H : MvPolynomial σ R, ∃ M : σ → MvPolynomial σ R,
      ∃ Q' : MvPolynomial σ R,
        H ≠ 0 ∧ H.IsHomogeneous d ∧ (∀ j, (M j).IsHomogeneous (d+1)) ∧
        IsRelPrime F H ∧ polynomialDirectional F M = A*H ∧
        polynomialDivNum H M = F*Q' := by
  obtain ⟨d, D', N', Q', hd, horder, hlegal', hnormal, hdiv⟩ :=
    normalized_data_with_legal_initial F A D N Q hF hprime hlegal normal divergence i hchart
  obtain ⟨H, M, Q'', hH, hhom, hM, hcoprime, hnormal', hdiv'⟩ :=
    homogeneous_data_from_initial_denominator F A D' N' Q' hF hA hprime hnormal hdiv
      d hd horder hlegal' (d+2) (by omega)
  exact ⟨(d+2)*d, H, M, Q'', hH, hhom, hM, hcoprime, hnormal', hdiv'⟩

end HoldoutConstruction



end
end

/- Source component: HodgeHomogeneousBridge -/
section
/-!
The final homogeneous-data interface to the unchanged HodgeComputer verifier.
The exact holdout corollary is conditional on normalized polynomial data;
this file alone does not supply that data or solve the instance.
-/

noncomputable section

namespace HoldoutConstruction

open MvPolynomial

theorem polynomialDirectional_eq_directional
    {R σ : Type*} [CommRing R] [Fintype σ]
    (p : MvPolynomial σ R) (N : σ → MvPolynomial σ R) :
    polynomialDirectional p N = HodgeTestbed.directional p N := by
  simp only [polynomialDirectional, HodgeTestbed.directional, mul_comm]

theorem polynomialDivNum_eq_divergenceNumerator
    {R σ : Type*} [CommRing R] [Fintype σ]
    (D : MvPolynomial σ R) (N : σ → MvPolynomial σ R) :
    polynomialDivNum D N = HodgeTestbed.divergenceNumerator D N := by
  simp only [polynomialDivNum, HodgeTestbed.divergenceNumerator,
    polynomialDivergence, HodgeTestbed.divergence, polynomialDirectional_eq_directional]

/-- Homogeneity imposes no extra obstruction once legal normalized
pole-order-one polynomial data have been obtained on this normal chart. -/
theorem hasCertificate_of_normalized
    (F A D : HodgeComputer.Sextic.Poly) (N : Fin 6 → HodgeComputer.Sextic.Poly)
    (Q : HodgeComputer.Sextic.Poly)
    (hF : F.IsHomogeneous 6) (hA : A.IsHomogeneous 6) (hprime : Prime F)
    (hlegal : IsRelPrime F D)
    (normal : HodgeTestbed.directional F N = A*D)
    (divergence : HodgeTestbed.divergenceNumerator D N = F*Q)
    (i : Fin 6) (hchart : ¬ F ∣ pderiv i F) :
    HodgeComputer.HasCertificate (n := 5) F A 6 1 := by
  have hnormal : polynomialDirectional F N = A*D := by
    exact (polynomialDirectional_eq_directional F N).trans normal
  have hdivergence : polynomialDivNum D N = F*Q := by
    exact (polynomialDivNum_eq_divergenceNumerator D N).trans divergence
  obtain ⟨d, H, M, Q', hH0, hH, hM, hcoprime, hnormal', hdiv'⟩ :=
    homogeneous_data_of_normalized F A D N Q hF hA hprime
      (hprime.irreducible.isRelPrime_iff_not_dvd.mp hlegal)
      hnormal hdivergence i hchart
  refine ⟨H, M, Q', ⟨hprime.ne_zero, hF, ?_, hH0, ?_, ?_, hcoprime, ?_⟩⟩
  · simpa using HodgeComputer.Homogeneous.of_isHomogeneous hA
  · rw [hH.totalDegree hH0]
    exact hH
  · intro j
    rw [hH.totalDegree hH0]
    convert HodgeComputer.Homogeneous.of_isHomogeneous (hM j) using 1
    push_cast
    omega
  · apply HodgeComputer.normalized_identity
    · simpa only [Nat.cast_one, one_mul, polynomialDirectional_eq_directional] using hnormal'
    · simpa only [pow_one, polynomialDivNum_eq_divergenceNumerator] using hdiv'

end HoldoutConstruction



end
end

end

end HodgeComputerFormalHomCertAux

theorem solution
    (F A D : HodgeComputer.Sextic.Poly) (N : Fin 6 → HodgeComputer.Sextic.Poly)
    (Q : HodgeComputer.Sextic.Poly)
    (hF : F.IsHomogeneous 6) (hA : A.IsHomogeneous 6) (hprime : Prime F)
    (hlegal : IsRelPrime F D)
    (normal : HodgeTestbed.directional F N = A * D)
    (divergence : HodgeTestbed.divergenceNumerator D N = F * Q)
    (i : Fin 6) (hchart : ¬ F ∣ MvPolynomial.pderiv i F) :
    HodgeComputer.HasCertificate (n := 5) F A 6 1 :=
  HodgeComputerFormalHomCertAux.HoldoutConstruction.hasCertificate_of_normalized
    F A D N Q hF hA hprime hlegal normal divergence i hchart
