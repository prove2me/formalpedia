-- Prove2me | solution 1 for HodgeComputer.FourPlusTwoResidual.coreCertificate_of_ungraded
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-22T21:02:23.950695+00:00
-- url     : https://prove2.me/submissions/ce3cb152-7793-47be-a8ab-ca440fabd42d

import Definitions.Def_HodgeComputerFourPlusTwoCore
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic

/-!
Finite homogeneous extraction for the exact four-variable core of four-plus-two-residual.
The finite geometric-sum argument comes from the Phase 4 packet. The helper lemmas in
`FourPlusTwoFiniteExtraction` adapt the shared Hodge Computer HoldoutCover modules
`HomogeneousOrder` and `HomogeneousField`, from the accepted holdout work by `fqlx`.
-/
set_option autoImplicit false
noncomputable section
open MvPolynomial
open scoped BigOperators

namespace HodgeComputer.FourPlusTwoResidual.FourPlusTwoFiniteExtraction
variable {R σ : Type*} [CommRing R]

def HasOrder (n : ℕ) (p : MvPolynomial σ R) : Prop :=
  ∀ m : σ →₀ ℕ, m.degree < n → coeff m p = 0

theorem HasOrder.mono {n k : ℕ} {p : MvPolynomial σ R}
    (h : HasOrder n p) (hk : k ≤ n) : HasOrder k p :=
  fun m hm => h m (lt_of_lt_of_le hm hk)

theorem hasOrder_zero_degree (p : MvPolynomial σ R) : HasOrder 0 p := by
  intro m hm
  omega

theorem HasOrder.add {n : ℕ} {p q : MvPolynomial σ R}
    (hp : HasOrder n p) (hq : HasOrder n q) : HasOrder n (p+q) := by
  intro m hm
  simp [coeff_add, hp m hm, hq m hm]

theorem HasOrder.sub {n : ℕ} {p q : MvPolynomial σ R}
    (hp : HasOrder n p) (hq : HasOrder n q) : HasOrder n (p-q) := by
  intro m hm
  simp [coeff_sub, hp m hm, hq m hm]

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
  have h := congrArg (coeff m) (hp m.degree hm)
  simpa [coeff_homogeneousComponent] using h

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

theorem order_sub_initial {n : ℕ} {p : MvPolynomial σ R}
    (hp : HasOrder n p) : HasOrder (n+1) (homogeneousComponent n p - p) := by
  classical
  intro m hm
  rw [coeff_sub, coeff_homogeneousComponent]
  by_cases h : m.degree = n
  · simp [h]
  · have hlt : m.degree < n := by omega
    simp [h, hp _ hlt]

variable [Fintype σ]

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

def finiteInverse (D h : MvPolynomial σ R) (p : ℕ) : MvPolynomial σ R :=
  ∑ i ∈ Finset.range p, h^i * (h-D)^(p-1-i)

omit [Fintype σ] in
theorem finiteInverse_identity (D h : MvPolynomial σ R) (p : ℕ) :
    D*finiteInverse D h p = h^p - (h-D)^p := by
  rw [mul_comm]
  simpa only [finiteInverse, sub_sub_cancel] using geom_sum₂_mul h (h-D) p

private abbrev CorePoly := MvPolynomial (Fin 4) ℂ

private lemma core_hom : core.IsHomogeneous 6 := by
  have hX := isHomogeneous_X (σ := Fin 4) ℂ
  have hC := isHomogeneous_C (Fin 4) (R := ℂ)
  have t1 : (X 0 ^ 6 : CorePoly).IsHomogeneous 6 := (hX 0).pow 6
  have t2 : (C (5 / 7 : ℂ) * X 0 ^ 5 * X 1 : CorePoly).IsHomogeneous 6 :=
    ((hC _).mul ((hX 0).pow 5)).mul (hX 1)
  have t3 : (C (5 / 7 : ℂ) * X 0 ^ 3 * X 1 * X 2 * X 3 : CorePoly).IsHomogeneous 6 :=
    ((((hC _).mul ((hX 0).pow 3)).mul (hX 1)).mul (hX 2)).mul (hX 3)
  have t4 : (C (10 / 7 : ℂ) * X 0 * X 1 ^ 5 : CorePoly).IsHomogeneous 6 :=
    ((hC _).mul (hX 0)).mul ((hX 1).pow 5)
  have t5 : (C (10 / 7 : ℂ) * X 0 * X 1 * X 2 ^ 3 * X 3 : CorePoly).IsHomogeneous 6 :=
    ((((hC _).mul (hX 0)).mul (hX 1)).mul ((hX 2).pow 3)).mul (hX 3)
  have t6 : (X 1 ^ 6 : CorePoly).IsHomogeneous 6 := (hX 1).pow 6
  have t7 : (X 2 ^ 6 : CorePoly).IsHomogeneous 6 := (hX 2).pow 6
  have t8 : (C (5 / 7 : ℂ) * X 2 ^ 5 * X 3 : CorePoly).IsHomogeneous 6 :=
    ((hC _).mul ((hX 2).pow 5)).mul (hX 3)
  have t9 : (C (15 / 7 : ℂ) * X 2 * X 3 ^ 5 : CorePoly).IsHomogeneous 6 :=
    ((hC _).mul (hX 2)).mul ((hX 3).pow 5)
  have t10 : (X 3 ^ 6 : CorePoly).IsHomogeneous 6 := (hX 3).pow 6
  unfold core
  exact ((((((((t1.add t2).add t3).add t4).add t5).add t6).add t7).add t8).add t9).add t10

private def defect (D : CorePoly) (N : Fin 4 → CorePoly) : CorePoly :=
  2 • (coreSource * D^2) - 2 • (D * polynomialDirectional core N) +
    3 • (core * polynomialDivNum D N)

private lemma defect_scale (D S : CorePoly) (N : Fin 4 → CorePoly) :
    defect (S*D) (fun i => S*N i) = S^2 * defect D N := by
  simp only [defect, polynomialDivNum, polynomialDirectional_scale,
    polynomialDivergence_scale, polynomialDirectional_mul, nsmul_eq_mul]
  ring

private lemma defect_change (T U : CorePoly) (M : Fin 4 → CorePoly) :
    defect (T-U) M = defect T M +
      (2 • (coreSource * U * (U-2*T)) + 2 • (U * polynomialDirectional core M) +
        3 • (core * (polynomialDirectional U M - U*polynomialDivergence M))) := by
  have hd : polynomialDirectional (T-U) M = polynomialDirectional T M - polynomialDirectional U M := by
    simp only [polynomialDirectional, map_sub, mul_sub, Finset.sum_sub_distrib]
  simp only [defect, polynomialDivNum, hd, nsmul_eq_mul]
  ring

private lemma scaled_order {n : ℕ} {Q : CorePoly} (h : HasOrder n Q) (c : ℕ) :
    HasOrder n (c • Q) := by
  rw [nsmul_eq_mul]
  simpa using (hasOrder_zero_degree (c : CorePoly)).mul h

private lemma directional_order {n w : ℕ} {P : CorePoly} {M : Fin 4 → CorePoly}
    (hP : HasOrder n P) (hM : ∀ i, HasOrder w (M i)) :
    HasOrder (w+(n-1)) (polynomialDirectional P M) :=
  HasOrder.sum _ _ fun i _ => (hM i).mul (hP.pderiv i)

private lemma inverse_order (D : CorePoly) (d p : ℕ) (hD : HasOrder d D) :
    HasOrder ((p-1)*d) (finiteInverse D (homogeneousComponent d D) p) := by
  let h := homogeneousComponent d D
  have hh : HasOrder d h := isHomogeneous_hasOrder (homogeneousComponent_isHomogeneous d D)
  have hR : HasOrder d (h-D) := hh.sub hD
  apply HasOrder.sum
  intro i hi
  have hip := Finset.mem_range.mp hi
  have hsum : i + (p-1-i) = p-1 := by omega
  simpa only [h, ← Nat.add_mul, hsum] using (hh.pow i).mul (hR.pow (p-1-i))

private lemma least_component (D : CorePoly) (hne : D ≠ 0) :
    ∃ d, HasOrder d D ∧ homogeneousComponent d D ≠ 0 := by
  classical
  have hex : ∃ n, homogeneousComponent n D ≠ 0 := by
    by_contra! hall
    apply hne
    rw [← sum_homogeneousComponent D]
    exact Finset.sum_eq_zero (fun k _ => hall k)
  exact ⟨Nat.find hex, hasOrder_of_components_zero (fun k hk => not_ne_iff.mp (Nat.find_min hex hk)), Nat.find_spec hex⟩

private lemma source_hom : coreSource.IsHomogeneous 6 :=
  ((isHomogeneous_X ℂ (0 : Fin 4)).pow 3).mul ((isHomogeneous_X ℂ (2 : Fin 4)).pow 3)

private lemma defect_component (T : CorePoly) (M : Fin 4 → CorePoly) (e : ℕ)
    (he : 0 < e) (hT : T.IsHomogeneous e) :
    homogeneousComponent (2*e+6) (defect T M) =
      defect T (fun i => homogeneousComponent (e+1) (M i)) := by
  have hA : (coreSource*T^2).IsHomogeneous (2*e+6) := by
    convert source_hom.mul (hT.pow 2) using 1
    omega
  have hdir : homogeneousComponent (2*e+6) (T * polynomialDirectional core M) =
      T * polynomialDirectional core (fun i => homogeneousComponent (e+1) (M i)) := by
    rw [show 2*e+6=e+(5+(e+1)) by omega, component_mul_homogeneous hT,
      component_polynomialDirectional (show core.IsHomogeneous (5+1) from core_hom)]
  have hdiv : homogeneousComponent (2*e+6) (core * polynomialDivNum T M) =
      core * polynomialDivNum T (fun i => homogeneousComponent (e+1) (M i)) := by
    rw [show 2*e+6=6+2*e by omega, component_mul_homogeneous core_hom,
      component_polynomialDivNum he hT]
  simp only [defect, map_add, map_sub, map_nsmul, homogeneousComponent_eq_self hA, hdir, hdiv]

/-- Project the rescaled polynomial identity after its error has moved above
homogeneous degree `2*(p*d)+6`, where `p=d+2`. -/
private theorem project_initial (D : CorePoly) (N : Fin 4 → CorePoly) (d : ℕ)
    (hd : 0 < d) (hD : HasOrder d D) (h0 : homogeneousComponent d D ≠ 0)
    (hc : defect D N = 0) : ∃ T M, CoreCertificate T M := by
  let h := homogeneousComponent d D
  let p := d+2
  let e := p*d
  let u := p*(d+1)
  let w := (p-1)*d
  let T := h^p
  let U := (h-D)^p
  let S := finiteInverse D h p
  let M : Fin 4 → CorePoly := fun i => S*N i
  have hp : 0 < p := by dsimp [p]; omega
  have he : 0 < e := Nat.mul_pos hp hd
  have hu : u = e + (d+2) := by simp only [u, e, p, Nat.mul_add, Nat.mul_one]
  have hw : w+d=e := by
    dsimp only [w, e, p]
    rw [show d+2-1 = d+1 by omega, ← Nat.succ_mul]
  have hh := homogeneousComponent_isHomogeneous d D
  have hT : T.IsHomogeneous e := by simpa only [T, h, e, Nat.mul_comm] using hh.pow p
  have tOrd := isHomogeneous_hasOrder hT
  have uOrd : HasOrder u U := (order_sub_initial hD).pow p
  have mOrd (i : Fin 4) : HasOrder w (M i) := by
    simpa only [Nat.add_zero, M, S, h, w] using (inverse_order D d p hD).mul (hasOrder_zero_degree (N i))
  have divOrd : HasOrder (w-1) (polynomialDivergence M) :=
    HasOrder.sum _ _ (fun i _ => (mOrd i).pderiv i)
  have hErr1 : HasOrder (2*e+7) (coreSource*U*(U-2*T)) := by
    have hUT : HasOrder e (U-2*T) := by
      apply HasOrder.sub (uOrd.mono (by omega))
      simpa only [two_nsmul, two_mul] using tOrd.add tOrd
    apply ((isHomogeneous_hasOrder source_hom).mul uOrd |>.mul hUT).mono
    omega
  have hErr2 : HasOrder (2*e+7) (U*polynomialDirectional core M) := by
    apply (uOrd.mul (directional_order (isHomogeneous_hasOrder core_hom) mOrd)).mono
    omega
  have hErr3 : HasOrder (2*e+1) (polynomialDirectional U M) := by
    apply (directional_order uOrd mOrd).mono
    omega
  have hErr4 : HasOrder (2*e+1) (U*polynomialDivergence M) := by
    apply (uOrd.mul divOrd).mono
    omega
  have hErr5 : HasOrder (2*e+7) (core*(polynomialDirectional U M-U*polynomialDivergence M)) :=
    ((isHomogeneous_hasOrder core_hom).mul (hErr3.sub hErr4)).mono (by omega)
  have hz := (((scaled_order hErr1 2).add (scaled_order hErr2 2)).add (scaled_order hErr5 3)).component_eq_zero
    (k := 2*e+6) (by omega)
  have hscaled : defect (T-U) M = 0 := by
    have hds : D*S = T-U := finiteInverse_identity D h p
    rw [← hds, mul_comm D S, show M = (fun i => S*N i) from rfl, defect_scale, hc, mul_zero]
  rw [defect_change] at hscaled
  have hproj := congrArg (homogeneousComponent (2*e+6)) hscaled
  rw [map_add, hz, add_zero, map_zero, defect_component T M e he hT] at hproj
  refine ⟨T, (fun i => homogeneousComponent (e+1) (M i)), pow_ne_zero p h0, ⟨e-1, ?_, ?_⟩, ?_⟩
  · simpa only [show e-1+1=e by omega] using hT
  · intro i
    simpa only [show e-1+2=e+1 by omega] using homogeneousComponent_isHomogeneous (e+1) (M i)
  · simpa only [defect, nsmul_eq_mul, Nat.cast_ofNat, polynomialDivNum, polynomialDirectional,
      polynomialDivergence, mul_comm, mul_left_comm, mul_assoc] using hproj

end HodgeComputer.FourPlusTwoResidual.FourPlusTwoFiniteExtraction

open HodgeComputer.FourPlusTwoResidual
open HodgeComputer.FourPlusTwoResidual.FourPlusTwoFiniteExtraction

/-- A denominator of any degree and four ungraded polynomial numerators
suffice. Multiplication by `X 0` first permits a nonzero constant term in D. -/
theorem solution
    (D : MvPolynomial (Fin 4) ℂ) (N : Fin 4 → MvPolynomial (Fin 4) ℂ) (hD : D ≠ 0)
    (hraw : 2 * HodgeComputer.FourPlusTwoResidual.coreSource * D ^ 2 - 2 * D * (∑ i, MvPolynomial.pderiv i HodgeComputer.FourPlusTwoResidual.core * N i)
      + 3 * HodgeComputer.FourPlusTwoResidual.core * (D * (∑ i, MvPolynomial.pderiv i (N i)) - ∑ i, MvPolynomial.pderiv i D * N i) = 0) :
    ∃ (T : MvPolynomial (Fin 4) ℂ) (M : Fin 4 → MvPolynomial (Fin 4) ℂ),
      HodgeComputer.FourPlusTwoResidual.CoreCertificate T M := by
  have hc : defect D N = 0 := by
    simpa only [defect, nsmul_eq_mul, Nat.cast_ofNat, polynomialDivNum, polynomialDirectional,
      polynomialDivergence, mul_comm, mul_left_comm, mul_assoc] using hraw
  let x : MvPolynomial (Fin 4) ℂ := X 0
  obtain ⟨d, ho, hn⟩ := least_component (x*D) (mul_ne_zero (X_ne_zero 0) hD)
  have hOrd1 : HasOrder 1 (x*D) := by
    simpa only [Nat.add_zero] using (isHomogeneous_hasOrder (isHomogeneous_X ℂ (0 : Fin 4))).mul (hasOrder_zero_degree D)
  have hd : 0 < d := by
    by_contra! hv
    exact hn (hOrd1.component_eq_zero (by omega))
  exact project_initial (x*D) (fun i => x*N i) d hd ho hn (by rw [defect_scale, hc, mul_zero])
