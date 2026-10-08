-- Prove2me | solution 1 for OAI.TwoPointCorrelations.halasz_residue_good_moment
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T01:35:31.641708+00:00
-- url     : https://prove2.me/submissions/84beaede-56af-4ede-981a-2018032bebd1

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

section
-- module Solutions.OAIChowla.Compat
/-!
Backports of a few Mathlib lemmas from Mathlib d13f23b (the openai/math pin) to
Mathlib 0df444a, with the same names and statements and Mathlib's own proofs.
-/

open _root_.Polynomial


lemma Multiset.esymm_of_card_lt {R : Type*} [CommSemiring R] {s : Multiset R} {n : ℕ}
    (h : s.card < n) : s.esymm n = 0 := by
  simp [Multiset.esymm, Multiset.powersetCard_eq_empty _ h]


namespace Finset



end Finset

section LogSubst
open _root_.Real _root_.Set _root_.MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]





end LogSubst

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszVinogradovDiagonal
namespace OAI

/-! The diagonal algebra for the complete Vinogradov system: its first
s power sums determine all elementary symmetric functions of s entries.
This is the finite algebraic starting point for the mean-value argument
underlying Ford's logarithmic exponential-sum estimate. -/
namespace TwoPointCorrelations

open _root_.Finset _root_.MvPolynomial




@[simp] lemma mem_halaszVinogradovFiber {s N k : ℕ} {x y : Fin s → Fin N} :
    y ∈ halaszVinogradovFiber x k ↔ ∀ j ∈ Icc 1 k,
      (∑ i, ((x i).val+1)^j) = ∑ i, ((y i).val+1)^j := by
  classical
  simp [halaszVinogradovFiber]







end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszPrimePowerRoots
namespace OAI

/-! A split polynomial with distinct roots modulo p has no additional
roots modulo a power of p. This is the uniqueness part needed in the
nonsingular congruence count. -/
namespace TwoPointCorrelations

open _root_.Finset


lemma halasz_prime_power_unit_iff {p r : ℕ} [Fact p.Prime] (z : ZMod (p^(r+1))) :
    IsUnit z ↔ halaszPrimePowerReduction p r z≠0 := by
  have hp : p.Prime := Fact.out
  have : NeZero (p^(r+1)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hz : (z.val : ZMod (p^(r+1))) = z := ZMod.natCast_zmod_val z
  calc
    IsUnit z ↔ IsUnit (z.val : ZMod (p^(r+1))) := by rw [hz]
    _ ↔ ¬p∣z.val := ZMod.isUnit_natCast_iff_not_dvd_pow hp (by omega)
    _ ↔ halaszPrimePowerReduction p r z≠0 := by
      have he : halaszPrimePowerReduction p r z = (z.val:ZMod p) := by
        calc
          _ = halaszPrimePowerReduction p r (z.val:ZMod (p^(r+1))) := congrArg _ hz.symm
          _ = _ := map_natCast _ _
      rw [he]
      exact (ZMod.natCast_eq_zero_iff _ _).not.symm

theorem halasz_prime_power_split_roots {p r k : ℕ} [Fact p.Prime]
    (x : Fin k → ZMod (p^(r+1)))
    (hx : Function.Injective (fun i => halaszPrimePowerReduction p r (x i)))
    (z : ZMod (p^(r+1))) (hz : ∏ i, (z-x i)=0) : ∃ i, z=x i := by
  classical
  let φ := halaszPrimePowerReduction p r
  have hred : ∏ i, (φ z-φ (x i))=0 := by
    simpa only [map_prod,map_sub,map_zero] using congrArg φ hz
  obtain ⟨i,_,hi⟩ := prod_eq_zero_iff.mp hred
  have hi' : φ z=φ (x i) := sub_eq_zero.mp hi
  have hu : IsUnit (∏ j ∈ (univ:Finset (Fin k)).erase i, (z-x j)) := by
    apply IsUnit.prod_iff.mpr
    intro j hj
    apply (halasz_prime_power_unit_iff _).mpr
    change φ (z-x j)≠0
    rw [map_sub,hi',sub_ne_zero]
    intro he
    exact (mem_erase.mp hj).1 (hx he).symm
  have hfactor : (z-x i)*(∏ j ∈ (univ:Finset (Fin k)).erase i, (z-x j))=0 := by
    rw [mul_prod_erase univ (fun j => z-x j) (mem_univ i)]
    exact hz
  exact ⟨i,sub_eq_zero.mp (hu.mul_left_eq_zero.mp hfactor)⟩

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszPrimePowerSums
namespace OAI

/-! Newton identities over the prime-power ring. The small integers in
the identities are units when the prime exceeds the number of variables. -/
namespace TwoPointCorrelations

open _root_.Finset _root_.MvPolynomial

lemma halasz_unit_power_sums_esymm {R : Type*} [CommRing R] {s : ℕ}
    (x y : Fin s → R)
    (hu : ∀ j : ℕ, 1≤ j → j≤ s → IsUnit (j:R))
    (hp : ∀ j : ℕ, 1≤ j → j≤ s → ∑ i, x i^j=∑ i, y i^j) :
    ∀ k : ℕ, k≤ s → eval x (esymm (Fin s) R k)=eval y (esymm (Fin s) R k) := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro hks
    by_cases hk : k=0
    · subst k
      simp
    have he (a : ℕ × ℕ) (ha : a∈(antidiagonal k).filter (fun a => a.1< k)) :
        eval x ((-1: MvPolynomial (Fin s) R)^a.1 * esymm (Fin s) R a.1 * psum (Fin s) R a.2) =
          eval y ((-1: MvPolynomial (Fin s) R)^a.1 * esymm (Fin s) R a.1 * psum (Fin s) R a.2) := by
      obtain ⟨ha,hak⟩ := mem_filter.mp ha
      have hab : a.1+a.2=k := mem_antidiagonal.mp ha
      have hj := hp a.2 (by omega) (by omega)
      have hi := ih a.1 hak (by omega)
      simp only [map_mul,map_pow,map_neg,map_one]
      rw [hi]
      have hs : eval x (psum (Fin s) R a.2)=eval y (psum (Fin s) R a.2) := by
        simpa [psum] using hj
      rw [hs]
    have hsum := sum_congr rfl he
    have hx := congrArg (eval x) (mul_esymm_eq_sum (Fin s) R k)
    have hy := congrArg (eval y) (mul_esymm_eq_sum (Fin s) R k)
    simp only [map_mul,map_natCast,map_pow,map_neg,map_one,map_sum] at hx hy
    apply (hu k (by omega) hks).mul_right_inj.mp
    rw [hx,hy]
    simpa only [map_mul,map_pow,map_neg,map_one] using
      congrArg (fun z : R => (-1:R)^(k+1)*z) hsum

theorem halasz_unit_power_sums_product {R : Type*} [CommRing R] {s : ℕ}
    (x y : Fin s → R)
    (hu : ∀ j : ℕ, 1≤ j → j≤ s → IsUnit (j:R))
    (hp : ∀ j : ℕ, 1≤ j → j≤ s → ∑ i, x i^j=∑ i, y i^j) :
    (∏ i, (Polynomial.X-Polynomial.C (x i))) =
      ∏ i, (Polynomial.X-Polynomial.C (y i)) := by
  classical
  let a : Multiset R := univ.val.map x
  let b : Multiset R := univ.val.map y
  have ha : a.card=s := by simp [a]
  have hb : b.card=s := by simp [b]
  have he : ∀ k : ℕ, a.esymm k=b.esymm k := by
    intro k
    by_cases hk : k≤ s
    · have hx := aeval_esymm_eq_multiset_esymm (Fin s) R k x
      have hy := aeval_esymm_eq_multiset_esymm (Fin s) R k y
      rw [aeval_eq_eval] at hx hy
      exact hx.symm.trans ((halasz_unit_power_sums_esymm x y hu hp k hk).trans hy)
    · rw [Multiset.esymm_of_card_lt (by omega : a.card< k),
        Multiset.esymm_of_card_lt (by omega : b.card< k)]
  have hprod : (a.map (fun t => Polynomial.X-Polynomial.C t)).prod =
      (b.map (fun t => Polynomial.X-Polynomial.C t)).prod := by
    rw [Multiset.prod_X_sub_X_eq_sum_esymm,Multiset.prod_X_sub_X_eq_sum_esymm,ha,hb]
    apply sum_congr rfl
    intro k _
    rw [he k]
  simpa only [a,b,Multiset.map_map,Function.comp_def,Finset.prod_eq_multiset_prod] using hprod

theorem halasz_prime_power_power_sums_product {p r k : ℕ} [Fact p.Prime]
    (hkp : k< p) (x y : Fin k → ZMod (p^(r+1)))
    (hp : ∀ j : ℕ, 1≤ j → j≤ k → ∑ i, x i^j=∑ i, y i^j) :
    (∏ i, (Polynomial.X-Polynomial.C (x i))) =
      ∏ i, (Polynomial.X-Polynomial.C (y i)) := by
  apply halasz_unit_power_sums_product x y _ hp
  intro j hj hjk
  apply (ZMod.isUnit_natCast_iff_not_dvd_pow (Fact.out : p.Prime) (by omega)).mpr
  exact Nat.not_dvd_of_pos_of_lt hj (hjk.trans_lt hkp)

theorem halasz_prime_power_solution_mem {p r k : ℕ} [Fact p.Prime]
    (hkp : k< p) (x y : Fin k → ZMod (p^(r+1)))
    (hx : Function.Injective (fun i => halaszPrimePowerReduction p r (x i)))
    (hp : ∀ j : ℕ, 1≤ j → j≤ k → ∑ i, x i^j=∑ i, y i^j) (i : Fin k) :
    ∃ j, y i=x j := by
  have hpoly := halasz_prime_power_power_sums_product hkp x y hp
  have he := congrArg (Polynomial.eval (y i)) hpoly
  simp only [Polynomial.eval_prod,Polynomial.eval_sub,Polynomial.eval_X,Polynomial.eval_C] at he
  have hy : ∏ j, (y i-y j)=0 := prod_eq_zero (mem_univ i) (sub_self _)
  exact halasz_prime_power_split_roots x hx (y i) (he.trans hy)

/-- A sufficient nonsingular congruence bound for the mean-value iteration.
The factor k^k is deliberately used in place of the sharper k!. -/
theorem halasz_prime_power_solution_count {p r k : ℕ} [Fact p.Prime]
    (hkp : k< p) (x : Fin k → ZMod (p^(r+1)))
    (hx : Function.Injective (fun i => halaszPrimePowerReduction p r (x i)))
    (F : Finset (Fin k → ZMod (p^(r+1))))
    (hF : ∀ y∈F, ∀ j : ℕ, 1≤ j → j≤ k → ∑ i, x i^j=∑ i, y i^j) :
    F.card ≤ k^k := by
  classical
  let S : Finset (ZMod (p^(r+1))) := univ.image x
  have hs : S.card≤ k := (card_image_le).trans_eq (card_fin k)
  have hsub : F ⊆ Fintype.piFinset (fun _ : Fin k => S) := by
    intro y hy
    apply Fintype.mem_piFinset.mpr
    intro i
    obtain ⟨j,hj⟩ := halasz_prime_power_solution_mem hkp x y hx (hF y hy) i
    exact mem_image.mpr ⟨j,mem_univ _,hj.symm⟩
  calc
    F.card ≤ (Fintype.piFinset (fun _ : Fin k => S)).card := card_le_card hsub
    _ = S.card^k := by simp
    _ ≤ k^k := Nat.pow_le_pow_left hs k

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszPrimePowerCongruences
namespace OAI

/-! Triangular systems of univariate polynomials reduce to power sums.
The leading coefficients need only be units, so the result applies to
the translated and differenced systems over prime-power residue rings. -/
namespace TwoPointCorrelations

open _root_.Finset _root_.Polynomial

theorem halasz_power_sums_of_polynomial_sums {R : Type*} [CommRing R] {k : ℕ}
    (P : Fin k → R[X]) (x y : Fin k → R)
    (hdeg : ∀ i, (P i).natDegree ≤ i.val+1)
    (hunit : ∀ i, IsUnit ((P i).coeff (i.val+1)))
    (hsum : ∀ i, ∑ j, (P i).eval (x j)=∑ j, (P i).eval (y j)) :
    ∀ j : ℕ, 1≤ j → j≤ k → ∑ i, x i^j=∑ i, y i^j := by
  intro j
  induction j using Nat.strong_induction_on with
  | h j ih =>
    intro hj hjk
    let l : Fin k := ⟨j-1,by omega⟩
    let Q := P l
    have hd : Q.natDegree < j+1 := by
      exact Nat.lt_succ_of_le (by
        simpa only [Q,l,Nat.sub_add_cancel hj] using hdeg l)
    have heval (z : Fin k → R) :
        (∑ i, Q.eval (z i)) = ∑ m ∈ range (j+1), Q.coeff m*(∑ i, z i^m) := by
      simp_rw [Polynomial.eval_eq_sum_range' hd]
      rw [sum_comm]
      simp_rw [← mul_sum]
    have hs := hsum l
    change (∑ i, Q.eval (x i)) = ∑ i, Q.eval (y i) at hs
    rw [heval,heval,sum_range_succ,sum_range_succ] at hs
    have hsmall : (∑ m ∈ range j, Q.coeff m*(∑ i, x i^m)) =
        ∑ m ∈ range j, Q.coeff m*(∑ i, y i^m) := by
      apply sum_congr rfl
      intro m hm
      have hmj := mem_range.mp hm
      by_cases hm0 : m=0
      · simp [hm0]
      · rw [ih m hmj (by omega) (by omega)]
    rw [hsmall] at hs
    have hu : IsUnit (Q.coeff j) := by
      simpa only [Q,l,Nat.sub_add_cancel hj] using hunit l
    exact hu.mul_right_inj.mp (add_left_cancel hs)

theorem halasz_prime_power_polynomial_count {p r k : ℕ} [Fact p.Prime]
    (hkp : k< p) (P : Fin k → (ZMod (p^(r+1)))[X])
    (hdeg : ∀ i, (P i).natDegree ≤ i.val+1)
    (hunit : ∀ i, IsUnit ((P i).coeff (i.val+1)))
    (x : Fin k → ZMod (p^(r+1)))
    (hx : Function.Injective (fun i => halaszPrimePowerReduction p r (x i)))
    (F : Finset (Fin k → ZMod (p^(r+1))))
    (hF : ∀ y∈F, ∀ i, ∑ j, (P i).eval (x j)=∑ j, (P i).eval (y j)) :
    F.card ≤ k^k := by
  apply halasz_prime_power_solution_count hkp x hx F
  intro y hy
  exact halasz_power_sums_of_polynomial_sums P x y hdeg hunit (hF y hy)

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszResidueFibers
namespace OAI

/-! Counting lifts of a residue class inside a prime-power interval. -/
namespace TwoPointCorrelations

open _root_.Finset

lemma halasz_residue_fiber_card {n m a : ℕ} (hn : 0< n) (F : Finset ℕ)
    (hbound : ∀ x∈F, x< n*m) (hmod : ∀ x∈F, x%n=a) : F.card≤ m := by
  classical
  have hinj : Set.InjOn (fun x : ℕ => x/n) (F:Set ℕ) := by
    intro x hx y hy he
    change x/n=y/n at he
    calc
      x = x%n+n*(x/n) := (Nat.mod_add_div x n).symm
      _ = y%n+n*(y/n) := by rw [hmod x hx,hmod y hy,he]
      _ = y := Nat.mod_add_div y n
  have hsub : F.image (fun x => x/n) ⊆ range m := by
    intro y hy
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hy
    exact mem_range.mpr ((Nat.div_lt_iff_lt_mul hn).mpr
      (by simpa only [Nat.mul_comm] using hbound x hx))
  calc
    F.card = (F.image (fun x => x/n)).card := (card_image_of_injOn hinj).symm
    _ ≤ (range m).card := card_le_card hsub
    _ = m := card_range m

lemma halasz_prime_power_residue_card {p r j a : ℕ} [Fact p.Prime] (hj : j≤ r+1)
    (F : Finset (ZMod (p^(r+1))))
    (hmod : ∀ z∈F, z.val%(p^j)=a) : F.card≤ p^(r+1-j) := by
  classical
  have hp : p.Prime := Fact.out
  have : NeZero (p^(r+1)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hsize : p^j*p^(r+1-j)=p^(r+1) := by rw [← pow_add,Nat.add_sub_of_le hj]
  have hb : ∀ z∈F.image ZMod.val, z< p^j*p^(r+1-j) := by
    intro z hz
    obtain ⟨w,_,rfl⟩ := mem_image.mp hz
    rw [hsize]
    exact ZMod.val_lt w
  have hm : ∀ z∈F.image ZMod.val, z%(p^j)=a := by
    intro z hz
    obtain ⟨w,hw,rfl⟩ := mem_image.mp hz
    exact hmod w hw
  calc
    F.card = (F.image ZMod.val).card :=
      (card_image_of_injective F (ZMod.val_injective (p^(r+1)))).symm
    _ ≤ p^(r+1-j) := halasz_residue_fiber_card (pow_pos hp.pos _) _ hb hm

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszMixedCongruenceCount
namespace OAI

/-! The congruence-counting factor in the complete-system iteration.
The jth polynomial sum is fixed only modulo p^min(j,r), and the unused
digits are counted before applying the nonsingular full-modulus bound. -/
namespace TwoPointCorrelations

open _root_.Finset _root_.Polynomial

theorem halasz_mixed_congruence_count {p r k : ℕ} [Fact p.Prime]
    (hkp : k< p) (P : Fin k → (ZMod (p^(r+1)))[X])
    (hdeg : ∀ i, (P i).natDegree ≤ i.val+1)
    (hunit : ∀ i, IsUnit ((P i).coeff (i.val+1)))
    (F : Finset (Fin k → ZMod (p^(r+1)))) (b : Fin k → ℕ)
    (hnonsing : ∀ x∈F, Function.Injective
      (fun i => halaszPrimePowerReduction p r (x i)))
    (hmod : ∀ x∈F, ∀ j,
      (∑ i, (P j).eval (x i)).val % (p^(min (j.val+1) (r+1))) = b j) :
    F.card ≤ k^k * ∏ j : Fin k, p^(r+1-min (j.val+1) (r+1)) := by
  classical
  let T : (Fin k → ZMod (p^(r+1))) → (Fin k → ZMod (p^(r+1))) :=
    fun x j => ∑ i, (P j).eval (x i)
  let S := F.image T
  let R : Fin k → Finset (ZMod (p^(r+1))) := fun j => F.image (fun x => T x j)
  have hR (j : Fin k) : (R j).card ≤ p^(r+1-min (j.val+1) (r+1)) := by
    apply halasz_prime_power_residue_card (Nat.min_le_right _ _) (R j)
    intro z hz
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hz
    exact hmod x hx j
  have hS : S ⊆ Fintype.piFinset R := by
    intro t ht
    obtain ⟨x,hx,rfl⟩ := mem_image.mp ht
    apply Fintype.mem_piFinset.mpr
    intro j
    exact mem_image.mpr ⟨x,hx,rfl⟩
  have hcardS : S.card ≤ ∏ j : Fin k, p^(r+1-min (j.val+1) (r+1)) := by
    calc
      S.card ≤ (Fintype.piFinset R).card := card_le_card hS
      _ = ∏ j, (R j).card := Fintype.card_piFinset R
      _ ≤ _ := prod_le_prod' (fun j _ => hR j)
  have hfiber (t : Fin k → ZMod (p^(r+1))) :
      (F.filter (fun y => T y=t)).card ≤ k^k := by
    let B := F.filter (fun y => T y=t)
    change B.card ≤ k^k
    by_cases hB : B.Nonempty
    · obtain ⟨w,hw⟩ := hB
      apply halasz_prime_power_polynomial_count hkp P hdeg hunit w
        (hnonsing w (mem_filter.mp hw).1) B
      intro y hy j
      have he : T w=T y := (mem_filter.mp hw).2.trans (mem_filter.mp hy).2.symm
      exact congrFun he j
    · simp only [not_nonempty_iff_eq_empty.mp hB,card_empty]
      exact Nat.zero_le _
  calc
    F.card = ∑ t∈S, (F.filter (fun y => T y=t)).card := card_eq_sum_card_image T F
    _ ≤ ∑ _t∈S, k^k := sum_le_sum (fun t _ => hfiber t)
    _ = S.card*k^k := by simp
    _ ≤ (∏ j : Fin k, p^(r+1-min (j.val+1) (r+1)))*k^k :=
      Nat.mul_le_mul_right _ hcardS
    _ = _ := Nat.mul_comm _ _

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszCongruenceExponent
namespace OAI

/-! The free residue digits in the mixed congruence count total the
triangular exponent r(r-1)/2. -/
namespace TwoPointCorrelations

open _root_.Finset

lemma halasz_congruence_exponent_sum {r k : ℕ} (hrk : r≤ k) :
    (∑ j∈range k, (r-min (j+1) r)) = r*(r-1)/2 := by
  have hcut : (∑ j∈range r, (r-min (j+1) r)) =
      ∑ j∈range k, (r-min (j+1) r) := by
    apply sum_subset (range_mono hrk)
    intro j _ hj
    have hh : r≤ j := Nat.le_of_not_gt (fun h => hj (mem_range.mpr h))
    rw [Nat.min_eq_right (by omega),Nat.sub_self]
  rw [← hcut]
  calc
    _ = ∑ j∈range r, (r-1-j) := by
      apply sum_congr rfl
      intro j hj
      have hjr := mem_range.mp hj
      omega
    _ = ∑ j∈range r, j := sum_range_reflect (fun j => j) r
    _ = _ := sum_range_id r

theorem halasz_congruence_digit_product {p r k : ℕ} (hrk : r≤ k) :
    (∏ j : Fin k, p^(r-min (j.val+1) r)) = p^(r*(r-1)/2) := by
  rw [prod_pow_eq_pow_sum]
  congr 1
  simpa only [← Fin.sum_univ_eq_sum_range] using halasz_congruence_exponent_sum hrk

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszVinogradovOrthogonality
namespace OAI

/-! Fourier orthogonality for the complete Vinogradov system, with
normalised Haar measure on its coefficient torus. -/
namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.ComplexConjugate





lemma halasz_vinogradov_fourier_integral (n : ℤ) :
    (∫ x : AddCircle (1:ℝ), fourier n x ∂AddCircle.haarAddCircle) =
      if n=0 then (1:ℂ) else 0 := by
  by_cases hn : n=0
  · subst n
    simp
  · simp only [hn,ite_false]
    exact integral_eq_zero_of_add_right_eq_neg
      (fourier_add_half_inv_index hn (by norm_num))

theorem halasz_vinogradov_character_integral {k : ℕ} (m : Fin k → ℤ) :
    (∫ α, halaszVinogradovCharacter m α ∂halaszVinogradovHaar k) =
      if m=0 then (1:ℂ) else 0 := by
  unfold halaszVinogradovCharacter halaszVinogradovHaar
  rw [integral_fintype_prod_eq_prod]
  simp_rw [halasz_vinogradov_fourier_integral]
  by_cases hm : m=0
  · subst m
    simp
  · simp only [hm,ite_false]
    obtain ⟨j,hj⟩ : ∃ j, m j≠0 := by
      by_contra hn
      push Not at hn
      apply hm
      funext j
      exact hn j
    apply prod_eq_zero (mem_univ j)
    simp [hj]

lemma halasz_vinogradov_character_add {k : ℕ} (m n : Fin k → ℤ)
    (α : Fin k → AddCircle (1:ℝ)) :
    halaszVinogradovCharacter (m+n) α =
      halaszVinogradovCharacter m α*halaszVinogradovCharacter n α := by
  simp only [halaszVinogradovCharacter,Pi.add_apply,fourier_add,prod_mul_distrib]

lemma halasz_vinogradov_character_neg {k : ℕ} (m : Fin k → ℤ)
    (α : Fin k → AddCircle (1:ℝ)) :
    halaszVinogradovCharacter (-m) α = conj (halaszVinogradovCharacter m α) := by
  simp only [halaszVinogradovCharacter,Pi.neg_apply,fourier_neg,map_prod]


lemma halasz_vinogradov_character_integrable {k : ℕ} (m : Fin k → ℤ) :
    Integrable (halaszVinogradovCharacter m) (halaszVinogradovHaar k) := by
  exact (halasz_vinogradov_character_continuous m).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

lemma halasz_vinogradov_character_inner {k : ℕ} (m n : Fin k → ℤ) :
    (∫ α, halaszVinogradovCharacter m α*conj (halaszVinogradovCharacter n α)
      ∂halaszVinogradovHaar k) = if m=n then (1:ℂ) else 0 := by
  simp_rw [← halasz_vinogradov_character_neg,← halasz_vinogradov_character_add]
  rw [halasz_vinogradov_character_integral]
  simp only [← sub_eq_add_neg,sub_eq_zero]

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszVinogradovMoment
namespace OAI

/-! The complete Vinogradov solution count is exactly a torus moment of
the polynomial exponential sum. -/
namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.ComplexConjugate



lemma halasz_vinogradov_character_sum {s k : ℕ} (S : Finset (Fin s))
    (m : Fin s → Fin k → ℤ) (α : Fin k → AddCircle (1:ℝ)) :
    halaszVinogradovCharacter (∑ i ∈ S, m i) α =
      ∏ i ∈ S, halaszVinogradovCharacter (m i) α := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [halaszVinogradovCharacter]
  | @insert i S hi ih =>
    rw [sum_insert hi,prod_insert hi,halasz_vinogradov_character_add,ih]




end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszPowerTranslation
namespace OAI

/-! Translation of the complete system on a finite set of coordinates.
The natural-number version uses an integer translation for the reverse
implication, so no truncated subtraction is hidden in the statement. -/
namespace TwoPointCorrelations

open _root_.Finset

lemma halasz_finite_power_translate {ι R : Type*} [Fintype ι] [CommSemiring R]
    {k : ℕ} (x y : ι → R)
    (hpower : ∀ j : ℕ, 1≤ j → j≤ k → ∑ i, x i^j=∑ i, y i^j)
    (c : R) : ∀ j : ℕ, 1≤ j → j≤ k → ∑ i, (x i+c)^j=∑ i, (y i+c)^j := by
  intro j _ hjk
  have he (z : ι → R) : (∑ i, (z i+c)^j) =
      ∑ m∈range (j+1), (∑ i, z i^m)*c^(j-m)*(Nat.choose j m:R) := by
    simp only [add_pow]
    rw [sum_comm]
    apply sum_congr rfl
    intro m _
    rw [← sum_mul,← sum_mul]
  rw [he,he]
  apply sum_congr rfl
  intro m hm
  have hmj : m≤ j := by have := mem_range.mp hm; omega
  have hp : (∑ i, x i^m)=∑ i, y i^m := by
    by_cases hz : m=0
    · simp [hz]
    · exact hpower m (by omega) (hmj.trans hjk)
  rw [hp]

lemma halasz_nat_power_translate_iff {ι : Type*} [Fintype ι] {k : ℕ}
    (x y : ι → ℕ) (a : ℕ) :
    (∀ j : ℕ, 1≤ j → j≤ k → ∑ i, x i^j=∑ i, y i^j) ↔
      (∀ j : ℕ, 1≤ j → j≤ k → ∑ i, (x i+a)^j=∑ i, (y i+a)^j) := by
  constructor
  · exact fun h => halasz_finite_power_translate x y h a
  · intro h j hj hjk
    have hz : ∀ j : ℕ, 1≤ j → j≤ k →
        (∑ i, ((x i:ℤ)+a)^j)=∑ i, ((y i:ℤ)+a)^j := by
      intro j hj hjk
      exact_mod_cast h j hj hjk
    have ht := halasz_finite_power_translate _ _ hz (-(a:ℤ)) j hj hjk
    simp only [add_neg_cancel_right] at ht
    exact_mod_cast ht

lemma halasz_power_vector_eq_iff {ι : Type*} [Fintype ι] {k : ℕ}
    (x y : ι → ℕ) :
    (fun j : Fin k => ∑ i, x i^(j.val+1)) = (fun j : Fin k => ∑ i, y i^(j.val+1)) ↔
      ∀ j : ℕ, 1≤ j → j≤ k → ∑ i, x i^j=∑ i, y i^j := by
  constructor
  · intro h j hj hjk
    have he := congrFun h (⟨j-1,by omega⟩ : Fin k)
    simpa only [Nat.sub_add_cancel hj] using he
  · intro h
    funext j
    exact h (j.val+1) (by omega) (by omega)

lemma halasz_power_vector_translate_iff {ι : Type*} [Fintype ι] {k : ℕ}
    (x y : ι → ℕ) (a : ℕ) :
    (fun j : Fin k => ∑ i, x i^(j.val+1)) = (fun j : Fin k => ∑ i, y i^(j.val+1)) ↔
      (fun j : Fin k => ∑ i, (x i+a)^(j.val+1)) =
        (fun j : Fin k => ∑ i, (y i+a)^(j.val+1)) := by
  rw [halasz_power_vector_eq_iff,halasz_power_vector_eq_iff]
  exact halasz_nat_power_translate_iff x y a

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszFiberEnergy
namespace OAI

/-! Finite energy under refinement of a partition. This is the counting
form of the Cauchy--Schwarz step that introduces the congruences on the
long variables in the complete-system mean-value argument. -/
namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical


lemma halasz_fiber_energy_rows {α β : Type*} (F : Finset α) (f : α → β) :
    halaszFiberEnergy F f = ∑ x ∈ F, (F.filter (fun y => f y=f x)).card := by
  unfold halaszFiberEnergy
  calc
    _ = ∑ t ∈ F.image f, ∑ x ∈ F.filter (fun x => f x=t),
        (F.filter (fun y => f y=f x)).card := by
      apply sum_congr rfl
      intro t _
      rw [show (∑ x ∈ F.filter (fun x => f x=t),
          (F.filter (fun y => f y=f x)).card) =
          ∑ _x ∈ F.filter (fun x => f x=t), (F.filter (fun y => f y=t)).card from
        sum_congr rfl (fun x hx => by rw [(mem_filter.mp hx).2])]
      simp [pow_two]
    _ = _ := sum_fiberwise_of_maps_to (fun x hx => mem_image_of_mem f hx) _

lemma halasz_fiber_energy_partition {α β γ : Type*} (F : Finset α)
    (f : α → β) (g : α → γ) :
    halaszFiberEnergy F (fun x => (f x,g x)) =
      ∑ t ∈ F.image f, halaszFiberEnergy (F.filter (fun x => f x=t)) g := by
  rw [halasz_fiber_energy_rows]
  calc
    _ = ∑ t ∈ F.image f, ∑ x ∈ F.filter (fun x => f x=t),
        (F.filter (fun y => (f y,g y)=(f x,g x))).card := by
      convert (preTransparency := .instances) (sum_fiberwise_of_maps_to (s := F) (t := F.image f) (g := f)
        (fun x hx => mem_image_of_mem f hx)
        (fun x => (F.filter (fun y => (f y,g y)=(f x,g x))).card)).symm using 1
      apply sum_congr rfl
      intro x _
      congr 1
      ext y
      simp only [mem_filter]
    _ = _ := by
      apply sum_congr rfl
      intro t _
      rw [halasz_fiber_energy_rows]
      apply sum_congr rfl
      intro x hx
      have hxt := (mem_filter.mp hx).2
      congr 1
      ext y
      simp only [mem_filter,Prod.mk.injEq]
      rw [hxt]
      tauto

lemma halasz_card_sq_le_fiber_energy {α β : Type*} (F : Finset α) (f : α → β) :
    F.card^2 ≤ (F.image f).card * halaszFiberEnergy F f := by
  have h := sq_sum_le_card_mul_sum_sq (s := F.image f)
    (f := fun t => (F.filter (fun x => f x=t)).card)
  rw [← card_eq_sum_card_image f F] at h
  exact h

theorem halasz_fiber_energy_refine {α β γ : Type*} (F : Finset α)
    (f : α → β) (g : α → γ) (B : ℕ)
    (hB : ∀ t ∈ F.image f, ((F.filter (fun x => f x=t)).image g).card ≤ B) :
    halaszFiberEnergy F f ≤ B * halaszFiberEnergy F (fun x => (f x,g x)) := by
  rw [halasz_fiber_energy_partition,mul_sum]
  change (∑ t ∈ F.image f, (F.filter (fun x => f x=t)).card^2) ≤ _
  apply sum_le_sum
  intro t ht
  exact (halasz_card_sq_le_fiber_energy _ g).trans
    (Nat.mul_le_mul_right _ (hB t ht))

lemma halasz_fiber_energy_congr {α β γ : Type*} (F : Finset α)
    (f : α → β) (g : α → γ)
    (h : ∀ x∈F, ∀ y∈F, f y=f x ↔ g y=g x) :
    halaszFiberEnergy F f = halaszFiberEnergy F g := by
  rw [halasz_fiber_energy_rows,halasz_fiber_energy_rows]
  apply sum_congr rfl
  intro x hx
  congr 1
  ext y
  simpa only [mem_filter] using and_congr_right (fun hy => h x hx y hy)

lemma halasz_fiber_energy_mono {α β : Type*} {F G : Finset α} (hFG : F⊆G)
    (f : α → β) : halaszFiberEnergy F f ≤ halaszFiberEnergy G f := by
  rw [halasz_fiber_energy_rows,halasz_fiber_energy_rows]
  calc
    _ ≤ ∑ x∈F, (G.filter (fun y => f y=f x)).card := by
      apply sum_le_sum
      intro x _
      exact card_le_card (filter_subset_filter _ hFG)
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg hFG (fun _ _ _ => Nat.zero_le _)

lemma halasz_fiber_energy_product {α β γ : Type*} (F : Finset α) (G : Finset β)
    (g : β → γ) :
    halaszFiberEnergy (F×ˢG) (fun x => (x.1,g x.2)) = F.card * halaszFiberEnergy G g := by
  rw [halasz_fiber_energy_rows,halasz_fiber_energy_rows,sum_product]
  have hf (a : α) (ha : a∈F) (b : β) :
      ((F×ˢG).filter (fun y => (y.1,g y.2)=(a,g b))).card =
        (G.filter (fun y => g y=g b)).card := by
    have he : (F×ˢG).filter (fun y => (y.1,g y.2)=(a,g b)) =
        {a}×ˢ(G.filter (fun y => g y=g b)) := by
      ext y
      simp only [mem_filter,mem_product,mem_singleton,Prod.mk.injEq]
      constructor
      · rintro ⟨⟨_,hG⟩,he,hg⟩
        exact ⟨he,hG,hg⟩
      · rintro ⟨he,hG,hg⟩
        exact ⟨⟨he ▸ ha,hG⟩,he,hg⟩
    rw [he,card_product,card_singleton,one_mul]
  calc
    _ = ∑ _a∈F, ∑ b∈G, (G.filter (fun y => g y=g b)).card := by
      apply sum_congr rfl
      intro a ha
      apply sum_congr rfl
      intro b _
      simpa only [filter_congr_decidable] using hf a ha b
    _ = _ := by simp


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszCongruenceEnergy
namespace OAI

/-! The mixed congruence count inserted into the finite energy inequality.
The trace `f` may contain further variables, provided those variables
vanish modulo the indicated prime powers. -/
namespace TwoPointCorrelations

open _root_.Finset _root_.Polynomial
open scoped _root_.Classical

theorem halasz_mixed_congruence_energy {ι : Type*} {p r k : ℕ} [Fact p.Prime]
    (hkp : k< p) (P : Fin k → (ZMod (p^(r+1)))[X])
    (hdeg : ∀ j, (P j).natDegree≤ j.val+1)
    (hunit : ∀ j, IsUnit ((P j).coeff (j.val+1)))
    (F : Finset ι) (z : ι → Fin k → ZMod (p^(r+1)))
    (f : ι → Fin k → ℕ)
    (hnonsing : ∀ x∈F, Function.Injective
      (fun j => halaszPrimePowerReduction p r (z x j)))
    (hmod : ∀ x∈F, ∀ j,
      (∑ i, (P j).eval (z x i)).val % p^(min (j.val+1) (r+1)) =
        f x j % p^(min (j.val+1) (r+1))) :
    halaszFiberEnergy F f ≤
      (k^k * ∏ j : Fin k, p^(r+1-min (j.val+1) (r+1))) *
        halaszFiberEnergy F (fun x => (f x,z x)) := by
  apply halasz_fiber_energy_refine
  intro t _
  convert (preTransparency := .instances) halasz_mixed_congruence_count hkp P hdeg hunit
    ((F.filter (fun x => f x=t)).image z)
    (fun j => t j % p^(min (j.val+1) (r+1))) ?_ ?_ using 1
  · congr 1
    ext y
    simp
  · intro y hy
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hy
    exact hnonsing x (mem_filter.mp hx).1
  · intro y hy j
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hy
    rw [hmod x (mem_filter.mp hx).1 j,(mem_filter.mp hx).2]

theorem halasz_mixed_congruence_energy_triangular {ι : Type*} {p r k : ℕ}
    [Fact p.Prime] (hkp : k< p) (hrk : r+1≤ k)
    (P : Fin k → (ZMod (p^(r+1)))[X])
    (hdeg : ∀ j, (P j).natDegree≤ j.val+1)
    (hunit : ∀ j, IsUnit ((P j).coeff (j.val+1)))
    (F : Finset ι) (z : ι → Fin k → ZMod (p^(r+1)))
    (f : ι → Fin k → ℕ)
    (hnonsing : ∀ x∈F, Function.Injective
      (fun j => halaszPrimePowerReduction p r (z x j)))
    (hmod : ∀ x∈F, ∀ j,
      (∑ i, (P j).eval (z x i)).val % p^(min (j.val+1) (r+1)) =
        f x j % p^(min (j.val+1) (r+1))) :
    halaszFiberEnergy F f ≤
      (k^k * p^((r+1)*r/2)) * halaszFiberEnergy F (fun x => (f x,z x)) := by
  have h := halasz_mixed_congruence_energy hkp P hdeg hunit F z f hnonsing hmod
  rw [halasz_congruence_digit_product hrk] at h
  simpa only [Nat.add_sub_cancel] using h

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszEnergyImage
namespace OAI

/-! Reindexing finite energies by the residue-class quotient map. -/
namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma halasz_fiber_energy_image {α β γ : Type*} (F : Finset α)
    (g : α → β) (hg : Set.InjOn g F) (f : β → γ) :
    halaszFiberEnergy (F.image g) f = halaszFiberEnergy F (fun x => f (g x)) := by
  rw [halasz_fiber_energy_rows,halasz_fiber_energy_rows,sum_image hg]
  apply sum_congr rfl
  intro x _
  rw [filter_image]
  exact card_image_of_injOn (hg.mono (filter_subset _ _))

lemma halasz_fiber_energy_natCast {α : Type*} {k : ℕ} (F : Finset α)
    (f : α → Fin k → ℕ) :
    halaszFiberEnergy F (fun x j => (f x j : ℤ)) = halaszFiberEnergy F f := by
  apply halasz_fiber_energy_congr
  intro x _ y _
  constructor
  · intro h
    funext j
    exact_mod_cast congrFun h j
  · intro h
    exact congrArg (fun v j => (v j : ℤ)) h

lemma halasz_fiber_energy_transfer {α β γ : Type*} (F : Finset α)
    (g : α → β) (hg : Set.InjOn g F) (u : α → γ) (v : β → γ)
    (hv : ∀ x∈F, v (g x)=u x) :
    halaszFiberEnergy F u = halaszFiberEnergy (F.image g) v := by
  rw [halasz_fiber_energy_image F g hg v]
  apply halasz_fiber_energy_congr
  intro x hx y hy
  rw [hv x hx,hv y hy]

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszFinitePhase
namespace OAI

/-! Exact Fourier formulas for the finite energies used when the short
variables are restricted to one residue class. -/
namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.Classical _root_.ComplexConjugate


lemma halasz_finite_phase_continuous {ι : Type*} {k : ℕ}
    (F : Finset ι) (f : ι → Fin k → ℤ) : Continuous (halaszFinitePhase F f) := by
  exact continuous_finsetSum F (fun x _ => halasz_vinogradov_character_continuous (f x))

lemma halasz_torus_integrable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {k : ℕ} (f : (Fin k → AddCircle (1:ℝ)) → E) (hf : Continuous f) :
    Integrable f (halaszVinogradovHaar k) :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem halasz_finite_phase_energy {ι : Type*} {k : ℕ} (F : Finset ι)
    (f : ι → Fin k → ℤ) :
    (∫ α, ‖halaszFinitePhase F f α‖^2 ∂halaszVinogradovHaar k) =
      (halaszFiberEnergy F f : ℝ) := by
  have hi (x y : ι) : Integrable (fun α =>
      halaszVinogradovCharacter (f x) α * conj (halaszVinogradovCharacter (f y) α))
      (halaszVinogradovHaar k) := by
    simp_rw [← halasz_vinogradov_character_neg,← halasz_vinogradov_character_add]
    exact halasz_vinogradov_character_integrable _
  have hc : (∫ α, halaszFinitePhase F f α * conj (halaszFinitePhase F f α)
      ∂halaszVinogradovHaar k) = (halaszFiberEnergy F f : ℂ) := by
    unfold halaszFinitePhase
    simp_rw [map_sum,sum_mul,mul_sum]
    rw [integral_finsetSum F (fun x _ => integrable_finsetSum F (fun y _ => hi x y))]
    simp_rw [integral_finsetSum F (fun y _ => hi _ y),halasz_vinogradov_character_inner]
    rw [halasz_fiber_energy_rows,Nat.cast_sum]
    apply sum_congr rfl
    intro x _
    simp only [sum_boole]
    congr 2
    ext y
    simp only [mem_filter]
    exact and_congr_right (fun _ => eq_comm)
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  simpa only [Complex.mul_conj',Complex.ofReal_pow,Complex.ofReal_natCast] using hc

lemma halasz_finite_phase_product {ι κ : Type*} {k : ℕ} (F : Finset ι) (G : Finset κ)
    (f : ι → Fin k → ℤ) (g : κ → Fin k → ℤ) (α : Fin k → AddCircle (1:ℝ)) :
    halaszFinitePhase (F×ˢG) (fun x => f x.1+g x.2) α =
      halaszFinitePhase F f α * halaszFinitePhase G g α := by
  simp only [halaszFinitePhase,sum_product,halasz_vinogradov_character_add,sum_mul,mul_sum]
  rw [sum_comm]

lemma halasz_finite_phase_power {ι : Type*} {k : ℕ} (F : Finset ι)
    (f : ι → Fin k → ℤ) (s : ℕ) (α : Fin k → AddCircle (1:ℝ)) :
    halaszFinitePhase (Fintype.piFinset (fun _ : Fin s => F))
        (fun x => ∑ i, f (x i)) α = (halaszFinitePhase F f α)^s := by
  rw [halaszFinitePhase,halaszFinitePhase,sum_pow']
  apply sum_congr rfl
  intro x _
  exact halasz_vinogradov_character_sum univ (fun i => f (x i)) α

theorem halasz_finite_mixed_moment {ι κ : Type*} {k : ℕ}
    (F : Finset ι) (G : Finset κ) (f : ι → Fin k → ℤ) (g : κ → Fin k → ℤ) (s : ℕ) :
    (∫ α, ‖halaszFinitePhase F f α‖^2 * ‖halaszFinitePhase G g α‖^(2*s)
      ∂halaszVinogradovHaar k) =
      (halaszFiberEnergy (F×ˢFintype.piFinset (fun _ : Fin s => G))
        (fun x => f x.1+∑ i, g (x.2 i)) : ℝ) := by
  rw [← halasz_finite_phase_energy]
  apply integral_congr_ae
  filter_upwards [] with α
  rw [halasz_finite_phase_product F (Fintype.piFinset (fun _ : Fin s => G)) f
    (fun x => ∑ i, g (x i)),halasz_finite_phase_power,norm_mul,mul_pow,norm_pow]
  congr 1
  rw [← pow_mul,Nat.mul_comm s 2]

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszLongShortEnergy
namespace OAI

/-! Once the long variables agree modulo a prime power exceeding their
range, the remaining energy is the ordinary complete-system moment. -/
namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma halasz_nat_power_frequency_eq {s k N : ℕ} (x y : Fin s → Fin N) :
    halaszNatPowerFrequency k y = halaszNatPowerFrequency k x ↔
      y ∈ halaszVinogradovFiber x k := by
  rw [mem_halaszVinogradovFiber]
  constructor
  · intro h j hj
    have hj1 := (mem_Icc.mp hj).1
    have hjk := (mem_Icc.mp hj).2
    have he := congrFun h (⟨j-1,by omega⟩ : Fin k)
    simpa only [halaszNatPowerFrequency,Nat.sub_add_cancel hj1] using he.symm
  · intro h
    funext j
    exact (h (j.val+1) (mem_Icc.mpr ⟨by omega,by omega⟩)).symm

lemma halasz_nat_power_energy (s k N : ℕ) :
    halaszFiberEnergy (univ : Finset (Fin s → Fin N)) (halaszNatPowerFrequency k) =
      halaszVinogradovCount s k N := by
  rw [halasz_fiber_energy_rows,halaszVinogradovCount]
  apply sum_congr rfl
  intro x _
  congr 1
  ext y
  simp only [mem_filter,mem_univ,true_and,halasz_nat_power_frequency_eq]

lemma halasz_long_residues_injective {s k N Q p r : ℕ} (hN : N< p^(r+1))
    (x y : (Fin k → Fin N) × (Fin s → Fin Q))
    (h : halaszLongResidues p r x = halaszLongResidues p r y) : x.1=y.1 := by
  funext i
  apply Fin.ext
  have he := congrArg ZMod.val (congrFun h i)
  have hx : (x.1 i).val+1< p^(r+1) := lt_of_le_of_lt (by omega) hN
  have hy : (y.1 i).val+1< p^(r+1) := lt_of_le_of_lt (by omega) hN
  simp only [halaszLongResidues,ZMod.val_natCast_of_lt hx,
    ZMod.val_natCast_of_lt hy] at he
  omega



end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszResidueAveraging
namespace OAI

/-! Averaging the short-variable moment over residue classes. This is
the p^(2s) step in the fundamental complete-system estimate. -/
namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.Classical

lemma halasz_torus_power_sum_bound {ι : Type*} {k : ℕ} (S : Finset ι)
    (F : (Fin k → AddCircle (1:ℝ)) → ℂ)
    (G : ι → (Fin k → AddCircle (1:ℝ)) → ℂ)
    (hF : Continuous F) (hG : ∀ b∈S, Continuous (G b)) (n : ℕ) :
    (∫ α, ‖F α‖^2 * ‖∑ b∈S, G b α‖^(n+1) ∂halaszVinogradovHaar k) ≤
      (S.card:ℝ)^n * ∑ b∈S,
        ∫ α, ‖F α‖^2 * ‖G b α‖^(n+1) ∂halaszVinogradovHaar k := by
  have hi (b : ι) (hb : b∈S) : Integrable
      (fun α => ‖F α‖^2 * ‖G b α‖^(n+1)) (halaszVinogradovHaar k) :=
    halasz_torus_integrable _ ((hF.norm.pow 2).mul ((hG b hb).norm.pow _))
  have hpoint (α : Fin k → AddCircle (1:ℝ)) :
      ‖F α‖^2 * ‖∑ b∈S, G b α‖^(n+1) ≤
        (S.card:ℝ)^n * ∑ b∈S, ‖F α‖^2 * ‖G b α‖^(n+1) := by
    have hs := pow_sum_le_card_mul_sum_pow
      (s := S) (f := fun b => ‖G b α‖) (fun b _ => norm_nonneg (G b α)) n
    have hn := pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le S (fun b => G b α)) (n+1)
    calc
      _ ≤ ‖F α‖^2 * ((S.card:ℝ)^n * ∑ b∈S, ‖G b α‖^(n+1)) :=
        mul_le_mul_of_nonneg_left (hn.trans hs) (sq_nonneg _)
      _ = _ := by
        simp only [mul_sum]
        apply sum_congr rfl
        intro b _
        ring
  calc
    _ ≤ ∫ α, (S.card:ℝ)^n * ∑ b∈S, ‖F α‖^2 * ‖G b α‖^(n+1)
        ∂halaszVinogradovHaar k := by
      apply integral_mono
      · exact halasz_torus_integrable _ ((hF.norm.pow 2).mul
          ((continuous_finsetSum S hG).norm.pow _))
      · exact (integrable_finsetSum S hi).const_mul _
      · exact hpoint
    _ = _ := by rw [integral_const_mul,integral_finsetSum S hi]

theorem halasz_residue_average_energy {ι κ : Type*} {k p s : ℕ}
    (hs : 0< s) (F : Finset ι) (G : Finset κ) (c : κ → Fin p)
    (f : ι → Fin k → ℤ) (g : κ → Fin k → ℤ) (B : ℕ)
    (hB : ∀ b : Fin p,
      halaszFiberEnergy (F×ˢFintype.piFinset (fun _ : Fin s => G.filter (fun x => c x=b)))
        (fun x => f x.1+∑ i, g (x.2 i)) ≤ B) :
    halaszFiberEnergy (F×ˢFintype.piFinset (fun _ : Fin s => G))
      (fun x => f x.1+∑ i, g (x.2 i)) ≤ p^(2*s)*B := by
  have hsplit (α : Fin k → AddCircle (1:ℝ)) :
      halaszFinitePhase G g α =
        ∑ b : Fin p, halaszFinitePhase (G.filter (fun x => c x=b)) g α := by
    exact (sum_fiberwise_of_maps_to (s := G) (t := univ) (g := c)
      (fun _ _ => mem_univ _) (fun x => halaszVinogradovCharacter (g x) α)).symm
  have h := halasz_torus_power_sum_bound (univ : Finset (Fin p))
    (halaszFinitePhase F f)
    (fun b => halaszFinitePhase (G.filter (fun x => c x=b)) g)
    (halasz_finite_phase_continuous F f)
    (fun b _ => halasz_finite_phase_continuous _ g) (2*s-1)
  have hexp : 2*s-1+1=2*s := by omega
  simp_rw [hexp,← hsplit,halasz_finite_mixed_moment] at h
  have hb (b : Fin p) :
      (halaszFiberEnergy (F×ˢFintype.piFinset (fun _ : Fin s => G.filter (fun x => c x=b)))
        (fun x => f x.1+∑ i, g (x.2 i)) : ℝ) ≤ B := by
    exact_mod_cast hB b
  have hh := h.trans (mul_le_mul_of_nonneg_left
    (sum_le_sum (fun b _ => hb b)) (by positivity))
  simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul] at hh
  have hp : (p:ℝ)^(2*s-1)*((p:ℝ)*B)=(p:ℝ)^(2*s)*B := by
    rw [← mul_assoc,← pow_succ,hexp]
  rw [hp] at hh
  exact_mod_cast hh

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszShiftedLongShort
namespace OAI

/-! A common short-variable residue is represented as p*u-a with
0<=a< p. Translating the whole system by a leaves positive long variables
and short variables divisible by p. -/
namespace TwoPointCorrelations

open _root_.Finset _root_.Polynomial
open scoped _root_.Classical



lemma halasz_common_residue_translate {s k N Q p a : ℕ} (ha : a< p)
    (x y : (Fin k → Fin N) × (Fin s → Fin Q)) :
    halaszCommonResidueFrequency p a x = halaszCommonResidueFrequency p a y ↔
      halaszShiftedLongShortFrequency p a x = halaszShiftedLongShortFrequency p a y := by
  let v (z : (Fin k → Fin N) × (Fin s → Fin Q)) : (Fin k ⊕ Fin s) → ℕ :=
    Sum.elim (fun i => (z.1 i).val+1) (fun i => p*((z.2 i).val+1)-a)
  have hadd (z : (Fin k → Fin N) × (Fin s → Fin Q)) (i : Fin s) :
      p*((z.2 i).val+1)-a+a=p*((z.2 i).val+1) := by
    apply Nat.sub_add_cancel
    exact ha.le.trans (Nat.le_mul_of_pos_right p (by omega))
  have h := halasz_power_vector_translate_iff (k := k) (v x) (v y) a
  have hraw (z : (Fin k → Fin N) × (Fin s → Fin Q)) :
      (fun j : Fin k => ∑ i, v z i^(j.val+1)) = halaszCommonResidueFrequency p a z := by
    funext j
    simp only [v,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,
      halaszCommonResidueFrequency,halaszNatPowerFrequency]
  have hshift (z : (Fin k → Fin N) × (Fin s → Fin Q)) :
      (fun j : Fin k => ∑ i, (v z i+a)^(j.val+1)) =
        halaszShiftedLongShortFrequency p a z := by
    funext j
    simp only [v,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,hadd,mul_pow,
      ← mul_sum,halaszShiftedLongShortFrequency,halaszNatPowerFrequency]
  rw [hraw,hraw,hshift,hshift] at h
  exact h

lemma halasz_shifted_long_short_congruence {s k N Q : ℕ} (p a r : ℕ)
    (x : (Fin k → Fin N) × (Fin s → Fin Q)) (j : Fin k) :
    (∑ i, (((X+C (a : ZMod (p^(r+1))))^(j.val+1)).eval
      (halaszLongResidues p r x i))).val % p^(min (j.val+1) (r+1)) =
        halaszShiftedLongShortFrequency p a x j % p^(min (j.val+1) (r+1)) := by
  have hcast : (∑ i, (((X+C (a : ZMod (p^(r+1))))^(j.val+1)).eval
      (halaszLongResidues p r x i))) =
      ((∑ i, ((x.1 i).val+1+a)^(j.val+1) : ℕ) : ZMod (p^(r+1))) := by
    simp only [eval_pow,eval_add,eval_X,eval_C,halaszLongResidues,Nat.cast_sum,
      Nat.cast_pow,Nat.cast_add]
  rw [hcast,ZMod.val_natCast,Nat.mod_mod_of_dvd _
    (pow_dvd_pow p (Nat.min_le_right _ _))]
  have hd : p^(min (j.val+1) (r+1)) ∣
      p^(j.val+1)*halaszNatPowerFrequency k x.2 j :=
    dvd_mul_of_dvd_left (pow_dvd_pow p (Nat.min_le_left _ _)) _
  simp only [halaszShiftedLongShortFrequency,Nat.add_mod,Nat.mod_eq_zero_of_dvd hd,
    add_zero,Nat.mod_mod]

theorem halasz_shifted_long_short_congruence_energy {s k N Q p r : ℕ} [Fact p.Prime]
    (hkp : k< p) (hrk : r+1≤ k) (a : ℕ)
    (F : Finset ((Fin k → Fin N) × (Fin s → Fin Q)))
    (hF : ∀ x∈F, Function.Injective
      (fun i => (((x.1 i).val+1:ℕ) : ZMod p))) :
    halaszFiberEnergy F (halaszShiftedLongShortFrequency p a) ≤
      (k^k*p^((r+1)*r/2)) * halaszFiberEnergy F
        (fun x => (halaszShiftedLongShortFrequency p a x,halaszLongResidues p r x)) := by
  apply halasz_mixed_congruence_energy_triangular hkp hrk
    (fun j => (X+C (a : ZMod (p^(r+1))))^(j.val+1))
  · intro j
    have hb : (X+C (a : ZMod (p^(r+1)))).natDegree≤1 :=
      (natDegree_add_le _ _).trans (max_le natDegree_X_le (by simp))
    simpa only [Nat.mul_one] using natDegree_pow_le_of_le (j.val+1) hb
  · intro j
    simp only [coeff_X_add_C_pow,Nat.choose_self,Nat.sub_self,pow_zero,
      Nat.cast_one,mul_one,isUnit_one]
  · intro x hx
    simpa only [halaszLongResidues,map_natCast] using hF x hx
  · exact fun x _ j => halasz_shifted_long_short_congruence p a r x j

lemma halasz_shifted_long_short_refined_energy {s k N Q p r : ℕ}
    (hp : 0< p) (a : ℕ) (hN : N< p^(r+1))
    (F : Finset ((Fin k → Fin N) × (Fin s → Fin Q))) :
    halaszFiberEnergy F
      (fun x => (halaszShiftedLongShortFrequency p a x,halaszLongResidues p r x)) ≤
        N^k * halaszVinogradovCount s k Q := by
  have he : halaszFiberEnergy F
      (fun x => (halaszShiftedLongShortFrequency p a x,halaszLongResidues p r x)) =
      halaszFiberEnergy F (fun x => (x.1,halaszNatPowerFrequency k x.2)) := by
    apply halasz_fiber_energy_congr
    intro x _ y _
    simp only [Prod.mk.injEq]
    constructor
    · rintro ⟨hf,hz⟩
      have hxy := halasz_long_residues_injective hN y x hz
      refine ⟨hxy,?_⟩
      funext j
      have hj := congrFun hf j
      simp only [halaszShiftedLongShortFrequency,hxy] at hj
      exact Nat.eq_of_mul_eq_mul_left (pow_pos hp _) (Nat.add_left_cancel hj)
    · rintro ⟨hz,hf⟩
      constructor
      · funext j
        simp only [halaszShiftedLongShortFrequency,hz,hf]
      · funext i
        simp only [halaszLongResidues,hz]
  rw [he]
  calc
    _ ≤ halaszFiberEnergy
        ((univ : Finset (Fin k → Fin N)) ×ˢ (univ : Finset (Fin s → Fin Q)))
        (fun x => (x.1,halaszNatPowerFrequency k x.2)) :=
      halasz_fiber_energy_mono (fun _ _ => mem_product.mpr ⟨mem_univ _,mem_univ _⟩) _
    _ = _ := by
      rw [halasz_fiber_energy_product,halasz_nat_power_energy]
      simp

theorem halasz_common_residue_energy {s k N Q p r a : ℕ} [Fact p.Prime]
    (hkp : k< p) (hrk : r+1≤ k) (ha : a< p) (hN : N< p^(r+1))
    (F : Finset ((Fin k → Fin N) × (Fin s → Fin Q)))
    (hF : ∀ x∈F, Function.Injective
      (fun i => (((x.1 i).val+1:ℕ) : ZMod p))) :
    halaszFiberEnergy F (halaszCommonResidueFrequency p a) ≤
      (k^k*p^((r+1)*r/2)) * (N^k*halaszVinogradovCount s k Q) := by
  have he : halaszFiberEnergy F (halaszCommonResidueFrequency p a) =
      halaszFiberEnergy F (halaszShiftedLongShortFrequency p a) := by
    exact halasz_fiber_energy_congr F _ _ (fun x _ y _ =>
      halasz_common_residue_translate ha y x)
  rw [he]
  exact (halasz_shifted_long_short_congruence_energy hkp hrk a F hF).trans
    (Nat.mul_le_mul_left _ (halasz_shifted_long_short_refined_energy
      (Fact.out : p.Prime).pos a hN F))

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszResidueQuotient
namespace OAI

/-! Quotient coordinates in one positive residue class. Representatives
p*u-a, with 0<=a< p, avoid a boundary point at u=0. -/
namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical



lemma halasz_residue_quotient_recover {M p : ℕ} (hp : 0< p) (b : Fin p)
    (x : Fin M) (hx : halaszResidueIndex hp x=b) :
    p*((halaszResidueQuotient p x).val+1)-(p-1-b.val)=x.val+1 := by
  have hm : x.val%p=b.val := congrArg Fin.val hx
  have hd := Nat.mod_add_div x.val p
  dsimp [halaszResidueQuotient]
  rw [Nat.mul_add,Nat.mul_one]
  omega

lemma halasz_residue_quotient_injOn {M p : ℕ} (hp : 0< p) (b : Fin p) :
    Set.InjOn (halaszResidueQuotient (M := M) p)
      ((univ.filter (fun x : Fin M => halaszResidueIndex hp x=b)) : Set (Fin M)) := by
  intro x hx y hy hxy
  apply Fin.ext
  have hx' : x.val%p=b.val := congrArg Fin.val (mem_filter.mp hx).2
  have hy' : y.val%p=b.val := congrArg Fin.val (mem_filter.mp hy).2
  have hd : x.val/p=y.val/p := congrArg Fin.val hxy
  change x.val/p=y.val/p at hd
  have hdx := Nat.mod_add_div x.val p
  have hdy := Nat.mod_add_div y.val p
  rw [hd] at hdx
  omega


lemma halasz_residue_tuple_quotient_injOn {s k N M p : ℕ} (hp : 0< p)
    (Z : Finset (Fin k → Fin N)) (b : Fin p) :
    Set.InjOn (halaszResidueTupleQuotient (s := s) (k := k) (N := N) (M := M) p)
      ((Z×ˢFintype.piFinset (fun _ : Fin s =>
        univ.filter (fun x => halaszResidueIndex hp x=b))) :
          Finset ((Fin k → Fin N) × (Fin s → Fin M))) := by
  intro x hx y hy hxy
  apply Prod.ext
  · exact congrArg (fun z : (Fin k → Fin N) × (Fin s → Fin (M/p+1)) => z.1) hxy
  · funext i
    apply halasz_residue_quotient_injOn hp b
    · exact Fintype.mem_piFinset.mp (mem_product.mp hx).2 i
    · exact Fintype.mem_piFinset.mp (mem_product.mp hy).2 i
    · exact congrFun (congrArg
        (fun z : (Fin k → Fin N) × (Fin s → Fin (M/p+1)) => z.2) hxy) i

lemma halasz_residue_tuple_trace {s k N M p : ℕ} (hp : 0< p)
    (Z : Finset (Fin k → Fin N)) (b : Fin p)
    (x : (Fin k → Fin N) × (Fin s → Fin M))
    (hx : x∈Z×ˢFintype.piFinset (fun _ : Fin s =>
      univ.filter (fun x => halaszResidueIndex hp x=b))) :
    halaszCommonResidueFrequency p (p-1-b.val) (halaszResidueTupleQuotient p x) =
      fun j => halaszNatPowerFrequency k x.1 j + halaszNatPowerFrequency k x.2 j := by
  funext j
  dsimp [halaszCommonResidueFrequency,halaszResidueTupleQuotient,halaszNatPowerFrequency]
  congr 1
  apply sum_congr rfl
  intro i _
  rw [halasz_residue_quotient_recover hp b (x.2 i)
    (mem_filter.mp (Fintype.mem_piFinset.mp (mem_product.mp hx).2 i)).2]

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszNonsingularMoment
namespace OAI

/-! The nonsingular branch of the classical complete-system iteration.
All short-variable residue classes are included. -/
namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

theorem halasz_fixed_residue_moment {s k N M p r : ℕ} [Fact p.Prime]
    (hkp : k< p) (hrk : r+1≤ k) (hN : N< p^(r+1))
    (Z : Finset (Fin k → Fin N))
    (hZ : ∀ z∈Z, Function.Injective (fun i => (((z i).val+1:ℕ):ZMod p))) (b : Fin p) :
    halaszFiberEnergy
      (Z×ˢFintype.piFinset (fun _ : Fin s =>
        univ.filter (fun x : Fin M => halaszResidueIndex (Fact.out : p.Prime).pos x=b)))
      (fun x j => halaszNatPowerFrequency k x.1 j+halaszNatPowerFrequency k x.2 j) ≤
      (k^k*p^((r+1)*r/2)) * (N^k*halaszVinogradovCount s k (M/p+1)) := by
  let F := Z×ˢFintype.piFinset (fun _ : Fin s =>
    univ.filter (fun x : Fin M => halaszResidueIndex (Fact.out : p.Prime).pos x=b))
  let q := halaszResidueTupleQuotient (s := s) (k := k) (N := N) (M := M) p
  let I := F.image q
  have hq : Set.InjOn q F := halasz_residue_tuple_quotient_injOn (Fact.out : p.Prime).pos Z b
  have hI : ∀ x∈I, Function.Injective (fun i => (((x.1 i).val+1:ℕ):ZMod p)) := by
    intro x hx
    obtain ⟨y,hy,rfl⟩ := mem_image.mp hx
    exact hZ y.1 (mem_product.mp hy).1
  have ha : p-1-b.val< p := by have := b.isLt; omega
  have he := halasz_fiber_energy_transfer F q hq
    (fun x j => halaszNatPowerFrequency k x.1 j+halaszNatPowerFrequency k x.2 j)
    (halaszCommonResidueFrequency p (p-1-b.val))
    (fun x hx => halasz_residue_tuple_trace (Fact.out : p.Prime).pos Z b x hx)
  have hb := halasz_common_residue_energy (a := p-1-b.val) (r := r)
    (s := s) (N := N) (Q := M/p+1) hkp hrk ha hN I hI
  apply he.trans_le
  convert (preTransparency := .instances) hb using 1
  congr 1
  ext z
  simp only [I,mem_image]

theorem halasz_nonsingular_moment {s k N M p r : ℕ} [Fact p.Prime]
    (hs : 0< s) (hkp : k< p) (hrk : r+1≤ k) (hN : N< p^(r+1))
    (Z : Finset (Fin k → Fin N))
    (hZ : ∀ z∈Z, Function.Injective (fun i => (((z i).val+1:ℕ):ZMod p))) :
    halaszFiberEnergy (Z×ˢ(univ : Finset (Fin s → Fin M)))
      (fun x j => halaszNatPowerFrequency k x.1 j+halaszNatPowerFrequency k x.2 j) ≤
      p^(2*s) * ((k^k*p^((r+1)*r/2)) * (N^k*halaszVinogradovCount s k (M/p+1))) := by
  let f (z : Fin k → Fin N) : Fin k → ℤ := fun j => halaszNatPowerFrequency k z j
  let g (x : Fin M) : Fin k → ℤ := fun j => ((x.val+1)^(j.val+1):ℕ)
  have he (G : Finset (Fin M)) :
      halaszFiberEnergy (Z×ˢFintype.piFinset (fun _ : Fin s => G))
        (fun x => f x.1+∑ i, g (x.2 i)) =
      halaszFiberEnergy (Z×ˢFintype.piFinset (fun _ : Fin s => G))
        (fun x j => halaszNatPowerFrequency k x.1 j+halaszNatPowerFrequency k x.2 j) := by
    rw [← halasz_fiber_energy_natCast]
    congr 1
    funext x j
    simp only [f,g,Pi.add_apply,Finset.sum_apply,halaszNatPowerFrequency,Nat.cast_add,Nat.cast_sum]
  have hh := halasz_residue_average_energy hs Z (univ : Finset (Fin M))
    (halaszResidueIndex (Fact.out : p.Prime).pos) f g
    ((k^k*p^((r+1)*r/2)) * (N^k*halaszVinogradovCount s k (M/p+1)))
    (by
      intro b
      rw [he]
      exact halasz_fixed_residue_moment hkp hrk hN Z hZ b)
  rw [he] at hh
  simpa only [Fintype.piFinset_univ] using hh

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszPrimeMoment
namespace OAI

/-! The selected-prime cover meets the proved nonsingular moment
estimate, with the original short-variable endpoint retained. -/
namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma halasz_residue_good_product (s k N p : ℕ) :
    halaszFiberEnergy
      (halaszResidueGoodTuples (N := N) (fun i : Fin k => i.castAdd s) p)
      (halaszVinogradovFrequency k) =
    halaszFiberEnergy
      ((univ.filter (fun z : Fin k → Fin N => Function.Injective
        (fun i => (((z i).val+1:ℕ):ZMod p))))×ˢ(univ : Finset (Fin s → Fin N)))
      (fun x j => halaszNatPowerFrequency k x.1 j+halaszNatPowerFrequency k x.2 j) := by
  let Z := (univ : Finset (Fin k → Fin N)).filter (fun z => Function.Injective
    (fun i => (((z i).val+1:ℕ):ZMod p)))
  let F := Z×ˢ(univ : Finset (Fin s → Fin N))
  let e := halaszTupleJoin k s N
  have himage : F.image e =
      halaszResidueGoodTuples (N := N) (fun i : Fin k => i.castAdd s) p := by
    ext x
    constructor
    · rintro hx
      obtain ⟨z,hz,rfl⟩ := mem_image.mp hx
      have hzI := (mem_filter.mp (mem_product.mp hz).1).2
      apply mem_filter.mpr
      refine ⟨mem_univ _,?_⟩
      simpa only [e,halaszTupleJoin,Equiv.coe_fn_mk,Fin.append_left] using hzI
    · intro hx
      refine mem_image.mpr ⟨e.symm x,?_,e.apply_symm_apply x⟩
      apply mem_product.mpr
      refine ⟨mem_filter.mpr ⟨mem_univ _,?_⟩,mem_univ _⟩
      exact (mem_filter.mp hx).2
  have hf (z : (Fin k → Fin N) × (Fin s → Fin N)) :
      halaszVinogradovFrequency k (e z) =
        (fun j => ((halaszNatPowerFrequency k z.1 j+
          halaszNatPowerFrequency k z.2 j:ℕ):ℤ)) := by
    funext j
    simp only [halaszVinogradovFrequency,e,halaszTupleJoin,Equiv.coe_fn_mk,
      Fin.sum_univ_add,Fin.append_left,Fin.append_right,halaszNatPowerFrequency,
      Nat.cast_add,Nat.cast_sum]
  have he := halasz_fiber_energy_transfer F e e.injective.injOn
    (fun z j => ((halaszNatPowerFrequency k z.1 j+
      halaszNatPowerFrequency k z.2 j:ℕ):ℤ)) (halaszVinogradovFrequency k)
    (fun z _ => hf z)
  rw [halasz_fiber_energy_natCast] at he
  convert (preTransparency := .instances) he.symm using 1
  congr 1
  convert (preTransparency := .instances) himage.symm using 1
  ext x
  simp only [mem_image]

theorem halasz_residue_good_moment {s k N p : ℕ} [Fact p.Prime]
    (hs : 0< s) (hk : 0< k) (hkp : k< p) (hNp : N< p^k) :
    halaszFiberEnergy
      (halaszResidueGoodTuples (N := N) (fun i : Fin k => i.castAdd s) p)
      (halaszVinogradovFrequency k) ≤
      p^(2*s)*((k^k*p^(k*(k-1)/2))*(N^k*halaszVinogradovCount s k (N/p+1))) := by
  rw [halasz_residue_good_product]
  have hk1 : k-1+1=k := Nat.sub_add_cancel hk
  have h := halasz_nonsingular_moment (s := s) (M := N) (r := k-1) hs hkp (by omega)
    (by simpa only [hk1] using hNp)
    ((univ : Finset (Fin k → Fin N)).filter (fun z => Function.Injective
      (fun i => (((z i).val+1:ℕ):ZMod p))))
    (fun z hz => (mem_filter.mp hz).2)
  simpa only [hk1] using h

end TwoPointCorrelations

end OAI

end

theorem solution : type_of% @OAI.TwoPointCorrelations.halasz_residue_good_moment := @OAI.TwoPointCorrelations.halasz_residue_good_moment
