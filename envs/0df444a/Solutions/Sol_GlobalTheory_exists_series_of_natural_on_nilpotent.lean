-- Prove2me | solution 1 for GlobalTheory.exists_series_of_natural_on_nilpotent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:00:09.508044+00:00
-- url     : https://prove2.me/submissions/75e9fcf6-d7c2-4bc3-ba80-7a516202a564

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsSeriesOfNaturalOnNilpotent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory
private lemma serNat_coeff {R₀ κ : Type} [CommRing R₀] [DecidableEq κ] {N : ℕ}
    {q : MvPolynomial κ R₀} (hq : q ∈ serNatI R₀ κ N) :
    ∀ m : κ →₀ ℕ, (∀ j, m j < N) → MvPolynomial.coeff m q = 0 := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hq
  · rintro _ ⟨j, rfl⟩ m hm
    simp only [MvPolynomial.coeff_X_pow]
    rw [if_neg]
    rintro rfl
    simpa using hm j
  · intro m _; simp
  · intro x y _ _ hx hy m hm
    rw [MvPolynomial.coeff_add, hx m hm, hy m hm, add_zero]
  · intro r x _ hx m hm
    rw [smul_eq_mul, MvPolynomial.coeff_mul]
    refine Finset.sum_eq_zero fun p hp => ?_
    rw [hx p.2, mul_zero]
    intro j
    have : p.1 + p.2 = m := by simpa using hp
    have h2 := hm j
    rw [← this, Finsupp.add_apply] at h2
    omega
private lemma serNat_nil {R₀ κ : Type} [CommRing R₀] (N : ℕ) (j : κ) :
    (Ideal.Quotient.mk (serNatI R₀ κ N) (MvPolynomial.X j)) ^ N = 0 := by
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span ⟨j, rfl⟩
private lemma serNat_aeval {R₀ κ : Type} [CommRing R₀] [Fintype κ] [DecidableEq κ]
    {S : Type} [CommRing S] [Algebra R₀ S] {N : ℕ} {a : κ → S} (ha : ∀ i, a i ^ N = 0)
    (q : MvPolynomial κ R₀) :
    MvPolynomial.aeval a q = ∑ e : κ → Fin N, algebraMap R₀ S (MvPolynomial.coeff
      (Finsupp.equivFunOnFinite.symm fun i => (e i : ℕ)) q) * ∏ i, a i ^ (e i : ℕ) := by
  induction q using MvPolynomial.induction_on' with
  | add p q hp hq =>
    simp only [map_add, MvPolynomial.coeff_add, add_mul, Finset.sum_add_distrib, hp, hq]
  | monomial m r =>
    rw [MvPolynomial.aeval_monomial, Finsupp.prod_fintype _ _ (fun i => pow_zero _)]
    by_cases hm : ∀ j, m j < N
    · rw [Finset.sum_eq_single (fun j => (⟨m j, hm j⟩ : Fin N))]
      · rw [MvPolynomial.coeff_monomial, if_pos]
        ext j; simp
      · intro e _ he
        rw [MvPolynomial.coeff_monomial, if_neg, map_zero, zero_mul]
        intro h
        apply he
        funext j
        apply Fin.ext
        simp [h]
      · intro h; exact absurd (Finset.mem_univ _) h
    · rw [Finset.sum_eq_zero]
      · push Not at hm
        obtain ⟨j, hj⟩ := hm
        rw [Finset.prod_eq_zero (f := fun i => a i ^ m i) (Finset.mem_univ j)
          (pow_eq_zero_of_le hj (ha j)), mul_zero]
      · intro e _
        rw [MvPolynomial.coeff_monomial, if_neg, map_zero, zero_mul]
        intro h
        apply hm
        intro j
        simp [h]
end GlobalTheory
end

set_option autoImplicit false
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
  (∀ {R₀ : Type} [CommRing R₀] {κ : Type} [Fintype κ] [DecidableEq κ] (f : MvPowerSeries κ R₀) (S : Type) [CommRing S] [Algebra R₀ S] (a : κ → S),
    (∀ N : ℕ, (∀ i, a i ^ N = 0) → nEval f a = tEval N f a) ∧
    ((∀ i, IsNilpotent (a i)) → (∀ (S' : Type) [CommRing S'] [Algebra R₀ S'] (φ : S →ₐ[R₀] S'), φ (nEval f a) = nEval f (fun i => φ (a i))) ∧
      nEval f a - algebraMap R₀ S (MvPowerSeries.coeff 0 f) ∈ Ideal.span (Set.range a))) →
  (∀ {R₀ : Type} [CommRing R₀] {κ : Type} [Fintype κ] [DecidableEq κ] (c : ∀ (S : Type) [CommRing S] [Algebra R₀ S], (κ → S) → S),
    (∀ (S : Type) [CommRing S] [Algebra R₀ S] (S' : Type) [CommRing S'] [Algebra R₀ S'] (φ : S →ₐ[R₀] S') (a : κ → S),
      (∀ i, IsNilpotent (a i)) → φ (c S a) = c S' (fun i => φ (a i))) →
    ∃ f : MvPowerSeries κ R₀, ∀ (S : Type) [CommRing S] [Algebra R₀ S] (a : κ → S), (∀ i, IsNilpotent (a i)) → c S a = nEval f a) := by
  intro hE R₀ _ κ _ _ c hc
  choose p hp using fun N : ℕ => Ideal.Quotient.mk_surjective (I := serNatI R₀ κ N)
    (c (MvPolynomial κ R₀ ⧸ serNatI R₀ κ N)
      (fun j => Ideal.Quotient.mk (serNatI R₀ κ N) (MvPolynomial.X j)))
  have key : ∀ (N : ℕ) (S : Type) [CommRing S] [Algebra R₀ S] (a : κ → S), (∀ i, a i ^ N = 0) →
      c S a = MvPolynomial.aeval a (p N) := by
    intro N S _ _ a ha
    let φ : (MvPolynomial κ R₀ ⧸ serNatI R₀ κ N) →ₐ[R₀] S :=
      Ideal.Quotient.liftₐ (serNatI R₀ κ N) (MvPolynomial.aeval a) (by
        intro x hx
        have : serNatI R₀ κ N ≤ RingHom.ker (MvPolynomial.aeval (R := R₀) a) := by
          refine Ideal.span_le.2 ?_
          rintro _ ⟨j, rfl⟩
          simp [RingHom.mem_ker, ha j]
        exact this hx)
    have hφ : ∀ x, φ (Ideal.Quotient.mk (serNatI R₀ κ N) x) = MvPolynomial.aeval a x :=
      fun x => rfl
    have h := hc _ S φ (fun j => Ideal.Quotient.mk (serNatI R₀ κ N) (MvPolynomial.X j))
      (fun j => ⟨N, serNat_nil N j⟩)
    rw [← hp N, hφ] at h
    simp only [hφ, MvPolynomial.aeval_X] at h
    exact h.symm
  have compat : ∀ N M : ℕ, N ≤ M → ∀ m : κ →₀ ℕ, (∀ j, m j < N) →
      MvPolynomial.coeff m (p M) = MvPolynomial.coeff m (p N) := by
    intro N M h m hm
    have h1 := key M _ (fun j => Ideal.Quotient.mk (serNatI R₀ κ N) (MvPolynomial.X j))
      (fun j => pow_eq_zero_of_le h (serNat_nil N j))
    have h2 : MvPolynomial.aeval (R := R₀)
        (fun j => Ideal.Quotient.mk (serNatI R₀ κ N) (MvPolynomial.X j))
        = Ideal.Quotient.mkₐ R₀ (serNatI R₀ κ N) := by
      ext j; simp
    rw [← hp N, h2, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq] at h1
    have h3 := serNat_coeff h1 m hm
    rw [MvPolynomial.coeff_sub, sub_eq_zero] at h3
    exact h3.symm
  refine ⟨fun m => MvPolynomial.coeff m (p (Finset.univ.sup m + 1)), ?_⟩
  intro S _ _ a ha
  choose n hn using ha
  have hN : ∀ i, a i ^ (Finset.univ.sup n) = 0 := fun i =>
    pow_eq_zero_of_le (Finset.le_sup (f := n) (Finset.mem_univ i)) (hn i)
  generalize Finset.univ.sup n = N at hN
  refine Eq.trans ?_ ((hE _ S a).1 N hN).symm
  rw [key N S a hN, serNat_aeval hN]
  unfold tEval
  refine Finset.sum_congr rfl fun e _ => ?_
  congr 2
  set m : κ →₀ ℕ := Finsupp.equivFunOnFinite.symm fun i => (e i : ℕ) with hm
  change _ = MvPolynomial.coeff m (p (Finset.univ.sup m + 1))
  rw [← compat N (max N (Finset.univ.sup m + 1)) (le_max_left _ _) m (fun j => by simp [hm]),
    compat _ _ (le_max_right _ _) m
      (fun j => Nat.lt_succ_of_le (Finset.le_sup (f := m) (Finset.mem_univ j)))]
end GlobalTheory
