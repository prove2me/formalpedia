-- Prove2me | solution 1 for GlobalTheory.pSerFrob_of_invariance
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:27:55.9969+00:00
-- url     : https://prove2.me/submissions/ddfab0d3-dbd6-4804-9e52-201fc9806fa6

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_PSerFrobStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_PSerFrobOfInvariance
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open TensorProduct IsLocalRing Matrix ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2
namespace GlobalTheory
private lemma pSerOf_trunc {R₀ : Type} [CommRing R₀] {g : ℕ} (N : ℕ) (G₁ : MvPolynomial (Fin g) R₀) :
    ∃ G : MvPolynomial (Fin g) R₀,
      (∀ m, MvPolynomial.coeff m G = if ∀ i, m i < N then MvPolynomial.coeff m G₁ else 0) ∧
      ∀ (S : Type) [CommRing S] [Algebra R₀ S] (a : Fin g → S), (∀ i, a i ^ N = 0) →
        MvPolynomial.aeval a G = MvPolynomial.aeval a G₁ := by
  classical
  refine ⟨∑ m ∈ G₁.support.filter (fun m => ∀ i, m i < N),
    MvPolynomial.monomial m (MvPolynomial.coeff m G₁), ?_, ?_⟩
  · intro m
    rw [MvPolynomial.coeff_sum]
    simp only [MvPolynomial.coeff_monomial]
    rw [Finset.sum_ite_eq']
    by_cases h : ∀ i, m i < N
    · by_cases h0 : MvPolynomial.coeff m G₁ = 0
      · simp [h0]
      · simp [h, h0]
    · rw [if_neg h, if_neg]
      intro hm
      exact h (Finset.mem_filter.1 hm).2
  · intro S _ _ a ha
    conv_rhs => rw [G₁.as_sum]
    rw [map_sum, map_sum, Finset.sum_filter]
    refine Finset.sum_congr rfl fun m _ => ?_
    split_ifs with h
    · rfl
    · push Not at h
      obtain ⟨i, hi⟩ := h
      have hz : ∏ j, a j ^ m j = 0 :=
        Finset.prod_eq_zero (f := fun j => a j ^ m j) (Finset.mem_univ i)
          (pow_eq_zero_of_le hi (ha i))
      rw [MvPolynomial.aeval_monomial, Finsupp.prod_fintype _ _ (by simp), hz, mul_zero]
end GlobalTheory
end

set_option autoImplicit false
open TensorProduct IsLocalRing Matrix ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
  (∀ {R₀ : Type} [CommRing R₀] {ι : Type} [Fintype ι] [DecidableEq ι] (f : MvPowerSeries ι R₀) (S : Type) [CommRing S] [Algebra R₀ S] (a : ι → S),
    (∀ N : ℕ, (∀ i, a i ^ N = 0) → nEval f a = tEval N f a) ∧
    ((∀ i, IsNilpotent (a i)) → (∀ (S' : Type) [CommRing S'] [Algebra R₀ S'] (φ : S →ₐ[R₀] S'), φ (nEval f a) = nEval f (fun i => φ (a i))) ∧
      nEval f a - algebraMap R₀ S (MvPowerSeries.coeff 0 f) ∈ Ideal.span (Set.range a))) →
  (∀ {R₀ : Type} [CommRing R₀] {g : ℕ} {B : BX R₀} {K : LAlg R₀} (ch : FormalChartAtZero B K g) (n : ℕ) (S : Type) [CommRing S] [Algebra R₀ S], (n : S) = 0 → ∀ a e : Fin g → S, (∀ i, IsNilpotent (a i)) →
    (∀ i j, e i * e j = 0) → nsmulF ch.F (a + e) n = nsmulF ch.F a n) →
  (∀ {R₀ : Type} [CommRing R₀] (p : ℕ) [Fact p.Prime] (g N : ℕ) (G : MvPolynomial (Fin g) R₀),
    (∀ (S : Type) [CommRing S] [Algebra R₀ S], (p : S) = 0 → ∀ a e : Fin g → S, (∀ i, a i ^ N = 0) → (∀ i j, e i * e j = 0) →
      MvPolynomial.aeval (a + e) G = MvPolynomial.aeval a G) →
    ∀ m : Fin g →₀ ℕ, (∀ i, m i < N) → (∃ i, ¬ p ∣ m i) → ∃ r : R₀, MvPolynomial.coeff m G = p * r) →
  (∀ {R₀ : Type} [CommRing R₀] (p : ℕ) [Fact p.Prime] {g : ℕ} {B : BX R₀} (K : LAlg R₀) (ch : FormalChartAtZero B K g), PSerFrobStatement p K ch) := by
  intro hev hinv hcoef R₀ _ p _ g B K ch N
  classical

  have hnil : ∀ (S : Type) [CommRing S] [Algebra R₀ S] (a b : Fin g → S),
      (∀ i, IsNilpotent (a i)) → (∀ i, IsNilpotent (b i)) → ∀ k, IsNilpotent (fAdd ch.F a b k) := by
    intro S _ _ a b ha hb k
    have h0 : algebraMap R₀ S (MvPowerSeries.coeff 0 (ch.F k)) = 0 := by
      have h1 := ((hev (ch.F k) S (Sum.elim (0 : Fin g → S) (0 : Fin g → S))).2
        (by rintro (i | i) <;> simp)).2
      have h2 : nEval (ch.F k) (Sum.elim (0 : Fin g → S) (0 : Fin g → S)) = 0 :=
        congrFun (ch.F_unit S 0 (by simp)) k
      have h3 : Ideal.span (Set.range (Sum.elim (0 : Fin g → S) (0 : Fin g → S))) = ⊥ := by
        rw [Ideal.span_eq_bot]
        rintro _ ⟨i | i, rfl⟩ <;> simp
      rw [h2, h3, Ideal.mem_bot, zero_sub, neg_eq_zero] at h1
      exact h1
    have h1 := ((hev (ch.F k) S (Sum.elim a b)).2 (by rintro (i | i); exacts [ha i, hb i])).2
    rw [h0, sub_zero] at h1
    have h2 : Ideal.span (Set.range (Sum.elim a b)) ≤ nilradical S := by
      rw [Ideal.span_le]
      rintro _ ⟨i | i, rfl⟩
      exacts [mem_nilradical.2 (ha i), mem_nilradical.2 (hb i)]
    exact mem_nilradical.1 (h2 h1)
  have hnil' : ∀ (S : Type) [CommRing S] [Algebra R₀ S] (a : Fin g → S),
      (∀ i, IsNilpotent (a i)) → ∀ n k, IsNilpotent (nsmulF ch.F a n k) := by
    intro S _ _ a ha n
    induction n with
    | zero => intro k; simp [nsmulF]
    | succ n ih => exact hnil S _ _ ih ha
  have hnat : ∀ (S : Type) [CommRing S] [Algebra R₀ S] (S' : Type) [CommRing S'] [Algebra R₀ S']
      (φ : S →ₐ[R₀] S') (a : Fin g → S), (∀ i, IsNilpotent (a i)) → ∀ n k,
      φ (nsmulF ch.F a n k) = nsmulF ch.F (fun i => φ (a i)) n k := by
    intro S _ _ S' _ _ φ a ha n
    induction n with
    | zero => intro k; simp [nsmulF]
    | succ n ih =>
      intro k
      have h1 := ((hev (ch.F k) S (Sum.elim (nsmulF ch.F a n) a)).2
        (by rintro (i | i); exacts [hnil' S a ha n i, ha i])).1 S' φ
      change φ (nEval (ch.F k) (Sum.elim (nsmulF ch.F a n) a)) =
        nEval (ch.F k) (Sum.elim (nsmulF ch.F (fun i => φ (a i)) n) (fun i => φ (a i)))
      rw [h1]
      congr 1
      funext i
      rcases i with i | i
      · exact ih i
      · rfl

  let I : Ideal (MvPolynomial (Fin g) R₀) :=
    Ideal.span (Set.range fun j : Fin g => (MvPolynomial.X j : MvPolynomial (Fin g) R₀) ^ (N + 1))
  let x : Fin g → MvPolynomial (Fin g) R₀ ⧸ I := fun j => Ideal.Quotient.mk I (MvPolynomial.X j)
  have hx : ∀ j, IsNilpotent (x j) := fun j => ⟨N + 1, by
    change Ideal.Quotient.mk I (MvPolynomial.X j) ^ (N + 1) = 0
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span ⟨j, rfl⟩⟩
  choose G₁ hG₁ using fun k => Ideal.Quotient.mk_surjective (nsmulF ch.F x p k)
  have huniv : ∀ (S : Type) [CommRing S] [Algebra R₀ S] (a : Fin g → S),
      (∀ i, a i ^ (N + 1) = 0) → ∀ k, nsmulF ch.F a p k = MvPolynomial.aeval a (G₁ k) := by
    intro S _ _ a ha k
    let φ : (MvPolynomial (Fin g) R₀ ⧸ I) →ₐ[R₀] S :=
      Ideal.Quotient.liftₐ I (MvPolynomial.aeval a) (by
        intro f hf
        have : I ≤ RingHom.ker (MvPolynomial.aeval a : MvPolynomial (Fin g) R₀ →ₐ[R₀] S) := by
          rw [Ideal.span_le]
          rintro _ ⟨j, rfl⟩
          simp [RingHom.mem_ker, ha j]
        exact this hf)
    have hφ : ∀ f, φ (Ideal.Quotient.mk I f) = MvPolynomial.aeval a f := fun f => rfl
    have h1 := hnat _ S φ x hx p k
    have h2 : (fun i => φ (x i)) = a := by
      funext i
      change φ (Ideal.Quotient.mk I _) = _
      rw [hφ, MvPolynomial.aeval_X]
    rw [h2, ← hG₁ k, hφ] at h1
    exact h1.symm
  choose G hG hGe using fun k => pSerOf_trunc N (G₁ k)
  refine ⟨G, ?_, ?_⟩
  · intro k m hm
    rw [hG]
    split_ifs with h
    · refine hcoef p g N (G₁ k) ?_ m h hm
      intro S _ _ hp a e ha he
      have h1 : ∀ i, (a + e) i ^ (N + 1) = 0 := fun i =>
        (Commute.all (a i) (e i)).add_pow_eq_zero_of_add_le_succ_of_pow_eq_zero (ha i)
          (show e i ^ 2 = 0 by rw [sq, he]) (by omega)
      have h2 : ∀ i, a i ^ (N + 1) = 0 := fun i => by rw [pow_succ, ha i, zero_mul]
      rw [← huniv S _ h1, ← huniv S _ h2, hinv ch p S hp a e (fun i => ⟨N, ha i⟩) he]
    · exact ⟨0, by simp⟩
  · intro S _ _ a ha
    funext k
    rw [hGe k S a ha]
    exact huniv S a (fun i => by rw [pow_succ, ha i, zero_mul]) k
end GlobalTheory
