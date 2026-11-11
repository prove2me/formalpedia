-- Prove2me | solution 1 for HarmonicGames.Projection.theorem_6_1
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-10T08:07:59.620379+00:00
-- url     : https://prove2.me/submissions/20a5c187-b02c-4739-a82f-cd385523e234

import Mathlib
import Definitions.Def_HarmonicGames_Projection_Closest
import Theorems.Thm_HarmonicGames_Decomposition_lemma_4_1

open HarmonicGames.Decomposition

section Aux

variable {ι : Type} [Fintype ι] [DecidableEq ι] (E : ι → Type) [∀ m, Fintype (E m)]
  [∀ m, DecidableEq (E m)]

private lemma c1_sum_apply {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {κ : Type*} (s : Finset κ) (X : κ → C1 G) (p q : V) :
    (∑ k ∈ s, X k) p q = ∑ k ∈ s, X k p q := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => simp [Finset.sum_insert ha, ih]

private lemma Dop_apply (u : Games E) (p q : ∀ k, E k) :
    (Dop E u) p q = ∑ k, (if MComparable E k p q then (1 : ℝ) else 0) * (u k q - u k p) := by
  show (∑ k, Dm E k (u k)) p q = _
  rw [c1_sum_apply]
  rfl

private lemma Dm_apply (m : ι) (φ : Util E) (p q : ∀ k, E k) :
    (Dm E m φ) p q = (if MComparable E m p q then (1 : ℝ) else 0) * (φ q - φ p) := rfl

private lemma Dop_update (u : Games E) (m : ι) (p : ∀ k, E k) (a : E m) :
    (Dop E u) p (Function.update p m a) =
      u m (Function.update p m a) - u m p := by
  rw [Dop_apply, Finset.sum_eq_single m]
  · by_cases h : Function.update p m a = p
    · rw [h]; simp
    · have hc : MComparable E m p (Function.update p m a) := by
        refine ⟨fun e => h e.symm, fun k hk => ?_⟩
        simp [Function.update_of_ne hk]
      rw [if_pos hc, one_mul]
  · intro k _ hk
    have : ¬ MComparable E k p (Function.update p m a) := by
      rintro ⟨h1, h2⟩
      have hpm : p m = a := by
        have := h2 m (fun e => hk e.symm)
        simpa using this
      have e : Function.update p m a = p := by
        rw [← hpm]; exact Function.update_eq_self m p
      exact h1 e.symm
    simp [this]
  · intro h; exact absurd (Finset.mem_univ m) h

private lemma comparable_exclusive {m k : ι} (hmk : m ≠ k) {p q : ∀ j, E j}
    (h1 : MComparable E m p q) (h2 : MComparable E k p q) : False := by
  obtain ⟨hne, hm⟩ := h1
  obtain ⟨_, hk⟩ := h2
  apply hne
  funext j
  by_cases hj : j = m
  · rw [hj]; exact hk m hmk
  · exact hm j hj

private lemma Dm_eq_zero_of_ker (y : Games E) (hy : Dop E y = 0) (m : ι) :
    Dm E m (y m) = 0 := by
  ext p q
  rw [Dm_apply]
  by_cases hc : MComparable E m p q
  · have hq : q = Function.update p m (q m) := by
      funext j
      by_cases hj : j = m
      · rw [hj]; simp
      · rw [Function.update_of_ne hj]; exact (hc.2 j hj).symm
    have h0 := Dop_update E y m p (q m)
    rw [← hq] at h0
    have h1 : y m q - y m p = 0 := by rw [← h0, hy] <;> rfl
    rw [if_pos hc, h1]; simp
  · simp [hc]

private lemma cross_zero (m k : ι) (hmk : m ≠ k) (x y : Util E) :
    innerC1 (gameGraph E) (Dm E m x) (Dm E k y) = 0 := by
  unfold innerC1
  rw [mul_eq_zero]; right
  refine Finset.sum_eq_zero fun p _ => Finset.sum_eq_zero fun q _ => ?_
  split_ifs with hadj
  · rw [Dm_apply, Dm_apply]
    by_cases h1 : MComparable E m p q
    · by_cases h2 : MComparable E k p q
      · exact (comparable_exclusive E hmk h1 h2).elim
      · simp [h2]
    · simp [h1]
  · rfl

private lemma sum_inner_Dm (a b : Games E) :
    ∑ m, innerC1 (gameGraph E) (Dm E m (a m)) (Dm E m (b m)) =
      innerC1 (gameGraph E) (Dop E a) (Dop E b) := by
  have h : innerC1 (gameGraph E) (Dop E a) (Dop E b) = inner ℝ (Dop E a) (Dop E b) := rfl
  rw [h]
  show _ = inner ℝ (∑ m, Dm E m (a m)) (∑ k, Dm E k (b k))
  rw [sum_inner]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [inner_sum, Finset.sum_eq_single m]
  · rfl
  · intro k _ hk; exact cross_zero E m k (Ne.symm hk) _ _
  · intro h; exact absurd (Finset.mem_univ m) h

private lemma key1 [∀ m, Nonempty (E m)] (m : ι) (x y : Util E) (hx : Pim E m x = x) :
    (Fintype.card (E m) : ℝ) * ∑ p, x p * y p =
      innerC1 (gameGraph E) (Dm E m x) (Dm E m y) := by
  have h41 := lemma_4_1 ι E m
  have h1 : (Fintype.card (E m) : ℝ) • x = LinearMap.adjoint (Dm E m) (Dm E m x) := by
    have : Delta0m E m x = (Fintype.card (E m) : ℝ) • Pim E m x := by rw [h41]; rfl
    rw [hx] at this
    exact this.symm
  have h2 : inner ℝ ((Fintype.card (E m) : ℝ) • x) y = inner ℝ (Dm E m x) (Dm E m y) := by
    rw [h1, LinearMap.adjoint_inner_left]
  have h3 : inner ℝ ((Fintype.card (E m) : ℝ) • x) y =
      (Fintype.card (E m) : ℝ) * ∑ p, x p * y p := by
    rw [real_inner_smul_left]
    congr 1
    simp [PiLp.inner_apply, mul_comm]
  rw [← h3, h2]
  rfl

private lemma pim_of_piop (v : Games E) (hv : PiOp E v = v) (m : ι) : Pim E m (v m) = v m := by
  have h := congrArg (fun w : Games E => w m) hv
  exact h

private lemma orthN [∀ m, Nonempty (E m)] (a b : ι → (∀ k, E k) → ℝ)
    (ha : PiOp E (HarmonicGames.Projection.toGames E a) = HarmonicGames.Projection.toGames E a)
    (hb : HarmonicGames.Projection.toGames E b ∈ nonstrategicSubspace E) :
    HarmonicGames.Projection.innerME E a b = 0 := by
  unfold HarmonicGames.Projection.innerME
  refine Finset.sum_eq_zero fun m _ => ?_
  have hk := key1 E m (HarmonicGames.Projection.toGames E a m)
    (HarmonicGames.Projection.toGames E b m) (pim_of_piop E _ ha m)
  have hz : Dm E m (HarmonicGames.Projection.toGames E b m) = 0 :=
    Dm_eq_zero_of_ker E _ (LinearMap.mem_ker.1 hb) m
  rw [hz] at hk
  have : innerC1 (gameGraph E) (Dm E m (HarmonicGames.Projection.toGames E a m)) 0 = 0 := by
    unfold innerC1
    simp
  rw [this] at hk
  simpa [HarmonicGames.Projection.toGames_apply] using hk

end Aux

theorem solution {ι : Type} [Fintype ι] [DecidableEq ι] (E : ι → Type)
    [∀ m, Fintype (E m)] [∀ m, DecidableEq (E m)] [∀ m, Nonempty (E m)] :
    (∀ a b : ι → (∀ m, E m) → ℝ, HarmonicGames.Projection.toGames E a ∈ HarmonicGames.Decomposition.potentialSubspace E →
        HarmonicGames.Projection.toGames E b ∈ HarmonicGames.Decomposition.harmonicSubspace E → HarmonicGames.Projection.innerME E a b = 0) ∧
      (∀ a b : ι → (∀ m, E m) → ℝ, HarmonicGames.Projection.toGames E a ∈ HarmonicGames.Decomposition.potentialSubspace E →
        HarmonicGames.Projection.toGames E b ∈ HarmonicGames.Decomposition.nonstrategicSubspace E → HarmonicGames.Projection.innerME E a b = 0) ∧
      (∀ a b : ι → (∀ m, E m) → ℝ, HarmonicGames.Projection.toGames E a ∈ HarmonicGames.Decomposition.harmonicSubspace E →
        HarmonicGames.Projection.toGames E b ∈ HarmonicGames.Decomposition.nonstrategicSubspace E → HarmonicGames.Projection.innerME E a b = 0) := by
  have hPi : ∀ v : Games E, (v ∈ LinearMap.eqLocus LinearMap.id (PiOp E)) → PiOp E v = v := by
    intro v hv
    simpa [LinearMap.mem_eqLocus] using hv.symm
  refine ⟨?_, ?_, ?_⟩
  · intro a b ha hb
    have hPa := hPi _ ha.1
    obtain ⟨φ, hφ⟩ := LinearMap.mem_range.1 (Submodule.mem_comap.1 ha.2)
    have hdiv : LinearMap.adjoint (delta0 (gameGraph E))
        (Dop E (HarmonicGames.Projection.toGames E b)) = 0 :=
      LinearMap.mem_ker.1 (Submodule.mem_comap.1 hb.2)
    unfold HarmonicGames.Projection.innerME
    calc _ = ∑ m, innerC1 (gameGraph E) (Dm E m (HarmonicGames.Projection.toGames E a m))
            (Dm E m (HarmonicGames.Projection.toGames E b m)) := by
          refine Finset.sum_congr rfl fun m _ => ?_
          have := key1 E m (HarmonicGames.Projection.toGames E a m)
            (HarmonicGames.Projection.toGames E b m) (pim_of_piop E _ hPa m)
          simpa [HarmonicGames.Projection.toGames_apply] using this
      _ = innerC1 (gameGraph E) (Dop E (HarmonicGames.Projection.toGames E a))
            (Dop E (HarmonicGames.Projection.toGames E b)) := sum_inner_Dm E _ _
      _ = 0 := by
          have h : innerC1 (gameGraph E) (Dop E (HarmonicGames.Projection.toGames E a))
              (Dop E (HarmonicGames.Projection.toGames E b)) =
              inner ℝ (Dop E (HarmonicGames.Projection.toGames E a))
              (Dop E (HarmonicGames.Projection.toGames E b)) := rfl
          rw [h, ← hφ, ← LinearMap.adjoint_inner_right, hdiv]
          simp
  · intro a b ha hb
    exact orthN E a b (hPi _ ha.1) hb
  · intro a b ha hb
    exact orthN E a b (hPi _ ha.1) hb
