-- Prove2me | solution 1 for HarmonicGames.UniformMixed.proposition_5_2
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-04T11:41:41.986192+00:00
-- url     : https://prove2.me/submissions/f9f04696-8333-4db2-a466-45d560d25e42

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_HartSchmeidler_Finite_Game
import Definitions.Def_HarmonicGames_Decomposition_Games
import Definitions.Def_HarmonicGames_GenericPure_Games


namespace GTHarm
open HarmonicGames.Decomposition HarmonicGames.GenericPure Finset

theorem div_free {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (X : C1 G) (hX : LinearMap.adjoint (delta0 G) X = 0) (p : V) :
    ∑ q, X p q = 0 := by
  have h := congrArg (fun z => inner ℝ z (EuclideanSpace.single p (1:ℝ))) hX
  simp only [LinearMap.adjoint_inner_left, inner_zero_left] at h
  change innerC1 G X (delta0 G (EuclideanSpace.single p (1:ℝ))) = 0 at h
  unfold innerC1 at h
  simp only [delta0, gradOn, LinearMap.coe_mk, AddHom.coe_mk, C1.mk_apply,
    PiLp.single_apply] at h
  have e : ∀ a b, (if G.Adj a b then X a b * ((if G.Adj a b then (1:ℝ) else 0) *
      ((if b = p then 1 else 0) - if a = p then 1 else 0)) else 0) =
      X a b * (if b = p then 1 else 0) - X a b * (if a = p then 1 else 0) := by
    intro a b
    by_cases hab : G.Adj a b
    · simp [hab, mul_sub]
    · simp [hab, C1.eq_zero_of_not_adj G X hab]
  simp only [e] at h
  have anti : ∀ a, X a p = - X p a := by
    intro a
    by_cases hab : G.Adj p a
    · exact C1.antisymm G X hab
    · have : ¬ G.Adj a p := fun h' => hab h'.symm
      rw [C1.eq_zero_of_not_adj G X hab, C1.eq_zero_of_not_adj G X this]; simp
  have t1 : ∑ a, ∑ b, X a b * (if b = p then (1:ℝ) else 0) = ∑ a, X a p := by simp
  have t2 : ∑ a, ∑ b, X a b * (if a = p then (1:ℝ) else 0) = ∑ b, X p b := by
    rw [Finset.sum_eq_single p]
    · simp
    · intro a _ hap; simp [hap]
    · simp
  simp only [Finset.sum_sub_distrib] at h
  rw [t1, t2] at h
  simp only [anti, Finset.sum_neg_distrib] at h
  linarith

theorem C1_sum_apply {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {κ : Type*} (s : Finset κ) (F : κ → C1 G) (p q : V) :
    (∑ k ∈ s, F k) p q = ∑ k ∈ s, F k p q := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, C1.add_apply, ih]

section
variable {ι : Type} [Fintype ι] [DecidableEq ι] (E : ι → Type) [∀ m, Fintype (E m)]
  [∀ m, DecidableEq (E m)]

theorem Dop_apply (u : Games E) (p q : ∀ k, E k) :
    (Dop E u) p q = ∑ m, (if MComparable E m p q then (u m q - u m p) else 0) := by
  show (∑ m, Dm E m (u m)) p q = _
  rw [C1_sum_apply]
  refine Finset.sum_congr rfl fun m _ => ?_
  show (if (mGraph E m).Adj p q then (1 : ℝ) else 0) * (u m q - u m p) = _
  change (if MComparable E m p q then (1 : ℝ) else 0) * (u m q - u m p) = _
  split_ifs <;> simp

theorem harmonicGames_adj (u : Games E) (hu : u ∈ harmonicGames E) :
    LinearMap.adjoint (delta0 (gameGraph E)) (Dop E u) = 0 := by
  have : harmonicGames E ≤
      (LinearMap.ker (LinearMap.adjoint (delta0 (gameGraph E)))).comap (Dop E) := by
    refine sup_le inf_le_right ?_
    intro v hv
    have hv' : Dop E v = 0 := hv
    simp [hv']
  exact this hu

theorem line_sum (g : (∀ k, E k) → ℝ) (m : ι) (p : ∀ k, E k) :
    ∑ q, (if MComparable E m p q then g q - g p else 0) =
      ∑ a : E m, (g (Function.update p m a) - g p) := by
  rw [← Finset.sum_filter]
  rw [← Finset.sum_filter_of_ne (s := (Finset.univ : Finset (E m)))
    (p := fun a => a ≠ p m) (f := fun a => g (Function.update p m a) - g p)
    (fun a _ ha hap => ha (by rw [hap]; simp))]
  refine Finset.sum_nbij' (fun q => q m) (fun a => Function.update p m a) ?_ ?_ ?_ ?_ ?_
  · intro q hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
    intro h
    apply hq.1
    funext k
    by_cases hk : k = m
    · subst hk; exact h.symm
    · exact hq.2 k hk
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    refine ⟨fun h => ha ?_, fun k hk => ?_⟩
    · have := congrFun h m
      simpa using this.symm
    · simp [Function.update_of_ne hk]
  · intro q hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
    funext k
    by_cases hk : k = m
    · subst hk; simp
    · simp [Function.update_of_ne hk, hq.2 k hk]
  · intro a _
    simp
  · intro q hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
    have : Function.update p m (q m) = q := by
      funext k
      by_cases hk : k = m
      · subst hk; simp
      · simp [Function.update_of_ne hk, hq.2 k hk]
    rw [this]

theorem div_zero (u : Games E) (hu : u ∈ harmonicGames E) (p : ∀ k, E k) :
    ∑ m, ∑ a : E m, (u m (Function.update p m a) - u m p) = 0 := by
  have h := div_free (gameGraph E) (Dop E u) (harmonicGames_adj E u hu) p
  simp only [Dop_apply] at h
  rw [Finset.sum_comm] at h
  rw [← h]
  refine Finset.sum_congr rfl fun m _ => ?_
  exact (line_sum E (fun q => u m q) m p).symm

theorem ce_sum_zero (u : Games E) (hu : u ∈ harmonicGames E) (x : (∀ k, E k) → ℝ) :
    ∑ m, ∑ a : E m, ∑ b : E m, ∑ p ∈ Finset.univ.filter (fun p : ∀ k, E k => p m = a),
      (u m p - u m (Function.update p m b)) * x p = 0 := by
  have h1 : ∀ m, ∑ a : E m, ∑ b : E m, ∑ p ∈ Finset.univ.filter (fun p : ∀ k, E k => p m = a),
      (u m p - u m (Function.update p m b)) * x p =
      ∑ p, x p * ∑ b : E m, (u m p - u m (Function.update p m b)) := by
    intro m
    calc _ = ∑ b : E m, ∑ a : E m, ∑ p ∈ Finset.univ.filter (fun p : ∀ k, E k => p m = a),
          (u m p - u m (Function.update p m b)) * x p := Finset.sum_comm
      _ = ∑ b : E m, ∑ p, (u m p - u m (Function.update p m b)) * x p :=
          Finset.sum_congr rfl (fun b _ => Finset.sum_fiberwise Finset.univ (fun p => p m)
            (fun p => (u m p - u m (Function.update p m b)) * x p))
      _ = ∑ p, ∑ b : E m, (u m p - u m (Function.update p m b)) * x p := Finset.sum_comm
      _ = ∑ p, x p * ∑ b : E m, (u m p - u m (Function.update p m b)) := by
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun b _ => by ring)
  simp only [h1]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun p _ => ?_
  rw [← Finset.mul_sum]
  have := div_zero E u hu p
  have e : ∑ m, ∑ b : E m, (u m p - u m (Function.update p m b)) =
      - ∑ m, ∑ a : E m, (u m (Function.update p m a) - u m p) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun b _ => by ring
  rw [e, this]; simp

theorem pinv_mem_orth {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ V]
    [FiniteDimensional ℝ W] (L : V →ₗ[ℝ] W) (y : W) : pinv L y ∈ (LinearMap.ker L)ᗮ :=
  Submodule.coe_mem _

theorem nu_mem_ker (m : ι) (p : ∀ k, E k) :
    nu E m (fun k : {k : ι // k ≠ m} => p k.1) ∈ LinearMap.ker (Dm E m) := by
  rw [LinearMap.mem_ker]
  apply C1.ext
  intro p' q'
  show (if (mGraph E m).Adj p' q' then (1 : ℝ) else 0) *
    (nu E m (fun k : {k : ι // k ≠ m} => p k.1) q' - nu E m (fun k : {k : ι // k ≠ m} => p k.1) p')
    = 0
  by_cases h : (mGraph E m).Adj p' q'
  · have h2 : ∀ k, k ≠ m → p' k = q' k := h.2
    have : nu E m (fun k : {k : ι // k ≠ m} => p k.1) q' =
        nu E m (fun k : {k : ι // k ≠ m} => p k.1) p' := by
      unfold nu
      simp only
      congr 1
      apply propext
      constructor
      · intro hq k hk; rw [h2 k hk]; exact hq k hk
      · intro hq k hk; rw [← h2 k hk]; exact hq k hk
    rw [this]; simp
  · simp [h]

theorem sum_line (f : (∀ k, E k) → ℝ) (m : ι) (p : ∀ k, E k) :
    ∑ q, (if ∀ k, k ≠ m → q k = p k then f q else 0) = ∑ a : E m, f (Function.update p m a) := by
  rw [← Finset.sum_filter]
  refine Finset.sum_nbij' (fun q => q m) (fun a => Function.update p m a) ?_ ?_ ?_ ?_ ?_
  · intro q _; exact Finset.mem_univ _
  · intro a _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro k hk; simp [Function.update_of_ne hk]
  · intro q hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
    funext k
    by_cases hk : k = m
    · subst hk; simp
    · simp [Function.update_of_ne hk, hq k hk]
  · intro a _; simp
  · intro q hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
    have : Function.update p m (q m) = q := by
      funext k
      by_cases hk : k = m
      · subst hk; simp
      · simp [Function.update_of_ne hk, hq k hk]
    rw [this]

theorem normalized (u : Games E) (hu : u ∈ HarmonicGames.Decomposition.harmonicSubspace E) (m : ι) (p : ∀ k, E k) :
    ∑ a : E m, u m (Function.update p m a) = 0 := by
  have hid : u = PiOp E u := (LinearMap.mem_eqLocus.1 hu.1)
  have hm : u m = Pim E m (u m) := congrArg (fun v : Games E => v m) hid
  have hmem : u m ∈ (LinearMap.ker (Dm E m))ᗮ := by
    rw [hm]
    exact pinv_mem_orth (Dm E m) (Dm E m (u m))
  have h0 := Submodule.inner_right_of_mem_orthogonal (nu_mem_ker E m p) hmem
  simp only [nu, PiLp.inner_apply, RCLike.inner_apply, conj_trivial, mul_ite, mul_one,
    mul_zero] at h0
  rw [← h0]
  exact (sum_line E (fun q => (u m).ofLp q) m p).symm

-- BEGIN_CE
theorem ce_iff (u : Games E) (hu : u ∈ HarmonicGames.GenericPure.harmonicGames E)
    (x : (∀ k, E k) → ℝ) (hx : AGT.IsLottery x) :
    HartSchmeidler.Finite.IsCorrelatedEq (HarmonicGames.GenericPure.payoff E u) x ↔
      ∀ (m : ι) (a b : E m),
        ∑ p ∈ Finset.univ.filter (fun p : ∀ k, E k => p m = a),
          (HarmonicGames.GenericPure.payoff E u m p -
            HarmonicGames.GenericPure.payoff E u m (Function.update p m b)) * x p = 0 := by
  have hsum := ce_sum_zero E u hu x
  constructor
  · rintro ⟨_, hce⟩
    have hnn : ∀ (m : ι) (a b : E m), 0 ≤ ∑ p ∈ Finset.univ.filter (fun p : ∀ k, E k => p m = a),
        (u m p - u m (Function.update p m b)) * x p := by
      intro m a b
      have := hce m a b
      refine le_of_le_of_eq this (Finset.sum_congr rfl fun p _ => ?_)
      show x p * (u m p - u m (Function.update p m b)) = _
      ring
    intro m a b
    have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun m _ => Finset.sum_nonneg (fun a _ =>
      Finset.sum_nonneg (fun b _ => hnn m a b)))).1 hsum m (Finset.mem_univ _)
    have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun a _ =>
      Finset.sum_nonneg (fun b _ => hnn m a b))).1 h1 a (Finset.mem_univ _)
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun b _ => hnn m a b)).1 h2 b (Finset.mem_univ _)
  · intro h
    refine ⟨hx, fun m a b => ?_⟩
    have := h m a b
    refine (le_of_eq this.symm).trans (le_of_eq (Finset.sum_congr rfl fun p _ => ?_))
    exact mul_comm _ _

-- END_CE

end

end GTHarm

theorem solution {ι : Type} [Fintype ι] [DecidableEq ι] (E : ι → Type)
    [∀ m, Fintype (E m)] [∀ m, DecidableEq (E m)] [∀ m, Nonempty (E m)]
    (u : HarmonicGames.Decomposition.Games E) (hu : u ∈ HarmonicGames.Decomposition.harmonicSubspace E) (x : (∀ k, E k) → ℝ) (hx : AGT.IsLottery x) :
    (HartSchmeidler.Finite.IsCorrelatedEq (HarmonicGames.GenericPure.payoff E u) x ↔
      ∀ (m : ι) (a b : E m),
        ∑ p ∈ Finset.univ.filter (fun p : ∀ k, E k => p m = a),
          (HarmonicGames.GenericPure.payoff E u m p - HarmonicGames.GenericPure.payoff E u m (Function.update p m b)) * x p = 0) ∧
    ((∀ (m : ι) (a b : E m),
        ∑ p ∈ Finset.univ.filter (fun p : ∀ k, E k => p m = a),
          (HarmonicGames.GenericPure.payoff E u m p - HarmonicGames.GenericPure.payoff E u m (Function.update p m b)) * x p = 0) ↔
      ∀ (m : ι) (a b : E m),
        ∑ p ∈ Finset.univ.filter (fun p : ∀ k, E k => p m = a),
          HarmonicGames.GenericPure.payoff E u m (Function.update p m b) * x p = 0) := by
  have huH : u ∈ HarmonicGames.GenericPure.harmonicGames E := Submodule.mem_sup_left hu
  refine ⟨GTHarm.ce_iff E u huH x hx, ?_⟩
  have hnorm := GTHarm.normalized E u hu
  simp only [HarmonicGames.GenericPure.payoff]
  -- S = V a
  have hSV : ∀ (m : ι) (a : E m),
      ∑ p ∈ Finset.univ.filter (fun p : ∀ k, E k => p m = a), u m p * x p =
      ∑ p ∈ Finset.univ.filter (fun p : ∀ k, E k => p m = a),
        u m (Function.update p m a) * x p := by
    intro m a
    refine Finset.sum_congr rfl fun p hp => ?_
    have hpa : p m = a := (Finset.mem_filter.1 hp).2
    rw [← hpa, Function.update_eq_self]
  have hdiff : ∀ (m : ι) (a b : E m),
      ∑ p ∈ Finset.univ.filter (fun p : ∀ k, E k => p m = a),
        (u m p - u m (Function.update p m b)) * x p =
      ∑ p ∈ Finset.univ.filter (fun p : ∀ k, E k => p m = a), u m p * x p -
      ∑ p ∈ Finset.univ.filter (fun p : ∀ k, E k => p m = a),
        u m (Function.update p m b) * x p := by
    intro m a b
    simp only [sub_mul, Finset.sum_sub_distrib]
  have hVsum : ∀ (m : ι) (a : E m),
      ∑ b : E m, ∑ p ∈ Finset.univ.filter (fun p : ∀ k, E k => p m = a),
        u m (Function.update p m b) * x p = 0 := by
    intro m a
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun p _ => ?_
    rw [← Finset.sum_mul]
    have := hnorm m p
    simp only [this, zero_mul]
  constructor
  · intro h m a b
    have h' : ∀ b', ∑ p ∈ Finset.univ.filter (fun p : ∀ k, E k => p m = a), u m p * x p =
        ∑ p ∈ Finset.univ.filter (fun p : ∀ k, E k => p m = a),
          u m (Function.update p m b') * x p := by
      intro b'
      have := h m a b'
      rw [hdiff] at this
      linarith
    have hS : ∑ p ∈ Finset.univ.filter (fun p : ∀ k, E k => p m = a), u m p * x p = 0 := by
      have hc : (0 : ℝ) < (Fintype.card (E m) : ℝ) := by exact_mod_cast Fintype.card_pos
      have := hVsum m a
      rw [Finset.sum_congr rfl (fun b' _ => (h' b').symm), Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul] at this
      exact (mul_eq_zero.1 this).resolve_left hc.ne'
    rw [← h' b]; exact hS
  · intro h m a b
    rw [hdiff]
    have h1 := h m a b
    have h2 := h m a a
    rw [hSV m a, h2, h1]; simp
