-- Prove2me | solution 1 for HarmonicGames.UniformMixed.corollary_5_2
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-04T11:41:40.112497+00:00
-- url     : https://prove2.me/submissions/acb0d53e-395a-4fb6-b5a9-704f7659c47f

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_HarmonicGames_Decomposition_Games
import Definitions.Def_HarmonicGames_GenericPure_Games
import Definitions.Def_HarmonicGames_UniformMixed_Mixed


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


-- BEGIN_MIXED
def Rr (x : ∀ k, E k → ℝ) (m : ι) (p : ∀ k, E k) : ℝ := ∏ k ∈ Finset.univ.erase m, x k (p k)

theorem pp_split (x : ∀ k, E k → ℝ) (m : ι) (p : ∀ k, E k) :
    AGT.profileProb x p = x m (p m) * Rr E x m p := by
  unfold AGT.profileProb Rr
  rw [Finset.mul_prod_erase Finset.univ (fun k => x k (p k)) (Finset.mem_univ m)]

theorem Rr_update (x : ∀ k, E k → ℝ) (m : ι) (p : ∀ k, E k) (b : E m) :
    Rr E x m (Function.update p m b) = Rr E x m p := by
  unfold Rr
  refine Finset.prod_congr rfl fun k hk => ?_
  have : k ≠ m := Finset.ne_of_mem_erase hk
  simp [Function.update_of_ne this]

theorem Rr_upd_prof (x : ∀ k, E k → ℝ) (m : ι) (τ : E m → ℝ) (p : ∀ k, E k) :
    Rr E (Function.update x m τ) m p = Rr E x m p := by
  unfold Rr
  refine Finset.prod_congr rfl fun k hk => ?_
  have : k ≠ m := Finset.ne_of_mem_erase hk
  simp [Function.update_of_ne this]

theorem pp_update (x : ∀ k, E k → ℝ) (m : ι) (a : E m) (p : ∀ k, E k) :
    AGT.profileProb (Function.update x m (HarmonicGames.UniformMixed.pureLottery a)) p =
      (if p m = a then 1 else 0) * Rr E x m p := by
  rw [pp_split E _ m p, Rr_upd_prof]
  simp [HarmonicGames.UniformMixed.pureLottery]

theorem Z (u : ι → (∀ k, E k) → ℝ) (x : ∀ k, E k → ℝ) (hx : ∀ k, AGT.IsLottery (x k))
    (m : ι) (a : E m) :
    ∑ p, AGT.profileProb x p * u m (Function.update p m a) =
      HarmonicGames.UniformMixed.mixedVsPure u x m a := by
  unfold HarmonicGames.UniformMixed.mixedVsPure AGT.expectedPayoff
  simp only [pp_update]
  have L : ∑ p, AGT.profileProb x p * u m (Function.update p m a) =
      ∑ p, x m (p m) * (Rr E x m (Function.update p m a) * u m (Function.update p m a)) := by
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [pp_split E x m p, Rr_update]; ring
  have M : ∑ p : ∀ k, E k, x m (p m) *
      (Rr E x m (Function.update p m a) * u m (Function.update p m a)) =
      ∑ bq ∈ (Finset.univ : Finset (E m)) ×ˢ
        (Finset.univ.filter (fun q : ∀ k, E k => q m = a)),
        x m bq.1 * (Rr E x m bq.2 * u m bq.2) := by
    refine Finset.sum_nbij' (fun p => (p m, Function.update p m a))
      (fun bq => Function.update bq.2 m bq.1) ?_ ?_ ?_ ?_ ?_
    · intro p _
      simp
    · intro bq _; exact Finset.mem_univ _
    · intro p _
      simp
    · intro bq hbq
      simp only [Finset.mem_product, Finset.mem_univ, Finset.mem_filter, true_and] at hbq
      ext
      · simp
      · simp [← hbq]
    · intro p _
      simp
  rw [L, M, Finset.sum_product]
  dsimp only
  rw [← Finset.sum_mul_sum, (hx m).2, one_mul]
  simp only [ite_mul, one_mul, zero_mul]
  rw [← Finset.sum_filter]

theorem mixed_sum_zero (u : Games E) (hu : u ∈ harmonicGames E) (x : ∀ k, E k → ℝ)
    (hx : ∀ k, AGT.IsLottery (x k)) :
    ∑ m, ∑ a : E m, (HarmonicGames.UniformMixed.mixedVsPure (payoff E u) x m a -
      AGT.expectedPayoff (payoff E u) x m) = 0 := by
  have per : ∀ m : ι, ∑ a : E m, (HarmonicGames.UniformMixed.mixedVsPure (payoff E u) x m a -
      AGT.expectedPayoff (payoff E u) x m) =
      ∑ p, AGT.profileProb x p * ∑ a : E m,
        (payoff E u m (Function.update p m a) - payoff E u m p) := by
    intro m
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Z E (payoff E u) x hx m a]
    unfold AGT.expectedPayoff
    simp only [mul_sub, Finset.sum_sub_distrib]
  simp only [per]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun p _ => ?_
  rw [← Finset.mul_sum]
  have h : ∑ m, ∑ a : E m, (payoff E u m (Function.update p m a) - payoff E u m p) = 0 :=
    div_zero E u hu p
  rw [h, mul_zero]

-- END_MIXED
end

end GTHarm

open HarmonicGames.UniformMixed in
theorem solution {ι : Type} [Fintype ι] [DecidableEq ι] (E : ι → Type)
    [∀ m, Fintype (E m)] [∀ m, DecidableEq (E m)] [∀ m, Nonempty (E m)]
    (u : HarmonicGames.Decomposition.Games E) (hu : u ∈ HarmonicGames.GenericPure.harmonicGames E) (x : ∀ m, E m → ℝ) (hx : AGT.IsMixedProfile x) :
    IsMixedNashEquilibrium (HarmonicGames.GenericPure.payoff E u) x ↔
      ∀ (m : ι) (a : E m), AGT.expectedPayoff (HarmonicGames.GenericPure.payoff E u) x m = mixedVsPure (HarmonicGames.GenericPure.payoff E u) x m a := by
  have hlot : ∀ k, AGT.IsLottery (x k) := hx
  have hsum := GTHarm.mixed_sum_zero E u hu x hlot
  constructor
  · rintro ⟨_, hne⟩ m a
    have hle : ∀ (m : ι) (a : E m), mixedVsPure (HarmonicGames.GenericPure.payoff E u) x m a -
        AGT.expectedPayoff (HarmonicGames.GenericPure.payoff E u) x m ≤ 0 :=
      fun m a => sub_nonpos.2 (hne m a)
    have h1 := (Finset.sum_eq_zero_iff_of_nonpos (fun m _ =>
      Finset.sum_nonpos fun a _ => hle m a)).1 hsum m (Finset.mem_univ _)
    have h2 := (Finset.sum_eq_zero_iff_of_nonpos (fun a _ => hle m a)).1 h1 a (Finset.mem_univ _)
    linarith
  · intro h
    exact ⟨hx, fun m a => le_of_eq (h m a).symm⟩
