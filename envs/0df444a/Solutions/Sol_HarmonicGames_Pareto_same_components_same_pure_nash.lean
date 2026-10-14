-- Prove2me | solution 1 for HarmonicGames.Pareto.same_components_same_pure_nash
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-13T03:25:11.446287+00:00
-- url     : https://prove2.me/submissions/794602fc-ea50-46ec-8151-97b9b310ab38

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_HarmonicGames_Pareto_Games

open HarmonicGames.Decomposition HarmonicGames.GenericPure HarmonicGames.Pareto

private theorem recover {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    [FiniteDimensional ℝ V] [FiniteDimensional ℝ W] (L : V →ₗ[ℝ] W) (x : V) :
    L (HarmonicGames.Decomposition.pinv L (L x)) = L x := by
  obtain ⟨y,hy,z,hz,rfl⟩ := (LinearMap.ker L).exists_add_mem_mem_orthogonal x
  have hy' : L y = 0 := hy
  simp only [map_add, hy', zero_add]
  let R := L ∘ₗ (LinearMap.ker L)ᗮ.subtype
  let e := LinearEquiv.ofInjective R (HarmonicGames.Decomposition.pinv_restrict_injective L)
  have hp : (LinearMap.range R).orthogonalProjectionOnto (L z) = e ⟨z,hz⟩ :=
    (LinearMap.range R).orthogonalProjectionOnto_mem_subspace_eq_self (e ⟨z,hz⟩)
  change L ((e.symm ((LinearMap.range R).orthogonalProjectionOnto (L z)) :
    (LinearMap.ker L)ᗮ) : V) = L z
  rw [hp]
  simp

private theorem flow_change {ι : Type} [Fintype ι] [DecidableEq ι] (E : ι → Type)
    [∀ m, Fintype (E m)] [∀ m, DecidableEq (E m)]
    (u : Games E) (p : ∀ m, E m) (m : ι) (a : E m) :
    Dop E u p (Function.update p m a) = u m (Function.update p m a)-u m p := by
  classical
  by_cases heq : Function.update p m a = p
  · rw [heq, sub_self]
    exact HarmonicGames.Decomposition.C1.eq_zero_of_not_adj _ _ (SimpleGraph.irrefl _)
  have hm : MComparable E m p (Function.update p m a) := by
    refine ⟨Ne.symm heq, ?_⟩
    intro k hk
    simp [Function.update_of_ne hk]
  have hn (k : ι) (hk : k ≠ m) : ¬ MComparable E k p (Function.update p m a) := by
    intro h
    have hv := h.2 m (Ne.symm hk)
    simp only [Function.update_self] at hv
    apply heq
    rw [← hv, Function.update_eq_self]
  have hev (s : Finset ι) (z : ι → Flow E) (q : ∀ m, E m) :
      (∑ k ∈ s, z k) p q = ∑ k ∈ s, z k p q := by
    induction s using Finset.induction_on with
    | empty => rfl
    | @insert k s hk ih => simp only [Finset.sum_insert hk, HarmonicGames.Decomposition.C1.add_apply, ih]
  change (∑ k, Dm E k (u k)) p _ = _
  rw [hev]
  rw [Finset.sum_eq_single m]
  · simp [Dm, HarmonicGames.Decomposition.gradOn, mGraph, hm]
  · intro k hk hkm
    simp [Dm, HarmonicGames.Decomposition.gradOn, mGraph, hn k hkm]
  · simp

theorem solution {ι : Type} [Fintype ι] [DecidableEq ι] (E : ι → Type)
    [∀ m, Fintype (E m)] [∀ m, DecidableEq (E m)] [∀ m, Nonempty (E m)]
    (u v : HarmonicGames.Decomposition.Games E) (hP : HarmonicGames.Decomposition.potentialComponent E u = HarmonicGames.Decomposition.potentialComponent E v)
    (hH : HarmonicGames.Decomposition.harmonicComponent E u = HarmonicGames.Decomposition.harmonicComponent E v) (p : ∀ m, E m) :
    AGT.IsPureNash (HarmonicGames.GenericPure.payoff E u) p ↔ AGT.IsPureNash (HarmonicGames.GenericPure.payoff E v) p := by
  have hsum (w : Games E) : potentialComponent E w + harmonicComponent E w =
      HarmonicGames.Decomposition.pinv (Dop E) (Dop E w) := by
    simp only [potentialComponent, harmonicComponent, LinearMap.comp_apply,
      LinearMap.sub_apply, LinearMap.id_apply, map_sub]
    abel
  have he : HarmonicGames.Decomposition.pinv (Dop E) (Dop E u) =
      HarmonicGames.Decomposition.pinv (Dop E) (Dop E v) := by
    rw [← hsum u, ← hsum v, hP,hH]
  have hd : Dop E u = Dop E v := by
    have h := congrArg (Dop E) he
    simpa only [recover] using h
  have hc (m : ι) (a : E m) :
      u m (Function.update p m a)-u m p = v m (Function.update p m a)-v m p := by
    rw [← flow_change E u p m a, ← flow_change E v p m a, hd]
  constructor <;> intro h m a
  · have hh := h m a
    change u m (Function.update p m a) ≤ u m p at hh
    change v m (Function.update p m a) ≤ v m p
    linarith [hc m a]
  · have hh := h m a
    change v m (Function.update p m a) ≤ v m p at hh
    change u m (Function.update p m a) ≤ u m p
    linarith [hc m a]
