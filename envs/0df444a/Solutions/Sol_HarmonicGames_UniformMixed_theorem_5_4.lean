-- Prove2me | solution 1 for HarmonicGames.UniformMixed.theorem_5_4
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-21T16:58:23.737969+00:00
-- url     : https://prove2.me/submissions/ea2982de-6c90-431f-9f99-19e4555a9e17

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_HarmonicGames_Decomposition_Games
import Definitions.Def_HarmonicGames_GenericPure_Games
import Definitions.Def_HarmonicGames_UniformMixed_Mixed

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace P9ed4e719

open HarmonicGames.Decomposition
open scoped InnerProductSpace

section Graph
variable {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

lemma C1_sum_apply {α : Type*} (s : Finset α) (f : α → C1 G) (a b : V) :
    (∑ m ∈ s, f m) a b = ∑ m ∈ s, f m a b := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih => rw [Finset.sum_insert hx, Finset.sum_insert hx, C1.add_apply, ih]

lemma inner_delta0 (φ : C0 V) (X : C1 G) :
    ⟪delta0 G φ, X⟫_ℝ = -∑ a, φ a * ∑ b, X a b := by
  have h0 : ⟪delta0 G φ, X⟫_ℝ = innerC1 G (delta0 G φ) X := rfl
  have hterm : ∀ a b, (if G.Adj a b then delta0 G φ a b * X a b else 0) =
      (φ b - φ a) * X a b := by
    intro a b
    by_cases h : G.Adj a b
    · rw [if_pos h]
      show ((if G.Adj a b then (1:ℝ) else 0) * (φ b - φ a)) * X a b = _
      rw [if_pos h, one_mul]
    · rw [if_neg h, C1.eq_zero_of_not_adj G X h, mul_zero]
  have hanti : ∀ a b, X b a = - X a b := by
    intro a b
    by_cases h : G.Adj a b
    · exact C1.antisymm G X h
    · rw [C1.eq_zero_of_not_adj G X h, C1.eq_zero_of_not_adj G X (fun h' => h h'.symm), neg_zero]
  rw [h0, innerC1]
  simp_rw [hterm, sub_mul, Finset.sum_sub_distrib]
  have h1 : ∑ a, ∑ b, φ b * X a b = -∑ a, ∑ b, φ a * X a b := by
    rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [hanti a b]; ring
  rw [h1]
  simp_rw [Finset.mul_sum]
  ring

lemma mem_ker_adjoint_iff (X : C1 G) :
    X ∈ LinearMap.ker (LinearMap.adjoint (delta0 G)) ↔ ∀ a, ∑ b, X a b = 0 := by
  constructor
  · intro hX a
    classical
    have := LinearMap.adjoint_inner_right (delta0 G) (EuclideanSpace.single a (1:ℝ)) X
    rw [LinearMap.mem_ker.1 hX, inner_zero_right, inner_delta0] at this
    simpa [PiLp.single_apply] using this.symm
  · intro h
    rw [LinearMap.mem_ker]
    refine ext_inner_left ℝ fun φ => ?_
    rw [LinearMap.adjoint_inner_right, inner_delta0, inner_zero_right]
    simp [h]

end Graph

section Split
variable {ι : Type} [Fintype ι] [DecidableEq ι] {E : ι → Type} [∀ m, Fintype (E m)]
  [∀ m, DecidableEq (E m)]

lemma S_self (k : ι) (b : E k) (r : ∀ j : {j // j ≠ k}, E j) :
    (Equiv.piSplitAt k E).symm (b, r) k = b := by
  simp [Equiv.piSplitAt_symm_apply]

lemma S_ne (k : ι) (b : E k) (r : ∀ j : {j // j ≠ k}, E j) (j : ι) (hj : j ≠ k) :
    (Equiv.piSplitAt k E).symm (b, r) j = r ⟨j, hj⟩ := by
  simp [Equiv.piSplitAt_symm_apply, hj]

lemma S_update (k : ι) (b c : E k) (r : ∀ j : {j // j ≠ k}, E j) :
    Function.update ((Equiv.piSplitAt k E).symm (b, r)) k c = (Equiv.piSplitAt k E).symm (c, r) := by
  funext j
  by_cases hj : j = k
  · subst hj; rw [Function.update_self, S_self]
  · rw [Function.update_of_ne hj, S_ne k b r j hj, S_ne k c r j hj]

lemma sum_split (k : ι) (f : (∀ j, E j) → ℝ) :
    ∑ p, f p = ∑ b : E k, ∑ r : (∀ j : {j // j ≠ k}, E j), f ((Equiv.piSplitAt k E).symm (b, r)) := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv (Equiv.piSplitAt k E) _ _ (fun p => (congrArg f ((Equiv.piSplitAt k E).symm_apply_apply p)).symm)).trans rfl

lemma sum_sub_sum {α : Type} [Fintype α] (g : α → ℝ) : ∑ b : α, ∑ c : α, (g c - g b) = 0 := by
  simp_rw [Finset.sum_sub_distrib]
  rw [Finset.sum_comm (f := fun _ c => g c)]
  simp

/-- The averaged identity: summing the divergence-free condition over the profiles with
`p m = a` leaves `T - h_m F(a) = 0`. -/
lemma key (v : ι → (∀ k, E k) → ℝ)
    (hdiv : ∀ p, ∑ k, ∑ c : E k, (v k (Function.update p k c) - v k p) = 0) (m : ι) (a : E m) :
    (Fintype.card (E m) : ℝ) * ∑ p, (if p m = a then v m p else 0) = ∑ p, v m p := by
  have h0 : ∑ p : (∀ k, E k), (if p m = a then (1:ℝ) else 0) *
      ∑ k, ∑ c : E k, (v k (Function.update p k c) - v k p) = 0 := by
    simp only [hdiv, mul_zero, Finset.sum_const_zero]
  simp_rw [Finset.mul_sum (s := (Finset.univ : Finset ι))] at h0
  rw [Finset.sum_comm] at h0
  rw [Finset.sum_eq_single m] at h0
  · rw [sum_split m] at h0
    rw [sum_split m (fun p => if p m = a then v m p else 0), sum_split m (fun p => v m p)]
    simp only [S_self, S_update] at h0 ⊢
    have h1 : ∀ b : E m, ∀ r : (∀ j : {j // j ≠ m}, E j),
        (if b = a then (1:ℝ) else 0) * ∑ c : E m,
          (v m ((Equiv.piSplitAt m E).symm (c, r)) - v m ((Equiv.piSplitAt m E).symm (b, r))) =
        if b = a then ∑ c : E m,
          (v m ((Equiv.piSplitAt m E).symm (c, r)) - v m ((Equiv.piSplitAt m E).symm (a, r)))
        else 0 := by
      intro b r; split_ifs with h
      · subst h; rw [one_mul]
      · rw [zero_mul]
    simp only [h1] at h0
    rw [Finset.sum_comm] at h0
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true] at h0
    rw [Finset.sum_comm (f := fun b r => if b = a then _ else 0)]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
    simp_rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h0
    rw [Finset.sum_comm (f := fun b r => v m ((Equiv.piSplitAt m E).symm (b, r))), Finset.mul_sum]
    linarith
  · intro k _ hk
    rw [sum_split k]
    have hS : ∀ (b : E k) (r : ∀ j : {j // j ≠ k}, E j),
        (Equiv.piSplitAt k E).symm (b, r) m = r ⟨m, Ne.symm hk⟩ :=
      fun b r => S_ne k b r m (Ne.symm hk)
    simp only [hS, S_update]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun r _ => ?_
    rw [← Finset.mul_sum, sum_sub_sum (fun c => v k ((Equiv.piSplitAt k E).symm (c, r))), mul_zero]
  · simp

end Split


section Games
variable {ι : Type} [Fintype ι] [DecidableEq ι] (E : ι → Type) [∀ m, Fintype (E m)]
  [∀ m, DecidableEq (E m)]

lemma Dop_apply (u : Games E) (a b : ∀ k, E k) :
    (Dop E u) a b = ∑ m, (if MComparable E m a b then (1:ℝ) else 0) * (u m b - u m a) := by
  show (∑ m, Dm E m (u m)) a b = _
  rw [C1_sum_apply]
  rfl

lemma div_of_mem (v : Games E) (hv : v ∈ HarmonicGames.GenericPure.harmonicGames E)
    (a : ∀ k, E k) :
    ∑ b, ∑ m, (if MComparable E m a b then (1:ℝ) else 0) * (v m b - v m a) = 0 := by
  obtain ⟨h, hh, n, hn, rfl⟩ := Submodule.mem_sup.1 hv
  have hD : Dop E (h + n) = Dop E h := by
    rw [map_add, LinearMap.mem_ker.1 hn, add_zero]
  have hk : Dop E h ∈ LinearMap.ker (LinearMap.adjoint (delta0 (gameGraph E))) :=
    Submodule.mem_comap.1 hh.2
  rw [← hD] at hk
  have := (mem_ker_adjoint_iff _ _).1 hk a
  simpa only [Dop_apply] using this


lemma sum_mcomp (m : ι) (f : (∀ k, E k) → ℝ) (a : ∀ k, E k) :
    ∑ b, (if MComparable E m a b then (1:ℝ) else 0) * (f b - f a) =
      ∑ c : E m, (f (Function.update a m c) - f a) := by
  have himg : ∑ c : E m, (f (Function.update a m c) - f a) =
      ∑ b ∈ Finset.univ.image (fun c => Function.update a m c), (f b - f a) := by
    rw [Finset.sum_image]
    intro x _ y _ hxy
    exact Function.update_injective a m hxy
  rw [himg, ← Finset.sum_subset (Finset.subset_univ
    (Finset.univ.image fun c => Function.update a m c))]
  · refine Finset.sum_congr rfl fun b hb => ?_
    obtain ⟨c, _, rfl⟩ := Finset.mem_image.1 hb
    split_ifs with hc
    · ring
    · have : Function.update a m c = a := by
        by_contra hne'
        exact hc ⟨fun e => hne' e.symm, fun k hk => (Function.update_of_ne hk c a).symm⟩
      rw [this]; ring
  · intro b _ hb
    split_ifs with hc
    · exfalso
      apply hb
      refine Finset.mem_image.2 ⟨b m, Finset.mem_univ _, ?_⟩
      funext k
      by_cases hk : k = m
      · subst hk; simp
      · rw [Function.update_of_ne hk]; exact hc.2 k hk
    · ring

end Games

end P9ed4e719

open HarmonicGames.UniformMixed in
theorem solution {ι : Type} [Fintype ι] [DecidableEq ι] (E : ι → Type)
    [∀ m, Fintype (E m)] [∀ m, DecidableEq (E m)] [∀ m, Nonempty (E m)]
    (u : HarmonicGames.Decomposition.Games E) (hu : u ∈ HarmonicGames.GenericPure.harmonicGames E) :
    IsMixedNashEquilibrium (HarmonicGames.GenericPure.payoff E u) (uniformProfile E) := by
  set v := HarmonicGames.GenericPure.payoff E u with hv
  have hdiv : ∀ p, ∑ k, ∑ c : E k, (v k (Function.update p k c) - v k p) = 0 := by
    intro p
    have h := P9ed4e719.div_of_mem E u hu p
    rw [Finset.sum_comm] at h
    simp_rw [P9ed4e719.sum_mcomp E _ (fun b => u _ b) p] at h
    exact h
  have hcard : ∀ k, (0:ℝ) < (Fintype.card (E k) : ℝ) := fun k =>
    Nat.cast_pos.2 Fintype.card_pos
  refine ⟨fun k => ⟨fun b => ?_, ?_⟩, fun m a => ?_⟩
  · show (0:ℝ) ≤ 1 / (Fintype.card (E k) : ℝ)
    exact le_of_lt (one_div_pos.2 (hcard k))
  · show ∑ b : E k, 1 / (Fintype.card (E k) : ℝ) = 1
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp [(hcard k).ne']
  · set Q : ℝ := ∏ k ∈ Finset.univ.erase m, 1 / (Fintype.card (E k) : ℝ) with hQ
    have hP : ∀ s : (∀ k, E k), AGT.profileProb (uniformProfile E) s =
        1 / (Fintype.card (E m) : ℝ) * Q := by
      intro s
      unfold AGT.profileProb
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ m)]
      rfl
    have hP' : ∀ s : (∀ k, E k), AGT.profileProb
        (Function.update (uniformProfile E) m (pureLottery a)) s =
        (if s m = a then (1:ℝ) else 0) * Q := by
      intro s
      unfold AGT.profileProb
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ m)]
      congr 1
      · simp [pureLottery]
      · refine Finset.prod_congr rfl fun k hk => ?_
        rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]
        rfl
    have hk := P9ed4e719.key v hdiv m a
    unfold mixedVsPure AGT.expectedPayoff
    simp_rw [hP, hP']
    have eL : ∑ s : (∀ k, E k), (if s m = a then (1:ℝ) else 0) * Q * v m s =
        Q * ∑ s : (∀ k, E k), (if s m = a then v m s else 0) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun s _ => ?_
      split_ifs <;> ring
    have eR : ∑ s : (∀ k, E k), 1 / (Fintype.card (E m) : ℝ) * Q * v m s =
        1 / (Fintype.card (E m) : ℝ) * Q * ∑ s : (∀ k, E k), v m s := by
      rw [Finset.mul_sum]
    rw [eL, eR, ← hk]
    apply le_of_eq
    field_simp [(hcard m).ne']
