-- Prove2me | solution 1 for HarmonicGames.Projection.theorem_5_1
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-10T08:05:44.079304+00:00
-- url     : https://prove2.me/submissions/70d2379c-3740-4440-94ca-fcf3f32c29eb

import Mathlib
import Definitions.Def_HarmonicGames_Projection_Closest
import Theorems.Thm_HarmonicGames_Decomposition_theorem_4_1

open HarmonicGames.Decomposition

section Aux

private lemma pinv_right {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ V]
    [FiniteDimensional ℝ W] (L : V →ₗ[ℝ] W) (y : W) (hy : y ∈ LinearMap.range L) :
    L (pinv L y) = y := by
  have hrange : LinearMap.range (L ∘ₗ (LinearMap.ker L)ᗮ.subtype) = LinearMap.range L := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩; exact ⟨x, rfl⟩
    · rintro _ ⟨x, rfl⟩
      have hx : x ∈ LinearMap.ker L ⊔ (LinearMap.ker L)ᗮ := by
        rw [Submodule.sup_orthogonal_of_hasOrthogonalProjection]; trivial
      obtain ⟨x1, hx1, x2, hx2, rfl⟩ := Submodule.mem_sup.1 hx
      refine ⟨⟨x2, hx2⟩, ?_⟩
      simp [LinearMap.mem_ker.1 hx1]
  have hy' : y ∈ LinearMap.range (L ∘ₗ (LinearMap.ker L)ᗮ.subtype) := hrange ▸ hy
  have hz : (LinearMap.range (L ∘ₗ (LinearMap.ker L)ᗮ.subtype)).orthogonalProjectionOnto y =
      ⟨y, hy'⟩ := Submodule.orthogonalProjectionOnto_mem_subspace_eq_self ⟨y, hy'⟩
  have h1 := (LinearEquiv.ofInjective (L ∘ₗ (LinearMap.ker L)ᗮ.subtype)
    (pinv_restrict_injective L)).apply_symm_apply ⟨y, hy'⟩
  have h2 := congrArg Subtype.val h1
  rw [LinearEquiv.ofInjective_apply] at h2
  unfold pinv
  simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe, hz]
  exact h2

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

private lemma delta0_update (φ : Util E) (m : ι) (p : ∀ k, E k) (x : E m) :
    (delta0 (gameGraph E) φ) p (Function.update p m x) =
      φ (Function.update p m x) - φ p := by
  show (if (gameGraph E).Adj p (Function.update p m x) then (1 : ℝ) else 0) *
    (φ (Function.update p m x) - φ p) = _
  by_cases h : Function.update p m x = p
  · rw [h]; simp
  · have hc : (gameGraph E).Adj p (Function.update p m x) :=
      ⟨m, fun e => h e.symm, fun k hk => by simp [Function.update_of_ne hk]⟩
    rw [if_pos hc, one_mul]

end Aux

theorem solution {ι : Type} [Fintype ι] [DecidableEq ι] (E : ι → Type)
    [∀ m, Fintype (E m)] [∀ m, DecidableEq (E m)] [∀ m, Nonempty (E m)]
    (u : ι → (∀ m, E m) → ℝ) :
    MondererShapley.ClosedPath.IsPotentialGame u ↔
      HarmonicGames.Projection.toGames E u ∈ HarmonicGames.Decomposition.potentialSubspace E ⊔ HarmonicGames.Decomposition.nonstrategicSubspace E := by
  classical
  constructor
  · -- potential game ⇒ u ∈ P ⊕ N
    rintro ⟨P, hP⟩
    set U := HarmonicGames.Projection.toGames E u with hU
    have hD : Dop E U = delta0 (gameGraph E) (WithLp.toLp 2 P) := by
      ext p q
      by_cases hadj : (gameGraph E).Adj p q
      · obtain ⟨m, hm⟩ := hadj
        have hq : q = Function.update p m (q m) := by
          funext j
          by_cases hj : j = m
          · rw [hj]; simp
          · rw [Function.update_of_ne hj]; exact (hm.2 j hj).symm
        rw [hq, Dop_update, delta0_update]
        have := hP m p (q m) (p m)
        rw [Function.update_eq_self] at this
        simpa [hU, HarmonicGames.Projection.toGames_apply] using this
      · rw [C1.eq_zero_of_not_adj _ _ hadj, C1.eq_zero_of_not_adj _ _ hadj]
    have hrange : Dop E U ∈ LinearMap.range (delta0 (gameGraph E)) := ⟨_, hD.symm⟩
    have h4 := theorem_4_1 ι E
    obtain ⟨hmem, -⟩ := h4.2
    obtain ⟨hs, hp, hh, hn⟩ := hmem U
    have hH0 : harmonicComponent E U = 0 := by
      unfold harmonicComponent
      simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply]
      rw [pinv_right _ _ hrange]
      simp
    rw [hH0, add_zero] at hs
    exact Submodule.mem_sup.2 ⟨_, hp, _, hn, hs⟩
  · -- u ∈ P ⊕ N ⇒ potential game
    intro hu
    obtain ⟨a, ha, n, hn, hsum⟩ := Submodule.mem_sup.1 hu
    obtain ⟨φ, hφ⟩ := LinearMap.mem_range.1 (Submodule.mem_comap.1 ha.2)
    have hu' : ∀ i p, u i p = a i p + n i p := fun i p => by
      have := congrArg (fun w : Games E => w i p) hsum
      simpa [HarmonicGames.Projection.toGames_apply] using this.symm
    have hker : ∀ i (p : ∀ k, E k) (x : E i), n i (Function.update p i x) = n i p := by
      intro i p x
      have h0 := Dop_update E n i p x
      rw [LinearMap.mem_ker.1 hn] at h0
      have : (0 : C1 (gameGraph E)) p (Function.update p i x) = 0 := rfl
      linarith
    refine ⟨fun p => φ p, ?_⟩
    intro i y x z
    have hxx : Function.update (Function.update y i z) i x = Function.update y i x := by
      simp
    have h1 := Dop_update E a i (Function.update y i z) x
    rw [← hφ, delta0_update, hxx] at h1
    have hnx := hker i y x
    have hnz := hker i y z
    show u i (Function.update y i x) - u i (Function.update y i z) =
      φ (Function.update y i x) - φ (Function.update y i z)
    rw [hu' i (Function.update y i x), hu' i (Function.update y i z)]
    linarith
