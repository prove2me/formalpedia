-- Prove2me | solution 1 for GlobalTheory.algHom_eq_of_reduction_eq_of_coords_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:22:13.381047+00:00
-- url     : https://prove2.me/submissions/3e6555cb-0a3d-4b9c-8884-0179dd799dc4

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_AlgHomEqOfReductionEqOfCoordsEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (O B : Type) [CommRing O] [IsLocalRing O] [CommRing B] [Algebra O B] [Algebra.FiniteType O B] (s s' : B →ₐ[O] O) (g : ℕ) (u : Fin g → B), (∀ b, s b - s' b ∈ IsLocalRing.maximalIdeal O) → (∀ i, s (u i) = s' (u i)) → (∀ b, s b = 0 → ∃ t : B, IsUnit (s t) ∧ t * b ∈ Ideal.span (Set.range fun i => u i - algebraMap O B (s (u i))) ⊔ (IsLocalRing.maximalIdeal O).map (algebraMap O B)) → s = s' := by
  intro O B _ _ _ _ hft s s' g u hred hu hgen
  classical
  obtain ⟨S, hS⟩ := hft.out
  let N : Ideal O := Ideal.span ((S.image fun b => s' b - s b : Finset O) : Set O)
  have hNfg : N.FG := ⟨_, rfl⟩
  have h1 : ∀ b, s' b - s b ∈ N := by
    intro b
    have hb : b ∈ Algebra.adjoin O (S : Set B) := hS ▸ Algebra.mem_top
    induction hb using Algebra.adjoin_induction with
    | mem x hx =>
      exact Ideal.subset_span (by
        simp only [Finset.coe_image]; exact ⟨x, hx, rfl⟩)
    | algebraMap r => simp
    | add x y _ _ hx hy =>
      have : s' (x + y) - s (x + y) = (s' x - s x) + (s' y - s y) := by
        simp only [map_add]; ring
      rw [this]; exact N.add_mem hx hy
    | mul x y _ _ hx hy =>
      have : s' (x * y) - s (x * y) = s' x * (s' y - s y) + s y * (s' x - s x) := by
        simp only [map_mul]; ring
      rw [this]; exact N.add_mem (N.mul_mem_left _ hy) (N.mul_mem_left _ hx)
  have h2 : ∀ y ∈ (IsLocalRing.maximalIdeal O).map (algebraMap O B),
      ∀ c : B, s' (c * y) - s (c * y) ∈ IsLocalRing.maximalIdeal O * N := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, ha, rfl⟩ := hx
      intro c
      have : s' (c * algebraMap O B a) - s (c * algebraMap O B a) = a * (s' c - s c) := by
        simp only [map_mul, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply]; ring
      rw [this]; exact Ideal.mul_mem_mul ha (h1 c)
    | zero => intro c; simp
    | add x y _ _ hx hy =>
      intro c
      have : s' (c * (x + y)) - s (c * (x + y))
          = (s' (c * x) - s (c * x)) + (s' (c * y) - s (c * y)) := by
        simp only [map_add, map_mul]; ring
      rw [this]; exact Ideal.add_mem _ (hx c) (hy c)
    | smul a x _ hx =>
      intro c
      have := hx (c * a)
      rwa [_root_.mul_assoc] at this
  have h3 : ∀ j ∈ Ideal.span (Set.range fun i => u i - algebraMap O B (s (u i))),
      s j = 0 ∧ s' j = 0 := by
    intro j hj
    have a1 : Ideal.span (Set.range fun i => u i - algebraMap O B (s (u i))) ≤
        RingHom.ker (s : B →+* O) := by
      rw [Ideal.span_le]; rintro _ ⟨i, rfl⟩
      simp [RingHom.mem_ker]
    have a2 : Ideal.span (Set.range fun i => u i - algebraMap O B (s (u i))) ≤
        RingHom.ker (s' : B →+* O) := by
      rw [Ideal.span_le]; rintro _ ⟨i, rfl⟩
      simp [RingHom.mem_ker, hu i]
    exact ⟨a1 hj, a2 hj⟩
  have h4 : ∀ x, s' x - s x ∈ IsLocalRing.maximalIdeal O * N := by
    intro x
    have hb : s (x - algebraMap O B (s x)) = 0 := by simp
    have hb' : s' (x - algebraMap O B (s x)) = s' x - s x := by simp
    obtain ⟨t, ht, hmem⟩ := hgen _ hb
    obtain ⟨j, hj, y, hy, hjy⟩ := Submodule.mem_sup.1 hmem
    have ht' : IsUnit (s' t) := by
      by_contra hn
      have m1 : s' t ∈ IsLocalRing.maximalIdeal O := hn
      have m2 := Ideal.add_mem _ (hred t) m1
      rw [sub_add_cancel] at m2
      exact m2 ht
    obtain ⟨j1, j2⟩ := h3 j hj
    have e1 := congrArg s hjy
    have e2 := congrArg s' hjy
    rw [map_add, map_mul, hb, j1] at e1
    rw [map_add, map_mul, hb', j2] at e2
    have h5 := h2 y hy 1
    rw [_root_.one_mul] at h5
    have : s' y - s y = s' t * (s' x - s x) := by
      linear_combination e2 - e1
    rw [this] at h5
    exact (Ideal.unit_mul_mem_iff_mem _ ht').1 h5
  have hN : N = ⊥ := by
    refine Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (IsLocalRing.maximalIdeal O) N hNfg ?_ ?_
    · rw [Ideal.span_le]
      intro z hz
      simp only [Finset.coe_image] at hz
      obtain ⟨x, _, rfl⟩ := hz
      exact h4 x
    · exact (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge
  ext b
  have := h1 b
  rw [hN, Ideal.mem_bot, sub_eq_zero] at this
  exact this.symm
end GlobalTheory
