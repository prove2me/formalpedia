-- Prove2me | solution 1 for KStar.Tree.twist_smul_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:37:12.200157+00:00
-- url     : https://prove2.me/submissions/a4028060-4371-471e-b318-90b2d1ad8fab

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_ClassNumberBounds_CyclotomicTotient_SkolemNoether
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_ClassNumberBounds_CyclotomicTotient_TwistTrace
import Theorems.Thm_KStar_Tree_det_algHom

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace KStar.Tree
private theorem squareTopTwistPlaces_coprime_splitPlaces {S A : Type} [CommRing A] [IsLocalRing A] [Ring S] [Algebra A S] {r : ℕ}
    (f f' : S →ₐ[A] Matrix (Fin r) (Fin r) A) (hf : Function.Surjective f)
    (hf' : Function.Surjective f') (U U' : Matrix (Fin r) (Fin r) A)
    (h : ∀ z, (f z * U).trace = (f' z * U').trace) (z₀ : S) (u : A) (hz : f' z₀ = u • f z₀)
    (hu : IsUnit (f z₀).det) : (u ^ r - 1) • U = 0 := by
  classical
  let c : Ideal A := (Submodule.span A {U}).annihilator
  have hc : ∀ a, a ∈ c ↔ a • U = 0 := fun a => Submodule.mem_annihilator_span_singleton U a
  have key : ∀ z, f' z = 0 → ∀ i j, f z i j ∈ c := by
    intro z hz i j
    rw [hc]
    ext b a
    obtain ⟨p, hp⟩ := hf (Matrix.single a i 1)
    obtain ⟨q, hq⟩ := hf (Matrix.single j b 1)
    have h1 := h (p * z * q)
    rw [map_mul, map_mul, map_mul, map_mul, hz, hp, hq, Matrix.single_mul_mul_single,
      Matrix.trace_single_mul] at h1
    simpa using h1
  rw [← hc]
  by_cases htop : c = ⊤
  · rw [htop]; trivial
  have : Nontrivial (A ⧸ c) := Ideal.Quotient.nontrivial_iff.mpr htop
  have : IsLocalRing (A ⧸ c) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk c) Ideal.Quotient.mk_surjective
  let π : Matrix (Fin r) (Fin r) A →+* Matrix (Fin r) (Fin r) (A ⧸ c) :=
    (Ideal.Quotient.mk c).mapMatrix
  have hπ : Function.Surjective π := by
    intro y
    choose w hw using fun i j => Ideal.Quotient.mk_surjective (I := c) (y i j)
    exact ⟨Matrix.of w, by ext i j; simp [π, hw]⟩
  have hπs : ∀ (a : A) x, π (a • x) = Ideal.Quotient.mk c a • π x := by
    intro a x
    ext i j
    simp [π]
  choose s hs using fun i j : Fin r => hf' (Matrix.single i j 1)
  let L : Matrix (Fin r) (Fin r) (A ⧸ c) →ₗ[A ⧸ c] Matrix (Fin r) (Fin r) (A ⧸ c) :=
    { toFun := fun y => ∑ i, ∑ j, y i j • π (f (s i j))
      map_add' := by
        intro x y
        simp [add_smul, Finset.sum_add_distrib]
      map_smul' := by
        intro a y
        simp [Finset.smul_sum, mul_smul] }
  have hL : ∀ z, L (π (f' z)) = π (f z) := by
    intro z
    have h0 : f' (z - ∑ i, ∑ j, f' z i j • s i j) = 0 := by
      rw [map_sub, sub_eq_zero]
      simp only [map_sum, map_smul, hs, Matrix.smul_single, smul_eq_mul, mul_one]
      exact Matrix.matrix_eq_sum_single _
    have h1 : π (f (z - ∑ i, ∑ j, f' z i j • s i j)) = 0 := by
      ext i j
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (key _ h0 i j)
    rw [map_sub, map_sub, sub_eq_zero] at h1
    rw [h1]
    simp only [map_sum, map_smul, hπs]
    rfl
  let θ : Matrix (Fin r) (Fin r) (A ⧸ c) →ₐ[A ⧸ c] Matrix (Fin r) (Fin r) (A ⧸ c) :=
    AlgHom.ofLinearMap L (by simpa using hL 1) (by
      intro x y
      obtain ⟨x, rfl⟩ := hπ x
      obtain ⟨y, rfl⟩ := hπ y
      obtain ⟨x, rfl⟩ := hf' x
      obtain ⟨y, rfl⟩ := hf' y
      rw [← map_mul, ← map_mul, hL, hL, hL, map_mul, map_mul])
  have hd := det_algHom θ (π (f' z₀))
  have hθ : θ (π (f' z₀)) = π (f z₀) := hL z₀
  rw [hθ, hz, ← RingHom.map_det, ← RingHom.map_det, Matrix.det_smul, map_mul] at hd
  have hu' : IsUnit (Ideal.Quotient.mk c (f z₀).det) := hu.map _
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_one, sub_eq_zero]
  rw [Fintype.card_fin] at hd
  exact hu'.mul_right_cancel (by rw [one_mul]; exact hd.symm)
end KStar.Tree
end

set_option autoImplicit false
open KStar KStar.Tree
namespace KStar.Tree
theorem _root_.solution (Γ A : Type) [Group Γ] [CommRing A] [IsLocalRing A] (r : ℕ)
    (T : Γ →* Matrix (Fin r) (Fin r) A) (χ : Γ →* A) (hspan : Submodule.span A (Set.range T) = ⊤)
    (U U' : Matrix (Fin r) (Fin r) A) (hU : ∀ g, (T g * U).trace = χ g * (T g * U').trace) (g₀ : Γ) :
    (χ g₀ ^ r - 1) • U = 0 := by
  classical
  let T' : Γ →* Matrix (Fin r) (Fin r) A :=
    { toFun := fun g => χ g • T g
      map_one' := by simp
      map_mul' := by
        intro g h
        simp [mul_smul, smul_comm (χ h) (χ g)] }
  let f : MonoidAlgebra A Γ →ₐ[A] Matrix (Fin r) (Fin r) A := MonoidAlgebra.lift A _ Γ T
  let f' : MonoidAlgebra A Γ →ₐ[A] Matrix (Fin r) (Fin r) A := MonoidAlgebra.lift A _ Γ T'
  have e : ∀ g, f (MonoidAlgebra.of A Γ g) = T g := fun g => MonoidAlgebra.lift_of _ _
  have e' : ∀ g, f' (MonoidAlgebra.of A Γ g) = χ g • T g := fun g => MonoidAlgebra.lift_of _ _
  have surj : ∀ F : MonoidAlgebra A Γ →ₐ[A] Matrix (Fin r) (Fin r) A,
      (∀ g, ∃ z, F z = T g) → Function.Surjective F := by
    intro F hF
    have : LinearMap.range F.toLinearMap = ⊤ := by
      rw [eq_top_iff, ← hspan, Submodule.span_le]
      rintro _ ⟨g, rfl⟩
      exact hF g
    exact LinearMap.range_eq_top.mp this
  refine squareTopTwistPlaces_coprime_splitPlaces f f' (surj f fun g => ⟨_, e g⟩) (surj f' fun g => ?_) U U' ?_
    (MonoidAlgebra.of A Γ g₀) (χ g₀) (by rw [e, e']) ?_
  · refine ⟨χ g⁻¹ • MonoidAlgebra.of A Γ g, ?_⟩
    rw [map_smul, e', smul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]
  · intro z
    induction z using MonoidAlgebra.induction_on with
    | of g => rw [e, e', hU, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
    | add x y hx hy => simp only [map_add, Matrix.add_mul, Matrix.trace_add, hx, hy]
    | smul a x hx => simp only [map_smul, Matrix.smul_mul, Matrix.trace_smul, hx]
  · rw [e]
    exact (Matrix.isUnit_iff_isUnit_det _).mp ((Group.isUnit g₀).map T)
end KStar.Tree
