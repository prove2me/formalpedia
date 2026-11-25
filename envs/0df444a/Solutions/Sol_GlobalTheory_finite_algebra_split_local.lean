-- Prove2me | solution 1 for GlobalTheory.finite_algebra_split_local
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:54:43.876954+00:00
-- url     : https://prove2.me/submissions/9547ce35-9f2d-4635-a10e-a9039f612c59

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_FiniteAlgebraSplitLocal
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
private theorem finSplit_max_eq {O A : Type} [CommRing O] [IsLocalRing O] [CommRing A]
    [Algebra O A] (φ : A →ₐ[O] O) (N : Ideal A) (hN : N.IsMaximal)
    (h : RingHom.ker φ ≤ N) : N = (maximalIdeal O).comap φ := by
  refine hN.eq_of_le ?_ ?_
  · intro htop
    have h1 : (1 : A) ∈ (maximalIdeal O).comap φ := htop ▸ Submodule.mem_top
    rw [Ideal.mem_comap, map_one] at h1
    exact mem_nonunits_iff.1 ((IsLocalRing.mem_maximalIdeal _).1 h1) isUnit_one
  · intro x hx
    rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    apply hN.ne_top
    rw [Ideal.eq_top_iff_one]
    have hy : algebraMap O A (↑hu.unit⁻¹) * x ∈ N := N.mul_mem_left _ hx
    have hφy : φ (algebraMap O A (↑hu.unit⁻¹) * x) = 1 := by
      rw [map_mul, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply]
      exact hu.val_inv_mul
    have hk : 1 - algebraMap O A (↑hu.unit⁻¹) * x ∈ N :=
      h (by rw [RingHom.mem_ker, map_sub, map_one, hφy, sub_self])
    simpa using N.add_mem hk hy
private theorem finSplit_exists {O A : Type} [CommRing O] [IsLocalRing O] [CommRing A]
    [Algebra O A] [Finite (A →ₐ[O] O)] (M : Ideal A) :
    ∃ e : A, ∀ φ : A →ₐ[O] O, ((maximalIdeal O).comap φ = M → φ e = 1) ∧
      ((maximalIdeal O).comap φ ≠ M → φ e = 0) := by
  classical
  have := Fintype.ofFinite (A →ₐ[O] O)
  have key : ∀ φ ψ : A →ₐ[O] O, ∃ x : A, (maximalIdeal O).comap φ = M →
      (maximalIdeal O).comap ψ ≠ M → φ x = 1 ∧ ψ x = 0 := by
    intro φ ψ
    by_cases hφ : (maximalIdeal O).comap φ = M
    swap
    · exact ⟨0, fun h => absurd h hφ⟩
    by_cases hψ : (maximalIdeal O).comap ψ = M
    · exact ⟨0, fun _ h => absurd hψ h⟩
    have htop : RingHom.ker φ ⊔ RingHom.ker ψ = ⊤ := by
      by_contra hne
      obtain ⟨N, hN, hle⟩ := Ideal.exists_le_maximal _ hne
      have e1 := finSplit_max_eq φ N hN (le_sup_left.trans hle)
      have e2 := finSplit_max_eq ψ N hN (le_sup_right.trans hle)
      exact hψ (e2.symm.trans (e1.trans hφ))
    have h1 : (1 : A) ∈ RingHom.ker φ ⊔ RingHom.ker ψ := htop ▸ Submodule.mem_top
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 h1
    refine ⟨b, fun _ _ => ⟨?_, RingHom.mem_ker.1 hb⟩⟩
    have hφab := congrArg φ hab
    rw [map_add, RingHom.mem_ker.1 ha, zero_add, map_one] at hφab
    exact hφab
  choose x hx using key
  refine ⟨1 - ∏ φ ∈ Finset.univ.filter (fun φ : A →ₐ[O] O => (maximalIdeal O).comap φ = M),
      (1 - ∏ ψ ∈ Finset.univ.filter (fun ψ : A →ₐ[O] O => (maximalIdeal O).comap ψ ≠ M), x φ ψ),
      fun φ0 => ⟨fun h0 => ?_, fun h0 => ?_⟩⟩
  · rw [map_sub, map_one, map_prod, sub_eq_self]
    apply Finset.prod_eq_zero (i := φ0) (by simp [h0])
    rw [map_sub, map_one, map_prod, sub_eq_zero, eq_comm]
    apply Finset.prod_eq_one
    intro ψ hψ
    exact (hx φ0 ψ h0 (Finset.mem_filter.1 hψ).2).1
  · rw [map_sub, map_one, map_prod, sub_eq_zero, eq_comm]
    apply Finset.prod_eq_one
    intro φ hφ
    rw [map_sub, map_one, map_prod, sub_eq_self]
    apply Finset.prod_eq_zero (i := φ0) (by simp [h0])
    exact (hx φ φ0 (Finset.mem_filter.1 hφ).2 h0).2
end GlobalTheory
end

set_option autoImplicit false
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
  (∀ (O A : Type) [CommRing O] [IsLocalRing O] [CommRing A] [Algebra O A] [Module.Finite O A] [Finite (A →ₐ[O] O)],
    (∀ f : A, (∀ φ : A →ₐ[O] O, φ f = 0) → f = 0) →
    ∃ (n : ℕ) (ε : Fin n → A), CompleteOrthogonalIdempotents ε ∧ ∀ i, IsLocalRing (A ⧸ Ideal.span {1 - ε i})) := by
  intro O A _ _ _ _ _ _ hsep
  classical
  have := Fintype.ofFinite (A →ₐ[O] O)
  have hone : (1 : O) ∉ maximalIdeal O := fun h =>
    mem_nonunits_iff.1 ((IsLocalRing.mem_maximalIdeal _).1 h) isUnit_one
  let Pts := Set.range (fun φ : A →ₐ[O] O => (maximalIdeal O).comap φ)
  let eqv : Fin (Fintype.card Pts) ≃ Pts := (Fintype.equivFin Pts).symm
  choose e he using fun M : Ideal A => finSplit_exists (O := O) M
  have hval : ∀ (M : Ideal A) (φ : A →ₐ[O] O),
      φ (e M) = if (maximalIdeal O).comap φ = M then 1 else 0 := by
    intro M φ
    split_ifs with h
    · exact (he M φ).1 h
    · exact (he M φ).2 h
  have ext : ∀ a b : A, (∀ φ : A →ₐ[O] O, φ a = φ b) → a = b := fun a b h =>
    sub_eq_zero.1 (hsep _ fun φ => by rw [map_sub, h φ, sub_self])
  have hmax : ∀ N : Ideal A, N.IsMaximal → ∃ φ : A →ₐ[O] O, (maximalIdeal O).comap φ = N := by
    intro N hN
    by_contra hcon
    simp only [not_exists] at hcon
    have hnot : ∀ φ : A →ₐ[O] O, ¬ RingHom.ker φ ≤ N := fun φ hle =>
      hcon φ (finSplit_max_eq φ N hN hle).symm
    simp only [SetLike.not_le_iff_exists] at hnot
    choose a ha haN using hnot
    have := hN.isPrime
    have h0 : ∏ φ, a φ = 0 := hsep _ fun ψ => by
      rw [map_prod]
      exact Finset.prod_eq_zero (Finset.mem_univ ψ) (RingHom.mem_ker.1 (ha ψ))
    have hin : ∏ φ, a φ ∈ N := h0 ▸ N.zero_mem
    obtain ⟨φ, -, hφ⟩ := Ideal.IsPrime.prod_mem_iff.1 hin
    exact haN φ hφ
  refine ⟨Fintype.card Pts, fun i => e (eqv i).1, ⟨⟨fun i => ?_, fun i j hij => ?_⟩, ?_⟩, fun i => ?_⟩
  · show e (eqv i).1 * e (eqv i).1 = e (eqv i).1
    apply ext
    intro φ
    rw [map_mul, hval]
    split_ifs <;> simp
  · show e (eqv i).1 * e (eqv j).1 = 0
    have hne : (eqv i).1 ≠ (eqv j).1 := fun h => hij (eqv.injective (Subtype.ext h))
    apply ext
    intro φ
    rw [map_mul, hval, hval, map_zero]
    split_ifs with h1 h2 h2
    · exact absurd (h1.symm.trans h2) hne
    all_goals simp
  · apply ext
    intro φ
    rw [map_sum, map_one]
    simp only [hval]
    rw [Fintype.sum_equiv eqv _
      (fun M : Pts => if (maximalIdeal O).comap φ = M.1 then (1 : O) else 0) (fun _ => rfl)]
    rw [Finset.sum_eq_single ⟨(maximalIdeal O).comap φ, φ, rfl⟩]
    · simp
    · intro b _ hb
      rw [if_neg]
      intro h
      exact hb (Subtype.ext h.symm)
    · intro h
      exact absurd (Finset.mem_univ _) h
  · obtain ⟨φ0, hφ0⟩ := (eqv i).2
    replace hφ0 : (maximalIdeal O).comap φ0 = (eqv i).1 := hφ0
    have hmem : ∀ ψ : A →ₐ[O] O,
        1 - e (eqv i).1 ∈ (maximalIdeal O).comap ψ ↔ (maximalIdeal O).comap ψ = (eqv i).1 := by
      intro ψ
      rw [Ideal.mem_comap, map_sub, map_one, hval]
      split_ifs with h
      · simp [h]
      · simp only [sub_zero, h, iff_false]
        exact hone
    have hJM : Ideal.span {1 - e (eqv i).1} ≤ (eqv i).1 := by
      rw [Ideal.span_le, Set.singleton_subset_iff]
      have h := (hmem φ0).2 hφ0
      rw [hφ0] at h
      exact h
    have hMtop : (eqv i).1 ≠ ⊤ := by
      rw [← hφ0]
      intro h
      have h1 : (1 : A) ∈ (maximalIdeal O).comap φ0 := h ▸ Submodule.mem_top
      rw [Ideal.mem_comap, map_one] at h1
      exact hone h1
    have hJ : Ideal.span {1 - e (eqv i).1} ≠ ⊤ := fun h => hMtop (top_le_iff.1 (h ▸ hJM))
    have := Ideal.Quotient.nontrivial_iff.2 hJ
    obtain ⟨Q0, hQ0⟩ := Ideal.exists_maximal (A ⧸ Ideal.span {1 - e (eqv i).1})
    have hcomap : ∀ Q : Ideal (A ⧸ Ideal.span {1 - e (eqv i).1}), Q.IsMaximal →
        Q = (eqv i).1.map (Ideal.Quotient.mk _) := by
      intro Q hQ
      have := hQ
      have hQ' : (Q.comap (Ideal.Quotient.mk (Ideal.span {1 - e (eqv i).1}))).IsMaximal :=
        Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
      obtain ⟨ψ, hψ⟩ := hmax _ hQ'
      have hin : 1 - e (eqv i).1 ∈ Q.comap (Ideal.Quotient.mk (Ideal.span {1 - e (eqv i).1})) := by
        rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span (Set.mem_singleton _))]
        exact Q.zero_mem
      rw [← hψ] at hin
      have hψM := (hmem ψ).1 hin
      rw [← Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective Q, ← hψ, hψM]
    exact IsLocalRing.of_unique_max_ideal
      ⟨Q0, hQ0, fun Q hQ => (hcomap Q hQ).trans (hcomap Q0 hQ0).symm⟩
end GlobalTheory
