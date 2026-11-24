-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FinPresDescent.ker_fg_of_projective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:31:38.4179+00:00
-- url     : https://prove2.me/submissions/739ea205-5250-49b9-abf4-016fa57d2eba

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ExistsRetr
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_FinitePresentationOfFaithfullyFlat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FinPresDescent
namespace GlobalTheory.CompanionTheory.FinPresDescent
theorem _root_.solution {P C M : Type*} [CommRing P] [CommRing C] [Algebra P C]
    [AddCommGroup M] [Module P M] [Module C M] [IsScalarTower P C M]
    (hsurj : Function.Surjective (algebraMap P C))
    [Module.FinitePresentation P M] [Module.Projective C M]
    (faith : ∀ c : C, (∀ m : M, c • m = 0) → c = 0) :
    (RingHom.ker (algebraMap P C)).FG := by
  classical
  obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' P M
  have hker : (LinearMap.ker π).FG := Module.FinitePresentation.fg_ker π hπ
  let b : Fin n → M := fun i => π (Pi.single i 1)
  have hπb : ∀ x, π x = ∑ i, x i • b i := fun x => by
    rw [LinearMap.pi_apply_eq_sum_univ π x]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 2
    ext j
    simp [b, Pi.single_apply, eq_comm]
  have hπC : ∀ x, π x = ∑ i, algebraMap P C (x i) • b i := fun x => by
    rw [hπb]
    simp only [algebraMap_smul]
  let πC : (Fin n → C) →ₗ[C] M := Fintype.linearCombination C b
  have hπCs : Function.Surjective πC := by
    intro m
    obtain ⟨x, rfl⟩ := hπ m
    refine ⟨fun i => algebraMap P C (x i), ?_⟩
    rw [hπC, Fintype.linearCombination_apply]
  obtain ⟨s, hs⟩ := Module.projective_lifting_property πC LinearMap.id hπCs
  have hs' : ∀ m, ∑ i, s m i • b i = m := fun m => by
    have := LinearMap.congr_fun hs m
    simpa [πC, Fintype.linearCombination_apply] using this
  choose v hv using fun (p : Fin n × Fin n) => hsurj (s (b p.1) p.2)
  let E : (Fin n → P) → Fin n → P := fun x j => ∑ i, x i * v (i, j)
  have key1 : ∀ x j, algebraMap P C (E x j) = s (π x) j := fun x j => by
    have hsx : s (π x) = ∑ i, algebraMap P C (x i) • s (b i) := by
      rw [hπC, map_sum]
      simp only [map_smul]
    rw [hsx, Finset.sum_apply]
    simp only [E, map_sum, map_mul, hv, Pi.smul_apply, smul_eq_mul]
  have key2 : ∀ x, π (fun j => E x j) = π x := fun x => by
    rw [hπC]
    simp only [key1]
    exact hs' _
  obtain ⟨G, hG⟩ := hker
  let I₀ : Ideal P := Ideal.span ((fun q : (Fin n → P) × Fin n => E q.1 q.2) ''
    ((G : Set (Fin n → P)) ×ˢ Set.univ))
  have hI₀ : I₀.FG := ⟨(G ×ˢ Finset.univ).image (fun q : (Fin n → P) × Fin n => E q.1 q.2), by
    simp [I₀]⟩
  have key3 : ∀ x ∈ LinearMap.ker π, ∀ j, E x j ∈ I₀ := by
    intro x hx j
    rw [← hG] at hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact Ideal.subset_span ⟨(x, j), ⟨hx, trivial⟩, rfl⟩
    | zero => simp [E]
    | add x y _ _ hx hy =>
      have : E (x + y) j = E x j + E y j := by simp [E, add_mul, Finset.sum_add_distrib]
      rw [this]; exact I₀.add_mem hx hy
    | smul t x _ hx =>
      have : E (t • x) j = t * E x j := by simp [E, Finset.mul_sum, mul_assoc]
      rw [this]; exact I₀.mul_mem_left t hx
  let T : Ideal P := Ideal.span (Set.range v)
  have hET : ∀ x j, E x j ∈ T := fun x j =>
    T.sum_mem fun i _ => T.mul_mem_left _ (Ideal.subset_span ⟨(i, j), rfl⟩)
  have hle : (⊤ : Submodule P M) ≤ T • (⊤ : Submodule P M) := by
    intro m _
    obtain ⟨x, rfl⟩ := hπ m
    rw [← key2, hπb]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (hET x i) trivial
  obtain ⟨r, hr, hr0⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul T ⊤
    Module.Finite.fg_top hle
  have hrI : r ∈ RingHom.ker (algebraMap P C) := by
    rw [RingHom.mem_ker]
    refine faith _ fun m => ?_
    rw [algebraMap_smul]
    exact hr0 m trivial
  have key5 : ∀ a ∈ RingHom.ker (algebraMap P C), ∀ p, a * v p ∈ I₀ := by
    rintro a ha ⟨i, j⟩
    have hx : (Pi.single i a : Fin n → P) ∈ LinearMap.ker π := by
      rw [LinearMap.mem_ker, hπC]
      refine Finset.sum_eq_zero fun k _ => ?_
      by_cases hk : k = i
      · subst hk
        rw [Pi.single_eq_same, RingHom.mem_ker.1 ha, zero_smul]
      · rw [Pi.single_eq_of_ne hk, map_zero, zero_smul]
    have := key3 _ hx j
    simpa [E, Pi.single_apply] using this
  have key6 : ∀ a ∈ RingHom.ker (algebraMap P C), ∀ t ∈ T, a * t ∈ I₀ := by
    intro a ha t ht
    induction ht using Submodule.span_induction with
    | mem t ht => obtain ⟨p, rfl⟩ := ht; exact key5 a ha p
    | zero => simp
    | add x y _ _ hx hy => rw [mul_add]; exact I₀.add_mem hx hy
    | smul c x _ hx =>
      rw [smul_eq_mul, mul_left_comm]; exact I₀.mul_mem_left c hx
  have hI₀le : I₀ ≤ RingHom.ker (algebraMap P C) := by
    refine Ideal.span_le.2 ?_
    rintro _ ⟨⟨g, j⟩, ⟨hg, -⟩, rfl⟩
    have hgk : g ∈ LinearMap.ker π := by
      rw [← hG]; exact Submodule.subset_span hg
    change algebraMap P C (E g j) = 0
    rw [key1, LinearMap.mem_ker.1 hgk, map_zero]
    rfl
  have heq : RingHom.ker (algebraMap P C) = I₀ ⊔ Ideal.span {r} := by
    apply le_antisymm
    · intro a ha
      have h1 : a * (r - 1) ∈ I₀ := key6 a ha _ hr
      have h2 : a * r ∈ Ideal.span {r} := Ideal.mul_mem_left _ a (Ideal.mem_span_singleton_self r)
      have : a = a * r + -(a * (r - 1)) := by ring
      rw [this]
      exact Submodule.add_mem_sup h2 (I₀.neg_mem h1) |> fun h => by
        rw [sup_comm]; exact h
    · refine sup_le hI₀le ?_
      rw [Ideal.span_singleton_le_iff_mem]
      exact hrI
  rw [heq]
  exact Submodule.FG.sup hI₀ (Submodule.fg_span_singleton r)
end GlobalTheory.CompanionTheory.FinPresDescent
