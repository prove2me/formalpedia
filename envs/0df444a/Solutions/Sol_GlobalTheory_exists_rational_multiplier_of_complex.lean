-- Prove2me | solution 1 for GlobalTheory.exists_rational_multiplier_of_complex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:38:48.874827+00:00
-- url     : https://prove2.me/submissions/451dc363-92a3-4c60-9d04-73004ad5e6be

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsRationalMultiplierOfComplexMultiplier
import Theorems.Thm_GlobalTheory_relation_descends_along_functional
import Theorems.Thm_GlobalTheory_exists_functional_ne_zero_of_embedding

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Module
namespace GlobalTheory
theorem _root_.solution :
    ∀ (K A B : Type) [Field K] [CommRing A] [Algebra K A] [CommRing B] [Algebra ℂ B] (σ : K →+* ℂ) (rd : A →+* B), (∀ (a : K) (f : A), rd (a • f) = σ a • rd f) → ∀ (V V' : Submodule K A) [FiniteDimensional K V] [FiniteDimensional K V'], (∀ (n : ℕ) (b : Fin n → A), (∀ i, b i ∈ V * V') → LinearIndependent K b → LinearIndependent ℂ (fun i => rd (b i))) → ∀ h : B, (∀ f ∈ V, h * rd f ∈ Submodule.span ℂ (rd '' (V' : Set A))) → (∃ f ∈ V, h * rd f ≠ 0) → ∃ T : V →ₗ[K] V', T ≠ 0 ∧ ∀ f g : V, (T f : A) * (g : A) = (f : A) * (T g : A) := by
  classical
  intro K A B _ _ _ _ _ σ rd hrd V V' _ _ hVV h hspan hne
  have : FiniteDimensional K ↥(V * V') :=
    Module.Finite.iff_fg.mpr (Submodule.FG.mul (Module.Finite.iff_fg.mp inferInstance)
      (Module.Finite.iff_fg.mp inferInstance))
  have hrdsum : ∀ {m : ℕ} (a : Fin m → K) (v : Fin m → A),
      rd (∑ j, a j • v j) = ∑ j, σ (a j) • rd (v j) := by
    intro m a v
    rw [map_sum]
    simp only [hrd]
  have hexp : ∀ {U : Submodule K A} {m : ℕ} (b : Basis (Fin m) K U) (u : U),
      (u : A) = ∑ j, b.repr u j • (b j : A) := by
    intro U m b u
    have h1 := congrArg (fun v : U => (v : A)) (b.sum_repr u)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h1
    exact h1.symm
  obtain ⟨n, ⟨bV⟩⟩ : ∃ n, Nonempty (Basis (Fin n) K V) := ⟨_, ⟨Module.finBasis K V⟩⟩
  obtain ⟨n', ⟨bV'⟩⟩ : ∃ n, Nonempty (Basis (Fin n) K V') := ⟨_, ⟨Module.finBasis K V'⟩⟩
  have hC : ∀ i, ∃ C : Fin n' → ℂ, h * rd (bV i : A) = ∑ j, C j • rd (bV' j : A) := by
    intro i
    have hm := hspan _ (bV i).2
    have hsub : Submodule.span ℂ (rd '' (V' : Set A)) ≤
        Submodule.span ℂ (Set.range fun j => rd (bV' j : A)) := by
      rw [Submodule.span_le]
      rintro _ ⟨u, hu, rfl⟩
      have e : u = ∑ j, bV'.repr ⟨u, hu⟩ j • (bV' j : A) := hexp bV' ⟨u, hu⟩
      rw [e, hrdsum]
      exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
    obtain ⟨C, hCe⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp (hsub hm)
    exact ⟨C, hCe.symm⟩
  choose C hC using hC
  have hi0 : ∃ i, h * rd (bV i : A) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨f, hf, hfne⟩ := hne
    apply hfne
    have e : f = ∑ j, bV.repr ⟨f, hf⟩ j • (bV j : A) := hexp bV ⟨f, hf⟩
    rw [e, hrdsum, Finset.mul_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [mul_smul_comm, hcon i, smul_zero]
  obtain ⟨i0, hi0⟩ := hi0
  have hj0 : ∃ j, C i0 j ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hi0
    rw [hC i0]
    exact Finset.sum_eq_zero fun j _ => by rw [hcon j, zero_smul]
  obtain ⟨j0, hj0⟩ := hj0
  obtain ⟨φ, hφ, hφne⟩ := exists_functional_ne_zero_of_embedding K σ (C i0 j0) hj0
  obtain ⟨T, hT⟩ : ∃ T : V →ₗ[K] V', ∀ i, T (bV i) = ∑ j, φ (C i j) • bV' j :=
    ⟨bV.constr K (fun i => ∑ j, φ (C i j) • bV' j), fun i => bV.constr_basis K _ i⟩
  have hTA : ∀ i, ((T (bV i) : V') : A) = ∑ j, φ (C i j) • (bV' j : A) := by
    intro i
    rw [hT]
    simp only [Submodule.coe_sum, Submodule.coe_smul]
  have hbasis : ∀ i k, ((T (bV i) : V') : A) * (bV k : A) = (bV i : A) * ((T (bV k) : V') : A) := by
    intro i k
    have key := relation_descends_along_functional K A B σ rd hrd (V * V') hVV φ hφ
      (ι := Fin n' ⊕ Fin n')
      (Sum.elim (fun j => (bV k : A) * (bV' j : A)) (fun j => (bV i : A) * (bV' j : A)))
      (by
        rintro (j | j)
        · exact Submodule.mul_mem_mul (bV k).2 (bV' j).2
        · exact Submodule.mul_mem_mul (bV i).2 (bV' j).2)
      (Sum.elim (fun j => C i j) (fun j => - C k j))
      (by
        rw [Fintype.sum_sum_type]
        simp only [Sum.elim_inl, Sum.elim_inr, map_mul, neg_smul, Finset.sum_neg_distrib]
        simp only [← mul_smul_comm, ← Finset.mul_sum, ← hC]
        ring)
    rw [Fintype.sum_sum_type] at key
    simp only [Sum.elim_inl, Sum.elim_inr, map_neg, neg_smul, Finset.sum_neg_distrib,
      ← mul_smul_comm, ← Finset.mul_sum] at key
    rw [hTA, hTA, mul_comm _ ((bV k : V) : A)]
    rw [mul_neg] at key
    exact add_neg_eq_zero.mp key
  have hleft : ∀ i (g : V), ((T (bV i) : V') : A) * (g : A) = (bV i : A) * ((T g : V') : A) := by
    intro i g
    have h2 := bV.ext (f₁ := (LinearMap.mulLeft K ((T (bV i) : V') : A)).comp V.subtype)
      (f₂ := (LinearMap.mulLeft K ((bV i : V) : A)).comp (V'.subtype.comp T))
      (fun k => by simpa using hbasis i k)
    simpa using LinearMap.congr_fun h2 g
  refine ⟨T, ?_, fun f g => ?_⟩
  · intro hT0
    have h1 : T (bV i0) = 0 := by rw [hT0, LinearMap.zero_apply]
    rw [hT] at h1
    exact hφne (Fintype.linearIndependent_iff.mp bV'.linearIndependent _ h1 j0)
  · have h2 := bV.ext (f₁ := (LinearMap.mulRight K (g : A)).comp (V'.subtype.comp T))
      (f₂ := (LinearMap.mulRight K ((T g : V') : A)).comp V.subtype)
      (fun i => by simpa using hleft i g)
    simpa using LinearMap.congr_fun h2 f
end GlobalTheory
