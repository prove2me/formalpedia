-- Prove2me | solution 1 for GlobalTheory.ideal_map_colon_eq_of_flat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:38:39.442098+00:00
-- url     : https://prove2.me/submissions/ab3e125f-8cd6-47dc-b8d3-ecfe51304f04

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_FlatMapColonIdeal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open IsLocalRing
namespace GlobalTheory
private lemma mem_colon_span_range_iff {B : Type*} [CommRing B] {P : Ideal B} {ι : Type*}
    (g : ι → B) (r : B) :
    r ∈ P.colon (Ideal.span (Set.range g) : Set B) ↔ ∀ i, r * g i ∈ P := by
  rw [Submodule.mem_colon', SetLike.coe_subset_coe]
  change Submodule.span B (Set.range g) ≤ _ ↔ _
  rw [Submodule.span_le, Set.range_subset_iff]
  simp [smul_eq_mul]
end GlobalTheory
end

set_option autoImplicit false
open IsLocalRing
open GlobalTheory
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution : ∀ {A R : Type} [CommRing A] [IsNoetherianRing A] [CommRing R]
    (φ : A →+* R), φ.Flat → ∀ I J : Ideal A, (I.colon J).map φ = (I.map φ).colon (J.map φ) := by
  intro A R _ _ _ φ hφ I J
  obtain ⟨n, a, hJ⟩ := Submodule.fg_iff_exists_fin_generating_family.mp (IsNoetherian.noetherian J)
  obtain ⟨m, b, hI⟩ := Submodule.fg_iff_exists_fin_generating_family.mp (IsNoetherian.noetherian I)
  replace hJ : Ideal.span (Set.range a) = J := hJ
  replace hI : Ideal.span (Set.range b) = I := hI
  subst hJ hI
  rw [Ideal.map_span φ (Set.range a), ← Set.range_comp]
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro r hr
    rw [Ideal.mem_comap, mem_colon_span_range_iff]
    rw [mem_colon_span_range_iff] at hr
    intro i
    simpa [map_mul] using Ideal.mem_map_of_mem φ (hr i)
  · intro s hs
    rw [mem_colon_span_range_iff] at hs
    have hmapI : (Ideal.span (Set.range b)).map φ = Ideal.span (Set.range (φ ∘ b)) := by
      rw [Ideal.map_span, ← Set.range_comp]
    choose c hc using fun i => Ideal.mem_span_range_iff_exists_fun.mp (hmapI ▸ hs i)
    letI := φ.toAlgebra
    haveI : Module.Flat A R := hφ
    let f : (Fin n → A) →ₗ[A] A × (Fin n × Fin m → A) :=
      LinearMap.prod (Fintype.linearCombination A a)
        (LinearMap.pi fun p => -(b p.2) • LinearMap.proj p.1)
    let x : A × (Fin n × Fin m → A) →ₗ[A] R :=
      LinearMap.coprod (LinearMap.toSpanSingleton A R s)
        (Fintype.linearCombination A fun p => c p.1 p.2)
    have hxf : x ∘ₗ f = 0 := by
      refine LinearMap.ext fun v => ?_
      simp [f, x, Algebra.smul_def, Fintype.sum_prod_type, Fintype.linearCombination_apply,
        LinearMap.pi_apply, map_sum, Finset.sum_mul]
      rw [← sub_eq_add_neg, sub_eq_zero]
      refine Finset.sum_congr rfl fun i _ => ?_
      have e : ∑ j, algebraMap A R (b j) * algebraMap A R (v i) * c i j
          = algebraMap A R (v i) * ∑ j, c i j * (φ ∘ b) j := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [RingHom.algebraMap_toAlgebra, Function.comp_apply]
        ring
      rw [e, hc i]
      simp only [RingHom.algebraMap_toAlgebra, Function.comp_apply]
      ring
    obtain ⟨k, g, y, hxy, hgf⟩ := Module.Flat.exists_factorization_of_comp_eq_zero_of_free hxf
    have hdec : ∀ w : A × (Fin n × Fin m → A), g w = w.1 • g (1, 0) +
        ∑ p, w.2 p • g (0, fun q => if p = q then 1 else 0) := by
      intro w
      have hw : w = w.1 • ((1 : A), (0 : Fin n × Fin m → A)) + ((0 : A), w.2) := by
        ext <;> simp
      conv_lhs => rw [hw]
      rw [map_add, map_smul]
      congr 1
      exact LinearMap.pi_apply_eq_sum_univ (g ∘ₗ LinearMap.inr A A (Fin n × Fin m → A)) w.2
    have key : ∀ q, g (1, 0) q ∈
        (Ideal.span (Set.range b)).colon (Ideal.span (Set.range a) : Set A) := by
      intro q
      rw [mem_colon_span_range_iff]
      intro i
      set w := f (fun j => if i = j then 1 else 0) with hw
      have hw1 : w.1 = a i := by simp [hw, f, Fintype.linearCombination_apply]
      have hw2 : ∀ p, w.2 p ∈ Ideal.span (Set.range b) := by
        intro p
        simp only [hw, f, LinearMap.prod_apply, Pi.prod, LinearMap.pi_apply, LinearMap.smul_apply,
          LinearMap.proj_apply, smul_eq_mul]
        exact Ideal.mul_mem_right _ _ (neg_mem (Ideal.subset_span ⟨p.2, rfl⟩))
      have h0 := DFunLike.congr_fun (hdec w) q
      rw [show g w = 0 from LinearMap.congr_fun hgf _] at h0
      simp only [Finsupp.coe_zero, Pi.zero_apply, Finsupp.coe_add, Pi.add_apply, Finsupp.coe_smul,
        Pi.smul_apply, smul_eq_mul, Finsupp.finset_sum_apply] at h0
      have h1 : g (1, 0) q * a i = -∑ p, w.2 p * g (0, fun q => if p = q then 1 else 0) q := by
        rw [← hw1]
        linear_combination -h0
      rw [h1]
      exact neg_mem (Ideal.sum_mem _ fun p _ => Ideal.mul_mem_right _ _ (hw2 p))
    have hs' : s = x (1, 0) := by simp [x]
    rw [hs', hxy, LinearMap.comp_apply, ← Finsupp.univ_sum_single (g (1, 0)), map_sum]
    refine Ideal.sum_mem _ fun q _ => ?_
    rw [← Finsupp.smul_single_one, map_smul, Algebra.smul_def, RingHom.algebraMap_toAlgebra]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem φ (key q))
end _root_.GlobalTheory
end GlobalTheory
