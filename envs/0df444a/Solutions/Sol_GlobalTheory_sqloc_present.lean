-- Prove2me | solution 1 for GlobalTheory.sqloc_present
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:33:53.971835+00:00
-- url     : https://prove2.me/submissions/4b7775cb-6d86-4c1a-976e-3964acd5d6f3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsPresentationSquareAtPointOfLocalFactor

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (k A : Type) [CommRing k] [CommRing A] [Algebra k A] (ε : A →ₐ[k] k) (e : A), ε e = 1 → IsIdempotentElem e → (∃ (s : ℕ) (φ : MvPolynomial (Fin s) k →ₐ[k] (A ⧸ Ideal.span {1 - e})) (g : Fin s → MvPolynomial (Fin s) k), Function.Surjective φ ∧ RingHom.ker φ = Ideal.span (Set.range g)) → ∀ (r : ℕ) (a : Fin r → A), Function.Surjective (MvPolynomial.aeval a : MvPolynomial (Fin r) k →ₐ[k] A) → ∃ (s : ℕ) (y : Fin s → A) (g : Fin s ⊕ Fin r → MvPolynomial (Fin s ⊕ Fin r) k), (∀ i, MvPolynomial.aeval (Sum.elim y a) (g i) = 0) ∧ RingHom.ker (MvPolynomial.aeval (Sum.elim y a) : MvPolynomial (Fin s ⊕ Fin r) k →ₐ[k] A) ≤ Ideal.span (Set.range g) ⊔ RingHom.ker (ε.comp (MvPolynomial.aeval (Sum.elim y a) : MvPolynomial (Fin s ⊕ Fin r) k →ₐ[k] A)) * RingHom.ker (MvPolynomial.aeval (Sum.elim y a) : MvPolynomial (Fin s ⊕ Fin r) k →ₐ[k] A) := by
  intro k A _ _ _ ε e he hidem ⟨s, φ, g', hφ, hker⟩ r a ha
  classical
  choose y hy using fun i : Fin s => Ideal.Quotient.mk_surjective (I := Ideal.span {1 - e}) (φ (MvPolynomial.X i))
  choose h hh using fun j : Fin r => hφ (Ideal.Quotient.mk (Ideal.span {1 - e}) (a j))
  set Ψ : MvPolynomial (Fin s ⊕ Fin r) k →ₐ[k] A := MvPolynomial.aeval (Sum.elim y a) with hΨ
  have hΨsurj : Function.Surjective Ψ := by
    intro x
    obtain ⟨p, hp⟩ := ha x
    refine ⟨MvPolynomial.rename Sum.inr p, ?_⟩
    rw [hΨ, MvPolynomial.aeval_rename, Sum.elim_comp_inr]
    exact hp
  obtain ⟨u, hu⟩ := hΨsurj e
  set κ : MvPolynomial (Fin s ⊕ Fin r) k →ₐ[k] MvPolynomial (Fin s) k :=
    MvPolynomial.aeval (Sum.elim MvPolynomial.X h) with hκdef
  have hκ : (Ideal.Quotient.mkₐ k (Ideal.span {1 - e})).comp Ψ = φ.comp κ := by
    apply MvPolynomial.algHom_ext
    intro i
    rcases i with i | j
    · simp [hΨ, hκdef, hy]
    · simp [hΨ, hκdef, hh]
  have hκF : ∀ F, Ideal.Quotient.mk (Ideal.span {1 - e}) (Ψ F) = φ (κ F) := by
    intro F
    have := congrArg (fun f => f F) hκ
    simpa using this
  let G : Fin s ⊕ Fin r → MvPolynomial (Fin s ⊕ Fin r) k :=
    Sum.elim (fun i => MvPolynomial.rename Sum.inl (g' i))
      (fun j => MvPolynomial.X (Sum.inr j) - MvPolynomial.rename Sum.inl (h j))
  have hκr : ∀ p, κ (MvPolynomial.rename Sum.inl p) = p := by
    intro p
    rw [hκdef, MvPolynomial.aeval_rename, Sum.elim_comp_inl, MvPolynomial.aeval_X_left_apply]
  have hκX : ∀ j, κ (MvPolynomial.X (Sum.inr j)) = h j := by
    intro j
    rw [hκdef, MvPolynomial.aeval_X, Sum.elim_inr]
  have hg'ker : ∀ i, φ (g' i) = 0 := by
    intro i
    have : g' i ∈ RingHom.ker φ := hker ▸ Ideal.subset_span ⟨i, rfl⟩
    simpa using this
  have hΨG : ∀ i, Ideal.Quotient.mk (Ideal.span {1 - e}) (Ψ (G i)) = 0 := by
    intro i
    rw [hκF]
    rcases i with i | j
    · simp only [G, Sum.elim_inl, hκr, hg'ker]
    · simp only [G, Sum.elim_inr, map_sub, hκr, hκX, sub_self, map_zero]
  have hΨuG : ∀ i, Ψ (u * G i) = 0 := by
    intro i
    have hm : Ψ (G i) ∈ Ideal.span {1 - e} := Ideal.Quotient.eq_zero_iff_mem.mp (hΨG i)
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hm
    rw [map_mul, hu, ← hc]
    have h0 : e * (1 - e) = 0 := by rw [mul_sub, mul_one, hidem.eq, sub_self]
    calc e * (c * (1 - e)) = c * (e * (1 - e)) := by ring
      _ = 0 := by rw [h0, mul_zero]
  refine ⟨s, y, fun i => u * G i, hΨuG, ?_⟩
  rw [← hΨ]
  intro F hF
  rw [RingHom.mem_ker] at hF

  have hFG : F ∈ Ideal.span (Set.range G) := by
    have hq : (Ideal.Quotient.mkₐ k (Ideal.span (Set.range G))).comp
        ((MvPolynomial.rename Sum.inl).comp κ) = Ideal.Quotient.mkₐ k (Ideal.span (Set.range G)) := by
      apply MvPolynomial.algHom_ext
      intro i
      rcases i with i | j
      · simp only [AlgHom.comp_apply, hκdef, MvPolynomial.aeval_X, Sum.elim_inl,
          MvPolynomial.rename_X]
      · simp only [AlgHom.comp_apply, hκX, Ideal.Quotient.mkₐ_eq_mk]
        rw [Ideal.Quotient.eq]
        rw [← neg_sub, neg_mem_iff]
        exact Ideal.subset_span ⟨Sum.inr j, rfl⟩
    have h1 : F - MvPolynomial.rename Sum.inl (κ F) ∈ Ideal.span (Set.range G) := by
      have := congrArg (fun f => f F) hq
      simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk] at this
      rw [← neg_sub, neg_mem_iff]
      exact Ideal.Quotient.eq.mp this
    have hmem : κ F ∈ Ideal.span (Set.range g') := by
      rw [← hker, RingHom.mem_ker, ← hκF, hF, map_zero]
    have h2 : MvPolynomial.rename Sum.inl (κ F) ∈ Ideal.span (Set.range G) := by
      have := Ideal.mem_map_of_mem (MvPolynomial.rename (R := k) (Sum.inl : Fin s → Fin s ⊕ Fin r)) hmem
      rw [Ideal.map_span] at this
      refine Ideal.span_mono ?_ this
      rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
      exact ⟨Sum.inl i, rfl⟩
    have := Ideal.add_mem _ h1 h2
    simpa using this
  have hsplit : F = u * F + (1 - u) * F := by ring
  rw [hsplit]
  refine Submodule.add_mem_sup ?_ ?_
  · obtain ⟨c, hc⟩ := (Ideal.mem_span_range_iff_exists_fun).mp hFG
    refine (Ideal.mem_span_range_iff_exists_fun).mpr ⟨c, ?_⟩
    rw [← hc, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  · apply Ideal.mul_mem_mul
    · rw [RingHom.mem_ker]
      simp [hu, he]
    · exact hF
end GlobalTheory
