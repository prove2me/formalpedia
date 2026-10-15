-- Prove2me | solution 1 for MazurTransfer.trivial_line_of_invariant_finrank_one
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-14T20:50:42.552618+00:00
-- url     : https://prove2.me/submissions/9b68b8db-1670-412d-a6ba-606201562323

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: a one-dimensional invariant subspace is the image of an
injective equivariant map from the trivial scalar representation.
Named downstream consumer: Order13ActualNormGaloisTrivialLine.
-/
import Mathlib.RepresentationTheory.Invariants

noncomputable section
theorem solution
    (k G V : Type*) [Field k] [Group G] [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) [Module.Finite k V]
    (h : Module.finrank k ρ.invariants = 1) :
    ∃ f : Representation.IntertwiningMap (Representation.trivial k G k) ρ,
      Function.Injective f ∧ LinearMap.range f.toLinearMap = ρ.invariants := by
  let e : k ≃ₗ[k] ρ.invariants := LinearEquiv.ofFinrankEq k ρ.invariants
    (by simpa only [Module.finrank_self] using h.symm)
  let l : k →ₗ[k] V := ρ.invariants.subtype.comp e.toLinearMap
  let f : Representation.IntertwiningMap (Representation.trivial k G k) ρ :=
    l.intertwiningMap_of_isIntertwiningMap _ _ (by
      intro g x
      change (e x).val = ρ g (e x).val
      exact ((e x).property g).symm)
  refine ⟨f, ?_, ?_⟩
  · intro a b hab
    apply e.injective
    exact Subtype.ext hab
  · ext v
    constructor
    · rintro ⟨a, rfl⟩
      exact (e a).property
    · intro hv
      refine ⟨e.symm ⟨v, hv⟩, ?_⟩
      exact congrArg Subtype.val (e.apply_symm_apply ⟨v, hv⟩)

#print axioms solution
