-- Prove2me | solution 1 for MazurTransfer.bilinear_eigenvector_twisted_equivariance
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-14T23:12:32.813305+00:00
-- url     : https://prove2.me/submissions/d2c7dc68-7586-43c3-bc01-89bf4e7d64c6

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: evaluating a covariant bilinear pairing on a character
vector yields covariance twisted by the inverse character.
Named downstream consumer: RepresentationCharacterTwist and the actual
complementary arithmetic norm quotient in the order-13 descent.
-/
import Mathlib.RepresentationTheory.Intertwining

noncomputable section
theorem solution
    (k G V W U : Type*) [Field k] [Group G]
    [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W] [AddCommGroup U] [Module k U]
    (ρ : Representation k G V) (τ : Representation k G W) (υ : Representation k G U)
    (B : V →ₗ[k] W →ₗ[k] U)
    (hB : ∀ (g : G) (v : V) (w : W), B (ρ g v) (τ g w) = υ g (B v w))
    (χ : G →* kˣ) (v : V) (hv : ∀ g : G, ρ g v = (χ g : k) • v)
    (g : G) (w : W) : B v (τ g w) = (((χ g)⁻¹ : kˣ) : k) • υ g (B v w) := by
  have h := hB g v w
  rw [hv g, map_smul, LinearMap.smul_apply] at h
  have hi := congrArg (fun z : U => ((χ g)⁻¹ : kˣ) • z) h
  simpa only [Units.smul_def, Units.val_inv_eq_inv_val,
    inv_smul_smul₀ (Units.ne_zero (χ g))] using hi

#print axioms solution
