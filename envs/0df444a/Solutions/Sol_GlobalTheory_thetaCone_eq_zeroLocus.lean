-- Prove2me | solution 1 for GlobalTheory.thetaCone_eq_zeroLocus
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:12:38.310543+00:00
-- url     : https://prove2.me/submissions/eed43e1a-1112-472e-a164-62f59d85e732

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsNhdsSubsetRange
import Theorems.Thm_GlobalTheory_ConeImage_exists_compact_cover
import Theorems.Thm_GlobalTheory_ConeImage_isClosed_cone
import Theorems.Thm_GlobalTheory_ConeImage_cone_eq_zeroLocus

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) → ∀ N : ℕ, 1 ≤ N → (∀ c : Fin g → Fin N, (Differentiable ℂ (fun z => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) ∧ ∀ (n n' : Fin g → ℤ) z, (fun z => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-(N : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * (fun z => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) z)) ∧ LinearIndependent ℂ (fun (c : Fin g → Fin N) (z : Fin g → ℂ) => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ))) → (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) → ∀ N : ℕ, 1 ≤ N → ∀ f : (Fin g → ℂ) → ℂ, (Differentiable ℂ f ∧ ∀ (n n' : Fin g → ℤ) z, f (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-(N : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * f z) → f ∈ Submodule.span ℂ (Set.range (fun (c : Fin g → Fin N) (z : Fin g → ℂ) => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)))) → (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) → ∀ N : ℕ, 2 ≤ N → ∀ z, ∃ f : (Fin g → ℂ) → ℂ, (Differentiable ℂ f ∧ ∀ (n n' : Fin g → ℤ) z, f (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-(N : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * f z) ∧ f z ≠ 0) → (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) → ∀ N : ℕ, 3 ≤ N → ∀ (z ξ : Fin g → ℂ) (γ : ℂ), (∀ f : (Fin g → ℂ) → ℂ, (Differentiable ℂ f ∧ ∀ (n n' : Fin g → ℤ) z, f (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-(N : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * f z) → fderiv ℂ f z ξ = γ * f z) → ξ = 0) → (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) → DiscreteTopology (periodLattice τ) ∧ Submodule.span ℝ (periodLattice τ : Set (Fin g → ℂ)) = ⊤ ∧ ∀ n n' : Fin g → ℤ, τ *ᵥ ofIntVec n + ofIntVec n' = 0 → n = 0 ∧ n' = 0) → (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) → ∀ N : ℕ, 2 ≤ N → ∀ (I : Ideal (MvPolynomial (Fin g → Fin N) ℂ)), (∀ F, F ∈ I ↔ ∀ (t : ℂ) (z : Fin g → ℂ), MvPolynomial.eval (fun c => t * theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) F = 0) → I.IsPrime ∧ ringKrullDim (MvPolynomial (Fin g → Fin N) ℂ ⧸ I) ≤ (g + 1 : ℕ)) → (∀ (A : Type) [CommRing A] [IsDomain A] [Algebra ℂ A] [Algebra.FiniteType ℂ A], ∃ (d : ℕ) (j : MvPolynomial (Fin d) ℂ →ₐ[ℂ] A) (a : A) (p : Polynomial (MvPolynomial (Fin d) ℂ)) (q : MvPolynomial (Fin d) ℂ), ringKrullDim A = d ∧ Function.Injective j ∧ j.toRingHom.Finite ∧ p.Monic ∧ Irreducible p ∧ (∀ r : Polynomial (MvPolynomial (Fin d) ℂ), r.eval₂ j.toRingHom a = 0 ↔ p ∣ r) ∧ q ≠ 0 ∧ Polynomial.C q ∈ Ideal.span {p, p.derivative} ∧ ∀ b : A, ∃ r : Polynomial (MvPolynomial (Fin d) ℂ), j q * b = r.eval₂ j.toRingHom a) → (∀ (A : Type) [CommRing A] [IsDomain A] [Algebra ℂ A] [Algebra.FiniteType ℂ A] (f : A), f ≠ 0 → IsConnected {x : A → ℂ | ∃ φ : A →ₐ[ℂ] ℂ, ⇑φ = x ∧ x f ≠ 0}) → (∀ (A : Type) [CommRing A] [IsDomain A] [Algebra ℂ A] [Algebra.FiniteType ℂ A] (f : A), f ≠ 0 → {x : A → ℂ | ∃ φ : A →ₐ[ℂ] ℂ, ⇑φ = x ∧ x 1 ≠ 0} ⊆ closure {x : A → ℂ | ∃ φ : A →ₐ[ℂ] ℂ, ⇑φ = x ∧ x f ≠ 0}) → (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) → ∀ N : ℕ, 3 ≤ N → ∀ (I : Ideal (MvPolynomial (Fin g → Fin N) ℂ)), (∀ F, F ∈ I ↔ ∀ (t : ℂ) (z : Fin g → ℂ), MvPolynomial.eval (fun c => t * theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) F = 0) → ∀ p : (Fin g → Fin N) → ℂ, (∀ F ∈ I, MvPolynomial.eval p F = 0) → ∃ (t : ℂ) (z : Fin g → ℂ), p = fun c => t * theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) := by
  intro h1 h2 h3 h4 h5 h6 h7 h8 h9 g τ hτ N hN I hI y hy
  obtain ⟨hprime, hdim⟩ := h6 g τ hτ N (by omega) I hI
  obtain ⟨d, j, a, p, q, hd, hj, -, -, -, hp, hq, hpq, hb⟩ :=
    h7 (MvPolynomial (Fin g → Fin N) ℂ ⧸ I)
  obtain ⟨h1, -⟩ := h1 g τ hτ N (by omega)
  replace h2 := h2 g τ hτ N (by omega)
  replace h3 := h3 g τ hτ N (by omega)
  replace h4 := h4 g τ hτ N hN
  set f : (Fin g → Fin N) → (Fin g → ℂ) → ℂ :=
    fun c z => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ) with hf
  have hdiff : ∀ c, Differentiable ℂ (f c) := fun c => (h1 c).1
  have h0 : ∀ z, ∃ c, f c z ≠ 0 := by
    intro z
    by_contra! h
    obtain ⟨F, hF, hFz⟩ := h3 z
    refine hFz ?_
    have := h2 F hF
    clear hF hFz
    induction this using Submodule.span_induction with
    | mem x hx => obtain ⟨c, rfl⟩ := hx; exact h c
    | zero => rfl
    | add x y _ _ hx hy => simp [hx, hy]
    | smul r x _ hx => simp [hx]
  have htan : ∀ (z ξ : Fin g → ℂ) (γ : ℂ), (∀ c, fderiv ℂ (f c) z ξ = γ * f c z) → ξ = 0 := by
    intro z ξ γ h
    refine h4 z ξ γ fun F hF => ?_
    have := h2 F hF
    clear hF
    suffices Differentiable ℂ F ∧ fderiv ℂ F z ξ = γ * F z from this.2
    induction this using Submodule.span_induction with
    | mem x hx => obtain ⟨c, rfl⟩ := hx; exact ⟨hdiff c, h c⟩
    | zero => exact ⟨differentiable_const 0, by simp⟩
    | add x y _ _ hx hy =>
      refine ⟨hx.1.add hy.1, ?_⟩
      rw [fderiv_add (hx.1 z) (hy.1 z), ContinuousLinearMap.add_apply, hx.2, hy.2, Pi.add_apply,
        mul_add]
    | smul r x _ hx =>
      refine ⟨hx.1.const_smul r, ?_⟩
      rw [fderiv_const_smul (hx.1 z), ContinuousLinearMap.smul_apply, hx.2, Pi.smul_apply,
        smul_eq_mul, smul_eq_mul]
      ring
  have hcl : IsClosed {p : (Fin g → Fin N) → ℂ |
      ∃ (t : ℂ) (z : Fin g → ℂ), p = fun c => t * f c z} := by
    obtain ⟨K, hK, hK'⟩ := ConeImage.exists_compact_cover τ (h5 g τ hτ).2.1
    convert ConeImage.isClosed_cone (f := fun z c => f c z)
      (continuous_pi fun c => (hdiff c).continuous)
      (fun z hz => by obtain ⟨c, hc⟩ := h0 z; exact hc (congrFun hz c)) hK using 1
    ext p
    constructor
    · rintro ⟨t, z, rfl⟩
      obtain ⟨w, hw, n, n', rfl⟩ := hK' z
      refine ⟨t * eC (-(N : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ w)), w, hw, ?_⟩
      ext c
      have : f c (w + τ *ᵥ ofIntVec n + ofIntVec n') = _ * f c w := (h1 c).2 n n' w
      rw [this, Pi.smul_apply, smul_eq_mul, mul_assoc]
    · rintro ⟨t, z, -, rfl⟩
      exact ⟨t, z, rfl⟩
  refine ConeImage.cone_eq_zeroLocus hdiff h0 htan hcl I hI (d := d) ?_ j hj a p q hq
    ((hp p).mpr dvd_rfl) hpq hb (h8 _) (h9 _) y hy
  rw [hd] at hdim
  rw [Module.finrank_fin_fun]
  exact_mod_cast hdim
end GlobalTheory
