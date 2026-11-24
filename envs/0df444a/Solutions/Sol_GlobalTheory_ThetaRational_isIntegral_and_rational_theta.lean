-- Prove2me | solution 1 for GlobalTheory.ThetaRational.isIntegral_and_rational_theta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:21:10.153861+00:00
-- url     : https://prove2.me/submissions/d5a4d1a1-0d74-4d60-8fd5-181a149be143

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsIntegralAndRationalTheta
import Theorems.Thm_GlobalTheory_ThetaRational_growth
import Theorems.Thm_GlobalTheory_ThetaRational_exists_analytic_descent
import Theorems.Thm_GlobalTheory_ThetaRational_isIntegral_and_rational
import Theorems.Thm_GlobalTheory_ThetaRational_exists_compact_reps

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real ContDiff
open GlobalTheory GlobalTheory.ThetaRational
namespace GlobalTheory.ThetaRational
theorem _root_.solution :
    (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin
        g) → ∀ N : ℕ, 1 ≤ N → (∀ c : Fin g → Fin N, (Differentiable ℂ (fun z => theta (fun i => ((c
        i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) ∧ ∀ (n n'
        : Fin g → ℤ) z, (fun z => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) •
        τ)) (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-(N : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) /
        2 + ofIntVec n ⬝ᵥ z)) * (fun z => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N
        : ℂ) • τ)) z)) ∧ LinearIndependent ℂ (fun (c : Fin g → Fin N) (z
        : Fin g → ℂ) => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ))) → (∀ (g
        : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) → ∀ N : ℕ, 1 ≤ N → ∀ f : (Fin g →
        ℂ) → ℂ, (Differentiable ℂ f ∧ ∀ (n n' : Fin g → ℤ) z, f (z + τ *ᵥ ofIntVec n + ofIntVec
        n') = eC (-(N : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ
        z)) * f z) → f ∈ Submodule.span ℂ (Set.range (fun (c : Fin g → Fin N) (z
        : Fin g → ℂ) => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) •
        τ)))) → (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin
        g) → ∀ N : ℕ, 2 ≤ N → ∀ z, ∃ f : (Fin g → ℂ) → ℂ, (Differentiable ℂ f ∧ ∀ (n n'
        : Fin g → ℤ) z, f (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-(N : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ
        ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * f z) ∧ f z ≠ 0) → (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin
        g) ℂ), τ ∈ SiegelH (Fin g) → ∀ N : ℕ, 3 ≤ N → ∀ (z z' : Fin g → ℂ) (γ : ℂ), (∀ f : (Fin g →
        ℂ) → ℂ, (Differentiable ℂ f ∧ ∀ (n n' : Fin g → ℤ) z, f (z + τ *ᵥ ofIntVec n + ofIntVec
        n') = eC (-(N : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ
        z)) * f z) → f z = γ * f z') → z - z' ∈ periodLattice τ) → (∀ (g : ℕ) (τ : Matrix (Fin
        g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) → ∀ N : ℕ, 3 ≤ N → ∀ (z ξ : Fin g → ℂ) (γ
        : ℂ), (∀ f : (Fin g → ℂ) → ℂ, (Differentiable ℂ f ∧ ∀ (n n' : Fin g → ℤ) z, f (z + τ *ᵥ
        ofIntVec n + ofIntVec n') = eC (-(N : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n
        ⬝ᵥ z)) * f z) → fderiv ℂ f z ξ = γ * f z) → ξ = 0) → (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin
        g) ℂ), τ ∈ SiegelH (Fin g) → DiscreteTopology (periodLattice
        τ) ∧ Submodule.span ℝ (periodLattice τ : Set (Fin g →
        ℂ)) = ⊤ ∧ ∀ n n' : Fin g → ℤ, τ *ᵥ ofIntVec n + ofIntVec n' = 0 → n = 0 ∧ n' = 0) → (∀ (g
        : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) → ∀ N : ℕ, 2 ≤ N → ∀ (I
        : Ideal (MvPolynomial (Fin g → Fin N) ℂ)), (∀ F, F ∈ I ↔ ∀ (t : ℂ) (z
        : Fin g → ℂ), MvPolynomial.eval (fun c => t * theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N
        : ℂ) • z) ((N : ℂ) • τ)) F = 0) → I.IsPrime ∧ ringKrullDim (MvPolynomial (Fin g → Fin N) ℂ ⧸
        I) ≤ (g + 1 : ℕ)) → (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin
        g) → ∀ N : ℕ, 3 ≤ N → ∀ (I : Ideal (MvPolynomial (Fin g → Fin N) ℂ)), (∀ F, F ∈ I ↔ ∀ (t
        : ℂ) (z : Fin g → ℂ), MvPolynomial.eval (fun c => t * theta (fun i => ((c i : ℕ)
        : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) F = 0) → ∀ p : (Fin g → Fin
        N) → ℂ, (∀ F ∈ I, MvPolynomial.eval p F = 0) → ∃ (t : ℂ) (z
        : Fin g → ℂ), p = fun c => t * theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ)
        • τ)) → (∀ (A : Type) [CommRing A] [IsDomain A] [Algebra ℂ A] [Algebra.FiniteType ℂ A], ∃ (d
        : ℕ) (j : MvPolynomial (Fin d) ℂ →ₐ[ℂ] A) (a : A) (p : Polynomial (MvPolynomial (Fin d)
        ℂ)) (q : MvPolynomial (Fin
        d) ℂ), ringKrullDim A = d ∧ Function.Injective j ∧ j.toRingHom.Finite ∧ p.Monic ∧ Irreducible p ∧ (∀ r : Polynomial (MvPolynomial
        (Fin d) ℂ), r.eval₂ j.toRingHom a = 0 ↔ p ∣ r) ∧ q ≠ 0 ∧ Polynomial.C q ∈ Ideal.span {p,
        p.derivative} ∧ ∀ b : A, ∃ r : Polynomial (MvPolynomial (Fin d)
        ℂ), j q * b = r.eval₂ j.toRingHom a) → (∀ (d m : ℕ) (p : Polynomial (MvPolynomial (Fin d)
        ℂ)) (q : MvPolynomial (Fin d) ℂ) (φ : (Fin d → ℂ) × ℂ → ℂ) (C
        : ℝ), p.Monic → q ≠ 0 → Polynomial.C q ∈ Ideal.span {p, p.derivative} → (∀ z ∈ {z : (Fin d →
        ℂ) × ℂ | MvPolynomial.eval z.1 q ≠ 0 ∧ (p.map (MvPolynomial.eval
        z.1)).eval z.2 = 0}, ∃ F : (Fin d → ℂ) × ℂ → ℂ, AnalyticAt ℂ F z ∧ ∀ᶠ w in 𝓝[{z : (Fin d →
        ℂ) × ℂ | MvPolynomial.eval z.1 q ≠ 0 ∧ (p.map (MvPolynomial.eval
        z.1)).eval z.2 = 0}] z, φ w = F w) → (∀ z ∈ {z : (Fin d →
        ℂ) × ℂ | MvPolynomial.eval z.1 q ≠ 0 ∧ (p.map (MvPolynomial.eval
        z.1)).eval z.2 = 0}, ‖φ z‖ ≤ C * (1 + ‖z.1‖) ^ m) → (∃ s : Polynomial (MvPolynomial (Fin d)
        ℂ), s.Monic ∧ ∀ z ∈ {z : (Fin d → ℂ) × ℂ | MvPolynomial.eval z.1 q ≠ 0 ∧ (p.map
        (MvPolynomial.eval z.1)).eval z.2 = 0}, (s.map (MvPolynomial.eval z.1)).eval (φ
        z) = 0) ∧ ∃ r : Polynomial (MvPolynomial (Fin d) ℂ), ∀ z ∈ {z : (Fin d →
        ℂ) × ℂ | MvPolynomial.eval z.1 q ≠ 0 ∧ (p.map (MvPolynomial.eval
        z.1)).eval z.2 = 0}, (p.derivative.map (MvPolynomial.eval z.1)).eval z.2 * φ z = (r.map
        (MvPolynomial.eval z.1)).eval z.2) → (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin
        g) ℂ), τ ∈ SiegelH (Fin g) → ∀ N : ℕ, 3 ≤ N → ∀ (d : ℕ) (f : (Fin g →
        ℂ) → ℂ), (Differentiable ℂ f ∧ ∀ (n n' : Fin g → ℤ) z, f (z + τ *ᵥ ofIntVec n + ofIntVec
        n') = eC (-((N * d : ℕ) : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ
        z)) * f z) → IsIntegral (Algebra.adjoin ℂ (Set.range fun (c : Fin g → Fin N) (p : ℂ × (Fin g
        → ℂ)) => p.1 * theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • p.2) ((N : ℂ) •
        τ))) (fun p : ℂ × (Fin g → ℂ) => p.1 ^ d * f p.2) ∧ ∃ a ∈ (Algebra.adjoin ℂ (Set.range
        fun (c : Fin g → Fin N) (p : ℂ × (Fin g → ℂ)) => p.1 * theta (fun i => ((c i : ℕ)
        : ℝ) / N) 0 ((N : ℂ) • p.2) ((N : ℂ) • τ))), ∃ b ∈ (Algebra.adjoin ℂ (Set.range fun (c
        : Fin g → Fin N) (p : ℂ × (Fin g → ℂ)) => p.1 * theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N
        : ℂ) • p.2) ((N : ℂ) • τ))), b ≠ 0 ∧ b * (fun p : ℂ × (Fin g →
        ℂ) => p.1 ^ d * f p.2) = a) := by
  intro hbas hspan hnz hsep htan hlat _ hcl hnoeth hrat g τ hτ N hN d f hf
  set u : (Fin g → Fin N) → (Fin g → ℂ) → ℂ := fun c z =>
    theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ) with hu
  set θ : (Fin g → ℂ) → (Fin g → Fin N) → ℂ := fun z c => u c z with hθ
  have hb := (hbas g τ hτ N (by omega)).1
  have hud : ∀ c, Differentiable ℂ (u c) := fun c => (hb c).1
  have hθd : Differentiable ℂ θ := differentiable_pi.2 hud
  have hsp := hspan g τ hτ N (by omega)
  have hN0 : ∀ z, θ z ≠ 0 := by
    intro z h0
    obtain ⟨f, hf, hf0⟩ := hnz g τ hτ N (by omega) z
    apply hf0
    have h1 := hsp f hf
    clear hf0 hf
    induction h1 using Submodule.span_induction with
    | mem x hx => obtain ⟨c, rfl⟩ := hx; exact congrFun h0 c
    | zero => rfl
    | add x y _ _ hx hy => simp [hx, hy]
    | smul r x _ hx => simp [hx]
  have hS : ∀ (z z' : Fin g → ℂ) (γ : ℂ), θ z = γ • θ z' →
      z - z' ∈ (periodLattice τ : Set (Fin g → ℂ)) := by
    intro z z' γ h0
    refine hsep g τ hτ N hN z z' γ fun f hf => ?_
    have h1 := hsp f hf
    clear hf
    induction h1 using Submodule.span_induction with
    | mem x hx => obtain ⟨c, rfl⟩ := hx; exact congrFun h0 c
    | zero => simp
    | add x y _ _ hx hy => simp [hx, hy, mul_add]
    | smul r x _ hx => simp [hx, mul_left_comm]
  have hT : ∀ (z ξ : Fin g → ℂ) (γ : ℂ), fderiv ℂ θ z ξ = γ • θ z → ξ = 0 := by
    intro z ξ γ h0
    refine htan g τ hτ N hN z ξ γ fun f hf => ?_
    have h1 := hsp f hf
    clear hf
    suffices Differentiable ℂ f ∧ fderiv ℂ f z ξ = γ * f z from this.2
    induction h1 using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨c, rfl⟩ := hx
      refine ⟨hud c, ?_⟩
      rw [hθ, fderiv_pi fun c => hud c z] at h0
      exact congrFun h0 c
    | zero => exact ⟨differentiable_const 0, by simp⟩
    | add x y _ _ hx hy =>
      refine ⟨hx.1.add hy.1, ?_⟩
      rw [fderiv_add (hx.1 z) (hy.1 z)]
      simp [hx.2, hy.2, mul_add]
    | smul r x _ hx =>
      refine ⟨hx.1.const_smul r, ?_⟩
      rw [fderiv_const_smul (hx.1 z)]
      simp [hx.2, mul_left_comm]
  have hL : ∀ l ∈ (periodLattice τ : Set (Fin g → ℂ)), ∃ κ : (Fin g → ℂ) → ℂ, Continuous κ ∧
      ∀ z, κ z ≠ 0 ∧ θ (z + l) = κ z • θ z ∧ f (z + l) = κ z ^ d * f z := by
    rintro _ ⟨n, n', rfl⟩
    refine ⟨fun z => eC (-(N : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)), ?_,
      fun z => ⟨Complex.exp_ne_zero _, funext fun c => ?_, ?_⟩⟩
    · unfold eC
      fun_prop
    · rw [← add_assoc]
      exact (hb c).2 n n' z
    · rw [← add_assoc, hf.2 n n' z]
      congr 1
      simp only [eC]
      rw [← Complex.exp_nat_mul]
      congr 1
      push_cast
      ring
  obtain ⟨K, hK, hP⟩ := exists_compact_reps τ (hlat g τ hτ).2.1
  obtain ⟨C, hC, hgr⟩ := growth hK hθd.continuous hf.1.continuous hN0 hP hL
  obtain ⟨c₀, hc₀⟩ := Function.ne_iff.1 (hN0 0)
  have hf1 := hf.1
  refine isIntegral_and_rational hnoeth hrat
    (u := fun c (p : ℂ × (Fin g → ℂ)) => p.1 * u c p.2) (h := fun p => p.1 ^ d * f p.2)
    (fun c => differentiable_fst.mul ((hud c).comp differentiable_snd)) (by fun_prop)
    (fun y hy => ?_) (c₀ := c₀) (fun h0 => hc₀ ?_)
    (exists_analytic_descent hK hθd hf.1 hN0 hP hL hS hT) hC hgr
  · obtain ⟨t, z, h1⟩ := hcl g τ hτ N hN
      (⨅ e : ℂ × (Fin g → ℂ), RingHom.ker (MvPolynomial.eval fun c => e.1 * u c e.2))
      (fun F => by simp only [Ideal.mem_iInf, RingHom.mem_ker, Prod.forall]; rfl) y
      (fun F hF => hy F (by simpa only [Ideal.mem_iInf, RingHom.mem_ker] using hF))
    exact ⟨(t, z), h1⟩
  · simpa using congrFun h0 (1, 0)
end GlobalTheory.ThetaRational
