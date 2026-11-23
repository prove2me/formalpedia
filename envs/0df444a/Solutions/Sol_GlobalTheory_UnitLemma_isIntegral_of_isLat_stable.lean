-- Prove2me | solution 1 for GlobalTheory.UnitLemma.isIntegral_of_isLat_stable
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:32:54.4443+00:00
-- url     : https://prove2.me/submissions/3805eca8-6ef3-4bf5-9261-08edef802ace

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_KappaSumZeroAndStableSumMulZeroOfNotIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
open GlobalTheory GlobalTheory.UnitLemma
open Polynomial
namespace GlobalTheory.UnitLemma
namespace _root_.GlobalTheory.UnitLemma
theorem _root_.solution {O E A : Type} [CommRing O] [Field E] [CommRing A] [Algebra O A]
    [Algebra E A] (L : Submodule O A) (hL : _root_.GlobalTheory.UnitLemma.IsLat O E L) (g : A) (hg : ∀ y ∈ L, g * y ∈ L) :
    IsIntegral O g := by
  obtain ⟨hfg, hspan⟩ := hL
  haveI : Module.Finite O L := Module.Finite.iff_fg.mpr hfg
  let f : Module.End O L := (LinearMap.mulLeft O g).restrict hg
  have hpow : ∀ (n : ℕ) (y : L), ((f ^ n) y : A) = g ^ n * y := by
    intro n
    induction n with
    | zero => intro y; simp
    | succ n ih => intro y; rw [pow_succ', Module.End.mul_apply, pow_succ', mul_assoc, ← ih]; rfl
  have hact : ∀ (q : O[X]) (y : L), ((aeval f q) y : A) = aeval g q * y := by
    intro q y
    induction q using Polynomial.induction_on' with
    | add p q hp' hq' => simp [add_mul, hp', hq']
    | monomial n c => simp [aeval_monomial, hpow, Algebra.smul_def, mul_assoc]
  obtain ⟨p, hmon, hp⟩ := LinearMap.exists_monic_and_aeval_eq_zero O f
  have hzero : ∀ y ∈ Submodule.span E (L : Set A), aeval g p * y = 0 := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem x hx => rw [← hact p ⟨x, hx⟩, hp]; rfl
    | zero => simp
    | add x y _ _ hx hy => rw [mul_add, hx, hy, add_zero]
    | smul e x _ hx => rw [mul_smul_comm, hx, smul_zero]
  refine ⟨p, hmon, ?_⟩
  have h1 := hzero 1 (hspan ▸ Submodule.mem_top)
  rw [mul_one] at h1
  rwa [← aeval_def]
end _root_.GlobalTheory.UnitLemma
end GlobalTheory.UnitLemma
