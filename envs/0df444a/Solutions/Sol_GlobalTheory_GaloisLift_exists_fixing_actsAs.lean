-- Prove2me | solution 1 for GlobalTheory.GaloisLift.exists_fixing_actsAs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:56:08.836426+00:00
-- url     : https://prove2.me/submissions/0156498f-50bb-47ac-9e45-6600d8ab0b6b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_ExistsNotCongPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsFixingActsAsFrobeniusPowerResidue
import Theorems.Thm_GlobalTheory_GaloisLift_cong_pow_of_cong_pow_int
import Theorems.Thm_GlobalTheory_GaloisLift_lift_resAut_of_fixes
import Theorems.Thm_GlobalTheory_WeilDeligne_coe_qPow
import Theorems.Thm_GlobalTheory_WeilDeligne_deg_ineIncl
import Theorems.Thm_GlobalTheory_WeilDeligne_qPow_zero
import Theorems.Thm_GlobalTheory_WeilDeligne_unrChar_apply
import Theorems.Thm_ReciprocityTheory_Gal_exists_isFrob
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.WeilDeligne.coe_qPow
attribute [local simp] GlobalTheory.WeilDeligne.deg_ineIncl
attribute [local simp] GlobalTheory.WeilDeligne.qPow_zero
attribute [local simp] GlobalTheory.WeilDeligne.unrChar_apply



set_option autoImplicit false
open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne
open Pointwise
open GlobalTheory GlobalTheory.GaloisLift
namespace GlobalTheory.GaloisLift
theorem _root_.solution : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (_h : IsPlaceOver A w)
    (K : IntermediateField E Ω) [FiniteDimensional E K], ∀ d ∈ Dec (F := E) A, ∀ j : ℕ,
      (∀ z ∈ K, A.valuation z ≤ 1 → A.valuation (d z - z ^ (normV w ^ j)) < 1) →
      ∃ ρ : G E Ω, (∀ z ∈ K, ρ z = z) ∧ ActsAs A (normV w) (d * ρ) j 0 := by
  intro E Ω _ _ _ _ _ A w h K _ d hd j hdK
  obtain ⟨φ, hφ⟩ := exists_isFrob h
  have hφ1 : ActsAs A (normV w) φ 1 0 := actsAs_one_iff.mpr hφ
  have hpow : ∀ n : ℕ, ActsAs A (normV w) (φ ^ n) n 0 := by
    intro n
    induction n with
    | zero => exact ⟨(Dec (F := E) A).one_mem, fun x _ => by simp⟩
    | succ n ih => simpa [pow_succ] using ih.mul hφ1
  have hφj := hpow j
  set σ₀ : G E Ω := d⁻¹ * φ ^ j with hσ₀def
  have hσ₀ : σ₀ ∈ Dec (F := E) A := (Dec (F := E) A).mul_mem ((Dec (F := E) A).inv_mem hd) hφj.1
  have hK : ∀ z ∈ K, A.valuation z ≤ 1 → A.valuation (σ₀ z - z) < 1 := by
    intro z hz hz1
    rw [← valuation_apply_lt_one_iff hd, map_sub]
    have e1 : d (σ₀ z) = (φ ^ j) z := by
      rw [hσ₀def, AlgEquiv.mul_apply, mul_inv_apply]
    rw [e1]
    have h1 := hφj.2 z hz1
    simp only [pow_zero, pow_one] at h1
    exact cong_trans h1 (cong_symm (hdK z hz hz1))
  obtain ⟨ρ, hρK, hρA, hρc⟩ := lift_resAut_of_fixes E Ω A K σ₀ hσ₀ hK
  set τ : G E Ω := σ₀⁻¹ * ρ with hτdef
  have hτ : τ ∈ Dec (F := E) A := (Dec (F := E) A).mul_mem ((Dec (F := E) A).inv_mem hσ₀) hρA
  have hτc : ∀ b : Ω, IsIntegral ℤ b → A.valuation (τ b - b ^ 1) < 1 := by
    intro b hb
    rw [pow_one, ← valuation_apply_lt_one_iff hσ₀, map_sub]
    have e3 : σ₀ (τ b) = ρ b := mul_inv_apply (ρ b)
    rw [e3]
    exact hρc b hb
  have hτI : ActsAs A (normV w) τ 0 0 :=
    ⟨hτ, fun x hx => by simpa using cong_pow_of_cong_pow_int E Ω A hτ hτc x hx⟩
  refine ⟨ρ, hρK, ?_⟩
  have e2 : d * ρ = φ ^ j * τ := by
    rw [hτdef, hσ₀def]; group
  rw [e2]
  simpa using hφj.mul hτI
end GlobalTheory.GaloisLift
