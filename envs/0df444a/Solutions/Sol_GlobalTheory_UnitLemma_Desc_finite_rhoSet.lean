-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Desc.finite_rhoSet
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:50:39.084151+00:00
-- url     : https://prove2.me/submissions/294cf2d2-fd0e-4e48-aaf9-e7057f5801ac

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DltEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FiniteIntegralClosureOfSeparableInvolutionAlgebrStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsInjectiveTorusClassesOfIdempotentDecomposiStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_RhoPowLowerBoundSwappedPairs
import Theorems.Thm_GlobalTheory_UnitLemma_Desc_finite_between
import Theorems.Thm_P2M_RH_GlobalTheory_UnitLemma_Desc_isIntegral_sigma_9c63cf01f25c1776
import Theorems.Thm_GlobalTheory_T_finite_integralClosure_of_separable_involution_algebra


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc
namespace GlobalTheory.UnitLemma.Desc
theorem _root_.solution (K : UQ) (B : InvAlg K) (hsep : B.P.Separable) (a : K.O) (ha : K.Small a) (k : ℕ) :
    Finite {c : B.T ⧸ (intUnits K.O B.A).subgroupOf B.T //
      IsIntegral K.O ((((Quotient.out c : B.T) : B.Aˣ)⁻¹ : B.Aˣ) * algebraMap K.O B.A a ^ k : B.A)} := by
  classical
  set R : Submodule K.O B.A := (integralClosure K.O B.A).toSubmodule with hR
  have hRfg : R.FG := by
    have := GlobalTheory.T.finite_integralClosure_of_separable_involution_algebra K B hsep
    have h2 := Module.Finite.fg_top (R := K.O) (M := integralClosure K.O B.A)
    have h3 := h2.map (integralClosure K.O B.A).val.toLinearMap
    convert h3 using 1
    ext x; simp [hR]
  have ha0 : a ^ (2 * k) ≠ 0 := pow_ne_zero _ ha.1
  have hfin := finite_between K.O B.A R hRfg (a ^ (2 * k)) ha0
  have hσα : B.σ (algebraMap K.O B.A a) = algebraMap K.O B.A a := by
    rw [IsScalarTower.algebraMap_apply K.O K.E B.A, B.σ_alg, ha.2.2]
  have hαu : IsUnit (algebraMap K.O B.A a) := by
    rw [IsScalarTower.algebraMap_apply K.O K.E B.A]
    refine IsUnit.map _ (isUnit_iff_ne_zero.2 ?_)
    intro h0
    exact ha.1 ((injective_iff_map_eq_zero (algebraMap K.O K.E)).1 (IsFractionRing.injective K.O K.E) a h0)
  set αu : B.Aˣ := hαu.unit with hαudef
  have hαeq : (αu : B.A) = algebraMap K.O B.A a := hαu.unit_spec
  have hmem : ∀ (u : B.A) (y : B.A), y ∈ mulLat K.O u R ↔ ∃ r ∈ R, u * r = y := by
    intro u y
    simp only [mulLat, Submodule.mem_map, LinearMap.mulLeft_apply]

  have hσinv : ∀ t : B.T, B.σ ((((t : B.Aˣ)⁻¹ : B.Aˣ)) : B.A) = ((t : B.Aˣ) : B.A) := by
    intro t
    have ht : ((t : B.Aˣ) : B.A) * B.σ ((t : B.Aˣ) : B.A) = 1 := t.2
    have h1 : B.σ ((((t : B.Aˣ)⁻¹ : B.Aˣ)) : B.A) * B.σ ((t : B.Aˣ) : B.A) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    calc B.σ ((((t : B.Aˣ)⁻¹ : B.Aˣ)) : B.A)
        = B.σ ((((t : B.Aˣ)⁻¹ : B.Aˣ)) : B.A) * (((t : B.Aˣ) : B.A) * B.σ ((t : B.Aˣ) : B.A)) := by rw [ht, mul_one]
      _ = ((t : B.Aˣ) : B.A) * (B.σ ((((t : B.Aˣ)⁻¹ : B.Aˣ)) : B.A) * B.σ ((t : B.Aˣ) : B.A)) := by ring
      _ = ((t : B.Aˣ) : B.A) := by rw [h1, mul_one]
  let φ : {c : B.T ⧸ (intUnits K.O B.A).subgroupOf B.T //
      IsIntegral K.O ((((Quotient.out c : B.T) : B.Aˣ)⁻¹ : B.Aˣ) * algebraMap K.O B.A a ^ k : B.A)} →
      {N : Submodule K.O B.A // N ≤ R ∧ ∀ x ∈ R, a ^ (2 * k) • x ∈ N} := fun c =>
    ⟨mulLat K.O ((((Quotient.out c.1 : B.T) : B.Aˣ)⁻¹ : B.Aˣ) * algebraMap K.O B.A a ^ k : B.A) R, by
      intro y hy
      obtain ⟨r, hr, rfl⟩ := (hmem _ _).1 hy
      exact c.2.mul hr, by
      intro x hx
      set t : B.T := Quotient.out c.1
      have h2 : IsIntegral K.O (((t : B.Aˣ) : B.A) * algebraMap K.O B.A a ^ k) := by
        have := isIntegral_sigma K B _ c.2
        rwa [map_mul, map_pow, hσα, hσinv] at this
      refine (hmem _ _).2 ⟨((t : B.Aˣ) : B.A) * algebraMap K.O B.A a ^ k * x, h2.mul hx, ?_⟩
      rw [Algebra.smul_def, map_pow, pow_mul]
      have : (((t : B.Aˣ)⁻¹ : B.Aˣ) : B.A) * ((t : B.Aˣ) : B.A) = 1 := Units.inv_mul _
      linear_combination (algebraMap K.O B.A a ^ k * algebraMap K.O B.A a ^ k * x) * this⟩
  refine Finite.of_injective φ ?_
  rintro ⟨c, hc⟩ ⟨c', hc'⟩ h
  have hN := congrArg Subtype.val h
  simp only [φ] at hN
  set t : B.T := Quotient.out c with htdef
  set t' : B.T := Quotient.out c' with ht'def
  have h1R : (1 : B.A) ∈ R := (integralClosure K.O B.A).one_mem

  have key : ∀ (s s' : B.T), mulLat K.O ((((s : B.Aˣ)⁻¹ : B.Aˣ) : B.A) * algebraMap K.O B.A a ^ k) R =
      mulLat K.O ((((s' : B.Aˣ)⁻¹ : B.Aˣ) : B.A) * algebraMap K.O B.A a ^ k) R →
      IsIntegral K.O ((((s : B.Aˣ)⁻¹ * (s' : B.Aˣ) : B.Aˣ)) : B.A) := by
    intro s s' hss
    have : (((s : B.Aˣ)⁻¹ : B.Aˣ) : B.A) * algebraMap K.O B.A a ^ k ∈
        mulLat K.O ((((s' : B.Aˣ)⁻¹ : B.Aˣ) : B.A) * algebraMap K.O B.A a ^ k) R := by
      rw [← hss]; exact (hmem _ _).2 ⟨1, h1R, mul_one _⟩
    obtain ⟨r, hr, hr'⟩ := (hmem _ _).1 this
    have h1 : ((s' : B.Aˣ) : B.A) * (((s' : B.Aˣ)⁻¹ : B.Aˣ) : B.A) = 1 := Units.mul_inv _
    have h2 : algebraMap K.O B.A a ^ k * (((αu ^ k)⁻¹ : B.Aˣ) : B.A) = 1 := by
      rw [← hαeq, ← Units.val_pow_eq_pow_val, Units.mul_inv]
    have : ((((s : B.Aˣ)⁻¹ * (s' : B.Aˣ) : B.Aˣ)) : B.A) = r := by
      rw [Units.val_mul]
      linear_combination -(((s' : B.Aˣ) : B.A) * (((αu ^ k)⁻¹ : B.Aˣ) : B.A) * hr' - r * algebraMap K.O B.A a ^ k * (((αu ^ k)⁻¹ : B.Aˣ) : B.A) * h1 - r * h2 + (((s : B.Aˣ)⁻¹ : B.Aˣ) : B.A) * ((s' : B.Aˣ) : B.A) * h2)
    rw [this]; exact hr
  have hA := key t t' hN
  have hB := key t' t hN.symm
  have hmemU : (t : B.Aˣ)⁻¹ * (t' : B.Aˣ) ∈ intUnits K.O B.A := by
    refine ⟨hA, ?_⟩
    have : ((t : B.Aˣ)⁻¹ * (t' : B.Aˣ))⁻¹ = ((t' : B.Aˣ)⁻¹ * (t : B.Aˣ)) := by
      rw [mul_inv_rev, inv_inv]
    rw [this]; exact hB
  have : c = c' := by
    rw [← QuotientGroup.out_eq' c, ← QuotientGroup.out_eq' c', QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simpa using hmemU
  subst this
  rfl
end GlobalTheory.UnitLemma.Desc
