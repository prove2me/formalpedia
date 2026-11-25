-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Reg.exists_unique_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:05:55.557706+00:00
-- url     : https://prove2.me/submissions/df1fdeca-eb59-4698-bb69-90297a789338

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_FiniteMinimalPrimes
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ConeChart
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterPCProof
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_SncResolutionRegularLocalRing
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_Reg_exists_clear
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_PB_VertClose_symm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Cmp.SncRes GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Reg
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Cmp
namespace GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Reg
theorem _root_.solution (σ : Type) (Ω : Type) [Field Ω] [CharZero Ω] (C : Type) [CommRing C] [Algebra ℚ C]
    (u : σ → Ω) (t : σ → C) (hker : ∀ g : MvPolynomial σ ℚ, aeval u g = 0 → aeval t g = 0)
    (F : MvPolynomial σ ℚ) (hF : aeval u F ≠ 0) (hunit : IsUnit (aeval t F : C))
    (S : Subalgebra ℚ Ω) (hS : S = Algebra.adjoin ℚ (insert (aeval u F)⁻¹ (Set.range u))) (hu : ∀ q, u q ∈ S) :
    ∃ Φ : S →ₐ[ℚ] C, (∀ q, Φ ⟨u q, hu q⟩ = t q) ∧
      ∀ Φ' : S →ₐ[ℚ] C, (∀ q, Φ' ⟨u q, hu q⟩ = t q) → Φ' = Φ := by
  classical
  obtain ⟨b, hb⟩ : ∃ b, b * aeval t F = 1 := hunit.exists_left_inv
  have ha : (aeval u F)⁻¹ * aeval u F = 1 := inv_mul_cancel₀ hF
  let π₀ : Option σ → Ω := fun o => o.elim (aeval u F)⁻¹ u
  let τ : Option σ → C := fun o => o.elim b t
  have hrange : Set.range π₀ = insert (aeval u F)⁻¹ (Set.range u) := by
    ext x
    constructor
    · rintro ⟨o, rfl⟩
      cases o with
      | none => exact Set.mem_insert _ _
      | some q => exact Set.mem_insert_of_mem _ ⟨q, rfl⟩
    · rintro (rfl | ⟨q, rfl⟩)
      · exact ⟨none, rfl⟩
      · exact ⟨some q, rfl⟩
  have hS' : S = (aeval π₀ : MvPolynomial (Option σ) ℚ →ₐ[ℚ] Ω).range := by
    rw [hS, ← hrange, Algebra.adjoin_range_eq_range_aeval]
  clear hS
  subst hS'
  have hkle : ∀ h : MvPolynomial (Option σ) ℚ, aeval π₀ h = 0 → aeval τ h = 0 := by
    intro h hh
    obtain ⟨n, g, h₁, h₂⟩ := exists_clear u t F _ b ha hb h
    have hg : aeval u g = 0 := by
      rw [← h₁]
      have : aeval (fun o : Option σ => o.elim (aeval u F)⁻¹ u) h = 0 := hh
      rw [this, mul_zero]
    have h₃ : aeval t F ^ n * aeval τ h = 0 := by
      have : aeval t F ^ n * aeval (fun o : Option σ => o.elim b t) h = 0 := by rw [h₂, hker g hg]
      exact this
    exact (hunit.pow n).mul_right_eq_zero.1 h₃
  let π : MvPolynomial (Option σ) ℚ →ₐ[ℚ] (aeval π₀ : MvPolynomial (Option σ) ℚ →ₐ[ℚ] Ω).range :=
    (aeval π₀).rangeRestrict
  have hs : Function.Surjective π := AlgHom.rangeRestrict_surjective _
  have hle : RingHom.ker π.toRingHom ≤ RingHom.ker (aeval τ : MvPolynomial (Option σ) ℚ →ₐ[ℚ] C).toRingHom := by
    intro h hh
    refine RingHom.mem_ker.2 (hkle h ?_)
    have : π h = 0 := RingHom.mem_ker.1 hh
    exact congrArg Subtype.val this
  let Φ₀ := RingHom.liftOfSurjective π.toRingHom hs ⟨(aeval τ).toRingHom, hle⟩
  have hΦ₀ : ∀ x, Φ₀ (π x) = aeval τ x := fun x =>
    RingHom.liftOfRightInverse_comp_apply π.toRingHom _ _ ⟨(aeval τ).toRingHom, hle⟩ x
  have huπ : ∀ q, (⟨u q, hu q⟩ : (aeval π₀ : MvPolynomial (Option σ) ℚ →ₐ[ℚ] Ω).range) = π (X (some q)) :=
    fun q => Subtype.ext (by simp [π, π₀])
  refine ⟨Φ₀.toRatAlgHom, fun q => ?_, fun Φ' hΦ' => ?_⟩
  · show Φ₀ _ = _
    rw [huπ, hΦ₀, aeval_X]
    rfl
  · have h1 : Φ'.comp π = aeval τ := by
      refine MvPolynomial.algHom_ext fun o => ?_
      cases o with
      | some q =>
        show Φ' (π (X (some q))) = _
        rw [← huπ, hΦ', aeval_X]
        rfl
      | none =>
        have h2 : (Φ'.comp π).comp (rename some : MvPolynomial σ ℚ →ₐ[ℚ] _) = aeval t := by
          refine MvPolynomial.algHom_ext fun q => ?_
          show Φ' (π (rename some (X q))) = _
          rw [rename_X, ← huπ, hΦ', aeval_X]
        have h3 : π (X none) * π (rename some F) = 1 := by
          refine Subtype.ext ?_
          show aeval π₀ (X none) * aeval π₀ (rename some F) = 1
          rw [aeval_X, aeval_rename]
          exact ha
        have h4 : Φ' (π (X none)) * aeval t F = 1 := by
          have : Φ' (π (rename some F)) = aeval t F := DFunLike.congr_fun h2 F
          rw [← this, ← map_mul, h3, map_one]
        show Φ' (π (X none)) = _
        rw [aeval_X]
        exact hunit.mul_right_cancel (h4.trans hb.symm)
    refine AlgHom.ext fun s => ?_
    obtain ⟨x, rfl⟩ := hs s
    have : Φ' (π x) = aeval τ x := DFunLike.congr_fun h1 x
    rw [this]
    exact (hΦ₀ x).symm
end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Reg
