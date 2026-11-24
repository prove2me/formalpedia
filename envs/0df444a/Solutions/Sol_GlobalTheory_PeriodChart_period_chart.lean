-- Prove2me | solution 1 for GlobalTheory.PeriodChart.period_chart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:12:59.950581+00:00
-- url     : https://prove2.me/submissions/6aadbc70-4a56-44d3-9a06-76a79f0466ce

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsContraction
import Theorems.Thm_GlobalTheory_PeriodChart_lin_anti_unique
import Theorems.Thm_GlobalTheory_PeriodChart_exists_param
import Theorems.Thm_GlobalTheory_PeriodChart_sesq_apply
import Theorems.Thm_GlobalTheory_PeriodChart_anti_apply
import Theorems.Thm_GlobalTheory_PeriodChart_anti_inj
import Theorems.Thm_GlobalTheory_PeriodChart_anti_symm_iff
import Theorems.Thm_GlobalTheory_PeriodChart_isUnit_det_of_ker
import Theorems.Thm_GlobalTheory_PeriodChart_isOpen_convex
import Theorems.Thm_GlobalTheory_PeriodChart_comm_iff
import Theorems.Thm_GlobalTheory_PeriodChart_anti_comm_iff
import Theorems.Thm_GlobalTheory_PeriodChart_lin_iff
import Theorems.Thm_GlobalTheory_PeriodChart_herm_comm
import Theorems.Thm_GlobalTheory_PeriodChart_isPeriod_add
import Theorems.Thm_GlobalTheory_PeriodChart_exists_contraction
import Theorems.Thm_GlobalTheory_PeriodChart_conj_rt
import Theorems.Thm_GlobalTheory_PeriodChart_card_pairs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix Module
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PeriodChart
namespace GlobalTheory.PeriodChart
theorem _root_.solution : (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ)), IsTypeFn H D.p D.q ty → ∀ P₀, IsPeriod D ty P₀ → ∃ (m : ℕ) (B : Set (Fin m → ℂ)) (P : (Fin m → ℂ) → (D.La →+ (Fin g → ℂ))), 2 * m = Module.finrank ℚ E * D.p * D.q ∧ IsOpen B ∧ Convex ℝ B ∧ 0 ∈ B ∧ P 0 = P₀ ∧ IsHolPeriods D ty B P ∧ ∀ P', IsPeriod D ty P' → ∃! b, b ∈ B ∧ ∃ h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ), ∀ a, P' a = h (P b a)) := by
  intro E _ _ _ H D g ty hty P₀ hP₀
  obtain ⟨hl0, hi, hd, hs, G, hG, hpos, hEF⟩ := hP₀
  have hp : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (sesq G z z).re := fun z hz => by
    rw [sesq_apply]; exact hpos z hz
  have hE : ∀ x y, (sesq G (P₀ x) (P₀ y)).im = D.EF x y := fun x y => by
    rw [sesq_apply]; exact hEF x y
  have hl : ∀ (a : 𝓞 E) x, P₀ (a • x) = dg ty a *ᵥ P₀ x := (lin_iff P₀).1 hl0

  have hGu : IsUnit Gᵀ.det := by
    refine isUnit_det_of_ker Gᵀ fun z hz h0 => ?_
    have h1 := hpos z hz
    rw [hermForm, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, h0] at h1
    simp at h1
  have hcancel : ∀ M N : Matrix (Fin g) (Fin g) ℂ, Gᵀ * M = Gᵀ * N → M = N := by
    intro M N h
    have h1 : Gᵀ⁻¹ * (Gᵀ * M) = Gᵀ⁻¹ * (Gᵀ * N) := by rw [h]
    rwa [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hGu, Matrix.one_mul,
      Matrix.one_mul] at h1
  have hcc : ∀ φ : E →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate φ) = φ :=
    fun φ => RingHom.ext fun x => by simp

  obtain ⟨m, L, hm, hLi, hLr⟩ := exists_param (fun i j : Fin g => ty i = ComplexEmbedding.conjugate (ty j))
      (fun i => ty i (H.rt : E) = H.rt0)
      (fun i j h => by
        show ty j = ComplexEmbedding.conjugate (ty i)
        rw [h, hcc])
      (fun i j h => by
        show ty i (H.rt : E) = H.rt0 ↔ ¬ ty j (H.rt : E) = H.rt0
        have h1 := conj_rt H (ty i)
        rw [h, hcc] at h1
        rw [h]
        exact h1)
  obtain ⟨Zl, hZl⟩ : ∃ Zl : (Fin m → ℂ) →ₗ[ℂ] Matrix (Fin g) (Fin g) ℂ, ∀ b, Zl b = Gᵀ⁻¹ * L b :=
    ⟨(LinearMap.mulLeft ℂ Gᵀ⁻¹).comp L, fun b => rfl⟩
  have hGc : ∀ a, dg ty a * Gᵀ = Gᵀ * dg ty a := herm_comm P₀ hl hs G hE

  have hchar : ∀ Z : Matrix (Fin g) (Fin g) ℂ,
      ((∀ (a : 𝓞 E) z, anti Z (dg ty a *ᵥ z) = dg ty a *ᵥ anti Z z) ∧
        ∀ z w, sesq G (anti Z z) w = sesq G (anti Z w) z) ↔ ∃ b, Zl b = Z := by
    intro Z
    have e0 : (∀ (a : 𝓞 E) z, anti Z (dg ty a *ᵥ z) = dg ty a *ᵥ anti Z z) ↔
        ∀ a, dg ty a * (Gᵀ * Z) = (Gᵀ * Z) * dg (fun i => ComplexEmbedding.conjugate (ty i)) a := by
      refine ⟨fun h a => ?_, fun h a => (anti_comm_iff ty a Z).2 ?_⟩
      · rw [← Matrix.mul_assoc, hGc, Matrix.mul_assoc, (anti_comm_iff ty a Z).1 (h a), Matrix.mul_assoc]
      · apply hcancel
        rw [← Matrix.mul_assoc, ← hGc, Matrix.mul_assoc, h a, Matrix.mul_assoc]
    have e1 := e0.trans (comm_iff ty (fun i => ComplexEmbedding.conjugate (ty i)) (Gᵀ * Z))
    have hex : (∃ b, L b = Gᵀ * Z) ↔ ∃ b, Zl b = Z := by
      constructor
      · rintro ⟨b, hb⟩
        refine ⟨b, ?_⟩
        rw [hZl, hb, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hGu, Matrix.one_mul]
      · rintro ⟨b, hb⟩
        refine ⟨b, ?_⟩
        rw [← hb, hZl, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hGu, Matrix.one_mul]
    exact (and_congr e1 (anti_symm_iff G Z)).trans (and_comm.trans ((hLr _).symm.trans hex))
  obtain ⟨hO, hC⟩ := isOpen_convex G hp Zl

  have hF : ∀ Z : Matrix (Fin g) (Fin g) ℂ, ∃ F : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ), ∀ z, F z = z + anti Z z := by
    intro Z
    refine ⟨⟨⟨fun z => z + anti Z z, fun x y => by simp only [map_add]; abel⟩, fun r z => ?_⟩, fun z => rfl⟩
    simp only [RingHom.id_apply, smul_add]
    congr 1
    rw [anti_apply, anti_apply, star_smul, star_trivial, Matrix.mulVec_smul]
  choose F hFz using hF
  refine ⟨m, {b | ∀ z, z ≠ 0 → (sesq G (anti (Zl b) z) (anti (Zl b) z)).re < (sesq G z z).re},
    fun b => P₀ + (anti (Zl b)).toAddMonoidHom.comp P₀, ?_, hO, hC, ?_, ?_, ⟨?_, ?_⟩, ?_⟩
  · exact hm.trans (card_pairs hty)
  · simp only [Set.mem_ofPred_eq]
    intro z hz
    simpa [anti_apply] using hp z hz
  · ext x i
    simp [anti_apply]
  · intro b hb
    obtain ⟨h1, h2⟩ := (hchar (Zl b)).2 ⟨b, rfl⟩
    exact isPeriod_add P₀ hl hi hd hs G hG hE (Zl b) h1 h2 hb
  · intro x
    obtain ⟨T, hT⟩ : ∃ T : (Fin m → ℂ) →L[ℂ] (Fin g → ℂ), ∀ b, T b = Zl b *ᵥ star (P₀ x) :=
      ⟨LinearMap.toContinuousLinearMap
        (⟨⟨fun b => Zl b *ᵥ star (P₀ x), fun a b => by simp [Matrix.add_mulVec]⟩,
          fun c b => by simp [Matrix.smul_mulVec]⟩ : (Fin m → ℂ) →ₗ[ℂ] (Fin g → ℂ)), fun b => rfl⟩
    have hfun : (fun b => (P₀ + (anti (Zl b)).toAddMonoidHom.comp P₀) x) = fun b => P₀ x + T b := by
      funext b
      simp [hT, anti_apply]
    show DifferentiableOn ℂ (fun b => (P₀ + (anti (Zl b)).toAddMonoidHom.comp P₀) x) _
    rw [hfun]
    exact (differentiableOn_const _).add T.differentiable.differentiableOn
  · intro P' hP'
    obtain ⟨Z, h, h1, h2, h3, hPh⟩ := exists_contraction P₀ hl hi hd hs G hp hE P' hP'
    obtain ⟨b, rfl⟩ := (hchar Z).1 ⟨h1, h2⟩
    refine ⟨b, ⟨h3, h, fun a => by simpa using hPh a⟩, ?_⟩
    rintro b' ⟨-, h', hh'⟩
    obtain ⟨k, hk⟩ : ∃ k : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ), ∀ z, k z = h'.symm (h z) :=
      ⟨h.trans h'.symm, fun z => rfl⟩

    have hext : F (Zl b') = (k.toLinearMap.restrictScalars ℝ).comp (F (Zl b)) := by
      refine LinearMap.ext_on_range hs fun a => ?_
      have e1 := hPh a
      have e2 := hh' a
      simp only [AddMonoidHom.add_apply, AddMonoidHom.coe_comp, Function.comp_apply,
        LinearMap.toAddMonoidHom_coe] at e2
      simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply, hFz, LinearEquiv.coe_coe, hk]
      rw [← e1, e2, LinearEquiv.symm_apply_apply]
    have hkey : ∀ z, z + anti (Zl b') z = k z + k (anti (Zl b) z) := by
      intro z
      have e := LinearMap.congr_fun hext z
      simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply, hFz, LinearEquiv.coe_coe,
        map_add] at e
      exact e
    have hu := fun z => lin_anti_unique (fun z => z) (fun z => k z) (fun z => anti (Zl b') z)
      (fun z => k (anti (Zl b) z)) (fun z => rfl) (fun z => by simp)
      (fun z => by rw [map_smulₛₗ, Complex.conj_I])
      (fun z => by rw [map_smulₛₗ, Complex.conj_I, map_smul]) hkey z
    have hZ : Zl b' = Zl b := by
      refine anti_inj fun z => ?_
      rw [(hu z).2]
      exact ((hu (anti (Zl b) z)).1).symm
    apply hLi
    rw [hZl, hZl] at hZ
    have h5 : Gᵀ * (Gᵀ⁻¹ * L b') = Gᵀ * (Gᵀ⁻¹ * L b) := by rw [hZ]
    rwa [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hGu, Matrix.one_mul,
      Matrix.one_mul] at h5
end GlobalTheory.PeriodChart
