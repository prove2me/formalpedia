-- Prove2me | solution 1 for GlobalTheory.PeriodChart.exists_contraction
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:53:02.03188+00:00
-- url     : https://prove2.me/submissions/b5cf7acf-78e7-4436-acb9-367c57fbf27f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsContraction
import Theorems.Thm_GlobalTheory_PeriodChart_symm_contraction
import Theorems.Thm_GlobalTheory_PeriodChart_exists_lin_anti
import Theorems.Thm_GlobalTheory_PeriodChart_lin_anti_unique
import Theorems.Thm_GlobalTheory_PeriodChart_sesq_apply
import Theorems.Thm_GlobalTheory_PeriodChart_isHermitian_iff
import Theorems.Thm_GlobalTheory_PeriodChart_exists_anti
import Theorems.Thm_GlobalTheory_PeriodChart_im_eq_of_span
import Theorems.Thm_GlobalTheory_PeriodChart_exists_extend
import Theorems.Thm_GlobalTheory_PeriodChart_lin_iff

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
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {g : ℕ}
variable {D : Datum H} {ty : Fin g → (E →+* ℂ)}
namespace GlobalTheory.PeriodChart
theorem _root_.solution (P : D.La →+ (Fin g → ℂ)) (hl : ∀ (a : 𝓞 E) x, P (a • x) = dg ty a *ᵥ P x)
    (hi : Function.Injective P) (hd : DiscreteTopology P.range)
    (hs : Submodule.span ℝ (Set.range P) = ⊤) (G : Matrix (Fin g) (Fin g) ℂ)
    (hp : ∀ z, z ≠ 0 → 0 < (sesq G z z).re)
    (hE : ∀ x y, (sesq G (P x) (P y)).im = D.EF x y) (P' : D.La →+ (Fin g → ℂ)) (hP' : IsPeriod D ty P') :
    ∃ (Z : Matrix (Fin g) (Fin g) ℂ) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)),
      (∀ a z, anti Z (dg ty a *ᵥ z) = dg ty a *ᵥ anti Z z) ∧
      (∀ z w, sesq G (anti Z z) w = sesq G (anti Z w) z) ∧
      (∀ z, z ≠ 0 → (sesq G (anti Z z) (anti Z z)).re < (sesq G z z).re) ∧
      ∀ x, P' x = h (P x + anti Z (P x)) := by
  obtain ⟨hl'c, -, -, -, Hm', hH', hpos', hE'⟩ := hP'
  have hl' := (lin_iff P').1 hl'c
  have := D.fin
  have : Module.Finite ℤ D.La := Module.Finite.trans (𝓞 E) D.La

  obtain ⟨T, hTP⟩ := exists_extend P P' hi hd hs
  have hTr : ∀ (r : ℝ) z, T.toAddMonoidHom ((r : ℂ) • z) = (r : ℂ) • T.toAddMonoidHom z := by
    intro r z
    simp only [LinearMap.toAddMonoidHom_coe, Complex.coe_smul, map_smul]
  obtain ⟨A, C, hAC⟩ := exists_lin_anti T.toAddMonoidHom hTr
  have hAC' : ∀ z, T z = A z + C z := hAC

  have hkey : ∀ z w, (sesq Hm' (T z) (T w)).im = (sesq G z w).im := by
    intro z w
    have := im_eq_of_span P hs (sesq Hm') (sesq G) T T LinearMap.id LinearMap.id
      (fun a b => by rw [hTP, hTP, sesq_apply, hE', LinearMap.id_apply, LinearMap.id_apply, hE]) z w
    simpa using this

  have hAi : Function.Injective A := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    by_contra hne
    have e1 : T z = C z := by rw [hAC', hz, zero_add]
    have e2 : T (Complex.I • z) = (-Complex.I) • C z := by
      rw [hAC', map_smul, hz, smul_zero, zero_add, LinearMap.map_smulₛₗ, Complex.conj_I]
    have hq := hp z hne
    have hs0 : 0 ≤ (sesq Hm' (C z) (C z)).re := by
      by_cases h0 : C z = 0
      · simp [h0]
      · rw [sesq_apply]; exact (hpos' _ h0).le
    have := hkey z (Complex.I • z)
    rw [e1, e2] at this
    simp only [LinearMap.map_smulₛₗ, map_neg, Complex.conj_I, neg_neg, smul_eq_mul, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.neg_im, zero_mul, one_mul, zero_add,
      neg_mul] at this
    linarith
  let h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ) := LinearEquiv.ofInjectiveEndo A hAi
  have hh : ∀ u, h u = A u := fun u => rfl
  have hA : ∀ u, A (h.symm u) = u := fun u => (hh _).symm.trans (h.apply_symm_apply u)
  let N : (Fin g → ℂ) →ₗ⋆[ℂ] (Fin g → ℂ) := (h.symm : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)).comp C
  have hN : ∀ z, N z = h.symm (C z) := fun z => rfl
  obtain ⟨Z, hZ⟩ := exists_anti N

  have hTD : ∀ (a : 𝓞 E) z, T (dg ty a *ᵥ z) = dg ty a *ᵥ T z := by
    intro a
    let Dr : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ) := (Matrix.mulVecLin (dg ty a)).restrictScalars ℝ
    have hDr : T.comp Dr = Dr.comp T := by
      apply LinearMap.ext_on_range hs
      intro x
      change T (dg ty a *ᵥ P x) = dg ty a *ᵥ T (P x)
      rw [← hl, hTP, hTP, hl']
    intro z
    exact LinearMap.congr_fun hDr z
  have hDI : ∀ (a : 𝓞 E) (c : ℂ) z, dg ty a *ᵥ (c • z) = c • (dg ty a *ᵥ z) :=
    fun a c z => Matrix.mulVec_smul _ _ _
  have hcomm : ∀ (a : 𝓞 E) z,
      A (dg ty a *ᵥ z) = dg ty a *ᵥ A z ∧ C (dg ty a *ᵥ z) = dg ty a *ᵥ C z := by
    intro a z
    refine lin_anti_unique (fun z => A (dg ty a *ᵥ z)) (fun z => dg ty a *ᵥ A z)
      (fun z => C (dg ty a *ᵥ z)) (fun z => dg ty a *ᵥ C z) ?_ ?_ ?_ ?_ ?_ z
    · intro z; simp only [hDI, map_smul]
    · intro z; simp only [map_smul, hDI]
    · intro z; simp only [hDI, LinearMap.map_smulₛₗ, Complex.conj_I]
    · intro z; simp only [LinearMap.map_smulₛₗ, Complex.conj_I, hDI]
    · intro z
      show A (dg ty a *ᵥ z) + C (dg ty a *ᵥ z) = dg ty a *ᵥ A z + dg ty a *ᵥ C z
      rw [← hAC', hTD, hAC', Matrix.mulVec_add]

  let F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ) →ₗ⋆[ℂ] ℂ := ((sesq Hm').comp A).compl₂ A
  have hFa : ∀ z w, F z w = sesq Hm' (A z) (A w) := fun z w => rfl
  have hFT : ∀ z w, F (z + N z) (w + N w) = sesq Hm' (T z) (T w) := by
    have e : ∀ u, A (u + N u) = T u := fun u => by rw [map_add, hN, hA, hAC']
    intro z w
    rw [hFa, e, e]
  obtain ⟨hsy, hct⟩ := symm_contraction F (sesq G) N
    (fun z w => by rw [hFa, hFa]; exact (isHermitian_iff Hm').1 hH' _ _)
    (fun z hz => by
      rw [hFa, sesq_apply]
      exact hpos' _ (fun h0 => hz (hAi (by rw [h0, map_zero]))))
    hp (fun z w => by rw [hFT, hkey])
  refine ⟨Z, h, ?_, ?_, ?_, ?_⟩ <;> rw [← hZ]
  · intro a z
    apply hAi
    rw [hN, hN, hA, (hcomm a _).1, hA, (hcomm a z).2]
  · exact hsy
  · exact hct
  · intro x
    rw [map_add, hh, hh, hN, hA, ← hAC', hTP]
end GlobalTheory.PeriodChart
