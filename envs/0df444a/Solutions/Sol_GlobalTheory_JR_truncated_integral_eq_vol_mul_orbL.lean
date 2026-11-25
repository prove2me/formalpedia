-- Prove2me | solution 1 for GlobalTheory.JR.truncated_integral_eq_vol_mul_orbL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:02:26.760531+00:00
-- url     : https://prove2.me/submissions/169212ec-bcf5-4e8f-ab53-79f02d466f43

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsSelfDualMeasuresAndAbsKScale
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NonemptyMeasAndReps
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TruncatedIntegralEqVolMulOrbitalIntegral
import Theorems.Thm_GlobalTheory_JR_TruncInt_absK_ne_zero
import Theorems.Thm_GlobalTheory_JR_TruncInt_absK_nonneg
import Theorems.Thm_GlobalTheory_JR_TruncInt_isLocallyConstant_indicator
import Theorems.Thm_GlobalTheory_JR_EtMeas_continuous_NL
import Theorems.Thm_GlobalTheory_JR_exists_meas_and_scale


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory.JR.TruncInt
namespace GlobalTheory.JR
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E), ((∀ s : A.K, A.NL (algebraMap A.K A.L s) = s ^ 2) ∧ (∀ y y' : A.L, A.NL (y * y') = A.NL y * A.NL y') ∧ (∀ t : unitary A.L, A.NL (t : A.L) = 1) ∧ (∀ y : A.L, IsUnit (A.NL y) → IsUnit y) ∧ (∀ y : A.L, IsUnit y → IsUnit (A.NL y))) → ((∀ s t : A.K, A.absK (s * t) = A.absK s * A.absK t) ∧ (∀ s s' : A.K, s ∈ A.OK → s' ∈ A.OK → s * s' = 1 → A.absK s = 1) ∧ (∀ (μ : Measure A.K), μ.IsAddHaarMeasure → ∀ (x : A.Kˣ) (a : A.K) (S : Set A.K), MeasurableSet S → μ {a' : A.K | (x : A.K) * a' - a ∈ S} = ENNReal.ofReal (A.absK (x : A.K))⁻¹ * μ S)) → ∀ (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (m : A.Meas ψ) (x : A.Kˣ) (y₀ : A.L), IsUnit y₀ → ∀ (D : AddSubgroup A.K), IsOpen (D : Set A.K) → IsCompact (D : Set A.K) → ∀ φ : A.L → ℂ, IsTest φ → (∀ b ∈ D, ∃ s s' : A.K, s ∈ A.OK ∧ s' ∈ A.OK ∧ s * s' = 1 ∧ s ^ 2 = 1 + Ring.inverse ((x : A.K) * A.NL y₀) * b ∧ ∀ y : A.L, φ (y * algebraMap A.K A.L s) = φ y) → ∫ y, φ y * Set.indicator (D : Set A.K) (fun _ => (1 : ℂ)) ((x : A.K) * A.NL y - (x : A.K) * A.NL y₀) ∂(m.μL x) = ((m.μK D).toReal : ℂ) * A.orbL m.ν φ y₀ := by
  intro F E _ _ _ _ _ A hN hK ψ hψ m x y₀ hy₀ D hDo hDc φ hφ hsq
  classical
  obtain ⟨hNs, hNmul, hNt, hNu1, hNu2⟩ := hN
  obtain ⟨habs, habs1, hvol⟩ := hK
  set a : A.K := (x : A.K) * A.NL y₀ with ha_def
  have ha : IsUnit a := x.isUnit.mul (hNu2 y₀ hy₀)
  have hx : IsUnit (x : A.K) := x.isUnit
  have hkey : ∀ b : A.K, ∀ s : A.K, s ^ 2 = 1 + Ring.inverse a * b → a * s ^ 2 = a + b := by
    intro b s hs
    rw [hs, mul_add, mul_one, ← mul_assoc, Ring.mul_inverse_cancel a ha, one_mul]
  have hsec : ∀ a' : A.K, ∀ s : A.K, s ^ 2 = 1 + Ring.inverse a * ((x : A.K) * a' - a) →
      A.NL (y₀ * algebraMap A.K A.L s) = a' := by
    intro a' s hs
    have h1 := hkey _ s hs
    rw [hNmul, hNs]
    apply hx.mul_left_cancel
    calc (x : A.K) * (A.NL y₀ * s ^ 2) = a * s ^ 2 := by rw [ha_def]; ring
      _ = _ := by rw [h1]; ring
  have habsT : ∀ a' : A.K, (x : A.K) * a' - a ∈ (D : Set A.K) →
      A.absK a' = A.absK a / A.absK x ∧ IsUnit a' := by
    intro a' hD
    obtain ⟨s, s', hs, hs', hss, hsq2, -⟩ := hsq _ hD
    have h1 := hkey _ s hsq2
    have h2 : (x : A.K) * a' = a * s ^ 2 := by rw [h1]; ring
    have hsu : IsUnit s := ⟨⟨s, s', hss, by rw [mul_comm]; exact hss⟩, rfl⟩
    have hu : IsUnit a' := by
      have : IsUnit ((x : A.K) * a') := by rw [h2]; exact ha.mul (hsu.pow 2)
      exact isUnit_of_mul_isUnit_right this
    refine ⟨?_, hu⟩
    have h3 := congrArg A.absK h2
    rw [habs (x : A.K) a', habs a (s ^ 2), pow_two, habs s s, habs1 s s' hs hs' hss, mul_one, mul_one] at h3
    rw [eq_div_iff (absK_ne_zero A hx), ← h3]; ring
  set f : A.L → A.K := fun y => (x : A.K) * A.NL y - a with hf
  have hfc : Continuous f := (continuous_const.mul (EtMeas.continuous_NL A)).sub continuous_const
  have hSu : ∀ y, f y ∈ (D : Set A.K) → IsUnit y := fun y hy => hNu1 y (habsT _ hy).2
  set h : A.L → ℂ := fun y => φ y * Set.indicator (D : Set A.K) (fun _ => (1 : ℂ)) (f y) with hh
  show ∫ y, h y ∂(m.μL x) = _
  have hDcl : IsClosed (D : Set A.K) := AddSubgroup.isClosed_of_isOpen D hDo
  have hTest : IsTest h := by
    refine ⟨hφ.1.mul ((isLocallyConstant_indicator ⟨hDcl, hDo⟩ (1 : ℂ)).comp_continuous hfc), ?_⟩
    exact hφ.2.mul_right
  have hsupp : tsupport h ⊆ {y | IsUnit y} := by
    refine (closure_minimal ?_ (hDcl.preimage hfc)).trans ?_
    · intro y hy
      by_contra hn
      exact hy (by simp only [h, Set.indicator_of_notMem (show f y ∉ (D : Set A.K) from hn), mul_zero])
    · intro y hy
      exact hSu y hy
  have hμ := (GlobalTheory.JR.exists_meas_and_scale F E A ψ hψ).2 m x
  rw [hμ, integral_smul_measure, ENNReal.toReal_ofReal (absK_nonneg A _)]
  have hxa : A.absK a / A.absK x ≠ 0 := div_ne_zero (absK_ne_zero A ha) (absK_ne_zero A hx)
  have hxaC : ((A.absK a / A.absK x : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hxa
  have hpt : ∀ y, h y = ((A.absK a / A.absK x : ℝ) : ℂ) * (h y * ((A.absK (A.NL y) : ℂ))⁻¹) := by
    intro y
    by_cases hy : f y ∈ (D : Set A.K)
    · rw [(habsT _ hy).1, mul_comm (h y), mul_inv_cancel_left₀ hxaC]
    · simp only [h, Set.indicator_of_notMem hy, mul_zero, zero_mul]
  have hI1 : ∫ y, h y ∂(m.μL 1) = ∫ y, ((A.absK a / A.absK x : ℝ) : ℂ) * (h y * ((A.absK (A.NL y) : ℂ))⁻¹) ∂(m.μL 1) :=
    integral_congr_ae (ae_of_all _ hpt)
  rw [hI1, integral_const_mul]
  let σ : A.K → A.L := fun a' =>
    if hb : (x : A.K) * a' - a ∈ (D : Set A.K) then y₀ * algebraMap A.K A.L (Classical.choose (hsq _ hb))
    else if he : ∃ y : A.L, A.NL y = a' then Classical.choose he else 0
  have hσD : ∀ a' (hb : (x : A.K) * a' - a ∈ (D : Set A.K)), ∃ s : A.K, σ a' = y₀ * algebraMap A.K A.L s ∧
      s ^ 2 = 1 + Ring.inverse a * ((x : A.K) * a' - a) ∧ ∀ y : A.L, φ (y * algebraMap A.K A.L s) = φ y := by
    intro a' hb
    obtain ⟨s', -, -, -, h4, h5⟩ := Classical.choose_spec (hsq _ hb)
    exact ⟨Classical.choose (hsq _ hb), by simp only [σ, dif_pos hb], h4, h5⟩
  have hσN : ∀ a', ((x : A.K) * a' - a ∈ (D : Set A.K) ∨ ∃ y : A.L, A.NL y = a') → A.NL (σ a') = a' := by
    intro a' hor
    by_cases hb : (x : A.K) * a' - a ∈ (D : Set A.K)
    · obtain ⟨s, hσs, hs2, -⟩ := hσD a' hb
      rw [hσs]; exact hsec a' s hs2
    · have he := hor.resolve_left hb
      simp only [σ, dif_neg hb, dif_pos he]
      exact Classical.choose_spec he
  have hσ : ∀ y : A.L, IsUnit y → A.NL (σ (A.NL y)) = A.NL y := fun y _ => hσN _ (Or.inr ⟨y, rfl⟩)
  rw [m.nat.2 σ hσ h hTest hsupp]
  set T : Set A.K := {a' | (x : A.K) * a' - a ∈ (D : Set A.K)} with hT
  have hTm : MeasurableSet T :=
    (hDo.preimage ((continuous_const.mul continuous_id).sub continuous_const)).measurableSet
  have hTN : T ⊆ {a' : A.K | ∃ y : A.L, IsUnit y ∧ A.NL y = a'} := by
    intro a' hb
    refine ⟨σ a', ?_, hσN a' (Or.inl hb)⟩
    exact hNu1 _ (by rw [hσN a' (Or.inl hb)]; exact (habsT a' hb).2)
  have hNL0 : A.NL 0 = 0 := by simpa using hNs 0
  have hpt2 : ∀ a', A.orbL m.ν h (σ a') * ((A.absK a' : ℂ))⁻¹ =
      T.indicator (fun a' => A.orbL m.ν φ y₀ * ((A.absK a' : ℂ))⁻¹) a' := by
    intro a'
    by_cases hb : a' ∈ T
    · obtain ⟨s, hσs, -, hφs⟩ := hσD a' hb
      have hNσ : A.NL (σ a') = a' := hσN a' (Or.inl hb)
      rw [Set.indicator_of_mem hb]
      congr 1
      unfold Et.orbL
      congr 1
      funext t
      have hft : f (t.1 * σ a') ∈ (D : Set A.K) := by
        show (x : A.K) * A.NL (t.1 * σ a') - a ∈ (D : Set A.K)
        rw [hNmul, hNt, hNσ, one_mul]; exact hb
      show φ (t.1 * σ a') * Set.indicator _ _ (f (t.1 * σ a')) = φ (t.1 * y₀)
      rw [Set.indicator_of_mem hft, mul_one, hσs, ← mul_assoc, hφs]
    · rw [Set.indicator_of_notMem hb]
      have hz : ∀ t : unitary A.L, h (t.1 * σ a') = 0 := by
        intro t
        have hft : f (t.1 * σ a') ∉ (D : Set A.K) := by
          by_cases he : ∃ y : A.L, A.NL y = a'
          · show (x : A.K) * A.NL (t.1 * σ a') - a ∉ (D : Set A.K)
            rw [hNmul, hNt, hσN a' (Or.inr he), one_mul]; exact hb
          · have h0 : σ a' = 0 := by simp only [σ, dif_neg (show ¬ ((x : A.K) * a' - a ∈ (D : Set A.K)) from hb), dif_neg he]
            show (x : A.K) * A.NL (t.1 * σ a') - a ∉ (D : Set A.K)
            rw [h0, mul_zero, hNL0, mul_zero, zero_sub]
            intro hD
            obtain ⟨s, s', -, -, hss, hs2, -⟩ := hsq _ hD
            have h1 := hkey _ s hs2
            rw [add_neg_cancel] at h1
            have hsu : IsUnit s := ⟨⟨s, s', hss, by rw [mul_comm]; exact hss⟩, rfl⟩
            have hu : IsUnit (a * s ^ 2) := ha.mul (hsu.pow 2)
            rw [h1, isUnit_zero_iff] at hu
            haveI := subsingleton_of_zero_eq_one hu
            exact he ⟨0, Subsingleton.elim _ _⟩
        simp only [h, Set.indicator_of_notMem hft, mul_zero]
      simp only [Et.orbL, hz, integral_zero, zero_mul]
  have hI2 : ∫ a' in {a' : A.K | ∃ y : A.L, IsUnit y ∧ A.NL y = a'}, A.orbL m.ν h (σ a') * ((A.absK a' : ℂ))⁻¹ ∂m.μK =
      ∫ a' in {a' : A.K | ∃ y : A.L, IsUnit y ∧ A.NL y = a'},
        T.indicator (fun a' => A.orbL m.ν φ y₀ * ((A.absK a' : ℂ))⁻¹) a' ∂m.μK :=
    integral_congr_ae (ae_of_all _ hpt2)
  rw [hI2, setIntegral_indicator hTm, Set.inter_eq_right.2 hTN]
  have hI3 : ∫ a' in T, A.orbL m.ν φ y₀ * ((A.absK a' : ℂ))⁻¹ ∂m.μK =
      ∫ a' in T, A.orbL m.ν φ y₀ * (((A.absK a / A.absK x : ℝ) : ℂ))⁻¹ ∂m.μK :=
    setIntegral_congr_fun hTm (fun a' hb => by simp only [(habsT a' hb).1])
  rw [hI3, setIntegral_const, Measure.real, hT, hvol m.μK m.sdK.1 x a _ hDo.measurableSet, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (inv_nonneg.2 (absK_nonneg A _))]
  have hx0 : A.absK x ≠ 0 := absK_ne_zero A hx
  have ha0 : A.absK a ≠ 0 := absK_ne_zero A ha
  simp only [Complex.real_smul]
  have hx0C : ((A.absK x : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hx0
  have ha0C : ((A.absK a : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ha0
  push_cast
  field_simp
end GlobalTheory.JR
