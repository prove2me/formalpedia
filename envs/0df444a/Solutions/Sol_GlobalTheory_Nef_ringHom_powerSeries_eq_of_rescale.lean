-- Prove2me | solution 1 for GlobalTheory.Nef.ringHom_powerSeries_eq_of_rescale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:03:05.62438+00:00
-- url     : https://prove2.me/submissions/e7777bae-8a1e-4686-a8e9-598ff2f75056

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsAdmissibleIntegralBasisChangeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RingHomPowerSeriesEqOfRescale
import Theorems.Thm_GlobalTheory_Nef_coeff_mul_of_coeff_lt_eq_zero
import Theorems.Thm_GroundTheory_FunctionField_Place_ordHom_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.FunctionField.Place.ordHom_apply



set_option autoImplicit false
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef
open GlobalTheory GlobalTheory.Nef
namespace GlobalTheory.Nef
theorem _root_.solution :
    ∀ (A B R : Type) [CommRing A] [CommRing B] [CommRing R] (π : B →+* A) (ε : A →+* B) (m : A →+* A) (β : B →+* R) (c : R) (n : ℕ), ε.comp π = RingHom.id B → m.comp π = π → ε.comp m = ε → (∀ f ∈ RingHom.ker ε, m f - 2 * f ∈ RingHom.ker ε ^ 2) → 0 < n → (∀ j, n ≤ j → IsUnit (c ^ j - 2)) → ∀ γ γ' : A →+* PowerSeries R, γ.comp π = PowerSeries.C.comp β → γ'.comp π = PowerSeries.C.comp β → PowerSeries.constantCoeff.comp γ = β.comp ε → PowerSeries.constantCoeff.comp γ' = β.comp ε → (PowerSeries.rescale c).comp γ = γ.comp m → (PowerSeries.rescale c).comp γ' = γ'.comp m → (∀ j < n, ∀ f, PowerSeries.coeff j (γ f) = PowerSeries.coeff j (γ' f)) → γ = γ' := by
  intro A B R _ _ _ π ε m β c n hεπ hmπ _hεm hm hn hc γ γ' hγπ hγ'π hγ0 hγ'0 hγm hγ'm hlow
  have hεπ' : ∀ b, ε (π b) = b := fun b => by simpa using RingHom.congr_fun hεπ b
  have hmπ' : ∀ b, m (π b) = π b := fun b => by simpa using RingHom.congr_fun hmπ b
  have hγπ' : ∀ b, γ (π b) = PowerSeries.C (β b) := fun b => by simpa using RingHom.congr_fun hγπ b
  have hγ'π' : ∀ b, γ' (π b) = PowerSeries.C (β b) := fun b => by simpa using RingHom.congr_fun hγ'π b
  have hc0 : ∀ f, PowerSeries.constantCoeff (γ f) = β (ε f) := fun f => by
    simpa using RingHom.congr_fun hγ0 f
  have hc0' : ∀ f, PowerSeries.constantCoeff (γ' f) = β (ε f) := fun f => by
    simpa using RingHom.congr_fun hγ'0 f
  have hγm' : ∀ f, γ (m f) = PowerSeries.rescale c (γ f) := fun f => by
    simpa using (RingHom.congr_fun hγm f).symm
  have hγ'm' : ∀ f, γ' (m f) = PowerSeries.rescale c (γ' f) := fun f => by
    simpa using (RingHom.congr_fun hγ'm f).symm
  have hcoeff : ∀ j, ∀ f, PowerSeries.coeff j (γ f) = PowerSeries.coeff j (γ' f) := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
    rcases lt_or_ge j n with hj | hj
    · exact hlow j hj
    have hj0 : j ≠ 0 := by omega
    obtain ⟨D, hD⟩ : ∃ D : A → R, ∀ f, D f = PowerSeries.coeff j (γ f) - PowerSeries.coeff j (γ' f) :=
      ⟨_, fun _ => rfl⟩
    have hlowδ : ∀ f, ∀ i < j, PowerSeries.coeff i (γ f - γ' f) = 0 := by
      intro f i hi; rw [map_sub, ih i hi f, sub_self]
    have Dadd : ∀ f g, D (f + g) = D f + D g := by
      intro f g; simp only [hD, map_add]; ring
    have Dsub : ∀ f g, D (f - g) = D f - D g := by
      intro f g; simp only [hD, map_sub]; ring
    have Dmul : ∀ f g, D (f * g) = β (ε f) * D g + β (ε g) * D f := by
      intro f g
      have e : γ (f * g) - γ' (f * g) = γ f * (γ g - γ' g) + γ' g * (γ f - γ' f) := by
        rw [map_mul, map_mul]; ring
      have h1 := coeff_mul_of_coeff_lt_eq_zero (γ f) _ j (hlowδ g)
      have h2 := coeff_mul_of_coeff_lt_eq_zero (γ' g) _ j (hlowδ f)
      have h3 : D (f * g) = PowerSeries.coeff j (γ (f * g) - γ' (f * g)) := by
        rw [hD, map_sub]
      rw [h3, e, map_add, h1, h2, hc0, hc0', map_sub, map_sub, hD, hD]
    have Dπ : ∀ b, D (π b) = 0 := by
      intro b; rw [hD, hγπ', hγ'π', PowerSeries.coeff_C, if_neg hj0, sub_self]
    have Dsq : ∀ x ∈ RingHom.ker ε ^ 2, D x = 0 := by
      intro x hx
      rw [pow_two] at hx
      refine Submodule.mul_induction_on hx ?_ ?_
      · intro a ha b hb
        rw [RingHom.mem_ker] at ha hb
        rw [Dmul, ha, hb, map_zero, zero_mul, zero_mul, add_zero]
      · intro x y hx hy
        rw [Dadd, hx, hy, add_zero]
    have Dm2 : ∀ f, D (m f) = 2 * D f := by
      intro f
      set f0 := f - π (ε f) with hf0
      have hf0k : f0 ∈ RingHom.ker ε := by
        rw [RingHom.mem_ker, hf0, map_sub, hεπ', sub_self]
      have hmf : m f = π (ε f) + m f0 := by
        rw [hf0, map_sub, hmπ']; ring
      have hff : f = π (ε f) + f0 := by rw [hf0]; ring
      have hDf : D f = D f0 := by
        conv_lhs => rw [hff]
        rw [Dadd, Dπ, zero_add]
      have hsplit : m f0 = (m f0 - 2 * f0) + (f0 + f0) := by ring
      rw [hmf, Dadd, Dπ, zero_add, hsplit, Dadd, Dsq _ (hm f0 hf0k), Dadd, hDf]
      ring
    have Dmc : ∀ f, D (m f) = c ^ j * D f := by
      intro f
      rw [hD, hD, hγm', hγ'm', PowerSeries.coeff_rescale, PowerSeries.coeff_rescale]
      ring
    intro f
    have h0 : (c ^ j - 2) * D f = 0 := by
      have := (Dmc f).symm.trans (Dm2 f)
      rw [sub_mul, this, sub_self]
    have hDf0 : D f = 0 := (hc j hj).mul_right_eq_zero.mp h0
    rw [hD] at hDf0
    exact sub_eq_zero.mp hDf0
  exact RingHom.ext fun f => PowerSeries.ext fun j => hcoeff j f
end GlobalTheory.Nef
