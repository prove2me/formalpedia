-- Prove2me | solution 1 for GlobalTheory.Nef.PathJet.exists_jet_succ_of_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:19:30.709638+00:00
-- url     : https://prove2.me/submissions/e869ab81-1147-4f71-a5d0-24e162bb1bf5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DerivCompM
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsDoublingJetSuccOfLift
import Theorems.Thm_GlobalTheory_Nef_PathJet_deriv_comp_m
import Theorems.Thm_GroundTheory_FunctionField_Place_ordHom_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.FunctionField.Place.ordHom_apply


section
open GlobalTheory.Nef
namespace GlobalTheory.Nef.PathJet
open PowerSeries
section Coeff
variable {R : Type} [CommRing R]
private lemma coeff_eq_of_X_pow_dvd_sub {n i : ℕ} {a b : PowerSeries R}
    (h : (X : PowerSeries R) ^ n ∣ a - b) (hi : i < n) : coeff i a = coeff i b := by
  rw [X_pow_dvd_iff] at h
  have := h i hi
  rwa [map_sub, sub_eq_zero] at this
private lemma coeff_mul_of_X_pow_dvd' {n : ℕ} {u : PowerSeries R} (hu : (X : PowerSeries R) ^ n ∣ u)
    (h : PowerSeries R) : coeff n (u * h) = coeff n u * coeff 0 h := by
  obtain ⟨k, rfl⟩ := hu
  rw [mul_assoc, coeff_X_pow_mul', coeff_X_pow_mul', if_pos le_rfl, if_pos le_rfl, Nat.sub_self]
  simp only [coeff_zero_eq_constantCoeff_apply, map_mul]
private lemma X_pow_dvd_rescale' {k : ℕ} {p : PowerSeries R} (a : R)
    (h : (X : PowerSeries R) ^ k ∣ p) : (X : PowerSeries R) ^ k ∣ rescale a p := by
  rw [X_pow_dvd_iff] at h ⊢
  intro i hi
  rw [coeff_rescale, h i hi, mul_zero]
end Coeff
end GlobalTheory.Nef.PathJet
end

set_option autoImplicit false
open GlobalTheory.Nef
open GlobalTheory GlobalTheory.Nef GlobalTheory.Nef.PathJet
open PowerSeries
namespace GlobalTheory.Nef.PathJet
theorem _root_.solution (A B R : Type) [CommRing A] [CommRing B] [CommRing R] [Algebra ℚ R]
    (π : B →+* A) (ε : A →+* B) (m : A →+* A) (β : B →+* R) (δ : A →+ R)
    (hεπ : ε.comp π = RingHom.id B) (hmπ : m.comp π = π) (hεm : ε.comp m = ε)
    (hm2 : ∀ f ∈ RingHom.ker ε, m f - 2 * f ∈ RingHom.ker ε ^ 2)
    (_hδ : ∀ f g, δ (f * g) = β (ε f) * δ g + β (ε g) * δ f) (_hδπ : ∀ a, δ (π a) = 0)
    (n : ℕ) (hn : 2 ≤ n) (φ ψ : A → PowerSeries R) (hφ : IsJet π ε m β δ n φ)
    (hψ : IsRingHomMod π β (n + 1) ψ) (hψφ : ∀ f, (X : PowerSeries R) ^ n ∣ ψ f - φ f) :
    ∃ ψ' : A → PowerSeries R, IsJet π ε m β δ (n + 1) ψ' ∧
      ∀ f, (X : PowerSeries R) ^ n ∣ ψ' f - φ f := by
  obtain ⟨-, hφm, hφ0, hφ1⟩ := hφ
  obtain ⟨hψmul, hψadd, hψone, hψπ⟩ := hψ
  have hεmf : ∀ f, ε (m f) = ε f := fun f => by rw [← RingHom.comp_apply, hεm]
  have hmπf : ∀ b, m (π b) = π b := fun b => by rw [← RingHom.comp_apply, hmπ]
  have hψ0 : ∀ f, coeff 0 (ψ f) = β (ε f) := fun f => by
    rw [coeff_eq_of_X_pow_dvd_sub (hψφ f) (by omega), coeff_zero_eq_constantCoeff_apply, hφ0]

  obtain ⟨u, hu_def⟩ : ∃ u : A → PowerSeries R, ∀ f, u f = ψ (m f) - rescale 2 (ψ f) :=
    ⟨_, fun _ => rfl⟩
  have hu : ∀ f, (X : PowerSeries R) ^ n ∣ u f := fun f => by
    have e : u f = (ψ (m f) - φ (m f)) + (φ (m f) - rescale 2 (φ f)) - rescale 2 (ψ f - φ f) := by
      rw [hu_def, map_sub]; ring
    rw [e]
    exact dvd_sub (dvd_add (hψφ _) (hφm f)) (X_pow_dvd_rescale' _ (hψφ f))
  obtain ⟨D, hD_def⟩ : ∃ D : A → R, ∀ f, D f = coeff n (u f) := ⟨_, fun _ => rfl⟩
  have hDadd : ∀ f g, D (f + g) = D f + D g := fun f g => by
    simp only [hD_def]
    rw [← map_add]
    apply coeff_eq_of_X_pow_dvd_sub _ (Nat.lt_succ_self n)
    have e : u (f + g) - (u f + u g) =
        (ψ (m f + m g) - (ψ (m f) + ψ (m g))) - rescale 2 (ψ (f + g) - (ψ f + ψ g)) := by
      simp only [hu_def, map_add, map_sub]; ring
    rw [e]
    exact dvd_sub (hψadd _ _) (X_pow_dvd_rescale' _ (hψadd _ _))
  have hDmul : ∀ f g, D (f * g) = β (ε f) * D g + β (ε g) * D f := fun f g => by
    have e1 : (X : PowerSeries R) ^ (n + 1) ∣
        u (f * g) - (u f * ψ (m g) + rescale 2 (ψ f) * u g) := by
      have e : u (f * g) - (u f * ψ (m g) + rescale 2 (ψ f) * u g) =
          (ψ (m f * m g) - ψ (m f) * ψ (m g)) - rescale 2 (ψ (f * g) - ψ f * ψ g) := by
        simp only [hu_def, map_mul, map_sub]; ring
      rw [e]
      exact dvd_sub (hψmul _ _) (X_pow_dvd_rescale' _ (hψmul _ _))
    simp only [hD_def]
    rw [coeff_eq_of_X_pow_dvd_sub e1 (Nat.lt_succ_self n), map_add,
      coeff_mul_of_X_pow_dvd' (hu f), mul_comm (rescale 2 (ψ f)), coeff_mul_of_X_pow_dvd' (hu g)]
    rw [coeff_rescale, pow_zero, one_mul, hψ0, hψ0, hεmf]
    ring
  have hDπ : ∀ b, D (π b) = 0 := fun b => by
    rw [hD_def, hu_def, hmπf, map_sub, coeff_rescale,
      coeff_eq_of_X_pow_dvd_sub (hψπ b) (Nat.lt_succ_self n), coeff_C, if_neg (by omega)]
    ring
  obtain ⟨c, hc⟩ : ∃ c : R, c * ((2 : R) ^ n - 2) = 1 := by
    have h4 : (4 : ℚ) ≤ 2 ^ n := by
      calc (4 : ℚ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hn
    have hne : (2 : ℚ) ^ n - 2 ≠ 0 := by intro h; linarith
    refine ⟨algebraMap ℚ R ((2 : ℚ) ^ n - 2)⁻¹, ?_⟩
    have e : ((2 : R) ^ n - 2) = algebraMap ℚ R ((2 : ℚ) ^ n - 2) := by
      rw [map_sub, map_pow, map_ofNat]
    rw [e, ← map_mul, inv_mul_cancel₀ hne, map_one]
  obtain ⟨E, hE⟩ : ∃ E : A →+ R, ∀ f, E f = c * D f :=
    ⟨AddMonoidHom.mk' (fun f => c * D f) (fun f g => by rw [hDadd]; ring), fun _ => rfl⟩
  have hEmul : ∀ f g, E (f * g) = β (ε f) * E g + β (ε g) * E f := fun f g => by
    rw [hE, hE, hE, hDmul]; ring
  have hEπ : ∀ b, E (π b) = 0 := fun b => by rw [hE, hDπ, mul_zero]
  have hEm : ∀ f, E (m f) = 2 * E f := deriv_comp_m π ε m β E hεπ hmπ hm2 hEmul hEπ
  refine ⟨fun f => ψ f + C (E f) * X ^ n, ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩, ?_⟩
  · intro f g
    have e : ψ (f * g) + C (E (f * g)) * X ^ n - (ψ f + C (E f) * X ^ n) * (ψ g + C (E g) * X ^ n) =
        (ψ (f * g) - ψ f * ψ g) + X ^ n * (C (E (f * g)) - C (E f) * ψ g - C (E g) * ψ f) -
          C (E f) * C (E g) * (X ^ n * X ^ n) := by ring
    rw [e]
    refine dvd_sub (dvd_add (hψmul f g) ?_) ?_
    · rw [pow_succ]
      apply mul_dvd_mul_left
      rw [X_dvd_iff, ← coeff_zero_eq_constantCoeff_apply]
      simp only [map_sub, coeff_zero_C, coeff_C_mul, hψ0, hEmul]
      ring
    · apply dvd_mul_of_dvd_right
      rw [← pow_add]
      exact pow_dvd_pow _ (by omega)
  · intro f g
    convert hψadd f g using 1
    simp only [map_add]
    ring
  · convert hψone using 1
    dsimp only
    rw [show E 1 = 0 by rw [← map_one π, hEπ]]
    simp
  · intro b
    convert hψπ b using 1
    dsimp only
    rw [hEπ]
    simp
  · intro f
    rw [X_pow_dvd_iff]
    intro i hi
    simp only [map_sub, map_add, coeff_rescale, coeff_C_mul_X_pow]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
    · rw [if_neg h.ne, if_neg h.ne]
      have := (X_pow_dvd_iff.mp (hu f)) i h
      rw [hu_def, map_sub, coeff_rescale] at this
      linear_combination this
    · rw [h, if_pos rfl, if_pos rfl, hEm, hE, hD_def, hu_def, map_sub, coeff_rescale]
      linear_combination (-(coeff n (ψ (m f)) - 2 ^ n * coeff n (ψ f))) * hc
  · intro f
    rw [← coeff_zero_eq_constantCoeff_apply, map_add, coeff_C_mul_X_pow, if_neg (by omega),
      add_zero, hψ0]
  · intro f
    rw [map_add, coeff_C_mul_X_pow, if_neg (by omega), add_zero,
      coeff_eq_of_X_pow_dvd_sub (hψφ f) (by omega), hφ1]
  · intro f
    have e : ψ f + C (E f) * X ^ n - φ f = (ψ f - φ f) + C (E f) * X ^ n := by ring
    rw [e]
    exact dvd_add (hψφ f) (dvd_mul_left _ _)
end GlobalTheory.Nef.PathJet
