-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgFl.exists_isDelta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:09:30.697745+00:00
-- url     : https://prove2.me/submissions/7438e259-6fac-4299-a09b-cfb7a82a5e8f

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_DeltaStatement

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory.Rg.FlB
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgFl
namespace GlobalTheory.CompanionTheory.RgFl
theorem _root_.solution (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L] [ProperSpace L]
    [CharZero L] (s : L →+* L) (hs : IsInv s) : ∃ δ, IsDelta s δ := by
  obtain ⟨hss, hn, -⟩ := hs
  have hcont : Continuous s := (AddMonoidHomClass.isometry_of_norm s hn).continuous
  have h2 : (2 : L) ≠ 0 := two_ne_zero
  have h2pos : 0 < ‖(2 : L)‖ := norm_pos_iff.2 h2
  have h2le : ‖(2 : L)‖ ≤ 1 := by
    have := IsUltrametricDist.norm_add_le_max (1 : L) 1
    rw [one_add_one_eq_two] at this
    simpa using this
  have htr : ∀ y : L, ‖y‖ ≤ 1 → ‖y + s y‖ ≤ 1 := fun y hy =>
    (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hy (by rw [hn]; exact hy))

  let I : Set L := {a | ∀ x : L, ‖x‖ ≤ 1 → ‖a * x + s (a * x)‖ ≤ 1}
  have h1I : (1 : L) ∈ I := fun x hx => by simpa using htr x hx
  have hclosed : IsClosed I := by
    have : I = ⋂ (x : L) (_ : ‖x‖ ≤ 1), {a : L | ‖a * x + s (a * x)‖ ≤ 1} := by
      ext a; simp [I]
    rw [this]
    refine isClosed_iInter fun x => isClosed_iInter fun _ => isClosed_le ?_ continuous_const
    have hm : Continuous fun a : L => a * x := continuous_id.mul continuous_const
    exact (hm.add (hcont.comp hm)).norm
  obtain ⟨p, hp⟩ := NormedField.exists_one_lt_norm L
  obtain ⟨N, hNdef⟩ : ∃ N : L, N = p * s p := ⟨_, rfl⟩
  have hNfix : s N = N := by rw [hNdef, map_mul, hss, mul_comm]
  have hN1 : 1 < ‖N‖ := by
    rw [hNdef, norm_mul, hn]
    nlinarith
  have hbound : ∀ a ∈ I, ‖a‖ ≤ ‖N‖ / ‖(2 : L)‖ := by
    intro a ha
    by_contra hlt
    push_neg at hlt
    have hNle : ‖N‖ ≤ ‖N‖ / ‖(2 : L)‖ := by
      rw [le_div_iff₀ h2pos]
      nlinarith [norm_nonneg N]
    have ha1 : 1 ≤ ‖a‖ := by linarith
    obtain ⟨k, hk1, hk2⟩ := exists_nat_pow_near ha1 hN1
    have a0 : a ≠ 0 := by
      rintro rfl
      simp at ha1
      linarith
    have hapos : 0 < ‖a‖ := norm_pos_iff.2 a0
    have hx : ‖N ^ k / a‖ ≤ 1 := by
      rw [norm_div, norm_pow]
      exact (div_le_one hapos).2 hk1
    have h3 := ha _ hx
    have h4 : a * (N ^ k / a) = N ^ k := by field_simp
    rw [h4, map_pow, hNfix, ← two_mul, norm_mul, norm_pow] at h3
    have h5 : ‖N‖ ^ k ≤ 1 / ‖(2 : L)‖ := by
      rw [le_div_iff₀ h2pos]
      linarith
    have h6 : ‖N‖ ^ (k + 1) ≤ ‖N‖ / ‖(2 : L)‖ := by
      rw [pow_succ, div_eq_mul_one_div ‖N‖, mul_comm]
      exact mul_le_mul_of_nonneg_left h5 (norm_nonneg _)
    linarith
  have hIc : IsCompact I :=
    (isCompact_closedBall (0 : L) (‖N‖ / ‖(2 : L)‖)).of_isClosed_subset hclosed
      (fun a ha => by simpa using hbound a ha)
  obtain ⟨δ, hδ, hmax⟩ := hIc.exists_isMaxOn ⟨1, h1I⟩ continuous_norm.continuousOn
  have hmax' : ∀ a ∈ I, ‖a‖ ≤ ‖δ‖ := fun a ha => hmax ha
  have hδ1 : 1 ≤ ‖δ‖ := by simpa using hmax' 1 h1I
  have δ0 : δ ≠ 0 := by
    rintro rfl
    simp at hδ1
    linarith
  have hδpos : 0 < ‖δ‖ := norm_pos_iff.2 δ0

  have hf : Continuous fun x : L => ‖x * δ + s (x * δ)‖ := by
    have hm : Continuous fun a : L => a * δ := continuous_id.mul continuous_const
    exact (hm.add (hcont.comp hm)).norm
  obtain ⟨x₀, hx₀, hx₀max⟩ := (isCompact_closedBall (0 : L) 1).exists_isMaxOn
    ⟨0, by simp⟩ hf.continuousOn
  have hx₀' : ‖x₀‖ ≤ 1 := by simpa using hx₀
  have hfmax : ∀ x : L, ‖x‖ ≤ 1 → ‖x * δ + s (x * δ)‖ ≤ ‖x₀ * δ + s (x₀ * δ)‖ := fun x hx =>
    hx₀max (by simpa using hx)
  obtain ⟨m, hm⟩ : ∃ m : L, m = x₀ * δ + s (x₀ * δ) := ⟨_, rfl⟩
  rw [← hm] at hfmax
  have hmfix : s m = m := by rw [hm, map_add, hss, add_comm]
  have hm1 : ‖m‖ ≤ 1 := by
    rw [hm, mul_comm]
    exact hδ x₀ hx₀'
  have hm0 : m ≠ 0 := by
    have hx : ‖δ⁻¹‖ ≤ 1 := by
      rw [norm_inv]
      exact inv_le_one_of_one_le₀ hδ1
    have h3 := hfmax _ hx
    have h4 : δ⁻¹ * δ = 1 := inv_mul_cancel₀ δ0
    rw [h4, map_one, one_add_one_eq_two] at h3
    intro h
    rw [h, norm_zero] at h3
    linarith
  have hmpos : 0 < ‖m‖ := norm_pos_iff.2 hm0
  have hmeq : ‖m‖ = 1 := by
    by_contra hne
    have hlt : ‖m‖ < 1 := lt_of_le_of_ne hm1 hne
    have hI' : δ / m ∈ I := by
      intro x hx
      have h3 : δ / m * x + s (δ / m * x) = (x * δ + s (x * δ)) / m := by
        rw [map_mul, map_div₀, hmfix, map_mul]
        field_simp
      rw [h3, norm_div]
      exact (div_le_one hmpos).2 (hfmax x hx)
    have h4 := hmax' _ hI'
    rw [norm_div, div_le_iff₀ hmpos] at h4
    nlinarith
  refine ⟨δ, δ0, fun a => ⟨fun ha => hmax' a ha, fun ha x hx => ?_⟩, x₀ / m, ?_, ?_⟩
  · have h3 : a * x = δ * (a / δ * x) := by field_simp
    rw [h3]
    refine hδ _ ?_
    rw [norm_mul, norm_div]
    exact mul_le_one₀ ((div_le_one hδpos).2 ha) (norm_nonneg _) hx
  · rw [norm_div, hmeq, div_one]
    exact hx₀'
  · have h3 : x₀ / m * δ + s (x₀ / m * δ) = (x₀ * δ + s (x₀ * δ)) / m := by
      rw [map_mul, map_div₀, hmfix, map_mul]
      field_simp
    rw [h3, ← hm, div_self hm0]
end GlobalTheory.CompanionTheory.RgFl
