-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HermPlane.lat_primitive
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:38:08.914891+00:00
-- url     : https://prove2.me/submissions/a949c49b-5eb2-4ff1-a314-f141f792a7f4

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_PlaneOfHenselAndPairing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory.Rg.FlB
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HermPlane
variable {L : Type} [NontriviallyNormedField L] [IsUltrametricDist L] {V : Type} [AddCommGroup V] [Module L V]
namespace GlobalTheory.CompanionTheory.HermPlane
theorem _root_.solution {Λ : AddSubgroup V} (hΛ : IsLat L Λ) {p : L} (hp0 : p ≠ 0) (hp1 : ‖p‖ < 1)
    {v : V} (hv : v ≠ 0) : ∃ a : L, a ≠ 0 ∧ a • v ∈ Λ ∧ p⁻¹ • a • v ∉ Λ := by
  obtain ⟨m, b, hb⟩ := id hΛ
  have hex : ∃ i, b.repr v i ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hv (b.repr.map_eq_zero_iff.1 (Finsupp.ext hcon))
  obtain ⟨i, hi⟩ := hex
  set C : ℝ := ∑ j, ‖b.repr v j‖ + 1 with hC
  have hC0 : 0 < C := by
    have : 0 ≤ ∑ j, ‖b.repr v j‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
    linarith
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (inv_pos.mpr hC0) hp1
  have hk0 : p ^ k ≠ 0 := pow_ne_zero _ hp0
  have hstart : p ^ k • v ∈ Λ := by
    rw [hb]
    intro j
    rw [map_smul, Finsupp.smul_apply, smul_eq_mul, norm_mul, norm_pow]
    have h1 : ‖b.repr v j‖ ≤ C := by
      have : ‖b.repr v j‖ ≤ ∑ j, ‖b.repr v j‖ :=
        Finset.single_le_sum (f := fun j => ‖b.repr v j‖) (fun _ _ => norm_nonneg _)
          (Finset.mem_univ j)
      linarith
    calc ‖p‖ ^ k * ‖b.repr v j‖ ≤ C⁻¹ * C := mul_le_mul hk.le h1 (norm_nonneg _) (inv_pos.mpr hC0).le
      _ = 1 := inv_mul_cancel₀ hC0.ne'
  have hpinv : 1 < ‖p⁻¹‖ := by
    rw [norm_inv]
    exact (one_lt_inv₀ (norm_pos_iff.2 hp0)).2 hp1
  have hnot : ∃ n : ℕ, (p⁻¹) ^ n • p ^ k • v ∉ Λ := by
    have hc : 0 < ‖p ^ k * b.repr v i‖ := norm_pos_iff.2 (mul_ne_zero hk0 hi)
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (‖p ^ k * b.repr v i‖)⁻¹ hpinv
    refine ⟨n, fun hmem => ?_⟩
    have := (hb _).1 hmem i
    rw [map_smul, map_smul, Finsupp.smul_apply, Finsupp.smul_apply, smul_eq_mul, smul_eq_mul,
      norm_mul, norm_pow] at this
    have h2 : 1 < ‖p⁻¹‖ ^ n * ‖p ^ k * b.repr v i‖ := by
      have := mul_lt_mul_of_pos_right hn hc
      rwa [inv_mul_cancel₀ hc.ne'] at this
    linarith
  classical
  have hfind := Nat.find_spec hnot
  have hne : Nat.find hnot ≠ 0 := by
    intro h0
    rw [h0] at hfind
    simp at hfind
    exact hfind hstart
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hne
  have hmem : (p⁻¹) ^ n • p ^ k • v ∈ Λ := by
    have := Nat.find_min hnot (m := n) (by omega)
    simpa using this
  refine ⟨(p⁻¹) ^ n * p ^ k, mul_ne_zero (pow_ne_zero _ (inv_ne_zero hp0)) hk0, ?_, ?_⟩
  · rwa [mul_smul]
  · rw [hn] at hfind
    intro hcon
    apply hfind
    rw [mul_smul, smul_smul p⁻¹] at hcon
    rwa [Nat.succ_eq_add_one, pow_succ']
end GlobalTheory.CompanionTheory.HermPlane
