-- Prove2me | solution 1 for GlobalTheory.AnisoSize.anisoSmall_of_shortSmall
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:16:11.142299+00:00
-- url     : https://prove2.me/submissions/400bec3e-7078-44d4-a464-08a31a7f5294

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IsLieDataCircle
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AdelicLattices__ExistsIntMulIsIntegralOfTrace_d66162b46f1d0309
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsNeZeroMemFractionalIdealNormSqLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_AnisotropicFiniteLengthsOfShortLatticeVector
import Theorems.Thm_GlobalTheory_AnisoSize_norm_le_house
import Theorems.Thm_GlobalTheory_AnisoSize_absNorm_le
import Theorems.Thm_GlobalTheory_AnisoSize_house_inv_le
import Theorems.Thm_GlobalTheory_AnisoSize_exists_near_integer
import Theorems.Thm_GlobalTheory_AnisoSize_exists_small_generator
import Theorems.Thm_GlobalTheory_AnisoSize_mul_le_pow
import Theorems.Thm_GlobalTheory_AnisoSize_add_le_pow
import Theorems.Thm_GlobalTheory_AnisoSize_size_sub_le
import Theorems.Thm_GlobalTheory_AnisoSize_size_smul_le
import Theorems.Thm_GlobalTheory_AnisoSize_house_form_le
import Theorems.Thm_GlobalTheory_AnisoSize_house_mul_le_pow
import Theorems.Thm_GlobalTheory_AnisoSize_house_sub_le_pow
import Theorems.Thm_GlobalTheory_AnisoSize_exists_small_lift
import Theorems.Thm_GlobalTheory_HermClass_exists_finite_residues
import Theorems.Thm_GlobalTheory_HermClass_fg_integers
import Theorems.Thm_GlobalTheory_HermClass_isIntegral_star
import Theorems.Thm_GlobalTheory_SmoothForms_house_star


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SmoothForms NumberField Matrix Module Submodule
open scoped ContDiff Topology nonZeroDivisors
open GlobalTheory GlobalTheory.AnisoSize
namespace GlobalTheory.AnisoSize
theorem _root_.solution (E : Type) [Field E] [NumberField E] [IsCMField E]
    (hS : ShortSmall E) : AnisoSmall E := by
  classical
  intro n hn N hN
  obtain ⟨C, k, hC⟩ := hS n hn N hN
  obtain ⟨M, C₁, hM, hMJ⟩ := exists_small_generator E
  obtain ⟨C₂, hC₂⟩ := exists_near_integer E
  let L : Submodule ℤ E := Subalgebra.toSubmodule (integralClosure ℤ E) ⊓
    LinearMap.ker ((starRingEnd E).toIntAlgHom.toLinearMap - LinearMap.id)
  have hL : ∀ x, x ∈ L ↔ IsIntegral ℤ x ∧ star x = x := fun x => by
    simp [L, sub_eq_zero, mem_integralClosure_iff, starRingEnd_apply]
  have hLfg : L.FG := (HermClass.fg_integers E).of_le inf_le_left
  have hK : 2 * (N * M) ≠ 0 := by positivity
  have hK' : ((2 * (N * M) : ℤ) : E) ≠ 0 := by exact_mod_cast hK
  obtain ⟨R, hR, -, hRL⟩ := HermClass.exists_finite_residues L hLfg hK
  obtain ⟨K, hK⟩ := ((hR.image house).union (Set.toFinite
    {C₁, C₂, (n : ℝ), house (N : E), house (M : E), house (1 : E),
      house ((2 * (N * M) : ℤ) : E)⁻¹})).bddAbove
  obtain ⟨k₀, hk₀⟩ := pow_unbounded_of_one_lt K (one_lt_two (α := ℝ))
  set d := finrank ℚ E with hd
  refine ⟨({x : E | IsIntegral ℤ x ∧ ∀ φ : E →+* ℂ, ‖φ x‖ ≤ C} ∪ R ∪
    {((2 * (N * M) : ℤ) : E)}) \ {0}, (k₀ + k + 1) * ((2 * d + 1) * (d + 1)) * 22,
    (((Embeddings.finite_of_norm_le E ℂ C).union hR).union (Set.finite_singleton _)).subset
      Set.diff_subset, by simp, ?_⟩
  intro V _ _ _ h Λ ν B hV H
  obtain ⟨v, hv, hv0, hvC, hvB⟩ := hC V h Λ ν B hV H
  have hs := H.symm
  have hO := H.stable
  have hint := H.int
  have hB := H.two_le
  have hB1 : 1 ≤ B := by linarith
  rw [pow_mul, pow_mul]
  set T := B ^ (k₀ + k + 1) with hT
  have hBT : B ≤ T := le_self_pow₀ hB1 (by omega)
  have hT2 : 2 ≤ T := hB.trans hBT
  have hT1 : 1 ≤ T := by linarith
  have hvT : ν v ≤ T := hvB.trans (pow_le_pow_right₀ hB1 (by omega))
  have hKT : K ≤ T := hk₀.le.trans ((pow_le_pow_left₀ zero_le_two hB _).trans
    (pow_le_pow_right₀ hB1 (by omega)))
  set U := T ^ ((2 * d + 1) * (d + 1)) with hU
  have hTU : T ≤ U ^ 1 := by rw [pow_one]; exact le_self_pow₀ hT1 (by positivity)
  have hU2 : 2 ≤ U := by simpa using hT2.trans hTU
  have hU1 : 1 ≤ U := by linarith
  have hvU := hvT.trans hTU
  have hKU := hKT.trans hTU
  by_cases hvv : h v v = 0
  swap
  · exact ⟨v, hv, ⟨Or.inl (Or.inl ⟨hint v hv v hv, fun φ => (norm_le_house φ _).trans hvC⟩), hvv⟩,
      hvU.trans (pow_le_pow_right₀ hU1 (by norm_num))⟩
  let J : Ideal (𝓞 E) :=
    { carrier := {a | ∃ x ∈ Λ, h x v = algebraMap (𝓞 E) E a}
      add_mem' := by
        rintro a b ⟨x, hx, ha⟩ ⟨y, hy, hb⟩
        exact ⟨x + y, add_mem hx hy, by simp [ha, hb]⟩
      zero_mem' := ⟨0, zero_mem _, by simp⟩
      smul_mem' := by
        rintro c a ⟨x, hx, ha⟩
        exact ⟨algebraMap (𝓞 E) E c • x, hO _ c.isIntegral_coe x hx, by
          rw [map_smul, LinearMap.smul_apply, ha, smul_eq_mul, smul_eq_mul, map_mul]⟩ }
  have hJ : ∀ x ∈ Λ, ∃ a ∈ J, algebraMap (𝓞 E) E a = h x v := fun x hx =>
    ⟨⟨h x v, hint x hx v hv⟩, ⟨x, hx, rfl⟩, rfl⟩
  obtain ⟨x₀, hx₀, hx₀B, hx₀v⟩ : ∃ x₀ ∈ Λ, ν x₀ ≤ B ∧ h x₀ v ≠ 0 := by
    by_contra hc
    push Not at hc
    refine hv0 (H.nondeg v fun x => ?_)
    have h1 : span E {x | x ∈ Λ ∧ ν x ≤ B} ≤ LinearMap.ker (h.flip v) :=
      span_le.2 fun y hy => hc y hy.1 hy.2
    have h2 : h x v = 0 := h1 (H.span ▸ mem_top)
    rw [hs, h2, star_zero]
  obtain ⟨a, haJ, ha⟩ := hJ x₀ hx₀
  have ha0 : a ≠ 0 := by rintro rfl; exact hx₀v (by simpa using ha.symm)
  have hJ0 : J ≠ ⊥ := fun h0 => ha0 (by rwa [h0, Ideal.mem_bot] at haJ)
  have haT : house (h x₀ v) ≤ T ^ 2 :=
    house_form_le H hT2 (a := 1) (b := 1) (by simpa using hx₀B.trans hBT) (by simpa using hvT)
  have haU : house (h x₀ v)⁻¹ ≤ U ^ 1 := by
    refine (house_inv_le (hint _ hx₀ _ hv) hx₀v (one_le_pow₀ hT1) haT).trans ?_
    rw [← pow_mul, pow_one]
    exact pow_le_pow_right₀ hT1 (by rw [← hd]; nlinarith)
  have hNJ : (Ideal.absNorm J : ℝ) ≤ T ^ (2 * d) := by
    have h1 : Ideal.absNorm J ≤ Ideal.absNorm (Ideal.span {a}) :=
      Nat.le_of_dvd (Nat.pos_of_ne_zero (by
        rwa [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]))
        (map_dvd _ (Ideal.dvd_span_singleton.2 haJ))
    refine le_trans (by exact_mod_cast h1) ((absNorm_le a).trans ?_)
    rw [ha, pow_mul]
    exact pow_le_pow_left₀ (house_nonneg _) haT _
  obtain ⟨j, ⟨w₀, hw₀, hw₀j⟩, hj0, hjC, hj⟩ := hMJ J hJ0
  have hj0' : algebraMap (𝓞 E) E j ≠ 0 := fun h0 => hj0 (RingOfIntegers.ext h0)
  have hjT : house (algebraMap (𝓞 E) E j) ≤ T ^ (1 + 2 * d) :=
    hjC.trans (mul_le_pow hT2 (by simpa using (hK (by simp)).trans hKT) hNJ (Nat.cast_nonneg _))
  have hjU : house (algebraMap (𝓞 E) E j) ≤ U ^ 1 := by
    refine hjT.trans ?_
    rw [pow_one]
    exact pow_le_pow_right₀ hT1 (by nlinarith)
  have hjU' : house (algebraMap (𝓞 E) E j)⁻¹ ≤ U ^ 1 := by
    refine (house_inv_le j.isIntegral_coe hj0' (one_le_pow₀ hT1) hjT).trans ?_
    rw [← pow_mul, pow_one]
    exact pow_le_pow_right₀ hT1 (by rw [← hd]; nlinarith)
  obtain ⟨w, hw, hwj, hwU⟩ := exists_small_lift H hC₂ hU2 (hBT.trans hTU)
    (by rw [hV]; exact (hK (by simp)).trans hKU) ((hK (by simp)).trans hKU) hv hx₀ hw₀ hvU
    (hx₀B.trans (hBT.trans hTU)) hx₀v haU (by rwa [hw₀j])
  rw [hw₀j] at hwj
  set v' : V := (N : E) • star ((M : E) / algebraMap (𝓞 E) E j) • v with hv'
  have hv'Λ : v' ∈ Λ := H.dual _ fun x hx => by
    obtain ⟨a, ha, hax⟩ := hJ x hx
    obtain ⟨c, hc⟩ := hj _ ha
    have hc' := congrArg (algebraMap (𝓞 E) E) hc
    rw [map_mul, map_mul, map_intCast, hax] at hc'
    have : (M : E) / algebraMap (𝓞 E) E j * h x v = algebraMap (𝓞 E) E c := by
      field_simp; exact hc'
    rw [map_smul, LinearMap.smul_apply, smul_eq_mul, hs x v, ← star_mul', this]
    exact HermClass.isIntegral_star c.isIntegral_coe
  have hv'U : ν v' ≤ U ^ 4 := by
    have h1 : house (star ((M : E) / algebraMap (𝓞 E) E j)) ≤ U ^ 2 := by
      rw [house_star, div_eq_mul_inv]
      exact house_mul_le_pow hU2 ((hK (by simp)).trans hKU) hjU'
    have h2 : house (N : E) ≤ U ^ 1 := (hK (by simp)).trans hKU
    exact size_smul_le H hU2 h2 (size_smul_le H hU2 h1 hvU)
  have h1 : h w v' = N * M := by
    simp only [hv', map_smulₛₗ, starRingEnd_apply, star_star, smul_eq_mul, hwj, star_intCast]
    field_simp
  have h2 : h v' w = N * M := by rw [hs, h1]; simp
  have h3 : h v' v' = 0 := by simp [hv', hvv]
  have h4 : ∀ s : E, star s = s → h (w - s • v') (w - s • v') = h w w - 2 * (N * M) * s := by
    intro s hs'
    simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, map_smulₛₗ,
      starRingEnd_apply, hs', smul_eq_mul, h1, h2, h3, RingHom.id_apply]
    ring
  obtain ⟨ρ, hρ, y, hy, hwρ⟩ := hRL (h w w) ((hL _).2 ⟨hint w hw w hw, (hs w w).symm⟩)
  obtain ⟨hyi, hys⟩ := (hL y).1 hy
  have hyU : house y ≤ U ^ 16 := by
    have h5 : y = ((2 * (N * M) : ℤ) : E)⁻¹ * (h w w - ρ) := by
      rw [hwρ, zsmul_eq_mul, add_sub_cancel_left, inv_mul_cancel_left₀ hK']
    have h6 : house ((2 * (N * M) : ℤ) : E)⁻¹ ≤ U ^ 1 :=
      (hK (Or.inr (by simp only [Set.mem_insert_iff, Set.mem_singleton_iff, or_true]))).trans hKU
    have h7 : house ρ ≤ U ^ 1 := (hK (Or.inl ⟨ρ, hρ, rfl⟩)).trans hKU
    rw [h5]
    exact house_mul_le_pow hU2 h6 (house_sub_le_pow hU2 (house_form_le H hU2 hwU hwU) h7)
  have hfin : ∀ s : E, house s ≤ U ^ 17 → ν (w - s • v') ≤ U ^ 22 := fun s hs =>
    (size_sub_le H _ _).trans (add_le_pow hU2 hwU (size_smul_le H hU2 hs hv'U))
  by_cases hρ0 : ρ = 0
  · refine ⟨w - (y - 1) • v', sub_mem hw (hO _ (hyi.sub isIntegral_one) _ hv'Λ), ?_, hfin _ ?_⟩
    · have : h (w - (y - 1) • v') (w - (y - 1) • v') = ((2 * (N * M) : ℤ) : E) := by
        rw [h4 _ (by rw [star_sub, hys, star_one]), hwρ, hρ0, zsmul_eq_mul]; push_cast; ring
      rw [this]
      exact ⟨Or.inr rfl, hK'⟩
    · have h6 : house (1 : E) ≤ U ^ 1 := (hK (by simp)).trans hKU
      exact house_sub_le_pow hU2 hyU h6
  · refine ⟨w - y • v', sub_mem hw (hO _ hyi _ hv'Λ), ?_,
      hfin _ (hyU.trans (pow_le_pow_right₀ hU1 (by norm_num)))⟩
    have : h (w - y • v') (w - y • v') = ρ := by
      rw [h4 _ hys, hwρ, zsmul_eq_mul]; push_cast; ring
    rw [this]
    exact ⟨Or.inl (Or.inr hρ), hρ0⟩
end GlobalTheory.AnisoSize
