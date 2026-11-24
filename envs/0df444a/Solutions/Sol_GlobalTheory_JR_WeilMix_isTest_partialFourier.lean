-- Prove2me | solution 1 for GlobalTheory.JR.WeilMix.isTest_partialFourier
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:32:25.335781+00:00
-- url     : https://prove2.me/submissions/16ee7df9-002a-4e38-bcd4-b0862f09963c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_RowMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedStandardAddCharConductorPropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocallyConstantCompactSupportMixedModelPartial
import Theorems.Thm_GlobalTheory_JR_WeilMix_psi_isLocallyConstant
import Theorems.Thm_GlobalTheory_JR_WeilMix_isOpen_setOf_eq_of_isLocallyConstant

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.WeilMix
namespace GlobalTheory.JR.WeilMix
theorem _root_.solution {X F : Type} [TopologicalSpace X] [T2Space X] [NontriviallyNormedField F]
    [ProperSpace F] {r : ℕ} [MeasurableSpace (Fin r → F)] (μ : Measure (Fin r → F))
    (hμ : ∀ (g : (Fin r → F) → ℂ) (w : Fin r → F), ∫ b, g (b + w) ∂μ = ∫ b, g b ∂μ)
    (ψ : AddChar F ℂ) (hψ : IsStdChar ψ) (f : X × (Fin r → F) → ℂ) (hf : IsTest f) :
    IsTest (fun p : X × (Fin r → F) => ∫ b, f (p.1, b) * ψ (b ⬝ᵥ p.2) ∂μ) := by
  obtain ⟨hfl, hfc⟩ := hf
  have hK : IsCompact (tsupport f) := hfc
  have hψl := psi_isLocallyConstant ψ hψ

  have hn1 : IsOpen {q : (X × (Fin r → F)) × (Fin r → F) | f (q.1.1, q.1.2 + q.2) = f q.1} :=
    isOpen_setOf_eq_of_isLocallyConstant (hfl.comp_continuous (by fun_prop))
      (hfl.comp_continuous continuous_fst)
  obtain ⟨u1, v1, -, hv1, hKu, h0v, huv⟩ :=
    generalized_tube_lemma hK (isCompact_singleton (x := (0 : Fin r → F))) hn1 (by
      rintro ⟨p, w⟩ ⟨-, hw⟩
      simp only [Set.mem_singleton_iff] at hw
      subst hw
      simp)
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hv1 0 (h0v rfl)
  have inv1 : ∀ x b (w : Fin r → F), ‖w‖ < δ → f (x, b + w) = f (x, b) := by
    intro x b w hw
    have hwv : w ∈ v1 := hball (by simpa using hw)
    by_cases hxb : (x, b) ∈ tsupport f
    · exact huv (⟨hKu hxb, hwv⟩ : ((x, b), w) ∈ u1 ×ˢ v1)
    · by_cases hxbw : (x, b + w) ∈ tsupport f
      · have hmw : -w ∈ v1 := hball (by simpa using hw)
        have := huv (⟨hKu hxbw, hmw⟩ : ((x, b + w), -w) ∈ u1 ×ˢ v1)
        simp only [Set.mem_setOf_eq, add_neg_cancel_right] at this
        exact this.symm
      · rw [image_eq_zero_of_notMem_tsupport hxb, image_eq_zero_of_notMem_tsupport hxbw]
  have hzero : ∀ x b, b ∉ Prod.snd '' tsupport f → f (x, b) = 0 := fun x b hb =>
    image_eq_zero_of_notMem_tsupport (fun h => hb ⟨_, h, rfl⟩)
  refine ⟨?_, ?_⟩
  · rw [IsLocallyConstant.iff_eventually_eq]
    rintro ⟨x0, u0⟩
    have hdot : Continuous fun q : (X × (Fin r → F)) × (Fin r → F) => q.2 ⬝ᵥ q.1.2 := by
      unfold dotProduct; fun_prop
    have hdot0 : Continuous fun q : (X × (Fin r → F)) × (Fin r → F) => q.2 ⬝ᵥ u0 := by
      unfold dotProduct; fun_prop
    have hn2 : IsOpen {q : (X × (Fin r → F)) × (Fin r → F) |
        f (q.1.1, q.2) * ψ (q.2 ⬝ᵥ q.1.2) = f (x0, q.2) * ψ (q.2 ⬝ᵥ u0)} :=
      isOpen_setOf_eq_of_isLocallyConstant
        ((hfl.comp_continuous (by fun_prop)).comp₂ (hψl.comp_continuous hdot) (· * ·))
        ((hfl.comp_continuous (by fun_prop)).comp₂ (hψl.comp_continuous hdot0) (· * ·))
    obtain ⟨u2, v2, hu2, -, hxu, hKv, hu2n⟩ :=
      generalized_tube_lemma (isCompact_singleton (x := (x0, u0))) (hK.image continuous_snd) hn2 (by
        rintro ⟨p, b⟩ ⟨hp, -⟩
        simp only [Set.mem_singleton_iff] at hp
        subst hp
        simp)
    filter_upwards [hu2.mem_nhds (hxu rfl)] with p hp
    refine integral_congr_ae (Eventually.of_forall fun b => ?_)
    by_cases hb : b ∈ Prod.snd '' tsupport f
    · exact hu2n (⟨hp, hKv hb⟩ : (p, b) ∈ u2 ×ˢ v2)
    · simp only [hzero _ _ hb, zero_mul]
  · obtain ⟨a, ha, -⟩ := hψ.2
    refine HasCompactSupport.intro
      ((hK.image continuous_fst).prod (isCompact_closedBall (0 : Fin r → F) (‖a‖ / δ))) ?_
    rintro ⟨x, u⟩ hxu
    rw [Set.mem_prod, not_and_or] at hxu
    rcases hxu with hx | hu
    · have h0 : ∀ b, f (x, b) = 0 := fun b =>
        image_eq_zero_of_notMem_tsupport (fun h => hx ⟨_, h, rfl⟩)
      simp [h0]
    · rw [mem_closedBall_zero_iff, not_le] at hu
      obtain ⟨i, hi⟩ : ∃ i, ‖a‖ / δ < ‖u i‖ := by
        by_contra h
        push_neg at h
        exact (not_le.2 hu) ((pi_norm_le_iff_of_nonneg (by positivity)).2 h)
      have hui : u i ≠ 0 := by
        intro h
        rw [h, norm_zero] at hi
        exact (not_lt.2 (by positivity)) hi
      classical
      have hw : ‖(Pi.single i (a / u i) : Fin r → F)‖ < δ := by
        rw [Pi.norm_single, norm_div, div_lt_iff₀ (norm_pos_iff.2 hui)]
        rw [div_lt_iff₀ hδ] at hi
        linarith
      have hwu : (Pi.single i (a / u i) : Fin r → F) ⬝ᵥ u = a := by
        rw [single_dotProduct]; field_simp
      have key := hμ (fun b => f (x, b) * ψ (b ⬝ᵥ u)) (Pi.single i (a / u i))
      have hsh : ∀ b, f (x, b + Pi.single i (a / u i)) * ψ ((b + Pi.single i (a / u i)) ⬝ᵥ u) =
          (f (x, b) * ψ (b ⬝ᵥ u)) * ψ a := by
        intro b
        rw [inv1 x b _ hw, add_dotProduct, AddChar.map_add_eq_mul, hwu]
        ring
      simp only [hsh, integral_mul_const] at key
      show ∫ b, f (x, b) * ψ (b ⬝ᵥ u) ∂μ = 0
      by_contra hI
      exact ha (mul_left_cancel₀ hI (key.trans (mul_one _).symm))
end GlobalTheory.JR.WeilMix
