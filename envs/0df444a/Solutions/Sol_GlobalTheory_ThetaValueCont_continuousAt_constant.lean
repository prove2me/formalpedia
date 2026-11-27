-- Prove2me | solution 1 for GlobalTheory.ThetaValueCont.continuousAt_constant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:34:55.656199+00:00
-- url     : https://prove2.me/submissions/7a6a3ba9-78bc-435c-b3cd-189bd078a9a5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_EqOfFiniteOfClosedFibres
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsUnitOfLagrangian
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsCoordinatesOfRelations
import Theorems.Thm_GlobalTheory_ThetaFamily_exists_entire_quotient
import Theorems.Thm_GlobalTheory_ThetaFamily_exists_quotient_closure
import Theorems.Thm_GlobalTheory_differentiableOn_quotient_of_differentiableOn_slice

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Filter Set
open scoped Topology
namespace GlobalTheory.ThetaValueCont
open GlobalTheory.ThetaFamily
open Filter Set in
open scoped Topology in
private theorem exists_differentiableOn_ne_zero_mul_eq {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {O : Set E} (hO : IsOpen O) {θ f : E → ℂ}
    (hnz : ∀ z, ∃ᶠ w in 𝓝 z, θ w ≠ 0)
    (hloc : ∀ z ∈ O, ∃ ρ : E → ℂ, ρ z ≠ 0 ∧
      ∀ᶠ w in 𝓝 z, DifferentiableAt ℂ ρ w ∧ ρ w * θ w = f w) :
    ∃ F : E → ℂ, DifferentiableOn ℂ F O ∧ (∀ z ∈ O, F z ≠ 0) ∧ ∀ z ∈ O, F z * θ z = f z := by
  choose! ρ hρ0 hρ using hloc
  refine ⟨fun z ↦ ρ z z, ?_, hρ0, fun z hz ↦ (hρ z hz).self_of_nhds.2⟩
  have heq : ∀ z ∈ O, (fun w ↦ ρ w w) =ᶠ[𝓝 z] ρ z := by
    intro z hz
    filter_upwards [(hρ z hz).eventually_nhds, hO.mem_nhds hz] with w hw hwO
    have h1 := hρ w hwO
    have hc1 : ContinuousAt (ρ w) w := h1.self_of_nhds.1.continuousAt
    have hc2 : ContinuousAt (ρ z) w := hw.self_of_nhds.1.continuousAt
    refine tendsto_nhds_unique_of_frequently_eq hc1 hc2 ?_
    refine ((hnz w).and_eventually (h1.and hw)).mono fun y hy ↦ ?_
    obtain ⟨hθ, ⟨_, h1y⟩, ⟨_, h2y⟩⟩ := hy
    exact mul_right_cancel₀ hθ (h1y.trans h2y.symm)
  intro z hz
  exact (((hρ z hz).self_of_nhds.1).congr_of_eventuallyEq (heq z hz)).differentiableWithinAt
open Filter Set in
open scoped Topology in
private theorem eq_of_continuousAt_mul_eq_eventually {E : Type} [TopologicalSpace E] {θ f ρ₁ ρ₂ : E → ℂ} {z : E}
    (hnz : ∃ᶠ w in 𝓝 z, θ w ≠ 0) (h₁ : ContinuousAt ρ₁ z) (h₂ : ContinuousAt ρ₂ z)
    (e₁ : ∀ᶠ w in 𝓝 z, ρ₁ w * θ w = f w) (e₂ : ∀ᶠ w in 𝓝 z, ρ₂ w * θ w = f w) :
    ρ₁ z = ρ₂ z := by
  refine tendsto_nhds_unique_of_frequently_eq h₁ h₂ ?_
  refine (hnz.and_eventually (e₁.and e₂)).mono fun y hy ↦ ?_
  exact mul_right_cancel₀ hy.1 (hy.2.1.trans hy.2.2.symm)
end GlobalTheory.ThetaValueCont
end

set_option autoImplicit false
open Filter Set
open scoped Topology
open GlobalTheory GlobalTheory.ThetaValueCont
open GlobalTheory.ThetaFamily
open Filter Set
open scoped Topology
namespace GlobalTheory.ThetaValueCont
namespace _root_.GlobalTheory.ThetaValueCont
theorem _root_.solution {V V' K ι : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
    [NormedAddCommGroup V'] [NormedSpace ℂ V'] [FiniteDimensional ℂ V'] {B : Set V} {b₀ : V}
    {W : ι → Set (V × V')} {f : ι → V × V' → ℂ} {θ : K → V × V' → ℂ} {C : Set K} (hC : C.Finite) {κ : V → K}
    {c : V → ℂ} {r : ι → V → ℂ} (hW : ∀ j, IsOpen (W j)) (hWB : ∀ j, ∀ w ∈ W j, w.1 ∈ B)
    (hf : ∀ j, DifferentiableOn ℂ (f j) (W j)) (hθ : ∀ k ∈ C, ∀ j, DifferentiableOn ℂ (θ k) (W j))
    (hnz : ∀ k ∈ C, ∀ b ∈ B, ∀ z, ∃ᶠ w in 𝓝 z, θ k (b, w) ≠ 0) (hκ : ∀ b ∈ B, κ b ∈ C)
    (hq : ∀ j b z, (b, z) ∈ W j → ∃ ρ : V' → ℂ, ρ z ≠ 0 ∧ (z = 0 → ρ 0 = c b * r j b) ∧
      ∀ᶠ w in 𝓝 z, DifferentiableAt ℂ ρ w ∧ ρ w * θ (κ b) (b, w) = f j (b, w))
    (hB : B ∈ 𝓝 b₀) (cov : ∀ z, ∃ j, (b₀, z) ∈ W j)
    (uniq : ∀ k ∈ C, ∀ ρ : V' → ℂ, Differentiable ℂ ρ → (∀ z, ρ z ≠ 0) →
      (∀ z, ρ z * θ (κ b₀) (b₀, z) = θ k (b₀, z)) → k = κ b₀)
    (hr : ∀ j, (b₀, 0) ∈ W j → ContinuousAt (r j) b₀ ∧ r j b₀ ≠ 0) : ContinuousAt c b₀ := by
  classical
  have hb₀B : b₀ ∈ B := mem_of_mem_nhds hB
  have hκ₀ : κ b₀ ∈ C := hκ b₀ hb₀B
  have hslice : ∀ j b, IsOpen {z : V' | (b, z) ∈ W j} := fun j b ↦
    (hW j).preimage (continuous_const.prodMk continuous_id)
  have hF : ∀ j, ∀ b ∈ B, ∃ F : V' → ℂ, DifferentiableOn ℂ F {z | (b, z) ∈ W j} ∧
      (∀ z ∈ {z | (b, z) ∈ W j}, F z ≠ 0) ∧
      ∀ z ∈ {z | (b, z) ∈ W j}, F z * θ (κ b) (b, z) = f j (b, z) := fun j b hb ↦
    exists_differentiableOn_ne_zero_mul_eq (hslice j b) (hnz _ (hκ b hb) b hb)
      (fun z hz ↦ by
        obtain ⟨ρ, h0, -, hρ⟩ := hq j b z hz
        exact ⟨ρ, h0, hρ⟩)
  have hev : ∀ᶠ b in 𝓝 b₀, κ b = κ b₀ := by
    by_contra hne
    rw [not_eventually] at hne
    obtain ⟨k, hk, hfreq⟩ : ∃ k ∈ C, ∃ᶠ b in 𝓝 b₀, b ∈ B ∧ κ b = k ∧ k ≠ κ b₀ := by
      by_contra hall
      have h1 : ∀ k ∈ C, ∀ᶠ b in 𝓝 b₀, ¬ (b ∈ B ∧ κ b = k ∧ k ≠ κ b₀) := fun k hk ↦
        not_frequently.1 (fun h ↦ hall ⟨k, hk, h⟩)
      have h2 := (Filter.eventually_all_finite hC).2 h1
      refine (hne.and_eventually (h2.and hB)).exists.elim fun b hb ↦ ?_
      exact hb.2.1 (κ b) (hκ b hb.2.2) ⟨hb.2.2, rfl, hb.1⟩
    set S : Set V := {b | b ∈ B ∧ κ b = k} with hSdef
    have hS : ∀ j, ∀ b ∈ S, ∃ F : V' → ℂ, DifferentiableOn ℂ F {z | (b, z) ∈ W j} ∧
        (∀ z ∈ {z | (b, z) ∈ W j}, F z ≠ 0) ∧
        ∀ z ∈ {z | (b, z) ∈ W j}, F z * θ k (b, z) = f j (b, z) := by
      intro j b hb
      obtain ⟨F, h1, h2, h3⟩ := hF j b hb.1
      rw [hb.2] at h3
      exact ⟨F, h1, h2, h3⟩
    have hb₀S : b₀ ∈ closure S :=
      mem_closure_iff_frequently.2 (hfreq.mono fun b hb ↦ ⟨hb.1, hb.2.1⟩)
    have hloc : ∀ z, ∃ ρ : V' → ℂ, ρ z ≠ 0 ∧ ∀ᶠ w in 𝓝 z,
        DifferentiableAt ℂ ρ w ∧ ρ w * θ (κ b₀) (b₀, w) = θ k (b₀, w) := by
        intro z
        obtain ⟨j, hj⟩ := cov z
        obtain ⟨ρ, hρz, -, hρ⟩ := hq j b₀ z hj
        have hρne : ∀ᶠ w in 𝓝 z, ρ w ≠ 0 := hρ.self_of_nhds.1.continuousAt.eventually_ne hρz
        have hfnz : ∃ᶠ w in 𝓝 z, f j (b₀, w) ≠ 0 :=
          ((hnz _ hκ₀ b₀ hb₀B z).and_eventually (hρne.and hρ)).mono fun w hw ↦ by
            rw [← hw.2.2.2]
            exact mul_ne_zero hw.2.1 hw.1
        obtain ⟨U₁, G₁, hU₁, hzU₁, -, hG₁, hG₁e⟩ := _root_.GlobalTheory.ThetaFamily.exists_quotient_closure (hW j) (hf j)
          (hθ k hk j) (fun b hb ↦ (hS j b hb).elim fun F hF ↦ ⟨F, hF.1, hF.2.2⟩) hj
          (hnz k hk b₀ hb₀B z)
        obtain ⟨U₂, G₂, hU₂, hzU₂, -, hG₂, hG₂e⟩ := _root_.GlobalTheory.ThetaFamily.exists_quotient_closure (hW j)
          (hθ k hk j) (hf j) (S := S) (fun b hb ↦ (hS j b hb).elim fun F hF ↦
            ⟨F⁻¹, hF.1.inv hF.2.1, fun z hz ↦ by
              rw [← hF.2.2 z hz, Pi.inv_apply, inv_mul_cancel_left₀ (hF.2.1 z hz)]⟩) hj hfnz
        have hcont : Continuous fun w : V' ↦ (b₀, w) := continuous_const.prodMk continuous_id
        have hU₁z : ∀ᶠ w in 𝓝 z, (b₀, w) ∈ U₁ := hcont.continuousAt.preimage_mem_nhds
          (hU₁.mem_nhds hzU₁)
        have hU₂z : ∀ᶠ w in 𝓝 z, (b₀, w) ∈ U₂ := hcont.continuousAt.preimage_mem_nhds
          (hU₂.mem_nhds hzU₂)
        have hG₁c : ContinuousAt (fun w ↦ G₁ (b₀, w)) z :=
          ((hG₁.continuousOn.continuousAt (hU₁.mem_nhds hzU₁))).comp hcont.continuousAt
        have hG₂c : ContinuousAt (fun w ↦ G₂ (b₀, w)) z :=
          ((hG₂.continuousOn.continuousAt (hU₂.mem_nhds hzU₂))).comp hcont.continuousAt
        have hone : G₁ (b₀, z) * G₂ (b₀, z) = 1 := by
          refine tendsto_nhds_unique_of_frequently_eq (hG₁c.mul hG₂c) tendsto_const_nhds ?_
          refine (hfnz.and_eventually (hU₁z.and hU₂z)).mono fun w hw ↦ ?_
          have e₁ := hG₁e _ hw.2.1 hb₀S
          have e₂ := hG₂e _ hw.2.2 hb₀S
          refine mul_right_cancel₀ hw.1 ?_
          show G₁ (b₀, w) * G₂ (b₀, w) * f j (b₀, w) = 1 * f j (b₀, w)
          rw [one_mul, mul_assoc, e₂, e₁]
        refine ⟨fun w ↦ G₂ (b₀, w) * ρ w, mul_ne_zero (right_ne_zero_of_mul_eq_one hone) hρz, ?_⟩
        filter_upwards [hρ, hU₂z] with w hw hw₂
        refine ⟨((hG₂.differentiableAt (hU₂.mem_nhds hw₂)).comp w
          ((differentiableAt_const _).prodMk differentiableAt_id)).mul hw.1, ?_⟩
        rw [mul_assoc, hw.2, hG₂e _ hw₂ hb₀S]
    obtain ⟨ρ, hρd, hρ0, hρ⟩ := _root_.GlobalTheory.ThetaFamily.exists_entire_quotient
      (θ := fun z ↦ θ k (b₀, z)) (θ' := fun z ↦ θ (κ b₀) (b₀, z)) (hnz _ hκ₀ b₀ hb₀B) hloc
    exact (hfreq.exists.elim fun b hb ↦ hb.2.2) (uniq k hk ρ hρd hρ0 hρ)
  obtain ⟨j, hj⟩ := cov 0
  obtain ⟨hrc, hr0⟩ := hr j hj
  obtain ⟨N, hNsub, hNo, hb₀N⟩ := eventually_nhds_iff.1 (hev.and hB)
  choose! Fs hFsd hFs0 hFse using hF j
  set Wst : Set (V × V') := W j ∩ Prod.fst ⁻¹' N with hWst
  have hWo : IsOpen Wst := (hW j).inter (hNo.preimage continuous_fst)
  have hFd : DifferentiableOn ℂ (fun y : V × V' ↦ Fs y.1 y.2) Wst :=
    _root_.GlobalTheory.differentiableOn_quotient_of_differentiableOn_slice V V' Wst (f j) (θ (κ b₀)) _ hWo
      ((hf j).mono inter_subset_left) ((hθ _ hκ₀ j).mono inter_subset_left)
      (fun w hw ↦ by
        obtain ⟨hκw, hBw⟩ := hNsub w.1 hw.2
        have h := hFse w.1 hBw w.2 hw.1
        rw [hκw] at h
        exact h)
      (fun b z hz ↦ ((hFsd b (hNsub b hz.2).2).mono fun z' hz' ↦ hz'.1) z hz)
      (fun w hw ↦ hnz _ hκ₀ w.1 (hNsub w.1 hw.2).2 w.2)
  have hmem : (b₀, (0 : V')) ∈ Wst := ⟨hj, hb₀N⟩
  have hpair : Continuous fun b : V ↦ (b, (0 : V')) := continuous_id.prodMk continuous_const
  have hFc : ContinuousAt (fun b ↦ Fs b 0) b₀ :=
    ContinuousAt.comp (f := fun b : V ↦ (b, (0 : V'))) (g := fun y : V × V' ↦ Fs y.1 y.2)
      (hFd.continuousOn.continuousAt (hWo.mem_nhds hmem)) hpair.continuousAt
  refine (hFc.div hrc hr0).congr ?_
  have hWz : ∀ᶠ b in 𝓝 b₀, (b, (0 : V')) ∈ Wst :=
    hpair.continuousAt.preimage_mem_nhds (hWo.mem_nhds hmem)
  filter_upwards [hWz, hrc.eventually_ne hr0] with b hb hrb
  obtain ⟨-, hBb⟩ := hNsub b hb.2
  obtain ⟨ρ, -, h0, hρ⟩ := hq j b 0 hb.1
  have hFsc : ContinuousAt (Fs b) 0 :=
    (hFsd b hBb).continuousOn.continuousAt ((hslice j b).mem_nhds hb.1)
  have heq : Fs b 0 = ρ 0 := eq_of_continuousAt_mul_eq_eventually (hnz _ (hκ b hBb) b hBb 0) hFsc
    hρ.self_of_nhds.1.continuousAt
    (by
      filter_upwards [(hslice j b).mem_nhds hb.1] with w hw
      exact hFse b hBb w hw)
    (hρ.mono fun w hw ↦ hw.2)
  show Fs b 0 / r j b = c b
  rw [heq, h0 rfl, mul_div_cancel_right₀ _ hrb]
end _root_.GlobalTheory.ThetaValueCont
end GlobalTheory.ThetaValueCont
