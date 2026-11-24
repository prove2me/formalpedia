-- Prove2me | solution 1 for GlobalTheory.existsUnique_linear_lift_of_separating
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:44:32.650443+00:00
-- url     : https://prove2.me/submissions/4cacadca-94ce-4de1-ad1c-33de9889a001

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueRealLinearOfEventuallyAddModDiscrete
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TangentBijectionOfValues
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_ExistsUniqueLinearLiftOfHolomorphicAbelianVariet
import Theorems.Thm_GlobalTheory_tendsto_map_nhds_of_separating
import Theorems.Thm_GlobalTheory_coe_modNEquivTorsion_mk
import Theorems.Thm_GlobalTheory_existsUnique_realLinear_lift_of_germ
import Theorems.Thm_GlobalTheory_realLinear_eq_of_sub_mem_discrete
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.coe_modNEquivTorsion_mk



set_option autoImplicit false
open Filter Topology Set Metric
open GlobalTheory
variable {V W : Type*} [NormedAddCommGroup V] [NormedAddCommGroup W] {A : Type*} [AddCommGroup A]
  {ι : Type*} {Y : Type*} [TopologicalSpace Y] [T2Space Y]
namespace GlobalTheory
theorem _root_.solution [NormedSpace ℂ V] [NormedSpace ℂ W]
    [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] {ex : W →+ A}
    (hex : Function.Surjective ex) (hker : IsDiscrete (ex.ker : Set W))
    {G : V →+ A} {S : Set A} (h0 : (0 : A) ∈ S) {f : ι → A → ℂ}
    (hsep : ∀ a ∈ S, ∀ b ∈ S, (∀ i, f i a = f i b) → a = b)
    (hSe : IsOpen (ex ⁻¹' S)) (hSG : IsOpen (G ⁻¹' S))
    (hfe : ∀ i, DifferentiableOn ℂ (fun w ↦ f i (ex w)) (ex ⁻¹' S))
    (hfG : ∀ i, DifferentiableOn ℂ (fun z ↦ f i (G z)) (G ⁻¹' S))
    (hD : ∀ w, (∀ i, fderiv ℂ (fun w ↦ f i (ex w)) 0 w = 0) → w = 0) :
    ∃! F : V →ₗ[ℂ] W, ∀ z, ex (F z) = G z := by
  have : CompleteSpace V := FiniteDimensional.complete ℂ V
  have : ProperSpace W := FiniteDimensional.proper ℂ W
  have ht := tendsto_map_nhds_of_separating hex h0 hsep hSe hSG
    (fun i ↦ (hfe i).continuousOn) (fun i ↦ (hfG i).continuousOn)
  have ht' : Tendsto G (𝓝 0) (map ex (𝓝 0)) := fun s hs ↦
    (ht _ hs).mono fun z hz ↦ image_preimage_subset _ _ hz
  obtain ⟨U, hU, hU0⟩ := isDiscrete_iff_forall_mem_exists_isOpen.1 hker 0 ex.ker.zero_mem
  obtain ⟨N, hN, hNU⟩ := exists_nhds_half_neg (hU.mem_nhds (hU0.ge rfl).1)
  have hinj : InjOn ex N := fun x hx y hy hxy ↦
    sub_eq_zero.1 (hU0.le ⟨hNU x hx y hy, by simp [AddMonoidHom.mem_ker, hxy]⟩)
  have hs : ∀ᶠ z in 𝓝 0, Function.invFunOn ex N (ex z) = z := by
    filter_upwards [hN] with z hz using hinj.leftInvOn_invFunOn hz
  have hs0 : Function.invFunOn ex N 0 = 0 := by simpa using hs.self_of_nhds
  have hc : ContinuousAt (fun z ↦ Function.invFunOn ex N (G z)) 0 := by
    rw [ContinuousAt, map_zero, hs0]
    have h1 : Tendsto (Function.invFunOn ex N) (map ex (𝓝 0)) (𝓝 0) :=
      tendsto_map'_iff.2 (tendsto_id.congr' (hs.mono fun z hz ↦ hz.symm))
    exact h1.comp ht'
  obtain ⟨L, hL, hu⟩ := existsUnique_realLinear_lift_of_germ (ex := G) hker hc
    ((ht N hN).mono fun z hz ↦ Function.invFunOn_eq hz)
  have hI : ∀ (c : ℂ) z, L (c • z) = c • L z := by
    intro c z
    refine sub_eq_zero.1 (hD _ fun i ↦ ?_)
    have h1 : DifferentiableAt ℂ (fun w ↦ f i (ex w)) 0 :=
      (hfe i).differentiableAt (hSe.mem_nhds (by simpa using h0))
    have h2 : DifferentiableAt ℂ (fun z ↦ f i (G z)) 0 :=
      (hfG i).differentiableAt (hSG.mem_nhds (by simpa using h0))
    have h3 := (h1.hasFDerivAt.restrictScalars ℝ)
    rw [← map_zero L] at h3
    have h4 := h3.comp 0 L.hasFDerivAt
    have h5 : ((fun w ↦ f i (ex w)) ∘ L) = fun z ↦ f i (G z) := by
      funext z
      simp [hL]
    rw [h5, map_zero] at h4
    have h6 := h4.unique (h2.hasFDerivAt.restrictScalars ℝ)
    have h7 : ∀ z, fderiv ℂ (fun w ↦ f i (ex w)) 0 (L z) = fderiv ℂ (fun z ↦ f i (G z)) 0 z :=
      fun z ↦ DFunLike.congr_fun h6 z
    rw [map_sub, h7, map_smul, map_smul, h7, sub_self]
  refine ⟨⟨⟨L, L.map_add⟩, hI⟩, hL, fun F hF ↦ ?_⟩
  have := realLinear_eq_of_sub_mem_discrete hker (L := F.restrictScalars ℝ) (L' := L.toLinearMap)
    fun x ↦ by simp [AddMonoidHom.mem_ker, hF, hL]
  ext z
  exact DFunLike.congr_fun this z
end GlobalTheory
