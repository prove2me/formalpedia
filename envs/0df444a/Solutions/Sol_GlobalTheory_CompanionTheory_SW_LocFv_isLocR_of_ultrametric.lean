-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.LocFv.isLocR_of_ultrametric
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:47:05.201796+00:00
-- url     : https://prove2.me/submissions/dfe5a186-5453-4cbe-933a-908992baca44

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_LocAtA
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_CompletionIsLocalRing
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_LocFv_isOpenEmbedding_units_val
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.LocFv
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
namespace GlobalTheory.CompanionTheory.SW.LocFv
theorem _root_.solution (K : Type) [NontriviallyNormedField K] [IsUltrametricDist K] [ProperSpace K]
    (h2 : (2 : K) ≠ 0) : IsLocR K := by
  have hd : HasStrictDerivAt (fun x : K => x ^ 2) (2 : K) 1 := by
    simpa using hasStrictDerivAt_pow 2 (1 : K)
  have hf := hd.hasStrictFDerivAt_equiv h2
  let e := hf.toOpenPartialHomeomorph _
  have he : (e : K → K) = fun x => x ^ 2 := hf.toOpenPartialHomeomorph_coe
  have h1 : (1 : K) ∈ e.source := hf.mem_toOpenPartialHomeomorph_source
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 e.open_source 1 h1
  obtain ⟨r, hr0, hrε, hr1⟩ : ∃ r : ℝ, 0 < r ∧ r < ε ∧ r < 1 :=
    ⟨min (ε / 2) (1 / 2), lt_min (by linarith) (by norm_num),
      lt_of_le_of_lt (min_le_left _ _) (by linarith), lt_of_le_of_lt (min_le_right _ _) (by norm_num)⟩
  have hsub : Metric.closedBall (1 : K) r ⊆ e.source :=
    (Metric.closedBall_subset_ball hrε).trans hball
  have hopen : IsOpen (Metric.closedBall (1 : K) r) :=
    IsUltrametricDist.isOpen_closedBall _ hr0.ne'
  have hnorm : ∀ a ∈ Metric.closedBall (1 : K) r, ‖a‖ = 1 := by
    intro a ha
    rw [mem_closedBall_iff_norm] at ha
    have hlt : ‖a - 1‖ < ‖(1 : K)‖ := by rw [norm_one]; linarith
    have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hlt.ne
    rw [sub_add_cancel, max_eq_right hlt.le, norm_one] at this
    exact this
  let U : Subgroup Kˣ :=
    { carrier := Units.val ⁻¹' Metric.closedBall (1 : K) r
      one_mem' := by simp [hr0.le]
      mul_mem' := by
        intro a b ha hb
        have hna := hnorm _ ha
        simp only [Set.mem_preimage, mem_closedBall_iff_norm, Units.val_mul] at ha hb ⊢
        have : (a : K) * b - 1 = a * (b - 1) + (a - 1) := by ring
        rw [this]
        refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ha)
        rwa [norm_mul, hna, one_mul]
      inv_mem' := by
        intro a ha
        have hna := hnorm _ ha
        simp only [Set.mem_preimage, mem_closedBall_iff_norm] at ha ⊢
        have h0 : (a : K) ≠ 0 := a.ne_zero
        have : (((a⁻¹ : Kˣ)) : K) - 1 = -((a : K)⁻¹ * (a - 1)) := by
          rw [Units.val_inv_eq_inv_val]; field_simp; ring
        rwa [this, norm_neg, norm_mul, norm_inv, hna, inv_one, one_mul] }
  have hval := isOpenEmbedding_units_val K
  have hU : IsOpen (U : Set Kˣ) := hopen.preimage Units.continuous_val
  have e1 : IsOpenEmbedding (fun u : U => ((u : Kˣ) : K)) := hval.comp hU.isOpenEmbedding_subtypeVal
  have hmem : ∀ u : U, ((u : Kˣ) : K) ∈ e.source := fun u => hsub u.2
  refine ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    hval, U, hU, ?_⟩
  refine IsOpenEmbedding.of_comp _ hval ?_
  refine IsOpenEmbedding.of_continuous_injective_isOpenMap ?_ ?_ ?_
  · exact Units.continuous_val.comp (continuous_subtype_val.pow 2)
  · intro u w h
    simp only [Function.comp, Units.val_pow_eq_pow_val] at h
    refine e1.injective (e.injOn (hmem u) (hmem w) ?_)
    rw [he]; exact h
  · intro s hs
    have himg : (Units.val ∘ fun u : U => ((u : Kˣ) ^ 2 : Kˣ)) '' s =
        e '' ((fun u : U => ((u : Kˣ) : K)) '' s) := by
      rw [he, Set.image_image]
      simp [Function.comp, Units.val_pow_eq_pow_val]
    rw [himg]
    refine e.isOpen_image_of_subset_source (e1.isOpenMap s hs) ?_
    rintro _ ⟨u, -, rfl⟩
    exact hmem u
end GlobalTheory.CompanionTheory.SW.LocFv
