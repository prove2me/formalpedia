-- Prove2me | solution 1 for GlobalTheory.JR.WeilQuad.LargeLattice.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:57:53.586269+00:00
-- url     : https://prove2.me/submissions/8f1437e7-e6c6-4d7e-9510-d5e3eebf0ee9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsStableGauss
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_QuadraticWeilFourierPreservesTestAdditive
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedStandardAddCharConductorPropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaleHermitianPairStructureFactsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsLargeCompactOpenSubgroupWithSmallDual
import Theorems.Thm_GlobalTheory_JR_WeilQuad_FourierTest_beta_sepLeft
import Theorems.Thm_GlobalTheory_JR_WeilQuad_FourierTest_beta_symm
import Theorems.Thm_GlobalTheory_JR_WeilQuad_FourierTest_finite_F_L
import Theorems.Thm_GlobalTheory_T_unramifiedStandardAddChar_conductor_properties


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.WeilQuad GlobalTheory.JR.WeilQuad.LargeLattice
namespace GlobalTheory.JR.WeilQuad.LargeLattice
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.Kˣ) (μ : Measure A.L) (ω : A.K → ℂ),
    Hyp A ψ x μ ω → ∀ C : Set A.L, IsCompact C → ∀ V ∈ 𝓝 (0 : A.L), ∃ Λ : AddSubgroup A.L,
      IsOpen (Λ : Set A.L) ∧ IsCompact (Λ : Set A.L) ∧ C ⊆ Λ ∧
      {y : A.L | ∀ w ∈ (Λ : Set A.L), A.kerL ψ x w y = 1} ⊆ Λ ∧
      {y : A.L | ∀ w ∈ (Λ : Set A.L), A.kerL ψ x w y = 1} ⊆ V := by
  intro F E _ _ _ _ _ A ψ x μ ω h C hC V hV
  obtain ⟨hK, hL, hψ, -, -⟩ := h
  haveI := FourierTest.finite_F_L A
  haveI : IsUltrametricDist F := Unram.ultraF (F := F) (E := E)
  haveI : LocallyCompactSpace F := Unram.lcF (F := F) (E := E)
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  haveI : ContinuousAdd A.L := IsModuleTopology.toContinuousAdd F A.L
  haveI : ContinuousSMul F A.L := IsModuleTopology.toContinuousSMul F A.L
  have hcond := ((GlobalTheory.T.unramifiedStandardAddChar_conductor_properties F E).2 ψ hψ).2.2.1
  let β := FourierTest.beta A (x : A.K)
  have hker : ∀ w y, A.kerL ψ x w y = ψ (β w y) := fun _ _ => rfl
  let e := Module.finBasis F A.L
  let Φ : A.L →ₗ[F] (Fin (Module.finrank F A.L) → F) := LinearMap.pi (fun i => β (e i))
  have hΦ : ∀ y i, Φ y i = β (e i) y := fun _ _ => rfl
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    apply FourierTest.beta_sepLeft A hK hL x y
    intro w
    have h0 : β.flip y = 0 := e.ext (fun i => by
      simpa [hΦ] using congrFun hy i)
    rw [FourierTest.beta_symm A hK hL]
    simpa using LinearMap.congr_fun h0 w
  have hsurj : Function.Surjective Φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp)).1 hinj
  let Φe := LinearEquiv.ofBijective Φ ⟨hinj, hsurj⟩
  have hΦe : ∀ y, Φe y = Φ y := fun _ => rfl
  have hΦc : Continuous Φ := IsModuleTopology.continuous_of_linearMap Φ
  have hΨc : Continuous Φe.symm :=
    IsModuleTopology.continuous_of_linearMap (Φe.symm : (Fin (Module.finrank F A.L) → F) →ₗ[F] A.L)

  have hV' : Φe.symm ⁻¹' V ∈ 𝓝 (0 : Fin (Module.finrank F A.L) → F) :=
    hΨc.continuousAt.preimage_mem_nhds (by simpa using hV)
  obtain ⟨ε, hε0, hεV⟩ := Metric.mem_nhds_iff.1 hV'
  obtain ⟨t, ht⟩ := NormedField.exists_lt_norm F (1 / ε)
  have ht0 : 0 < ‖t‖ := lt_trans (by positivity) ht
  obtain ⟨b, hb⟩ := hC.exists_bound_of_continuousOn hΦc.continuousOn
  let Km : ℝ := ∑ i, ‖Φ (e i)‖
  have hKm : ∀ i j, ‖Φ (e i) j‖ ≤ Km := fun i j =>
    (norm_le_pi_norm (Φ (e i)) j).trans
      (Finset.single_le_sum (f := fun i => ‖Φ (e i)‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ i))
  let R : ℝ := max (max b (‖t‖ * Km)) (max ε 1)
  have hR1 : 1 ≤ R := le_trans (le_max_right _ _) (le_max_right _ _)
  have hR0 : 0 < R := lt_of_lt_of_le one_pos hR1
  have hRε : ε ≤ R := le_trans (le_max_left _ _) (le_max_right _ _)
  have hRb : b ≤ R := le_trans (le_max_left _ _) (le_max_left _ _)
  have hRt : ‖t‖ * Km ≤ R := le_trans (le_max_right _ _) (le_max_left _ _)
  let Λ : AddSubgroup A.L :=
    { carrier := {y | ∀ i, ‖Φ y i‖ ≤ R}
      add_mem' := by
        intro a c ha hc i
        simp only [Set.mem_setOf_eq, map_add, Pi.add_apply] at *
        exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (ha i) (hc i))
      zero_mem' := by intro i; simp [hR0.le]
      neg_mem' := by
        intro a ha i
        simp only [Set.mem_setOf_eq, map_neg, Pi.neg_apply, norm_neg] at *
        exact ha i }
  have hmem : ∀ y, y ∈ Λ ↔ ∀ i, ‖Φ y i‖ ≤ R := fun _ => Iff.rfl

  have hperp : ∀ y ∈ {y : A.L | ∀ w ∈ (Λ : Set A.L), A.kerL ψ x w y = 1}, ∀ i, ‖Φ y i‖ < ε := by
    intro y hy i
    have h1 : ‖t * Φ y i‖ ≤ 1 := by
      refine (hcond (t * Φ y i)).1 fun e' he' => ?_
      have hw : (e' * t) • e i ∈ Λ := by
        rw [hmem]; intro j
        rw [map_smul, Pi.smul_apply, smul_eq_mul, norm_mul, norm_mul]
        calc ‖e'‖ * ‖t‖ * ‖Φ (e i) j‖ ≤ 1 * ‖t‖ * Km := by gcongr; exact hKm i j
          _ ≤ R := by rw [one_mul]; exact hRt
      have := hy _ hw
      rw [hker, map_smul, LinearMap.smul_apply, smul_eq_mul] at this
      rw [← hΦ] at this
      rwa [← mul_assoc]
    rw [norm_mul] at h1
    have h2 : ‖Φ y i‖ ≤ 1 / ‖t‖ := by rw [le_div_iff₀ ht0]; linarith
    have h3 : 1 / ‖t‖ < ε := by
      rw [div_lt_iff₀ ht0]
      rw [div_lt_iff₀ hε0] at ht
      linarith
    exact lt_of_le_of_lt h2 h3
  refine ⟨Λ, ?_, ?_, ?_, ?_, ?_⟩
  · have : (Λ : Set A.L) = ⋂ i, (fun y => Φ y i) ⁻¹' Metric.closedBall 0 R := by
      ext y; simp [hmem, mem_closedBall_zero_iff]
    rw [this]
    exact isOpen_iInter_of_finite fun i =>
      (IsUltrametricDist.isOpen_closedBall 0 hR0.ne').preimage ((continuous_apply i).comp hΦc)
  · have : (Λ : Set A.L) = Φe.symm '' Metric.closedBall 0 R := by
      ext y
      rw [SetLike.mem_coe, hmem, Set.mem_image]
      constructor
      · intro hy
        refine ⟨Φe y, ?_, by simp⟩
        rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg hR0.le, hΦe]; exact hy
      · rintro ⟨z, hz, rfl⟩
        rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg hR0.le] at hz
        intro i
        have : Φ (Φe.symm z) = z := by rw [← hΦe]; simp
        rw [this]; exact hz i
    rw [this]
    exact (isCompact_closedBall 0 R).image hΨc
  · intro y hy
    rw [SetLike.mem_coe, hmem]
    intro i
    exact ((norm_le_pi_norm (Φ y) i).trans (hb y hy)).trans hRb
  · intro y hy
    rw [SetLike.mem_coe, hmem]
    intro i
    exact (hperp y hy i).le.trans hRε
  · intro y hy
    have hb' : Φe y ∈ Metric.ball (0 : Fin (Module.finrank F A.L) → F) ε := by
      rw [mem_ball_zero_iff, pi_norm_lt_iff hε0, hΦe]; exact hperp y hy
    have := hεV hb'
    simpa using this
end GlobalTheory.JR.WeilQuad.LargeLattice
