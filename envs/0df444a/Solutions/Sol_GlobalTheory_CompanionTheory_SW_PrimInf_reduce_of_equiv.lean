-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.PrimInf.reduce_of_equiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:30:45.576794+00:00
-- url     : https://prove2.me/submissions/5e31a0f1-093e-479f-80e1-03f2286f5f50

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_HypJ
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRing
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ArchimedeanPrimitiveVectorCompactRescale

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PrimInf
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
namespace GlobalTheory.CompanionTheory.SW.PrimInf
theorem _root_.solution {K : Type} [CommRing K] [TopologicalSpace K] {W : Type} [Fintype W]
    (Φ : K ≃+* (W → ℂ)) (hΦ : IsHomeomorph Φ) (M : ℕ) :
    ∃ Ω : Set (Fin 1 → Fin M → K), IsCompact Ω ∧ ∀ y : Fin 1 → Fin M → K,
      (∃ z : Fin M → K, z ⬝ᵥ y 0 = 1) →
      ∃ (a : Kˣ) (z : Fin 1 → Fin M → K), (a : K) • y ∈ Ω ∧ z ∈ Ω ∧ z 0 ⬝ᵥ ((a : K) • y) 0 = 1 := by
  classical
  let e : K ≃ₜ (W → ℂ) := hΦ.homeomorph
  have he : ∀ x, e x = Φ x := fun _ => rfl
  let H : (Fin 1 → Fin M → K) ≃ₜ (Fin 1 → Fin M → W → ℂ) :=
    Homeomorph.piCongrRight fun _ => Homeomorph.piCongrRight fun _ => e
  let P : Set (Fin 1 → Fin M → W → ℂ) :=
    Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Metric.closedBall 0 1
  have hP : IsCompact P :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_univ_pi fun _ =>
      isCompact_closedBall 0 1
  have hmem : ∀ y, y ∈ H ⁻¹' P ↔ ∀ a i w, ‖Φ (y a i) w‖ ≤ 1 := by
    intro y
    simp only [Set.mem_preimage, P, Set.mem_pi, Set.mem_univ, true_imp_iff, mem_closedBall_zero_iff]
    rfl
  refine ⟨H ⁻¹' P, H.isCompact_preimage.mpr hP, ?_⟩
  rintro y ⟨z₀, hz₀⟩
  have hsum : ∀ w, ∑ i, Φ (z₀ i) w * Φ (y 0 i) w = 1 := by
    intro w
    have := congrFun (congrArg Φ hz₀) w
    simpa [dotProduct, map_sum, Finset.sum_apply] using this
  have hmax : ∀ w, ∃ i, (∀ j, ‖Φ (y 0 j) w‖ ≤ ‖Φ (y 0 i) w‖) ∧ Φ (y 0 i) w ≠ 0 := by
    intro w
    obtain ⟨i₀, hi₀⟩ : ∃ i, Φ (y 0 i) w ≠ 0 := by
      by_contra hall
      push_neg at hall
      have := hsum w
      simp [hall] at this
    haveI : Nonempty (Fin M) := ⟨i₀⟩
    obtain ⟨i, hi⟩ := Finite.exists_max fun j => ‖Φ (y 0 j) w‖
    refine ⟨i, hi, fun h0 => hi₀ ?_⟩
    have := hi i₀
    rw [h0, norm_zero] at this
    exact norm_le_zero_iff.mp this
  choose I hI hI0 using hmax
  let u : W → ℂ := fun w => Φ (y 0 (I w)) w
  have hu : ∀ w, u w ≠ 0 := hI0
  let a : Kˣ :=
    { val := Φ.symm fun w => (u w)⁻¹
      inv := Φ.symm u
      val_inv := by
        apply Φ.injective
        funext w
        simp [hu w]
      inv_val := by
        apply Φ.injective
        funext w
        simp [hu w] }
  have hΦa : ∀ w, Φ (a : K) w = (u w)⁻¹ := fun w => by simp [a]
  let z : Fin 1 → Fin M → K := fun _ i => Φ.symm fun w => if I w = i then 1 else 0
  have hΦz : ∀ b i w, Φ (z b i) w = if I w = i then 1 else 0 := fun b i w => by simp [z]
  refine ⟨a, z, ?_, ?_, ?_⟩
  · rw [hmem]
    intro b i w
    obtain rfl : b = 0 := Subsingleton.elim _ _
    have : Φ (((a : K) • y) 0 i) w = (u w)⁻¹ * Φ (y 0 i) w := by
      simp [hΦa]
    rw [this, norm_mul, norm_inv]
    have hpos : 0 < ‖u w‖ := norm_pos_iff.mpr (hu w)
    rw [inv_mul_le_iff₀ hpos, mul_one]
    exact hI w i
  · rw [hmem]
    intro b i w
    rw [hΦz b i w]
    split_ifs <;> simp
  · apply Φ.injective
    funext w
    have h1 : ∀ i, Φ (z 0 i) w * Φ (((a : K) • y) 0 i) w =
        if I w = i then (u w)⁻¹ * Φ (y 0 i) w else 0 := by
      intro i
      have : Φ (((a : K) • y) 0 i) w = (u w)⁻¹ * Φ (y 0 i) w := by simp [hΦa]
      rw [this, hΦz 0 i w]
      split_ifs <;> simp
    simp only [dotProduct, map_sum, Finset.sum_apply, map_mul, Pi.mul_apply, map_one, Pi.one_apply]
    rw [Finset.sum_congr rfl fun i _ => h1 i]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
    exact inv_mul_cancel₀ (hu w)
end GlobalTheory.CompanionTheory.SW.PrimInf
