-- Prove2me | solution 1 for GlobalTheory.JR.image_openClosed_section
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:46:09.11509+00:00
-- url     : https://prove2.me/submissions/3bb434df-da2c-43c3-86b2-734fa9836774

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CompanionMatrixOfCoeffsPowMulVecFirstBasisVector
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitaryActionHermitianInvariantsTransitiveStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsContinuousCongruenceNearSymmetricMatrixStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CompanionMatrixOfCoeffsCharpolyCoeffEqStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_BorderedMatrixInvariantSpaceExistsCompactOpenSubStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitaryOrbitProperOfInvertibleKrylovColumnsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ContinuousOnHermitianBlockMatrixOfInvariantsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_InvariantImageOpenClosedLocalSections
import Theorems.Thm_GlobalTheory_JR_ImgSec_exists_compact_open_nhd
import Theorems.Thm_GlobalTheory_JR_ImgSec_isCompact_orbit
import Theorems.Thm_GlobalTheory_JR_ImgSec_continuousOn_mkX
import Theorems.Thm_GlobalTheory_JR_ImgSec_hasInv_mkX
import Theorems.Thm_GlobalTheory_JR_ImgSec_bm_mkX
import Theorems.Thm_GlobalTheory_JR_ImgSec_conjTranspose_map
import Theorems.Thm_GlobalTheory_JR_ImgSec_continuousStar
import Theorems.Thm_GlobalTheory_JR_ImgSec_continuous_delta
import Theorems.Thm_GlobalTheory_JR_ImgSec_continuous_hankel
import Theorems.Thm_GlobalTheory_JR_ImgSec_hankel_isSymm
import Theorems.Thm_GlobalTheory_JR_OrbProper_isCompact_orbit
import Theorems.Thm_GlobalTheory_T_exists_continuous_congruence_near_symmetric_matrix
import Theorems.Thm_GlobalTheory_T_unitary_action_hermitian_invariants_transitive


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory.JR.ImgSec
namespace GlobalTheory.JR
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (a₀ : Inv r F), Delta a₀ ≠ 0 → ((¬ ∃ X : Hn r F E, HasInv X a₀) → ∀ᶠ a in 𝓝 a₀, ¬ ∃ X : Hn r F E, HasInv X a) ∧ ((∃ X : Hn r F E, HasInv X a₀) → ∃ (Ω : Set (Inv r F)) (s : Inv r F → Hn r F E), IsCompact Ω ∧ IsOpen Ω ∧ a₀ ∈ Ω ∧ ContinuousOn s Ω ∧ (∀ a ∈ Ω, Delta a ≠ 0 ∧ HasInv (s a) a) ∧ ∀ C : Set (Hn r F E), IsCompact C → IsCompact {p : Matrix.unitaryGroup (Fin r) E × Inv r F | p.2 ∈ Ω ∧ actU p.1 (s p.2) ∈ C}) := by
  intro F E _ _ _ _ _ r a₀ hΔ
  haveI := continuousStar (E := E) F
  obtain ⟨-, -, -, hcrit⟩ := GlobalTheory.T.unitary_action_hermitian_invariants_transitive F E r
  obtain ⟨Ω₁, κ, hΩ₁, hH₀, hκ, -, hκeq⟩ := GlobalTheory.T.exists_continuous_congruence_near_symmetric_matrix F E r (hankel a₀) (hankel_isSymm a₀) hΔ
  set φ := algebraMap F E with hφ
  let U : Set (Inv r F) := {a | Delta a ≠ 0} ∩ (fun a => hankel a) ⁻¹' Ω₁
  have hU : IsOpen U := (isOpen_ne_fun continuous_delta continuous_const).inter (hΩ₁.preimage continuous_hankel)
  have ha₀ : a₀ ∈ U := ⟨hΔ, hH₀⟩
  have hK : ∀ a ∈ U, (κ (hankel a))ᵀ * hankel a₀ * κ (hankel a) = hankel a :=
    fun a ha => hκeq _ ha.2 (hankel_isSymm a)
  have hKd : ∀ a ∈ U, IsUnit (κ (hankel a)).det := by
    intro a ha
    refine isUnit_iff_ne_zero.2 fun h0 => ha.1 ?_
    have := congrArg Matrix.det (hK a ha)
    rw [det_mul, det_mul, h0, mul_zero] at this
    exact this.symm
  have hdm : ∀ M : Matrix (Fin r) (Fin r) F, (M.map φ).det = φ M.det := fun M => (RingHom.map_det φ M).symm
  have hKd' : ∀ a ∈ U, IsUnit ((κ (hankel a)).map φ).det := fun a ha => by
    rw [hdm]; exact (hKd a ha).map φ
  have hmapK : ∀ a ∈ U, ((κ (hankel a)).map φ)ᴴ * ((hankel a₀).map φ * (κ (hankel a)).map φ) = (hankel a).map φ := by
    intro a ha
    rw [ImgSec.conjTranspose_map, ← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.mul_assoc, hK a ha]
  have transport : ∀ a ∈ U, (∃ h : Matrix (Fin r) (Fin r) E, hᴴ * h = (hankel a).map φ) →
      ∃ h : Matrix (Fin r) (Fin r) E, hᴴ * h = (hankel a₀).map φ := by
    rintro a ha ⟨h, hh⟩
    set K' := (κ (hankel a)).map φ
    have hu' : IsUnit K'ᴴ.det := by rw [det_conjTranspose]; exact (hKd' a ha).star
    refine ⟨h * K'⁻¹, ?_⟩
    rw [conjTranspose_mul, conjTranspose_nonsing_inv]
    calc K'ᴴ⁻¹ * hᴴ * (h * K'⁻¹) = K'ᴴ⁻¹ * (hᴴ * h) * K'⁻¹ := by simp only [Matrix.mul_assoc]
      _ = K'ᴴ⁻¹ * (K'ᴴ * ((hankel a₀).map φ * K')) * K'⁻¹ := by rw [hh, ← hmapK a ha]
      _ = (hankel a₀).map φ := by
        rw [nonsing_inv_mul_cancel_left _ _ hu', mul_nonsing_inv_cancel_right _ _ (hKd' a ha)]
  refine ⟨fun hno => ?_, fun hex => ?_⟩
  · filter_upwards [hU.mem_nhds ha₀] with a ha
    rintro ⟨X, hX⟩
    apply hno
    rw [hcrit a₀ hΔ]
    exact transport a ha ((hcrit a ha.1).1 ⟨X, hX⟩)
  · obtain ⟨h₀, hh₀⟩ := (hcrit a₀ hΔ).1 hex
    have hd₀ : IsUnit h₀.det := by
      refine isUnit_iff_ne_zero.2 fun h0 => ?_
      have := congrArg Matrix.det hh₀
      rw [det_mul, h0, mul_zero, hdm] at this
      exact hΔ ((map_eq_zero_iff φ φ.injective).1 this.symm)
    obtain ⟨Ω, hΩc, hΩo, ha₀Ω, hΩU⟩ := exists_compact_open_nhd F E r U a₀ hU ha₀
    let hf : Inv r F → Matrix (Fin r) (Fin r) E := fun a => h₀ * (κ (hankel a)).map φ
    have hhf : ∀ a ∈ U, (hf a)ᴴ * hf a = (hankel a).map φ := by
      intro a ha
      simp only [hf]
      rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc h₀ᴴ, hh₀, hmapK a ha]
    have hdf : ∀ a ∈ U, IsUnit (hf a).det := fun a ha => by
      simp only [hf]; rw [det_mul]; exact hd₀.mul (hKd' a ha)
    have hcf : ContinuousOn hf Ω := by
      have h1 : ContinuousOn (fun a => κ (hankel a)) Ω :=
        hκ.comp continuous_hankel.continuousOn fun a ha => (hΩU ha).2
      exact continuousOn_const.mul ((continuous_id.matrix_map (continuous_algebraMap F E)).comp_continuousOn h1)
    have hcs : ContinuousOn (fun a => mkX a (hf a)) Ω :=
      continuousOn_mkX F E r Ω hf hcf fun a ha => hdf a (hΩU ha)
    refine ⟨Ω, fun a => mkX a (hf a), hΩc, hΩo, ha₀Ω, hcs,
      fun a ha => ⟨(hΩU ha).1, hasInv_mkX (hhf a (hΩU ha)) (hdf a (hΩU ha))⟩, ?_⟩
    intro C hC
    exact isCompact_orbit F E r Ω (fun a => mkX a (hf a)) hf hΩc hcs hcf
      (fun a ha => ⟨hdf a (hΩU ha), bm_mkX (hhf a (hΩU ha)) (hdf a (hΩU ha))⟩) C hC
end GlobalTheory.JR
