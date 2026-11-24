-- Prove2me | solution 1 for GlobalTheory.ThetaTranslSpan.exists_eq_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:47:05.137894+00:00
-- url     : https://prove2.me/submissions/2b9389b4-9b82-473f-80c8-59c3fed18247

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_FourierCoeffUnitCubeTranslateOfEntirePeriodic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_EntirePeriodicEqZeroOfFourierCoeffEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_CardLePowOfLinearIndependent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsUnitOfLagrangian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_CardLePowOfLinearIndependentThetaPrincipal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsImEqLattice
import Theorems.Thm_GlobalTheory_ThetaTranslSpan_span_eq_top
import Theorems.Thm_GlobalTheory_ThetaTranslSpan_exists_im_eq_lattice
import Theorems.Thm_GlobalTheory_ThetaTranslSpan_herm_swap
import Theorems.Thm_GlobalTheory_ClassicalTheta_card_le_pow_of_linearIndependent
import Theorems.Thm_GlobalTheory_SiegelNormalForm_exists_normal_form
import Theorems.Thm_GlobalTheory_card_le_pow_of_linearIndependent_theta_principal
import Theorems.Thm_GlobalTheory_entire_periodic_eq_zero_of_fourierCoeff_eq_zero
import Theorems.Thm_GlobalTheory_fourierCoeff_unitCube_translate_of_entire_periodic
import Theorems.Thm_GlobalTheory_orthogonalQuotientForm_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.orthogonalQuotientForm_mk



set_option autoImplicit false
open Matrix
open scoped ComplexOrder
open GlobalTheory GlobalTheory.ThetaTranslSpan
variable {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ}
namespace GlobalTheory.ThetaTranslSpan
theorem _root_.solution (hH : Hm.PosDef) (Λ : AddSubgroup (Fin g → ℂ)) [hd : DiscreteTopology Λ]
    (hΛ : ∀ v, (∀ a ∈ Λ, ∃ k : ℤ, (star v ⬝ᵥ Hm.mulVec a).im = k) ↔ v ∈ Λ)
    (χ θ G : (Fin g → ℂ) → ℂ) (hχ : ∀ a ∈ Λ, ‖χ a‖ = 1) (hθ : Differentiable ℂ θ) (h0 : θ ≠ 0)
    (hθt : ∀ a ∈ Λ, ∀ z, θ (z + a) = χ a * Complex.exp (Real.pi * (star a ⬝ᵥ Hm.mulVec z) +
      Real.pi / 2 * (star a ⬝ᵥ Hm.mulVec a)) * θ z) (hG : Differentiable ℂ G)
    (hGt : ∀ a ∈ Λ, ∀ z, G (z + a) = χ a * Complex.exp (Real.pi * (star a ⬝ᵥ Hm.mulVec z) +
      Real.pi / 2 * (star a ⬝ᵥ Hm.mulVec a)) * G z) : ∃ c : ℂ, G = c • θ := by
  let L : Submodule ℤ (Fin g → ℂ) := AddSubgroup.toIntSubmodule Λ
  haveI hL : DiscreteTopology L := hd
  have hsp : Submodule.span ℝ (L : Set (Fin g → ℂ)) = ⊤ := span_eq_top hH Λ fun v => (hΛ v).1
  have htr : ∀ z u : Fin g → ℂ, z ⬝ᵥ Hmᵀ.mulVec (star u) = star u ⬝ᵥ Hm.mulVec z := fun z u => by
    rw [mulVec_transpose, dotProduct_comm, dotProduct_mulVec]
  have hsk : ∀ z u : Fin g → ℂ, (star u ⬝ᵥ Hm.mulVec z).im = -(star z ⬝ᵥ Hm.mulVec u).im :=
    fun z u => by rw [herm_swap hH z u]; simp
  have hint : ∀ l m : L, ∃ k : ℤ,
      (k : ℝ) = (star (m : Fin g → ℂ) ⬝ᵥ Hm.mulVec (l : Fin g → ℂ)).im := fun l m => by
    obtain ⟨k, hk⟩ := (hΛ m).2 m.2 l l.2
    exact ⟨k, hk.symm⟩
  choose k hk using hint
  let Ef : LinearMap.BilinForm ℤ L := LinearMap.mk₂ ℤ k
    (fun a b m => Int.cast_injective (α := ℝ) (by
      rw [Int.cast_add, hk, hk, hk, Submodule.coe_add, mulVec_add, dotProduct_add,
        Complex.add_im]))
    (fun t a m => Int.cast_injective (α := ℝ) (by
      rw [smul_eq_mul, Int.cast_mul, hk, hk, Submodule.coe_smul, mulVec_smul, dotProduct_smul]
      simp))
    (fun m a b => Int.cast_injective (α := ℝ) (by
      rw [Int.cast_add, hk, hk, hk, Submodule.coe_add, star_add, add_dotProduct,
        Complex.add_im]))
    (fun t m a => Int.cast_injective (α := ℝ) (by
      rw [smul_eq_mul, Int.cast_mul, hk, hk, Submodule.coe_smul, star_smul, smul_dotProduct]
      simp))
  have hE : ∀ l m : L, (Ef l m : ℝ) =
      (star (m : Fin g → ℂ) ⬝ᵥ Hm.mulVec (l : Fin g → ℂ)).im := hk
  have hbij : Function.Bijective Ef := by
    refine ⟨(injective_iff_map_eq_zero Ef).2 fun l hl => ?_, fun φ => ?_⟩
    · by_contra hne
      have h1 := hH.dotProduct_mulVec_pos (x := (l : Fin g → ℂ)) fun h => hne (Subtype.ext h)
      have h : ∀ m, (star (l : Fin g → ℂ) ⬝ᵥ Hm.mulVec m).im = 0 := by
        intro m
        have hm : m ∈ Submodule.span ℝ (L : Set (Fin g → ℂ)) := hsp ▸ Submodule.mem_top
        induction hm using Submodule.span_induction with
        | mem m hm => rw [hsk, ← hE l ⟨m, hm⟩, hl]; simp
        | zero => simp
        | add a b _ _ ha hb => rw [mulVec_add, dotProduct_add, Complex.add_im, ha, hb, add_zero]
        | smul t a _ ha => rw [mulVec_smul, dotProduct_smul, Complex.smul_im, ha, smul_zero]
      have h2 := h (Complex.I • (l : Fin g → ℂ))
      rw [mulVec_smul, dotProduct_smul] at h2
      simp at h2
      have := (Complex.pos_iff.1 h1).1
      linarith
    · obtain ⟨y, hy⟩ := exists_im_eq_lattice hH L hsp (-(Algebra.linearMap ℤ ℝ ∘ₗ φ))
      have hyΛ : y ∈ Λ := (hΛ y).1 fun a ha => ⟨-φ ⟨a, ha⟩, by rw [hy ⟨a, ha⟩]; simp⟩
      refine ⟨⟨y, hyΛ⟩, LinearMap.ext fun a => Int.cast_injective (α := ℝ) ?_⟩
      rw [hE, hsk, hy]; simp
  have hli : ¬ LinearIndependent ℂ ![θ, G] := fun hli => by
    have := GlobalTheory.card_le_pow_of_linearIndependent_theta_principal
      GlobalTheory.SiegelNormalForm.exists_normal_form
      (GlobalTheory.ClassicalTheta.card_le_pow_of_linearIndependent
        GlobalTheory.fourierCoeff_unitCube_translate_of_entire_periodic
        (GlobalTheory.entire_periodic_eq_zero_of_fourierCoeff_eq_zero
          GlobalTheory.fourierCoeff_unitCube_translate_of_entire_periodic))
      g L hL hsp Hmᵀ (fun l => χ l) Ef hH.isHermitian.transpose
      (fun z hz => by rw [htr]; exact (Complex.pos_iff.1 (hH.dotProduct_mulVec_pos hz)).1)
      (fun l => hχ l l.2) (fun l m => by rw [htr, hE]) hbij 1 le_rfl 2 ![θ, G]
      (fun k => by
        fin_cases k
        · exact ⟨hθ, fun l z => by rw [pow_one, htr, htr]; exact hθt l l.2 z⟩
        · exact ⟨hG, fun l z => by rw [pow_one, htr, htr]; exact hGt l l.2 z⟩) hli
    simp at this
  rw [LinearIndependent.pair_iff' h0] at hli
  push_neg at hli
  obtain ⟨a, ha⟩ := hli
  exact ⟨a, ha.symm⟩
end GlobalTheory.ThetaTranslSpan
