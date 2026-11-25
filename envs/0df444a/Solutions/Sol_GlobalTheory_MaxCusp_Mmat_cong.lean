-- Prove2me | solution 1 for GlobalTheory.MaxCusp.Mmat_cong
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:17:50.859031+00:00
-- url     : https://prove2.me/submissions/f1eeb5d6-8ba6-4966-93fb-b4e5c4b33fb6

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientSupportHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FixedPointImaginarySpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsHermOfMemLZ
import Theorems.Thm_GlobalTheory_MaxCusp_Mmat_mulVec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_DataX_discr_mul_hermitian_integral
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_Mmat_mulVec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_smul_mem_of_int


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.MaxCusp
open NumberField Complex MeasureTheory Matrix ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r d : ℕ}
variable (X : Data E r)
variable (Y : DataX E r)
namespace GlobalTheory.MaxCusp
theorem _root_.solution (u : Fin d → Fin r → E) (hmem : ∀ i, u i ∈ Y.Λ) (β : Matrix (Fin d) (Fin d) E)
    (hβ : ∀ i k, ∃ γ : E, IsIntegral ℤ γ ∧ β i k = ((Y.g * dEnat E : ℕ) : E) / 2 * γ) :
    ∀ v ∈ Y.Λ, ∃ y ∈ Y.Λ, Mmat Y.toData u β *ᵥ v - v = (Y.g : E) • y := by
  intro v hv
  choose γ hγi hγ using hβ
  set D := (NumberField.discr E).natAbs with hd
  have hint : ∀ k, IsIntegral ℤ ((D : E) * (Y.ξ0 * herm Y.Gm v (u k))) :=
    fun k => Y.discr_mul_hermitian_integral hv (hmem k)
  have hc : ∀ i k, IsIntegral ℤ (Y.κ0 / 2 * D * γ i k * herm Y.Gm v (u k)) := by
    intro i k
    rcases Y.κ0_xi with h | h
    · have e1 : Y.κ0 / 2 * D * γ i k * herm Y.Gm v (u k) =
          γ i k * ((D : E) * (Y.ξ0 * herm Y.Gm v (u k))) := by
        rw [h]; ring
      rw [e1]; exact (hγi i k).mul (hint k)
    · have e1 : Y.κ0 / 2 * D * γ i k * herm Y.Gm v (u k) =
          -(γ i k * ((D : E) * (Y.ξ0 * herm Y.Gm v (u k)))) := by
        rw [h]; ring
      rw [e1]; exact ((hγi i k).mul (hint k)).neg
  set c : Fin d → E := fun i => ∑ k, Y.κ0 / 2 * D * γ i k * herm Y.Gm v (u k) with hcdef
  have hci : ∀ i, IsIntegral ℤ (c i) := fun i => IsIntegral.sum _ fun k _ => hc i k
  refine ⟨∑ i, c i • u i, Submodule.sum_mem _ fun i _ => smul_mem_of_int Y.Λ (hci i) (hmem i), ?_⟩
  rw [Mmat_mulVec, add_sub_cancel_left, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_smul]
  congr 1
  simp only [hcdef, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hγ i k, hd]
  unfold dEnat
  push_cast
  ring
end GlobalTheory.MaxCusp
