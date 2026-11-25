-- Prove2me | solution 1 for GlobalTheory.TensorLat.mem_stdLat_iff_herm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:47:52.62184+00:00
-- url     : https://prove2.me/submissions/21d29bdf-3a5e-452f-a16b-65189db46bf7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ActEMemSpanOmega
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TiledBoundaries_ETSymmApply
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_LatticeCovolumes_InhabSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_FlatMemLatIffStdLat
import Theorems.Thm_GlobalTheory_TensorLat_mem_stdLat
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_actE_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_dim
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.I2.actE_apply



set_option autoImplicit false
open GlobalTheory GlobalTheory.TensorLat
open NumberField Complex ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.GeometryOfNumbersTheory (stdLat)
noncomputable section
variable {E : Type} [Field E] [NumberField E] {dim : (E →+* ℂ) → ℕ} {n : ℕ}
variable [IsCMField E]
variable {X : PT E} {Λ' : Submodule (𝓞 E) (Fin n → E)}
namespace GlobalTheory.TensorLat
theorem _root_.solution {v : Fin n → E} :
    v ∈ stdLat E n ↔ ∀ w ∈ stdLat E n, IsIntegral ℤ (herm 1 v w) := by
  have hh : ∀ w, herm 1 v w = ∑ k, v k * cc (w k) := fun w => by simp [herm, Matrix.one_apply]
  constructor
  · intro hv w hw
    rw [hh]
    exact IsIntegral.sum _ fun k _ => (mem_stdLat.1 hv k).mul
      ((mem_stdLat.1 hw k).map (IsCMField.complexConj E).toRingEquiv.toRingHom.toIntAlgHom)
  · intro h
    refine mem_stdLat.2 fun k => ?_
    have := h (Pi.single k 1) (Submodule.subset_span ⟨k, rfl⟩)
    rw [hh, Finset.sum_eq_single k] at this
    · simpa [cc] using this
    · intro j _ hj
      simp [hj, cc]
    · simp
end GlobalTheory.TensorLat
