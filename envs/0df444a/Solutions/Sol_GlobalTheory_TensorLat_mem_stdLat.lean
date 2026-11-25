-- Prove2me | solution 1 for GlobalTheory.TensorLat.mem_stdLat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:33:41.888881+00:00
-- url     : https://prove2.me/submissions/5556b1c8-1188-4d69-a6ab-75336e4ae5b8

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ActEMemSpanOmega
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TiledBoundaries_ETSymmApply
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_LatticeCovolumes_InhabSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_FlatMemLatIffStdLat
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
omit [IsCMField E]
namespace GlobalTheory.TensorLat
theorem _root_.solution {v : Fin n → E} : v ∈ stdLat E n ↔ ∀ k, IsIntegral ℤ (v k) := by
  rw [stdLat, Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨c, rfl⟩ k
    have : (∑ j, c j • (Pi.single j 1 : Fin n → E)) k = (c k : E) := by
      simp [Finset.sum_apply, Pi.single_apply, Algebra.smul_def]
    rw [this]
    exact (c k).isIntegral_coe
  · intro h
    have hc : ∀ k, ∃ c : 𝓞 E, algebraMap (𝓞 E) E c = v k := fun k => ⟨⟨v k, h k⟩, rfl⟩
    choose c hc using hc
    refine ⟨c, ?_⟩
    funext k
    simp [Finset.sum_apply, Pi.single_apply, Algebra.smul_def, hc]
end GlobalTheory.TensorLat
