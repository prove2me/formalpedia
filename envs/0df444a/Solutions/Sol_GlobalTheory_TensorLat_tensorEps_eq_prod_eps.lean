-- Prove2me | solution 1 for GlobalTheory.TensorLat.tensorEps_eq_prod_eps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:03:38.026367+00:00
-- url     : https://prove2.me/submissions/c4f74b8f-625c-4d61-8f54-7fcc016c2666

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ActEMemSpanOmega
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TiledBoundaries_ETSymmApply
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_LatticeCovolumes_InhabSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_FlatMemLatIffStdLat
import Theorems.Thm_GlobalTheory_TensorLat_tensorEps_eq_prod
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
namespace GlobalTheory.TensorLat
theorem _root_.solution (X : PT E) (w₀ : 𝓞 E)
    (heps : ∀ x ∈ X.L, (X.eps x : ℝ) = Real.cos (Real.pi * (Hf x (act w₀ x)).im))
    {γ : Fin n → Vsp X.dim} (hγ : ∀ k, γ k ∈ X.L) :
    tensorEps w₀ γ = ∏ k, (X.eps (γ k) : ℂ) := by
  rw [tensorEps_eq_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  obtain ⟨m, hm⟩ := X.integral _ _ (hγ k) (X.stable w₀ _ (hγ k))
  have h1 := heps _ (hγ k)
  rw [hm, mul_comm, Real.cos_int_mul_pi] at h1
  have h2 : (X.eps (γ k) : ℂ) = (-1) ^ m := by simpa using congrArg (fun t : ℝ => (t : ℂ)) h1
  rw [hm, h2, mul_comm, Complex.ofReal_intCast, Complex.exp_int_mul, Complex.exp_pi_mul_I]
end GlobalTheory.TensorLat
