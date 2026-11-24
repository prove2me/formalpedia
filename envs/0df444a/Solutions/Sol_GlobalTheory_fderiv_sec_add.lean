-- Prove2me | solution 1 for GlobalTheory.fderiv_sec_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:06:08.296792+00:00
-- url     : https://prove2.me/submissions/76b9ce00-0417-4b29-aec3-f2ff9d1fdb86

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_LevelThreeSeparatesTangents
import Theorems.Thm_GlobalTheory_hasFDerivAt_Hf_left

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ReciprocityTheory.ChartRestriction.G.I2 Filter Topology
open GlobalTheory
variable {ι : Type} [Fintype ι]
namespace GlobalTheory
theorem _root_.solution (Y : GT ι) {θ : EuclideanSpace ℂ ι → ℂ} (hθ : θ ∈ Y.Sec 1)
    {γ : EuclideanSpace ℂ ι} (hγ : γ ∈ lat Y.b) (a c : EuclideanSpace ℂ ι) :
    fderiv ℂ θ (a + γ) c * θ a = θ (a + γ) * (Real.pi * Hf c γ * θ a + fderiv ℂ θ a c) := by
  obtain ⟨hd, hl⟩ := hθ
  obtain ⟨A, hA, hA'⟩ := hasFDerivAt_Hf_left γ a
  have h1 : HasFDerivAt (fun v => θ (v + γ)) (fderiv ℂ θ (a + γ)) a :=
    (hasFDerivAt_comp_add_right γ).2 (hd _).hasFDerivAt
  have h2 := ((((hA'.const_mul (((1 : ℕ) : ℂ) * Real.pi)).add_const
    (((1 : ℕ) : ℂ) * Real.pi * Hf γ γ / 2)).cexp).const_mul (Y.ka γ)).mul (hd a).hasFDerivAt
  have h3 : (fun v => θ (v + γ)) = _ := funext (hl γ hγ)
  rw [h3] at h1
  have h4 := congrArg (fun B => B c) (h1.unique h2)
  rw [h4, hl γ hγ a]
  simp [hA]
  ring
end GlobalTheory
