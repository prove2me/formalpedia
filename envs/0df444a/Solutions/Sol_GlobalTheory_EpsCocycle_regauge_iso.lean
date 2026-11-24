-- Prove2me | solution 1 for GlobalTheory.EpsCocycle.regauge_iso
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:06:20.915721+00:00
-- url     : https://prove2.me/submissions/00610c51-c52c-408d-a4c2-6fc262b0fb12

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSymm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ConstThickeningComplexFunctionsStructure
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsLineBundleCocycleOneAddEps
import Theorems.Thm_GlobalTheory_EpsCocycle_res_res
import Theorems.Thm_GlobalTheory_EpsCocycle_cocycle_on

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
open GlobalTheory GlobalTheory.EpsCocycle
noncomputable section
namespace GlobalTheory.EpsCocycle
theorem _root_.solution {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) (u : ∀ i, Γ(X, L.U i)ˣ) :
    LBIso L (regauge L u) := by
  refine ⟨⟨fun p : L.ι × L.ι => ((res inf_le_left (u p.1))⁻¹ * L.g p.1 p.2 :
    Γ(X, L.U p.1 ⊓ L.U p.2)ˣ)⟩, ?_⟩
  rintro ⟨a, b⟩ ⟨a', b'⟩
  let W : X.Opens := L.U a ⊓ L.U b ⊓ (L.U a' ⊓ L.U b')
  have ha : W ≤ L.U a := inf_le_left.trans inf_le_left
  have hb : W ≤ L.U b := inf_le_left.trans inf_le_right
  have ha' : W ≤ L.U a' := inf_le_right.trans inf_le_left
  have hb' : W ≤ L.U b' := inf_le_right.trans inf_le_right
  change res (le_inf ha hb) ((res inf_le_left (u a))⁻¹ * L.g a b) =
    (res (le_inf ha ha') ((res inf_le_left (u a))⁻¹ * L.g a a' * res inf_le_right (u a')) *
      (res (le_inf hb hb') (L.g b b'))⁻¹) *
      res (le_inf ha' hb') ((res inf_le_left (u a'))⁻¹ * L.g a' b')
  have e₁ := cocycle_on hL a a' b' (le_inf ha ha') (le_inf ha' hb') (le_inf ha hb')
  have e₂ := cocycle_on hL a b b' (le_inf ha hb) (le_inf hb hb') (le_inf ha hb')
  have e₃ : res (le_inf ha hb) (L.g a b) = res (le_inf ha ha') (L.g a a') *
      res (le_inf ha' hb') (L.g a' b') * (res (le_inf hb hb') (L.g b b'))⁻¹ := by
    rw [e₁, ← e₂, mul_inv_cancel_right]
  simp only [map_mul, map_inv, res_res, e₃]
  generalize res ha (u a) = x
  generalize res ha' (u a') = y
  generalize res (le_inf ha ha') (L.g a a') = z
  generalize res (le_inf ha' hb') (L.g a' b') = w
  generalize res (le_inf hb hb') (L.g b b') = v
  rw [mul_mul_mul_comm _ v⁻¹, mul_inv_cancel_right]
  ac_rfl
end GlobalTheory.EpsCocycle
