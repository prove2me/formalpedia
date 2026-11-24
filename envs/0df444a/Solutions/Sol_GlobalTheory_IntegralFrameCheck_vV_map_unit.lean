-- Prove2me | solution 1 for GlobalTheory.IntegralFrameCheck.vV_map_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:08:33.493802+00:00
-- url     : https://prove2.me/submissions/db212325-c69d-4d0a-966d-1d38c89bf241

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IntAllFree
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_VVAlgebraMapNonneg
import Theorems.Thm_GlobalTheory_IntegralFrameCheck_vV_algebraMap_nonneg
import Theorems.Thm_GlobalTheory_IntegralFrameCheck_vV_one
import Theorems.Thm_Formalism_L2_Pj_vV_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.IntegralFrameCheck
open Formalism.L2.Pj NumberField IsDedekindDomain
open scoped WithZero
variable {V K' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K'] [Algebra V K']
  [IsFractionRing V K']
variable {V' K'' : Type} [CommRing V'] [IsDomain V'] [IsDiscreteValuationRing V'] [Field K''] [Algebra V' K'']
  [IsFractionRing V' K'']
namespace GlobalTheory.IntegralFrameCheck
theorem _root_.solution (i : K' →+* K'') (hi : ∀ a : V, i (algebraMap V K' a) ∈ Set.range (algebraMap V' K''))
    (u : Vˣ) : vV V' (i (algebraMap V K' u)) = 0 := by
  have hne : ∀ w : Vˣ, i (algebraMap V K' w) ≠ 0 := fun w =>
    ((w.isUnit.map (algebraMap V K')).map i).ne_zero
  have h0 : ∀ w : Vˣ, 0 ≤ vV V' (i (algebraMap V K' w)) := fun w => by
    obtain ⟨b, hb⟩ := hi w
    rw [← hb]; exact vV_algebraMap_nonneg b
  have h1 := vV_mul (V := V') (hne u) (hne u⁻¹)
  rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one, vV_one] at h1
  have := h0 u
  have := h0 u⁻¹
  omega
end GlobalTheory.IntegralFrameCheck
