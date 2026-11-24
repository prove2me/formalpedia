-- Prove2me | solution 1 for GlobalTheory.LatPair.cross_dia_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:23:45.235488+00:00
-- url     : https://prove2.me/submissions/8b265eb4-e894-40a2-b078-acb2d6d0ae8b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ExistsGlOfEquiv
import Theorems.Thm_GlobalTheory_LatPair_Pair_dia_hasVal_one
import Theorems.Thm_GlobalTheory_LatPair_cross_hasVal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Matrix IsLocalRing
open scoped Pointwise
noncomputable section
open GlobalTheory GlobalTheory.LatPair
variable (k : Type*) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {k}
variable {n n' : Type*}
namespace GlobalTheory.LatPair
theorem _root_.solution (q : Unif k) {P₁ P : Pair k n} (h : P.lat = P₁.ker) (c : 𝓀[k]ˣ) :
    cross q (c • P₁) P = (c⁻¹ : 𝓀[k]ˣ) * cross q P₁ P := by
  obtain ⟨s, hs⟩ := residue_surjective (R := 𝒪[k]) (c⁻¹ : 𝓀[k]ˣ)
  have h1 := cross_hasVal q (P₁ := c • P₁) (h.trans (Pair.dia_ker _ _).symm) (Pair.dia_hasVal_one P₁.hasVal_vec hs)
  rw [smul_comm] at h1
  rw [h1.unique ((cross_hasVal q h P₁.hasVal_vec).smul s), hs]
end GlobalTheory.LatPair
