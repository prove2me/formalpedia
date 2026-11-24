-- Prove2me | solution 1 for GlobalTheory.LatPair.conj_resChar
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:07:39.537196+00:00
-- url     : https://prove2.me/submissions/b75892b7-537b-4055-bd46-a8b7aa301b69

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ExistsGlOfEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_HasConductorMulShift
import Theorems.Thm_GlobalTheory_LatPair_resChar_residue

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
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n n' : Type*}
open SplitWeil
namespace GlobalTheory.LatPair
theorem _root_.solution {ψ : AddChar k Circle} (hψ : HasConductor ψ 1) (q : Unif k) (a : 𝓀[k]) :
    (starRingEnd ℂ) (resChar ψ hψ q a) = resChar ψ hψ q (-a) := by
  obtain ⟨s, rfl⟩ := residue_surjective (R := 𝒪[k]) a
  rw [← map_neg, resChar_residue, resChar_residue, ← Circle.coe_inv_eq_conj, ← AddChar.map_neg_eq_inv]
  simp
end GlobalTheory.LatPair
