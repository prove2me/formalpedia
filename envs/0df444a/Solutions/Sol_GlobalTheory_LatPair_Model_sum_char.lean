-- Prove2me | solution 1 for GlobalTheory.LatPair.Model.sum_char
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:12:33.12337+00:00
-- url     : https://prove2.me/submissions/ede018a1-07ad-42f1-bc38-034201750d8c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_HasConductorMulShift
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SecondCountableAndT2LocalField
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ExistsFFNeZeroThree

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
open GlobalTheory GlobalTheory.LatPair GlobalTheory.LatPair.Model
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n n' : Type*}
variable {M : Type*} [AddCommGroup M] [Module ℂ M]
namespace GlobalTheory.LatPair.Model
theorem _root_.solution {V : Type*} [AddCommGroup V] [Module 𝓀[k] V] [Fintype V] {χ : AddChar 𝓀[k] ℂ} (hχ : χ ≠ 1)
    (g : Module.Dual 𝓀[k] V) [Decidable (g = 0)] : ∑ x, χ (g x) = if g = 0 then (Fintype.card V : ℂ) else 0 := by
  split_ifs with hg
  · simp [hg]
  · refine (AddChar.sum_eq_zero_iff_ne_zero (ψ := χ.compAddMonoidHom g.toAddMonoidHom)).2 fun h => hχ ?_
    ext a
    obtain ⟨x, rfl⟩ := LinearMap.surjective hg a
    exact DFunLike.congr_fun h x
end GlobalTheory.LatPair.Model
