-- Prove2me | solution 1 for GroundTheory.Global.HeckeCharacter.exists_toIdele_pow_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:17:37.907865+00:00
-- url     : https://prove2.me/submissions/b579f2ed-d327-4703-bef5-a929d971bfa7

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_HeckeCharRayClass
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_FiniteOrderParams
import Theorems.Thm_GroundTheory_Global_HeckeCharacter_toIdele_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open Topology Filter NumberField IsDedekindDomain Function Complex
open scoped NumberField.AdeleRing
open GroundTheory GroundTheory.Global
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
open GroundTheory.Global.HeckeCharacter
open IdeleGroup
variable (χ : HeckeCharacter K)
namespace GroundTheory.Global.HeckeCharacter
theorem _root_.solution (h : IsOfFinOrder χ) :
    ∃ n : ℕ, 0 < n ∧ ∀ x : IdeleGroup K, χ.toIdele x ^ n = 1 := by
  obtain ⟨n, hn, hχ⟩ := isOfFinOrder_iff_pow_eq_one.1 h
  refine ⟨n, hn, fun x ↦ ?_⟩
  rw [toIdele_apply, ← ContinuousMonoidHom.pow_apply, hχ]
  rfl
end GroundTheory.Global.HeckeCharacter
