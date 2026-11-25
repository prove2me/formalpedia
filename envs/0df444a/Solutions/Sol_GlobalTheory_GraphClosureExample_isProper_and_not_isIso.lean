-- Prove2me | solution 1 for GlobalTheory.GraphClosureExample.isProper_and_not_isIso
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:47:42.817551+00:00
-- url     : https://prove2.me/submissions/a119a539-989c-4dfe-b448-fc5b17531e7a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_FlatImageOfOverFractionFieldOfValuationRing
import Theorems.Thm_GlobalTheory_graphClosure_exists_extension_of_isIso_fst
import Theorems.Thm_GlobalTheory_GraphClosureExample_isFinite_str

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
universe u
open GlobalTheory
noncomputable section
open GlobalTheory.GraphClosureExample
namespace GlobalTheory.GraphClosureExample
theorem _root_.solution :
    IsProper (graphClosure.fst (str (-4)) (str (-1)) openPart partialMap comm) ∧
      IsIso (graphClosure.fst (str (-4)) (str (-1)) openPart partialMap comm ∣_
        openPart.opensRange) ∧
      ¬ IsIso (graphClosure.fst (str (-4)) (str (-1)) openPart partialMap comm) := by
  have := isFinite_str (-1)
  refine ⟨inferInstance, inferInstance, fun _ ↦ ?_⟩
  obtain ⟨ψ, -, -⟩ :=
    graphClosure.exists_extension_of_isIso_fst (str (-4)) (str (-1)) openPart partialMap comm
  obtain ⟨g, rfl⟩ := Spec.map_surjective ψ
  have h := congrArg g.hom (Zsqrtd.dmuld (d := -1))
  rw [map_mul, map_intCast] at h
  have h' := congrArg Zsqrtd.re h
  generalize g.hom Zsqrtd.sqrtd = z at h'
  simp only [Zsqrtd.re_mul, Zsqrtd.re_intCast] at h'
  have h4 : z.re * z.re % 4 = 0 ∨ z.re * z.re % 4 = 1 := by
    have : z.re % 4 = 0 ∨ z.re % 4 = 1 ∨ z.re % 4 = 2 ∨ z.re % 4 = 3 := by omega
    rcases this with h | h | h | h <;> simp [Int.mul_emod, h]
  rw [mul_assoc] at h'
  omega
end GlobalTheory.GraphClosureExample
