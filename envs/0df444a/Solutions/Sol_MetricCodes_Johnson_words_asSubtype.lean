-- Prove2me | solution 1 for MetricCodes.Johnson.words_asSubtype
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:29.660979+00:00
-- url     : https://prove2.me/submissions/bb654695-363e-46f9-86c4-6c8803d68c5c

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open MetricCodes.Johnson
noncomputable section
open scoped BigOperators InnerProductSpace Matrix
namespace MetricCodes.Johnson
theorem _root_.solution {n w : ℕ}
    (C : Finset (BinaryWord n))
    (hweight : C ⊆ weightShell n w) :
    words (asSubtype C hweight) = C := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨z, _hz, hz⟩ := Finset.mem_image.mp hy
    have hval := congrArg Subtype.val hz
    simpa using hval ▸ z.property
  · intro hx
    let z : {z : BinaryWord n // z ∈ C} := ⟨x, hx⟩
    let y : JohnsonSphere n w :=
      ⟨x, (MetricCodes.mem_weightShell x).mp (hweight hx)⟩
    apply Finset.mem_image.mpr
    refine ⟨y, ?_, rfl⟩
    unfold asSubtype
    apply Finset.mem_image.mpr
    refine ⟨z, by simp, ?_⟩
    exact Subtype.ext rfl
end MetricCodes.Johnson
