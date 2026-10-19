-- Prove2me | solution 1 for OAI.CriticalZ3.quarterFace_preimage
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T19:31:09.38251+00:00
-- url     : https://prove2.me/submissions/9d256061-8b46-461e-be26-067246e074b9

import Mathlib
import Definitions.Def_CriticalZ3
import Definitions.Def_OAI_Probability_CriticalZ3_Basic
import Definitions.Def_OAI_Probability_CriticalZ3_ProductCylinder
import Definitions.Def_OAI_Probability_CriticalZ3_Symmetry
import Definitions.Def_OAI_Probability_CriticalZ3_QuarterFaces

open OAI OAI.CriticalZ3
universe uE uI uV uW
open MeasureTheory ProbabilityTheory Classical
open Classical


theorem solution (c : Vertex) (n : ℕ) (f : FaceIndex) :
    (faceSymmetry c f).vertex ⁻¹' QuarterFace c n f = QuarterFace 0 n canonicalFace := by
  ext x
  simp only [Set.mem_preimage, QuarterFace, canonicalFace, faceSymmetry, SignedSymmetry.vertex,
    Equiv.coe_fn_mk, Set.mem_setOf_eq, Pi.zero_apply, zero_add, if_true, Equiv.swap_apply_left]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, fun i hi => ?_⟩
    · split_ifs at h1 <;> omega
    · have hne : Equiv.swap f.1 0 i ≠ f.1 := by
        intro h; apply hi; simpa using congrArg (Equiv.swap f.1 0) h
      have := h2 (Equiv.swap f.1 0 i) hne
      simp only [Equiv.swap_apply_self] at this
      split_ifs at this <;> constructor <;> omega
  · rintro ⟨h1, h2⟩
    refine ⟨?_, fun i hi => ?_⟩
    · split_ifs <;> omega
    · have hne : Equiv.swap f.1 0 i ≠ 0 := by
        intro h; apply hi
        have := congrArg (Equiv.swap f.1 0) h
        simpa using this
      obtain ⟨ha, hb⟩ := h2 _ hne
      by_cases hs : f.2 i = true <;> simp [hs] <;> omega

