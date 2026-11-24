-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m87ex_root_translation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T12:32:55.194662+00:00
-- url     : https://prove2.me/submissions/09ad5b2a-8e95-46e1-a321-6b2beec8796f

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_C
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (ψ : ℝ → ℝ) (c q : ℝ) (hc : 0 ≤ c)
    (hr : PhiIsLargestRoot (shiftedExponent ψ c) q) :
    Phi (shiftedExponent ψ c) q = Phi ψ (q + ψ c) - c := by
  let f := shiftedExponent ψ c
  let R := Phi f q
  have hroot := hr
  have hRmem : R ∈ RightRootSet f q := hroot.2.1
  have hR : R+c ∈ RightRootSet ψ (q+ψ c) := by
    refine ⟨add_nonneg hRmem.1 hc, ?_⟩
    have he := hRmem.2
    change ψ (R+c) - ψ c = q at he
    linarith
  have hmax (z : ℝ) (hz : z ∈ RightRootSet ψ (q+ψ c)) : z ≤ R+c := by
    by_cases h : c ≤ z
    · have hm : z-c ∈ RightRootSet f q := by
        refine ⟨sub_nonneg.mpr h, ?_⟩
        change ψ (z-c+c) - ψ c = q
        rw [sub_add_cancel, hz.2]
        ring
      linarith [hroot.2.2 (z-c) hm]
    · linarith [hRmem.1]
  have hsup : Phi ψ (q+ψ c) = R+c :=
    le_antisymm (csSup_le ⟨_, hR⟩ hmax) (le_csSup ⟨_, hmax⟩ hR)
  change R = Phi ψ (q+ψ c) - c
  rw [hsup, add_sub_cancel_right]
