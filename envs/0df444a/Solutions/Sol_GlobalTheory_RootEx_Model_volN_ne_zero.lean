-- Prove2me | solution 1 for GlobalTheory.RootEx.Model.volN_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:08:11.398373+00:00
-- url     : https://prove2.me/submissions/891add1b-23c7-4ba4-80ad-7fcb6b3749ec

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSumRowCol
import Theorems.Thm_GlobalTheory_RootEx_Model_coord_embedding

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal
noncomputable section
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.Model
open GlobalTheory.SplitWeil GlobalTheory.RootEx
variable {k : Type*} [Field k] {n : Type*} [Fintype n] [DecidableEq n] {c : ℕ}
variable [MeasurableSpace k]
namespace GlobalTheory.RootEx.Model
theorem _root_.solution (ν : Measure k) [SigmaFinite ν] (hν : ν ≠ 0) (p : ℕ) : volN ν n c p ≠ 0 := by
  classical
  intro h
  have h1 : volN ν n c p Set.univ = 0 := by rw [h]; rfl
  unfold volN at h1
  rw [(coord_embedding (k := k) (n := n) (c := c) p).1.comap_apply, Set.image_univ, (coord_embedding (k := k) (n := n) (c := c) p).2.range_eq, Measure.pi_univ] at h1
  obtain ⟨_, _, h2⟩ := Finset.prod_eq_zero_iff.1 h1
  exact hν (Measure.measure_univ_eq_zero.1 h2)
end GlobalTheory.RootEx.Model
