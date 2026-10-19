-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.eventually_opening_interlacing
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:37.685478+00:00
-- url     : https://prove2.me/submissions/5457c156-4e6b-47fc-8da8-77698fa62f6a

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
set_option autoImplicit false
open MetricCodes
open MetricCodes.Spherical
open MetricCodes.Spherical.HigherHierarchy
noncomputable section
open Filter Topology
open scoped BigOperators Topology
namespace MetricCodes.Spherical.HigherHierarchy
theorem _root_.solution {r : ℕ}
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b) (hzero : a (Fin.last r) = 0)
    (η : ℝ) :
    ∀ᶠ t : ℝ in 𝓝[>] 0,
      Interlacing (openingAmbient a (η * t) (t ^ 2)) b := by
  have hcontinuous (i : Fin (r + 1)) :
      Continuous (fun t : ℝ => openingAmbient a (η * t) (t ^ 2) i) := by
    unfold openingAmbient
    simp only [Function.update_apply]
    split_ifs <;> fun_prop
  have htend (i : Fin (r + 1)) :
      Tendsto (fun t : ℝ => openingAmbient a (η * t) (t ^ 2) i)
        (nhds 0) (nhds (a i)) := by
    have hi := (hcontinuous i).continuousAt (x := (0 : ℝ))
    convert hi.tendsto using 1; simp [openingAmbient_zero hzero]
  have hpair (i : Fin r) :
      ∀ᶠ t : ℝ in nhds (0 : ℝ),
        b i < openingAmbient a (η * t) (t ^ 2) i.castSucc ∧
          openingAmbient a (η * t) (t ^ 2) i.succ < b i := by
    exact (htend i.castSucc).eventually (lt_mem_nhds (h.2 i).1) |>.and
      ((htend i.succ).eventually (gt_mem_nhds (h.2 i).2))
  have hall : ∀ᶠ t : ℝ in nhds (0 : ℝ), ∀ i : Fin r,
      b i < openingAmbient a (η * t) (t ^ 2) i.castSucc ∧
        openingAmbient a (η * t) (t ^ 2) i.succ < b i :=
    eventually_all.2 hpair
  filter_upwards [nhdsWithin_le_nhds hall] with t ht
  refine ⟨?_, ht⟩
  simp [openingAmbient, sq_nonneg]
end MetricCodes.Spherical.HigherHierarchy
