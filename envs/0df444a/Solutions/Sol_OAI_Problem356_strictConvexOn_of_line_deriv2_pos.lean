-- Prove2me | solution 1 for OAI.Problem356.strictConvexOn_of_line_deriv2_pos
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T21:20:03.940221+00:00
-- url     : https://prove2.me/submissions/7a88db81-32e1-45cb-a14b-84d82aff0e16

import Mathlib
import Definitions.Def_CoulombCounterexample
import Definitions.Def_OAI_Analysis_CoulombTransport_AxisHessian
import Definitions.Def_OAI_Analysis_CoulombTransport_BranchCoupling
import Definitions.Def_OAI_Analysis_CoulombTransport_CoulombEstimates
import Definitions.Def_OAI_Analysis_CoulombTransport_BranchSeparation
import Definitions.Def_OAI_Analysis_CoulombTransport_GraphBridge
import Definitions.Def_OAI_Analysis_CoulombTransport_DualCertificate
import Definitions.Def_OAI_Analysis_CoulombTransport_OptimalLocalization
import Definitions.Def_OAI_Analysis_CoulombTransport_Calibration
import Definitions.Def_OAI_Analysis_CoulombTransport_CertificateAttainment
import Definitions.Def_OAI_Analysis_CoulombTransport_SplitMeasure
import Definitions.Def_OAI_Analysis_CoulombTransport_PartitionLabel
import Definitions.Def_OAI_Analysis_CoulombTransport_CenterCertificate
import Definitions.Def_OAI_Analysis_CoulombTransport_CommonBranches
import Definitions.Def_OAI_Analysis_CoulombTransport_DensityMeasure
import Definitions.Def_OAI_Analysis_CoulombTransport_ComponentPotential
import Definitions.Def_OAI_Analysis_CoulombTransport_LocalImplicit
import Definitions.Def_OAI_Analysis_CoulombTransport_HessianCLM
import Definitions.Def_OAI_Analysis_CoulombTransport_CoulombCalculus
import Definitions.Def_OAI_Analysis_CoulombTransport_StationaryEquation
import Definitions.Def_OAI_Analysis_CoulombTransport_HessianMatrix
import Definitions.Def_OAI_Analysis_CoulombTransport_CoulombCoercivity

open OAI OAI.Problem356
universe uE uP
open Set Filter
open scoped Topology
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]


theorem solution {s : Set E} {f : E → ℝ}
    (hs : Convex ℝ s) (hf : ContinuousOn f s)
    (hpos : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → ∀ t ∈ Ioo (0 : ℝ) 1,
      0 < deriv (deriv (f ∘ AffineMap.lineMap x y)) t) :
    StrictConvexOn ℝ s f := by
  refine ⟨hs, fun x hx y hy hxy a b ha hb hab => ?_⟩
  set g : ℝ → ℝ := f ∘ AffineMap.lineMap x y with hg
  have hmaps : ∀ t ∈ Icc (0:ℝ) 1, AffineMap.lineMap x y t ∈ s := fun t ht =>
    hs.lineMap_mem hx hy ht
  have hgc : ContinuousOn g (Icc 0 1) :=
    hf.comp (AffineMap.lineMap_continuous (R := ℝ)).continuousOn hmaps
  have hgs : StrictConvexOn ℝ (Icc (0:ℝ) 1) g := by
    refine strictConvexOn_of_deriv2_pos (convex_Icc 0 1) hgc fun t ht => ?_
    rw [interior_Icc] at ht
    simpa [Function.iterate_succ, hg] using hpos x hx y hy hxy t ht
  have h0 : (0:ℝ) ∈ Icc (0:ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h1 : (1:ℝ) ∈ Icc (0:ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have := hgs.2 h0 h1 (by norm_num) ha hb hab
  have ea : a = 1 - b := by linarith
  simp only [hg, Function.comp, smul_eq_mul, mul_zero, mul_one, zero_add,
    AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one, AffineMap.lineMap_apply_module] at this
  rw [ea] at this ⊢
  simpa [smul_eq_mul] using this

