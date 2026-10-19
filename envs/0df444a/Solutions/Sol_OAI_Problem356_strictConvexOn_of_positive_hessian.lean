-- Prove2me | solution 1 for OAI.Problem356.strictConvexOn_of_positive_hessian
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T21:25:37.019904+00:00
-- url     : https://prove2.me/submissions/1ec730b0-cd91-4018-a045-bef4f5bd15eb

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
open Set in
theorem ap_scl {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {s : Set E} {f : E → ℝ}
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
    AffineMap.lineMap_apply_module] at this
  rw [ea] at this ⊢
  simpa [smul_eq_mul] using this

theorem solution {s : Set E} {f : E → ℝ}
    {f' : E → E →L[ℝ] ℝ} {f'' : E → E →L[ℝ] E →L[ℝ] ℝ}
    (hs : Convex ℝ s) (hsopen : IsOpen s)
    (hf : ∀ z ∈ s, HasFDerivAt f (f' z) z)
    (hf' : ∀ z ∈ s, HasFDerivAt f' (f'' z) z)
    (hpos : ∀ z ∈ s, ∀ v : E, v ≠ 0 → 0 < f'' z v v) :
    StrictConvexOn ℝ s f := by
  have hfc : ContinuousOn f s := fun z hz => (hf z hz).continuousAt.continuousWithinAt
  refine ap_scl hs hfc fun x hx y hy hxy t ht => ?_
  set L : ℝ → E := ⇑(AffineMap.lineMap x y : ℝ →ᵃ[ℝ] E) with hL
  have hLd : ∀ τ, HasDerivAt L (y - x) τ := fun τ => AffineMap.hasDerivAt_lineMap
  have hLc : Continuous L := AffineMap.lineMap_continuous (R := ℝ)
  have hLt : L t ∈ s := hs.lineMap_mem hx hy ⟨ht.1.le, ht.2.le⟩
  have hU : IsOpen (L ⁻¹' s) := hsopen.preimage hLc
  have hev : deriv (f ∘ L) =ᶠ[𝓝 t] fun τ => f' (L τ) (y - x) := by
    filter_upwards [hU.mem_nhds hLt] with τ hτ
    exact ((hf (L τ) hτ).comp_hasDerivAt τ (hLd τ)).deriv
  rw [hev.deriv_eq]
  have hk : HasDerivAt (fun τ => f' (L τ) (y - x)) (f'' (L t) (y - x) (y - x)) t := by
    have := ((hf' (L t) hLt).comp_hasDerivAt t (hLd t)).clm_apply (hasDerivAt_const t (y - x))
    simpa using this
  rw [hk.deriv]
  exact hpos _ hLt _ (sub_ne_zero.mpr (Ne.symm hxy))

