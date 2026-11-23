-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEis.UnitaryConv.cos_eq_of_rep
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:25:25.162684+00:00
-- url     : https://prove2.me/submissions/9bbf00bb-6ec8-4303-9fc9-3d0981d7eaa9

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_ConvGrOf
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnipotentConvergenceOfParabolic
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEis_UnitaryConv_cos_mk_eq_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgEis GlobalTheory.CompanionTheory.RgEis.UnitaryConv
open PositivityTheory.RgEis
variable {G : Type} [Group G]
namespace GlobalTheory.CompanionTheory.RgEis.UnitaryConv
theorem _root_.solution {P Γ : Subgroup G} {q q' : Cos P Γ} (h : rep q' * (rep q)⁻¹ ∈ P) : q = q' := by
  have h' := (cos_mk_eq_iff (P := P) (Γ := Γ) (Quotient.out q) (Quotient.out q')).mpr h
  rw [Quotient.out_eq, Quotient.out_eq] at h'
  exact h'
end GlobalTheory.CompanionTheory.RgEis.UnitaryConv
