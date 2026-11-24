-- Prove2me | solution 1 for GlobalTheory.ProjSpace.Model.isIso_str_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:05:17.85263+00:00
-- url     : https://prove2.me/submissions/8f47a8a2-aa33-4135-9631-ef36d3cd9593

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_TwistingSheafOneChartEqPreimageStandardChart
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsFormOfEqRatioPowMul
import Theorems.Thm_P2M_GlobalTheory_ProjSpace_chart__str_475cb27b7b18


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi (LB res pullU)
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap PSpace resG lbPow LBIso)
open GlobalTheory.ProjFrac
attribute [local instance] MvPolynomial.gradedAlgebra
open GlobalTheory GlobalTheory.ProjSpace GlobalTheory.ProjSpace.Model
variable {R : Type} [CommRing R] {N : ℕ}
namespace GlobalTheory.ProjSpace.Model
theorem _root_.solution : IsIso (PSpace.str R 0) := by
  haveI : IsIso (chartι R 0 0) := by
    refine isIso_of_isOpenImmersion_of_opensRange_eq_top _ ?_
    rw [opensRange_chartι, ← iSup_chart R 0]
    exact (iSup_unique (ι := Fin 1) (f := chart R 0)).symm
  haveI : IsEmpty {j : Fin (0 + 1) // j ≠ 0} := ⟨fun j => j.2 (Subsingleton.elim (α := Fin 1) _ _)⟩
  haveI : IsIso (chartι R 0 0 ≫ PSpace.str R 0) := by
    rw [chartι_str]
    exact inferInstanceAs (IsIso (Spec.map
      (isEmptyRingEquiv R {j : Fin (0 + 1) // j ≠ 0}).toCommRingCatIso.inv))
  exact IsIso.of_isIso_comp_left (chartι R 0 0) _
end GlobalTheory.ProjSpace.Model
