-- Prove2me | solution 1 for GlobalTheory.EffCartierData.keepsRegular_of_notMem_support
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:34:02.188298+00:00
-- url     : https://prove2.me/submissions/df1130cd-eb4e-4d25-bbb9-bf1f983e0efc

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_DivSheaf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsRegularFnIffOfIsAffineOpen
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_CoeNonzeroLocusCanonicalEqComplRange
import Theorems.Thm_GlobalTheory_EffCartierData_keepsRegular_iff_isRegularSec
import Theorems.Thm_GlobalTheory_Cartier_isRegularSec_of_ne_zero
import Theorems.Thm_GlobalTheory_Cartier_mem_nonzeroLocus_iff
import Theorems.Thm_GlobalTheory_Cartier_nonzeroLocus_secPull


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open Cartier
open GlobalTheory.EffCartierData
variable {X Y Z : Scheme.{0}}
variable (D D' : EffCartierData X)
namespace GlobalTheory.EffCartierData
theorem _root_.solution [IsIntegral Y] (φ : Y ⟶ X) {y : Y}
    (hy : φ y ∉ D.idealSheaf.support) : D.KeepsRegular φ := by
  obtain ⟨i, hi⟩ := D.exists_mem (φ y)
  refine (D.keepsRegular_iff_isRegularSec φ).2
    (isRegularSec_of_ne_zero _ (i := fun _ => i) fun h0 => ?_)
  have h1 : φ y ∈ Out.nonzeroLocus D.canonical := D.coe_nonzeroLocus_canonical.ge hy
  have h2 : y ∈ Out.nonzeroLocus (secPull D.canonical φ) :=
    (nonzeroLocus_secPull D.canonical φ).ge h1
  have h3 := (mem_nonzeroLocus_iff (secPull D.canonical φ) (fun _ => i)
    ((pull_U D.lb φ fun _ => i).ge hi)).1 h2
  rw [h0, Scheme.basicOpen_zero] at h3
  exact h3
end GlobalTheory.EffCartierData
