-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.PB.Realis.eval_PBsDe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:39:55.194449+00:00
-- url     : https://prove2.me/submissions/440e81bd-b32d-42e9-a568-16ce3c2573ba

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRes
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterNamed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_KleimanNefness_TargetSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_KleimanNefness_KleimanSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_ExistsUniqueStatement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_GenericComplexPoint
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_DivisibilityTowers_Birational
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MetricPeriods_IsTwiceDifferentiableAt
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MetricPeriods_MetricsProjectionFormulaNef
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_PB_AnSys_nComp_pos
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_PB_Realis_nComp_pos
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_PB_eval_scaleS
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_PB_Realis_scaleS_PBs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Filter Topology
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {D N : ℕ} {Ψ : Type} [Fintype Ψ] {S : AnSys D (Option (Ψ × Fin N))} {P : Ideal (MRing ι)}
  (Re : Realis S P) (II : IntersectionSystem)
namespace GlobalTheory.CompanionTheory.Ar.PB
namespace Realis
theorem _root_.solution (k : ℕ) (lam : Ψ × Fin N → ℝ) (s : ℝ) :
    eval (fun o => o.elim s lam) (Re.PBsDe II k) = eval (fun o => o.elim (s / k) lam) (Re.PBs II) / S.nComp := by
  have h : (S.nComp : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Re.nComp_pos.ne'
  rw [← eval_scaleS, Realis.scaleS_PBs, smul_eval, mul_div_cancel_left₀ _ h]
end Realis
end GlobalTheory.CompanionTheory.Ar.PB
