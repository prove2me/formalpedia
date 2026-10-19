-- Prove2me | solution 2 for OAI.Problem356.GoodTypePermutation.certificate_of_good
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T22:43:38.407998+00:00
-- url     : https://prove2.me/submissions/c90fef94-7ede-46d7-9c05-e8d0113ba560

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CoulombTransport/GoodTypePermutation.lean:L46-L66
-- (upload_full_project.md Phase 4): solution for node OAI.Problem356.GoodTypePermutation.certificate_of_good. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
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
import Definitions.Def_OAI_Analysis_CoulombTransport_LocalCertificate
import Definitions.Def_OAI_Analysis_CoulombTransport_StationaryMap
import Definitions.Def_OAI_Analysis_CoulombTransport_LocalBranchMeasure
import Definitions.Def_OAI_Analysis_CoulombTransport_SmoothPushforward
import Definitions.Def_OAI_Analysis_CoulombTransport_GluedCertificate
import Definitions.Def_OAI_Analysis_CoulombTransport_GoodTypePermutation

-- ---- from OAI.Analysis.CoulombTransport.TriplePermutation ----
namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Problem356.TriplePermutation

private lemma pair_symm (x y : E3) : invDistance x y = invDistance y x := by
  simp only [invDistance, norm_sub_rev]

lemma cost_swap_first (x y z : E3) :
    coulombCost (x, (y, z)) = coulombCost (y, (x, z)) := by
  simp only [coulombCost, tripleFst, tripleSnd, tripleThd]
  rw [pair_symm y x]
  ac_rfl

lemma cost_swap_last (x y z : E3) :
    coulombCost (x, (y, z)) = coulombCost (x, (z, y)) := by
  simp only [coulombCost, tripleFst, tripleSnd, tripleThd]
  rw [pair_symm z y]
  ac_rfl

end Problem356.TriplePermutation

end

end OAI

-- ---- from OAI.Analysis.CoulombTransport.GoodTypePermutation ----
namespace OAI

noncomputable section
open scoped ENNReal

namespace Problem356.GoodTypePermutation

variable {U : Fin 5 → Set E3} {v : Fin 5 → E3 → ℝ}
  {Contact : Triple → Prop}

/-- Contact localization is transported along a swap of the first two entries. -/
theorem LocalTypeCertificate.swap_first {i j k : Fin 5}
    (h : LocalTypeCertificate U v Contact i j k)
    (hperm : ∀ {x y z a b c : E3}, List.Perm [x, y, z] [a, b, c] →
      Contact (x, (y, z)) → Contact (a, (b, c))) :
    LocalTypeCertificate U v Contact j i k := by
  intro x hx y hy z hz
  have hc := h y hy x hx z hz
  rw [add_comm (v i y) (v j x), TriplePermutation.cost_swap_first y x z] at hc
  exact ⟨hc.1, fun heq => hperm (List.Perm.swap x y [z]) (hc.2 heq)⟩

/-- Contact localization is transported along a swap of the last two entries. -/
theorem LocalTypeCertificate.swap_last {i j k : Fin 5}
    (h : LocalTypeCertificate U v Contact i j k)
    (hperm : ∀ {x y z a b c : E3}, List.Perm [x, y, z] [a, b, c] →
      Contact (x, (y, z)) → Contact (a, (b, c))) :
    LocalTypeCertificate U v Contact i k j := by
  intro x hx y hy z hz
  have hc := h x hx z hz y hy
  have hsum : v i x + v j z + v k y = v i x + v k y + v j z := by ac_rfl
  rw [hsum, TriplePermutation.cost_swap_last x z y] at hc
  exact ⟨hc.1, fun heq => hperm ((List.Perm.swap y z []).cons x) (hc.2 heq)⟩

/-- The two canonical component orders supply every good component type.
No converse from the abstract contact predicate to equality is assumed. -/
theorem certificate_of_good
    (hperm : ∀ {x y z a b c : E3}, List.Perm [x, y, z] [a, b, c] →
      Contact (x, (y, z)) → Contact (a, (b, c)))
    (h012 : LocalTypeCertificate U v Contact 0 1 2)
    (h034 : LocalTypeCertificate U v Contact 0 3 4)
    (i j k : Fin 5) (hgood : CenterCertificate.Good i j k) :
    LocalTypeCertificate U v Contact i j k := by
  have h102 := h012.swap_first hperm
  have h021 := h012.swap_last hperm
  have h120 := h102.swap_last hperm
  have h201 := h021.swap_first hperm
  have h210 := h201.swap_last hperm
  have h304 := h034.swap_first hperm
  have h043 := h034.swap_last hperm
  have h340 := h304.swap_last hperm
  have h403 := h043.swap_first hperm
  have h430 := h403.swap_last hperm
  fin_cases i <;> fin_cases j <;> fin_cases k
  all_goals first | assumption | (exfalso; revert hgood; unfold CenterCertificate.Good; decide)

end Problem356.GoodTypePermutation

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem356 OAI.Problem356.GoodTypePermutation
open scoped ENNReal


theorem solution : type_of% @_root_.OAI.Problem356.GoodTypePermutation.certificate_of_good := @_root_.OAI.Problem356.GoodTypePermutation.certificate_of_good
