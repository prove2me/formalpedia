-- Prove2me | solution 1 for OAI.Problem356.GoodTypePermutation.certificate_of_good
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T22:16:07.735827+00:00
-- url     : https://prove2.me/submissions/df374540-ae0f-467f-8f9d-327770b05cb7

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

open OAI OAI.Problem356 OAI.Problem356.GoodTypePermutation
open scoped ENNReal
variable {U : Fin 5 → Set E3} {v : Fin 5 → E3 → ℝ}
  {Contact : Triple → Prop}
theorem h41_cost12 (x y z : E3) : coulombCost (x, (y, z)) = coulombCost (y, (x, z)) := by
  simp only [coulombCost, tripleFst, tripleSnd, tripleThd, invDistance, norm_sub_rev x y]
  ring

theorem h41_cost23 (x y z : E3) : coulombCost (x, (y, z)) = coulombCost (x, (z, y)) := by
  simp only [coulombCost, tripleFst, tripleSnd, tripleThd, invDistance, norm_sub_rev y z]
  ring

theorem solution
    (hperm : ∀ {x y z a b c : E3}, List.Perm [x, y, z] [a, b, c] →
      Contact (x, (y, z)) → Contact (a, (b, c)))
    (h012 : LocalTypeCertificate U v Contact 0 1 2)
    (h034 : LocalTypeCertificate U v Contact 0 3 4)
    (i j k : Fin 5) (hgood : CenterCertificate.Good i j k) :
    LocalTypeCertificate U v Contact i j k := by
  have s12 : ∀ {a b c : Fin 5}, LocalTypeCertificate U v Contact a b c →
      LocalTypeCertificate U v Contact b a c := by
    intro a b c h x hx y hy z hz
    obtain ⟨h1, h2⟩ := h y hy x hx z hz
    rw [← h41_cost12, show v a y + v b x + v c z = v b x + v a y + v c z by ring] at h1 h2
    exact ⟨h1, fun he => hperm (List.Perm.swap x y [z]) (h2 he)⟩
  have s23 : ∀ {a b c : Fin 5}, LocalTypeCertificate U v Contact a b c →
      LocalTypeCertificate U v Contact a c b := by
    intro a b c h x hx y hy z hz
    obtain ⟨h1, h2⟩ := h x hx z hz y hy
    rw [← h41_cost23, show v a x + v b z + v c y = v a x + v c y + v b z by ring] at h1 h2
    exact ⟨h1, fun he => hperm (List.Perm.cons x (List.Perm.swap y z [])) (h2 he)⟩
  have key : ∀ i j k : Fin 5, CenterCertificate.Good i j k →
      (i = 0 ∧ j = 1 ∧ k = 2) ∨ (i = 1 ∧ j = 0 ∧ k = 2) ∨ (i = 0 ∧ j = 2 ∧ k = 1) ∨
      (i = 2 ∧ j = 0 ∧ k = 1) ∨ (i = 1 ∧ j = 2 ∧ k = 0) ∨ (i = 2 ∧ j = 1 ∧ k = 0) ∨
      (i = 0 ∧ j = 3 ∧ k = 4) ∨ (i = 3 ∧ j = 0 ∧ k = 4) ∨ (i = 0 ∧ j = 4 ∧ k = 3) ∨
      (i = 4 ∧ j = 0 ∧ k = 3) ∨ (i = 3 ∧ j = 4 ∧ k = 0) ∨ (i = 4 ∧ j = 3 ∧ k = 0) := by
    unfold CenterCertificate.Good
    decide
  rcases key i j k hgood with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · exact h012
  · exact s12 h012
  · exact s23 h012
  · exact s12 (s23 h012)
  · exact s23 (s12 h012)
  · exact s12 (s23 (s12 h012))
  · exact h034
  · exact s12 h034
  · exact s23 h034
  · exact s12 (s23 h034)
  · exact s23 (s12 h034)
  · exact s12 (s23 (s12 h034))

