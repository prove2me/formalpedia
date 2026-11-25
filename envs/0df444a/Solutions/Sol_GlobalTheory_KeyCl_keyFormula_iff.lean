-- Prove2me | solution 1 for GlobalTheory.KeyCl.keyFormula_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:03:51.909395+00:00
-- url     : https://prove2.me/submissions/d5166afe-bf08-4637-afcb-95cd34d8d03d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_KeyRootOfKeyFormula

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.KeyCl
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace GlobalTheory.KeyCl
theorem _root_.solution :
    KeyFormula ↔ ∃ κ : Rule, Homog (fun _ => 1) κ ∧ Funct κ ∧ UnitSp κ ∧ ThetaOne κ ∧ ArchNorm (fun _ => 1) κ := by
  constructor
  · rintro ⟨κ, hH, hF, hU, hT, hA⟩
    refine ⟨κ, ?_, hF, hU, hT, ?_⟩
    · intro K _ _ P hg rig hr th hth v hv th' hth' v' hv' a M h₁ h₂
      simpa only [mul_one, Nat.mul_one] using hH K P hg rig hr th hth v hv th' hth' v' hv' a M h₁ h₂
    · intro x u Hm W χ θ Fd nth nη h₁ h₂ h₃ h₄ h₅ h₆ h₇
      simpa only [mul_one, Nat.mul_one] using hA x u Hm W χ θ Fd nth nη h₁ h₂ h₃ h₄ h₅ h₆ h₇
  · rintro ⟨κ, hH, hF, hU, hT, hA⟩
    refine ⟨κ, ?_, hF, hU, hT, ?_⟩
    · intro K _ _ P hg rig hr th hth v hv th' hth' v' hv' a M h₁ h₂
      simpa only [mul_one, Nat.mul_one] using hH K P hg rig hr th hth v hv th' hth' v' hv' a M h₁ h₂
    · intro x u Hm W χ θ Fd nth nη h₁ h₂ h₃ h₄ h₅ h₆ h₇
      simpa only [mul_one, Nat.mul_one] using hA x u Hm W χ θ Fd nth nη h₁ h₂ h₃ h₄ h₅ h₆ h₇
end GlobalTheory.KeyCl
