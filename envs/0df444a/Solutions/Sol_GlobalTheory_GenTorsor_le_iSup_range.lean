-- Prove2me | solution 1 for GlobalTheory.GenTorsor.le_iSup_range
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:56:48.517946+00:00
-- url     : https://prove2.me/submissions/c9d125f8-d725-4b2c-883f-d38382d860f1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_IsRepresentableOfCover

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.GenTorsor
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Semi
variable {X Y Z : Scheme.{0}}
variable {J : Type*} {T : J → Scheme.{0}} (a : ∀ i, T i ⟶ X) [∀ i, IsOpenImmersion (a i)]
namespace GlobalTheory.GenTorsor
theorem _root_.solution (hc : ∀ x : X, ∃ i y, a i y = x) (V : X.Opens) :
    V ≤ ⨆ i, V ⊓ (a i).opensRange := fun x hx => by
  obtain ⟨i, y, rfl⟩ := hc x
  exact Opens.mem_iSup.2 ⟨i, hx, y, rfl⟩
end GlobalTheory.GenTorsor
