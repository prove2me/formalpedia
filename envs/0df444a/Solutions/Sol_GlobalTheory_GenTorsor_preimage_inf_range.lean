-- Prove2me | solution 1 for GlobalTheory.GenTorsor.preimage_inf_range
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:57:22.6098+00:00
-- url     : https://prove2.me/submissions/15652664-ee0c-43f6-96ca-88312e6e2ab1

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
theorem _root_.solution (i : J) (V : X.Opens) :
    a i ⁻¹ᵁ V = a i ⁻¹ᵁ (V ⊓ (a i).opensRange) := by
  ext y
  exact ⟨fun h => ⟨h, y, rfl⟩, fun h => h.1⟩
end GlobalTheory.GenTorsor
