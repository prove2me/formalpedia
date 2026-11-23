-- Prove2me | solution 1 for GlobalTheory.GenTorsor.pb_congr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:56:47.49129+00:00
-- url     : https://prove2.me/submissions/d654002d-0447-47fb-a27d-854ca41ac60c

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
namespace GlobalTheory.GenTorsor
theorem _root_.solution {a b : Y ⟶ X} (e : a = b) {U : X.Opens} {W : Y.Opens} (h : W ≤ a ⁻¹ᵁ U)
    (h' : W ≤ b ⁻¹ᵁ U) (x : Γ(X, U)ˣ) : pb a U W h x = pb b U W h' x := by
  subst e; rfl
end GlobalTheory.GenTorsor
