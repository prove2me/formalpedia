-- Prove2me | solution 1 for GlobalTheory.GenTorsor.pb_pb
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:56:28.399147+00:00
-- url     : https://prove2.me/submissions/5f49b4e4-5ddc-4e6b-be7a-0054e56b5a75

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
theorem _root_.solution (b : Z ⟶ Y) (a : Y ⟶ X) {U : X.Opens} {V : Y.Opens} {W : Z.Opens}
    (h : V ≤ a ⁻¹ᵁ U) (h' : W ≤ b ⁻¹ᵁ V) (x : Γ(X, U)ˣ) :
    pb b V W h' (pb a U V h x) = pb (b ≫ a) U W (h'.trans (b.preimage_mono h)) x := by
  ext
  change ((a.appLE U V h ≫ b.appLE V W h').hom) (x : Γ(X, U)) = _
  rw [Scheme.Hom.appLE_comp_appLE]
  rfl
end GlobalTheory.GenTorsor
