-- Prove2me | solution 1 for GlobalTheory.KS.Square.exists_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:11:04.514185+00:00
-- url     : https://prove2.me/submissions/e0a28819-29a5-4d06-a5e4-af78f2549a45

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsCobOfIsAffineOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_KunnethSymmProductAffineCoversStatement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsIsSymmOfSquare
import Theorems.Thm_GlobalTheory_KS_Square_rsT_sub
import Theorems.Thm_GlobalTheory_KS_Square_rsT_rsT
import Theorems.Thm_GlobalTheory_KS_Square_iSup_inf_eq
import Theorems.Thm_GlobalTheory_KS_isCob_of_isAffineOpen


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
open GlobalTheory GlobalTheory.KS GlobalTheory.KS.Square
variable {Z : Scheme.{0}}
variable {J : Type} {V : J → Z.Opens}
namespace GlobalTheory.KS.Square
theorem _root_.solution (hV : ⨆ α, V α = ⊤) {W : Z.Opens} (hW : IsAffineOpen W)
    (k : C1 fun α => W ⊓ V α) (hk : IsCoc _ k) :
    ∃ c : ∀ α, Γ(Z, W ⊓ V α), ∀ α β O, O ≤ W ⊓ V α ⊓ V β →
      rsT (k α β) O = rsT (c β) O - rsT (c α) O := by
  have hW' : IsAffineOpen (⨆ α, W ⊓ V α) := by
    rw [iSup_inf_eq hV W]
    exact hW
  obtain ⟨b, hb⟩ := isCob_of_isAffineOpen Z J (fun α => W ⊓ V α) k hW' hk
  refine ⟨b, fun α β O hO => ?_⟩
  have hO' : O ≤ (W ⊓ V α) ⊓ (W ⊓ V β) :=
    le_inf (hO.trans inf_le_left) (le_inf (hO.trans (inf_le_left.trans inf_le_left)) (hO.trans inf_le_right))
  rw [hb α β, rsT_sub, rsT_rsT hO' inf_le_right, rsT_rsT hO' inf_le_left]
end GlobalTheory.KS.Square
