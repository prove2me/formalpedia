-- Prove2me | solution 1 for GlobalTheory.KS.Square.exists_glue
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:10:56.986973+00:00
-- url     : https://prove2.me/submissions/68db9598-3cec-47cc-b565-4d9bb4d9b634

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsCobOfIsAffineOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_KunnethSymmProductAffineCoversStatement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsIsSymmOfSquare
import Theorems.Thm_GlobalTheory_KS_Square_rsT_eq
import Theorems.Thm_GlobalTheory_KS_Square_rsT_rsT
import Theorems.Thm_GlobalTheory_KS_Square_iSup_inf_eq

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
theorem _root_.solution (hV : ⨆ α, V α = ⊤) (W : Z.Opens) (F : J → ∀ O : Z.Opens, Γ(Z, O))
    (h₁ : ∀ α O, O ≤ W ⊓ V α → rsT (F α (W ⊓ V α)) O = F α O)
    (h₂ : ∀ α β O, O ≤ W ⊓ V α ⊓ V β → F α O = F β O) :
    ∃ s : Γ(Z, W), ∀ α O, O ≤ W ⊓ V α → rsT s O = F α O := by
  obtain ⟨s, hs, -⟩ := TopCat.Sheaf.existsUnique_gluing' (F := Z.sheaf) (U := fun α => W ⊓ V α) (V := W)
    (iUV := fun α => homOfLE inf_le_left) (iSup_inf_eq hV W).ge (fun α => F α (W ⊓ V α)) (by
      intro α β
      have e1 := h₁ α ((W ⊓ V α) ⊓ (W ⊓ V β)) inf_le_left
      have e2 := h₁ β ((W ⊓ V α) ⊓ (W ⊓ V β)) inf_le_right
      have e3 := h₂ α β ((W ⊓ V α) ⊓ (W ⊓ V β)) (le_inf inf_le_left (inf_le_right.trans inf_le_right))
      rw [rsT_eq inf_le_left] at e1
      rw [rsT_eq inf_le_right] at e2
      exact e1.trans (e3.trans e2.symm))
  refine ⟨s, fun α O hO => ?_⟩
  have hsα : resG Z (inf_le_left : W ⊓ V α ≤ W) s = F α (W ⊓ V α) := hs α
  rw [← rsT_rsT hO inf_le_left s, rsT_eq (inf_le_left : W ⊓ V α ≤ W) s, hsα]
  exact h₁ α O hO
end GlobalTheory.KS.Square
