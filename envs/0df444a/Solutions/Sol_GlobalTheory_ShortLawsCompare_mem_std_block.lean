-- Prove2me | solution 1 for GlobalTheory.ShortLawsCompare.mem_std_block
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:33:07.23475+00:00
-- url     : https://prove2.me/submissions/f44296c8-1753-4207-9957-97d04049b8f3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_BlockPolyLevelMove
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_BlockProductLattices
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsIndexIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_BetaIsPrincipal
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_ZeroNotAdmissibleOfRankPos
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_BaseClassMove
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_BlockHarmLevOfBlockHarm
import Theorems.Thm_GlobalTheory_BetaEx_mem_std


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ShortLawsCompare
open NumberField MvPolynomial Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory.IndefiniteRowSideFullHecke
variable {E : Type} [Field E] [NumberField E]
variable {n₁ n₂ : ℕ}
set_option autoImplicit false
open NumberField MvPolynomial
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
variable {E : Type} [Field E] [NumberField E]
variable {n₁ n₂ : ℕ}
namespace GlobalTheory.ShortLawsCompare
namespace _root_.GlobalTheory.ShortLawsCompare
theorem _root_.solution (v : Fin (n₁ + n₂) → E) :
    v ∈ _root_.Formalism.L2.Pj.stdLat E (n₁ + n₂) ↔
      (fun j => v (Fin.castAdd n₂ j)) ∈ _root_.Formalism.L2.Pj.stdLat E n₁ ∧
        (fun j => v (Fin.natAdd n₁ j)) ∈ _root_.Formalism.L2.Pj.stdLat E n₂ := by
  simp only [_root_.GlobalTheory.BetaEx.mem_std]
  constructor
  · intro h
    exact ⟨fun j => h _, fun j => h _⟩
  · rintro ⟨h₁, h₂⟩ j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · exact h₁ i
    · exact h₂ i
end _root_.GlobalTheory.ShortLawsCompare
end GlobalTheory.ShortLawsCompare
