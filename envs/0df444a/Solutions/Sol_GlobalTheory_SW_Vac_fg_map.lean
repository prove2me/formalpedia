-- Prove2me | solution 1 for GlobalTheory.SW.Vac.fg_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:44:54.481024+00:00
-- url     : https://prove2.me/submissions/e20dc3c4-0239-4aa4-b407-c899e40f9af8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SchwartzBruhatInnerProductSelfNonnegBoundsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsExOfPow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.Vac
noncomputable section
variable {κ ι : Type} [Fintype κ] [Fintype ι]
namespace GlobalTheory.SW.Vac
theorem _root_.solution {G G' : Type} [AddCommGroup G] [AddCommGroup G'] {A : AddSubgroup G} (hA : A.FG)
    (f : G →+ G') : (A.map f).FG := by
  classical
  obtain ⟨S, rfl⟩ := hA
  exact ⟨S.image f, by rw [AddMonoidHom.map_closure, Finset.coe_image]⟩
end GlobalTheory.SW.Vac
