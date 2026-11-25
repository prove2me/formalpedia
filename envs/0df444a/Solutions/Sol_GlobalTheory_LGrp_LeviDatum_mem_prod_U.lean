-- Prove2me | solution 1 for GlobalTheory.LGrp.LeviDatum.mem_prod_U
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:00:57.4377+00:00
-- url     : https://prove2.me/submissions/d9d59953-b653-4c95-9177-32dd7c34eaa9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Formalism_SatakeDualWeyl_StatementF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_EqOfHasValueAtInfinite
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LineOppositeParabolicUnitaryLeviSectionEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
open scoped NNReal TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.LGrp
open GlobalTheory.PRep
open GlobalTheory.LGrp.LeviDatum
variable {G M : Type} [Group G] [TopologicalSpace G] [Group M] [TopologicalSpace M] (P : LeviDatum G M)
namespace GlobalTheory.LGrp.LeviDatum
theorem _root_.solution (H : Type) [Group H] [TopologicalSpace H] (g : G × H) : g ∈ (P.prod H).U ↔ g.1 ∈ P.U ∧ g.2 = 1 := by
  rw [mem_U, mem_U]
  exact ⟨fun ⟨h, e⟩ => ⟨⟨h, congrArg Prod.fst e⟩, congrArg Prod.snd e⟩, fun ⟨⟨h, e⟩, e'⟩ => ⟨h, Prod.ext e e'⟩⟩
end GlobalTheory.LGrp.LeviDatum
