-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume.baseFr_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:40:07.665454+00:00
-- url     : https://prove2.me/submissions/466998f8-35ab-4036-8fa0-f52c6c516f73

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_NormsFree
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_UnitaryHaarVolume

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
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume
open Formalism.L2.Pj Formalism.L2.PjFree NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD MeasureTheory
open scoped ENNReal
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
set_option autoImplicit false
open NumberField MeasureTheory
open scoped ENNReal
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r)
namespace GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume
namespace _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume
theorem _root_.solution :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume.baseFr X ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume.OrthFr X := by
  intro τ
  exact (X.signature τ).choose_spec.2
end _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume
end GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume
