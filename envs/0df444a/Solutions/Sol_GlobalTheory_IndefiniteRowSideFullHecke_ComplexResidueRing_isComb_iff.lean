-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.ComplexResidueRing.isComb_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:51:39.898945+00:00
-- url     : https://prove2.me/submissions/eeddcddf-25a0-441f-966a-82b418f44aae

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CuspFree
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_ComplexResidueRing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.ComplexResidueRing
open Formalism.L2.Pj Formalism.L2.PjFree NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {c c' : Coeff l}
variable {Xo : Moduli Dw l}
variable {r : ℕ}
set_option synthInstance.maxHeartbeats 200000
namespace GlobalTheory.IndefiniteRowSideFullHecke.ComplexResidueRing
theorem _root_.solution (h : c.F ≤ c'.F) {m : ℕ} (b : Fin m → c'.F) (f : Fin m → Rul Xo c) (f' : Rul Xo c') :
    IsComb h b f f' ↔ f' = ∑ i, b i • ruleUp h (f i) := by
  have key : ∀ (p : TRing c'.F) (y : FrPt Xo c' p.R), (∑ i, b i • ruleUp h (f i)) p y =
      ∑ i, algebraMap c'.F p.R (b i) * unRes (evR Xo c (f i) (ptDown h y)) := by
    intro p y
    rw [Finset.sum_apply, Finset.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Pi.smul_apply, Pi.smul_apply, Algebra.smul_def]
    rfl
  constructor
  · intro hf
    funext p y
    rw [key, hf p y]
  · intro hf p y
    rw [hf, key]
end GlobalTheory.IndefiniteRowSideFullHecke.ComplexResidueRing
