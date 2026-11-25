-- Prove2me | solution 1 for GlobalTheory.ThetaClaimsCompare.gaps_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:00:55.497529+00:00
-- url     : https://prove2.me/submissions/d5558f32-807c-49b0-8894-4ad3059cd744

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThProps
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CuspFree
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_JetRangeLevelFactor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_MinorsDisjointColumnsHarmonic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLastEntryPosNotLastPos

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
open GlobalTheory GlobalTheory.ThetaClaimsCompare
open NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.PjFree GlobalTheory.IndefiniteRowSideFullHecke.JetRangeLevelFactor
variable {T : Type} [Fintype T] (r : T → ℕ) (n : ℕ) (k : Type) [Field k] (col : ∀ σ, Fin (r σ) → Fin n)
namespace GlobalTheory.ThetaClaimsCompare
theorem _root_.solution (b : ℕ → ℕ) (hb : Antitone b) (N i : ℕ) (hi : i ≤ N) :
    ∑ s ∈ Finset.range N, (if i ≤ s then b s - b (s + 1) else 0) = b i - b N := by
  induction N, hi using Nat.le_induction with
  | base =>
    rw [Nat.sub_self]
    exact Finset.sum_eq_zero fun s hs => if_neg (by simpa using hs)
  | succ N hN ih =>
    rw [Finset.sum_range_succ, ih, if_pos hN]
    have := hb hN
    have := hb (Nat.le_succ N)
    simp only [Nat.succ_eq_add_one] at this
    omega
end GlobalTheory.ThetaClaimsCompare
