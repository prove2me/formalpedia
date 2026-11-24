-- Prove2me | solution 1 for GlobalTheory.SymCompare.td_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:20:10.133535+00:00
-- url     : https://prove2.me/submissions/a64ed58d-b71e-4485-9878-0fbb1d395308

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_OnesRepresent
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_SiegelEisenstein_SymmetricPatternGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsReindexIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
noncomputable section
open GlobalTheory GlobalTheory.SymCompare
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n m n' m' : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
  [Fintype n'] [DecidableEq n'] [Fintype m'] [DecidableEq m'] {c : ℕ}
namespace GlobalTheory.SymCompare
theorem _root_.solution {P Q : TypeDatum k n} (hJ : ∀ g, g ∈ P.J ↔ g ∈ Q.J)
    (hl : ∀ g (h : g ∈ P.J) (h' : g ∈ Q.J), P.lam ⟨g, h⟩ = Q.lam ⟨g, h'⟩) : P = Q := by
  obtain ⟨⟨J, l⟩, _, _, _⟩ := P
  obtain ⟨⟨J', l'⟩, _, _, _⟩ := Q
  obtain rfl : J = J' := Subgroup.ext hJ
  obtain rfl : l = l' := MonoidHom.ext fun g => hl g.1 g.2 g.2
  rfl
end GlobalTheory.SymCompare
