-- Prove2me | solution 1 for GlobalTheory.LatClass.lat_bas
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:12:15.639868+00:00
-- url     : https://prove2.me/submissions/b93cbf70-85d4-4362-8432-8bd8f9e55ead

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_NormalRepresentationLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LatticeBounds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsValuationEqZpow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_MulMemOfHatCosetIndNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FlatNeZeroOfMemR
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_TwistSupportPeriodicLevels
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LatticeClasses
import Theorems.Thm_GlobalTheory_LatClass_latOf_mul_congr


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.NormalRepresentationLattice
open GlobalTheory GlobalTheory.LatClass
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable [MeasurableSpace k] [BorelSpace k]
variable {s : ℕ} {X : ℕ → Type} [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)] {Z : Type} [Fintype Z] [DecidableEq Z]
  {T : Chain k s X Z} {ϖ : kˣ} {ψ : AddChar k Circle} {ν : Measure k} [ν.IsAddHaarMeasure]
  (hϖ : valuation k (ϖ : k) = uniformizer k) (hψ : HasConductor ψ 1)
  (hb : ∀ j c h, latOf (T.bas j c h) = latOf 1)
  (hs : ∀ j c h x, T.Phi j c h x ≠ 0 → IntM x)
  (hp : ∀ j c h x y, MaxM y → T.Phi j c h (x + y) = T.Phi j c h x)
  (hJ : ∀ j c h, (T.lev j c h).J ≤ KO k (X j ⊕ Fin c))
omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
include hb
namespace GlobalTheory.LatClass
theorem _root_.solution {j c h} (g : GL (X j ⊕ Fin c) k) : latOf (g * T.bas j c h) = latOf g := by
  rw [latOf_mul_congr _ (hb j c h), mul_one]
end GlobalTheory.LatClass
