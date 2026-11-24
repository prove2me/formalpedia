-- Prove2me | solution 1 for GlobalTheory.T.isUnimodular_blockUpperTriangular_symmetricLevels
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:36:05.455082+00:00
-- url     : https://prove2.me/submissions/e82b4227-ee02-4fb3-a9cc-63508c611699

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsUnimodularBlockUpperTriangularSymmetricLevels
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FourierJacobiAverage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsUnimodularBlockUpperTriangularSymmetricLevelsStatement
import Theorems.Thm_GlobalTheory_LevelUnimod_unimodular


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (c l : ℕ) (L : Fin c → ℕ) (_ : ∀ i, L (Fin.rev i) + L i = 2 * l) (S : Subgroup (GL (n ⊕ Fin c) k)) (_ : ∀ g : GL (n ⊕ Fin c) k, g ∈ S ↔ ∀ r s : n ⊕ Fin c, (r.isRight ∨ s.isRight) → Sum.elim (fun _ => l) L s ≤ Sum.elim (fun _ => l) L r → g.val r s = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r s) (m : Measure S), m.IsHaarMeasure → m.IsMulRightInvariant := by
  first | exact @GlobalTheory.LevelUnimod.unimodular | exact GlobalTheory.LevelUnimod.unimodular | (intros; apply GlobalTheory.LevelUnimod.unimodular <;> assumption)
end _root_.GlobalTheory.T
