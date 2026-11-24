-- Prove2me | solution 1 for GlobalTheory.RootEx.VolN.map_volN_of_affine
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:19:05.989959+00:00
-- url     : https://prove2.me/submissions/9fb11e4e-d4f7-4c9c-a4f0-88390e424c68

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSumRowCol
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SecondCountableAndT2LocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LinearChangeOfVariablesLocalFieldMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeUnipotentHaarAndModulus
import Theorems.Thm_GlobalTheory_RootEx_VolN_map_affine
import Theorems.Thm_GlobalTheory_RootEx_VolN_volN_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
noncomputable section
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.VolN
open GlobalTheory.RootEx.Model
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}
variable [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure]
namespace GlobalTheory.RootEx.VolN
theorem _root_.solution (p : ℕ) (T : N k n c p → N k n c p) (L : Matrix (Ix n c p) (Ix n c p) k)
    (hL : L.det = 1) (b : Ix n c p → k) (hT : ∀ e, T (mkNel p e) = mkNel p (L.mulVec e + b)) :
    (volN ν n c p).map T = volN ν n c p := by
  obtain ⟨h1, h2⟩ := map_affine ν L hL b
  have e1 : T ∘ coEquiv p = coEquiv p ∘ fun e => L.mulVec e + b := funext hT
  have e2 : T = coEquiv p ∘ (fun e => L.mulVec e + b) ∘ (coEquiv p).symm := by
    rw [← Function.comp_assoc, ← e1]; ext1 g; simp
  have hm : Measurable T := e2 ▸ (coEquiv p).measurable.comp (h1.comp (coEquiv p).symm.measurable)
  rw [volN_eq, Measure.map_map hm (coEquiv p).measurable, e1, ← Measure.map_map (coEquiv p).measurable h1, h2]
end GlobalTheory.RootEx.VolN
