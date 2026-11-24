-- Prove2me | solution 1 for GlobalTheory.FunObj.measurePreserving_elim
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:52:46.502868+00:00
-- url     : https://prove2.me/submissions/f6ea570a-3be0-48d5-898f-a102a1790398

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FlatTensorVacuum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MeasurePreservingPiProdSplit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal
noncomputable section
open GlobalTheory GlobalTheory.FunObj
open GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx
variable {ι : Type*} [Fintype ι] {α β γ : ι → Type*} [∀ i, MeasurableSpace (α i)] [∀ i, MeasurableSpace (β i)]
  [∀ i, MeasurableSpace (γ i)]
namespace GlobalTheory.FunObj
theorem _root_.solution {A B C k : Type*} [Fintype A] [Fintype B] [Fintype C] [MeasurableSpace k]
    (ν : Measure k) [SigmaFinite ν] (e : A ⊕ B ≃ C) :
    MeasurePreserving (fun (p : (A → k) × (B → k)) c => Sum.elim p.1 p.2 (e.symm c))
      ((Measure.pi fun _ => ν).prod (Measure.pi fun _ => ν)) (Measure.pi fun _ => ν) := by
  have h := (measurePreserving_piCongrLeft (fun _ : C => ν) e).comp
    (measurePreserving_sumPiEquivProdPi_symm (fun _ : A ⊕ B => ν))
  convert h using 1
  funext p c
  obtain ⟨a | b, rfl⟩ := e.surjective c <;>
    simp [MeasurableEquiv.coe_piCongrLeft, MeasurableEquiv.coe_sumPiEquivProdPi_symm]
end GlobalTheory.FunObj
