-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.Isometric.of_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:51:26.085326+00:00
-- url     : https://prove2.me/submissions/757d26d8-c469-4f4d-a83f-0775c6bdfa83

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_ExistsOrthonormalOfUnimodular
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_SelfReciprocalLocalField
import Theorems.Thm_GlobalTheory_LocalQuad_HermClass_Congr_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Polynomial
open scoped TensorProduct
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField
variable (E : Type) [Field E] [NumberField E] [IsCMField E]
variable {E}
variable {r : ℕ} (P : SelfRecip E r)
variable (k : Type) [CommRing k] [Algebra (maximalRealSubfield E) k]
namespace GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField
namespace Isometric
theorem _root_.solution {G : Matrix (Fin r) (Fin r) E}
    {x n : (k ⊗[maximalRealSubfield E] plus P)ˣ} (hn : n ∈ norms P k)
    (h : Isometric P k G x) : Isometric P k G (x * n : (k ⊗[maximalRealSubfield E] plus P)ˣ) := by
  obtain ⟨c, hc⟩ := hn
  have hc' : (c : k ⊗[maximalRealSubfield E] Fld P) * involBase P k c = inclPlus P k n :=
    congrArg Units.val hc
  obtain ⟨φ, h1, h2⟩ := h
  refine ⟨(AddAut.mulLeft c).trans φ, fun e y => ?_, fun y y' => ?_⟩
  · change φ (c * (inclBase P k e * y)) = e • φ (c * y)
    rw [← h1, mul_left_comm]
  · change gramForm k G (φ (c * y)) (φ (c * y')) = _
    rw [h2, traceForm, traceForm, Units.val_mul, map_mul (inclPlus P k), map_mul (involBase P k), ← hc']
    congr 1
    ring
end Isometric
end GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField
