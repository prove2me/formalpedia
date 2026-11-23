-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Desc.Window.trace_ne_zero_of_idem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:10:58.324963+00:00
-- url     : https://prove2.me/submissions/d3c2c2cf-0bca-4071-b973-9b7f7baaadd8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DltEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_DiscrMulMemOfIsIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AlternatingDifferenceTermWindow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology Classical
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc GlobalTheory.UnitLemma.Desc.Window
variable {K : UQ} (B : InvAlg K) {ι : Type}
namespace GlobalTheory.UnitLemma.Desc.Window
theorem _root_.solution {f : B.A} (hf : IsIdempotentElem f) (h0 : f ≠ 0) :
    Algebra.trace K.E B.A f ≠ 0 := by
  set g := Algebra.lmul K.E B.A f
  have hproj : LinearMap.IsProj (LinearMap.range g) g := by
    refine ⟨fun x => LinearMap.mem_range_self g x, ?_⟩
    rintro _ ⟨z, rfl⟩
    change f * (f * z) = f * z
    rw [← mul_assoc, hf.eq]
  rw [Algebra.trace_apply, hproj.trace]
  have hmem : f ∈ LinearMap.range g := ⟨1, by change f * 1 = f; rw [mul_one]⟩
  have hpos : LinearMap.range g ≠ ⊥ := by
    intro hb; rw [hb, Submodule.mem_bot] at hmem; exact h0 hmem
  rw [Ne, Nat.cast_eq_zero, Submodule.finrank_eq_zero]
  exact hpos
end GlobalTheory.UnitLemma.Desc.Window
