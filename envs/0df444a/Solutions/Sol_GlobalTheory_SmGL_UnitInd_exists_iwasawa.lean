-- Prove2me | solution 1 for GlobalTheory.SmGL.UnitInd.exists_iwasawa
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:33:49.774465+00:00
-- url     : https://prove2.me/submissions/2d67e796-5b95-46d3-bc97-39273d965b5d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_BlockTriangularOneAddMat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwasawaBlockTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsLocallyConstantModulus
import Theorems.Thm_GlobalTheory_SmGL_exists_levi_mul_unip
import Theorems.Thm_GlobalTheory_SplitWeil_iwasawa_blockTriangular


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel MeasureTheory Matrix
open scoped TensorProduct ENNReal
open GlobalTheory GlobalTheory.SmGL GlobalTheory.SmGL.UnitInd
open GlobalTheory.SplitFlip GlobalTheory.SmGL.UnipHaar
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n)
namespace GlobalTheory.SmGL.UnitInd
theorem _root_.solution (x : GL n k) :
    ∃ (u : unipRad k e) (g : Levi k m), ∃ w ∈ KO k n, x = u * leviEmb k e g * w := by
  let r := (monoEquivOfFin α rfl).symm
  obtain ⟨b, hb, w, hw, rfl⟩ := iwasawa_blockTriangular k n (fun i => r (blk e i)) x
  have hp : b ∈ parab k e := fun i j h => hb (r.strictMono h)
  obtain ⟨u, hu, h⟩ := exists_levi_mul_unip k e ⟨b, hp⟩
  refine ⟨conj e (leviProj k e ⟨b, hp⟩) ⟨u, hu⟩, leviProj k e ⟨b, hp⟩, w, hw, ?_⟩
  simp only [conj, inv_mul_cancel_right]
  rw [← h]
end GlobalTheory.SmGL.UnitInd
