-- Prove2me | solution 1 for GlobalTheory.SmGL.MultiIrr.exists_parab_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:40:24.940042+00:00
-- url     : https://prove2.me/submissions/f6a67723-823b-40e2-a773-d158711a26ce

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_BernsteinUnitaryProductIrreducible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsLocallyConstantModulus
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LowerEquivUpperSwap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsIrreducibleIffOfLinearEquiv
import Theorems.Thm_GlobalTheory_SmGL_UnitInd_exists_iwasawa
import Theorems.Thm_GlobalTheory_SmGL_unipRad_le_parab


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel Matrix
open scoped TensorProduct
open GlobalTheory GlobalTheory.SmGL GlobalTheory.SmGL.MultiIrr
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {a b n a' b' n' : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype n] [DecidableEq n]
  [Fintype a'] [DecidableEq a'] [Fintype b'] [DecidableEq b'] [Fintype n'] [DecidableEq n']
  {V W U : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [AddCommGroup U] [Module ℂ U]
namespace GlobalTheory.SmGL.MultiIrr
theorem _root_.solution {α : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ i, Fintype (m i)]
    [∀ i, DecidableEq (m i)] (e : (Σ i, m i) ≃ n) (x : GL n k) :
    ∃ p : parab k e, ∃ w ∈ (KO k n : Set (GL n k)), x = p * w := by
  obtain ⟨u, g, w, hw, rfl⟩ := UnitInd.exists_iwasawa e x
  exact ⟨⟨u * leviEmb k e g, mul_mem (unipRad_le_parab k _ u.2) (leviEmb_mem_parab k _ g)⟩, w, hw, rfl⟩
end GlobalTheory.SmGL.MultiIrr
