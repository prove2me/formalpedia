-- Prove2me | solution 1 for GlobalTheory.SmGL.MultiIrr.isIrreducible_multiProd_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:40:25.907805+00:00
-- url     : https://prove2.me/submissions/623d24f2-f119-4a7f-a13e-8169a53a22f2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_BernsteinUnitaryProductIrreducible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsLocallyConstantModulus
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LowerEquivUpperSwap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsIrreducibleIffOfLinearEquiv
import Theorems.Thm_GlobalTheory_SmGL_MultiIrr_isIrreducible_iff_of_linearEquiv
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_trans
import Theorems.Thm_GlobalTheory_SmGL_isIrreducible_ofChar


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
variable {s : ℕ} {m : Fin (s + 1) → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]
namespace GlobalTheory.SmGL.MultiIrr
theorem _root_.solution {m : Fin 0 → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]
    (e : (Σ i, m i) ≃ n) {X : Fin 0 → Type} [∀ i, AddCommGroup (X i)] [∀ i, Module ℂ (X i)]
    (σ : ∀ i, Representation ℂ (GL (m i) k) (X i)) : (multiProd e σ).IsIrreducible := by
  haveI : IsEmpty n := ⟨fun x => (e.symm x).1.elim0⟩
  haveI : Subsingleton (GL n k) := ⟨fun _ _ => Units.ext (Subsingleton.elim _ _)⟩
  let κ : IndSp e (piTensor σ) ≃ₗ[ℂ] ⨂[ℂ] i, X i := LinearEquiv.ofBijective (ev _ 1) ⟨fun f g h =>
    Subtype.ext (Subtype.ext (funext fun x => by rw [Subsingleton.elim x 1]; exact h)), fun v =>
    ⟨⟨⟨fun _ => v, fun p _ => by rw [Subsingleton.elim p 1, map_one]; rfl⟩,
      mem_smooth_of_eventually _ (.of_forall fun _ _ => rfl)⟩, rfl⟩⟩
  refine (isIrreducible_iff_of_linearEquiv (σ := ofChar (1 : GL n k →* ℂˣ)) id Function.surjective_id
    (κ.trans (PiTensorProduct.isEmptyEquiv _)) fun g v => ?_).2 (isIrreducible_ofChar _)
  rw [Subsingleton.elim g 1]
  simp
end GlobalTheory.SmGL.MultiIrr
