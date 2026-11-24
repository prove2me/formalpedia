-- Prove2me | solution 1 for GlobalTheory.SmGL.inSupport_detRep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:04:16.03534+00:00
-- url     : https://prove2.me/submissions/aed5f2aa-0b3c-49ff-9ccc-792de9595217

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsUnitarisableOfCharIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_LeviEmbMemNormalizerLower
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Theorems.Thm_GlobalTheory_SmGL_detLevi_apply
import Theorems.Thm_GlobalTheory_SmGL_isSubquotient_jac_detRep
import Theorems.Thm_GlobalTheory_SmGL_modExp_fin
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
open GlobalTheory.PRep GlobalTheory.SplitWeil ValuativeRel
open scoped TensorProduct
open GlobalTheory GlobalTheory.SmGL
open Matrix
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]
namespace GlobalTheory.SmGL
theorem _root_.solution {N : ℕ} (χ : kˣ →* ℂˣ) (i : Fin N) :
    InSupport (detRep (Fin N) χ) (χ * absPow k (((i : ℕ) : ℂ) - ((N : ℂ) - 1) / 2)) := by
  let e : (Σ _ : Fin N, Fin 1) ≃ Fin N := Equiv.sigmaUnique _ _
  refine ⟨N, fun _ => 1, e, i, rfl, ℂ, inferInstance, inferInstance, ofChar (detLevi e χ),
    isIrreducible_ofChar _, isSubquotient_jac_detRep e χ, fun g y => ?_⟩
  rw [ofChar_apply, detLevi_apply, Finset.prod_eq_single i, Pi.mulSingle_eq_same,
    modExp_fin _ (fun _ => by simp), smul_eq_mul]
  · congr 6
    push_cast
    ring
  · intro j _ hj
    rw [Pi.mulSingle_eq_of_ne hj, map_one, map_one]
  · simp
end GlobalTheory.SmGL
