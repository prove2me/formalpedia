-- Prove2me | solution 1 for GlobalTheory.SmGL.hasSatake_detRep
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:55:24.853794+00:00
-- url     : https://prove2.me/submissions/3f6e9579-547e-4617-b398-2a21092c0878

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsUnitarisableOfCharIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_LeviEmbMemNormalizerLower
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Theorems.Thm_GlobalTheory_SmGL_isUnram_absPow
import Theorems.Thm_GlobalTheory_SmGL_isSmoothChar_of_isUnram
import Theorems.Thm_GlobalTheory_SmGL_eq_unrChar
import Theorems.Thm_GlobalTheory_SmGL_detLevi_apply
import Theorems.Thm_GlobalTheory_SmGL_isSubquotient_detRep_parInd
import Theorems.Thm_GlobalTheory_SmGL_modExp_fin
import Theorems.Thm_GlobalTheory_SmGL_isSpherical_detRep
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_comp
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
theorem _root_.solution {N : ℕ} {χ : kˣ →* ℂˣ} (h : IsUnram χ) {ϖ : kˣ}
    (hϖ : valuation k (ϖ : k) = uniformizer k) :
    HasSatake (detRep (Fin N) χ)
      fun i => χ ϖ * absPow k (((i : ℕ) : ℂ) - ((N : ℂ) - 1) / 2) ϖ := by
  refine ⟨isIrreducible_ofChar _, isSpherical_detRep h, ?_⟩
  have key : (ofChar (torusChar fun i : Fin N => unrChar k
      (χ ϖ * absPow k (((i : ℕ) : ℂ) - ((N : ℂ) - 1) / 2) ϖ))).comp
        (leviTorus k (Fin N)).symm.toMonoidHom = ofChar (detLevi (points (Fin N)) χ) := by
    refine MonoidHom.ext fun g => LinearMap.ext fun y => ?_
    show ofChar _ _ y = _
    rw [ofChar_apply, ofChar_apply, detLevi_apply, torusChar_apply]
    congr 2
    refine Finset.prod_congr rfl fun i _ => ?_
    have hu : IsUnram (χ * absPow k (((i : ℕ) : ℂ) - ((N : ℂ) - 1) / 2)) := fun x hx => by
      rw [MonoidHom.mul_apply, h x hx, isUnram_absPow k _ x hx, one_mul]
    rw [← MonoidHom.mul_apply, ← eq_unrChar hu hϖ, modExp_fin _ (fun _ => by simp)]
    congr 3
    push_cast
    ring
  have := isSubquotient_detRep_parInd (points (Fin N)) (isSmoothChar_of_isUnram h)
  rw [← key] at this
  exact this
end GlobalTheory.SmGL
