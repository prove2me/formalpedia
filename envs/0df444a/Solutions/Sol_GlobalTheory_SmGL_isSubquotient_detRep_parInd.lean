-- Prove2me | solution 1 for GlobalTheory.SmGL.isSubquotient_detRep_parInd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:40:37.508882+00:00
-- url     : https://prove2.me/submissions/abbcbae8-87de-410f-9577-baaf50e23e77

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsUnitarisableOfCharIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_LeviEmbMemNormalizerLower
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_of_injective
import Theorems.Thm_GlobalTheory_SmGL_det_leviEmb
import Theorems.Thm_GlobalTheory_SmGL_det_parab


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
theorem _root_.solution (e : (Σ a, m a) ≃ n) {χ : kˣ →* ℂˣ} (hχ : IsSmoothChar χ) :
    IsSubquotient (detRep n χ) (parInd e (ofChar (detLevi e χ))) := by
  let f : ℂ →ₗ[ℂ] IndSp e (ofChar (detLevi e χ)) :=
    { toFun := fun c => ⟨⟨fun g => (detChar n χ g : ℂ) * c, fun p g => by
          have : GeneralLinearGroup.det (leviEmb k e (leviProj k e p)) =
              GeneralLinearGroup.det (p : GL n k) := by rw [det_leviEmb, det_parab]
          show _ = (deltaHalf k m _ : ℂ) • ofChar (detLevi e χ) (leviProj k e p) _
          simp [detLevi, this, mul_assoc, mul_left_comm (deltaHalf k m (leviProj k e p) : ℂ)]⟩,
        mem_smoothPart_of_nhds (Filter.mem_of_superset
          (IsOpen.mem_nhds (hχ.detChar (n := n)) (one_mem _)) fun g hg => by
            have hg' : detChar n χ g = 1 := hg
            apply Subtype.ext
            funext x
            show (detChar n χ (x * g) : ℂ) * c = (detChar n χ x : ℂ) * c
            rw [map_mul, hg', mul_one])⟩
      map_add' := fun c d => by ext g; exact mul_add _ _ _
      map_smul' := fun c d => by ext g; exact mul_left_comm _ _ _ }
  refine .of_injective ⟨f, fun g => ?_⟩ fun c d h => ?_
  · refine LinearMap.ext fun c => Subtype.ext (Subtype.ext (funext fun x => ?_))
    show (detChar n χ x : ℂ) * (detRep n χ g c) = (detChar n χ (x * g) : ℂ) * c
    simp [detRep, mul_assoc]
  · simpa [f] using congrFun (congrArg (fun φ => φ.1.1) h) 1
end GlobalTheory.SmGL
