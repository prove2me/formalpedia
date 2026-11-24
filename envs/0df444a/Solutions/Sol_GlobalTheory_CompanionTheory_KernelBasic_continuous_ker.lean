-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.KernelBasic.continuous_ker
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:40:52.746018+00:00
-- url     : https://prove2.me/submissions/769147b2-013f-4b5c-b435-6e61399b4515

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_ThetaCellCovers_KernelL2RowsColumns
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FiniteOfCompact
import Theorems.Thm_GlobalTheory_CompanionTheory_KernelBasic_finite_of_compact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory PositivityTheory.Rg.BcB.E1
open scoped ENNReal Pointwise
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.KernelBasic
namespace GlobalTheory.CompanionTheory.KernelBasic
theorem _root_.solution (X : Ctx) {φ : X.G → ℂ} (hφ : Tst φ) :
    Continuous (Function.uncurry (ker X.Γ φ)) := by
  have e : Function.uncurry (ker X.Γ φ) =
      fun p : X.G × X.G => ∑ᶠ γ : X.Γ, φ (p.1⁻¹ * (γ : X.G) * p.2) := by
    funext p
    rfl
  rw [e]
  refine continuous_finsum (fun γ => ?_) ?_
  · exact hφ.1.comp ((continuous_fst.inv.mul continuous_const).mul continuous_snd)
  · rintro ⟨x, y⟩
    obtain ⟨U, hU, hUx⟩ := exists_compact_mem_nhds x
    obtain ⟨V, hV, hVy⟩ := exists_compact_mem_nhds y
    refine ⟨U ×ˢ V, prod_mem_nhds hUx hVy, ?_⟩
    refine (finite_of_compact X hφ.2 hU hV).subset ?_
    rintro γ ⟨⟨a, b⟩, hs, hab⟩
    exact ⟨a, hab.1, b, hab.2, hs⟩
end GlobalTheory.CompanionTheory.KernelBasic
