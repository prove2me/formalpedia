-- Prove2me | solution 1 for GlobalTheory.BetaEx.span_image_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:01:27.673919+00:00
-- url     : https://prove2.me/submissions/639c6178-7803-4f36-bd64-c35299b591d7

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsIndexIdeal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.BetaEx
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
variable {E F : Type} [Field E] [Field F] (φ : E →+* F)
namespace GlobalTheory.BetaEx
theorem _root_.solution (𝔞 : Ideal (𝓞 E)) (N : Submodule (𝓞 E) E) :
    Submodule.span (𝓞 F) (φ '' ((𝔞 • N : Submodule (𝓞 E) E) : Set E)) =
      Submodule.span (𝓞 F) ((φ.comp (algebraMap (𝓞 E) E)) '' (𝔞 : Set (𝓞 E))) *
        Submodule.span (𝓞 F) (φ '' (N : Set E)) := by
  apply le_antisymm
  · apply Submodule.span_le.2
    rintro _ ⟨x, hx, rfl⟩
    refine Submodule.smul_induction_on hx ?_ ?_
    · intro a ha y hy
      rw [Algebra.smul_def, map_mul]
      exact Submodule.mul_mem_mul (Submodule.subset_span ⟨a, ha, rfl⟩) (Submodule.subset_span ⟨y, hy, rfl⟩)
    · intro x y hx hy
      rw [map_add]; exact Submodule.add_mem _ hx hy
  · rw [Submodule.span_mul_span]
    apply Submodule.span_mono
    rintro _ ⟨_, ⟨a, ha, rfl⟩, _, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨a • y, Submodule.smul_mem_smul ha hy, by rw [Algebra.smul_def, map_mul]; rfl⟩
end GlobalTheory.BetaEx
