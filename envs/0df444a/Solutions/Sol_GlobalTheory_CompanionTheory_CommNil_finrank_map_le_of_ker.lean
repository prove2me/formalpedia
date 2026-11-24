-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CommNil.finrank_map_le_of_ker
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:24:19.879583+00:00
-- url     : https://prove2.me/submissions/7ac87226-7493-4158-ba48-d83e156ccacf

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_FinrankRangePowConvex
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace GlobalTheory.CompanionTheory.CommNil
open Module
variable {V : Type} [AddCommGroup V] [Module ℂ V]
private theorem finrank_map_add_finrank_inf_ker' {E F : Type} [AddCommGroup E] [Module ℂ E]
    [FiniteDimensional ℂ E] [AddCommGroup F] [Module ℂ F] (f : E →ₗ[ℂ] F) (A : Submodule ℂ E) :
    finrank ℂ (A.map f) + finrank ℂ (A ⊓ LinearMap.ker f : Submodule ℂ E) = finrank ℂ A := by
  have h := LinearMap.finrank_range_add_finrank_ker (f.domRestrict A)
  rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict] at h
  rw [← Submodule.map_comap_subtype, Submodule.finrank_map_subtype_eq]
  exact h
end GlobalTheory.CompanionTheory.CommNil
end

set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CommNil
open Module
variable {V : Type} [AddCommGroup V] [Module ℂ V]
namespace GlobalTheory.CompanionTheory.CommNil
theorem _root_.solution {E F G : Type} [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E]
    [AddCommGroup F] [Module ℂ F] [AddCommGroup G] [Module ℂ G]
    (f : E →ₗ[ℂ] F) (T : E →ₗ[ℂ] G) (A : Submodule ℂ E)
    (h : ∀ b ∈ A, T b = 0 → f b = 0) : finrank ℂ (A.map f) ≤ finrank ℂ (A.map T) := by
  have hf := finrank_map_add_finrank_inf_ker' f A
  have hT := finrank_map_add_finrank_inf_ker' T A
  have hle : finrank ℂ (A ⊓ LinearMap.ker T : Submodule ℂ E) ≤ finrank ℂ (A ⊓ LinearMap.ker f : Submodule ℂ E) :=
    Submodule.finrank_mono fun b hb => Submodule.mem_inf.2 ⟨(Submodule.mem_inf.1 hb).1,
      LinearMap.mem_ker.2 (h b (Submodule.mem_inf.1 hb).1 (LinearMap.mem_ker.1 (Submodule.mem_inf.1 hb).2))⟩
  omega
end GlobalTheory.CompanionTheory.CommNil
