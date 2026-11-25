-- Prove2me | solution 1 for GlobalTheory.QCoh.section_eq_zero_of_germ_assPoints
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:07:48.069324+00:00
-- url     : https://prove2.me/submissions/d3c63ca5-c523-4fd0-b5c2-5c9b6476f744

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsLocalizedModuleGermLinearPointOfPrime
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_TopologicalKrullDimLeOfIrreducibleCloseds
import Theorems.Thm_GlobalTheory_QCoh_pointOfPrime_mem_assPoints_iff
import Theorems.Thm_GlobalTheory_QCoh_germLinear_apply
import Theorems.Thm_GlobalTheory_QCoh_isLocalizedModule_germLinear_pointOfPrime
import Theorems.Thm_GlobalTheory_QCoh_section_eq_zero_of_germ
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.QCoh.germLinear_apply



set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite TensorProduct IsLocalRing
universe u
noncomputable section
open GlobalTheory GlobalTheory.QCoh
variable {X : Scheme.{u}} {F G H : X.Modules} {U V : X.Opens}
variable [IsLocallyNoetherian X]
namespace GlobalTheory.QCoh
theorem _root_.solution [F.IsQuasicoherent] (s : Γ(F, U))
    (h : ∀ x ∈ assPoints F, ∀ hx : x ∈ U, F.presheaf.germ U x hx s = 0) : s = 0 := by
  refine section_eq_zero_of_germ s fun x hx ↦ ?_
  obtain ⟨V, hV, hxV, hVU⟩ := exists_affine_mem_le x hx
  rw [← F.presheaf.germ_res_apply (homOfLE hVU) x hxV]
  suffices F.presheaf.map (homOfLE hVU).op s = 0 by rw [this, map_zero]
  by_contra hs
  have : IsNoetherianRing Γ(X, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  obtain ⟨P, hP, hle⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing Γ(X, V) _ hs
  have := hP.isPrime
  have := isLocalizedModule_germLinear_pointOfPrime F hV P
  let y := pointOfPrime hV ⟨P, hP.isPrime⟩
  have hy : germLinear F y (F.presheaf.map (homOfLE hVU).op s) = 0 := by
    rw [germLinear_apply, F.presheaf.germ_res_apply]
    exact h y ((pointOfPrime_mem_assPoints_iff hV _).2 hP) _
  obtain ⟨r, hr⟩ := (IsLocalizedModule.eq_zero_iff P.primeCompl (germLinear F y)).1 hy
  exact r.2 (hle (Submodule.mem_colon_singleton.2 hr))
end GlobalTheory.QCoh
