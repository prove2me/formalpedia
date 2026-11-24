-- Prove2me | solution 1 for GlobalTheory.IsQuasiRegularSeq.of_isLocalizedModule_maximal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:05:03.911562+00:00
-- url     : https://prove2.me/submissions/c2534135-feaa-4dbf-b215-c7ced814035c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsQuasiRegularSeqSelfIffLocalizationMaximal
import Theorems.Thm_GlobalTheory_exists_smul_mem_smul_top_of_isLocalizedModule

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory
variable {R : Type*} [CommRing R] {ι : Type*} [Finite ι]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable (S : Type*) [CommRing S] [Algebra R S]
variable {N : Type*} [AddCommGroup N] [Module R N]
namespace GlobalTheory
namespace IsQuasiRegularSeq
theorem _root_.solution {f : ι → R}
    (Mₚ : ∀ (P : Ideal R) [P.IsMaximal], Type*)
    [∀ (P : Ideal R) [P.IsMaximal], AddCommGroup (Mₚ P)]
    [∀ (P : Ideal R) [P.IsMaximal], Module R (Mₚ P)]
    (g : ∀ (P : Ideal R) [P.IsMaximal], M →ₗ[R] Mₚ P)
    [∀ (P : Ideal R) [P.IsMaximal], IsLocalizedModule P.primeCompl (g P)]
    (h : ∀ (P : Ideal R) [P.IsMaximal], Ideal.span (Set.range f) ≤ P →
      IsQuasiRegularSeq (Mₚ P) f) : IsQuasiRegularSeq M f := by
  intro a c hc α
  by_contra hα
  let J : Ideal R := (Ideal.span (Set.range f) • ⊤ : Submodule R M).comap
    (LinearMap.toSpanSingleton R M (c α))
  have hJ : J ≠ ⊤ := fun hJ => hα (by simpa [J] using (Ideal.eq_top_iff_one J).mp hJ)
  obtain ⟨P, hP, hJP⟩ := Ideal.exists_le_maximal J hJ
  have hIJ : Ideal.span (Set.range f) ≤ J := fun r hr => Submodule.smul_mem_smul hr trivial
  have := h P (hIJ.trans hJP) a (fun β => g P (c β)) (by
    simpa using Submodule.smul_top_le_comap_smul_top _ (g P) hc) α
  obtain ⟨s, hs, hsx⟩ := exists_smul_mem_smul_top_of_isLocalizedModule P.primeCompl (g P) _ this
  exact hs (hJP hsx)
end IsQuasiRegularSeq
end GlobalTheory
