-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEisExt.extLaw
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:16:31.66909+00:00
-- url     : https://prove2.me/submissions/ddda9006-5734-4c29-80cb-6eaf5c3dee84

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_ConvGrOf
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SectionLawHolds
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExtensionLaw
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisExt_ext_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory.RgEis
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgEisExt
variable {G : Type} [Group G]
namespace GlobalTheory.CompanionTheory.RgEisExt
theorem _root_.solution : ExtLaw := by
  intro G _ _ _ _ Γ K P f hK hP hIwa hadd hfc hfK hfΓ
  have hval : ∀ p ∈ P, ∀ k ∈ K, PositivityTheory.RgEis.ext K P f (p * k) = f p :=
    fun p hp k hk => ext_mul hadd hfK hp hk
  have hone : ∀ p ∈ P, PositivityTheory.RgEis.ext K P f p = f p := by
    intro p hp
    simpa using hval p hp 1 K.one_mem
  refine ⟨⟨?_, ?_, ?_, ?_⟩, hval⟩
  · intro p hp g
    obtain ⟨q, hq, k, hk, rfl⟩ := hIwa g
    rw [← mul_assoc, hval _ (P.mul_mem hp hq) k hk, hval q hq k hk, hone p hp, hadd p hp q hq]
  · intro g k hk
    obtain ⟨q, hq, k', hk', rfl⟩ := hIwa g
    rw [mul_assoc, hval q hq _ (K.mul_mem hk' hk), hval q hq k' hk']
  · intro γ hγ hγP
    rw [hone γ hγP]
    exact hfΓ γ hγP hγ
  · open Pointwise in
    · rw [continuous_iff_isClosed]
      intro C hC
      have hset : PositivityTheory.RgEis.ext K P f ⁻¹' C = ((P : Set G) ∩ f ⁻¹' C) * (K : Set G) := by
        ext g
        constructor
        · intro hg
          obtain ⟨q, hq, k, hk, rfl⟩ := hIwa g
          have hC' : PositivityTheory.RgEis.ext K P f (q * k) ∈ C := hg
          rw [hval q hq k hk] at hC'
          exact Set.mem_mul.mpr ⟨q, ⟨hq, hC'⟩, k, hk, rfl⟩
        · intro hg
          obtain ⟨q, ⟨hq, hqC⟩, k, hk, rfl⟩ := Set.mem_mul.mp hg
          show PositivityTheory.RgEis.ext K P f (q * k) ∈ C
          rw [hval q hq k hk]
          exact hqC
      rw [hset]
      exact (hfc.preimage_isClosed_of_isClosed hP hC).mul_right_of_isCompact hK
end GlobalTheory.CompanionTheory.RgEisExt
