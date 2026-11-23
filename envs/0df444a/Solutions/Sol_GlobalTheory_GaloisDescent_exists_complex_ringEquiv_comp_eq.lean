-- Prove2me | solution 1 for GlobalTheory.GaloisDescent.exists_complex_ringEquiv_comp_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:05:09.443858+00:00
-- url     : https://prove2.me/submissions/d648fa3c-4dee-4864-bdbf-a0768bac287b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsRingEquivOfIsTranscendenceBasis
import Theorems.Thm_GlobalTheory_GaloisDescent_exists_ringEquiv_of_isTranscendenceBasis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Cardinal
open GlobalTheory GlobalTheory.GaloisDescent
open MvPolynomial Cardinal
namespace GlobalTheory.GaloisDescent
namespace _root_.GlobalTheory.GaloisDescent
theorem _root_.solution {K : Type} [Field K] [Countable K] (f g : K →+* ℂ) :
    ∃ σ : ℂ ≃+* ℂ, ∀ a, σ (f a) = g a := by
  have hK : Cardinal.mk K ≤ Cardinal.aleph0 := Cardinal.mk_le_aleph0
  have hC : Cardinal.aleph0 < Cardinal.mk ℂ := by
    rw [Cardinal.mk_complex]; exact Cardinal.aleph0_lt_continuum
  letI Af : Algebra K ℂ := f.toAlgebra
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis K ℂ
  have hsc := IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt' _ hs hK hC
  letI Ag : Algebra K ℂ := g.toAlgebra
  obtain ⟨t, ht⟩ := exists_isTranscendenceBasis K ℂ
  have htc := IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt' _ ht hK hC
  obtain ⟨eqv⟩ := Cardinal.eq.1 (hsc.symm.trans htc)
  obtain ⟨σ, hσ⟩ := @_root_.GlobalTheory.GaloisDescent.exists_ringEquiv_of_isTranscendenceBasis K K ℂ ℂ s t _ _ _ _ Af Ag _ _ _ _
    hs ht (MvPolynomial.renameEquiv K eqv).toRingEquiv
  refine ⟨σ, fun a => ?_⟩
  simpa [RingHom.algebraMap_toAlgebra] using hσ (MvPolynomial.C a)
end _root_.GlobalTheory.GaloisDescent
end GlobalTheory.GaloisDescent
