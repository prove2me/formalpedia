-- Prove2me | solution 1 for GlobalTheory.FibreHyp.spectrum_fibre_preirreducible_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:13:55.344792+00:00
-- url     : https://prove2.me/submissions/cf270109-f680-422c-842a-d461be4a07e6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PreirreducibleSpaceFibreHypersurfaceSpectrumIff
import Theorems.Thm_GlobalTheory_FibreHyp_fwd_bwd
import Theorems.Thm_GlobalTheory_FibreHyp_bwd_fwd
import Theorems.Thm_GlobalTheory_FibreHyp_isEmbedding_comap_rhoK
import Theorems.Thm_GlobalTheory_FibreHyp_range_comap_rhoK
import Theorems.Thm_GlobalTheory_FibreHyp_preirreducibleSpace_congr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj
noncomputable section
open GlobalTheory GlobalTheory.FibreHyp
namespace GlobalTheory.FibreHyp
theorem _root_.solution (A : Type) [CommRing A] (σ : Type) (f g : MvPolynomial σ A)
    (k : Type) [Field k] [Algebra A k] :
    PreirreducibleSpace (PrimeSpectrum (k ⊗[A] Localization.Away (Ideal.Quotient.mk (Ideal.span {f}) g))) ↔
      IsPreirreducible (PrimeSpectrum.zeroLocus {MvPolynomial.map (algebraMap A k) f} \
        PrimeSpectrum.zeroLocus {MvPolynomial.map (algebraMap A k) g}) := by
  let e : (k ⊗[A] LA f g) ≃ₐ[k] Lk f g k :=
    AlgEquiv.ofAlgHom (fwd f g k) (bwd2 f g k) (fwd_bwd f g k) (bwd_fwd f g k)
  rw [preirreducibleSpace_congr (PrimeSpectrum.homeomorphOfRingEquiv e.toRingEquiv), ← range_comap_rhoK,
    isPreirreducible_iff_preirreducibleSpace]
  exact preirreducibleSpace_congr (isEmbedding_comap_rhoK f g k).toHomeomorph
end GlobalTheory.FibreHyp
