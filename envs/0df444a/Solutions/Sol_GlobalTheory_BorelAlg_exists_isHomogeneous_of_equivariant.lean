-- Prove2me | solution 1 for GlobalTheory.BorelAlg.exists_isHomogeneous_of_equivariant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:38:31.373836+00:00
-- url     : https://prove2.me/submissions/b3803f95-2757-4e8b-83f4-c0482748bc0f

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_SectionOfLineBundleOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IrreducibleDetOfIsRelPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsIsHomogeneousOfEquivariant
import Theorems.Thm_GlobalTheory_BorelAlg_Equivariant_exists_isHomogeneous

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open GlobalTheory GlobalTheory.BorelAlg
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
namespace GlobalTheory.BorelAlg
theorem _root_.solution :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (K : Type) [Field K] (a : (E →+* ℂ) × ℕ → ℕ) (f : ArcS Dw K), (∀ (T : Type) [Field T] (φ ψ : ArcS Dw K →+* T) (b : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) T), (∀ g : LaurentSeries K, φ (algebraMap (MvPolynomial (ArcLt Dw) (LaurentSeries K)) _ (MvPolynomial.C g)) = ψ (algebraMap (MvPolynomial (ArcLt Dw) (LaurentSeries K)) _ (MvPolynomial.C g))) → (∀ τ i j, i < j → b τ i j = 0) → (∀ τ i k, ψ (arcX Dw K τ i k) = ∑ j, b τ i j * φ (arcX Dw K τ j k)) → ψ f = (∏ τ, ∏ i, b τ i i ^ a (τ, (i : ℕ))) * φ f) → ∃ P : MvPolynomial (ArcLt Dw) (LaurentSeries K), algebraMap _ (ArcS Dw K) P = f ∧ P.IsHomogeneous (∑ τ : E →+* ℂ, ∑ i : Fin (Dw.mult τ), a (τ, (i : ℕ))) := by
  intro E _ _ _ H Dw K _ a f hf
  haveI : IsLocalization.Away (∏ τ, (gen Dw.mult (LaurentSeries K) τ).det) (ArcS Dw K) :=
    (inferInstance : IsLocalization.Away (arcDet Dw K) (ArcS Dw K))
  exact Equivariant.exists_isHomogeneous (m := Dw.mult) (L := LaurentSeries K) hf
end GlobalTheory.BorelAlg
