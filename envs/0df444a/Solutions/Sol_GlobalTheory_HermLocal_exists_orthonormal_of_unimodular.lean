-- Prove2me | solution 1 for GlobalTheory.HermLocal.exists_orthonormal_of_unimodular
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:47:09.659607+00:00
-- url     : https://prove2.me/submissions/1a05d438-c440-4e1c-80fd-907cc1d4c13a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsCongrIffTraceFormsIsometricCm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_HasseNormTheoremQuadraticExtension
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_UnimodUnramUnique
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_ExistsOrthonormalOfUnimodular
import Theorems.Thm_Formalism_HermitianLatticesTheory_unimodUnramUnique
import Theorems.Thm_GlobalTheory_LocalQuad_HermClass_Congr_det
import Theorems.Thm_GlobalTheory_LocalQuad_HermClass_Congr_symm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Matrix TensorProduct ComplexConjugate WithZero
open ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.LocalQuad GlobalTheory.LocalQuad.HermClass
open GlobalTheory GlobalTheory.HermLocal
namespace GlobalTheory.HermLocal
theorem _root_.solution (R : Type) [CommRing R] (σ : R ≃+* R)
    (hσ : ∀ x, σ (σ x) = x) (R₀ : Subring R) (hR₀ : ∀ x, x ∈ R₀ ↔ σ x = x)
    [HenselianLocalRing R₀] [Finite (IsLocalRing.ResidueField R₀)]
    (hθ : ∃ θ : R, IsUnit (θ - σ θ)) {n : ℕ} {A : Matrix (Fin n) (Fin n) R}
    (hA : ∀ a b, σ (A a b) = A b a) (hd : IsUnit A.det) :
    ∃ P : Matrix (Fin n) (Fin n) R, IsUnit P.det ∧ Pᵀ * A * P.map σ = 1 := by
  obtain ⟨g, hg, h⟩ := Formalism.HermitianLatticesTheory.unimodUnramUnique R σ hσ R₀ hR₀ hθ n A
    (by ext a b; exact hA b a) hd
  refine ⟨g.map σ, ?_, ?_⟩
  · rw [show (g.map σ).det = σ g.det from (RingHom.map_det (σ : R →+* R) g).symm]
    exact hg.map σ
  · rwa [show (g.map σ).map σ = g by ext a b; exact hσ _]
end GlobalTheory.HermLocal
