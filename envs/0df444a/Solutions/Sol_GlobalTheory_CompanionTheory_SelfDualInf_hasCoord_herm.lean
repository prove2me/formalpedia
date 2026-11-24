-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SelfDualInf.hasCoord_herm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:47:31.875194+00:00
-- url     : https://prove2.me/submissions/b25dff42-befc-4746-830a-a3eafce0c857

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SiegelWeilUnitaryConvergent
import Definitions.Def_Formalism_UnipotentAdelicQuotients_StdAdditiveCharExists
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_HermitianForms_BijectiveLinearCombinationOfRankAtStalk
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_HermitianCharacters_SelfDualLatticeFiltrationCharacter
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_HermitianForms_HasCoordOfFiniteDimensional
import Theorems.Thm_GlobalTheory_CompanionTheory_SelfDualInf_HasCoord_pi
import Theorems.Thm_GlobalTheory_CompanionTheory_SelfDualInf_HasCoord_fixed
import Theorems.Thm_GlobalTheory_CompanionTheory_SelfDualInf_isTopologicalRing_tens
import Theorems.Thm_GlobalTheory_CompanionTheory_SelfDualInf_continuous_sigR
import Theorems.Thm_GlobalTheory_CompanionTheory_SelfDualInf_hasCoord_tens
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Idele.adelicMulEquiv_mk



set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory HeckeCharacterZeroLocus.SiegelWeilU
open scoped TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SelfDualInf
variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
  (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
  (σ : E →ₐ[F] E)
namespace GlobalTheory.CompanionTheory.SelfDualInf
theorem _root_.solution (h : HasCoord R) (n : ℕ) (hσ : ∀ x, σ (σ x) = x) :
    HasCoord (HermR R σ n) := by
  have := isTopologicalRing_tens (F := F) (E := E) R
  have hm : HasCoord (Matrix (Fin n) (Fin n) (R ⊗[F] E)) :=
    ((hasCoord_tens R h).pi (Fin n)).pi (Fin n)
  let f : Matrix (Fin n) (Fin n) (R ⊗[F] E) →+ Matrix (Fin n) (Fin n) (R ⊗[F] E) :=
    AddMonoidHom.mk' (fun S => (S.map (sigR R σ)).transpose) fun S T => by
      ext i j; simp
  have hf : Continuous f := ((continuous_id.matrix_map (continuous_sigR R σ))).matrix_transpose
  refine hm.fixed f hf _ fun S => ⟨fun hS => ?_, fun hS a b => ?_⟩
  · ext a b; exact hS a b
  · exact congrFun (congrFun hS a) b
end GlobalTheory.CompanionTheory.SelfDualInf
