-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.LenFib.qR_of_gram
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:30:42.910804+00:00
-- url     : https://prove2.me/submissions/af913129-8374-46e2-938a-c908d44af0c8

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ContinuousHermScal
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRing
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IsFibreFamilyLength
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_LenFib_qR_eq_hermHalf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.LenFib
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable (R : Type) [CommRing R] [Algebra F R]
namespace GlobalTheory.CompanionTheory.SW.LenFib
theorem _root_.solution [TopologicalSpace R] [IsTopologicalRing R] {σ : E →ₐ[F] E}
    (hσ : IsCMExt F E σ) {M : ℕ}
    {J : Matrix (Fin M) (Fin M) E} (hJ : IsHermND σ J) {X : Fin 1 → Fin M → R ⊗[F] E} {c : R}
    (h : gramR R σ J X = ((hermScal R σ c : HermR R σ 1) : Matrix (Fin 1) (Fin 1) (R ⊗[F] E))) :
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR R σ J (X 0) = c := by
  have h' : gramH R hσ hJ X = hermScal R σ c := Subtype.ext h
  rw [qR_eq_hermHalf R hσ hJ X, h', OneHerm.hermHalf_hermScal R hσ]
end GlobalTheory.CompanionTheory.SW.LenFib
