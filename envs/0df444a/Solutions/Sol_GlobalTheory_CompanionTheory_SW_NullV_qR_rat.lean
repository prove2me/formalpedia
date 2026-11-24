-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.NullV.qR_rat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:24:29.112343+00:00
-- url     : https://prove2.me/submissions/da3558bf-5a67-4c7f-9cad-072eba7213c6

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianNondegRepresentsNonzeroScalar
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_CompletionIsLocalRing
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRing
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_HaarMeasureNonunitsNull
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
noncomputable section
open scoped Pointwise
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.NullV
variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
namespace GlobalTheory.CompanionTheory.SW.NullV
theorem _root_.solution [CharZero F] (b : Module.Basis (Fin 2) F E) (x : Fin M → E) (β : F)
    (h : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hE σ J x x = algebraMap F E β) :
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR R σ J (fun j => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) R (x j)) = algebraMap F R β := by
  have h1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hR R σ J (fun j => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) R (x j))
      (fun j => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) R (x j)) =
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) R (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hE σ J x x) := by
    simp only [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hR, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hE, Formalism.UG.hform, map_sum, map_mul,
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR, Matrix.map_apply]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    congr 2
  have h2 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) R (algebraMap F E β) =
      algebraMap R (R ⊗[F] E) (algebraMap F R β) := by
    rw [← IsScalarTower.algebraMap_apply]
    exact (Algebra.TensorProduct.includeRight : E →ₐ[F] R ⊗[F] E).commutes β
  rw [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR, h1, h, h2, Algebra.trace_algebraMap_of_basis (Algebra.TensorProduct.basis R b),
    Fintype.card_fin, ← map_nsmul, ← map_mul]
  congr 1
  rw [nsmul_eq_mul]; push_cast; field_simp
end GlobalTheory.CompanionTheory.SW.NullV
