-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.NullV.qR_line
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:42:51.42603+00:00
-- url     : https://prove2.me/submissions/7451d651-0eca-45e1-90e3-eb1de973b9de

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianNondegRepresentsNonzeroScalar
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_CompletionIsLocalRing
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRing
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_HaarMeasureNonunitsNull
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_NullV_sigR_algebraMap
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
theorem _root_.solution [Module.Free F E] [Module.Finite F E] (x y : Fin M → R ⊗[F] E) (s : R) :
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR R σ J (fun j => x j + algebraMap R (R ⊗[F] E) s * y j) =
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR R σ J x +
        s * (algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E)
          (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hR R σ J x y + Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hR R σ J y x)) +
        s ^ 2 * Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR R σ J y := by
  have h : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hR R σ J (fun j => x j + algebraMap R (R ⊗[F] E) s * y j)
        (fun j => x j + algebraMap R (R ⊗[F] E) s * y j) =
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hR R σ J x x +
        algebraMap R (R ⊗[F] E) s *
          (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hR R σ J x y + Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hR R σ J y x) +
        algebraMap R (R ⊗[F] E) (s ^ 2) * Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hR R σ J y y := by
    simp only [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hR, Formalism.UG.hform, map_add, map_mul, map_pow, sigR_algebraMap,
      Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have ht : ∀ (c : R) (a : R ⊗[F] E), Algebra.trace R (R ⊗[F] E) (algebraMap R (R ⊗[F] E) c * a) =
      c * Algebra.trace R (R ⊗[F] E) a := by
    intro c a
    rw [← Algebra.smul_def, map_smul, smul_eq_mul]
  rw [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR, h, map_add, map_add, ht, ht, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR]
  ring
end GlobalTheory.CompanionTheory.SW.NullV
