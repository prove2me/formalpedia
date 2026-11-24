-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SdFin.BR_symm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T15:02:23.435237+00:00
-- url     : https://prove2.me/submissions/bdb8c596-f446-416e-994f-eb96c6193fc2

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SiegelWeilUnitaryConvergent
import Definitions.Def_Formalism_UnipotentAdelicQuotients_StdAdditiveCharExists
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_HermitianForms_IndicatorInSchrodingerSpanStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_HermitianForms_AdelicCharacterLocalNontrivial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsSmallDualLattices
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_AdditiveCharConductorExists
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Tjcosets
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_HermitianForms_ExistsSdWSdHerm
import Theorems.Thm_GlobalTheory_CompanionTheory_SdFin_hR_symm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory HeckeCharacterZeroLocus.SiegelWeilU Topology
open scoped TensorProduct
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SdFin
variable {F E : Type} [Field F] [Field E] [Algebra F E]
  (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E)
variable {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
namespace GlobalTheory.CompanionTheory.SdFin
theorem _root_.solution [FiniteDimensional F E] (hσ : ∀ x, σ (σ x) = x) (hJ : IsHermND σ J) {n : ℕ}
    (X Y : Fin n → Fin M → R ⊗[F] E) : BR R σ J X Y = BR R σ J Y X :=
  Finset.sum_congr rfl fun a _ => hR_symm R σ J hσ hJ (X a) (Y a)
end GlobalTheory.CompanionTheory.SdFin
