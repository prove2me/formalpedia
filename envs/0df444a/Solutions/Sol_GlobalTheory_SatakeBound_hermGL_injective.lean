-- Prove2me | solution 1 for GlobalTheory.SatakeBound.hermGL_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:13:28.32283+00:00
-- url     : https://prove2.me/submissions/6216594f-7b1c-450c-8916-33233b2c3699

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_SatakeTrivialRangeBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasBoundedSumsOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwasawaBlockTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RelativeLatticeVolumeOfDetValuation
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_EqOfHasValueAtInfinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormLeCard
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsIsBorelSphRevInv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormLeOfCompleteHomogeneousLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HermiteReductionUnipotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PowDvdOfHermMatEq
import Theorems.Thm_GlobalTheory_SatakeBound_pow_dvd_of_hermMat_eq
import Theorems.Thm_GlobalTheory_SatakeBound_eq_of_hermMat_eq
import Theorems.Thm_GlobalTheory_SatakeBound_hermMat_eq_of_coe_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel
open GlobalTheory GlobalTheory.SatakeBound
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
  {p : 𝒪[k]}
namespace GlobalTheory.SatakeBound
theorem _root_.solution (hp : Irreducible p) : Function.Injective
    fun x : Σ a : Fin n → ℕ, HermIdx p a => (hermGL hp x.1 x.2 : GL (Fin n) k ⧸ KO k (Fin n)) := by
  rintro ⟨a, c⟩ ⟨a', c'⟩ h
  obtain ⟨W, hW⟩ := hermMat_eq_of_coe_eq hp h
  obtain ⟨W', hW'⟩ := hermMat_eq_of_coe_eq hp h.symm
  obtain rfl : a = a' := funext fun i => le_antisymm
    ((pow_dvd_pow_iff hp.ne_zero hp.not_isUnit).1 (pow_dvd_of_hermMat_eq hp.ne_zero hW i))
    ((pow_dvd_pow_iff hp.ne_zero hp.not_isUnit).1 (pow_dvd_of_hermMat_eq hp.ne_zero hW' i))
  exact congrArg (Sigma.mk a) (eq_of_hermMat_eq hp.ne_zero hW')
end GlobalTheory.SatakeBound
