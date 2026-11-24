-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.PrimV.primitiveCompact_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:47:00.458277+00:00
-- url     : https://prove2.me/submissions/ee550e58-3810-4ec0-87ea-5b9e480699d6

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_HypJ
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRing
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_LocAtA
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_LocalPrimitiveVectorCompactRescale
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_PrimV_primitiveCompact_prod
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_PrimV_primitiveCompact_of_ringEquiv
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_PrimV_gg_rr
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_PrimV_rr_gg
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_PrimV_rr_mul
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_PrimV_rr_add
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_PrimV_primitiveCompact_normedField
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
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PrimV
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
variable {L K : Type*} [NormedField L] [ProperSpace L]
variable [CommRing K] [Algebra L K] [TopologicalSpace K] (bs : Module.Basis (Fin 2) L K)
namespace GlobalTheory.CompanionTheory.SW.PrimV
theorem _root_.solution (h0 : bs 0 = 1) {D : L} (hd : bs 1 * bs 1 = algebraMap L K D) {s : L} (hs : s ≠ 0)
    (hD : s * s = D) (h2 : (2 : L) ≠ 0) (hg : Continuous (gg (bs 1) : L × L → K)) (M : ℕ) : UniP K M := by
  let e : K ≃+* L × L :=
    { toFun := fun x => ((rr bs x).1 + s * (rr bs x).2, (rr bs x).1 - s * (rr bs x).2)
      invFun := fun w => gg (bs 1) ((w.1 + w.2) / 2, (w.1 - w.2) / (2 * s))
      left_inv := fun x => by
        have e1 : ((rr bs x).1 + s * (rr bs x).2 + ((rr bs x).1 - s * (rr bs x).2)) / 2 = (rr bs x).1 := by
          field_simp
          ring
        have e2 : ((rr bs x).1 + s * (rr bs x).2 - ((rr bs x).1 - s * (rr bs x).2)) / (2 * s) = (rr bs x).2 := by
          field_simp
          ring
        simp only [e1, e2]
        exact gg_rr bs h0 x
      right_inv := fun w => by
        simp only [rr_gg bs h0]
        refine Prod.ext ?_ ?_
        · simp only
          field_simp
          ring
        · simp only
          field_simp
          ring
      map_mul' := fun x y => by
        simp only [rr_mul bs h0 hd, ← hD]
        refine Prod.ext ?_ ?_
        · simp only [Prod.fst_mul]
          ring
        · simp only [Prod.snd_mul]
          ring
      map_add' := fun x y => by
        simp only [rr_add]
        refine Prod.ext ?_ ?_
        · simp only [Prod.fst_add, Prod.snd_add]
          ring
        · simp only [Prod.fst_add, Prod.snd_add]
          ring }
  refine primitiveCompact_of_ringEquiv e ?_ (primitiveCompact_prod (primitiveCompact_normedField M) (primitiveCompact_normedField M))
  show Continuous fun w : L × L => gg (bs 1) ((w.1 + w.2) / 2, (w.1 - w.2) / (2 * s))
  exact hg.comp (by fun_prop)
end GlobalTheory.CompanionTheory.SW.PrimV
