-- Prove2me | solution 1 for GlobalTheory.DegCnt.PosJ.ref_coef
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T06:01:18.550133+00:00
-- url     : https://prove2.me/submissions/dede6f83-cf26-42cd-8fef-00ed043fb92e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LeadingMinorsProdDenominatorUnitriangularFactors
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFramesPairingStabilizerBlockDiagonal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NormalFormFlagLatticesNearUnderStabiliser
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
noncomputable section
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical nonZeroDivisors
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.PosJ
open GlobalTheory.HL Matrix Formalism.MainNotions.S.Loc
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {H : HermSpace K V} {r : ℕ} (N : NF H r)
namespace GlobalTheory.DegCnt.PosJ
theorem _root_.solution (d : V) (A : Submodule (𝓞 K) K)
    (h1 : ∀ b : Fin N.j, ∀ t ∈ N.aa (Fin.castLE N.j_le b), t * H.B (ej N.F N.j_le b) d ∈ A)
    (h2 : ∀ b : Fin N.j, ∀ t ∈ N.aa (Fin.castLE N.j_le b), t * H.B (ej N.F' N.j_le b) d ∈ A)
    (h3 : ∀ b : Fin (r + 1), N.j ≤ (b : ℕ) → H.B (N.F.e b) d = 0)
    (h4 : ∀ b : Fin r, N.j ≤ (b : ℕ) → H.B (N.ist b) d = 0) : ∀ y ∈ N.P0, H.B y d ∈ A := by
  have hl : ∀ (B : Submodule (𝓞 K) K) (v : V), (∀ t ∈ B, t * H.B v d ∈ A) →
      line B v ≤ A.comap ((H.B.flip d).restrictScalars (𝓞 K)) := by
    rintro B v h _ ⟨t, ht, rfl⟩
    simpa using h t ht
  have : N.P0 ≤ A.comap ((H.B.flip d).restrictScalars (𝓞 K)) := by
    refine sup_le (sup_le (sup_le (iSup_le fun a => hl _ _ fun t ht => ?_)
      (iSup₂_le fun a ha => hl _ _ (h2 ⟨a, ha⟩))) (hl _ _ fun t _ => ?_))
      (iSup₂_le fun a ha => hl _ _ fun t _ => ?_)
    · by_cases ha : (a : ℕ) < N.j
      · exact h1 ⟨a, ha⟩ t ht
      · rw [h3 _ (not_lt.1 ha), mul_zero]; exact A.zero_mem
    · rw [FlagD.z, h3 _ N.j_le, mul_zero]; exact A.zero_mem
    · rw [h4 _ ha, mul_zero]; exact A.zero_mem
  exact fun y hy => this hy
end GlobalTheory.DegCnt.PosJ
