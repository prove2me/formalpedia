-- Prove2me | solution 1 for GlobalTheory.LabelsAgree.eq_of_qEq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:08:34.912852+00:00
-- url     : https://prove2.me/submissions/5d7085b2-208d-4cd4-825d-15e777562371

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_NotAllMatchRankZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationWeilPairingPropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ThetaConstantTermRepresentativeDependence
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_NormRepGeneratorsAndThetaSeriesTermStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationDataTorsionStructureAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_HomTransportStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SymmPairingEqOneOfOddOfDiag
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsBasisUniqueMinPairSums
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FourierExtractionTsumClass
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ThetaRecognitionLabelsAgreeOfIso
import Theorems.Thm_GlobalTheory_TorsionFourier_add_nsmul_injective
import Theorems.Thm_GlobalTheory_realExtBilin_tmul
import Theorems.Thm_GlobalTheory_realExt_tmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.realExtBilin_tmul
attribute [local simp] GlobalTheory.realExt_tmul



set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators
open GlobalTheory GlobalTheory.LabelsAgree
variable {O : Type} [CommRing O] {N N' : NumD O} (J : NumD.Iso N N')
namespace GlobalTheory.LabelsAgree
theorem _root_.solution {k : ℕ} (hk : k ≠ 0) {p q : N.QT k} (h : N.QEq p q) (hy : p.1.1 = q.1.1) : p = q := by
  obtain ⟨z, h1, h2⟩ := h
  have hz : k • z = 0 := by rw [hy] at h1; exact left_eq_add.1 h1
  have hz0 : z = 0 := by
    have := TorsionFourier.add_nsmul_injective (Nat.pos_of_ne_zero hk) (0 : N.X) (a₁ := z) (a₂ := 0)
      (by simp [hz])
    exact this
  rw [hz0, N.io_zero, mul_one] at h2
  exact Subtype.ext (Prod.ext hy h2.symm)
end GlobalTheory.LabelsAgree
