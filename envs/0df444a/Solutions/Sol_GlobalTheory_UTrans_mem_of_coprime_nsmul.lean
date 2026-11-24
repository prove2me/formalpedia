-- Prove2me | solution 1 for GlobalTheory.UTrans.mem_of_coprime_nsmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:43:43.46234+00:00
-- url     : https://prove2.me/submissions/a1169da3-6cb7-48bc-9a29-84147aec1e67

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermHyperbolic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_UnitaryTransvectionSubmonoidAdjustIntegralAway
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_UnitaryEqQuasiReflectionMulTransvections
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_UnitaryTransvectionSubmonoidNormalDetOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_TransvectionIdentitiesUnitary
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsUnitaryConjSplitLatticeOfLocal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open GlobalTheory GlobalTheory.UTrans
namespace GlobalTheory.UTrans
theorem _root_.solution {V : Type} [AddCommGroup V] (L : AddSubgroup V) {K M : ℕ} (h : K.Coprime M) {v : V}
    (h1 : K • v ∈ L) (h2 : M • v ∈ L) : v ∈ L := by
  obtain ⟨a, c, hac⟩ := Nat.isCoprime_iff_coprime.2 h
  have : v = a • K • v + c • M • v := by
    rw [← natCast_zsmul, ← natCast_zsmul, smul_smul, smul_smul, ← add_smul, hac, one_smul]
  rw [this]
  exact add_mem (zsmul_mem h1 _) (zsmul_mem h2 _)
end GlobalTheory.UTrans
