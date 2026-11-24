-- Prove2me | solution 1 for GlobalTheory.UnRep.LatForm.congAtA_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:45:09.158216+00:00
-- url     : https://prove2.me/submissions/dc1f962a-0fd1-4596-ae4d-33021021b346

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUnitaryCorrectionCongruentOneAtLevelStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IdempotentAdelesAndSmallAdelicMatricesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_UnitaryGroupWeakApproximationAtPrimesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsRationalUnitarySplitDenominator

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnRep GlobalTheory.UnRep.LatForm
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix nonZeroDivisors
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}
namespace GlobalTheory.UnRep.LatForm
theorem _root_.solution (L : Submodule (𝓞 E) (Fin n → E)) (N D : ℕ) (a b : Matrix (Fin n) (Fin n) (RA F E))
    (ha : CongAtA F L N D a) (hb : CongAtA F L N D b) : CongAtA F L N D (a * b) := by
  obtain ⟨t, ht, ha⟩ := ha
  obtain ⟨u, hu, hb⟩ := hb
  refine ⟨t * u, Nat.Coprime.mul_left ht hu, fun z hz => ?_⟩
  obtain ⟨w, hw, e⟩ := hb z hz
  obtain ⟨w', hw', e'⟩ := ha (u • z + D • w)
    (AddSubgroup.add_mem _ (AddSubgroup.nsmul_mem _ hz _) (AddSubgroup.nsmul_mem _ hw _))
  refine ⟨w' + t • w, AddSubgroup.add_mem _ hw' (AddSubgroup.nsmul_mem _ hw _), ?_⟩
  have e1 : u • z + D • w = u • (b *ᵥ z) := by rw [← e, smul_sub]; abel
  rw [e1, Matrix.mulVec_smul, Matrix.mulVec_mulVec] at e'
  rw [smul_add, ← e', smul_comm D t, ← e, ← smul_add, mul_smul]
  congr 1
  rw [smul_sub, smul_sub]; abel
end GlobalTheory.UnRep.LatForm
