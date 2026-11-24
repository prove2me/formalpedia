-- Prove2me | solution 1 for GlobalTheory.FunObj.exists_isCompact_of_mul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:48:33.848553+00:00
-- url     : https://prove2.me/submissions/ec49222d-1b98-47c7-9b9b-279328671132

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FlatTensorVacuum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasCompactSupportFlatIntegrand
import Theorems.Thm_GlobalTheory_SplitFlip_mem_matLat_stdLat


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
noncomputable section
open GlobalTheory GlobalTheory.FunObj
open GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {G : Grid k}
namespace GlobalTheory.FunObj
theorem _root_.solution {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (A : GL m k) (B : GL n k) :
    ∃ K : Set (Matrix m n k), IsCompact K ∧ ∀ X, A.val * X * B.val ∈ matLat m (stdLat k n) → X ∈ K := by
  have hO : IsCompact (𝒪[k] : Set k) := isCompact_iff_compactSpace.2 (inferInstanceAs (CompactSpace 𝒪[k]))
  have hC : IsCompact (Set.univ.pi fun _ : m => Set.univ.pi fun _ : n => (𝒪[k] : Set k)) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hO
  have hc : Continuous fun M : Matrix m n k => (A⁻¹).val * M * (B⁻¹).val :=
    (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  refine ⟨_, hC.image hc, fun X hX => ⟨A.val * X * B.val, fun i _ j _ => mem_matLat_stdLat.1 hX i j, ?_⟩⟩
  show (A⁻¹).val * (A.val * X * B.val) * (B⁻¹).val = X
  rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one, ← Matrix.mul_assoc,
    Units.inv_mul, Matrix.one_mul]
end GlobalTheory.FunObj
