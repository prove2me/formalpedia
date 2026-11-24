-- Prove2me | solution 1 for GlobalTheory.ClassSumCompare.exists_tmul_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:49:15.539801+00:00
-- url     : https://prove2.me/submissions/3634046c-6e4b-4759-94be-74e75a2ad098

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_AdelicNormWeight
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FiniteAdeleStrongApproximationModNat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionFractionalIdealProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsNatMulInt
import Theorems.Thm_GlobalTheory_ClassSumCompare_exists_nat_mul_int
import Theorems.Thm_GlobalTheory_ClassSumCompare_diag_algebraMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ClassSumCompare
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField IsDedekindDomain GlobalTheory.IndefiniteRowSideFullHecke.AdelicNormWeight
open scoped TensorProduct nonZeroDivisors
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}
namespace GlobalTheory.ClassSumCompare
theorem _root_.solution (a : AdF E) (e : E) : ∃ (t : maximalRealSubfield E) (o : 𝓞 E),
    inclF E a * diagE E e = inclF E (algebraMap _ (AdF E) t * a) * diagE E (o : E) := by
  obtain ⟨k, hk, o, ho⟩ := exists_nat_mul_int e
  refine ⟨(k : maximalRealSubfield E)⁻¹, o, ?_⟩
  have hk' : (k : E) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
  rw [map_mul, ← diag_algebraMap, ho, mul_comm (diagE E _) (inclF E a), mul_assoc, ← map_mul]
  congr 2
  rw [map_inv₀, map_natCast]
  field_simp
end GlobalTheory.ClassSumCompare
