-- Prove2me | solution 1 for GlobalTheory.UnRep.ReflGen.herm_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:45:06.250042+00:00
-- url     : https://prove2.me/submissions/0a098204-e6b2-44bc-8f92-afa181fb94c9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_UnitaryQuasiReflectionLawsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsAnisotropicOrthogonalBasisHermitianStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsQuasiReflectionProdMulVecEqStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_UnitaryMatrixEqProdQuasiReflections

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix
open GlobalTheory GlobalTheory.UnRep GlobalTheory.UnRep.ReflGen
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {c : E ≃ₐ[F] E} {n : ℕ} {G : Matrix (Fin n) (Fin n) E}
omit [NumberField F] [NumberField E]
namespace GlobalTheory.UnRep.ReflGen
theorem _root_.solution {v x z y : Fin n → E} (hx : hermE c G v x = 0) (hz : hermE c G v z = 0)
    (hy : y ∈ Submodule.span E {x, z}) : hermE c G v y = 0 := by
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.1 hy
  have : hermE c G v (a • x + b • z) = c a * hermE c G v x + c b * hermE c G v z := by
    simp only [hermE, Finset.mul_sum, ← Finset.sum_add_distrib, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, map_add, map_mul]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [this, hx, hz]
  simp
end GlobalTheory.UnRep.ReflGen
