-- Prove2me | solution 1 for GlobalTheory.SW.SiegelOp.pushZ_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:33:51.25595+00:00
-- url     : https://prove2.me/submissions/3cfc42b1-66f7-4744-b600-a246fb836d2b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianThetaSummableAndDeterminesTestFn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ThHSiegelOperator

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.SiegelOp
variable {E : Type} [Field E] [NumberField E] (Ψ : Finset (E →+* ℂ)) {n N : ℕ}
omit [NumberField E]
namespace GlobalTheory.SW.SiegelOp
theorem _root_.solution {Z : CM Ψ N N} (h : Z ∈ Hn Ψ N) (v : Fin N → E) {t : ℝ} (ht : 0 ≤ t) :
    pushZ Ψ Z v t ∈ Hn Ψ N := by
  intro τ
  have e : imH (pushZ Ψ Z v t τ) = imH (Z τ) +
      (t : ℂ) • vecMulVec (fun a => τ.1 (v a)) (star fun a => τ.1 (v a)) := by
    ext a b
    simp only [imH, pushZ, Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply,
      conjTranspose_apply, vecMulVec_apply, smul_eq_mul, star_add, star_mul', Pi.star_apply,
      RCLike.star_def, conj_I, conj_ofReal, conj_conj]
    field_simp
    ring
  rw [e]
  exact (h τ).add_posSemidef
    ((posSemidef_vecMulVec_self_star _).smul (Complex.zero_le_real.2 ht))
end GlobalTheory.SW.SiegelOp
