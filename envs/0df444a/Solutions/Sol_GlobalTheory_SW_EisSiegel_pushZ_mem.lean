-- Prove2me | solution 1 for GlobalTheory.SW.EisSiegel.pushZ_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:41:42.077983+00:00
-- url     : https://prove2.me/submissions/8e86c895-1ee0-46f0-859a-f672d0a39b7c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_NormDetDenomLeRankOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_EisAutomorphyLinear
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionSiegelParabolicExplicitStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_EmbeddingCompatibleWithWeilAndDenominatorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SiegelOperatorHermitianEisensteinSeries
import Theorems.Thm_GlobalTheory_IsSiegel_smul
import Theorems.Thm_GlobalTheory_SW_imH_add_I_smul


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
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.EisSiegel
variable {N : ℕ}
variable {E : Type} [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)) {n : ℕ}
omit [NumberField E] [IsCMField E]
namespace GlobalTheory.SW.EisSiegel
theorem _root_.solution {Z : CM Ψ N N} (hZ : Z ∈ Hn Ψ N) (v : Fin N → E) {t : ℝ} (ht : 0 ≤ t) :
    pushZ Ψ Z v t ∈ Hn Ψ N := by
  intro τ
  have hP : ((t : ℂ) • vecMulVec (fun a => τ.1 (v a)) (star fun a => τ.1 (v a))).PosSemidef :=
    (posSemidef_vecMulVec_self_star _).smul (by exact_mod_cast ht)
  have := imH_add_I_smul (Z τ) _ hP.1
  rw [smul_smul] at this
  exact this ▸ (hZ τ).add_posSemidef hP
end GlobalTheory.SW.EisSiegel
