-- Prove2me | solution 1 for GlobalTheory.CMTransference.majSq_intCast_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:27:21.944017+00:00
-- url     : https://prove2.me/submissions/db64c557-802e-4307-97a4-98fa62941961

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CoveringRadiusStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_Transference
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_BabaiCovering
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ConjugateConjugate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_CmApproximationTransference
import Theorems.Thm_GlobalTheory_CMTransference_norm_emb_sq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CMTransference
open NumberField Matrix Module Submodule ReciprocityTheory.MultiplicativeHeights ComplexConjugate
variable {K : Type} [Field K] [NumberField K] {r : ℕ} {ι : Type} [Fintype ι]
variable (p : ℕ) (σ : ι → K →+* ℂ) (Q : ι → Matrix (Fin r) (Fin r) ℂ)
namespace GlobalTheory.CMTransference
theorem _root_.solution (d : ℤ) (x : Fin r → K) :
    majSq σ Q ((d : K) • x) = (d : ℝ) ^ 2 * majSq σ Q x := by
  rw [← norm_emb_sq, ← norm_emb_sq, Int.cast_smul_eq_zsmul, map_zsmul,
    ← Int.cast_smul_eq_zsmul ℝ, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
end GlobalTheory.CMTransference
