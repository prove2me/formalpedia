-- Prove2me | solution 1 for GlobalTheory.CMTransference.normSq_le_majSq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:03:54.175984+00:00
-- url     : https://prove2.me/submissions/1373a638-62d0-40ad-a253-9e9b2413d6eb

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CoveringRadiusStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_Transference
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_BabaiCovering
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ConjugateConjugate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_CmApproximationTransference

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
theorem _root_.solution (i : ι) (x : Fin r → K) :
    normSq (Q i *ᵥ embVec (σ i) x) ≤ majSq σ Q x :=
  Finset.single_le_sum (f := fun i => normSq (Q i *ᵥ embVec (σ i) x))
    (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ i)
end GlobalTheory.CMTransference
