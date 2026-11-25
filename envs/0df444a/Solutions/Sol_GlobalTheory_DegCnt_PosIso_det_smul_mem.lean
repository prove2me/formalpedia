-- Prove2me | solution 1 for GlobalTheory.DegCnt.PosIso.det_smul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:39:47.282309+00:00
-- url     : https://prove2.me/submissions/f806ce04-e084-429a-955b-c6ca6ab7ce66

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SameBlockAppend
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NormalFormIdealDivisibility
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
noncomputable section
open NumberField Formalism.HermitianLatticeCounting.P Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical nonZeroDivisors
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.PosIso
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
omit [NumberField K]
namespace GlobalTheory.DegCnt.PosIso
theorem _root_.solution (H : HermSpace K V) (Λ : Submodule (𝓞 K) V) {j : ℕ} (x x' : Fin j → V)
    (hx : ∀ a, x a ∈ Λ) (hG : ∀ a b, H.B (x a) (x' b) ∈ (1 : Submodule (𝓞 K) K)) (p : Fin j → K)
    (hp : ∀ b, H.B (∑ a, p a • x a) (x' b) ∈ (1 : Submodule (𝓞 K) K)) :
    (Matrix.of fun a b => H.B (x a) (x' b)).det • (∑ a, p a • x a) ∈ Λ := by
  choose G0 hG0 using fun a b => Submodule.mem_one.1 (hG a b)
  choose η hη using fun b => Submodule.mem_one.1 (hp b)
  set G : Matrix (Fin j) (Fin j) K := Matrix.of fun a b => H.B (x a) (x' b) with hGdef
  have hGm : G = (algebraMap (𝓞 K) K).mapMatrix (Matrix.of G0) := by
    ext a b; simp [hGdef, ← hG0]
  have h1 : Matrix.vecMul p G = fun b => algebraMap (𝓞 K) K (η b) := by
    funext b
    rw [hη]
    simp [Matrix.vecMul, dotProduct, hGdef, map_sum]
  have h2 : G.det • p = Matrix.vecMul (Matrix.vecMul p G) G.adjugate := by
    rw [Matrix.vecMul_vecMul, Matrix.mul_adjugate, Matrix.vecMul_smul, Matrix.vecMul_one]
  rw [Finset.smul_sum]
  refine Submodule.sum_mem _ fun a _ => ?_
  have h3 : G.det * p a = algebraMap (𝓞 K) K (∑ b, η b * (Matrix.of G0).adjugate b a) := by
    have := congrFun h2 a
    rw [Pi.smul_apply, smul_eq_mul] at this
    rw [this, h1, hGm, ← RingHom.map_adjugate]
    simp [Matrix.vecMul, dotProduct, map_sum]
  rw [smul_smul, h3, algebraMap_smul]
  exact Λ.smul_mem _ (hx a)
end GlobalTheory.DegCnt.PosIso
