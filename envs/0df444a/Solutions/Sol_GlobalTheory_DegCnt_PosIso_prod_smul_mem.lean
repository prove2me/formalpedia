-- Prove2me | solution 1 for GlobalTheory.DegCnt.PosIso.prod_smul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:07:44.970214+00:00
-- url     : https://prove2.me/submissions/5fa076ce-ce6c-41f8-bf4b-918ed4172629

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SameBlockAppend
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NormalFormIdealDivisibility
import Theorems.Thm_GlobalTheory_DegCnt_PosIso_det_smul_mem
import Theorems.Thm_GlobalTheory_DegCnt_PosIso_Xa_coords
import Theorems.Thm_GlobalTheory_DegCnt_PosIso_exists_tri
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_e_mem_X
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
variable {H : HermSpace K V} {r : ℕ}
omit [NumberField K]
namespace GlobalTheory.DegCnt.PosIso
theorem _root_.solution (F F' : FlagD H r) (Λ : Submodule (𝓞 K) V) (aa : Fin r → Submodule (𝓞 K) K)
    (hF : IsFrame F Λ aa) (hF' : IsFrame F' Λ aa)
    (hint : ∀ x ∈ Λ, ∀ y ∈ Λ, H.B x y ∈ (1 : Submodule (𝓞 K) K))
    {j : ℕ} (hj : j ≤ r) (s t : Fin j → K) (hs : ∀ a, s a ∈ aa (Fin.castLE hj a))
    (ht : ∀ a, t a ∈ aa (Fin.castLE hj a)) {ξ : V} (hξ : ξ ∈ F.Xa j)
    (hp : ∀ y ∈ Λ, y ∈ F'.X → H.B ξ y ∈ (1 : Submodule (𝓞 K) K)) :
    ((∏ a, s a) * Dl F F' j (hj.trans (Nat.le_succ r)) * star (∏ a, t a)) • ξ ∈ Λ := by
  obtain ⟨A, hA, hAΛ⟩ := exists_tri F Λ aa hF hj s hs
  obtain ⟨A', hA', hAΛ'⟩ := exists_tri F' Λ aa hF' hj t ht
  by_cases h0 : A.det = 0
  · rw [← hA, h0]; simp
  obtain ⟨q, -, rfl⟩ := Xa_coords F (hj.trans (Nat.le_succ r)) le_rfl hξ
  have hq : ∑ a, (Matrix.vecMul q A⁻¹) a • ∑ c, A a c • F.e (Fin.castLE (hj.trans (Nat.le_succ r)) c) =
      ∑ c, q c • F.e (Fin.castLE (hj.trans (Nat.le_succ r)) c) := by
    have : Matrix.vecMul (Matrix.vecMul q A⁻¹) A = q := by
      rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ (Ne.isUnit h0), Matrix.vecMul_one]
    conv_rhs => rw [← this]
    generalize Matrix.vecMul q A⁻¹ = p
    simp only [Finset.smul_sum, smul_smul, Matrix.vecMul, dotProduct, Finset.sum_smul]
    exact Finset.sum_comm
  have hX : ∀ b, ∑ c, A' b c • F'.e (Fin.castLE (hj.trans (Nat.le_succ r)) c) ∈ F'.X := fun b =>
    Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (e_mem_X F' (Fin.castLE hj c))
  have key := det_smul_mem H Λ _ _ hAΛ (fun a b => hint _ (hAΛ a) _ (hAΛ' b)) (Matrix.vecMul q A⁻¹)
    (fun b => by rw [hq]; exact hp _ (hAΛ' b) (hX b))
  rw [hq] at key
  convert key using 2
  rw [← hA, ← hA', ← Matrix.det_conjTranspose, Dl, ← Matrix.det_mul, ← Matrix.det_mul]
  congr 1
  ext a b
  simp only [Matrix.mul_apply, Matrix.of_apply, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.map_smulₛₗ, Matrix.submatrix_apply, Zhat, Matrix.conjTranspose_apply, smul_eq_mul, Finset.sum_mul,
    Finset.mul_sum, starRingEnd_apply]
  first
    | (refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => by ring)
    | (rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => by ring)
end GlobalTheory.DegCnt.PosIso
