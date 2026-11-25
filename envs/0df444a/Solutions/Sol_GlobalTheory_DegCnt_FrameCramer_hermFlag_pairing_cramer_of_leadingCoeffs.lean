-- Prove2me | solution 1 for GlobalTheory.DegCnt.FrameCramer.hermFlag_pairing_cramer_of_leadingCoeffs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:26:17.297751+00:00
-- url     : https://prove2.me/submissions/e494a557-730b-4d94-8452-cb844d249332

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsLocalizedModuleSubtype
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemOfForall
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFlagPairingCramerOfLeadingCoeffs
import Theorems.Thm_GlobalTheory_DegCnt_FrameCramer_exists_coord
import Theorems.Thm_GlobalTheory_DegCnt_FrameCramer_e_mem
import Theorems.Thm_GlobalTheory_DegCnt_FrameCramer_exists_tri
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
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical
open Formalism.MainNotions.S.Loc
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.FrameCramer
open Matrix
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] {H : HermSpace K V} {r : ℕ}
variable [NumberField K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace GlobalTheory.DegCnt.FrameCramer
theorem _root_.solution (F F' : FlagD H r) (Λ : Submodule (𝓞 K) V)
    (hint : ∀ x ∈ Λ, ∀ y ∈ Λ, H.B x y ∈ (1 : Submodule (𝓞 K) K)) {l : ℕ} (hl : l ≤ r) (α β : Fin l → K)
    (hα : ∀ a, α a ∈ lead F Λ (Fin.castLE hl a).castSucc) (hβ : ∀ a, β a ∈ lead F' Λ (Fin.castLE hl a).castSucc) :
    (∏ a, α a) * (∏ a, star (β a)) * Dl F F' l (hl.trans (Nat.le_succ r)) ∈ (1 : Submodule (𝓞 K) K) ∧
    ∀ x ∈ F.Xa l, (∀ p ∈ Λ, p ∈ F'.Xa l → H.B x p ∈ (1 : Submodule (𝓞 K) K)) →
      ((∏ a, α a) * (∏ a, star (β a)) * Dl F F' l (hl.trans (Nat.le_succ r))) • x ∈ Λ := by
  obtain ⟨A, hA, hA'⟩ := exists_tri F Λ hl α hα
  obtain ⟨B, hB, hB'⟩ := exists_tri F' Λ hl β hβ
  set e : Fin l → V := fun b => F.e (Fin.castLE (hl.trans (Nat.le_succ r)) b) with he
  set e' : Fin l → V := fun b => F'.e (Fin.castLE (hl.trans (Nat.le_succ r)) b) with he'
  set Z : Matrix (Fin l) (Fin l) K := Matrix.of fun a b => H.B (e a) (e' b) with hZ
  have hD : Dl F F' l (hl.trans (Nat.le_succ r)) = Z.det := rfl
  have key : ∀ (ξ : Fin l → K) (b : Fin l), H.B (∑ a, ξ a • e a) (∑ c, B b c • e' c) = (ξ ᵥ* (Z * Bᴴ)) b := by
    intro ξ b
    simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, LinearMap.map_smulₛₗ, smul_eq_mul,
      vecMul, dotProduct, Matrix.mul_apply, hZ, Matrix.of_apply, conjTranspose_apply, starRingEnd_apply,
      Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have hQ : ∀ a b, ∃ q : 𝓞 K, algebraMap (𝓞 K) K q = (A * (Z * Bᴴ)) a b := by
    intro a b
    have := hint _ (hA' a) _ (hB' b)
    rw [key] at this
    exact Submodule.mem_one.1 this
  choose Q hQ using hQ
  have hQ' : (algebraMap (𝓞 K) K).mapMatrix (Matrix.of Q) = A * (Z * Bᴴ) := by
    ext a b; exact hQ a b
  have hdet : (∏ a, α a) * (∏ a, star (β a)) * Dl F F' l (hl.trans (Nat.le_succ r)) = (A * (Z * Bᴴ)).det := by
    rw [det_mul, det_mul, det_conjTranspose, hA, hB, hD, star_prod]; ring
  rw [hdet]
  refine ⟨Submodule.mem_one.2 ⟨(Matrix.of Q).det, by rw [RingHom.map_det, hQ']⟩, fun x hx hp => ?_⟩
  obtain ⟨ξ, -, rfl⟩ := exists_coord F hl le_rfl hx
  have hp' : ∀ b, ∃ q : 𝓞 K, algebraMap (𝓞 K) K q = (ξ ᵥ* (Z * Bᴴ)) b := by
    intro b
    have := hp _ (hB' b) (Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (e_mem F' hl c))
    rw [key] at this
    exact Submodule.mem_one.1 this
  choose p hp' using hp'
  have hu : ∀ a, algebraMap (𝓞 K) K ((p ᵥ* (Matrix.of Q).adjugate) a) =
      ((ξ ᵥ* (Z * Bᴴ)) ᵥ* (A * (Z * Bᴴ)).adjugate) a := by
    intro a
    rw [RingHom.map_vecMul, ← hQ', ← RingHom.map_adjugate]
    congr 1
    exact funext hp'
  have hv : ((ξ ᵥ* (Z * Bᴴ)) ᵥ* (A * (Z * Bᴴ)).adjugate) ᵥ* A = (A * (Z * Bᴴ)).det • ξ := by
    rw [adjugate_mul_distrib, vecMul_vecMul, vecMul_vecMul, Matrix.mul_assoc, Matrix.mul_assoc, adjugate_mul,
      ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_assoc (Z * Bᴴ), ← Matrix.mul_assoc (Z * Bᴴ), mul_adjugate,
      det_mul A]
    simp [vecMul_smul, smul_smul, mul_comm]
  have hs := Λ.sum_mem (t := Finset.univ) fun a _ => Λ.smul_mem ((p ᵥ* (Matrix.of Q).adjugate) a) (hA' a)
  convert hs using 1
  simp only [← algebraMap_smul K ((p ᵥ* (Matrix.of Q).adjugate) _), hu, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← Finset.sum_smul]
  congr 1
  exact (congrFun hv b).symm
end GlobalTheory.DegCnt.FrameCramer
