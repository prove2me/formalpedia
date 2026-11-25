-- Prove2me | solution 1 for GlobalTheory.DegCnt.PosJ.exists_isom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:01:15.556677+00:00
-- url     : https://prove2.me/submissions/8ef7d7c8-c26a-435c-b241-7ce400d44c5a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LeadingMinorsProdDenominatorUnitriangularFactors
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFramesPairingStabilizerBlockDiagonal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NormalFormFlagLatticesNearUnderStabiliser
import Theorems.Thm_GlobalTheory_DegCnt_PosJ_B_vec
import Theorems.Thm_GlobalTheory_DegCnt_PosJ_B_symm0
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
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical nonZeroDivisors
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.PosJ
open GlobalTheory.HL Matrix
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] (H : HermSpace K V) {j : ℕ}
namespace GlobalTheory.DegCnt.PosJ
theorem _root_.solution [FiniteDimensional K V] (e d : Fin j → V) (M M' : Matrix (Fin j) (Fin j) K)
    (hee : ∀ a b, H.B (e a) (e b) = 0) (hdd : ∀ a b, H.B (d a) (d b) = 0)
    (hed : ∀ a b, H.B (e a) (d b) = if a = b then 1 else 0) (hM : Mᵀ * M'.map star = 1) :
    ∃ s : V ≃ₗ[K] V, (∀ x y, H.B (s x) (s y) = H.B x y) ∧
      ∀ y, s y = y + ∑ a, H.B y (d a) • (vec e M a - e a) + ∑ a, H.B y (e a) • (vec d M' a - d a) := by
  have hde : ∀ a b, H.B (d a) (e b) = if a = b then 1 else 0 := fun a b => by
    rw [← H.herm, hed]
    rcases eq_or_ne a b with h | h
    · simp [h]
    · simp [h, h.symm]
  let π : V → V := fun y => y - ∑ a, H.B y (d a) • e a - ∑ a, H.B y (e a) • d a
  have hπe : ∀ y b, H.B (π y) (e b) = 0 := fun y b => by
    simp [π, hee, hde]
  have hπd : ∀ y b, H.B (π y) (d b) = 0 := fun y b => by
    simp [π, hdd, hed]
  have key : ∀ M M' : Matrix (Fin j) (Fin j) K, Mᵀ * M'.map star = 1 → ∀ x y,
      H.B (π x + ∑ a, H.B x (d a) • vec e M a + ∑ a, H.B x (e a) • vec d M' a)
        (π y + ∑ a, H.B y (d a) • vec e M a + ∑ a, H.B y (e a) • vec d M' a) =
      H.B (π x) (π y) + ∑ a, H.B x (d a) * star (H.B y (e a)) + ∑ a, H.B x (e a) * star (H.B y (d a)) := by
    intro M M' hM x y
    have h1 : ∀ y b, H.B (π y) (vec e M b) = 0 := fun y b => by simp [vec, hπe]
    have h2 : ∀ y b, H.B (π y) (vec d M' b) = 0 := fun y b => by simp [vec, hπd]
    have h3 : ∀ a b, H.B (vec e M a) (vec e M b) = 0 := fun y b => by simp [vec, hee]
    have h4 : ∀ a b, H.B (vec d M' a) (vec d M' b) = 0 := fun y b => by simp [vec, hdd]
    have h5 : ∀ a b, H.B (vec e M a) (vec d M' b) = if a = b then 1 else 0 := fun a b => by
      have : (Matrix.of fun a b => H.B (e a) (d b)) = 1 := by
        ext a b; simp [hed, Matrix.one_apply]
      rw [B_vec, this, Matrix.mul_one, hM, Matrix.one_apply]
    have h6 : ∀ a b, H.B (vec d M' a) (vec e M b) = if a = b then 1 else 0 := fun a b => by
      rw [← H.herm, h5]
      rcases eq_or_ne a b with h | h
      · simp [h]
      · simp [h, h.symm]
    simp [h1, h2, h3, h4, h5, h6, fun y b => B_symm0 H (h1 y b), fun y b => B_symm0 H (h2 y b), mul_comm]
    rfl
  let g : V →ₗ[K] V := LinearMap.id + ∑ a, (H.B.flip (d a)).smulRight (vec e M a - e a) +
    ∑ a, (H.B.flip (e a)).smulRight (vec d M' a - d a)
  have hg : ∀ y, g y = y + ∑ a, H.B y (d a) • (vec e M a - e a) + ∑ a, H.B y (e a) • (vec d M' a - d a) :=
    fun y => by simp [g]
  have hiso : ∀ x y, H.B (g x) (g y) = H.B x y := by
    intro x y
    have h1 := key M M' hM x y
    have h2 := key 1 1 (by simp) x y
    have h3 : ∀ y, π y + ∑ a, H.B y (d a) • vec e M a + ∑ a, H.B y (e a) • vec d M' a = g y := fun y => by
      simp only [hg, π, smul_sub, Finset.sum_sub_distrib]; abel
    have h4 : ∀ y, π y + ∑ a, H.B y (d a) • vec e (1 : Matrix (Fin j) (Fin j) K) a +
        ∑ a, H.B y (e a) • vec d (1 : Matrix (Fin j) (Fin j) K) a = y := fun y => by
      simp only [π, vec, Matrix.one_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq',
        Finset.mem_univ, if_true]
      abel
    rw [h3, h3] at h1
    rw [h4, h4] at h2
    rw [h1, h2]
  have hinj : Function.Injective g := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    refine H.nondeg x fun y => ?_
    rw [← hiso, hx]; simp
  exact ⟨LinearEquiv.ofInjectiveEndo g hinj, hiso, hg⟩
end GlobalTheory.DegCnt.PosJ
