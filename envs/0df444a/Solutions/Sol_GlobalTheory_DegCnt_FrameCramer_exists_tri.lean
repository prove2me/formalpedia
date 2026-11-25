-- Prove2me | solution 1 for GlobalTheory.DegCnt.FrameCramer.exists_tri
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:08:47.948525+00:00
-- url     : https://prove2.me/submissions/4107e697-782f-4924-bba9-7665a495f2a8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsLocalizedModuleSubtype
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemOfForall
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFlagPairingCramerOfLeadingCoeffs
import Theorems.Thm_GlobalTheory_DegCnt_FrameCramer_exists_coord
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
theorem _root_.solution (F : FlagD H r) (Λ : Submodule (𝓞 K) V) {l : ℕ} (hl : l ≤ r) (α : Fin l → K)
    (hα : ∀ a, α a ∈ lead F Λ (Fin.castLE hl a).castSucc) :
    ∃ A : Matrix (Fin l) (Fin l) K, A.det = ∏ a, α a ∧
      ∀ a, ∑ b, A a b • F.e (Fin.castLE (hl.trans (Nat.le_succ r)) b) ∈ Λ := by
  have h : ∀ a : Fin l, ∃ c : Fin l → K, (∀ b : Fin l, a.val ≤ b.val → c b = 0) ∧
      α a • F.e (Fin.castLE (hl.trans (Nat.le_succ r)) a) -
        ∑ b, c b • F.e (Fin.castLE (hl.trans (Nat.le_succ r)) b) ∈ Λ := by
    intro a
    obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.1 (hα a)
    obtain ⟨c, hc, rfl⟩ := exists_coord F hl (m := a.val) a.2.le hy
    refine ⟨c, hc, ?_⟩
    convert hx using 1
    rw [sub_eq_iff_eq_add]
    exact hxy.symm
  choose c hc hc' using h
  refine ⟨diagonal α - Matrix.of c, ?_, fun a => ?_⟩
  · rw [Matrix.det_of_lowerTriangular]
    · simp [hc]
    · intro a b hab
      have hab' : a < b := hab
      simp [hab'.ne, hc a b hab'.le]
  · convert hc' a using 1
    simp [sub_smul, Finset.sum_sub_distrib, diagonal_apply, ite_smul]
end GlobalTheory.DegCnt.FrameCramer
