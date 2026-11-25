-- Prove2me | solution 1 for GlobalTheory.DegCnt.PosIso.exists_tri
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:30:46.971065+00:00
-- url     : https://prove2.me/submissions/7d7360e4-dc07-4178-88bf-04a878931307

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SameBlockAppend
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NormalFormIdealDivisibility
import Theorems.Thm_GlobalTheory_DegCnt_PosIso_Xa_coords
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
variable {H : HermSpace K V} {r : ℕ}
omit [NumberField K]
namespace GlobalTheory.DegCnt.PosIso
theorem _root_.solution (F : FlagD H r) (Λ : Submodule (𝓞 K) V) (aa : Fin r → Submodule (𝓞 K) K) (hF : IsFrame F Λ aa)
    {j : ℕ} (hj : j ≤ r) (s : Fin j → K) (hs : ∀ a, s a ∈ aa (Fin.castLE hj a)) :
    ∃ A : Matrix (Fin j) (Fin j) K, A.det = ∏ a, s a ∧
      ∀ a, ∑ c, A a c • F.e (Fin.castLE (hj.trans (Nat.le_succ r)) c) ∈ Λ := by
  have h : ∀ a : Fin j, ∃ p : Fin j → K, (∀ b : Fin j, a.val ≤ b.val → p b = 0) ∧
      s a • F.e (Fin.castLE (hj.trans (Nat.le_succ r)) a) -
        ∑ b, p b • F.e (Fin.castLE (hj.trans (Nat.le_succ r)) b) ∈ Λ := by
    intro a
    have h1 := hs a
    rw [← hF.1] at h1
    obtain ⟨l, hl, ξ, hξ, he⟩ := Submodule.mem_sup.1 h1
    obtain ⟨p, hp, rfl⟩ := Xa_coords F (hj.trans (Nat.le_succ r)) (n := a.val) a.isLt.le hξ
    refine ⟨p, hp, ?_⟩
    have he' : l + ∑ b, p b • F.e (Fin.castLE (hj.trans (Nat.le_succ r)) b) =
      s a • F.e (Fin.castLE (hj.trans (Nat.le_succ r)) a) := he
    rw [← he']; simpa using hl
  choose p hp hΛ using h
  refine ⟨Matrix.diagonal s - Matrix.of p, ?_, fun a => ?_⟩
  · rw [Matrix.det_of_lowerTriangular]
    · refine Finset.prod_congr rfl fun a _ => ?_
      simp [hp a a le_rfl]
    · intro a b hab
      have hab' : a < b := hab
      simp [Matrix.diagonal_apply_ne _ hab'.ne, hp a b hab'.le]
  · convert hΛ a using 1
    simp [sub_smul, Finset.sum_sub_distrib, Matrix.diagonal_apply, ite_smul]
end GlobalTheory.DegCnt.PosIso
