-- Prove2me | solution 1 for GlobalTheory.AbLaw.exists_pow_mul_twCoord_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:39:16.585808+00:00
-- url     : https://prove2.me/submissions/17c6974e-ef5a-42c7-aabc-2cd8769907da

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsNhdsPowMulTwCoordEqZero
import Theorems.Thm_GlobalTheory_AbLaw_exists_nhds_pow_mul_twCoord_eq_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_rs_rs


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw
open GlobalTheory GlobalTheory.AbLaw
namespace GlobalTheory.AbLaw
theorem _root_.solution : ∀ (Y : Scheme.{0}) (H M : LB Y) (d : ℤ) (σ : LB.Sec (pw H d)) (V : Y.Opens) (t : ℤ), H.IsLB → M.IsLB → V = nonzeroLocus σ → CompactSpace Y → ∀ a : SecOn (tw M H t) ⊤, SecOn.restrict _ (le_top : V ≤ ⊤) a = 0 → ∃ k : ℕ, ∀ (p : M.ι) (l : H.ι), rs Y (inf_le_right.trans inf_le_right : ⊤ ⊓ (M.U p ⊓ H.U l) ≤ H.U l) (σ.f l) ^ k * SecOn.twCoord a p l = 0 := by
  rintro Y H M d σ V t hH hM rfl hY a ha
  choose W n hxW hn using exists_nhds_pow_mul_twCoord_eq_zero σ hH hM a ha
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun x : Y => (W x : Set Y))
    (fun x => (W x).2) fun x _ => Set.mem_iUnion.2 ⟨x, hxW x⟩
  refine ⟨s.sup n, fun p l => ?_⟩
  refine GlobalTheory.LB.fun_ext_of_cover (fun x : s => W x ⊓ (⊤ ⊓ (M.U p ⊓ H.U l)))
    (fun _ => inf_le_right) (fun y hy => ?_) fun x => ?_
  · obtain ⟨x, hx, hy'⟩ := Set.mem_iUnion₂.1 (hs (Set.mem_univ y))
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨x, hx⟩, hy', hy⟩
  · obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le' (Finset.le_sup (f := n) x.2)
    have e := hn x p l _ inf_le_left inf_le_right
    change rs Y _ _ = rs Y _ _
    rw [map_mul, map_pow, rs_rs (U := H.U l) _ _ (σ.f l), map_zero, hm,
      pow_add, _root_.mul_assoc, e, mul_zero]
end GlobalTheory.AbLaw
