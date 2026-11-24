-- Prove2me | solution 1 for GlobalTheory.ZH.WtPart.supp_finite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:38:08.644818+00:00
-- url     : https://prove2.me/submissions/139c9624-e094-4b08-a517-9a07c3aef815

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PullChartIsLB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IsPartPartSec
import Theorems.Thm_GlobalTheory_ZH_WtPart_cf_finite
import Theorems.Thm_GlobalTheory_ZH_WtPart_part_eq_zero
import Theorems.Thm_GlobalTheory_ZH_WtPart_isPart_partSec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
noncomputable section
open GlobalTheory GlobalTheory.ZH GlobalTheory.ZH.WtPart
variable {k : Type} [Field k] (Φ : FibPre k) {d : ℕ}
namespace GlobalTheory.ZH.WtPart
theorem _root_.solution (φ : (Φ.H d).Sec) : (Φ.supp φ).Finite := by
  have := Φ.E.isAbelian.proper
  have : CompactSpace Φ.E.B.left := QuasiCompact.compactSpace_of_compactSpace Φ.E.B.hom
  obtain ⟨T, hT⟩ := isCompact_univ.elim_finite_subcover (fun l => (Φ.N₀.U l : Set Φ.E.B.left))
    (fun l => (Φ.N₀.U l).isOpen) (fun x _ => Set.mem_iUnion.2
      (TopologicalSpace.Opens.mem_iSup.1 (Φ.isLB.cover.ge (show x ∈ ⊤ from trivial))))
  refine (T.finite_toSet.biUnion fun l _ =>
    cf_finite (Φ.D.coord (Φ.ch l) (Φ.N₀.U l) (Φ.aff l) (Φ.le l)) (φ.f l)).subset ?_
  rintro α ⟨l', hl'⟩
  by_contra hn
  have h0 : ∀ l ∈ T, (partSec Φ φ α).f l = 0 := fun l hl => by
    have : cf (Φ.D.coord (Φ.ch l) (Φ.N₀.U l) (Φ.aff l) (Φ.le l)) α (φ.f l) = 0 := by
      by_contra h
      exact hn (Set.mem_biUnion hl h)
    exact part_eq_zero _ this
  have h1 : (partSec Φ φ α).f l' = 0 := by
    refine Φ.G.left.sheaf.eq_of_locally_eq' (fun l : T => (Φ.H d).U l' ⊓ (Φ.H d).U l.1) _
      (fun l => homOfLE inf_le_left) (fun x hx => ?_) _ _ fun l => ?_
    · obtain ⟨l, hl, hx'⟩ := Set.mem_iUnion₂.1 (hT (Set.mem_univ (Φ.D.q.left x)))
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨l, hl⟩, hx, hx'⟩
    · refine ((partSec Φ φ α).compat l' l.1).trans ?_
      rw [h0 l.1 l.2, map_zero, mul_zero]
      exact (map_zero (resG _ _)).symm
  apply hl'
  rw [← (isPart_partSec Φ φ α).2 l', FibPre.wt, h1]
  exact cf_zero (Φ.D.coord (Φ.ch l') (Φ.N₀.U l') (Φ.aff l') (Φ.le l')) α
end GlobalTheory.ZH.WtPart
