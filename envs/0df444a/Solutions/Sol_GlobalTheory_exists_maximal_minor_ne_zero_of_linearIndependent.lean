-- Prove2me | solution 1 for GlobalTheory.exists_maximal_minor_ne_zero_of_linearIndependent
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:53:32.795201+00:00
-- url     : https://prove2.me/submissions/55d70110-cd0e-4b55-8dba-18a34619a7d7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsMaximalMinorNeZeroOfLinearIndependent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix
open GlobalTheory
open NumberField MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution
    (K : Type) [Field K] (r : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (w : ι → Fin r → K)
    (hw : LinearIndependent K w) :
    ∃ e : ι → Fin r, Function.Injective e ∧ (Matrix.of fun k a => w a (e k)).det ≠ 0 := by
  classical
  set A : Matrix (Fin r) ι K := Matrix.of fun k a => w a k with hA
  have hcol : A.col = w := rfl
  have hrank : A.rank = Fintype.card ι := by
    rw [Matrix.rank_eq_finrank_span_cols, hcol, finrank_span_eq_card hw]
  have htop : Submodule.span K (Set.range A.row) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [← Matrix.rank_eq_finrank_span_row, hrank, Module.finrank_fintype_fun_eq_card]
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' K A.row
  haveI : Fintype κ := Fintype.ofInjective a ha
  let b := Module.Basis.mk hli (by rw [hspan, htop])
  have hcard : Fintype.card ι = Fintype.card κ := by
    rw [← Module.finrank_fintype_fun_eq_card (R := K), Module.finrank_eq_card_basis b]
  let f : ι ≃ κ := Fintype.equivOfCardEq hcard
  refine ⟨a ∘ f, ha.comp f.injective, ?_⟩
  have hrow : LinearIndependent K (Matrix.of fun k a' => w a' ((a ∘ f) k)).row :=
    hli.comp f f.injective
  exact ((Matrix.isUnit_iff_isUnit_det _).mp
    (Matrix.linearIndependent_rows_iff_isUnit.mp hrow)).ne_zero
end _root_.GlobalTheory
end GlobalTheory
