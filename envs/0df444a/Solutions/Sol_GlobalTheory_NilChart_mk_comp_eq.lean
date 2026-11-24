-- Prove2me | solution 1 for GlobalTheory.NilChart.mk_comp_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:29:07.947906+00:00
-- url     : https://prove2.me/submissions/a785af86-db3b-477d-b3df-482ffe8313f0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ReductionSurjectiveOfIsNilpotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_JetPointAddSqZeroEqProdMulTangent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsUniqueCoord
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_jetAug_zR
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_jet_ext


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp epsR IsTangent IsLieComb IsLieBasis)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.NilChart
open SqZero
variable {R : Type} [CommRing R] {B : Type} [CommRing B] [Algebra R B]
namespace GlobalTheory.NilChart
theorem _root_.solution {κ : Type} {m : ℕ} {I : Ideal B} (ψ : JetR R κ m →ₐ[R] B) (h : ∀ j, ψ (zR m j) ∈ I) :
    (Ideal.Quotient.mkₐ R I).comp ψ = (Algebra.ofId R _).comp (jetAug R κ m) :=
  jet_ext fun j => by
    rw [AlgHom.comp_apply, AlgHom.comp_apply, jetAug_zR, map_zero]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (h j)
end GlobalTheory.NilChart
