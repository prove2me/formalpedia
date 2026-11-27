-- Prove2me | solution 1 for GlobalTheory.CubeReading.tripleColumnPeriodLattice_span_real_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:15:48.243995+00:00
-- url     : https://prove2.me/submissions/4ff4039b-e792-4494-b0a4-2ca682bee961

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ThConst
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_TripleProductTorusPeriodicBounded
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IsHolFamPullbackLiftOfCommonBase
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_AbelianHolomorphicFrameReadingConstOfFormsCancel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_CubicalReadingOneAnalyticFrame

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.CubeReading
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {L : RigLB A} {x0 : Sp ℂ ⟶ S} {g : ℕ}
  (Φ : AnFr A L x0 g)
omit [IsCommMonObj A]
namespace GlobalTheory.CubeReading
theorem _root_.solution : Submodule.span ℝ (lat3 Φ : Set (Fin (3 * g) → ℂ)) = ⊤ := by
  set e : (Fin (3 * g) → ℂ) ≃ₗ[ℝ] (Fin 3 → Fin g → ℂ) := (colsEquiv 3 g).restrictScalars ℝ with he
  have hmem : ∀ w, w ∈ lat3 Φ ↔ ∀ k, colsEquiv 3 g w k ∈ Φ.lat := by
    intro w
    show colsEquiv 3 g w ∈ AddSubgroup.pi Set.univ (fun _ : Fin 3 => Φ.lat) ↔ _
    simp [AddSubgroup.mem_pi]
  have key : ∀ (k : Fin 3) (y : Fin g → ℂ),
      e.symm (Pi.single k y) ∈ Submodule.span ℝ (lat3 Φ : Set (Fin (3 * g) → ℂ)) := by
    intro k y
    have hy : y ∈ Submodule.span ℝ (Φ.lat : Set (Fin g → ℂ)) := by rw [Φ.span]; trivial
    induction hy using Submodule.span_induction with
    | mem x hx =>
      apply Submodule.subset_span
      rw [SetLike.mem_coe, hmem]
      intro i
      have : colsEquiv 3 g (e.symm (Pi.single k x)) = Pi.single k x := e.apply_symm_apply _
      rw [this]
      by_cases hik : i = k
      · subst hik; simpa using hx
      · simp [hik, zero_mem]
    | zero => simp
    | add x y _ _ hx hy => simpa [Pi.single_add] using add_mem hx hy
    | smul r x _ hx => simpa [Pi.single_smul'] using Submodule.smul_mem _ r hx
  rw [eq_top_iff]
  rintro v -
  have hv : v = ∑ k : Fin 3, e.symm (Pi.single k (e v k)) := by
    rw [← map_sum, Finset.univ_sum_single, LinearEquiv.symm_apply_apply]
  rw [hv]
  exact Submodule.sum_mem _ fun k _ => key k _
end GlobalTheory.CubeReading
