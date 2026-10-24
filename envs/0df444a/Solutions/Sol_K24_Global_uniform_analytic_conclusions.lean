-- Prove2me | solution 1 for K24.Global.uniform_analytic_conclusions
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T19:06:42.917792+00:00
-- url     : https://prove2.me/submissions/5fbacca1-a534-4eb1-a8f8-3c96a06a1986
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_K24_Global_uniform_analytic_core
import Definitions.Def_K24AnalyticCore
import Theorems.Thm_K24_Global_section_neumann_transfer

set_option autoImplicit false
set_option maxSynthPendingDepth 8
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped NNReal ENNReal Manifold ContDiff Matrix.Norms.Elementwise

namespace K24.Global

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]

theorem HolderNaturalAnalyticCore.toConclusions
    {C : BoundedLocalCover M} {alpha H CT CV : ℝ≥0}
    {rho : CircleAction M} {lam : ℝ} {ghat z g : RawCov2 M}
    (h : HolderNaturalAnalyticCore C alpha H CT CV rho lam ghat z g) :
    HolderNaturalConclusions C alpha H CT CV rho lam ghat z g where
  projections := h.projections
  exact_identities := h.exact_identities
  bianchi_regularity := h.bianchi_regularity
  vector_regularity := h.vector_regularity
  defect_regularity := h.defect_regularity
  tensor_domain_banach := h.tensor_domain_banach
  tensor_target_banach := h.tensor_target_banach
  tensor_perp_domain_banach := h.tensor_perp_domain_banach
  tensor_perp_target_banach := h.tensor_perp_target_banach
  vector_domain_banach := h.vector_domain_banach
  vector_target_banach := h.vector_target_banach
  positive_neighborhood := h.positive_neighborhood
  fixed_frechet := h.fixed_frechet
  reanchored_frechet := h.reanchored_frechet
  tensor_estimate := h.tensor_estimate
  symbol_estimate := h.symbol_estimate
  vector_center_estimate := h.vector_center_estimate
  vector_actual_estimate := h.vector_actual_estimate
  center_comparison := h.center_comparison
  tensor_inverse_transfer := by
    intro CA _ hA hInv hsmall
    exact section_neumann_transfer h.tensor_perp_domain_banach
      h.tensor_perp_target_banach hA hInv h.tensor_operator.1
      h.tensor_operator.2.1 h.tensor_operator.2.2 hsmall
  vector_inverse_transfer := by
    intro CB _ hA hInv hsmall
    exact section_neumann_transfer h.vector_domain_banach
      h.vector_target_banach hA hInv h.vector_operator.1
      h.vector_operator.2.1 h.vector_operator.2.2 hsmall

theorem HolderShiftedAnalyticCore.toConclusions
    {C : BoundedLocalCover M} {alpha H CV : ℝ≥0}
    {rho : CircleAction M} {ghat z g : RawCov2 M}
    (h : HolderShiftedAnalyticCore C alpha H CV rho ghat z g) :
    HolderShiftedConclusions C alpha H CV rho ghat z g where
  projections := h.projections
  domain_banach := h.domain_banach
  target_banach := h.target_banach
  vector_regularity := h.vector_regularity
  center_estimate := h.center_estimate
  actual_estimate := h.actual_estimate
  inverse_transfer := by
    intro CB _ hA hInv hsmall
    exact section_neumann_transfer h.domain_banach
      h.target_banach hA hInv h.vector_operator.1
      h.vector_operator.2.1 h.vector_operator.2.2 hsmall

theorem SobolevAnalyticCore.toConclusions
    {C : BoundedLocalCover M} {P : SobolevPartition C} {s : ℝ} {H CS : ℝ≥0}
    {rho : CircleAction M} {lam : ℝ} {ghat z : RawCov2 M}
    (h : SobolevAnalyticCore P s H CS rho lam ghat z) :
    SobolevConclusions P s H CS rho lam ghat z where
  bianchi_regularity := h.bianchi_regularity
  defect_regularity := h.defect_regularity
  domain_banach := h.domain_banach
  target_banach := h.target_banach
  perp_domain_banach := h.perp_domain_banach
  perp_target_banach := h.perp_target_banach
  tensor_projection := h.tensor_projection
  covector_projection := h.covector_projection
  positive_neighborhood := h.positive_neighborhood
  fixed_frechet := h.fixed_frechet
  reanchored_frechet := h.reanchored_frechet
  cancellation := h.cancellation
  product_rule := h.product_rule
  dangerous_term_zero := h.dangerous_term_zero
  tensor_difference := h.tensor_difference
  tensor_estimate := h.tensor_estimate
  inverse_transfer := by
    intro CA _ hA hInv hsmall
    exact section_neumann_transfer h.perp_domain_banach
      h.perp_target_banach hA hInv h.tensor_operator.1
      h.tensor_operator.2.1 h.tensor_operator.2.2 hsmall

universe u

theorem UniformHolderNaturalAnalyticCore.toStatement
    (h : UniformHolderNaturalAnalyticCore.{u}) : UniformHolderNaturalStatement.{u} := by
  intro coverBounds metricBounds H hH
  obtain ⟨CT, CV, hCT, hCV, hcore⟩ := h coverBounds metricBounds H hH
  refine ⟨CT, CV, hCT, hCV, ?_⟩
  intro M _ _ _ _ _ C hC rho hrho lam ghat z g hghat hz hg hinvghat hinvz
  exact (hcore M C hC rho hrho lam ghat z g hghat hz hg hinvghat hinvz).toConclusions

theorem UniformHolderShiftedAnalyticCore.toStatement
    (h : UniformHolderShiftedAnalyticCore.{u}) : UniformHolderShiftedStatement.{u} := by
  intro coverBounds metricBounds horder H hH
  obtain ⟨CV, hCV, hcore⟩ := h coverBounds metricBounds horder H hH
  refine ⟨CV, hCV, ?_⟩
  intro M _ _ _ _ _ C hC rho hrho ghat z g hghat hz hg hinvghat hinvz
  exact (hcore M C hC rho hrho ghat z g hghat hz hg hinvghat hinvz).toConclusions

theorem UniformSobolevAnalyticCore.toStatement
    (h : UniformSobolevAnalyticCore.{u}) : UniformSobolevStatement.{u} := by
  intro coverBounds metricBounds s hs m hm Bcut Btransition H hH
  obtain ⟨CS, hCS, hcore⟩ := h coverBounds metricBounds s hs m hm Bcut Btransition H hH
  refine ⟨CS, hCS, ?_⟩
  intro M _ _ _ _ _ C hC P L hP hL htrans rho hrho lam ghat z hghat hz hPg hPz hinvg hinvz
  exact (hcore M C hC P L hP hL htrans rho hrho lam ghat z hghat hz hPg hPz hinvg hinvz).toConclusions

/-- A genuine reduction: all four inverse-transfer obligations are reconstructed
by the proved Neumann theorem on the exact section spaces. Every other original
analytic obligation and the literal torus sharpness child remain to be proved. -/
theorem analyticCore_reduction
    (hcore : AnalyticCoreStatement.{u}) (hsharp : FlatTorus.SharpnessStatement) :
    FullK24Statement.{u} := by
  exact ⟨hcore.1.toStatement, hcore.2.1.toStatement, hcore.2.2.toStatement, hsharp⟩

end K24.Global


universe uSolution

theorem solution :
    K24.Global.UniformHolderNaturalStatement.{uSolution} ∧
    K24.Global.UniformHolderShiftedStatement.{uSolution} ∧
    K24.Global.UniformSobolevStatement.{uSolution} := by
  have h := K24.Global.uniform_analytic_core.{uSolution}
  exact ⟨h.1.toStatement, h.2.1.toStatement, h.2.2.toStatement⟩

#print axioms solution
