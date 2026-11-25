-- Prove2me | solution 1 for GlobalTheory.LogKS.mem_balanced_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:02:24.982309+00:00
-- url     : https://prove2.me/submissions/31ecd43e-cfdf-4ec5-8fcb-3953d7cd70d7

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsChartIff
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasArcDataIff
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_FinalTheorems
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__DenseInterior_23def473f6482931

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open scoped Matrix
open GlobalTheory GlobalTheory.LogKS
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.LogKS
theorem _root_.solution {O R : Type} [CommRing R] {n : ℕ} (bar : O → O) (χ : Fin n → O → R)
    (Θ : Matrix (Fin n) (Fin n) R) :
    Θ ∈ balanced bar (fun a => Matrix.diagonal fun i => χ i a) ↔
      Θᵀ = Θ ∧ ∀ a i k, (χ i a - χ k (bar a)) * Θ i k = 0 := by
  refine and_congr_right fun _ => forall_congr' fun a => ?_
  rw [Matrix.diagonal_transpose, ← Matrix.ext_iff]
  refine forall₂_congr fun i k => ?_
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal, sub_mul, sub_eq_zero, mul_comm (Θ i k)]
end GlobalTheory.LogKS
