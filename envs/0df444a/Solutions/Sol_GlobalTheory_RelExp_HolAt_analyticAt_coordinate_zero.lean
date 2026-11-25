-- Prove2me | solution 1 for GlobalTheory.RelExp.HolAt.analyticAt_coordinate_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:56:39.209922+00:00
-- url     : https://prove2.me/submissions/dd2dc5f3-68e7-47a9-a8dd-0719626c7d2f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TangentBijectionOfValues
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_EventuallyEqOfAdditiveOfHasFDerivAt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_AnalyticAtCoordinateZero
import Theorems.Thm_GlobalTheory_RelExp_HolAt_one_of
import Theorems.Thm_GlobalTheory_RelExp_HolAt_analyticAt_pi


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.RelExp
variable {X : Scheme.{0}} {G : Over X}
variable [GrpObj G] {g m n : ℕ} {y : (Fin m → ℂ) → (Sp ℂ ⟶ X)} {b₀ : Fin m → ℂ} {U : G.left.Opens}
  {t : Fin g → Γ(G.left, U)} {f : Fin n → Γ(G.left, U)} {O : Set ((Fin m → ℂ) × (Fin n → ℂ))}
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] {β : E → (Fin m → ℂ)}
  {a : ∀ w, Over.mk (y (β w)) ⟶ G} {w₀ : E}
namespace GlobalTheory.RelExp
namespace HolAt
theorem _root_.solution (ha : HolAt (fun w => pt (a w)) w₀) (h1 : a w₀ = 1)
    (hU : ⊤ ≤ pt (1 : Over.mk (y (β w₀)) ⟶ G) ⁻¹ᵁ U) : AnalyticAt ℂ (fun w => crd0 t (a w)) w₀ :=
  (ha.analyticAt_pi (by rw [h1]; exact hU) t).sub (ha.one_of.analyticAt_pi hU t)
end HolAt
end GlobalTheory.RelExp
