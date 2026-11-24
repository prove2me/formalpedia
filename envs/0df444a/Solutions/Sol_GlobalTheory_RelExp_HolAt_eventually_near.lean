-- Prove2me | solution 1 for GlobalTheory.RelExp.HolAt.eventually_near
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:54:36.920503+00:00
-- url     : https://prove2.me/submissions/e79fdc64-25a3-4d5b-bfe7-b7b11fdb2cef

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TangentBijectionOfValues
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_EventuallyEqOfAdditiveOfHasFDerivAt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_AnalyticAtCoordinateZero
import Theorems.Thm_GlobalTheory_RelExp_HolAt_analyticAt_pi
import Theorems.Thm_GlobalTheory_RelExp_HolAt_eventually
import Theorems.Thm_GlobalTheory_RelExp_HolAt_eventually_mem


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
theorem _root_.solution (ha : HolAt (fun w => pt (a w)) w₀) (hβ : ContinuousAt β w₀) (h1 : a w₀ = 1)
    (hOo : IsOpen O) (hU : ⊤ ≤ pt (1 : Over.mk (y (β w₀)) ⟶ G) ⁻¹ᵁ U)
    (hO : (β w₀, crd U f (pt (1 : Over.mk (y (β w₀)) ⟶ G))) ∈ O) :
    ∀ᶠ w in 𝓝 w₀, ⊤ ≤ pt (a w) ⁻¹ᵁ U ∧ (β w, crd U f (pt (a w))) ∈ O := by
  have hU' : ⊤ ≤ pt (a w₀) ⁻¹ᵁ U := by rw [h1]; exact hU
  refine (ha.eventually_mem hU').and ((hβ.prodMk (ha.analyticAt_pi hU' f).continuousAt).eventually
    (hOo.mem_nhds ?_))
  simpa only [h1] using hO
end HolAt
end GlobalTheory.RelExp
