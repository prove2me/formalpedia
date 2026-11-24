-- Prove2me | solution 1 for GlobalTheory.eq_zero_of_mem_pow_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:38:10.223272+00:00
-- url     : https://prove2.me/submissions/19917000-eb48-4439-8605-417594847cbe

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SecEqZeroOfDvdPowUniformiser

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open TopologicalSpace
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    (U : X.Opens) (x : X) (hx : x ∈ U) (a b : Γ(X, U)) (ha : x ∉ X.basicOpen a)
    (hb : ∀ e : ℕ, b ∈ Ideal.span {a} ^ e) : b = 0 := by
  apply germ_injective_of_isIntegral X x hx
  rw [map_zero]
  rw [X.mem_basicOpen a x hx] at ha
  have hI : Ideal.span {(X.presheaf.germ U x hx).hom a} ≠ ⊤ := by
    rwa [Ne, Ideal.span_singleton_eq_top]
  have h := Ideal.iInf_pow_eq_bot_of_isLocalRing _ hI
  rw [← Ideal.mem_bot, ← h, Ideal.mem_iInf]
  intro e
  have := Ideal.mem_map_of_mem (X.presheaf.germ U x hx).hom (hb e)
  rwa [Ideal.map_pow, Ideal.map_span, Set.image_singleton] at this
end GlobalTheory
