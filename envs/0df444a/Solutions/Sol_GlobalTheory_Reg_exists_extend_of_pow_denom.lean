-- Prove2me | solution 1 for GlobalTheory.Reg.exists_extend_of_pow_denom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:55:18.415565+00:00
-- url     : https://prove2.me/submissions/967a7bbb-b152-424e-863f-ced1a2b452a6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_RegularCharts_ModelAt
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_FrameCharts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_ExistsExtendOfPowDenom

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg
open GlobalTheory GlobalTheory.Reg
namespace GlobalTheory.Reg
theorem _root_.solution {R A L : Type} [CommRing R] [CommRing A] [IsDomain A] [Field L]
    (β : R →+* FractionRing A) (d : A)
    (h : ∀ r, ∃ (x : A) (t : ℕ), β r * algebraMap A _ (d ^ t) = algebraMap A _ x)
    (φ : A →+* L) (hd : φ d ≠ 0) :
    ∃ ψ : R →+* L, ∀ (r : R) (x s : A),
      β r * algebraMap A _ s = algebraMap A _ x → ψ r * φ s = φ x := by
  choose X T hXT using h
  have hp : ∀ t : ℕ, φ (d ^ t) ≠ 0 := fun t => by rw [map_pow]; exact pow_ne_zero _ hd
  have key : ∀ (r : R) (x s : A), β r * algebraMap A _ s = algebraMap A _ x →
      φ (X r) / φ (d ^ T r) * φ s = φ x := by
    intro r x s hx
    have h1 : X r * s = x * d ^ T r := by
      apply IsFractionRing.injective A (FractionRing A)
      rw [map_mul, map_mul, ← hXT r, ← hx]; ring
    have h2 := congrArg φ h1
    rw [map_mul, map_mul] at h2
    rw [div_mul_eq_mul_div, h2, mul_div_assoc, div_self (hp _), _root_.mul_one]
  refine ⟨{ toFun := fun r => φ (X r) / φ (d ^ T r), map_one' := ?_, map_mul' := ?_,
            map_zero' := ?_, map_add' := ?_ }, key⟩
  · have := key 1 1 1 (by simp)
    simpa using this
  · intro r s
    have := key (r * s) (X r * X s) (d ^ T r * d ^ T s) (by
      rw [map_mul, map_mul, map_mul, ← hXT r, ← hXT s]; ring)
    rw [map_mul, map_mul] at this
    rw [div_mul_div_comm, eq_div_iff (mul_ne_zero (hp _) (hp _))]
    exact this
  · have := key 0 0 1 (by simp)
    simpa using this
  · intro r s
    have := key (r + s) (X r * d ^ T s + d ^ T r * X s) (d ^ T r * d ^ T s) (by
      rw [map_add, map_add, map_mul, map_mul, map_mul, ← hXT r, ← hXT s]; ring)
    rw [map_add, map_mul, map_mul, map_mul] at this
    rw [div_add_div _ _ (hp _) (hp _), eq_div_iff (mul_ne_zero (hp _) (hp _))]
    exact this
end GlobalTheory.Reg
