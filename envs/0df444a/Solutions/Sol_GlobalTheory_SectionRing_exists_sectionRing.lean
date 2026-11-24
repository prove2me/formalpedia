-- Prove2me | solution 1 for GlobalTheory.SectionRing.exists_sectionRing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:56:07.825687+00:00
-- url     : https://prove2.me/submissions/e60f99ff-984c-458c-a341-8db75483e815

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MonomialMemReesAlgIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_ExistsSectionRing
import Theorems.Thm_GlobalTheory_SectionRing_mono_injective
import Theorems.Thm_GlobalTheory_SectionRing_isDomain
import Theorems.Thm_GlobalTheory_SectionRing_eq_zero_of_chart

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.SectionRing
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
namespace GlobalTheory.SectionRing
theorem _root_.solution :
    (∀ (K : Type) [Field K] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp K) (L : LB X), L.IsLB → ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (_ : Algebra K R) (𝒜 : ℕ → Submodule K R) (_ : GradedAlgebra 𝒜) (Φ : ∀ e : ℕ, (lbPow L e).Sec ≃ 𝒜 e), (∀ e (s s' s'' : (lbPow L e).Sec), (∀ j, s''.f j = s.f j + s'.f j) → Φ e s'' = Φ e s + Φ e s') ∧ (∀ e (a : K) (s s' : (lbPow L e).Sec), (∀ j, s'.f j = constFn p _ a * s.f j) → Φ e s' = a • Φ e s) ∧ (∀ e e' (s : (lbPow L e).Sec) (s' : (lbPow L e').Sec) (s'' : (lbPow L (e + e')).Sec), (∀ j, s''.f j = (show Γ(X, (lbPow L (e + e')).U j) from s.f j) * (show Γ(X, (lbPow L (e + e')).U j) from s'.f j)) → (Φ (e + e') s'' : R) = Φ e s * Φ e' s') ∧ ∀ (j : PUnit → L.ι), ∃ ρ : R →+* Γ(X, (lbPow L 0).U j), (∀ a : K, ρ (algebraMap K R a) = constFn p _ a) ∧ ∀ e (s : (lbPow L e).Sec), ρ (Φ e s) = s.f j) := by
  intro K _ X _ p L hL
  obtain ⟨x⟩ : Nonempty X := inferInstance
  have hx : x ∈ ⨆ i, L.U i := hL.cover ▸ trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
  haveI : Nonempty (chart L fun _ => i) := ⟨⟨x, Set.mem_iInter.2 fun _ => hi⟩⟩
  refine ⟨polyAlg (secs p L), inferInstance,
    isDomain (secs p L) (evalFam p L fun _ => i) (eq_zero_of_chart p L _), inferInstance,
    piece (secs p L), grading (secs p L),
    fun e => (secEquiv p L e).trans
      (LinearEquiv.ofInjective _ (mono_injective (secs p L) e)).toEquiv, ?_, ?_, ?_, ?_⟩
  · intro e s s' s'' h
    have h1 : secEquiv p L e s'' = secEquiv p L e s + secEquiv p L e s' :=
      Subtype.ext (funext h)
    exact (congrArg (LinearEquiv.ofInjective _ (mono_injective (secs p L) e)) h1).trans
      (map_add _ _ _)
  · intro e a s s' h
    have h1 : secEquiv p L e s' = a • secEquiv p L e s := Subtype.ext (funext h)
    exact (congrArg (LinearEquiv.ofInjective _ (mono_injective (secs p L) e)) h1).trans
      (map_smul _ _ _)
  · intro e e' s s' s'' h
    have h1 : (secEquiv p L (e + e') s'' : Fam p L) =
        (secEquiv p L e s : Fam p L) * (secEquiv p L e' s' : Fam p L) := funext h
    apply Subtype.ext
    change Polynomial.monomial (e + e') (secEquiv p L (e + e') s'' : Fam p L) =
      Polynomial.monomial e (secEquiv p L e s : Fam p L) *
        Polynomial.monomial e' (secEquiv p L e' s' : Fam p L)
    rw [h1, Polynomial.monomial_mul_monomial]
  · intro j
    refine ⟨(evalFam p L j).comp ((Polynomial.evalRingHom 1).comp
      (polyAlg (secs p L)).val.toRingHom), fun a => ?_, fun e s => ?_⟩
    · change evalFam p L j (Polynomial.eval 1 (Polynomial.C (algebraMap K (Fam p L) a))) = _
      rw [Polynomial.eval_C]
      rfl
    · change evalFam p L j
        (Polynomial.eval 1 (Polynomial.monomial e (secEquiv p L e s : Fam p L))) = _
      rw [Polynomial.eval_monomial, one_pow, _root_.mul_one]
      rfl
end GlobalTheory.SectionRing
