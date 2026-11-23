-- Prove2me | solution 1 for GlobalTheory.FibreLinInd.exists_fibrePower
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:16:04.587357+00:00
-- url     : https://prove2.me/submissions/92200962-c56b-4e24-b8b3-833e878bf04b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IsOpenSetOfLinearIndependentOnFibres

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory GlobalTheory.FibreLinInd
namespace GlobalTheory.FibreLinInd
theorem _root_.solution {G Z : Scheme.{0}} (f : G ⟶ Z) [UniversallyOpen f]
    [LocallyOfFiniteType f] (r : ℕ) :
    ∃ (P : Scheme.{0}) (p : P ⟶ Z) (π : Fin r → (P ⟶ G)), UniversallyOpen p ∧
      LocallyOfFiniteType p ∧ (∀ k, π k ≫ f = p) ∧
      ∀ (T : Scheme.{0}) (x : T ⟶ Z) (g : Fin r → (T ⟶ G)), (∀ k, g k ≫ f = x) →
        ∃ h : T ⟶ P, h ≫ p = x ∧ ∀ k, h ≫ π k = g k := by
  induction r with
  | zero =>
    exact ⟨Z, 𝟙 Z, Fin.elim0, inferInstance, inferInstance, fun k => k.elim0,
      fun T x g _ => ⟨x, by simp, fun k => k.elim0⟩⟩
  | succ r ih =>
    obtain ⟨P, p, π, h1, h2, h3, h4⟩ := ih
    refine ⟨pullback f p, pullback.snd f p ≫ p,
      Fin.cons (pullback.fst f p) (fun k => pullback.snd f p ≫ π k), inferInstance, inferInstance,
      ?_, ?_⟩
    · refine Fin.cases ?_ fun k => ?_
      · simpa using pullback.condition
      · simp [h3]
    · intro T x g hg
      obtain ⟨h, hp, hπ⟩ := h4 T x (fun k => g k.succ) fun k => hg _
      refine ⟨pullback.lift (g 0) h (by rw [hg, hp]), by rw [pullback.lift_snd_assoc, hp], ?_⟩
      refine Fin.cases ?_ fun k => ?_
      · simp [pullback.lift_fst]
      · simp [pullback.lift_snd_assoc, hπ]
end GlobalTheory.FibreLinInd
