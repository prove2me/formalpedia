-- Prove2me | solution 1 for GlobalTheory.ZH.FibPre.pure_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:30:38.512616+00:00
-- url     : https://prove2.me/submissions/22874f8b-5201-4954-8b5e-d964e3b47e05

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PullChartIsLB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_EqOfWeightEq
import Theorems.Thm_GlobalTheory_ZH_weight_app
import Theorems.Thm_GlobalTheory_ZH_eq_of_weight_eq
import Theorems.Thm_GlobalTheory_ZH_FibPre_compat_iff

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
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
open GlobalTheory GlobalTheory.ZH
namespace GlobalTheory.ZH
namespace FibPre
theorem _root_.solution : (∀ (k : Type) [Field k] (Φ : FibPre k), (∀ t : Φ.N₀.Sec, ∃ φ : (Φ.H 1).Sec, Φ.Pure 0 φ ∧ ∀ l, Φ.wt φ 0 l = t.f l) ∧ ∀ φ : (Φ.H 1).Sec, Φ.Pure 0 φ → ∃ t : Φ.N₀.Sec, (∀ l, Φ.wt φ 0 l = t.f l) ∧ (∀ l, φ.f l = (Φ.D.q.left.app (Φ.N₀.U l)).hom (t.f l)) ∧ Out.nonzeroLocus φ = Φ.D.q.left ⁻¹ᵁ Out.nonzeroLocus t) := by
  intro k _ Φ
  refine ⟨fun t => ?_, fun φ hφ => ?_⟩
  · refine ⟨⟨fun l => (Φ.D.q.left.app (Φ.N₀.U l)).hom (t.f l),
      fun i j => (Φ.compat_iff t.f i j).2 (t.compat i j)⟩, ?_, fun l => ?_⟩
    · rintro α ⟨l, hl⟩
      by_contra hα
      exact hl ((weight_app Φ.D _ _ _ _ α (t.f l)).trans (Finsupp.single_eq_of_ne hα))
    · exact (weight_app Φ.D _ _ _ _ 0 (t.f l)).trans Finsupp.single_eq_same
  · have hf : ∀ l, φ.f l = (Φ.D.q.left.app (Φ.N₀.U l)).hom (Φ.wt φ 0 l) := fun l => by
      refine eq_of_weight_eq Φ.D (Φ.ch l) _ (Φ.aff l) (Φ.le l) fun χ => ?_
      rw [weight_app]
      by_cases hχ : χ = 0
      · subst hχ
        exact Finsupp.single_eq_same.symm
      · rw [Finsupp.single_eq_of_ne hχ]
        by_contra hne
        exact hχ (hφ ⟨l, hne⟩)
    refine ⟨⟨fun l => Φ.wt φ 0 l, fun i j => (Φ.compat_iff _ i j).1 ?_⟩, fun _ => rfl, hf, ?_⟩
    · have c := φ.compat i j
      rw [hf i, hf j] at c
      exact c
    · unfold Out.nonzeroLocus
      rw [Scheme.Hom.preimage_iSup]
      refine iSup_congr fun l => ?_
      rw [Scheme.preimage_basicOpen, hf]
      rfl
end FibPre
end GlobalTheory.ZH
