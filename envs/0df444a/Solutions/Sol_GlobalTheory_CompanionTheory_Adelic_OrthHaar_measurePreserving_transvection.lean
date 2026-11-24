-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Adelic.OrthHaar.measurePreserving_transvection
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:33:11.562819+00:00
-- url     : https://prove2.me/submissions/9c4be3e5-51a0-47d8-8b8f-c0ca58de0d87

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_MatrixInductionTransvectionDiagonalStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_MapMulVecEqOfTransposeMulMulEq
import Theorems.Thm_GlobalTheory_CompanionTheory_Adelic_OrthHaar_transvection_mulVec_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Adelic GlobalTheory.CompanionTheory.Adelic.OrthHaar
variable {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R]
  [LocallyCompactSpace R] [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R]
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.CompanionTheory.Adelic.OrthHaar
theorem _root_.solution (ν : Measure R) [ν.IsAddHaarMeasure] {i j : ι}
    (hij : i ≠ j) (c : R) :
    MeasurePreserving (fun x : ι → R => Matrix.transvection i j c *ᵥ x)
      (Measure.pi fun _ => ν) (Measure.pi fun _ => ν) := by
  let p : ι → Prop := fun k => k ≠ i
  let α : Type := { x // p x }
  let β : Type := { x // ¬p x }
  let g : (α → R) → (β → R) → β → R := fun a b => (fun _ => c * a ⟨j, hij.symm⟩) + b
  let F : (α → R) × (β → R) → (α → R) × (β → R) := fun q => (id q.1, g q.1 q.2)
  let e : (ι → R) ≃ᵐ (α → R) × (β → R) :=
    MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => R) p
  have key : (fun x : ι → R => Matrix.transvection i j c *ᵥ x) = e.symm ∘ F ∘ e := by
    ext f k
    rw [transvection_mulVec_apply]
    by_cases hk : k = i
    · subst hk
      simp [e, F, g, p, α, β, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, add_comm]
    · simp [e, F, g, p, α, β, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, hk]
  rw [key]
  have A : MeasurePreserving e (Measure.pi fun _ => ν) _ :=
    measurePreserving_piEquivPiSubtypeProd (fun _ => ν) p
  have B : MeasurePreserving F
      ((Measure.pi fun _ : α => ν).prod (Measure.pi fun _ : β => ν))
      ((Measure.pi fun _ : α => ν).prod (Measure.pi fun _ : β => ν)) := by
    have g_meas : Measurable (Function.uncurry g) := by
      have : Continuous (Function.uncurry g) := by
        unfold Function.uncurry
        simp only [g]
        fun_prop
      exact this.measurable
    exact (MeasurePreserving.id _).skew_product g_meas
      (Filter.Eventually.of_forall fun a => map_add_left_eq_self _ _)
  exact (A.symm e).comp (B.comp A)
end GlobalTheory.CompanionTheory.Adelic.OrthHaar
