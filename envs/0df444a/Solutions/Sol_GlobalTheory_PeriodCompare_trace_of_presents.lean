-- Prove2me | solution 1 for GlobalTheory.PeriodCompare.trace_of_presents
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:24:32.335309+00:00
-- url     : https://prove2.me/submissions/1dd81696-e2b9-4663-ba7e-aef9a34e83cf

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_PeriodMapPresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsEquivOfSumEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsIsDerivAt0NotIsDerivAlong
import Theorems.Thm_GlobalTheory_PeriodCompare_finiteDimensional
import Theorems.Thm_GlobalTheory_EigenSplit_coe_eigenBaseChangeEquiv_tmul
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_PeriodMapPresentation_IsPeriodMap_map_smul
import Theorems.Thm_GlobalTheory_PeriodNonempty_trace_real
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.EigenSplit.coe_eigenBaseChangeEquiv_tmul



set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.PeriodCompare
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding IsTypeFn IsThetaFrame
open GlobalTheory.IndefiniteRowSideFullHecke.PeriodMapPresentation hiding IsTypeFn IsThetaFrame
open scoped TensorProduct Topology
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
namespace GlobalTheory.PeriodCompare
theorem _root_.solution {D : Datum H} {g : ℕ} {ty : Fin g → (E →+* ℂ)} {P : D.La →+ (Fin g → ℂ)}
    {J : ℝ ⊗[ℤ] D.La →ₗ[ℝ] ℝ ⊗[ℤ] D.La} (h : Presents D ty P J) (a : 𝓞 E) :
    ((LinearMap.trace ℝ _ (actR D a) : ℝ) : ℂ) / 2 -
      Complex.I * ((LinearMap.trace ℝ _ (J ∘ₗ actR D a) : ℝ) : ℂ) / 2 = ∑ i, ty i (a : E) := by
  obtain ⟨_, _⟩ := finiteDimensional D
  obtain ⟨φ, -, h2, h3⟩ := h
  let f : Module.End ℂ (Fin g → ℂ) := Matrix.toLin' (Matrix.diagonal fun i => ty i (a : E))
  have hf : ∀ z, f z = tyAct ty a z := fun z => by
    funext i; simp [f, tyAct, Matrix.mulVec_diagonal]
  have ht : LinearMap.trace ℂ _ f = ∑ i, ty i (a : E) := by simp [f]
  have e1 : φ.conj (actR D a) = f.restrictScalars ℝ := by
    refine LinearMap.ext fun y => ?_
    rw [LinearEquiv.conj_apply_apply, h3, φ.apply_symm_apply]
    exact (hf y).symm
  have e2 : φ.conj (J ∘ₗ actR D a) = (Complex.I • f).restrictScalars ℝ := by
    refine LinearMap.ext fun y => ?_
    rw [LinearEquiv.conj_apply_apply, LinearMap.comp_apply, h2, h3, φ.apply_symm_apply, ← hf]
    rfl
  rw [← LinearMap.trace_conj' _ φ, ← LinearMap.trace_conj' (J ∘ₗ actR D a) φ, e1, e2, PeriodNonempty.trace_real,
    PeriodNonempty.trace_real, map_smul, ht]
  generalize ∑ i, ty i (a : E) = t
  apply Complex.ext
  · simp
  · simp; ring
end GlobalTheory.PeriodCompare
