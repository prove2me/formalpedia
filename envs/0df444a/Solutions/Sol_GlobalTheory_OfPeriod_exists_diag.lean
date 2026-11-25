-- Prove2me | solution 1 for GlobalTheory.OfPeriod.exists_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:07:05.442283+00:00
-- url     : https://prove2.me/submissions/8dbb2b30-3488-4e7a-8fb0-7ca01a8de2c0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_TorusProjPeriodZeroEqReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsEquivOfSumEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_FinrankHomComplex
import Theorems.Thm_GlobalTheory_OfPeriod_reForm_apply
import Theorems.Thm_GlobalTheory_EigenSplit_coe_eigenBaseChangeEquiv_tmul
import Theorems.Thm_GlobalTheory_EigenSplit_isSplitting_complex
import Theorems.Thm_GlobalTheory_PeriodNonempty_exists_diag
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.EigenSplit.coe_eigenBaseChangeEquiv_tmul


attribute [local simp] GlobalTheory.OfPeriod.reForm_apply

set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.OfPeriod
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (hermForm)
open Complex
variable {W : Type} [AddCommGroup W] [Module ℂ W] [Module ℝ W] [IsScalarTower ℝ ℂ W]
variable {S : W →ₗ[ℂ] W →ₗ⋆[ℂ] ℂ} {R : Submodule ℝ W}
open NumberField
namespace GlobalTheory.OfPeriod
theorem _root_.solution {E : Type} [Field E] [NumberField E] (U : Type) [AddCommGroup U] [Module ℂ U]
    [FiniteDimensional ℂ U] (σ : 𝓞 E →+* Module.End ℂ U) :
    ∃ (n : ℕ) (k : U ≃ₗ[ℂ] (Fin n → ℂ)) (F : 𝓞 E →+* Module.End ℂ (Fin n → ℂ)),
      (∃ ty : Fin n → (E →+* ℂ), ∀ a z i, F a z i = ty i (a : E) * z i) ∧ ∀ a u, k (σ a u) = F a (k u) := by
  classical
  let T₀ : Set U := {v | ∃ φ : E →+* ℂ, ∀ a : 𝓞 E, σ a v = φ (a : E) • v}
  have hS : Submodule.span ℂ T₀ = ⊤ := by
    rw [eq_top_iff]
    intro v _
    rw [← EigenSplit.sum_proj (EigenSplit.isSplitting_complex E) σ v]
    refine Submodule.sum_mem _ fun φ _ => Submodule.subset_span ⟨φ, ?_⟩
    exact EigenSplit.mem_eigenSub.1 (EigenSplit.proj_mem (EigenSplit.isSplitting_complex E) σ φ v)
  obtain ⟨T, hT, hspan, hli⟩ := exists_linearIndependent ℂ T₀
  let b : Module.Basis T ℂ U := Module.Basis.mk hli (by rw [Subtype.range_coe, hspan, hS])
  have : Finite T := Module.Finite.finite_basis b
  have : Fintype T := Fintype.ofFinite T
  choose s hs using fun v : T => hT v.2
  have hb : ∀ a v, σ a (b v) = s v (a : E) • b v := fun a v => by
    simp only [b, Module.Basis.mk_apply]; exact hs v a
  let e := Fintype.equivFin T
  obtain ⟨k, hk⟩ := PeriodNonempty.exists_diag σ (fun i => s (e.symm i)) fun a => by
    rw [LinearMap.trace_eq_matrix_trace ℂ b, e.symm.sum_comp fun v => s v (a : E)]
    simp [Matrix.trace, LinearMap.toMatrix_apply, hb]
  refine ⟨_, k, k.conjRingEquiv.toRingHom.comp σ, ⟨fun i => s (e.symm i), fun a z i => ?_⟩, fun a u => ?_⟩
  · obtain ⟨u, rfl⟩ := k.surjective z
    simpa using hk a u i
  · simp
end GlobalTheory.OfPeriod
