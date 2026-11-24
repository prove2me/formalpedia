-- Prove2me | solution 1 for GlobalTheory.PeriodNonempty.exists_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T15:47:01.368948+00:00
-- url     : https://prove2.me/submissions/26bc3b19-38c7-4570-82d0-af924f201f0b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_IsLocallyConstantRankAtStalkEigenSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsEquivOfSumEq
import Theorems.Thm_GlobalTheory_PeriodNonempty_exists_equiv_of_sum_eq
import Theorems.Thm_GlobalTheory_EigenSplit_coe_eigenBaseChangeEquiv_tmul
import Theorems.Thm_GlobalTheory_EigenSplit_isSplitting_complex
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.EigenSplit.coe_eigenBaseChangeEquiv_tmul



set_option autoImplicit false
open NumberField Matrix
open scoped TensorProduct ComplexConjugate
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PeriodNonempty
noncomputable section
namespace GlobalTheory.PeriodNonempty
theorem _root_.solution {E : Type} [Field E] [NumberField E] {W : Type} [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ W] (ρ : 𝓞 E →+* Module.End ℂ W) {g : ℕ} (ty : Fin g → (E →+* ℂ))
    (h : ∀ a, LinearMap.trace ℂ W (ρ a) = ∑ i, ty i (a : E)) :
    ∃ e : W ≃ₗ[ℂ] (Fin g → ℂ), ∀ a v i, e (ρ a v) i = ty i (a : E) * e v i := by
  classical
  let S : Set W := {v | ∃ φ : E →+* ℂ, ∀ a : 𝓞 E, ρ a v = φ (a : E) • v}
  have hS : Submodule.span ℂ S = ⊤ := by
    rw [eq_top_iff]
    intro v _
    rw [← EigenSplit.sum_proj (EigenSplit.isSplitting_complex E) ρ v]
    refine Submodule.sum_mem _ fun φ _ => Submodule.subset_span ⟨φ, ?_⟩
    exact EigenSplit.mem_eigenSub.1 (EigenSplit.proj_mem (EigenSplit.isSplitting_complex E) ρ φ v)
  obtain ⟨T, hT, hspan, hli⟩ := exists_linearIndependent ℂ S
  let b : Module.Basis T ℂ W := Module.Basis.mk hli (by rw [Subtype.range_coe, hspan, hS])
  haveI : Finite T := Module.Finite.finite_basis b
  haveI : Fintype T := Fintype.ofFinite T
  choose s hs using fun v : T => hT v.2
  have hb : ∀ a v, ρ a (b v) = s v (a : E) • b v := fun a v => by
    simp only [b, Module.Basis.mk_apply]; exact hs v a
  obtain ⟨e, he⟩ := exists_equiv_of_sum_eq s ty (fun a => by
    rw [← h, LinearMap.trace_eq_matrix_trace ℂ b]
    simp [Matrix.trace, LinearMap.toMatrix_apply, hb])
  let c := b.reindex e
  have hc : ∀ a i, ρ a (c i) = ty i (a : E) • c i := fun a i => by
    simp only [c, Module.Basis.reindex_apply, hb, ← he, Equiv.apply_symm_apply]
  refine ⟨c.equivFun, fun a v i => ?_⟩
  conv_lhs => rw [← c.sum_equivFun v]
  simp only [map_sum, map_smul, hc, Finset.sum_apply, Pi.smul_apply, Module.Basis.equivFun_self, smul_eq_mul]
  simp [mul_comm]
end GlobalTheory.PeriodNonempty
