-- Prove2me | solution 1 for GlobalTheory.CentralExponent.exists_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:43:09.602703+00:00
-- url     : https://prove2.me/submissions/c5048030-98c1-48d8-9148-dde1dd6a895a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_IrreducibleTensorCharacter
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_HasFiniteLengthOfIsIrreducible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwahoriProjSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ValuationDetOfMemKO
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_CentralExponentBoundOver
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_trans
import Theorems.Thm_GlobalTheory_SmGL_IwahoriOnto_exists_fixed_map_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.StepData ValuativeRel Matrix Topology Filter
open scoped TensorProduct
open GlobalTheory GlobalTheory.CentralExponent
variable {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]
namespace GlobalTheory.CentralExponent
theorem _root_.solution {π : Representation ℂ G V} (hπ : IsAdmissible π) (hU : IsUnitarisable π)
    {K N : Subgroup G} (ho : IsOpen (K : Set G)) (hc : IsCompact (K : Set G)) (a : G) (C : Set G)
    (hCK : ∀ c ∈ C, c ∈ K) (hfac : ∀ g ∈ K, ∃ x ∈ N, ∃ c ∈ C, g = x * c)
    (hcon : ∀ c ∈ C, a⁻¹ * c * a ∈ C) {u : V} (hu : ∀ g ∈ K, π g u = u) (l : V →ₗ[ℂ] ℂ)
    (hl : ∀ x ∈ N, ∀ v, l (π x v) = l v) : ∃ M : ℝ, ∀ r : ℕ, ‖l (π (a ^ r) u)‖ ≤ M := by
  obtain ⟨B, hB, hp, hi⟩ := hU
  let core : InnerProductSpace.Core ℂ V :=
    { inner := fun x y => B y x
      conj_inner_symm := fun x y => (hB x y).symm
      re_inner_nonneg := fun x => by
        by_cases h : x = 0
        · simp [h]
        · exact (hp x h).le
      add_left := fun x y z => by simp
      smul_left := fun x y r => by simp
      definite := fun x hx => by
        by_contra h
        have := hp x h
        have hx' : B x x = 0 := hx
        simp [hx'] at this }
  letI : NormedAddCommGroup V := core.toNormedAddCommGroup
  letI : InnerProductSpace ℂ V := InnerProductSpace.ofCore _
  have hin : ∀ x y : V, inner ℂ x y = B y x := fun _ _ => rfl
  have hn : ∀ g v, ‖π g v‖ = ‖v‖ := fun g v => by
    rw [@norm_eq_sqrt_re_inner ℂ, @norm_eq_sqrt_re_inner ℂ, hin, hin, hi]
  haveI := hπ.2 K ho hc
  let L : fixed π K →L[ℂ] ℂ := LinearMap.toContinuousLinearMap (l ∘ₗ (fixed π K).subtype)
  refine ⟨‖L‖ * ‖u‖, fun r => ?_⟩
  have hpow : ∀ c ∈ C, (a ^ r)⁻¹ * c * a ^ r ∈ C := by
    induction r with
    | zero => simp
    | succ r ih =>
      intro c hcC
      have := hcon _ (ih c hcC)
      convert this using 1
      rw [pow_succ]; group
  let f : V →ₗ[ℂ] ℂ × (fixed π K → ℂ) := l.prod (LinearMap.pi fun z => B.flip z.1)
  obtain ⟨v, hv, e⟩ := IwahoriOnto.exists_fixed_map_eq hπ.1 hc f (π (a ^ r) u) fun g hg => by
    refine Prod.ext ?_ (funext fun z => ?_)
    · obtain ⟨x, hx, c, hcC, rfl⟩ := hfac g hg
      show l _ = l _
      rw [map_mul, Module.End.mul_apply, hl x hx]
      conv_rhs => rw [← hu _ (hCK _ (hpow c hcC))]
      rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
      congr 3
      group
    · show B _ z.1 = B _ z.1
      have hz : π g z.1 = z.1 := by simpa using z.2 ⟨g, hg⟩
      conv_lhs => rw [← hz, hi]
  have e1 : l v = l (π (a ^ r) u) := congrArg Prod.fst e
  have e2 : B v v = B (π (a ^ r) u) v := congrFun (congrArg Prod.snd e) ⟨v, hv⟩
  have hv' : ‖v‖ ≤ ‖u‖ := by
    have h1 : ‖v‖ * ‖v‖ ≤ ‖v‖ * ‖u‖ := by
      rw [← inner_self_eq_norm_mul_norm (𝕜 := ℂ), hin, e2, ← hin, ← hn (a ^ r) u]
      exact re_inner_le_norm _ _
    by_cases h : v = 0
    · simp [h]
    · exact le_of_mul_le_mul_left h1 (norm_pos_iff.2 h)
  rw [← e1]
  exact (L.le_opNorm ⟨v, hv⟩).trans (mul_le_mul_of_nonneg_left hv' (norm_nonneg _))
end GlobalTheory.CentralExponent
