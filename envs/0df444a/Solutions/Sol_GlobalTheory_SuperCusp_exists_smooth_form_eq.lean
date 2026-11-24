-- Prove2me | solution 1 for GlobalTheory.SuperCusp.exists_smooth_form_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:59:49.001875+00:00
-- url     : https://prove2.me/submissions/6450fd1c-18b3-479f-9030-5286c1479c73

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_CentralExponentBoundOver
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SubsingletonJacquetOfPerm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsInvariantForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsCuspidalOfIsSupercuspidal
import Theorems.Thm_GlobalTheory_SmGL_DualAverage_exists_invariant_form
import Theorems.Thm_GlobalTheory_SmGL_IwahoriOnto_exists_fixed_map_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix Topology Filter
noncomputable section
open GlobalTheory GlobalTheory.SuperCusp
namespace GlobalTheory.SuperCusp
theorem _root_.solution {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [AddCommGroup V] [Module ℂ V] {π : Representation ℂ G V} (hπ : IsSmooth π)
    {K N : Subgroup G} (ho : IsOpen (K : Set G)) (hc : IsCompact (K : Set G)) (a : G) (C : Set G)
    (hCK : ∀ c ∈ C, c ∈ K) (hfac : ∀ g ∈ K, ∃ x ∈ N, ∃ c ∈ C, g = x * c)
    (hcon : ∀ c ∈ C, a⁻¹ * c * a ∈ C) {u : V} (hu : ∀ g ∈ K, π g u = u) (l₀ : Module.Dual ℂ V)
    (hl : ∀ x ∈ N, ∀ v, l₀ (π x v) = l₀ v) :
    ∃ l ∈ smoothPart π.dual, ∀ r : ℕ, l (π (a ^ r) u) = l₀ (π (a ^ r) u) := by
  obtain ⟨l, hlK, hlf⟩ := DualAverage.exists_invariant_form G V π hπ K hc l₀
  refine ⟨l, ?_, fun r => ?_⟩
  · let S : Subgroup G :=
      { carrier := {g | π.dual g l = l}
        mul_mem' := by
          intro x y hx hy
          simp only [Set.mem_setOf_eq, map_mul, Module.End.mul_apply] at *
          rw [hy, hx]
        one_mem' := by
          show π.dual 1 l = l
          rw [map_one]; rfl
        inv_mem' := by
          intro x hx
          show π.dual x⁻¹ l = l
          have hx' : π.dual x l = l := hx
          conv_lhs => rw [← hx']
          rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl }
    have hKS : K ≤ S := by
      intro g hg
      show π.dual g l = l
      refine LinearMap.ext fun v => ?_
      rw [Representation.dual_apply]
      exact hlK _ (inv_mem hg) v
    exact Subgroup.isOpen_mono hKS ho
  · have hpow : ∀ c ∈ C, (a ^ r)⁻¹ * c * a ^ r ∈ C := by
      induction r with
      | zero => simp
      | succ r ih =>
        intro c hcC
        have := hcon _ (ih c hcC)
        convert this using 1
        rw [pow_succ]; group
    obtain ⟨v, hv, e⟩ := IwahoriOnto.exists_fixed_map_eq hπ hc (l.prod l₀) (π (a ^ r) u) fun g hg => by
      refine Prod.ext (hlK g hg _) ?_
      obtain ⟨x, hx, c, hcC, rfl⟩ := hfac g hg
      show l₀ _ = l₀ _
      rw [map_mul, Module.End.mul_apply, hl x hx]
      conv_rhs => rw [← hu _ (hCK _ (hpow c hcC))]
      rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
      congr 3
      group
    have e1 : l v = l (π (a ^ r) u) := congrArg Prod.fst e
    have e2 : l₀ v = l₀ (π (a ^ r) u) := congrArg Prod.snd e
    have hv' : ∀ h ∈ K, π h v = v := fun h hh => by simpa using hv ⟨h, hh⟩
    rw [← e1, ← e2, hlf v hv']
end GlobalTheory.SuperCusp
