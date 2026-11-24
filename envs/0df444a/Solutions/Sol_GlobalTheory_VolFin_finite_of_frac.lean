-- Prove2me | solution 1 for GlobalTheory.VolFin.finite_of_frac
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:11:50.891072+00:00
-- url     : https://prove2.me/submissions/1f3221f8-7ad2-476c-8c59-362a6f6f5107

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_TendstoOfSandwich
import Theorems.Thm_GlobalTheory_VolFin_mem_span_of_frac

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.VolFin
open Module Filter Topology
variable {K F F' : Type} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] {ι : Type}
variable [Algebra F F'] [IsScalarTower K F F'] [Module.Finite F F'] [Finite ι]
omit [IsScalarTower K F F'] [Module.Finite F F']
namespace GlobalTheory.VolFin
theorem _root_.solution (S : Subalgebra K F') (hS : ∀ t : F', ∃ a ∈ S, ∃ b ∈ S, b ≠ 0 ∧ t * b = a)
    {n : ℕ} (g : Fin n → F') (hg : ∀ t ∈ S, ∃ w : Fin n → F, t = ∑ l, w l • g l) :
    Module.Finite F F' := by
  have hle : Submodule.span F (S : Set F') ≤ Submodule.span F (Set.range g) := by
    rw [Submodule.span_le]
    intro t ht
    obtain ⟨w, rfl⟩ := hg t ht
    exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩)
  have hsub : ((Submonoid.closure (S : Set F') : Submonoid F') : Set F') ⊆
      (Submodule.span F (S : Set F') : Set F') := by
    intro x hx
    have hx' : x ∈ S.toSubmonoid :=
      (Submonoid.closure_le (S := S.toSubmonoid)).2 (fun y hy => hy) hx
    exact Submodule.subset_span hx'
  have : FiniteDimensional F (Submodule.span F (Set.range g)) :=
    FiniteDimensional.span_of_finite F (Set.finite_range g)
  have : FiniteDimensional F (Submodule.span F (S : Set F')) :=
    Submodule.finiteDimensional_of_le hle
  have halg : ∀ b ∈ S, IsAlgebraic F b := by
    intro b hb
    refine (IsIntegral.of_mem_of_fg (Algebra.adjoin F (S : Set F')) ?_ b
      (Algebra.subset_adjoin hb)).isAlgebraic
    rw [Algebra.adjoin_eq_span_of_subset F hsub]
    exact Module.Finite.iff_fg.1 inferInstance
  have htop : Submodule.span F (Set.range g) = ⊤ :=
    eq_top_iff.2 fun t _ => hle (mem_span_of_frac S hS halg t)
  exact Module.finite_def.2 (Submodule.fg_def.2 ⟨_, Set.finite_range g, htop⟩)
end GlobalTheory.VolFin
