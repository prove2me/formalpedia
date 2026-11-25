-- Prove2me | solution 1 for John.exists_gap_of_lt_one_on_compact
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:08:25.568085+00:00
-- url     : https://prove2.me/submissions/15f3fbba-8cbb-4861-8642-09b18c5e7abc

module
public import Definitions.Def_BasicResults_Determinant
public import Definitions.Def_BasicResults_CompactConvexHull
public import Definitions.Def_BasicResults_JohnIngredients
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Spectrum
public import Mathlib.Analysis.InnerProductSpace.Trace
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Analysis.Normed.Group.Quotient
public import Mathlib.Analysis.Normed.Module.DoubleDual
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Mathlib.Analysis.Seminorm
public import Mathlib.Topology.Order.Compact
public import Definitions.Def_BasicResults_John

set_option autoImplicit true
@[expose] public section
public section
universe u
open scoped InnerProductSpace ComplexConjugate
open RCLike (re)
open John
variable {𝕜 : Type u} [RCLike 𝕜] {k : ℕ}
namespace John
theorem _root_.solution {q : Seminorm 𝕜 (EuclideanSpace 𝕜 (Fin k))}
    (hqc : Continuous q) {C : Set (EuclideanSpace 𝕜 (Fin k))} (hC : IsCompact C)
    (hlt : ∀ u ∈ C, q u < 1) :
    ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧ ∀ u ∈ C, q u ≤ 1 - η := by
  rcases C.eq_empty_or_nonempty with hCe | hCne
  · exact ⟨1 / 2, by norm_num, by norm_num,
      fun u hu => absurd (hCe ▸ hu) (Set.notMem_empty u)⟩
  · obtain ⟨u₀, hu₀C, hu₀max⟩ := hC.exists_isMaxOn hCne hqc.continuousOn
    refine ⟨1 - q u₀, by linarith [hlt u₀ hu₀C], by linarith [apply_nonneg q u₀], ?_⟩
    intro u hu
    linarith [(isMaxOn_iff.mp hu₀max) u hu]
end John
