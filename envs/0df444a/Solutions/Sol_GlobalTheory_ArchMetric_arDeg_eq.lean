-- Prove2me | solution 1 for GlobalTheory.ArchMetric.arDeg_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:19:40.550369+00:00
-- url     : https://prove2.me/submissions/b3b3b7bc-bd35-48a8-bf74-45194d6873a4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_MemSaturatedOrderIsoSubspaceSpanSymmApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FinrankMulDiscrRpowLeSumSqOfMemTraceDual
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsSmulMemOfMemSpanLattice
import Theorems.Thm_GlobalTheory_isLatticeFrame_iff_card_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Matrix
open scoped ComplexOrder ComplexConjugate
open GlobalTheory
open GlobalTheory.ArchMetric
variable {K : Type*} [Field K] [NumberField K] {V V' : Type*} [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V']
  [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V'] (h : ArchMetric K V)
variable {A : Submodule (𝓞 K) V} {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.ArchMetric
theorem _root_.solution (hA : A.FG) {e : ι → V} (mem : ∀ i, e i ∈ A) (he : LinearIndependent K e)
    (hc : Fintype.card ι = finrank (𝓞 K) A) :
    h.arDeg A = Real.log (Nat.card (A ⧸ (Submodule.span (𝓞 K) (Set.range e)).submoduleOf A)) -
      ∑ σ : K →+* ℂ, 1 / 2 * Real.log (h.gramDet σ e) :=
  h.arDeg_eq_frameDeg hA ((isLatticeFrame_iff_card_eq hA).2 ⟨mem, he, hc⟩)
end GlobalTheory.ArchMetric
