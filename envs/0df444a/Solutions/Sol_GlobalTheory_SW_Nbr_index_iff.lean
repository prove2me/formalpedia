-- Prove2me | solution 1 for GlobalTheory.SW.Nbr.index_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:55:42.974067+00:00
-- url     : https://prove2.me/submissions/9436a47f-1acd-40a1-96ac-b109f9caa24d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_CycOfPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_NeBotOfNorm
import Theorems.Thm_GlobalTheory_SW_Nbr_max_of_norm
import Theorems.Thm_GlobalTheory_SW_Hyper_cyc_of_prime
import Theorems.Thm_GlobalTheory_SW_Hyper_exists_fun
import Theorems.Thm_GlobalTheory_SW_Hyper_index_ker


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical nonZeroDivisors
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.Nbr
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}
omit [IsCMField E]
namespace GlobalTheory.SW.Nbr
theorem _root_.solution {q : ℕ} {P : Ideal (𝓞 E)} (hq : q.Prime) (hP : Ideal.absNorm P = q)
    {Λ : Lt E n} (N : Submodule (𝓞 E) Λ) :
    ((∀ c ∈ P, ∀ x, c • x ∈ N) ∧ N.toAddSubgroup.index = q) ↔
      ∃ f : Λ →ₗ[𝓞 E] 𝓞 E ⧸ P, f ≠ 0 ∧ LinearMap.ker f = N := by
  have := max_of_norm hq hP
  constructor
  · rintro ⟨h1, h2⟩
    obtain ⟨v, hv, hc⟩ := Hyper.cyc_of_prime N hq h2
    exact Hyper.exists_fun P N v hv (fun c hc => h1 c hc v) hc
  · rintro ⟨f, hf, rfl⟩
    refine ⟨fun c hc x => ?_, (Hyper.index_ker P f hf).trans hP⟩
    rw [LinearMap.mem_ker, map_smul, Algebra.smul_def]
    have : algebraMap (𝓞 E) (𝓞 E ⧸ P) c = 0 := Ideal.Quotient.eq_zero_iff_mem.2 hc
    rw [this, zero_mul]
end GlobalTheory.SW.Nbr
