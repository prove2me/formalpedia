-- Prove2me | solution 1 for GlobalTheory.FramePeriod.cmType
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:35:33.513574+00:00
-- url     : https://prove2.me/submissions/1fb50c3f-1289-48f6-9fb3-2a94e06794af

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ProdCastLESucc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusSplitting_EqTopOfForallEmbAllMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_HermFormConjDiag
import Theorems.Thm_GlobalTheory_CMLattice_embAll_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMLattice.embAll_apply



set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors ComplexConjugate
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.FramePeriod
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace GlobalTheory.FramePeriod
theorem _root_.solution (H : Host E) (Ψ : Finset (E →+* ℂ)) (hΨ : ∀ τ, τ ∈ Ψ ↔ τ (H.rt : E) = H.rt0)
    (τ : E →+* ℂ) : τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ := by
  rw [hΨ, hΨ, ComplexEmbedding.conjugate_coe_eq]
  set z := τ (H.rt : E) with hz
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have h1 : z ^ 2 = -(H.d : ℂ) := by
    have := congrArg (fun a : 𝓞 E => τ (a : E)) H.rt_sq
    simpa using this
  have hc : conj z = -z := by
    have h2 : (conj z) ^ 2 = z ^ 2 := by rw [← map_pow, h1]; simp
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 h2 with h | h
    · exfalso
      have h3 := Complex.conj_eq_iff_re.1 h
      rw [← h3] at h1
      have h4 : z.re ^ 2 = -(H.d : ℝ) := by exact_mod_cast h1
      nlinarith [sq_nonneg z.re]
    · exact h
  have hz0 : z ≠ 0 := by
    intro h
    rw [h] at h1
    have : (H.d : ℂ) = 0 := by simpa using h1
    exact hd.ne' (by exact_mod_cast this)
  rw [hc]
  constructor
  · intro h h'
    apply hz0
    linear_combination (h - h') / 2
  · intro h
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 (h1.trans H.sqrt_neg_disc_sq.symm) with h' | h'
    · exact h'
    · exact absurd (by rw [h', neg_neg]) h
end GlobalTheory.FramePeriod
