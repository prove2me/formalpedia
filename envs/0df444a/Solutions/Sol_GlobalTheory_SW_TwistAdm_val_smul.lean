-- Prove2me | solution 1 for GlobalTheory.SW.TwistAdm.val_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:14:23.79324+00:00
-- url     : https://prove2.me/submissions/466b8160-f876-4410-9172-0df141bcbbe0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_TwistAdmissible
import Theorems.Thm_GlobalTheory_SW_TwistAdm_int_smul_mem

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
open scoped ComplexConjugate ComplexOrder Real Classical
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.TwistAdm
variable {E : Type} [Field E] [NumberField E] {n N : ℕ}
variable [IsCMField E]
namespace GlobalTheory.SW.TwistAdm
theorem _root_.solution {M R : ℕ} {φ : Fam E n N} (hφ : admitted M R φ) {Λ : Lt E n} (hΛ : Λ ∈ Vset E n M)
    {x : Matrix (Fin n) (Fin N) E} {s : ℕ} (hs : s ≡ 1 [MOD R ^ 2])
    (hx : ColsIn Λ ((R : E) • x)) : φ Λ ((s : E) • x) = φ Λ x := by
  obtain ⟨k, hk⟩ := hs.symm.dvd
  have h1 : (s : E) = 1 + R * (k * R) := by
    have := congrArg (Int.cast : ℤ → E) hk
    push_cast at this
    linear_combination this
  have : (s : E) • x = x + (R : E) • ((k : E) • ((R : E) • x)) := by
    rw [h1, add_smul, one_smul, smul_smul, smul_smul, mul_assoc]
  rw [this]
  refine hφ.per Λ hΛ _ _ fun a => ?_
  exact int_smul_mem Λ k (hx a)
end GlobalTheory.SW.TwistAdm
