-- Prove2me | solution 1 for GlobalTheory.LatDen.latDen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:14:40.795837+00:00
-- url     : https://prove2.me/submissions/7f665ed9-2f28-4dbe-b319-6f0bb3f4c3f1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsIntMulIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_LatDen
import Theorems.Thm_GlobalTheory_IntegralMultiples_exists_int_smul_mem
import Theorems.Thm_GlobalTheory_LatFin_exists_common_den
import Theorems.Thm_GlobalTheory_LatFin_exists_int_smul_mem


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix
open GlobalTheory GlobalTheory.LatDen
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.LatDen
theorem _root_.solution : (∀ (r : ℕ) (X : Data E r), (∀ v : Fin r → E, ∃ n : ℕ, 0 < n ∧ (n : E) • v ∈ X.Λ) ∧ ∃ n : ℕ, 0 < n ∧ ∀ v ∈ X.Λ, ∀ k, IsIntegral ℤ ((n : E) * v k)) := by
  intro r X
  have hsq : ∀ k : ℤ, (((k.natAbs * k.natAbs : ℕ)) : E) = (k : E) * (k : E) := by
    intro k
    have h : ((k.natAbs * k.natAbs : ℕ) : ℤ) = k * k := by
      rw [Nat.cast_mul]; exact Int.natAbs_mul_self' k
    rw [← Int.cast_natCast, h, Int.cast_mul]
  have hpos : ∀ k : ℤ, k ≠ 0 → 0 < k.natAbs * k.natAbs := fun k hk =>
    Nat.mul_pos (Int.natAbs_pos.2 hk) (Int.natAbs_pos.2 hk)
  refine ⟨fun v => ?_, ?_⟩
  · obtain ⟨k, hk, hm⟩ := GlobalTheory.LatFin.exists_int_smul_mem X.Λ X.Λ_span v
    refine ⟨_, hpos k hk, ?_⟩
    rw [hsq, mul_smul, Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul]
    exact zsmul_mem hm k
  · obtain ⟨k, hk, hi⟩ := GlobalTheory.LatFin.exists_common_den X.Λ X.Λ_fg
    refine ⟨_, hpos k hk, fun v hv a => ?_⟩
    rw [hsq, mul_assoc]
    have h1 : IsIntegral ℤ (k : E) := by
      simpa using (isIntegral_algebraMap (R := ℤ) (A := E) (x := k))
    exact h1.mul (hi v hv a)
end GlobalTheory.LatDen
