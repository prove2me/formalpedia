-- Prove2me | solution 1 for GlobalTheory.coeff_eq_zero_of_simple_pole
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:59:35.268839+00:00
-- url     : https://prove2.me/submissions/a98659cd-b13b-4bb2-b88f-5c5b50f8a5de

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjDehomA
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_OpensRangeChartYSupOpensRangeChartZ
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_AwayToSectionFromZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsRegularFnIffOfIsAffineOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsAffineHomOfIsPullbackSpecMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TangentBijectionOfValues
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_SpecMapAwayFnEquivAwayChart
import Theorems.Thm_GlobalTheory_QCoh_Qcqs_appLinearBase_apply
import Theorems.Thm_GlobalTheory_QCoh_germLinear_apply
import Theorems.Thm_GlobalTheory_QCoh_resBasicOpen_apply
import Theorems.Thm_GlobalTheory_QCoh_resLinear_apply
import Theorems.Thm_GlobalTheory_WeierstrassCurve_affineMap_affineX
import Theorems.Thm_GlobalTheory_WeierstrassCurve_affineMap_affineY
import Theorems.Thm_GlobalTheory_WeierstrassCurve_affineMap_algebraMap
import Theorems.Thm_GlobalTheory_WeierstrassCurve_originMap_algebraMap
import Theorems.Thm_GlobalTheory_WeierstrassCurve_originMap_originW
import Theorems.Thm_GlobalTheory_WeierstrassCurve_originMap_originZ
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.QCoh.Qcqs.appLinearBase_apply
attribute [local simp] GlobalTheory.QCoh.germLinear_apply
attribute [local simp] GlobalTheory.QCoh.resBasicOpen_apply
attribute [local simp] GlobalTheory.QCoh.resLinear_apply
attribute [local simp] GlobalTheory.WeierstrassCurve.affineMap_affineX
attribute [local simp] GlobalTheory.WeierstrassCurve.affineMap_affineY
attribute [local simp] GlobalTheory.WeierstrassCurve.affineMap_algebraMap
attribute [local simp] GlobalTheory.WeierstrassCurve.originMap_algebraMap
attribute [local simp] GlobalTheory.WeierstrassCurve.originMap_originW
attribute [local simp] GlobalTheory.WeierstrassCurve.originMap_originZ



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap resG constFn)
open GlobalTheory.ProjFrac GlobalTheory.QCoh.Qcqs GlobalTheory.TangentOrigin
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {R B C κ : Type*} [CommRing R] [CommRing B] [CommRing C]
    (ρ : R →+* B) (ι : B →+* C) (hι : Function.Injective ι) (ε : B →+* R)
    (hρ : ∀ r, ε (ρ r) = r) (z : B) (hz : ε z = 0) (d : κ → ℕ) (hd : Function.Injective d)
    (e : κ → C) (v : κ → B) (hv : ∀ k, ι z ^ d k * e k = ι (v k)) (hε : ∀ k, ε (v k) = 1)
    (c : κ → R) (s : Finset κ) (b : B) (h : ι z * ∑ k ∈ s, ι (ρ (c k)) * e k = ι b) :
    ∀ k ∈ s, 2 ≤ d k → c k = 0 := by
  classical
  induction s using Finset.induction_on_max_value d with
  | empty => simp
  | insert a s ha hmax ih =>
    by_cases h2 : 2 ≤ d a
    · have hlt : ∀ k ∈ s, d k < d a := fun k hk =>
        lt_of_le_of_ne (hmax k hk) fun e => ha (hd e ▸ hk)
      have key : ρ (c a) * v a + ∑ k ∈ s, ρ (c k) * (z ^ (d a - d k) * v k) = z ^ (d a - 1) * b := by
        apply hι
        rw [map_mul ι (z ^ _), ← h, map_pow, ← mul_assoc, ← pow_succ, Nat.sub_add_cancel (by omega),
          Finset.sum_insert ha, mul_add, map_add, map_sum, Finset.mul_sum, map_mul, ← hv]
        refine congrArg₂ (· + ·) (by ring) (Finset.sum_congr rfl fun k hk => ?_)
        obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le (hlt k hk).le
        rw [map_mul, map_mul, map_pow, ← hv, hm, Nat.add_sub_cancel_left]
        ring
      have hca : c a = 0 := by
        have := congrArg ε key
        rw [map_add, map_sum, map_mul, map_mul, map_pow, hz, zero_pow (by omega), zero_mul, hρ, hε,
          mul_one, Finset.sum_eq_zero, add_zero] at this
        · exact this
        · intro k hk
          have := hlt k hk
          rw [map_mul, map_mul, map_pow, hz, zero_pow (by omega), zero_mul, mul_zero]
      rw [Finset.sum_insert ha, hca, map_zero, map_zero, zero_mul, zero_add] at h
      intro k hk
      rcases Finset.mem_insert.1 hk with rfl | hk
      · exact fun _ => hca
      · exact ih h k hk
    · intro k hk hk2
      rcases Finset.mem_insert.1 hk with rfl | hk
      · exact absurd hk2 h2
      · have := hmax k hk
        omega
end GlobalTheory
