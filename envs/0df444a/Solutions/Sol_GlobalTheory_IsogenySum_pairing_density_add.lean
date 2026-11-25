-- Prove2me | solution 1 for GlobalTheory.IsogenySum.pairing_density_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:23:51.799844+00:00
-- url     : https://prove2.me/submissions/5e6d1fd1-08fd-47b4-b796-5c11bc738d53

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_FockTranslationLaws
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IntegrableOnFundamentalDomainOfContinuous
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ContinuousThetaSectionPointwiseNormSq
import Theorems.Thm_GlobalTheory_FockTranslation_herm_add_left
import Theorems.Thm_GlobalTheory_FockTranslation_herm_add_right
import Theorems.Thm_GlobalTheory_FockTranslation_herm_conj
import Theorems.Thm_GlobalTheory_FockTranslation_herm_sub_left
import Theorems.Thm_GlobalTheory_FockTranslation_herm_sub_right
import Theorems.Thm_GlobalTheory_FockTranslation_herm_sub_swap


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Complex ReciprocityTheory.ChartRestriction.G.I2 MeasureTheory
open GlobalTheory.IsogenySum
open FockTranslation
variable {ι : Type} [Fintype ι]
variable (U : ℕ → EuclideanSpace ℂ ι → (EuclideanSpace ℂ ι → ℂ) → EuclideanSpace ℂ ι → ℂ)
  (hU : ∀ (q : ℕ) a F v, U q a F v =
    cexp (q * Real.pi * Hf v a - q * Real.pi * Hf a a / 2) * F (v - a))
include hU
namespace GlobalTheory.IsogenySum
theorem _root_.solution (Y : GT ι) {F : EuclideanSpace ℂ ι → ℂ} (hF : F ∈ Y.Sec 1)
    (y y' : EuclideanSpace ℂ ι) {x : EuclideanSpace ℂ ι} (hx : x ∈ lat Y.b)
    (v : EuclideanSpace ℂ ι) :
    U 1 y F (v + x) * (starRingEnd ℂ) (U 1 y' F (v + x)) * cexp (-(Real.pi * Hf (v + x) (v + x))) =
      cexp (2 * Real.pi * I * (Hf x (y - y')).im) *
        (U 1 y F v * (starRingEnd ℂ) (U 1 y' F v) * cexp (-(Real.pi * Hf v v))) := by
  have hk : Y.ka x * (starRingEnd ℂ) (Y.ka x) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Y.ka_abs x hx]; simp
  have e : ∀ z, v + x - z = (v - z) + x := fun z => by abel
  simp only [hU, e, hF.2 x hx, map_mul, ← Complex.exp_conj, map_add, map_sub, map_div₀,
    herm_conj, Complex.conj_ofReal, Nat.cast_one, one_mul, map_ofNat]
  have key : cexp (Real.pi * Hf (v + x) y - Real.pi * Hf y y / 2) *
      cexp (Real.pi * Hf (v - y) x + Real.pi * Hf x x / 2) *
      cexp (Real.pi * Hf y' (v + x) - Real.pi * Hf y' y' / 2) *
      cexp (Real.pi * Hf x (v - y') + Real.pi * Hf x x / 2) *
      cexp (-(Real.pi * Hf (v + x) (v + x))) =
      cexp (2 * Real.pi * I * (Hf x (y - y')).im) *
      cexp (Real.pi * Hf v y - Real.pi * Hf y y / 2) *
      cexp (Real.pi * Hf y' v - Real.pi * Hf y' y' / 2) * cexp (-(Real.pi * Hf v v)) := by
    simp only [← Complex.exp_add]
    congr 1
    simp only [herm_add_left, herm_add_right, herm_sub_left, herm_sub_right, Complex.sub_im]
    rw [herm_sub_swap x y, herm_sub_swap x y']
    push_cast
    ring
  linear_combination (F (v - y) * (starRingEnd ℂ) (F (v - y'))) * key +
    (F (v - y) * (starRingEnd ℂ) (F (v - y')) *
      cexp (Real.pi * Hf (v + x) y - Real.pi * Hf y y / 2) *
      cexp (Real.pi * Hf (v - y) x + Real.pi * Hf x x / 2) *
      cexp (Real.pi * Hf y' (v + x) - Real.pi * Hf y' y' / 2) *
      cexp (Real.pi * Hf x (v - y') + Real.pi * Hf x x / 2) *
      cexp (-(Real.pi * Hf (v + x) (v + x)))) * hk
end GlobalTheory.IsogenySum
