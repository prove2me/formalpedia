-- Prove2me | solution 1 for GlobalTheory.KSp.Homog.eq_smul_haar_of_homog
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:14:31.856438+00:00
-- url     : https://prove2.me/submissions/cb9ccf14-ddcb-4b55-9674-04128fe40f13

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_UnipVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HomogeneousMeasureEqSmulAddHaarLocalField
import Theorems.Thm_GlobalTheory_KSp_Homog_isOpen_sphere
import Theorems.Thm_GlobalTheory_KSp_Homog_measure_mul_measure_units_eq
import Theorems.Thm_GlobalTheory_SplitWeil_isCompact_int
import Theorems.Thm_GlobalTheory_SplitWeil_secondCountable
import Theorems.Thm_GlobalTheory_SplitWeil_t2Space


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
open ValuativeRel Topology
open scoped ENNReal NNReal Pointwise
noncomputable section
open GlobalTheory GlobalTheory.KSp GlobalTheory.KSp.Homog
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
namespace GlobalTheory.KSp.Homog
theorem _root_.solution : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F]
    (lam : Measure F) [lam.IsAddHaarMeasure] (n : Measure F) [IsFiniteMeasureOnCompacts n],
    n {0} = 0 → (∀ u : Fˣ, n.map (fun x => (u : F) * x) = (distribHaarChar F u)⁻¹ • n) →
    ∃ r : NNReal, n = r • lam := by
  intro F _ _ _ _ _ _ _ lam _ n _ hn0 hn
  haveI := GlobalTheory.SplitWeil.secondCountable F
  haveI := GlobalTheory.SplitWeil.t2Space F
  have hn' : ∀ x : F, x ≠ 0 → n.map (fun y ↦ x * y) = (absE x)⁻¹ • n := by
    intro x hx
    have h := hn (Units.mk0 x hx)
    simp only [Units.val_mk0] at h
    rw [h, absE, dif_neg hx, ← ENNReal.coe_inv (distribHaarChar_pos (A := F) (g := Units.mk0 x hx)).ne']
    ext s; rw [Measure.smul_apply, Measure.smul_apply, ENNReal.smul_def]
  have hUO : (U : Set F) ⊆ (𝒪[F] : Set F) := fun y hy ↦
    (Valuation.mem_integer_iff _ _).mpr (le_of_eq hy)
  have hnU : n U ≠ ∞ :=
    ((measure_mono hUO).trans_lt (GlobalTheory.SplitWeil.isCompact_int F).measure_lt_top).ne
  have hlU : lam U ≠ ∞ :=
    ((measure_mono hUO).trans_lt (GlobalTheory.SplitWeil.isCompact_int F).measure_lt_top).ne
  have hlU0 : lam U ≠ 0 :=
    ((isOpen_sphere (F := F) one_ne_zero).measure_pos lam ⟨1, by simp⟩).ne'
  refine ⟨(n U / lam U).toNNReal, ?_⟩
  ext s hs
  rw [Measure.smul_apply, ENNReal.smul_def, ENNReal.coe_toNNReal (ENNReal.div_ne_top hnU hlU0),
    smul_eq_mul]
  have hk := measure_mul_measure_units_eq lam n hn0 hn' hs
  rw [div_eq_mul_inv, mul_right_comm, ← hk, mul_assoc, ENNReal.mul_inv_cancel hlU0 hlU, mul_one]
end GlobalTheory.KSp.Homog
