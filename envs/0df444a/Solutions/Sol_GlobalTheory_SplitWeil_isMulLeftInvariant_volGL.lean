-- Prove2me | solution 1 for GlobalTheory.SplitWeil.isMulLeftInvariant_volGL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:54:46.989347+00:00
-- url     : https://prove2.me/submissions/f93134f3-097b-4b9f-9cbc-ee919f5badcf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ValuationDetOfMemKO
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormalizedAbsCharacterization
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LinearChangeOfVariablesLocalFieldMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsMulLeftInvariantVolGL
import Theorems.Thm_GlobalTheory_SplitWeil_map_mul_left_volM
import Theorems.Thm_GlobalTheory_SplitWeil_continuous_density_volGL
import Theorems.Thm_GlobalTheory_SplitWeil_Model_measurableEmbedding_val
import Theorems.Thm_GlobalTheory_SplitWeil_Model_nabs_mul
import Theorems.Thm_GlobalTheory_SplitWeil_Model_nabs_one
import Theorems.Thm_GlobalTheory_SplitWeil_nabs_mul
import Theorems.Thm_GlobalTheory_SplitWeil_nabs_one
import Theorems.Thm_GlobalTheory_SplitWeil_secondCountable
import Theorems.Thm_P2M_GlobalTheory_SplitWeil_nabs_pos__162ed63212bf


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open scoped ENNReal NNReal
open GlobalTheory GlobalTheory.SplitWeil
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k] {n : Type} [Fintype n] [DecidableEq n]
  (ν : Measure k) [ν.IsAddHaarMeasure]
namespace GlobalTheory.SplitWeil
theorem _root_.solution : (volGL ν n).IsMulLeftInvariant := by
  haveI := secondCountable k
  haveI : BorelSpace (Matrix n n k) := inferInstanceAs (BorelSpace (n → n → k))
  have hE := Model.measurableEmbedding_val (k := k) n
  have hd := (continuous_density_volGL (k := k) (n := n)).measurable
  set μ := (volM ν n n).comap (fun g : GL n k => g.val) with hμ
  set d := fun g : GL n k =>
    ENNReal.ofReal (nabs k (Matrix.GeneralLinearGroup.det g) ^ (-(Fintype.card n : ℝ))) with hdd
  have dmul : ∀ g h, d (g * h) = d g * d h := fun g h => by
    simp only [hdd, map_mul, nabs_mul]
    rw [Real.mul_rpow (nabs_pos' _).le (nabs_pos' _).le,
      ENNReal.ofReal_mul (Real.rpow_nonneg (nabs_pos' _).le _)]
  have done' : d 1 = 1 := by simp [hdd, nabs_one]
  have hm : ∀ h : GL n k, μ.map (fun x => h * x) = d h • μ := fun h => by
    ext s hs
    have cm : Measurable fun x : Matrix n n k => h.val * x :=
      (continuous_const.matrix_mul continuous_id).measurable
    rw [Measure.map_apply (measurable_const_mul h) hs, Measure.smul_apply, hE.comap_apply, hE.comap_apply,
      ← Measure.smul_apply, ← map_mul_left_volM ν h, Measure.map_apply cm (hE.measurableSet_image.2 hs)]
    congr 1
    ext x
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact ⟨h * g, hg, rfl⟩
    · rintro ⟨g, hg, e⟩
      refine ⟨h⁻¹ * g, by simpa using hg, ?_⟩
      have e' : g.val = h.val * x := e
      simp only [Units.val_mul, e', ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
  refine ⟨fun h => ?_⟩
  ext s hs
  have hs' := measurable_const_mul h hs
  change (μ.withDensity d).map _ s = μ.withDensity d s
  rw [Measure.map_apply (measurable_const_mul h) hs, withDensity_apply _ hs', withDensity_apply _ hs,
    ← lintegral_indicator hs', ← lintegral_indicator hs]
  have e1 : ∀ x, ((fun x => h * x) ⁻¹' s).indicator d x = d h⁻¹ * s.indicator d (h * x) := fun x => by
    by_cases hx : h * x ∈ s
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (show x ∈ (fun x => h * x) ⁻¹' s from hx), ← dmul,
        inv_mul_cancel_left]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (show x ∉ (fun x => h * x) ⁻¹' s from hx),
        mul_zero]
  simp_rw [e1]
  rw [lintegral_const_mul _ (f := fun a => s.indicator d (h * a))
      ((hd.indicator hs).comp (measurable_const_mul h)),
    ← lintegral_map (hd.indicator hs) (measurable_const_mul h), hm, lintegral_smul_measure, smul_eq_mul,
    ← mul_assoc, ← dmul, inv_mul_cancel, done', one_mul]
end GlobalTheory.SplitWeil
