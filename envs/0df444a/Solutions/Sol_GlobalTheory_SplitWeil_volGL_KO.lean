-- Prove2me | solution 1 for GlobalTheory.SplitWeil.volGL_KO
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:56:07.363174+00:00
-- url     : https://prove2.me/submissions/85abe707-1fb0-40c1-872b-cb9d72b705a5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ValuationDetOfMemKO
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormalizedAbsCharacterization
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LinearChangeOfVariablesLocalFieldMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsMulLeftInvariantVolGL
import Theorems.Thm_GlobalTheory_SplitWeil_Model_measurableEmbedding_val
import Theorems.Thm_GlobalTheory_SplitWeil_nabs_eq_one_iff


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
theorem _root_.solution : volGL ν n (KO k n) = volM ν n n ((fun g : GL n k => g.val) '' (KO k n)) := by
  have hE := Model.measurableEmbedding_val (k := k) n
  have hs := (SplitFlip.isOpen_KO (k := k) (n := n)).measurableSet
  unfold volGL
  rw [withDensity_apply _ hs, setLIntegral_congr_fun hs (g := fun _ => 1), setLIntegral_one, hE.comap_apply]
  rintro _ ⟨u, rfl⟩
  have h1 : nabs k (Matrix.GeneralLinearGroup.det
      (Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) u)) = 1 := by
    rw [nabs_eq_one_iff]
    have : ((Matrix.GeneralLinearGroup.det
      (Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) u) : kˣ) : k) = algebraMap 𝒪[k] k u.val.det :=
      ((algebraMap 𝒪[k] k).map_det u.val).symm
    rw [this]
    exact (Valuation.integer.integers (valuation k)).one_of_isUnit
      ((Matrix.isUnit_iff_isUnit_det _).1 u.isUnit)
  simp only [h1, Real.one_rpow, ENNReal.ofReal_one]
end GlobalTheory.SplitWeil
