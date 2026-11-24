-- Prove2me | solution 1 for GlobalTheory.IndexVolume.volGL_of_subset_KO
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:56:01.525938+00:00
-- url     : https://prove2.me/submissions/6fd0b010-2e7c-4bca-aae8-0e8485e78be4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_BorelParam
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsMulLeftInvariantVolGL
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RelIndexMulMatrixVolumeOpenSubgroupIntegralGL
import Theorems.Thm_GlobalTheory_Doubling_flatSec_self
import Theorems.Thm_GlobalTheory_Doubling_val_aOf
import Theorems.Thm_GlobalTheory_Doubling_val_leviOf
import Theorems.Thm_GlobalTheory_SplitWeil_Model_measurableEmbedding_val
import Theorems.Thm_GlobalTheory_SplitWeil_nabs_eq_one_iff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Doubling.flatSec_self
attribute [local simp] GlobalTheory.Doubling.val_aOf
attribute [local simp] GlobalTheory.Doubling.val_leviOf



set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound
open scoped Pointwise
open GlobalTheory GlobalTheory.IndexVolume
namespace GlobalTheory.IndexVolume
theorem _root_.solution {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] {n : Type} [Fintype n] [DecidableEq n]
    (ν : Measure k) (s : Set (GL n k)) (hs : MeasurableSet s) (hK : s ⊆ KO k n) :
    volGL ν n s = volM ν n n (Units.val '' s) := by
  have hE := Model.measurableEmbedding_val (k := k) n
  unfold volGL
  rw [withDensity_apply _ hs, setLIntegral_congr_fun hs (g := fun _ => 1), setLIntegral_one, hE.comap_apply]
  intro g hg
  obtain ⟨u, rfl⟩ := hK hg
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
end GlobalTheory.IndexVolume
