-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Desc.Window.exists_scale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:23:20.377388+00:00
-- url     : https://prove2.me/submissions/386403f5-47fb-4a6c-a43f-7bfb1d933d54

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DltEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_DiscrMulMemOfIsIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AlternatingDifferenceTermWindow
import Theorems.Thm_GlobalTheory_UnitLemma_Desc_Window_isIntegral_zpow_smul_of_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology Classical
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc GlobalTheory.UnitLemma.Desc.Window
variable {K : UQ} (B : InvAlg K) {ι : Type}
namespace GlobalTheory.UnitLemma.Desc.Window
theorem _root_.solution {a : K.O} (ha : K.Small a) (y : B.A) :
    ∃ c : ℕ, ∀ n : ℤ, (c : ℤ) ≤ n → IsIntegral K.O (al K a ^ n • y) := by
  have halg : IsAlgebraic K.O y :=
    (IsFractionRing.isAlgebraic_iff K.O K.E (C := B.A)).2 (Algebra.IsAlgebraic.isAlgebraic y)
  obtain ⟨y0, hy0, hint⟩ := halg.exists_integral_multiple
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible K.O
  obtain ⟨m, hm⟩ := IsDiscreteValuationRing.associated_pow_irreducible hy0 hϖ
  have hdvd : ϖ ∣ a := by
    have := ha.2.1
    rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at this
    exact this
  obtain ⟨w, hw⟩ : y0 ∣ a ^ m := hm.dvd.trans (pow_dvd_pow_of_dvd hdvd m)
  refine ⟨m, fun n hn => isIntegral_zpow_smul_of_le B ha hn ?_⟩
  rw [zpow_natCast]
  have : al K a ^ m • y = algebraMap K.O B.A w * (y0 • y) := by
    rw [← map_pow, algebraMap_smul, hw, Algebra.smul_def, Algebra.smul_def, map_mul]; ring
  rw [this]
  exact isIntegral_algebraMap.mul hint
end GlobalTheory.UnitLemma.Desc.Window
