-- Prove2me | solution 1 for GlobalTheory.ConvexCutOff.iteratedFDeriv_symm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:14:57.55786+00:00
-- url     : https://prove2.me/submissions/196b53f6-ad24-4208-8ece-4b2948a305d7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsPermOfOfFnPerm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_PolyDerivRenameOfConvex
import Theorems.Thm_GlobalTheory_ConvexCutOff_fderiv_eq_zero
import Theorems.Thm_GlobalTheory_ConvexCutOff_iteratedFDeriv_eq_zero_off
import Theorems.Thm_GlobalTheory_SCV_analyticOnNhd_of_differentiableOn


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open GlobalTheory GlobalTheory.ConvexCutOff
namespace GlobalTheory.ConvexCutOff
theorem _root_.solution {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [FiniteDimensional ℂ V] {K : Set V} (hK : Convex ℝ K) {F : V → ℂ}
    (hF : ∀ z, z ∉ K → F z = 0) (hd : DifferentiableOn ℂ F (interior K)) (x : V) (n : ℕ)
    (v : Fin n → V) (σ : Equiv.Perm (Fin n)) :
    iteratedFDeriv ℂ n F x (v ∘ σ) = iteratedFDeriv ℂ n F x v := by
  by_cases hx : x ∈ interior K
  · exact (GlobalTheory.SCV.analyticOnNhd_of_differentiableOn isOpen_interior hd x
      hx).contDiffAt.iteratedFDeriv_comp_perm v σ
  · cases n with
    | zero => simp
    | succ n =>
      have : iteratedFDeriv ℂ (n + 1) F x = 0 := by
        rw [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply,
          fderiv_eq_zero hK (iteratedFDeriv_eq_zero_off hK hF n) hx]
        exact map_zero _
      simp [this]
end GlobalTheory.ConvexCutOff
