-- Prove2me | solution 1 for OAI.Paper256.tangent_coordinates_isomorphism
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T20:45:50.48899+00:00
-- url     : https://prove2.me/submissions/db0c2466-8724-4323-ab04-96f312f40415

-- Generated from openai/math@1581d4c lean/OAI/Analysis/HyperbolicCones/TangentBasic.lean:L43-L83
-- (upload_full_project.md Phase 4): solution for node OAI.Paper256.tangent_coordinates_isomorphism. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_HyperbolicCones
import Definitions.Def_OAI_Analysis_HyperbolicCones_Model
import Definitions.Def_OAI_Analysis_HyperbolicCones_MatrixBasic
import Definitions.Def_OAI_Analysis_HyperbolicCones_MatrixLinear
import Definitions.Def_OAI_Analysis_HyperbolicCones_PencilConjugation
import Definitions.Def_OAI_Analysis_HyperbolicCones_PencilBlocks
import Definitions.Def_OAI_Analysis_HyperbolicCones_RawBlocks
import Definitions.Def_OAI_Analysis_HyperbolicCones_KernelSpectrum
import Definitions.Def_OAI_Analysis_HyperbolicCones_PencilTopology
import Definitions.Def_OAI_Analysis_HyperbolicCones_SplitBasic
import Definitions.Def_OAI_Analysis_HyperbolicCones_SplitFrame
import Definitions.Def_OAI_Analysis_HyperbolicCones_CongruenceMaps
import Definitions.Def_OAI_Analysis_HyperbolicCones_BlockNormalization
import Definitions.Def_OAI_Analysis_HyperbolicCones_BlockReduction
import Definitions.Def_OAI_Analysis_HyperbolicCones_ScalingAlgebra
import Definitions.Def_OAI_Analysis_HyperbolicCones_FiniteTopology
import Definitions.Def_OAI_Analysis_HyperbolicCones_PencilLimit
import Definitions.Def_OAI_Analysis_HyperbolicCones_Coordinates
import Definitions.Def_OAI_Analysis_HyperbolicCones_ConeMatrix
import Definitions.Def_OAI_Analysis_HyperbolicCones_GramProjection
import Definitions.Def_OAI_Analysis_HyperbolicCones_KernelSmooth
import Definitions.Def_OAI_Analysis_HyperbolicCones_TangentBasic

-- ---- from OAI.Analysis.HyperbolicCones.TangentBasic ----
namespace OAI

noncomputable section

open scoped RealInnerProductSpace

namespace Paper256

theorem tangent_coordinates_isomorphism (v : Vec 4) (hv : ‖v‖ = 1) (hv0 : v 0 ≠ 0) :
    ∃ J : tangentSpace v ≃ₗ[ℝ] (Fin 3 → ℝ),
      ∀ h : tangentSpace v, J h = wedgeCoordinates v h.val := by
  have hf : (innerSL ℝ v).toLinearMap ≠ 0 := by
    intro hf
    have := LinearMap.congr_fun hf v
    simp only [ContinuousLinearMap.coe_coe, innerSL_apply_apply,
      LinearMap.zero_apply, real_inner_self_eq_norm_sq, hv, one_pow] at this
    exact one_ne_zero this
  have hdim : Module.finrank ℝ (tangentSpace v) =
      Module.finrank ℝ (Fin 3 → ℝ) := by
    have ht := Module.Dual.finrank_ker_add_one_of_ne_zero hf
    simp only [finrank_euclideanSpace, Fintype.card_fin] at ht
    simp only [Module.finrank_pi_fintype, Module.finrank_self, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
    change Module.finrank ℝ (LinearMap.ker (innerSL ℝ v).toLinearMap) = 3
    omega
  have hinj : Function.Injective (tangentCoordinates v) := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.2
    intro h hh
    have hw (i : Fin 3) : v 0 * h.val i.succ - h.val 0 * v i.succ = 0 := by
      exact congrFun hh i
    have he : h.val = (h.val 0 / v 0) • v := by
      apply PiLp.ext
      intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · simp [div_mul_cancel₀ _ hv0]
      · dsimp
        calc
          h.val i.succ = (h.val 0 * v i.succ) / v 0 :=
            (eq_div_iff hv0).2 (by nlinarith [hw i])
          _ = (h.val 0 / v 0) * v i.succ := by ring
    have hz : h.val 0 / v 0 = 0 := by
      have hm := h.property
      change inner ℝ v h.val = 0 at hm
      rw [he, real_inner_smul_right, real_inner_self_eq_norm_sq, hv] at hm
      simpa using hm
    apply Subtype.ext
    simpa [hz] using he
  exact ⟨(tangentCoordinates v).linearEquivOfInjective hinj hdim, fun _ => rfl⟩

end Paper256

end

end OAI

-- ---- platform node ----
open OAI OAI.Paper256
open scoped RealInnerProductSpace


theorem solution : type_of% @_root_.OAI.Paper256.tangent_coordinates_isomorphism := @_root_.OAI.Paper256.tangent_coordinates_isomorphism
