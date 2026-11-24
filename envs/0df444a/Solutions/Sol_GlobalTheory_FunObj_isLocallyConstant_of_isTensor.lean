-- Prove2me | solution 1 for GlobalTheory.FunObj.isLocallyConstant_of_isTensor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:52:43.213313+00:00
-- url     : https://prove2.me/submissions/2d524328-57f7-455b-a45e-63c095635cfb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FlatTensorVacuum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasCompactSupportFlatIntegrand
import Theorems.Thm_GlobalTheory_SplitFlip_CondLE_mul
import Theorems.Thm_GlobalTheory_SplitFlip_mem_smul_lat
import Theorems.Thm_GlobalTheory_SplitFlip_mem_stdLat
import Theorems.Thm_GlobalTheory_SplitWeil_Model_isOpen_int


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
noncomputable section
open GlobalTheory GlobalTheory.FunObj
open GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {G : Grid k}
namespace GlobalTheory.FunObj
theorem _root_.solution {ϖ : kˣ} {e : ℕ} {γ : List Edge} {T : G.Args → ℂ} (hT : G.IsTensor ϖ e γ T) :
    IsLocallyConstant T := by
  classical
  refine (IsLocallyConstant.iff_eventually_eq T).2 fun x => ?_
  have h : ∀ᶠ y in nhds x, ∀ b ∈ γ.toFinset, ∀ i j, (((ϖ ^ e)⁻¹ : kˣ) : k) * (y b i j - x b i j) ∈ 𝒪[k] := by
    refine (Filter.eventually_all_finset _).2 fun b _ => Filter.eventually_all.2 fun i =>
      Filter.eventually_all.2 fun j => ?_
    have hc : Continuous fun y : G.Args => (((ϖ ^ e)⁻¹ : kˣ) : k) * (y b i j - x b i j) :=
      continuous_const.mul (((continuous_apply b).matrix_elem i j).sub continuous_const)
    exact (Model.isOpen_int.preimage hc).mem_nhds (by simp)
  filter_upwards [h] with y hy
  rw [← hT.2.2 x (fun b => if b ∈ γ then y b - x b else 0) fun b => ?_]
  · exact hT.1 fun b hb => by simp [show b ∈ γ from hb]
  · split_ifs with hb
    · exact fun i => (mem_smul_lat _ _ _).2 (mem_stdLat.2 fun j => hy b (List.mem_toFinset.2 hb) i j)
    · exact zero_mem _
end GlobalTheory.FunObj
