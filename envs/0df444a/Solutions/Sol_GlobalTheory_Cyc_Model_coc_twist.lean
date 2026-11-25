-- Prove2me | solution 1 for GlobalTheory.Cyc.Model.coc_twist
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:41:14.719083+00:00
-- url     : https://prove2.me/submissions/2e59755a-0d3e-40ed-8f72-03ee5c0511f8

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_PowLtFirstRadius
import Theorems.Thm_GlobalTheory_Cyc_Model_isActC_actC
import Theorems.Thm_GlobalTheory_Cyc_Model_chi_val
import Theorems.Thm_GlobalTheory_Cyc_Model_chi_cont
import Theorems.Thm_GlobalTheory_Cyc_Model_chiC_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Cyc GlobalTheory.Cyc.Model
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc Polynomial
variable {l : ℕ} [Fact l.Prime]
namespace GlobalTheory.Cyc.Model
theorem _root_.solution (G : Subgroup (GQ l)) :
    CobOn G (twAct actC chi 1 (fun _ => (1 : Matrix (Fin 1) (Fin 1) (PadicComplex l)))) (ball l 1)
      (fun σ _ => chiC chi 1 σ - 1) ∧
    CocOn G (twAct actC chi 1 (fun _ => (1 : Matrix (Fin 1) (Fin 1) (PadicComplex l)))) (ball l 1)
      (fun σ _ => chiC chi 1 σ - 1) := by
  refine ⟨⟨fun _ => 1, fun _ => by simp, fun g _ => ?_⟩, ?_, fun g _ a => ?_, fun g _ h _ => ?_⟩
  · ext a; simp [twAct]
  · refine Continuous.continuousOn (continuous_pi fun _ => Continuous.sub ?_ continuous_const)
    change Continuous fun σ : GQ l => algebraMap ℚ_[l] (PadicComplex l) ((chi σ ^ (1 : ℤ) : ℚ_[l]ˣ) : ℚ_[l])
    simp only [zpow_one]
    exact (continuous_algebraMap ℚ_[l] (PadicComplex l)).comp chi_cont
  · have h1 : ‖chiC chi 1 g‖ ≤ 1 := by
      rw [chiC_one, PadicComplex.norm_extends', chi_val]
      exact (chiZ g : ℤ_[l]).2
    change ‖chiC chi 1 g - 1‖ ≤ 1
    rw [sub_eq_add_neg]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h1 (by simp))
  · ext a
    have h1 : actC g (chiC chi 1 h) = chiC chi 1 h := by
      rw [chiC_one, isActC_actC.1, AlgEquiv.commutes]
    have h2 : chiC chi 1 (g * h) = chiC chi 1 g * chiC chi 1 h := by simp [chiC]
    simp only [twAct, Matrix.one_mulVec, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_sub, map_one, h1, h2]
    ring
end GlobalTheory.Cyc.Model
