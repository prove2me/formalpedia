-- Prove2me | solution 1 for GlobalTheory.Nef.admissible_degree_symmetricPowerFamily
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:09:40.883529+00:00
-- url     : https://prove2.me/submissions/8d4b40f9-46be-4304-b514-5db8df5e1d45

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsAdmissibleIntegralBasisChangeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TwistAtOfNe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AdmissibleDegreeSymmetricPowerFamily
import Theorems.Thm_GlobalTheory_Nef_det_symMat_of_upper
import Theorems.Thm_P2M_GlobalTheory_Nef_ord_pow__1a78e6d19b24
import Theorems.Thm_GlobalTheory_Nef_unimod_symMat
import Theorems.Thm_GroundTheory_FunctionField_Place_ordHom_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.FunctionField.Place.ordHom_apply



set_option autoImplicit false
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef Polynomial
set_option autoImplicit false
open GlobalTheory GlobalTheory.Nef
namespace GlobalTheory.Nef
theorem _root_.solution : ∀ (k F : Type) [Field k] [IsAlgClosed k] [Field F] [Algebra k F] (m : ℕ)
    (g : Place k F → Matrix (Fin 2) (Fin 2) F), admitted g → (∀ v, g v 1 0 = 0) →
      admitted (fun v => symMat m (g v)) ∧ deg (fun v => symMat m (g v)) = ((m * (m + 1) / 2 : ℕ) : ℤ) * deg g := by
  intro k F _ _ _ _ m g hg h0
  refine ⟨⟨fun v => ?_, hg.2.subset fun v hv hu => hv (unimod_symMat v m (g v) (h0 v) hu)⟩, ?_⟩
  · rw [det_symMat_of_upper m (g v) (h0 v)]
    exact pow_ne_zero _ (hg.1 v)
  · simp only [deg, det_symMat_of_upper m _ (h0 _), ord_pow']
    rw [mul_finsum]
end GlobalTheory.Nef
