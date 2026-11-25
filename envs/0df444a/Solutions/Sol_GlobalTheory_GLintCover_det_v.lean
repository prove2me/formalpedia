-- Prove2me | solution 1 for GlobalTheory.GLintCover.det_v
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:56:53.644602+00:00
-- url     : https://prove2.me/submissions/9c6cc3c1-2d27-418f-be93-a9ff48bbc345

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsAdicCompleteAndCardQuotientAdicCompletionInteg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_DetCoverMatrixValuationOne
import Theorems.Thm_GlobalTheory_GLintCover_v_eq_one_of_mul
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open Formalism.UG (GLint)
noncomputable section
open GlobalTheory GlobalTheory.GLintCover
variable {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)}
namespace GlobalTheory.GLintCover
theorem _root_.solution {n : ℕ} {X : GL (Fin n) (v.adicCompletion F)} (hX : X ∈ GLint (Fin n) (Formalism.UG.Ov F v)) :
    Valued.v (X : Matrix (Fin n) (Fin n) (v.adicCompletion F)).det = 1 := by
  obtain ⟨y, rfl⟩ := hX
  have hd : ∀ z : GL (Fin n) (Formalism.UG.Ov F v),
      ((Formalism.UG.bc (n := Fin n) (Formalism.UG.Ov F v).subtype z : GL (Fin n) (v.adicCompletion F)) :
        Matrix (Fin n) (Fin n) (v.adicCompletion F)).det
      = (((z : Matrix (Fin n) (Fin n) (Formalism.UG.Ov F v)).det : Formalism.UG.Ov F v) : v.adicCompletion F) := by
    intro z
    rw [← (Formalism.UG.Ov F v).subtype_apply, RingHom.map_det]; rfl
  have hdi : (y : Matrix (Fin n) (Fin n) (Formalism.UG.Ov F v)).det *
      ((y⁻¹ : GL (Fin n) (Formalism.UG.Ov F v)) : Matrix (Fin n) (Fin n) (Formalism.UG.Ov F v)).det = 1 := by
    rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
  rw [hd]
  refine v_eq_one_of_mul (SetLike.coe_mem _)
    (SetLike.coe_mem (((y⁻¹ : GL (Fin n) (Formalism.UG.Ov F v)) : Matrix (Fin n) (Fin n) (Formalism.UG.Ov F v)).det)) ?_
  have := congrArg (fun z : Formalism.UG.Ov F v => (z : v.adicCompletion F)) hdi
  exact_mod_cast this
end GlobalTheory.GLintCover
