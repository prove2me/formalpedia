-- Prove2me | solution 1 for NFOne.normFormOne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:59:47.543537+00:00
-- url     : https://prove2.me/submissions/29b52f1f-650c-4008-987e-74afdbfac594

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_NormFormOneUnitary_UnitaryP
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_NormFormOneUnitary_HermitianOrthogonalProjectionVector
import Theorems.Thm_NFOne_Vv_zero
import Theorems.Thm_NFOne_Vv_iso
import Theorems.Thm_NFOne_hermitian_orthogonal_projection_vector
import Theorems.Thm_NFOne_projection_vector_coordinate
import Theorems.Thm_NFOne_nf
import Theorems.Thm_NFOne_cols_X
import Theorems.Thm_NFOne_z_fix
import Theorems.Thm_NFOne_P_rowS
import Theorems.Thm_NFOne_P_rowWS_colW
import Theorems.Thm_NFOne_sg_val
import Theorems.Thm_NFOne_unitary_P
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] NFOne.sg_val



set_option autoImplicit false
open Matrix Finset Formalism.QuantumDeterminants Formalism.FourierDecayAlt.C3
noncomputable section
open NFOne
namespace NFOne
theorem _root_.solution : IsotropicNormalFormPartial := by
  intro k r z' j hj y hz hy2 hdet hzy hyy
  have hu : IsUnit (Matrix.of fun a b : Fin j => y a (sR k r j hj b)).det := isUnit_iff_ne_zero.mpr hdet
  have hMN : (Matrix.of fun a b : Fin j => y a (sR k r j hj b)) *
      (Matrix.of fun a b : Fin j => y a (sR k r j hj b))⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
  have hNM : (Matrix.of fun a b : Fin j => y a (sR k r j hj b))⁻¹ *
      (Matrix.of fun a b : Fin j => y a (sR k r j hj b)) = 1 := Matrix.nonsing_inv_mul _ hu
  refine ⟨1 + Pm k r j (Vv y (Matrix.of fun a b : Fin j => y a (sR k r j hj b))⁻¹), ?_,
    fun a q => if r + k < q.val then y a q else 0, fun a => ⟨?_, ?_, ?_⟩⟩
  · simp only [N0set, UH, Set.mem_setOf_eq]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · exact unitary_P k r j _ (fun c hc => Vv_zero y _ c hc)
        (fun b hb q hq => projection_vector_coordinate k r j hj y _ hy2 hNM b hb q hq)
        (fun b c hb hc => Vv_iso k r j y _ hyy b c hb hc)
    · exact fun a => cols_X k r j _ a
    · exact z_fix k r j _ z' hz (fun c => hermitian_orthogonal_projection_vector k r j y _ z' hzy c)
    · intro p q hq1 hq2 hp
      rw [Matrix.add_apply, P_rowWS_colW k r j _ p q hp hq2, add_zero, Matrix.one_apply]
    · intro p q hq hp
      rw [Matrix.add_apply, P_rowS k r j _ p q hp, add_zero, Matrix.one_apply]
  · exact nf k r j hj y _ hy2 hMN a
  · intro p hp
    exact if_neg (show ¬ (r + k < p.val) by omega)
  · intro p hp
    exact if_pos hp
end NFOne
