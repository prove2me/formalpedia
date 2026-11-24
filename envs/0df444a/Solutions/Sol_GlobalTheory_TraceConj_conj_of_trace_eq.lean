-- Prove2me | solution 1 for GlobalTheory.TraceConj.conj_of_trace_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:19:18.914016+00:00
-- url     : https://prove2.me/submissions/3014bc4b-c6a6-482f-8358-74e4a5b2832f

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataN
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NonemptyLinearEquivOfCharpolyEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ColRepSemisimple
import Theorems.Thm_GlobalTheory_TraceConj_colRep_apply
import Theorems.Thm_GlobalTheory_TraceConj_colRep_semisimple
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_GaloisCohomology_scalRep_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_GlobalTheory_TraceIso_exists_equiv_of_trace_eq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.GaloisCohomology.scalRep_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.TraceConj
variable {Γ k : Type} [Group Γ] [Field k] {a : ℕ}
namespace GlobalTheory.TraceConj
theorem _root_.solution : ∀ (Γ k : Type) [Group Γ] [Field k] [CharZero k] (a : ℕ)
    (ρ ρ' : Γ →* GL (Fin a) k), Formalism.MainNotions.N.IsSSRep ρ → Formalism.MainNotions.N.IsSSRep ρ' →
    (∀ g, ((ρ g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k).trace =
      ((ρ' g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k).trace) →
    ∃ h : GL (Fin a) k, ∀ g, ρ' g = h * ρ g * h⁻¹ := by
  intro Γ k _ _ _ a ρ ρ' hρ hρ' ht
  obtain ⟨e, he⟩ := GlobalTheory.TraceIso.exists_equiv_of_trace_eq (colRep ρ) (colRep ρ')
    (colRep_semisimple ρ hρ) (colRep_semisimple ρ' hρ') fun g => by
      rw [colRep_apply, colRep_apply, Matrix.trace_toLin'_eq, Matrix.trace_toLin'_eq, ht]
  let h : GL (Fin a) k :=
    ⟨LinearMap.toMatrix' e.toLinearMap, LinearMap.toMatrix' e.symm.toLinearMap,
      by rw [← LinearMap.toMatrix'_comp]; simp,
      by rw [← LinearMap.toMatrix'_comp]; simp⟩
  refine ⟨h, fun g => ?_⟩
  rw [eq_mul_inv_iff_mul_eq]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  apply Matrix.toLin'.injective
  rw [Matrix.toLin'_mul, Matrix.toLin'_mul]
  have hh : Matrix.toLin' (h : Matrix (Fin a) (Fin a) k) = e.toLinearMap :=
    Matrix.toLin'_toMatrix' _
  rw [hh]
  exact LinearMap.ext fun v => (he g v).symm
end GlobalTheory.TraceConj
