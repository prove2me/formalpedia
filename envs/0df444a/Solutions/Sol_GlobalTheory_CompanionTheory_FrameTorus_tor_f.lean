-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FrameTorus.tor_f
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:06:42.795343+00:00
-- url     : https://prove2.me/submissions/0d6e9624-7c4c-4d90-9473-3dabc72cdbfa

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_TorusStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_FrameTorus_pair_apply
import Theorems.Thm_GlobalTheory_CompanionTheory_FrameTorus_tor_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CompanionTheory.FrameTorus.pair_apply

set_option autoImplicit false
open CompanionTheory.Rg.FlB
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FrameTorus
variable {L : Type} [NontriviallyNormedField L] {V : Type} [AddCommGroup V] [Module L V]
variable {s : L →+* L} {h : V → V → L} {δ : L} {l : ℕ} {e f : Fin l → V} {W : Submodule L V}
namespace GlobalTheory.CompanionTheory.FrameTorus
theorem _root_.solution (hH : IsHerm s h) (hF : IsFrame h δ e f W) (hδ : δ ≠ 0) (u : Fin l → L) (j : Fin l) :
    tor hH δ e f u (f j) = (s (u j))⁻¹ • f j := by
  rw [tor_apply]
  simp only [hF.2.1, hF.2.2.1, zero_smul, smul_zero, Finset.sum_const_zero, add_zero, ite_smul,
    smul_ite, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [smul_smul, mul_assoc, inv_mul_cancel₀ hδ, mul_one, sub_smul, one_smul]
  abel
end GlobalTheory.CompanionTheory.FrameTorus
