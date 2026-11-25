-- Prove2me | solution 1 for GlobalTheory.bijOn_ker_and_exact_of_quasiIso
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:53:38.548073+00:00
-- url     : https://prove2.me/submissions/a770a6fc-6b8f-4544-923a-2fd212f324de

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsFiniteProjectiveComplexQuasiIso
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_BijOnKerAndExactOfQuasiIsoBaseChange
import Theorems.Thm_GlobalTheory_cochain_comm_apply
import Theorems.Thm_GlobalTheory_cochain_d_d_apply
import Theorems.Thm_GlobalTheory_quasiIsoAt_succ_iff
import Theorems.Thm_GlobalTheory_quasiIsoAt_zero_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {R : Type} [CommRing R]
    {K C : CochainComplex (ModuleCat.{0} R) ℕ} (φ : K ⟶ C) (h : QuasiIso φ) :
    Set.BijOn (φ.f 0).hom (LinearMap.ker (K.d 0 1).hom) (LinearMap.ker (C.d 0 1).hom) ∧
      (Function.Exact (C.d 0 1).hom (C.d 1 2).hom → Function.Exact (K.d 0 1).hom (K.d 1 2).hom) := by
  have h0 := (quasiIsoAt_zero_iff φ).1 inferInstance
  have h1 := (quasiIsoAt_succ_iff φ 0).1 inferInstance
  refine ⟨⟨fun x hx => ?_, fun x hx y hy hxy => ?_, fun y hy => ?_⟩, fun hC x => ⟨fun hx => ?_, ?_⟩⟩
  · have hx' : (K.d 0 1).hom x = 0 := hx
    change (C.d 0 1).hom ((φ.f 0).hom x) = 0
    rw [cochain_comm_apply, hx', map_zero]
  · have hx' : (K.d 0 1).hom x = 0 := hx
    have hy' : (K.d 0 1).hom y = 0 := hy
    exact sub_eq_zero.1 (h0.2 (x - y) (by rw [map_sub, hx', hy', sub_zero])
      (by rw [map_sub, hxy, sub_self]))
  · obtain ⟨x, hx, hx'⟩ := h0.1 y hy
    exact ⟨x, hx, hx'⟩
  · obtain ⟨z, hz⟩ := (hC ((φ.f 1).hom x)).1 (by rw [cochain_comm_apply, hx, map_zero])
    exact h1.2 x z hx hz
  · rintro ⟨w, rfl⟩
    exact cochain_d_d_apply K 0 1 2 w
end GlobalTheory
