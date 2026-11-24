-- Prove2me | solution 1 for GlobalTheory.Mem.RayEx.isUnit_quot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:57:13.097821+00:00
-- url     : https://prove2.me/submissions/6a30970e-96da-4766-ac9f-444f7b16687d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_NonemptyRayDataOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RayDataNonempty
import Theorems.Thm_GlobalTheory_Mem_RayEx_exists_mem_sub_one
import Theorems.Thm_GlobalTheory_Mem_RayEx_isCoprime_span

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.RayEx
open NumberField IsDedekindDomain
variable {R : Type} [CommRing R] [IsDedekindDomain R] (m : Ideal R)
variable {m}
namespace GlobalTheory.Mem.RayEx
theorem _root_.solution (x : (con m).Quotient) : IsUnit x := by
  obtain ⟨⟨I, hI⟩, rfl⟩ := Con.mk'_surjective (c := con m) x
  obtain ⟨a, haI, ha⟩ := exists_mem_sub_one hI
  obtain ⟨J, hJ⟩ : I ∣ Ideal.span {a} := Ideal.dvd_span_singleton.mpr haI
  have hJ' : IsCoprime J m := by
    have := isCoprime_span ha
    rw [hJ] at this
    exact this.of_mul_left_right
  refine IsUnit.of_mul_eq_one ((con m).mk' ⟨J, hJ'⟩) ?_
  rw [← map_mul, ← map_one (con m).mk']
  refine (Con.eq _).mpr ?_
  refine ⟨1, a, by simp, ha, ?_⟩
  simp [hJ]
end GlobalTheory.Mem.RayEx
