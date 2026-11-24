-- Prove2me | solution 1 for GlobalTheory.Mem.RayEx.exists_group
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:16:19.696228+00:00
-- url     : https://prove2.me/submissions/84b5ea3f-1e20-421a-a0e2-75ef4b7b6b73

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_NonemptyRayDataOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RayDataNonempty
import Theorems.Thm_GlobalTheory_Mem_RayEx_isUnit_quot
import Theorems.Thm_GlobalTheory_Mem_RayEx_finite_quot

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
theorem _root_.solution (hm : m ≠ ⊤) [Finite (R ⧸ m)] [Finite (ClassGroup R)] :
    ∃ (G : Type) (_ : CommGroup G) (_ : Fintype G) (φ : S m →* G), Function.Surjective φ ∧
      ∀ I J, φ I = φ J ↔ Rel m I.1 J.1 := by
  haveI : Finite (con m).Quotient := finite_quot hm
  exact ⟨(con m).Quotient, commGroupOfIsUnit isUnit_quot, Fintype.ofFinite _, (con m).mk',
    Con.mk'_surjective, fun I J => Con.eq _⟩
end GlobalTheory.Mem.RayEx
