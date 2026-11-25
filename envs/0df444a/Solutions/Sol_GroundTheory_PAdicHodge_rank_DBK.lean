-- Prove2me | solution 1 for GroundTheory.PAdicHodge.rank_DBK
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:29:32.993968+00:00
-- url     : https://prove2.me/submissions/df17b2aa-ad4b-43cc-88ad-3b8af8eb0eaa

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_Admissible
import Definitions.Def_GroundTheory_PAdicHodge_AdmissibleField
import Theorems.Thm_GroundTheory_PAdicHodge_coe_toInvariantRing
import Theorems.Thm_GroundTheory_PAdicHodge_toInvariantRing_bijective
import Theorems.Thm_GroundTheory_PAdicHodge_IsRegular_coe_basisOfIsAdmissible
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.PAdicHodge.IsRegular.coe_basisOfIsAdmissible


attribute [local simp] GroundTheory.PAdicHodge.coe_toInvariantRing

set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.PAdicHodge
open TensorProduct Module
variable (G F K B : Type*) [Group G] [Field F] [Field K] [CommRing B] [Algebra F K] [Algebra K B]
  [Algebra F B] [IsScalarTower F K B] [MulSemiringAction G B] [SMulCommClass G F B]
  [SMulCommClass G K B]
variable {V : Type*} [AddCommGroup V] [Module F V] (ρ : Representation F G V)
variable {G F K B}
namespace GroundTheory.PAdicHodge
theorem _root_.solution [Nontrivial B]
    (hK : ∀ b : B, (∀ g : G, g • b = b) → ∃ k : K, algebraMap K B k = b) :
    Module.rank K (DBK G F K B ρ) = Module.rank (invariantRing G F B) (DB B ρ) := by
  let j : DBK G F K B ρ ≃+ DB B ρ :=
    { toFun := fun x => ⟨x, x.2⟩
      invFun := fun x => ⟨x, x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl }
  refine rank_eq_of_equiv_equiv (toInvariantRing G F K B) j (toInvariantRing_bijective hK) ?_
  intro k x
  apply Subtype.ext
  change k • (x : B ⊗[F] V) =
    ((toInvariantRing G F K B k : invariantRing G F B) : B) • (x : B ⊗[F] V)
  rw [coe_toInvariantRing, algebraMap_smul]
end GroundTheory.PAdicHodge
