-- Prove2me | solution 1 for GlobalTheory.exists_algHom_apply_eq_of_transcendental
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:37:03.728924+00:00
-- url     : https://prove2.me/submissions/88af8153-7702-4f6b-98b5-c04e549f5ee0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SpecialisationNumberFieldAndCountableValues
import Theorems.Thm_GlobalTheory_exists_ringHom_extend_of_finiteType
import Theorems.Thm_GlobalTheory_exists_fg_subalgebra_over

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {k L : Type*} [Field k] [Field L] [Algebra k L]
    [IsAlgClosed L] (R : Subalgebra k L) (hR : R.FG) (c : R) (hc : Transcendental k (c : L))
    (t : L) (ht : Transcendental k t) : ∃ ρ : R →ₐ[k] L, ρ c = t := by
  let F : IntermediateField k L := IntermediateField.adjoin k {(c : L)}
  let σ : F →ₐ[k] L := (IntermediateField.val _).comp
    ((RatFunc.algEquivOfTranscendental t ht).toAlgHom.comp
      (RatFunc.algEquivOfTranscendental (c : L) hc).symm.toAlgHom)
  have hσ : σ (IntermediateField.AdjoinSimple.gen k (c : L)) = t := by
    change ((RatFunc.algEquivOfTranscendental t ht)
      ((RatFunc.algEquivOfTranscendental (c : L) hc).symm
        (IntermediateField.AdjoinSimple.gen k (c : L))) : L) = t
    rw [RatFunc.algEquivOfTranscendental_symm_gen, RatFunc.algEquivOfTranscendental_X]
  obtain ⟨A, hA, hRA, -⟩ := exists_fg_subalgebra_over F R hR 0
  obtain ⟨φ, hφ⟩ := exists_ringHom_extend_of_finiteType F A L σ.toRingHom
  let ι : R →+* A :=
    { toFun := fun x => ⟨x.1, hRA x.2⟩
      map_one' := rfl, map_mul' := fun _ _ => rfl, map_zero' := rfl, map_add' := fun _ _ => rfl }
  refine ⟨{ φ.comp ι with commutes' := fun a => ?_ }, ?_⟩
  · exact (hφ (algebraMap k F a)).trans (σ.commutes a)
  · exact (hφ (IntermediateField.AdjoinSimple.gen k (c : L))).trans hσ
end GlobalTheory
