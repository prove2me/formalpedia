-- Prove2me | solution 1 for GlobalTheory.FiniteFlatKilled.exists_id_pow_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T15:47:09.210191+00:00
-- url     : https://prove2.me/submissions/433e5226-2a40-4c3f-ab10-8340dea921d9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsIdPowEqOneOfIsFiniteOfFlat
import Theorems.Thm_GlobalTheory_FiniteFlatKilled_postcomp_apply
import Theorems.Thm_GlobalTheory_FiniteFlatKilled_point_pow_card
import Theorems.Thm_GlobalTheory_FiniteFlatKilled_comp_convPow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.FiniteFlatKilled.postcomp_apply

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory
open GlobalTheory.FiniteFlatKilled
open TensorProduct WithConv Coalgebra
variable {R B C F : Type*} [CommRing R] [CommRing C] [CommRing F] [Algebra R C] [Algebra R F]
variable [CommRing B] [HopfAlgebra R B]
variable [IsCocomm R B]
namespace GlobalTheory.FiniteFlatKilled
theorem _root_.solution [Module.Finite R B] [Module.Flat R B] :
    ∃ N : ℕ, 1 ≤ N ∧ toConv (AlgHom.id R B) ^ N = 1 := by
  obtain ⟨d, s, hs⟩ := Module.Finite.exists_fin (R := R) (M := B)
  refine ⟨d.factorial, d.factorial_pos, ?_⟩
  apply ofConv_injective
  ext c
  refine Module.eq_of_localization_maximal (R := B) (fun P _ => Localization.AtPrime P)
    (fun P _ => Algebra.linearMap B (Localization.AtPrime P)) _ _ (fun m hm => ?_)
  let C := Localization.AtPrime m
  let u : B →ₐ[R] C := IsScalarTower.toAlgHom R B C
  haveI : Module.Free C (C ⊗[R] B) := Module.free_of_flat_of_isLocalRing
  have h1 := point_pow_card (Module.finBasis C (C ⊗[R] B)) u
  rw [Fintype.card_fin] at h1
  haveI : Nontrivial (C ⊗[R] B) :=
    (Algebra.TensorProduct.lift (AlgHom.id C C) u fun _ _ => Commute.all _ _).toRingHom.domain_nontrivial
  have hpos : 0 < Module.finrank C (C ⊗[R] B) :=
    (Module.finrank_pos_iff_of_free C (C ⊗[R] B)).2 inferInstance
  have hle : Module.finrank C (C ⊗[R] B) ≤ d := by
    have hsp : Submodule.span C (Set.range fun i => (1 : C) ⊗ₜ[R] s i) = ⊤ := by
      have := Submodule.baseChange_span (R := R) C (Set.range s)
      rw [hs, Submodule.baseChange_top, ← Set.range_comp] at this
      exact this.symm
    simpa using finrank_le_of_span_eq_top hsp
  obtain ⟨k, hk⟩ := Nat.dvd_factorial hpos hle
  have h2 := comp_convPow u (toConv (AlgHom.id R B)) d.factorial
  rw [ofConv_toConv, AlgHom.comp_id, hk, pow_mul (toConv u), h1, one_pow, ← hk] at h2
  have h3 := congr($h2 c)
  refine h3.trans ?_
  exact IsScalarTower.algebraMap_apply R B C _
end GlobalTheory.FiniteFlatKilled
