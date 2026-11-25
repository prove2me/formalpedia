-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.spanFinrank_maximalIdeal_le_quotient_add_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:48:01.107778+00:00
-- url     : https://prove2.me/submissions/00e1ab4c-e6a7-4523-b9ce-8eb5d4a1a9cf

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularUFDSerre
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularUFDLocalization

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.SchemeCoh
open IsLocalRing Ideal CategoryTheory Abelian
open scoped Pointwise
universe u
variable {R : Type u} [CommRing R]
namespace GroundTheory.Arith.SchemeCoh
theorem _root_.solution [IsLocalRing R] [IsNoetherianRing R]
    {x : R} [IsLocalRing (R ⧸ span {x})] :
    (maximalIdeal R).spanFinrank ≤ (maximalIdeal (R ⧸ span {x})).spanFinrank + 1 := by
  classical
  obtain ⟨t, hcard, hspan⟩ := Submodule.FG.exists_span_finset_card_eq_spanFinrank
    (maximalIdeal (R ⧸ span {x})).fg_of_isNoetherianRing
  let lift : R ⧸ span {x} → R := Function.surjInv Ideal.Quotient.mk_surjective
  have hlift : ∀ b, Ideal.Quotient.mk (span {x}) (lift b) = b :=
    Function.surjInv_eq Ideal.Quotient.mk_surjective
  let S : Finset R := insert x (t.image lift)
  have hloc : IsLocalHom (Ideal.Quotient.mk (span {x})) :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  have hcomap : (maximalIdeal (R ⧸ span {x})).comap (Ideal.Quotient.mk (span {x})) =
      maximalIdeal R := IsLocalRing.maximalIdeal_comap _
  have hmap : (span ((t.image lift : Finset R) : Set R)).map (Ideal.Quotient.mk (span {x})) =
      maximalIdeal (R ⧸ span {x}) := by
    rw [Ideal.map_span, ← hspan, Finset.coe_image, ← Set.image_comp]
    congr 1
    ext b
    simp [hlift]
  have heq : span (S : Set R) = maximalIdeal R := by
    have h2 := congrArg (Ideal.comap (Ideal.Quotient.mk (span {x}))) hmap
    rw [Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective, Ideal.mk_ker,
      hcomap] at h2
    rw [Finset.coe_insert, Ideal.span_insert, ← h2, sup_comm]
  have hle : (Ideal.span (S : Set R)).spanFinrank ≤ (S : Set R).ncard :=
    Submodule.spanFinrank_span_le_ncard_of_finite (Finset.finite_toSet S)
  rw [heq, Set.ncard_coe_finset] at hle
  refine hle.trans ((Finset.card_insert_le _ _).trans ?_)
  rw [← hcard]
  exact Nat.add_le_add_right Finset.card_image_le 1
end GroundTheory.Arith.SchemeCoh
