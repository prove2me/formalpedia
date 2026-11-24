-- Prove2me | solution 1 for GlobalTheory.DvrFinExt.exists_finite_intermediateField
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:25:07.963053+00:00
-- url     : https://prove2.me/submissions/19d67bbe-e974-479d-8332-66b2fa52a448

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsCompleteDvrIntegralClosureFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitBallEqOfIntegralDvr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsFiniteExtensionCompleteDvrPadicAlgCl
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory GlobalTheory.DvrFinExt
namespace GlobalTheory.DvrFinExt
theorem _root_.solution (F K Ω : Type) [Field F] [Field K] [Field Ω] [Algebra F Ω]
    [Algebra.IsIntegral F Ω] [Algebra K Ω] (hQ : ∀ q : F, algebraMap F Ω q ∈ (algebraMap K Ω).range)
    (R : Type) [CommRing R] [Algebra.FiniteType ℤ R] (y₀ : R →+* Ω) :
    ∃ L : IntermediateField K Ω, FiniteDimensional K L ∧ ∀ a, y₀ a ∈ L := by
  have hb : Function.Bijective (algebraMap K Ω).rangeRestrict :=
    ⟨(algebraMap K Ω).rangeRestrict.injective, (algebraMap K Ω).rangeRestrict_surjective⟩
  let e := RingEquiv.ofBijective _ hb
  let u : F →+* K := e.symm.toRingHom.comp ((algebraMap F Ω).codRestrict _ hQ)
  have hu : (algebraMap K Ω).comp u = (RingHom.id Ω).comp (algebraMap F Ω) := by
    ext q
    have h := e.apply_symm_apply ((algebraMap F Ω).codRestrict _ hQ q)
    exact congrArg Subtype.val h
  have hint : ∀ x : Ω, IsIntegral K x := fun x =>
    IsIntegral.map_of_comp_eq u (RingHom.id Ω) hu (Algebra.IsIntegral.isIntegral (R := F) x)
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := ℤ) (A := R)
  haveI : Finite (y₀ '' (s : Set R)) := (s.finite_toSet.image y₀).to_subtype
  refine ⟨IntermediateField.adjoin K (y₀ '' (s : Set R)),
    IntermediateField.finiteDimensional_adjoin (fun x _ => hint x), fun a => ?_⟩
  have ha : a ∈ Algebra.adjoin ℤ (s : Set R) := hs ▸ Algebra.mem_top
  induction ha using Algebra.adjoin_induction with
  | mem x hx => exact IntermediateField.subset_adjoin _ _ ⟨x, hx, rfl⟩
  | algebraMap n => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
end GlobalTheory.DvrFinExt
