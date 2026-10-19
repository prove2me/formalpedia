-- Prove2me | solution 1 for MazurTransfer.ProperRelativeGroupTorsionSpecialization.eq_one_of_pow_eq_one_of_residue_specialization_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-17T10:14:05.940981+00:00
-- url     : https://prove2.me/submissions/9bf4f21a-c874-4931-8dc4-f842fa86693c

/- Copyright (c) 2026 Vas and contributors. Apache-2.0.
Uses official Anthropic FLT at pin 6e837e75355538c7f80bab5b956861e86c4eacc2.
Design boundary: invertible-order torsion detection by the actual residue
specialization of any proper relative group over a valuation ring.
Named downstream consumer: actual rational order-thirteen Picard torsion. -/
import Definitions.Def_MazurTransfer_ProperRelativeGroupValuationSpecialization
import Theorems.Thm_MazurTransfer_OriginalRelativeGroupTorsionKernelInterop_eq_one_of_isTorsionPoint_of_comp_residue_eq
noncomputable section
universe u
open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open MazurTransfer.ValuationRingProperPointRestriction
open MazurTransfer.ProperRelativeGroupValuationSpecialization
variable {R : Type u} [CommRing R] {X : Scheme.{u}} {f : X ⟶ Spec (.of R)}
namespace MazurTransfer.ProperRelativeTorsionSpecializationHelpers20261017
theorem point_pow_eq_nsmul (L : RelativeGroupLaw R f)
    {T : Scheme.{u}} (t : T ⟶ Spec (.of R)) (m : ℕ) (x : SchemeHomOver t f) :
    (letI := L.pointGroup t; x ^ m) = L.nsmul t m x := by
  letI := L.pointGroup t
  induction m with
  | zero => rfl
  | succ m ih => rw [pow_succ, ih, RelativeGroupLaw.nsmul_succ]; rfl
end MazurTransfer.ProperRelativeTorsionSpecializationHelpers20261017
open MazurTransfer.ProperRelativeTorsionSpecializationHelpers20261017
variable (B K : Type u) [CommRing B] [IsDomain B] [ValuationRing B] [IsLocalRing B]
variable [Field K] [Algebra B K] [IsFractionRing B K]
theorem solution
    (L : RelativeGroupLaw R f) (hc : L.IsCommutative) [IsProper f]
    (t : Spec (.of B) ⟶ Spec (.of R)) (m : ℕ) (hm : IsUnit (m : B)) :
    letI := L.pointGroup (fractionInclusion B K ≫ t)
    letI := L.pointGroup (Spec.map (CommRingCat.ofHom (IsLocalRing.residue B)) ≫ t)
    ∀ a : SchemeHomOver (fractionInclusion B K ≫ t) f, a ^ m = 1 →
      specializationHom B K L t (IsLocalRing.ResidueField B) (IsLocalRing.residue B) a = 1 → a = 1 := by
  letI := L.pointGroup t
  letI := L.pointGroup (fractionInclusion B K ≫ t)
  letI := L.pointGroup (Spec.map (CommRingCat.ofHom (IsLocalRing.residue B)) ≫ t)
  intro a ha hred
  let e : SchemeHomOver t f ≃* SchemeHomOver (fractionInclusion B K ≫ t) f :=
    fractionPointGroupEquiv B K L t
  let x : SchemeHomOver t f := e.symm a
  have hxpow : x ^ m = 1 := by
    simpa only [map_pow, map_one] using congrArg e.symm ha
  have hxtor : L.IsTorsionPoint t m x := by
    change L.nsmul t m x = L.one t
    rw [← point_pow_eq_nsmul]
    exact hxpow
  have hred' : schemeHomOverComp (Spec.map (CommRingCat.ofHom (IsLocalRing.residue B))) rfl x =
      L.one (Spec.map (CommRingCat.ofHom (IsLocalRing.residue B)) ≫ t) := hred
  have hx : x = L.one t :=
    MazurTransfer.OriginalRelativeGroupTorsionKernelInterop.eq_one_of_isTorsionPoint_of_comp_residue_eq L hc t m hm x hxtor
      (hred'.trans (L.one_natural t _ (Spec.map (CommRingCat.ofHom (IsLocalRing.residue B))) rfl).symm)
  apply e.symm.injective
  exact hx.trans e.symm.map_one.symm
#print axioms solution
