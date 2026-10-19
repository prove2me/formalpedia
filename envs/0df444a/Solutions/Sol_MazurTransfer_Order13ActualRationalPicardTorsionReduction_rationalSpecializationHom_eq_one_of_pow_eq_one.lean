-- Prove2me | solution 1 for MazurTransfer.Order13ActualRationalPicardTorsionReduction.rationalSpecializationHom_eq_one_of_pow_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-17T10:09:01.342738+00:00
-- url     : https://prove2.me/submissions/ea2033e4-4411-4a4b-9f58-d3e22dc22440

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Uses the pinned Anthropic FLT relative-group residue torsion kernel theorem.
Design boundary: torsion detection by the actual mod-three and mod-five
specialization homomorphisms of the same integral Picard group.
Named downstream consumer: rational torsion bound of nineteen.
-/
import Mathlib
import Definitions.Def_MazurTransfer_Order13ActualRationalPicardSpecialization
import Definitions.Def_MazurTransfer_Order13LocalCoefficientResidueField
import Theorems.Thm_MazurTransfer_OriginalRelativeGroupTorsionKernelInterop_eq_one_of_isTorsionPoint_of_comp_residue_eq
noncomputable section
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open NeronModelInfra GoodReductionJacobian
open MazurTorsion.XOneThirteenProjectiveCurve
open MazurTransfer MazurTransfer.Order13IntegralSections MazurTransfer.Order13IntegralBase
open MazurTransfer.Order13SameIntegralPicardFamilyFiniteFibres
open MazurTransfer.Order13LocalIntegralCoefficientMaps
open MazurTransfer.Order13LocalCoefficientResidueField
open MazurTransfer.Order13ActualRationalPicardSpecialization
open MazurTransfer.ProperRelativeGroupValuationSpecialization
open MazurTransfer.ValuationRingProperPointRestriction

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the actual finite-field map of Z localized at q reflects
residue restriction equalities and makes every q-coprime integer a unit.
Named downstream consumer: torsion injectivity of rational Picard specialization.
-/


noncomputable section
namespace MazurTransfer.Order13RationalTorsionResidueHelpers20261017
open CategoryTheory AlgebraicGeometry
open Order13LocalIntegralCoefficientMaps Order13LocalCoefficientResidueField
variable (q : ℕ) [Fact q.Prime]

theorem natCast_isUnit (m : ℕ) (hm : ¬ q ∣ m) : IsUnit (m : LocalRing q) := by
  have hmem : (m : ℤ) ∈ (primeIdeal q).primeCompl := by
    change ¬ (m : ℤ) ∈ primeIdeal q
    rw [primeIdeal, Ideal.mem_span_singleton]
    exact fun h => hm (Int.natCast_dvd_natCast.mp h)
  simpa only [map_natCast] using
    (IsLocalization.map_units (LocalRing q) (⟨(m : ℤ),hmem⟩ : (primeIdeal q).primeCompl))

theorem finiteFieldSpec_factor :
    Spec.map (CommRingCat.ofHom (localFiniteFieldMap q)) =
      Spec.map (residueFieldIso q).toCommRingCatIso.hom ≫
        Spec.map (CommRingCat.ofHom (IsLocalRing.residue (LocalRing q))) := by
  rw [← Spec.map_comp]
  congr 1

theorem residue_comp_eq_of_finiteField_comp_eq {X : Scheme}
    (s e : Spec (.of (LocalRing q)) ⟶ X)
    (h : Spec.map (CommRingCat.ofHom (localFiniteFieldMap q)) ≫ s =
      Spec.map (CommRingCat.ofHom (localFiniteFieldMap q)) ≫ e) :
    Spec.map (CommRingCat.ofHom (IsLocalRing.residue (LocalRing q))) ≫ s =
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue (LocalRing q))) ≫ e := by
  rw [finiteFieldSpec_factor,Category.assoc,Category.assoc] at h
  exact (cancel_epi (Spec.map (residueFieldIso q).toCommRingCatIso.hom)).mp h

end MazurTransfer.Order13RationalTorsionResidueHelpers20261017



namespace MazurTransfer.Order13RationalTorsionResidueHelpers20261017
variable {R : Type u} [CommRing R] {X : Scheme.{u}} {f : X ⟶ Spec (.of R)}
theorem point_pow_eq_nsmul (L : RelativeGroupLaw R f)
    {T : Scheme.{u}} (t : T ⟶ Spec (.of R)) (m : ℕ) (x : SchemeHomOver t f) :
    (letI := L.pointGroup t; x ^ m) = L.nsmul t m x := by
  letI := L.pointGroup t
  induction m with
  | zero => rfl
  | succ m ih => rw [pow_succ, ih, RelativeGroupLaw.nsmul_succ]; rfl
end MazurTransfer.Order13RationalTorsionResidueHelpers20261017
open MazurTransfer.Order13RationalTorsionResidueHelpers20261017
theorem solution (q : ℕ) [Fact q.Prime] (hq : q=3 ∨ q=5)
    (D : RelativePic0Designation BaseRing (curveToBase BaseRing))
    (L : RelativeGroupLaw BaseRing D.toBase) (hc : L.IsCommutative) [IsProper D.toBase] :
    letI := L.pointGroup (Spec.map (CommRingCat.ofHom canonicalRationalMap))
    letI := L.pointGroup (Spec.map (CommRingCat.ofHom (canonicalFiniteFieldMap q hq)))
    ∀ (m : ℕ), ¬ q ∣ m →
      ∀ a : SchemeHomOver (Spec.map (CommRingCat.ofHom canonicalRationalMap)) D.toBase,
      a ^ m = 1 → rationalSpecializationHom q hq D L a = 1 → a = 1 := by
  let t := Spec.map (CommRingCat.ofHom (localBaseMap q hq))
  let tQ := Spec.map (CommRingCat.ofHom canonicalRationalMap)
  let tk := Spec.map (CommRingCat.ofHom (canonicalFiniteFieldMap q hq))
  letI := L.pointGroup t
  letI := L.pointGroup tQ
  letI := L.pointGroup tk
  letI := L.pointGroup (fractionInclusion (LocalRing q) ℚ ≫ t)
  let e : SchemeHomOver t D.toBase ≃* SchemeHomOver tQ D.toBase :=
    (fractionPointGroupEquiv (LocalRing q) ℚ L t).trans
      (pointGroupCongr L (localRationalSpec_comp q hq))
  intro m hm a ha hred
  let x : SchemeHomOver t D.toBase := e.symm a
  have hxpow : x ^ m = 1 := by
    simpa only [map_pow,map_one] using congrArg e.symm ha
  have hxtor : L.IsTorsionPoint t m x := by
    change L.nsmul t m x = L.one t
    rw [← point_pow_eq_nsmul]
    exact hxpow
  have hredval : Spec.map (CommRingCat.ofHom (localFiniteFieldMap q)) ≫ x.val = (L.one tk).val :=
    congrArg Subtype.val hred
  have hone : (L.one tk).val = Spec.map (CommRingCat.ofHom (localFiniteFieldMap q)) ≫ (L.one t).val := by
    have h := congrArg Subtype.val (L.one_natural t tk
      (Spec.map (CommRingCat.ofHom (localFiniteFieldMap q))) (localFiniteFieldSpec_comp q hq))
    exact h.symm
  have hres := residue_comp_eq_of_finiteField_comp_eq q x.val (L.one t).val (hredval.trans hone)
  have hx : x = L.one t :=
    MazurTransfer.OriginalRelativeGroupTorsionKernelInterop.eq_one_of_isTorsionPoint_of_comp_residue_eq L hc t m (natCast_isUnit q m hm)
      x hxtor (Subtype.ext hres)
  apply e.symm.injective
  exact hx.trans e.symm.map_one.symm
#print axioms solution
