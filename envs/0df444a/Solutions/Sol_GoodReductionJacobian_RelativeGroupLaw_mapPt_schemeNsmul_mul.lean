-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.mapPt_schemeNsmul_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/9ef8c316-3b6e-56ac-81e6-2707cf712883

import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_mapPt_schemeNsmul_mul

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

namespace K79HK

variable {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)

theorem inv_natural {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (t' : T' ⟶ Spec (CommRingCat.of R))
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (x : SchemeHomOver t f) :
    schemeHomOverComp ψ hψ (L.inv t x) = L.inv t' (schemeHomOverComp ψ hψ x) := by
  letI := L.pointGroup t'
  have h : schemeHomOverComp ψ hψ (L.inv t x) * schemeHomOverComp ψ hψ x = 1 := by
    change L.mul t' _ _ = L.one t'
    rw [← L.mul_natural t t' ψ hψ, L.inv_mul_cancel, L.one_natural t t' ψ hψ]
  exact eq_inv_of_mul_eq_one_left h

theorem schemeHomOverComp_idPoint {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P : SchemeHomOver t f) :
    schemeHomOverComp P.1 P.2 (RelativeGroupLaw.idPoint (f := f)) = P :=
  Subtype.ext (Category.comp_id _)

theorem mapPt_schemeNsmul (m : ℕ) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P : SchemeHomOver t f) :
    CerednikDrinfeld.QM.mapPt (L.schemeNsmul m) (L.schemeNsmul_over m) P = L.nsmul t m P := by
  have h := L.nsmul_natural f t P.1 P.2 m (RelativeGroupLaw.idPoint (f := f))
  rw [schemeHomOverComp_idPoint] at h
  rw [← h]
  rfl

theorem mapPt_negMor {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P : SchemeHomOver t f) :
    CerednikDrinfeld.QM.mapPt (Polarisation.negMor f L) (Polarisation.negMor_over f L) P = L.inv t P := by
  have h := inv_natural L f t P.1 P.2 (Polarisation.idPt f)
  have h2 : schemeHomOverComp P.1 P.2 (Polarisation.idPt f) = P := Subtype.ext (Category.comp_id _)
  rw [h2] at h
  rw [← h]
  rfl

theorem nsmul_mul (hc : L.IsCommutative) (m : ℕ) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f) :
    L.nsmul t m (L.mul t P Q) = L.mul t (L.nsmul t m P) (L.nsmul t m Q) := by
  letI : CommGroup (SchemeHomOver t f) := { L.pointGroup t with mul_comm := fun x y => hc t x y }
  have hpow : ∀ (x : SchemeHomOver t f) (n : ℕ), L.nsmul t n x = x ^ n := by
    intro x n
    induction n with
    | zero => rw [pow_zero]; rfl
    | succ n ih => rw [RelativeGroupLaw.nsmul_succ, ih, pow_succ]; rfl
  rw [hpow, hpow, hpow]
  exact mul_pow P Q m

end K79HK

open K79HK in
theorem solution
    {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (hc : L.IsCommutative) (m : ℕ)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f) :
    CerednikDrinfeld.QM.mapPt (L.schemeNsmul m) (L.schemeNsmul_over m) (L.mul t P Q) =
      L.mul t (CerednikDrinfeld.QM.mapPt (L.schemeNsmul m) (L.schemeNsmul_over m) P)
        (CerednikDrinfeld.QM.mapPt (L.schemeNsmul m) (L.schemeNsmul_over m) Q) := by
  rw [mapPt_schemeNsmul, mapPt_schemeNsmul, mapPt_schemeNsmul]
  exact nsmul_mul L hc m t P Q

end S_GoodReductionJacobian_RelativeGroupLaw_mapPt_schemeNsmul_mul
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_mapPt_schemeNsmul_mul (solution)
