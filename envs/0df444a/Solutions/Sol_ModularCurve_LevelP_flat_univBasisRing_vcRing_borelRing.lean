-- Prove2me | solution 1 for ModularCurve.LevelP.flat_univBasisRing_vcRing_borelRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/09d05a45-9e1d-5020-9781-9f6f7035394f

import Mathlib
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_KatzLevelPUniversal
import Definitions.Def_ModularCurve_KatzLevelPClassifyingMaps
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_LevelP_flat_univBasisRing_vcRing_borelRing

set_option autoImplicit false

universe u

noncomputable section

open Polynomial WeierstrassCurve

namespace ModularCurve
p2m_export "ModularCurve" "LevelP.PsiRoot LevelP.TorsionPointRing LevelP.BasisRing LevelP.UnivBasisRing LevelP.VCRing LevelP.BorelRing"
namespace LevelP
p2m_export "ModularCurve.LevelP" "PsiRoot torsionQuadratic TorsionPointRing TorsionPointRing.ofBase torsionPtCurve TwoPointRing indepDenom BasisRing pDelta UnivBase univCurve isUnit_natCast_univBase UnivBasisRing isUnit_natCast_univBasisRing VCPoly VCRing monic_borelQuadratic BorelQRing borelQCurve BorelPRing borelDenom BorelRing"
namespace FlatProof
p2m_open "ModularCurve.LevelP ModularCurve"

variable {B : Type u} [CommRing B]

def lc (n : ℤ) : ℤ := if Even n then n / 2 else n

theorem isUnit_lc (p : ℕ) (hp : IsUnit (p : B)) : IsUnit ((lc p : ℤ) : B) := by
  unfold lc
  split_ifs with h
  · obtain ⟨m, hm⟩ := h
    have hm' : (p : ℤ) / 2 = m := by omega
    rw [hm']
    have hp' : (p : B) = (m : B) * 2 := by
      have h1 : ((p : ℤ) : B) = ((m + m : ℤ) : B) := by rw [hm]
      push_cast at h1
      rw [h1]; ring
    rw [hp'] at hp
    exact isUnit_of_mul_isUnit_left hp
  · simpa only [Int.cast_natCast] using hp

theorem free_adjoinRoot_of_mul_coeff_eq_one (f : B[X]) (n : ℕ) (hdeg : f.natDegree ≤ n) (c : B)
    (hc : c * f.coeff n = 1) : Module.Free B (AdjoinRoot f) := by
  have hmonic : (C c * f).Monic :=
    monic_of_natDegree_le_of_coeff_eq_one n ((natDegree_C_mul_le _ _).trans hdeg) (by rw [coeff_C_mul, hc])
  have hunit : IsUnit (C c) := (isUnit_of_mul_isUnit_left (by rw [hc]; exact isUnit_one)).map C
  have hI : Ideal.span {C c * f} = Ideal.span {f} := Ideal.span_singleton_mul_left_unit hunit f
  let e : AdjoinRoot (C c * f) ≃ₐ[B] AdjoinRoot f := Ideal.quotientEquivAlgOfEq B hI
  haveI : Module.Free B (AdjoinRoot (C c * f)) := Module.Free.of_basis (AdjoinRoot.powerBasis' hmonic).basis
  exact Module.Free.of_equiv e.toLinearEquiv

theorem free_psiRoot (W : WeierstrassCurve B) (p : ℕ) (hp : IsUnit (p : B)) : Module.Free B (PsiRoot W p) := by
  obtain ⟨c, hc⟩ := (isUnit_lc p hp).exists_left_inv
  exact free_adjoinRoot_of_mul_coeff_eq_one (W.preΨ p) _ (W.natDegree_preΨ_le p) c
    (by rw [W.coeff_preΨ]; exact hc)

theorem monic_torsionQuadratic (W : WeierstrassCurve B) (p : ℕ) : (torsionQuadratic W p).Monic := by
  refine monic_of_natDegree_le_of_coeff_eq_one 2 ?_ ?_
  · rw [torsionQuadratic]
    refine (natDegree_sub_le _ _).trans (max_le ((natDegree_add_le _ _).trans (max_le ?_ ?_)) ?_)
    · exact natDegree_X_pow_le 2
    · exact (natDegree_C_mul_le _ _).trans (natDegree_X_le.trans one_le_two)
    · exact (natDegree_C _).le.trans (Nat.zero_le _)
  · rw [torsionQuadratic, coeff_sub, coeff_add, coeff_X_pow, coeff_C_mul_X, coeff_C]
    norm_num

theorem flat_torsionPointRing (W : WeierstrassCurve B) (p : ℕ) (hp : IsUnit (p : B)) :
    Module.Flat B (TorsionPointRing W p) := by
  haveI : Module.Free B (PsiRoot W p) := free_psiRoot W p hp
  haveI : Module.Free (PsiRoot W p) (TorsionPointRing W p) :=
    Module.Free.of_basis (AdjoinRoot.powerBasis' (monic_torsionQuadratic W p)).basis
  exact Module.Flat.trans B (PsiRoot W p) (TorsionPointRing W p)

theorem flat_basisRing (W : WeierstrassCurve B) (p : ℕ) (hp : IsUnit (p : B)) : Module.Flat B (BasisRing W p) := by
  haveI h1 : Module.Flat B (TorsionPointRing W p) := flat_torsionPointRing W p hp
  have hp' : IsUnit (p : TorsionPointRing W p) := by
    simpa only [map_natCast] using hp.map (TorsionPointRing.ofBase W p)
  haveI h2 : Module.Flat (TorsionPointRing W p) (TwoPointRing W p) := flat_torsionPointRing (torsionPtCurve W p) p hp'
  haveI h3 : Module.Flat B (TwoPointRing W p) := Module.Flat.trans B (TorsionPointRing W p) (TwoPointRing W p)
  haveI h4 : Module.Flat (TwoPointRing W p) (BasisRing W p) :=
    IsLocalization.flat (BasisRing W p) (Submonoid.powers (indepDenom W p))
  exact Module.Flat.trans B (TwoPointRing W p) (BasisRing W p)

theorem flat_int_transfer {M : Type*} [AddCommGroup M] (i₁ i₂ : Module ℤ M)
    (h : @Module.Flat ℤ M _ _ i₁) : @Module.Flat ℤ M _ _ i₂ := by
  have e : i₁ = i₂ := Subsingleton.elim _ _
  subst e
  exact h

theorem flat_ringHom_univBasisRing (p : ℕ) :
    ((algebraMap (UnivBase p) (UnivBasisRing p)).comp
      ((algebraMap (MvPolynomial (Fin 5) ℤ) (UnivBase p)).comp
        (algebraMap ℤ (MvPolynomial (Fin 5) ℤ)))).Flat := by
  refine RingHom.Flat.comp (RingHom.Flat.comp ?_ ?_) ?_
  · exact RingHom.flat_algebraMap_iff.mpr inferInstance
  · exact RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat (UnivBase p) (Submonoid.powers (pDelta p)))
  · haveI : Module.Flat (UnivBase p) (UnivBasisRing p) :=
      flat_basisRing (univCurve p) p (isUnit_natCast_univBase p)
    exact RingHom.flat_algebraMap_iff.mpr this

theorem flat_univBasisRing (p : ℕ) : Module.Flat ℤ (UnivBasisRing p) := by
  have h := flat_ringHom_univBasisRing p
  have e : ((algebraMap (UnivBase p) (UnivBasisRing p)).comp
      ((algebraMap (MvPolynomial (Fin 5) ℤ) (UnivBase p)).comp
        (algebraMap ℤ (MvPolynomial (Fin 5) ℤ)))) = algebraMap ℤ (UnivBasisRing p) :=
    RingHom.ext_int _ _
  rw [e, RingHom.flat_algebraMap_iff] at h
  exact flat_int_transfer _ _ h

theorem flat_vcRing (p : ℕ) : Module.Flat (UnivBasisRing p) (VCRing p) := by
  haveI : Module.Flat (VCPoly p) (VCRing p) :=
    IsLocalization.flat (VCRing p) (Submonoid.powers (MvPolynomial.X 0 : VCPoly p))
  exact Module.Flat.trans (UnivBasisRing p) (VCPoly p) (VCRing p)

theorem flat_borelRing (p a : ℕ) : Module.Flat (UnivBasisRing p) (BorelRing p a) := by
  haveI : Module.Free (UnivBasisRing p) (BorelQRing p a) :=
    Module.Free.of_basis (AdjoinRoot.powerBasis' (monic_borelQuadratic p a)).basis
  have hp : IsUnit (p : BorelQRing p a) := by
    simpa only [map_natCast] using
      (isUnit_natCast_univBasisRing p).map (algebraMap (UnivBasisRing p) (BorelQRing p a))
  haveI : Module.Flat (BorelQRing p a) (BorelPRing p a) := flat_torsionPointRing (borelQCurve p a) p hp
  haveI : Module.Flat (UnivBasisRing p) (BorelPRing p a) :=
    Module.Flat.trans (UnivBasisRing p) (BorelQRing p a) (BorelPRing p a)
  exact Localization.flat (BorelPRing p a) (Submonoid.powers (borelDenom p a))

end ModularCurve.LevelP.FlatProof

theorem solution (p : ℕ) :
    Module.Flat ℤ (ModularCurve.LevelP.UnivBasisRing p) ∧
      Module.Flat (ModularCurve.LevelP.UnivBasisRing p) (ModularCurve.LevelP.VCRing p) ∧
        ∀ a : ℕ, Module.Flat (ModularCurve.LevelP.UnivBasisRing p) (ModularCurve.LevelP.BorelRing p a) :=
  ⟨ModularCurve.LevelP.FlatProof.flat_univBasisRing p, ModularCurve.LevelP.FlatProof.flat_vcRing p,
    fun a => ModularCurve.LevelP.FlatProof.flat_borelRing p a⟩

end
end S_ModularCurve_LevelP_flat_univBasisRing_vcRing_borelRing
end P2MW
export P2MW.S_ModularCurve_LevelP_flat_univBasisRing_vcRing_borelRing (solution)
