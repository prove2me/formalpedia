-- Prove2me | solution 1 for ModularCurve.degeneracyPair_finite_separable_identity_ssPlaces
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/22dd700a-f137-594b-9a71-b63a93d90052

import Mathlib
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_ModularCurve_CharLDegeneracyHecke
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_ModularCurve_finiteAlong_heckeAlphaC
import Theorems.Thm_ModularCurve_finiteAlong_heckeBetaC
import Theorems.Thm_ModularCurve_separableAlong_heckeAlphaC_heckeBetaC
import Theorems.Thm_ModularCurve_charLDegeneracyRoof_eq_modularFunctionFieldFullC_mul
import Theorems.Thm_ModularCurve_modularFunctionFieldC_eq_modularFunctionFieldFullC_of_charP_pos
import Theorems.Thm_AlgebraicCurve_Place_evalAt_algebraMap_eq_evalAt_restrict
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldC_of_perfectField
import Theorems.Thm_AlgebraicCurve_Place_isRational_iff_deg_eq_one
import Theorems.Thm_ModularCurve_nonempty_modularPolynomialData
import Theorems.Thm_AlgebraicCurve_Place_mem_toValuationSubring_of_isIntegral_adjoin
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_degeneracyPair_finite_separable_identity_ssPlaces
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois"

set_option autoImplicit false

open AlgebraicCurve ModularCurve

namespace DegPair

section Transport

variable {k L : Type*} [Field k] [Field L] [Algebra k L]

theorem algHom_eq_of_coe_eq {A E : IntermediateField k L} (ψ ψ' : ↥A →ₐ[k] ↥E)
    (h : ∀ x, (ψ x : L) = (ψ' x : L)) : ψ = ψ' :=
  AlgHom.ext fun x => Subtype.ext (h x)

theorem finiteAlong_transport {A E₁ E₂ : IntermediateField k L} (hE : E₁ = E₂)
    (ψ₁ : ↥A →ₐ[k] ↥E₁) (ψ₂ : ↥A →ₐ[k] ↥E₂) (h : ∀ x, (ψ₁ x : L) = (ψ₂ x : L))
    (hf : FiniteAlong k ψ₁) : FiniteAlong k ψ₂ := by
  subst hE
  rw [← algHom_eq_of_coe_eq ψ₁ ψ₂ h]; exact hf

theorem separableAlong_transport {A E₁ E₂ : IntermediateField k L} (hE : E₁ = E₂)
    (ψ₁ : ↥A →ₐ[k] ↥E₁) (ψ₂ : ↥A →ₐ[k] ↥E₂) (h : ∀ x, (ψ₁ x : L) = (ψ₂ x : L))
    (hf : SeparableAlong k ψ₁) : SeparableAlong k ψ₂ := by
  subst hE
  rw [← algHom_eq_of_coe_eq ψ₁ ψ₂ h]; exact hf

end Transport

section Places

variable (K : Type*) [Field K] [IsAlgClosed K] (N : ℕ) [NeZero N]

theorem isRational (x : Place K ↥(modularFunctionFieldC K N)) : x.IsRational := by
  haveI := isCurveOver_modularFunctionFieldC_of_perfectField K N
  exact (Place.isRational_iff_deg_eq_one x).2 (IsCurveOver.deg_eq_one_of_isAlgClosed x)

omit [IsAlgClosed K] in

theorem isIntegral_jNGeomGen :
    IsIntegral (Algebra.adjoin K ({jGeomGen K N} : Set ↥(modularFunctionFieldC K N))) (jNGeomGen K N) := by
  obtain ⟨data⟩ := nonempty_modularPolynomialData N
  set A := Algebra.adjoin K ({jGeomGen K N} : Set ↥(modularFunctionFieldC K N)) with hA
  have hjA : jGeomGen K N ∈ A := Algebra.subset_adjoin rfl
  let g : Polynomial ℤ →+* ↥A := Polynomial.eval₂RingHom (Int.castRingHom ↥A) ⟨jGeomGen K N, hjA⟩
  have hg : (algebraMap ↥A ↥(modularFunctionFieldC K N)).comp g
      = Polynomial.eval₂RingHom (Int.castRingHom ↥(modularFunctionFieldC K N)) (jGeomGen K N) := by
    refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
    simp [g]
  refine ⟨data.Φ.map g, data.monic.map g, ?_⟩
  rw [Polynomial.eval₂_map, hg]
  exact evalModularPair_jGeomGen_eq_zero K N data

omit [IsAlgClosed K] in
theorem isAffineGeomPlace_of_mem (x : Place K ↥(modularFunctionFieldC K N))
    (hj : jGeomGen K N ∈ x.toValuationSubring) : IsAffineGeomPlace K N x :=
  ⟨hj, x.mem_toValuationSubring_of_isIntegral_adjoin hj (isIntegral_jNGeomGen K N)⟩

end Places

section Alpha

variable (q' : ℕ) (M s : ℕ) [NeZero M] [NeZero s] [NeZero (M * s)]
  {k : Type*} [Field k] [IsAlgClosed k] [DecidableEq k]
  (φ₀ : ↥(modularFunctionFieldC k M) →ₐ[k] ↥(modularFunctionFieldC k (M * s)))
  (hφ₀ : φ₀.toRingHom.IsIntegral)
  (hφα : ∀ x, ((φ₀ x : ↥(modularFunctionFieldC k (M * s))) : LaurentSeries k) = x)

include hφα in
theorem map_jGeomGen : φ₀ (jGeomGen k M) = jGeomGen k (M * s) :=
  Subtype.ext (by rw [hφα]; rfl)

include hφα in

theorem ssPlaces_alpha (p : Place k ↥(modularFunctionFieldC k (M * s))) :
    p ∈ ssPlaces q' (M * s) k ↔ Place.restrictAlong φ₀ hφ₀ p ∈ ssPlaces q' M k := by
  letI := algebraAlong φ₀
  haveI := isScalarTower_along φ₀
  haveI := isIntegral_along φ₀ hφ₀
  have hres : Place.restrictAlong φ₀ hφ₀ p = p.restrict ↥(modularFunctionFieldC k M) := rfl
  have hratM := isRational k M (Place.restrictAlong φ₀ hφ₀ p)
  have hratMs := isRational k (M * s) p

  have hjmem : jGeomGen k M ∈ (Place.restrictAlong φ₀ hφ₀ p).toValuationSubring ↔
      jGeomGen k (M * s) ∈ p.toValuationSubring := by
    rw [hres, Place.mem_restrict_iff, show algebraMap _ _ (jGeomGen k M) = φ₀ (jGeomGen k M) from rfl,
      map_jGeomGen M s φ₀ hφα]

  have hval : jGeomGen k (M * s) ∈ p.toValuationSubring →
      (Place.restrictAlong φ₀ hφ₀ p).evalAt (jGeomGen k M) = p.evalAt (jGeomGen k (M * s)) := by
    intro hmem
    rw [hres, ← map_jGeomGen M s φ₀ hφα, show φ₀ (jGeomGen k M) = algebraMap _ _ (jGeomGen k M) from rfl]
    refine (Place.evalAt_algebraMap_eq_evalAt_restrict p (hres ▸ hratM) ?_).symm
    rw [Place.mem_restrict_iff, show algebraMap _ _ (jGeomGen k M) = φ₀ (jGeomGen k M) from rfl,
      map_jGeomGen M s φ₀ hφα]
    exact hmem
  rw [mem_ssPlaces_iff, mem_ssPlaces_iff, isSupersingularPlace_iff, isSupersingularPlace_iff]
  constructor
  · rintro ⟨-, haff, hss⟩
    refine ⟨hratM, isAffineGeomPlace_of_mem k M _ (hjmem.2 haff.1), ?_⟩
    rw [hval haff.1]; exact hss
  · rintro ⟨-, haff, hss⟩
    have hj : jGeomGen k (M * s) ∈ p.toValuationSubring := hjmem.1 haff.1
    refine ⟨hratMs, isAffineGeomPlace_of_mem k (M * s) _ hj, ?_⟩
    rw [← hval hj]; exact hss

end Alpha

section FinSep

variable (M s q' : ℕ) [NeZero M] [NeZero s] (hs : s.Prime) [Fact q'.Prime]
  (hsq' : s ≠ q') (hq'M : ¬ q' ∣ M)
  {k : Type*} [Field k] [CharP k q'] [IsAlgClosed k]

include hs hsq' hq'M in
theorem not_dvd_mul : ¬ q' ∣ M * s := by
  intro h
  rcases (Nat.Prime.dvd_mul (Fact.out)).mp h with h1 | h2
  · exact hq'M h1
  · exact hsq' ((Nat.prime_dvd_prime_iff_eq (Fact.out) hs).mp h2).symm

include hs hsq' hq'M in

theorem roof_eq [NeZero (M * s)] : charLDegeneracyRoof k M s = modularFunctionFieldC k (M * s) := by
  haveI : NeZero q' := ⟨(Fact.out : q'.Prime).ne_zero⟩
  rw [charLDegeneracyRoof_eq_modularFunctionFieldFullC_mul k q' M s (not_dvd_mul M s q' hs hsq' hq'M),
    modularFunctionFieldC_eq_modularFunctionFieldFullC_of_charP_pos k q' (M * s) (not_dvd_mul M s q' hs hsq' hq'M)]

include hs hsq' hq'M in
theorem finite_separable [NeZero (M * s)]
    (φ : Fin 2 → (↥(modularFunctionFieldC k M) →ₐ[k] ↥(modularFunctionFieldC k (M * s))))
    (hφα : ∀ x, ((φ 0 x : ↥(modularFunctionFieldC k (M * s))) : LaurentSeries k) = x)
    (hφβ : ∀ x, ((φ 1 x : ↥(modularFunctionFieldC k (M * s))) : LaurentSeries k) = qExpand k s x) :
    (∀ i, FiniteAlong k (φ i)) ∧ (∀ i, SeparableAlong k (φ i)) := by
  haveI : Fact s.Prime := ⟨hs⟩
  have hR := roof_eq M s q' hs hsq' hq'M (k := k)
  have hcoeα : ∀ x, ((heckeAlphaC k M s x : ↥(charLDegeneracyRoof k M s)) : LaurentSeries k) =
      ((φ 0 x : ↥(modularFunctionFieldC k (M * s))) : LaurentSeries k) := fun x => by
    rw [coe_heckeAlphaC, hφα]
  have hcoeβ : ∀ x, ((heckeBetaC k M s x : ↥(charLDegeneracyRoof k M s)) : LaurentSeries k) =
      ((φ 1 x : ↥(modularFunctionFieldC k (M * s))) : LaurentSeries k) := fun x => by
    rw [coe_heckeBetaC, hφβ]
  obtain ⟨hsepα, hsepβ⟩ := separableAlong_heckeAlphaC_heckeBetaC k (ℓ := q') M s (not_dvd_mul M s q' hs hsq' hq'M)
  refine ⟨?_, ?_⟩
  · refine Fin.forall_fin_two.2 ⟨?_, ?_⟩
    · exact finiteAlong_transport hR _ _ hcoeα (finiteAlong_heckeAlphaC k M s)
    · exact finiteAlong_transport hR _ _ hcoeβ (finiteAlong_heckeBetaC k M s)
  · refine Fin.forall_fin_two.2 ⟨?_, ?_⟩
    · exact separableAlong_transport hR _ _ hcoeα hsepα
    · exact separableAlong_transport hR _ _ hcoeβ hsepβ

end FinSep

end DegPair

theorem solution
    (M s q' : ℕ) [NeZero M] [NeZero s] (hs : s.Prime) [Fact q'.Prime]
    (hsq' : s ≠ q') (hq'M : ¬ q' ∣ M) (hsM : ¬ s ∣ M)
    {k : Type*} [Field k] [CharP k q'] [IsAlgClosed k] [DecidableEq k] :
    haveI : NeZero (M * s) := ⟨Nat.mul_ne_zero (NeZero.ne M) (NeZero.ne s)⟩
    ∀ (φ : Fin 2 → (↥(modularFunctionFieldC k M) →ₐ[k] ↥(modularFunctionFieldC k (M * s))))
      (hφ : ∀ i, (φ i).toRingHom.IsIntegral)
      (hφα : ∀ x, ((φ 0 x : ↥(modularFunctionFieldC k (M * s))) : LaurentSeries k) = x)
      (hφβ : ∀ x, ((φ 1 x : ↥(modularFunctionFieldC k (M * s))) : LaurentSeries k)
        = qExpand k s x),
    (∀ i, FiniteAlong k (φ i)) ∧
    (∀ i, SeparableAlong k (φ i)) ∧
    (∀ (p : Place k ↥(modularFunctionFieldC k (M * s))),
      p ∈ ssPlaces q' (M * s) k →
        Place.restrictAlong (φ 0) (hφ 0) p ∈ ssPlaces q' M k) ∧
    (∀ (v : Place k ↥(modularFunctionFieldC k M)),
      v ∈ ssPlaces q' M k →
        ∀ p : Place k ↥(modularFunctionFieldC k (M * s)),
          Place.restrictAlong (φ 0) (hφ 0) p = v → p ∈ ssPlaces q' (M * s) k) := by
  intro φ hφ hφα hφβ
  haveI : NeZero (M * s) := ⟨Nat.mul_ne_zero (NeZero.ne M) (NeZero.ne s)⟩
  obtain ⟨hfin, hsep⟩ := DegPair.finite_separable M s q' hs hsq' hq'M (k := k) φ hφα hφβ
  refine ⟨hfin, hsep, fun p hp => ?_, fun v hv p hpv => ?_⟩
  · exact (DegPair.ssPlaces_alpha q' M s (φ 0) (hφ 0) hφα p).1 hp
  · exact (DegPair.ssPlaces_alpha q' M s (φ 0) (hφ 0) hφα p).2 (hpv ▸ hv)

end S_ModularCurve_degeneracyPair_finite_separable_identity_ssPlaces
end P2MW
export P2MW.S_ModularCurve_degeneracyPair_finite_separable_identity_ssPlaces (solution)
