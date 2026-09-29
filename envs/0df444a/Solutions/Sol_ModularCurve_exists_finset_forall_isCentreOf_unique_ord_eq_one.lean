-- Prove2me | solution 1 for ModularCurve.exists_finset_forall_isCentreOf_unique_ord_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/e2b1476e-a8a5-5d01-8da5-86ff9a94a894

import Mathlib
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldC_of_perfectField
import Theorems.Thm_ModularCurve_nonempty_modularPolynomialData
import Theorems.Thm_ModularCurve_ModularPolynomialData_separable_map_ratFunc_of_natCast_ne_zero
import Theorems.Thm_ModularCurve_CharPModel_place_eq_of_ord_pos_of_derivative_evalEval_ne_zero
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Definitions.Def_ModularCurve_CharLSpecialFibreLevelNDictionary
import Theorems.Thm_ModularCurve_place_deg_eq_one_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_Place_isRational_iff_deg_eq_one
import Theorems.Thm_ModularCurve_CharPModel_ord_sub_eq_one_of_derivative_evalEval_ne_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_finset_forall_isCentreOf_unique_ord_eq_one
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 800000

p2m_open "ModularCurve~coeffMap_injective AlgebraicCurve Polynomial"
open scoped Polynomial.Bivariate

namespace CofinD01

section PlaceHelpers

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (w : Place K F)

theorem mem_of_ord_nonneg {f : F} (h : 0 ≤ w.ord f) : f ∈ w.toValuationSubring := by
  by_cases hf0 : f = 0
  · rw [hf0]; exact zero_mem _
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible w.toValuationSubring
  obtain ⟨u, hu⟩ := w.exists_unit_mul_zpow hf0 hπ
  rw [hu, ← Int.toNat_of_nonneg h, zpow_natCast]
  exact mul_mem (u : w.toValuationSubring).2 (pow_mem π.2 _)

theorem mk_mem_maximalIdeal_of_ord_pos {f : F} (h : 0 < w.ord f) :
    (⟨f, mem_of_ord_nonneg w h.le⟩ : w.toValuationSubring) ∈
      IsLocalRing.maximalIdeal w.toValuationSubring := by
  rw [w.mem_maximalIdeal_iff_adicValuation_lt_one]
  by_cases hf0 : f = 0
  · subst hf0; simp
  have hne := w.adicValuation_ne_zero hf0
  rw [← WithZero.exp_log hne, ← WithZero.exp_zero, WithZero.exp_lt_exp]
  simp only [Place.ord] at h
  omega

theorem ord_pos_of_mem_maximalIdeal (a : w.toValuationSubring)
    (ha : a ∈ IsLocalRing.maximalIdeal w.toValuationSubring) (ha0 : (a : F) ≠ 0) :
    0 < w.ord (a : F) := by
  rw [w.mem_maximalIdeal_iff_adicValuation_lt_one] at ha
  have hne := w.adicValuation_ne_zero ha0
  rw [← WithZero.exp_log hne, ← WithZero.exp_zero, WithZero.exp_lt_exp] at ha
  simp only [Place.ord]
  omega

end PlaceHelpers

section Ev

variable (K : Type*) [Field K]

noncomputable def ev {A : Type*} [CommRing A] [Algebra K A] (x y : A) : K[X][Y] →+* A :=
  eval₂RingHom (aeval x : K[X] →ₐ[K] A).toRingHom y

variable {K}

theorem ev_C {A : Type*} [CommRing A] [Algebra K A] (x y : A) (p : K[X]) :
    ev K x y (C p) = aeval x p := by
  simp [ev]

theorem ev_X {A : Type*} [CommRing A] [Algebra K A] (x y : A) : ev K x y (X : K[X][Y]) = y := by
  simp [ev]

theorem map_ev (K) [Field K] {A B : Type*} [CommRing A] [Algebra K A] [CommRing B] [Algebra K B]
    (φ : A →+* B) (hφ : ∀ c : K, φ (algebraMap K A c) = algebraMap K B c) (x y : A)
    (P : K[X][Y]) : φ (ev K x y P) = ev K (φ x) (φ y) P := by
  have h : φ.comp (ev K x y) = ev K (φ x) (φ y) := by
    apply Polynomial.ringHom_ext
    · intro p
      rw [RingHom.comp_apply, ev_C, ev_C]
      have h2 : φ.comp (aeval x : K[X] →ₐ[K] A).toRingHom
          = (aeval (φ x) : K[X] →ₐ[K] B).toRingHom := by
        apply Polynomial.ringHom_ext
        · intro c
          simp [hφ]
        · simp
      exact congrArg (fun g : K[X] →+* B => g p) h2
    · rw [RingHom.comp_apply, ev_X, ev_X]
  exact congrArg (fun g : K[X][Y] →+* B => g P) h

theorem ev_self (s t : K) (P : K[X][Y]) : ev K s t P = P.evalEval s t := by
  have h : (aeval s : K[X] →ₐ[K] K).toRingHom = evalRingHom s := by
    ext p
    · simp
    · simp
  show eval₂ (aeval s : K[X] →ₐ[K] K).toRingHom t P = _
  rw [h, eval₂_evalRingHom]

noncomputable def evZ {A : Type*} [CommRing A] (x y : A) : ℤ[X][Y] →+* A :=
  eval₂RingHom (eval₂RingHom (Int.castRingHom A) x) y

theorem map_evZ {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B) (x y : A) (P : ℤ[X][Y]) :
    φ (evZ x y P) = evZ (φ x) (φ y) P := by
  have h : φ.comp (evZ x y) = evZ (φ x) (φ y) := by
    apply Polynomial.ringHom_ext
    · intro p
      simp only [evZ, RingHom.comp_apply, coe_eval₂RingHom, eval₂_C]
      rw [hom_eval₂]
      congr 1
      ext
      simp
    · simp [evZ]
  exact congrArg (fun g : ℤ[X][Y] →+* B => g P) h

theorem ev_map_intCast {A : Type*} [CommRing A] [Algebra K A] (x y : A) (P : ℤ[X][Y]) :
    ev K x y (P.map (mapRingHom (Int.castRingHom K))) = evZ x y P := by
  show eval₂ _ y (P.map _) = eval₂ _ y P
  rw [eval₂_map]
  congr 1
  ext <;> simp

theorem aeval_toRingHom_eq_evalZ {A : Type*} [CommRing A] [inst : Algebra ℤ A] (x y : A)
    (P : ℤ[X][Y]) : P.eval₂ (aeval (R := ℤ) x).toRingHom y = evZ x y P := by
  show _ = eval₂ _ y P
  congr 1
  ext <;> simp

end Ev

section ModEq

variable (K : Type*) [Field K] (N : ℕ) [NeZero N] (data : ModularPolynomialData N)

noncomputable abbrev PhiK : K[X][Y] := data.Φ.map (mapRingHom (Int.castRingHom K))

theorem coeffMap_injective {R S : Type*} [CommRing R] [CommRing S] {f : R →+* S}
    (hf : Function.Injective f) : Function.Injective (coeffMap f) := by
  intro a b hab
  ext k
  have := congrArg (fun z : LaurentSeries S => z.coeff k) hab
  exact hf (by simpa [coeffMap_coeff] using this)

theorem evZ_jq_eq_zero : evZ (jqModC K) (jqNModC K N) data.Φ = 0 := by
  have hQ : evZ (jqModC ℚ) (jqNModC ℚ N) data.Φ = 0 := by
    rw [← aeval_toRingHom_eq_evalZ]
    exact data.eval_eq_zero
  have hZ : evZ (jqModC ℤ) (jqNModC ℤ N) data.Φ = 0 := by
    apply coeffMap_injective (f := Int.castRingHom ℚ) (Int.castRingHom ℚ).injective_int
    rw [map_evZ, coeffMap_jqModC, coeffMap_jqNModC, map_zero]
    exact hQ
  have h := congrArg (coeffMap (Int.castRingHom K)) hZ
  rwa [map_evZ, coeffMap_jqModC, coeffMap_jqNModC, map_zero] at h

noncomputable abbrev jF : modularFunctionFieldC K N := ⟨jqModC K, jqModC_mem K N⟩
noncomputable abbrev jNF : modularFunctionFieldC K N := ⟨jqNModC K N, jqNModC_mem K N⟩

theorem ev_PhiK_F : ev K (jF K N) (jNF K N) (PhiK K N data) = 0 := by
  apply (algebraMap (modularFunctionFieldC K N) (LaurentSeries K)).injective
  rw [map_zero, map_ev K (algebraMap (modularFunctionFieldC K N) (LaurentSeries K)) (fun c => rfl),
    ev_map_intCast]
  exact evZ_jq_eq_zero K N data

theorem transcendental_jF : Transcendental K (jF K N) := by
  rw [← transcendental_algebraMap_iff (R := K)
    (algebraMap (modularFunctionFieldC K N) (LaurentSeries K)).injective]
  exact transcendental_jqModC K

theorem aeval_jF_injective :
    Function.Injective (aeval (jF K N) : K[X] →ₐ[K] modularFunctionFieldC K N) := by
  rw [injective_iff_map_eq_zero]
  exact transcendental_iff.mp (transcendental_jF K N)

theorem isUnit_aeval_jF (y : nonZeroDivisors K[X]) :
    IsUnit ((aeval (jF K N) : K[X] →ₐ[K] modularFunctionFieldC K N).toRingHom y) := by
  rw [isUnit_iff_ne_zero, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, ne_eq,
    map_eq_zero_iff _ (aeval_jF_injective K N)]
  exact nonZeroDivisors.coe_ne_zero y

noncomputable def psi : RatFunc K →+* modularFunctionFieldC K N :=
  IsLocalization.lift (M := nonZeroDivisors K[X]) (isUnit_aeval_jF K N)

theorem psi_algebraMap (p : K[X]) :
    psi K N (algebraMap K[X] (RatFunc K) p) = aeval (jF K N) p := by
  unfold psi
  rw [IsLocalization.lift_eq]
  rfl

theorem psi_comp_algebraMap :
    (psi K N).comp (algebraMap K[X] (RatFunc K))
      = (aeval (jF K N) : K[X] →ₐ[K] modularFunctionFieldC K N).toRingHom := by
  refine RingHom.ext fun p => ?_
  rw [RingHom.comp_apply, psi_algebraMap]
  rfl

theorem eval₂_psi_map (P : K[X][Y]) :
    eval₂ (psi K N) (jNF K N) (P.map (algebraMap K[X] (RatFunc K))) = ev K (jF K N) (jNF K N) P := by
  rw [eval₂_map, psi_comp_algebraMap]
  rfl

theorem ev_derivative_PhiK_ne_zero (hNK : (N : K) ≠ 0) :
    ev K (jF K N) (jNF K N) (derivative (PhiK K N data)) ≠ 0 := by
  obtain ⟨a, b, hab⟩ :=
    ModularPolynomialData.separable_map_ratFunc_of_natCast_ne_zero K N data hNK
  intro hD
  rw [derivative_map] at hab
  have h1 := congrArg (eval₂ (psi K N) (jNF K N)) hab
  rw [eval₂_add, eval₂_mul, eval₂_mul, eval₂_one, eval₂_psi_map, eval₂_psi_map, ev_PhiK_F, hD,
    mul_zero, mul_zero, zero_add] at h1
  exact zero_ne_one h1

end ModEq

section Local

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (Q : Place K F)

theorem exists_integral_repr {x : F} {s : K} (h : 0 < Q.ord (x - algebraMap K F s)) :
    ∃ xO : Q.toValuationSubring, (xO : F) = x ∧
      IsLocalRing.residue Q.toValuationSubring xO = algebraMap K Q.ResidueField s := by
  refine ⟨⟨x - algebraMap K F s, mem_of_ord_nonneg Q h.le⟩ + algebraMap K Q.toValuationSubring s,
    ?_, ?_⟩
  · show (x - algebraMap K F s) + ((algebraMap K Q.toValuationSubring s : Q.toValuationSubring) : F)
      = x
    rw [Place.coe_algebraMap, sub_add_cancel]
  · rw [map_add, (IsLocalRing.residue_eq_zero_iff _).mpr (mk_mem_maximalIdeal_of_ord_pos Q h),
      zero_add, IsScalarTower.algebraMap_apply K Q.toValuationSubring Q.ResidueField,
      IsLocalRing.ResidueField.algebraMap_eq]

theorem coe_ev (xO yO : Q.toValuationSubring) (P : K[X][Y]) :
    ((ev K xO yO P : Q.toValuationSubring) : F) = ev K (xO : F) (yO : F) P :=
  map_ev K (Q.toValuationSubring.subtype) (fun _ => rfl) xO yO P

theorem residue_ev (xO yO : Q.toValuationSubring) (s t : K)
    (hx : IsLocalRing.residue Q.toValuationSubring xO = algebraMap K Q.ResidueField s)
    (hy : IsLocalRing.residue Q.toValuationSubring yO = algebraMap K Q.ResidueField t)
    (P : K[X][Y]) :
    IsLocalRing.residue Q.toValuationSubring (ev K xO yO P)
      = algebraMap K Q.ResidueField (P.evalEval s t) := by
  rw [map_ev K (IsLocalRing.residue Q.toValuationSubring) (fun c => by
      rw [IsScalarTower.algebraMap_apply K Q.toValuationSubring Q.ResidueField,
        IsLocalRing.ResidueField.algebraMap_eq]) xO yO P,
    hx, hy, ← ev_self, ← map_ev K (algebraMap K Q.ResidueField) (fun _ => rfl) s t P]

variable {Q}

theorem evalEval_eq_zero_of_ev_eq_zero {x y : F} {s t : K}
    (h1 : 0 < Q.ord (x - algebraMap K F s)) (h2 : 0 < Q.ord (y - algebraMap K F t))
    (P : K[X][Y]) (hP : ev K x y P = 0) : P.evalEval s t = 0 := by
  obtain ⟨xO, hxF, hxr⟩ := exists_integral_repr Q h1
  obtain ⟨yO, hyF, hyr⟩ := exists_integral_repr Q h2
  have h0 : ev K xO yO P = 0 := by
    apply Subtype.val_injective
    rw [coe_ev, hxF, hyF, hP]
    rfl
  have := residue_ev Q xO yO s t hxr hyr P
  rw [h0, map_zero] at this
  exact (map_eq_zero _).mp this.symm

theorem ord_ev_pos {x y : F} {s t : K}
    (h1 : 0 < Q.ord (x - algebraMap K F s)) (h2 : 0 < Q.ord (y - algebraMap K F t))
    (P : K[X][Y]) (hP : P.evalEval s t = 0) (hne : ev K x y P ≠ 0) : 0 < Q.ord (ev K x y P) := by
  obtain ⟨xO, hxF, hxr⟩ := exists_integral_repr Q h1
  obtain ⟨yO, hyF, hyr⟩ := exists_integral_repr Q h2
  have hmem : ev K xO yO P ∈ IsLocalRing.maximalIdeal Q.toValuationSubring := by
    rw [← IsLocalRing.residue_eq_zero_iff, residue_ev Q xO yO s t hxr hyr P, hP, map_zero]
  have hcoe : ((ev K xO yO P : Q.toValuationSubring) : F) = ev K x y P := by
    rw [coe_ev, hxF, hyF]
  rw [← hcoe]
  exact ord_pos_of_mem_maximalIdeal Q _ hmem (by rw [hcoe]; exact hne)

end Local

end CofinD01

open CofinD01 in
theorem solution
    (q : ℕ) (k : Type*) [Field k] [Fact q.Prime] [CharP k q] [IsAlgClosed k]
    (N : ℕ) [NeZero N] (hqN : ¬ q ∣ N) :
    ∃ B : Finset (Place k ↥(modularFunctionFieldC k N)),
      ∀ v ∉ B, IsAffineGeomPlace k N v →
        ∃ c : k × k, IsCentreOf k N c v ∧
          (∀ v' : Place k ↥(modularFunctionFieldC k N), IsCentreOf k N c v' → v' = v) ∧
          (v.ord (jGeomGen k N - algebraMap k ↥(modularFunctionFieldC k N) c.1) = 1 ∨
            v.ord (jNGeomGen k N - algebraMap k ↥(modularFunctionFieldC k N) c.2) = 1) := by
  classical
  haveI : IsCurveOver k (modularFunctionFieldC k N) :=
    isCurveOver_modularFunctionFieldC_of_perfectField k N
  obtain ⟨data⟩ := nonempty_modularPolynomialData N
  have hNK : (N : k) ≠ 0 := fun h => hqN ((CharP.cast_eq_zero_iff k q N).mp h)

  have hfin : ∀ f : modularFunctionFieldC k N, ∃ S : Finset (Place k (modularFunctionFieldC k N)),
      ∀ v : Place k (modularFunctionFieldC k N), v.ord f ≠ 0 → v ∈ S := by
    intro f
    by_cases hf : f = 0
    · exact ⟨∅, fun v hv => (hv (by rw [hf, Place.ord_zero])).elim⟩
    · obtain ⟨D, hD, -⟩ := HasPrincipalDivisors.exists_divisor (K := k) f hf
      exact ⟨D.support, fun v hv => Finsupp.mem_support_iff.mpr (by rw [hD v]; exact hv)⟩
  choose S hS using hfin

  have hDv0 := ev_derivative_PhiK_ne_zero k N data hNK

  refine ⟨S (ev k (jF k N) (jNF k N) (derivative (PhiK k N data))), ?_⟩
  intro v hvB haff

  have hrat : v.IsRational :=
    (Place.isRational_iff_deg_eq_one v).mpr (place_deg_eq_one_of_isAlgClosed k N v)
  have hc : IsCentreOf k N (v.evalAt (jGeomGen k N), v.evalAt (jNGeomGen k N)) v :=
    exists_isCentreOf_of_isRational hrat haff
  refine ⟨(v.evalAt (jGeomGen k N), v.evalAt (jNGeomGen k N)), hc, ?_, ?_⟩
  ·
    have hroot : (PhiK k N data).evalEval (v.evalAt (jGeomGen k N)) (v.evalAt (jNGeomGen k N))
        = 0 :=
      evalEval_eq_zero_of_ev_eq_zero hc.1 hc.2 (PhiK k N data) (ev_PhiK_F k N data)
    have hder : (derivative (PhiK k N data)).evalEval (v.evalAt (jGeomGen k N))
        (v.evalAt (jNGeomGen k N)) ≠ 0 := fun hz =>
      hvB (hS _ v (ord_ev_pos hc.1 hc.2 _ hz hDv0).ne')
    intro v' hv'
    exact CharPModel.place_eq_of_ord_pos_of_derivative_evalEval_ne_zero N data _ _ hroot hder
      v' v hv'.1 hv'.2 hc.1 hc.2
  · have hder : (derivative (PhiK k N data)).evalEval (v.evalAt (jGeomGen k N))
        (v.evalAt (jNGeomGen k N)) ≠ 0 := fun hz =>
      hvB (hS _ v (ord_ev_pos hc.1 hc.2 _ hz hDv0).ne')
    exact Or.inl (CharPModel.ord_sub_eq_one_of_derivative_evalEval_ne_zero N data _ _ hder
      v hc.1 hc.2)

end S_ModularCurve_exists_finset_forall_isCentreOf_unique_ord_eq_one
end P2MW
export P2MW.S_ModularCurve_exists_finset_forall_isCentreOf_unique_ord_eq_one (solution)
