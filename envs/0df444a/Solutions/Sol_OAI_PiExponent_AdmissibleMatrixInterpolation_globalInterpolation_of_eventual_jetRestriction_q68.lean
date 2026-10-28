-- Prove2me | solution 1 for OAI.PiExponent.AdmissibleMatrixInterpolation.globalInterpolation_of_eventual_jetRestriction_q68
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T09:35:50.282952+00:00
-- url     : https://prove2.me/submissions/ae84ec2f-5b70-4b63-9af0-ea2576204470

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ068A046
import Theorems.Thm_OAI_PiExponent_AdmissibleMatrixInterpolation_eventual_packets_of_eventual_jetRestriction_q68

section
-- module Solutions.OAIQ068_PI.PiExponent_Jets_JetGeometry
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.JetGeometry

noncomputable section

open MvPowerSeries

variable {σ R : Type*} [CommRing R]

theorem rationalWeightedIdeal_mul_le (v : σ → ℚ) (hv : ∀ i, 0 ≤ v i) (H K : ℚ) :
    (rationalWeightedIdeal v hv H : Ideal (MvPowerSeries σ R)) *
      rationalWeightedIdeal v hv K ≤ rationalWeightedIdeal v hv (H + K) := by
  classical
  apply Ideal.mul_le.mpr
  intro f hf g hg d hd
  rw [coeff_mul]
  apply Finset.sum_eq_zero
  intro ij hij
  have he : ij.1 + ij.2 = d := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
  by_cases hfirst : Finsupp.weight v ij.1 < H
  · rw [hf ij.1 hfirst, zero_mul]
  · have hsecond : Finsupp.weight v ij.2 < K := by
      apply lt_of_not_ge
      intro hsecond
      have hsum := add_le_add (le_of_not_gt hfirst) hsecond
      rw [← map_add, he] at hsum
      exact (not_le_of_gt hd) hsum
    rw [hg ij.2 hsecond, mul_zero]

theorem ideal_pow_le_rationalWeightedIdeal (v : σ → ℚ) (hv : ∀ i, 0 ≤ v i)
    (I : Ideal (MvPowerSeries σ R)) (H : ℚ)
    (hI : I ≤ rationalWeightedIdeal v hv H) (n : ℕ) :
    I ^ n ≤ rationalWeightedIdeal v hv (n * H) := by
  induction n with
  | zero =>
      intro f hf d hd
      have hzero := rational_weight_nonneg v hv d
      simp only [Nat.cast_zero, zero_mul] at hd
      exact False.elim ((not_lt_of_ge hzero) hd)
  | succ n ih =>
      rw [pow_succ, Nat.cast_add, Nat.cast_one, add_mul, one_mul]
      apply Ideal.mul_le.mpr
      intro f hf g hg
      exact (Ideal.mul_le.mp (rationalWeightedIdeal_mul_le v hv (n * H) H))
        f (ih hf) g (hI hg)

end

end PiExponent.JetGeometry

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Analysis_FormalLogTruncation
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.FormalLogTruncation

open MvPowerSeries
open scoped BigOperators

variable {R : Type*} [CommRing R]

theorem liftSeries_eq_toMvPowerSeries (m : ℕ) (f : PowerSeries R) :
    FormalLogJet.liftSeries m f = f.toMvPowerSeries (0 : Fin (m+1)) := by
  classical
  let e : Unit ↪ Fin (m+1) := ⟨fun _ => 0, fun a b _ => Subsingleton.elim a b⟩
  ext d
  rw [FormalLogJet.coeff_liftSeries]
  change (if d.tail = 0 then PowerSeries.coeff (d 0) f else 0) = coeff d (rename e f)
  by_cases ht : d.tail = 0
  · rw [ite_eq_left ht]
    have hd : d = Finsupp.single 0 (d 0) := by
      calc
        d = Finsupp.cons (d 0) d.tail := (Finsupp.cons_tail d).symm
        _ = Finsupp.single 0 (d 0) := by rw [ht, Finsupp.cons_zero_eq_single_zero]
    have he : Finsupp.embDomain e (Finsupp.single () (d 0)) = Finsupp.single 0 (d 0) := by
      rw [Finsupp.embDomain_single]
      rfl
    conv_rhs => rw [hd, ← he, coeff_embDomain_rename]
    rfl
  · rw [ite_eq_right ht]
    symm
    apply coeff_rename_eq_zero
    rintro ⟨x, hx⟩
    have hx' : x = Finsupp.single () (x ()) := by ext; simp
    rw [hx', Finsupp.mapDomain_single] at hx
    apply ht
    rw [← hx]
    ext i
    change (Finsupp.single (0 : Fin (m+1)) (x ())) i.succ = 0
    exact Finsupp.single_eq_of_ne (Fin.succ_ne_zero i)

@[simp] theorem shiftMap_liftSeries {m : ℕ} (tail : Fin m → PowerSeries R)
    (ht : ∀ i, PowerSeries.constantCoeff (tail i) = 0) (f : PowerSeries R) :
    shiftMap tail ht (FormalLogJet.liftSeries m f) = FormalLogJet.liftSeries m f := by
  rw [liftSeries_eq_toMvPowerSeries, shiftMap_toMvPowerSeries]

open JetGeometry

theorem rationalWeightedIdeal_prod {σ ι : Type*} (v : σ → ℚ) (hv : ∀ i, 0 ≤ v i)
    (s : Finset ι) (f : ι → MvPowerSeries σ R) (c : ι → ℚ)
    (hf : ∀ i ∈ s, f i ∈ rationalWeightedIdeal v hv (c i)) :
    ∏ i ∈ s, f i ∈ rationalWeightedIdeal v hv (∑ i ∈ s, c i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro d hd
    simp only [Finset.sum_empty] at hd
    exact False.elim ((not_lt_of_ge (rational_weight_nonneg v hv d)) hd)
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    exact Ideal.mul_le.mp (rationalWeightedIdeal_mul_le v hv (c i) (∑j∈s,c j))
      _ (hf i (Finset.mem_insert_self _ _)) _
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

theorem subst_mem_rationalWeightedIdeal {σ τ : Type*}
    (w : σ → ℚ) (v : τ → ℚ) (hw : ∀ i, 0 ≤ w i) (hv : ∀ i, 0 ≤ v i)
    (a : σ → MvPowerSeries τ R) (ha : HasSubst a)
    (hweight : ∀ i, a i ∈ rationalWeightedIdeal v hv (w i))
    (H : ℚ) (f : MvPowerSeries σ R) (hf : f ∈ rationalWeightedIdeal w hw H) :
    subst a f ∈ rationalWeightedIdeal v hv H := by
  classical
  intro d hd
  rw [coeff_subst ha]
  apply finsum_eq_zero_of_forall_eq_zero
  intro e
  by_cases he : coeff e f = 0
  · rw [he, zero_smul]
  have hHe : H ≤ Finsupp.weight w e := le_of_not_gt (fun h => he (hf e h))
  have hprod : e.prod (fun i n => a i ^ n) ∈
      rationalWeightedIdeal v hv (Finsupp.weight w e) := by
    rw [Finsupp.prod, Finsupp.weight_apply, Finsupp.sum]
    apply rationalWeightedIdeal_prod
    intro i hi
    have hp := Ideal.pow_mem_pow (hweight i) (e i)
    have hh := ideal_pow_le_rationalWeightedIdeal v hv
      (rationalWeightedIdeal v hv (w i)) (w i) le_rfl (e i) hp
    simpa only [nsmul_eq_mul] using hh
  rw [hprod d (hd.trans_le hHe), smul_zero]

theorem X_mem_rationalWeightedIdeal {σ : Type*} (v : σ → ℚ) (hv : ∀ i, 0 ≤ v i)
    (i : σ) : (X i : MvPowerSeries σ R) ∈ rationalWeightedIdeal v hv (v i) := by
  classical
  intro d hd
  rw [coeff_X]
  split_ifs with he
  · subst d
    simp only [Finsupp.weight_single, one_nsmul] at hd
    exact False.elim (lt_irrefl _ hd)
  · rfl

theorem shiftMap_mem_rationalWeightedIdeal {m : ℕ} (tail : Fin m → PowerSeries R)
    (ht : ∀ i, PowerSeries.constantCoeff (tail i) = 0)
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 ≤ v i)
    (hweight : ∀ i, (tail i).toMvPowerSeries (0 : Fin (m+1)) ∈
      rationalWeightedIdeal v hv (v i.succ)) (H : ℚ)
    (f : MvPowerSeries (Fin (m+1)) R) (hf : f ∈ rationalWeightedIdeal v hv H) :
    shiftMap tail ht f ∈ rationalWeightedIdeal v hv H := by
  rw [shiftMap_apply]
  apply subst_mem_rationalWeightedIdeal v v hv hv _ (shiftVars_hasSubst tail ht) _ H f hf
  intro i
  cases i using Fin.cases with
  | zero => exact X_mem_rationalWeightedIdeal v hv 0
  | succ i => exact Ideal.add_mem _ (X_mem_rationalWeightedIdeal v hv i.succ) (hweight i)

theorem rationalCoefficientPacket_eq_iff {σ : Type*} (v : σ → ℚ)
    (hv : ∀ i, 0 ≤ v i) (H : ℚ) (f g : MvPowerSeries σ R) :
    rationalCoefficientPacket v H f = rationalCoefficientPacket v H g ↔
      f - g ∈ rationalWeightedIdeal v hv H := by
  constructor
  · intro h d hd
    exact sub_eq_zero.mpr (congrFun h ⟨d,hd⟩)
  · intro h
    funext d
    exact sub_eq_zero.mp (h d.val d.property)

theorem rationalCoefficientPacket_surjective {σ : Type*} (v : σ → ℚ) (H : ℚ) :
    Function.Surjective (rationalCoefficientPacket (R := R) v H) := by
  classical
  intro p
  refine ⟨fun d => if hd : Finsupp.weight v d < H then p ⟨d,hd⟩ else 0, ?_⟩
  funext d
  exact dite_eq_left d.property

theorem shiftEquiv_mem_iff {m : ℕ} (tail : Fin m → PowerSeries R)
    (ht : ∀ i, PowerSeries.constantCoeff (tail i) = 0)
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 ≤ v i)
    (hweight : ∀ i, (tail i).toMvPowerSeries (0 : Fin (m+1)) ∈
      rationalWeightedIdeal v hv (v i.succ)) (H : ℚ) (f) :
    shiftEquiv tail ht f ∈ rationalWeightedIdeal v hv H ↔
      f ∈ rationalWeightedIdeal v hv H := by
  have hn : ∀ i, (-tail i).toMvPowerSeries (0 : Fin (m+1)) ∈
      rationalWeightedIdeal v hv (v i.succ) := by
    intro i
    rw [map_neg]
    intro d hd
    rw [map_neg, hweight i d hd, neg_zero]
  constructor
  · intro hf
    have h := shiftMap_mem_rationalWeightedIdeal (fun i => -tail i)
      (by simp [ht]) v hv hn H _ hf
    change (shiftEquiv tail ht).symm (shiftEquiv tail ht f) ∈ _ at h
    simpa only [AlgEquiv.symm_apply_apply] using h
  · exact shiftMap_mem_rationalWeightedIdeal tail ht v hv hweight H f

theorem logTail_mem_rationalWeightedIdeal {m : ℕ} (v : Fin (m+1) → ℚ)
    (hv : ∀ i, 0 ≤ v i) (T : ℕ) (H : ℚ) (hT : H ≤ (T : ℚ) * v 0) :
    (logTail T).toMvPowerSeries (0 : Fin (m+1)) ∈ rationalWeightedIdeal v hv H := by
  intro d hd
  rw [← liftSeries_eq_toMvPowerSeries, FormalLogJet.coeff_liftSeries]
  split_ifs with ht
  · have he : d = Finsupp.single 0 (d 0) := by
      calc
        d = Finsupp.cons (d 0) d.tail := (Finsupp.cons_tail d).symm
        _ = Finsupp.single 0 (d 0) := by rw [ht, Finsupp.cons_zero_eq_single_zero]
    have hdeg : (d 0 : ℚ) * v 0 < H := by
      calc
        (d 0 : ℚ) * v 0 = Finsupp.weight v (Finsupp.single 0 (d 0)) := by
          rw [Finsupp.weight_single, nsmul_eq_mul]
        _ = Finsupp.weight v d := congrArg _ he.symm
        _ < H := hd
    apply coeff_logTail_eq_zero
    by_contra hn
    have hcast : (T : ℚ) ≤ d 0 := by exact_mod_cast (Nat.le_of_not_gt hn)
    exact (not_lt_of_ge ((mul_le_mul_of_nonneg_right hcast (hv 0)).trans' hT)) hdeg
  · rfl

theorem shiftMap_truncatedFormalJet {m : ℕ} (c : Fin m → ℂ) (T : Fin m → ℕ)
    (P : PiExponentApprox.FramePolynomial m) :
    shiftMap (fun i => logTail (T i)) (fun i => logTail_constantCoeff (T i))
      (truncatedFormalJet c T P) = FormalLogJet.formalJet c P := by
  have he : (shiftMap (fun i => logTail (T i)) (fun i => logTail_constantCoeff (T i))).comp
      (truncatedFormalJet c T) = FormalLogJet.formalJet c := by
    apply MvPolynomial.algHom_ext
    intro i
    cases i using Fin.cases with
    | zero =>
      simp only [AlgHom.comp_apply, truncatedFormalJet, MvPolynomial.aeval_X,
        Fin.cases_zero, FormalLogJet.formalJet_Y, map_add, map_one, shiftMap_X_zero]
    | succ i =>
      simp only [AlgHom.comp_apply, truncatedFormalJet, MvPolynomial.aeval_X,
        Fin.cases_succ, FormalLogJet.formalJet_X, map_add,
        shiftMap_X_succ, shiftMap_liftSeries]
      rw [← liftSeries_eq_toMvPowerSeries, logTail, map_sub, FormalLogJet.formalLog]
      have hc : shiftMap (fun i => logTail (T i)) (fun i => logTail_constantCoeff (T i))
          (C (c i)) = C (c i) := (shiftMap _ _).commutes (c i)
      rw [hc]
      ring
  exact DFunLike.congr_fun he P

theorem packets_surjective_comp_equiv {σ α J : Type*} (v : σ → ℚ)
    (hv : ∀ i, 0 ≤ v i) (H : ℚ)
    (e : MvPowerSeries σ R ≃ₐ[R] MvPowerSeries σ R)
    (he : ∀ f ∈ rationalWeightedIdeal v hv H, e f ∈ rationalWeightedIdeal v hv H)
    (f : α → J → MvPowerSeries σ R)
    (hf : Function.Surjective (fun a j => rationalCoefficientPacket v H (f a j))) :
    Function.Surjective (fun a j => rationalCoefficientPacket v H (e (f a j))) := by
  intro p
  choose F hF using fun j => rationalCoefficientPacket_surjective (R := R) v H (p j)
  obtain ⟨a,ha⟩ := hf (fun j => rationalCoefficientPacket v H (e.symm (F j)))
  refine ⟨a, ?_⟩
  funext j
  have hdiff := he _ ((rationalCoefficientPacket_eq_iff v hv H _ _).mp (congrFun ha j))
  rw [map_sub, e.apply_symm_apply] at hdiff
  exact ((rationalCoefficientPacket_eq_iff v hv H _ _).mpr hdiff).trans (hF j)

theorem packets_surjective_comp_equiv_iff {σ α J : Type*} (v : σ → ℚ)
    (hv : ∀ i, 0 ≤ v i) (H : ℚ)
    (e : MvPowerSeries σ R ≃ₐ[R] MvPowerSeries σ R)
    (he : ∀ f ∈ rationalWeightedIdeal v hv H, e f ∈ rationalWeightedIdeal v hv H)
    (hi : ∀ f ∈ rationalWeightedIdeal v hv H, e.symm f ∈ rationalWeightedIdeal v hv H)
    (f : α → J → MvPowerSeries σ R) :
    Function.Surjective (fun a j => rationalCoefficientPacket v H (e (f a j))) ↔
      Function.Surjective (fun a j => rationalCoefficientPacket v H (f a j)) := by
  constructor
  · intro h
    simpa only [e.symm_apply_apply] using
      packets_surjective_comp_equiv v hv H e.symm hi (fun a j => e (f a j)) h
  · exact packets_surjective_comp_equiv v hv H e he f

theorem formalLog_packets_surjective_iff_truncated {m : ℕ} {α J : Type*}
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 ≤ v i) (H : ℚ)
    (T : Fin m → ℕ) (hT : ∀ i, v i.succ ≤ (T i : ℚ) * v 0)
    (c : J → Fin m → ℂ) (P : α → PiExponentApprox.FramePolynomial m) :
    Function.Surjective (fun a j => rationalCoefficientPacket v H (FormalLogJet.formalJet (c j) (P a))) ↔
      Function.Surjective (fun a j => rationalCoefficientPacket v H (truncatedFormalJet (c j) T (P a))) := by
  let tail := fun i => logTail (T i)
  let ht := fun i => logTail_constantCoeff (T i)
  let e := shiftEquiv tail ht
  have hw : ∀ i, (tail i).toMvPowerSeries (0 : Fin (m+1)) ∈
      rationalWeightedIdeal v hv (v i.succ) :=
    fun i => logTail_mem_rationalWeightedIdeal v hv (T i) (v i.succ) (hT i)
  have he : ∀ f ∈ rationalWeightedIdeal v hv H, e f ∈ rationalWeightedIdeal v hv H :=
    fun f hf => (shiftEquiv_mem_iff tail ht v hv hw H f).mpr hf
  have hi : ∀ f ∈ rationalWeightedIdeal v hv H, e.symm f ∈ rationalWeightedIdeal v hv H := by
    intro f hf
    apply (shiftEquiv_mem_iff tail ht v hv hw H (e.symm f)).mp
    change e (e.symm f) ∈ rationalWeightedIdeal v hv H
    simpa only [AlgEquiv.apply_symm_apply] using hf
  have hh := packets_surjective_comp_equiv_iff v hv H e he hi
    (fun a j => truncatedFormalJet (c j) T (P a))
  simpa only [e, tail, ht, shiftEquiv_apply, shiftMap_truncatedFormalJet] using hh

end PiExponent.FormalLogTruncation

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_InterpolationMatrix
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

namespace PiExponent.InterpolationMatrix

theorem sectionImage_coeff {m : ℕ} {C : Type*} [Fintype C]
    (r : Fin m → ℂ) (G : Fin m → Polynomial ℂ)
    (h : C → ℕ) (a : C → Fin m → ℕ) (x : C → ℂ)
    (j s : ℕ) (b : Fin m → ℕ) :
    ((sectionImage r G h a x j).coeff (exponentVector b)).coeff s =
      ∑ c, entry r G j s b (h c) (a c) * x c := by
  classical
  simp only [sectionImage, MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul,
    Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, entry]
  apply Finset.sum_congr rfl
  intro c hc
  exact mul_comm _ _

theorem linearEvaluation_apply {m : ℕ} (K : ℕ) (w0 v0 θ : ℝ)
    (w : Fin m → ℝ) (H : ℝ) (r : Fin m → ℂ) (G : Fin m → Polynomial ℂ)
    (x : Column w0 w H → ℂ) (ρ : Row K v0 θ w H) :
    linearEvaluation K w0 v0 θ w H r G x ρ =
      ∑ c, entry r G ρ.1.val (ρ.2.1 0) (fun i => ρ.2.1 i.succ)
        (c.1 0) (fun i => c.1 i.succ) * x c := rfl

theorem linearEvaluation_eq_coeff {m : ℕ} (K : ℕ) (w0 v0 θ : ℝ)
    (w : Fin m → ℝ) (H : ℝ) (r : Fin m → ℂ) (G : Fin m → Polynomial ℂ)
    (x : Column w0 w H → ℂ) (ρ : Row K v0 θ w H) :
    linearEvaluation K w0 v0 θ w H r G x ρ =
      ((sectionImage r G (fun c : Column w0 w H => c.1 0)
        (fun c i => c.1 i.succ) x ρ.1.val).coeff
          (exponentVector (fun i => ρ.2.1 i.succ))).coeff (ρ.2.1 0) := by
  rw [linearEvaluation_apply, sectionImage_coeff]

end PiExponent.InterpolationMatrix

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Polynomials_AuxiliaryPolynomial
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators
open Filter Topology

namespace PiExponent

theorem exponentVector_injective {d : ℕ} :
    Function.Injective (@InterpolationMatrix.exponentVector d) := by
  intro a b h
  funext i
  have hi := congrArg (fun v : Fin d →₀ ℕ => v i) h
  simpa only [InterpolationMatrix.exponentVector_apply] using hi

@[simp] theorem polynomialOfCoefficients_coeff {d : ℕ} (S : Finset (Fin d → ℕ))
    (x : S → ℂ) (a : S) :
    (polynomialOfCoefficients S x).coeff (InterpolationMatrix.exponentVector a.val) = x a := by
  classical
  change (∑ exponent : S, MvPolynomial.monomial
    (InterpolationMatrix.exponentVector exponent.val) (x exponent)).coeff
      (InterpolationMatrix.exponentVector a.val) = x a
  simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
  rw [Finset.sum_eq_single a]
  · simp
  · intro b hb hba
    have hne : InterpolationMatrix.exponentVector b.val ≠
        InterpolationMatrix.exponentVector a.val := by
      intro h
      exact hba (Subtype.ext (exponentVector_injective h))
    simp [hne]
  · simp

theorem polynomialOfCoefficients_support {d : ℕ} (S : Finset (Fin d → ℕ))
    (x : S → ℂ) :
    (polynomialOfCoefficients S x).support ⊆ S.image InterpolationMatrix.exponentVector := by
  classical
  intro e he
  by_contra hn
  have hzero : (polynomialOfCoefficients S x).coeff e = 0 := by
    change (∑ exponent : S, MvPolynomial.monomial
      (InterpolationMatrix.exponentVector exponent.val) (x exponent)).coeff e = 0
    rw [MvPolynomial.coeff_sum]
    apply Finset.sum_eq_zero
    intro a ha
    have hne : InterpolationMatrix.exponentVector a.val ≠ e := by
      intro h
      exact hn (Finset.mem_image.mpr ⟨a.val, a.property, h⟩)
    simp [MvPolynomial.coeff_monomial, hne]
  exact (MvPolynomial.mem_support_iff.mp he) hzero

end PiExponent

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Jets_FormalJetIndices
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponent.FormalMatrixBridge

theorem polynomialOfCoefficients_of_weighted {m : ℕ}
    (W : Fin (m + 1) → ℝ) (hW : ∀ i, 0 < W i) (H : ℝ)
    (p : PiExponentApprox.FramePolynomial m)
    (hp : PiExponentApprox.HasWeightedDegreeLE W H p) :
    polynomialOfCoefficients (realWeightedSimplex W H)
      (fun a => p.coeff (InterpolationMatrix.exponentVector a.val)) = p := by
  classical
  ext d
  by_cases hd : (fun i => d i) ∈ realWeightedSimplex W H
  · have he := polynomialOfCoefficients_coeff (realWeightedSimplex W H)
      (fun a => p.coeff (InterpolationMatrix.exponentVector a.val))
      ⟨fun i => d i, hd⟩
    simpa only [exponentVector_coe] using he
  · have hpzero : p.coeff d = 0 := by
      by_contra hne
      apply hd
      apply (mem_realWeightedSimplex hW).mpr
      simpa only [PiExponentApprox.monomialWeight, mul_comm] using
        hp d (MvPolynomial.mem_support_iff.mpr hne)
    rw [hpzero]
    by_contra hne
    have hmem := MvPolynomial.mem_support_iff.mpr hne
    obtain ⟨a, ha, he⟩ := Finset.mem_image.mp
      (polynomialOfCoefficients_support _ _ hmem)
    apply hd
    have hea : a = fun i => d i := by
      funext i
      simpa only [InterpolationMatrix.exponentVector_apply] using
        congrArg (fun e : Fin (m + 1) →₀ ℕ => e i) he
    simpa only [← hea] using ha

end PiExponent.FormalMatrixBridge

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_DeterminantContradiction
attribute [-instance] _root_.OAI.PiExponent.AdmissibleBlowupGeometry.affineChart_isOpenImmersion _root_.OAI.PiExponent.AdmissibleBlowupGeometry.affineChart_quasiCompact _root_.OAI.PiExponent.AdmissibleBlowupGeometry.blowup_compact _root_.OAI.PiExponent.AdmissibleBlowupGeometry.blowup_isIntegral _root_.OAI.PiExponent.AdmissibleBlowupGeometry.blowup_isLocallyNoetherian _root_.OAI.PiExponent.AdmissibleBlowupGeometry.blowup_isNoetherian _root_.OAI.PiExponent.AdmissibleBlowupGeometry.compactificationStructureMap_proper _root_.OAI.PiExponent.AdmissibleBlowupGeometry.compactification_compact _root_.OAI.PiExponent.AdmissibleBlowupGeometry.compactification_isIntegral _root_.OAI.PiExponent.AdmissibleBlowupGeometry.compactification_isLocallyNoetherian _root_.OAI.PiExponent.AdmissibleBlowupGeometry.compactification_isNoetherian _root_.OAI.PiExponent.AdmissibleBlowupGeometry.compactification_nonempty _root_.OAI.PiExponent.AdmissibleBlowupGeometry.index_nonempty _root_.OAI.PiExponent.AdmissibleBlowupGeometry.projection_proper _root_.OAI.PiExponent.AdmissibleBlowupGeometry.structureMap_proper _root_.OAI.PiExponent.AdmissibleCurveImage.projection_restrict_isIso _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter
open scoped Topology

namespace PiExponent.DeterminantContradiction

theorem logWeights_eq {nu : ℝ} (d : FixedData nu) (i : Fin d.m) :
    MatrixArithmetic.logWeights (finiteDenominators d) i = d.x (i.val + 1) :=
  (d.x_log i.val).symm

end PiExponent.DeterminantContradiction

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Jets_AuxiliaryJetMap
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators
open Filter Topology

namespace PiExponent

theorem literalJetSubstitution_monomial {m : ℕ} (r : Fin m → ℂ)
    (G : Fin m → Polynomial ℂ) (j : ℕ) (e : Fin (m + 1) → ℕ) (z : ℂ) :
    literalJetSubstitution r G j
      (MvPolynomial.monomial (InterpolationMatrix.exponentVector e) z) =
      MvPolynomial.C (Polynomial.C z) *
        InterpolationMatrix.monomialImage r G j (e 0) (fun i => e i.succ) := by
  classical
  rw [literalJetSubstitution, MvPolynomial.aeval_monomial,
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_succ]
  simp only [InterpolationMatrix.exponentVector_apply, Fin.cases_zero, Fin.cases_succ,
    InterpolationMatrix.monomialImage, ← map_pow]
  rfl

theorem literalJetSubstitution_polynomialOfCoefficients {m : ℕ}
    (S : Finset (Fin (m + 1) → ℕ)) (x : S → ℂ)
    (r : Fin m → ℂ) (G : Fin m → Polynomial ℂ) (j : ℕ) :
    literalJetSubstitution r G j (polynomialOfCoefficients S x) =
      InterpolationMatrix.sectionImage r G (fun c : S => c.val 0)
        (fun c i => c.val i.succ) x j := by
  classical
  change literalJetSubstitution r G j
    (∑ exponent : S, MvPolynomial.monomial
      (InterpolationMatrix.exponentVector exponent.val) (x exponent)) = _
  simp only [map_sum, literalJetSubstitution_monomial, InterpolationMatrix.sectionImage]

end PiExponent

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Polynomials_NestedPolynomialSwap
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponent.FormalMatrixBridge

theorem coeff_commAlgEquiv {R σ τ : Type*} [CommRing R]
    (p : MvPolynomial σ (MvPolynomial τ R)) (b : σ →₀ ℕ) (c : τ →₀ ℕ) :
    ((MvPolynomial.commAlgEquiv R σ τ p).coeff c).coeff b = (p.coeff b).coeff c := by
  classical
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq =>
    simp only [map_add, MvPolynomial.coeff_add, Finsupp.add_apply, hp, hq]
  | monomial d a =>
    induction a using MvPolynomial.induction_on' with
    | add a e ha he =>
      simpa only [map_add, MvPolynomial.coeff_add, Finsupp.add_apply]
        using congrArg₂ (· + ·) ha he
    | monomial e r =>
      have hs : MvPolynomial.commAlgEquiv R σ τ
          (MvPolynomial.monomial d (MvPolynomial.monomial e r)) =
          MvPolynomial.monomial e (MvPolynomial.monomial d r) :=
        AddMonoidAlgebra.commAlgEquiv_single_single (R := R) d e r
      rw [hs]
      simp only [MvPolynomial.coeff_monomial]
      split_ifs <;> simp_all

theorem coeff_nestedPolynomialSwap {R : Type*} [CommRing R] {m : ℕ}
    (p : MvPolynomial (Fin m) (Polynomial R)) (s : ℕ) (b : Fin m →₀ ℕ) :
    ((nestedPolynomialSwap R m p).coeff s).coeff b = (p.coeff b).coeff s := by
  change ((MvPolynomial.uniqueAlgEquiv (MvPolynomial (Fin m) R) Unit
    (MvPolynomial.commAlgEquiv R (Fin m) Unit
      (MvPolynomial.mapAlgEquiv (Fin m) (MvPolynomial.uniqueAlgEquiv R Unit).symm p))).coeff s).coeff b = _
  rw [MvPolynomial.coeff_uniqueAlgEquiv, coeff_commAlgEquiv]
  rw [MvPolynomial.mapAlgEquiv_apply, MvPolynomial.coeff_map]
  change (((MvPolynomial.uniqueAlgEquiv R Unit).symm (p.coeff b)).coeff
    (Finsupp.single () s)) = _
  rw [MvPolynomial.coeff_uniqueAlgEquiv_symm]
  simp

end PiExponent.FormalMatrixBridge

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_FormalMatrixBridge
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponent.FormalMatrixBridge

open MvPowerSeries
open scoped BigOperators

@[simp] theorem coeff_flatten {m : ℕ}
    (p : MvPolynomial (Fin m) (Polynomial ℂ)) (d : Fin (m+1) →₀ ℕ) :
    coeff d (flatten m p) = (p.coeff d.tail).coeff (d 0) := by
  change ((MvPolynomial.finSuccEquiv ℂ m).symm (nestedPolynomialSwap ℂ m p)).coeff d = _
  rw [← Finsupp.cons_tail d, ← MvPolynomial.finSuccEquiv_coeff_coeff,
    AlgEquiv.apply_symm_apply]
  exact coeff_nestedPolynomialSwap p (d 0) d.tail

@[simp] theorem flatten_C {m : ℕ} (p : Polynomial ℂ) :
    flatten m (MvPolynomial.C p) = FormalLogJet.liftSeries m (p : PowerSeries ℂ) := by
  classical
  ext d
  rw [coeff_flatten, FormalLogJet.coeff_liftSeries]
  simp only [MvPolynomial.coeff_C, Polynomial.coeff_coe]
  split_ifs <;> simp_all

@[simp] theorem flatten_X {m : ℕ} (i : Fin m) :
    flatten m (MvPolynomial.X i) = X i.succ := by
  classical
  ext d
  rw [coeff_flatten, MvPolynomial.coeff_X, coeff_X]
  have hd : d = Finsupp.single i.succ 1 ↔
      d.tail = Finsupp.single i 1 ∧ d 0 = 0 := by
    conv_lhs => rw [← Finsupp.cons_tail d]
    exact Finsupp.cons_eq_single_succ_iff i
  simp only [hd]
  by_cases ht : Finsupp.single i 1 = d.tail
  · rw [ite_eq_left ht]
    have ht' : d.tail = Finsupp.single i 1 := ht.symm
    simp only [ht', true_and, Polynomial.coeff_one]
  · rw [ite_eq_right ht, Polynomial.coeff_zero]
    have ht' : ¬ d.tail = Finsupp.single i 1 := Ne.symm ht
    simp only [ht', false_and, ite_false]

theorem flatten_literalJetSubstitution {m : ℕ}
    (r : Fin m → ℂ) (T : Fin m → ℕ) (j : ℕ)
    (p : PiExponentApprox.FramePolynomial m) :
    flatten m (literalJetSubstitution r
      (fun i => InterpolationMatrix.truncatedLog (T i)) j p) =
      FormalLogTruncation.truncatedFormalJet (fun i => (j : ℂ) * r i) T p := by
  have hh : (flatten m).comp
      (literalJetSubstitution r (fun i => InterpolationMatrix.truncatedLog (T i)) j) =
        FormalLogTruncation.truncatedFormalJet (fun i => (j : ℂ) * r i) T := by
    ext i
    cases i using Fin.cases with
    | zero =>
      simp [literalJetSubstitution, FormalLogTruncation.truncatedFormalJet]
    | succ i =>
      simp [literalJetSubstitution, FormalLogTruncation.truncatedFormalJet,
        InterpolationMatrix.truncatedLog, add_assoc, add_left_comm, add_comm]
  exact DFunLike.congr_fun hh p

theorem coeff_truncatedFormalJet {m : ℕ}
    (r : Fin m → ℂ) (T : Fin m → ℕ) (j : ℕ)
    (p : PiExponentApprox.FramePolynomial m) (d : Fin (m+1) →₀ ℕ) :
    coeff d (FormalLogTruncation.truncatedFormalJet
      (fun i => (j : ℂ) * r i) T p) =
      ((literalJetSubstitution r (fun i => InterpolationMatrix.truncatedLog (T i)) j p).coeff
        d.tail).coeff (d 0) := by
  rw [← flatten_literalJetSubstitution, coeff_flatten]

theorem truncatedLogMatrix_mulVec_eq_coeff {m : ℕ}
    (K : ℕ) (w0 v0 θ : ℝ) (w : Fin m → ℝ) (H : ℝ)
    (r : Fin m → ℂ) (T : Fin m → ℕ)
    (x : InterpolationMatrix.Column w0 w H → ℂ)
    (ρ : InterpolationMatrix.Row K v0 θ w H) :
    (InterpolationMatrix.truncatedLogMatrix K w0 v0 θ w H r T).mulVecLin x ρ =
      coeff (InterpolationMatrix.exponentVector ρ.2.val)
        (FormalLogTruncation.truncatedFormalJet (fun i => (ρ.1.val : ℂ) * r i) T
          (polynomialOfCoefficients
            (realWeightedSimplex (InterpolationMatrix.columnWeights w0 w) H) x)) := by
  rw [coeff_truncatedFormalJet, literalJetSubstitution_polynomialOfCoefficients]
  simpa only [exponentVector_tail, InterpolationMatrix.exponentVector_apply,
    InterpolationMatrix.linearEvaluation, InterpolationMatrix.truncatedLogMatrix] using
    InterpolationMatrix.linearEvaluation_eq_coeff K w0 v0 θ w H r
      (fun i => InterpolationMatrix.truncatedLog (T i)) x ρ

end PiExponent.FormalMatrixBridge

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_FormalMatrixSurjectivity
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponent.FormalMatrixBridge

open MvPowerSeries

theorem truncatedLogMatrix_surjective_of_rational_packets {m : ℕ} {α : Type*}
    (K : ℕ) (w0 v0 θ : ℝ) (w : Fin m → ℝ) (H : ℚ)
    (hw0 : 0 < w0) (hw : ∀ i, 0 < w i)
    (V : Fin (m+1) → ℚ) (hV : ∀ i, 0 < V i)
    (hrow : ∀ i, (V i : ℝ) = InterpolationMatrix.rowWeights v0 θ w i)
    (r : Fin m → ℂ) (T : Fin m → ℕ)
    (P : α → PiExponentApprox.FramePolynomial m)
    (hdegree : ∀ a, PiExponentApprox.HasWeightedDegreeLE
      (InterpolationMatrix.columnWeights w0 w) (H : ℝ) (P a))
    (hpacket : Function.Surjective (fun a => fun j : Fin K =>
      JetGeometry.rationalCoefficientPacket V H
        (FormalLogTruncation.truncatedFormalJet (fun i => (j.val : ℂ) * r i) T (P a)))) :
    Function.Surjective
      (InterpolationMatrix.truncatedLogMatrix K w0 v0 θ w (H : ℝ) r T).mulVecLin := by
  classical
  have hrow' : (fun i => (V i : ℝ)) = InterpolationMatrix.rowWeights v0 θ w := funext hrow
  have hW : ∀ i, 0 < InterpolationMatrix.columnWeights w0 w i := by
    intro i
    exact Fin.cases hw0 hw i
  intro y
  let e := rationalJetIndexEquiv V hV H
  let z : Fin K → JetGeometry.RationalCoefficientPacket (R := ℂ) V H :=
    fun j d => y (j, ⟨(e d).val, by
      simpa only [← hrow'] using (e d).property⟩)
  obtain ⟨a, ha⟩ := hpacket z
  let x : InterpolationMatrix.Column w0 w (H : ℝ) → ℂ :=
    fun c => (P a).coeff (InterpolationMatrix.exponentVector c.val)
  refine ⟨x, ?_⟩
  funext ρ
  rw [truncatedLogMatrix_mulVec_eq_coeff]
  change coeff (InterpolationMatrix.exponentVector ρ.2.val)
    (FormalLogTruncation.truncatedFormalJet (fun i => (ρ.1.val : ℂ) * r i) T
      (polynomialOfCoefficients
        (realWeightedSimplex (InterpolationMatrix.columnWeights w0 w) (H : ℝ))
        (fun c => (P a).coeff (InterpolationMatrix.exponentVector c.val)))) = y ρ
  rw [polynomialOfCoefficients_of_weighted _ hW _ (P a) (hdegree a)]
  let b : ↥(strictWeightedSimplex (fun i => (V i : ℝ)) (H : ℝ)) :=
    ⟨ρ.2.val, by simpa only [hrow'] using ρ.2.property⟩
  have hh := congrFun (congrFun ha ρ.1) (e.symm b)
  change coeff (e.symm b).val
    (FormalLogTruncation.truncatedFormalJet (fun i => (ρ.1.val : ℂ) * r i) T (P a)) =
      z ρ.1 (e.symm b) at hh
  simpa only [e, rationalJetIndexEquiv_symm_val, b, z, Equiv.apply_symm_apply] using hh

theorem truncatedLogMatrix_surjective_of_formalLog_packets {m : ℕ} {α : Type*}
    (K : ℕ) (w0 v0 θ : ℝ) (w : Fin m → ℝ) (H : ℚ)
    (hw0 : 0 < w0) (hw : ∀ i, 0 < w i)
    (V : Fin (m+1) → ℚ) (hV : ∀ i, 0 < V i)
    (hrow : ∀ i, (V i : ℝ) = InterpolationMatrix.rowWeights v0 θ w i)
    (r : Fin m → ℂ) (T : Fin m → ℕ)
    (hT : ∀ i, V i.succ ≤ (T i : ℚ) * V 0)
    (P : α → PiExponentApprox.FramePolynomial m)
    (hdegree : ∀ a, PiExponentApprox.HasWeightedDegreeLE
      (InterpolationMatrix.columnWeights w0 w) (H : ℝ) (P a))
    (hpacket : Function.Surjective (fun a => fun j : Fin K =>
      JetGeometry.rationalCoefficientPacket V H
        (FormalLogJet.formalJet (fun i => (j.val : ℂ) * r i) (P a)))) :
    Function.Surjective
      (InterpolationMatrix.truncatedLogMatrix K w0 v0 θ w (H : ℝ) r T).mulVecLin := by
  apply truncatedLogMatrix_surjective_of_rational_packets
    K w0 v0 θ w H hw0 hw V hV hrow r T P hdegree
  exact (FormalLogTruncation.formalLog_packets_surjective_iff_truncated
    V (fun i => (hV i).le) H T hT (fun j : Fin K => fun i => (j.val : ℂ) * r i) P).mp hpacket

end PiExponent.FormalMatrixBridge

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_AdmissibleMatrixInterpolation
attribute [-instance] _root_.OAI.PiExponent.AdmissibleCurveImage.projection_restrict_isIso _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.AdmissibleMatrixInterpolation
open Filter
open DeterminantContradiction AdmissibleBlowupGeometry
variable {ν : ℝ} (d : FixedData ν)

theorem degreeWeights_eq_matrix (i : Fin (d.m+1)) :
    (d.curveDegreeWeights i : ℝ) =
      InterpolationMatrix.columnWeights d.w0
        (MatrixArithmetic.logWeights (finiteDenominators d)) i := by
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · simp only [AdmissibleParameters.curveDegreeWeights_succ,
      d.cast_rationalWeight, InterpolationMatrix.columnWeights, Fin.cases_succ,
      logWeights_eq]

theorem jetWeights_eq_matrix (i : Fin (d.m+1)) :
    (d.curveJetWeights i : ℝ) =
      InterpolationMatrix.rowWeights d.v0 d.base.theta
        (MatrixArithmetic.logWeights (finiteDenominators d)) i := by
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · simp only [AdmissibleParameters.curveJetWeights_succ, Rat.cast_div,
      d.cast_rationalWeight, InterpolationMatrix.rowWeights, Fin.cases_succ,
      logWeights_eq]

theorem actual_truncation_weight_bound (i : Fin d.m) :
    d.curveJetWeights i.succ ≤
      (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0 i : ℚ) *
        d.curveJetWeights 0 := by
  have hw : 0 < MatrixArithmetic.logWeights (finiteDenominators d) i := by
    rw [logWeights_eq]
    exact zero_lt_one.trans_le (d.x_one_le _)
  have hF : 1 / (d.base.theta : ℝ) < d.F0 :=
    (div_lt_div_of_pos_right (by norm_num : (1 : ℝ) < 2) d.base.theta_pos).trans d.F0_large
  have hceil := Nat.le_ceil
    (d.F0 * MatrixArithmetic.logWeights (finiteDenominators d) i / (d.v0 : ℝ))
  have hbound : MatrixArithmetic.logWeights (finiteDenominators d) i / (d.base.theta : ℝ) ≤
      (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0 i : ℝ) *
        (d.v0 : ℝ) := by
    calc
      _ = (1 / (d.base.theta : ℝ)) *
          MatrixArithmetic.logWeights (finiteDenominators d) i := by ring
      _ ≤ d.F0 * MatrixArithmetic.logWeights (finiteDenominators d) i :=
        mul_le_mul_of_nonneg_right hF.le hw.le
      _ ≤ _ := (div_le_iff₀ d.v0_pos).mp hceil
  have hcast : (d.curveJetWeights i.succ : ℝ) ≤
      (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0 i : ℝ) *
        (d.curveJetWeights 0 : ℝ) := by
    simpa only [AdmissibleParameters.curveJetWeights_zero,
      AdmissibleParameters.curveJetWeights_succ, Rat.cast_div,
      d.cast_rationalWeight, logWeights_eq] using hbound
  exact_mod_cast hcast

theorem matrix_degree_of_supportBound (H : ℝ) (P : PiExponentApprox.FramePolynomial d.m)
    (hP : WeightedSliceDegree.SupportBound (fun i => (d.curveDegreeWeights i : ℝ)) H P) :
    PiExponentApprox.HasWeightedDegreeLE
      (InterpolationMatrix.columnWeights d.w0
        (MatrixArithmetic.logWeights (finiteDenominators d))) H P := by
  intro a ha
  have h := hP a ha
  have hw : (fun i => (d.curveDegreeWeights i : ℝ)) =
      InterpolationMatrix.columnWeights d.w0
        (MatrixArithmetic.logWeights (finiteDenominators d)) :=
    funext (degreeWeights_eq_matrix d)
  rw [hw] at h
  simpa only [PiExponentApprox.monomialWeight, Finsupp.weight_eq_sum, nsmul_eq_mul] using h

theorem actualMatrix_surjective_of_formalPackets {α : Type*} (H : ℚ)
    (P : α → PiExponentApprox.FramePolynomial d.m)
    (hdegree : ∀ a, WeightedSliceDegree.SupportBound
      (fun i => (d.curveDegreeWeights i : ℝ)) (H : ℝ) (P a))
    (hpacket : Function.Surjective (fun a => fun j : Fin d.K =>
      JetGeometry.rationalCoefficientPacket d.curveJetWeights H
        (FormalLogJet.formalJet (d.curveCenters j) (P a)))) :
    Function.Surjective (actualMatrix d (H : ℝ)).mulVecLin := by
  apply FormalMatrixBridge.truncatedLogMatrix_surjective_of_formalLog_packets
    d.K d.w0 d.v0 d.base.theta
    (MatrixArithmetic.logWeights (finiteDenominators d)) H
    d.w0_pos (fun i => ?_) d.curveJetWeights d.curveJetWeights_pos
    (jetWeights_eq_matrix d)
    (MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d))
    (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0)
    (actual_truncation_weight_bound d) P
    (fun a => matrix_degree_of_supportBound d _ _ (hdegree a)) hpacket
  rw [logWeights_eq]
  exact zero_lt_one.trans_le (d.x_one_le _)

theorem actualMatrix_surjective_of_packetMap (n : ℕ)
    (hpacket : Function.Surjective (packetMap d n)) :
    Function.Surjective (actualMatrix d ((n : ℝ) * (scale d).radius)).mulVecLin := by
  have h := actualMatrix_surjective_of_formalPackets d
    ((n : ℚ) * (scale d).radius) (fun P : WeightedPolynomials d n => P.val)
    (fun P => by simpa only [Rat.cast_mul, Rat.cast_natCast] using P.property) hpacket
  have hc : (((n : ℚ) * (scale d).radius : ℚ) : ℝ) =
      (n : ℝ) * (scale d).radius := by push_cast; rfl
  exact hc ▸ h

theorem cofinal_actualMatrix_of_eventual_packets
    (hpacket : ∀ᶠ n : ℕ in atTop, Function.Surjective (packetMap d n))
    (L : ℝ) : ∃ H : ℝ, L ≤ H ∧ Function.Surjective (actualMatrix d H).mulVecLin := by
  obtain ⟨N,hN⟩ := eventually_atTop.mp hpacket
  let n := max N (Nat.ceil (L / ((scale d).radius : ℝ)))
  have hR : (0 : ℝ) < (scale d).radius := by exact_mod_cast (scale d).radius_pos
  have hL : L ≤ (n : ℝ) * (scale d).radius := by
    apply (div_le_iff₀ hR).mp
    exact (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right N
      (Nat.ceil (L / ((scale d).radius : ℝ)))))
  exact ⟨(n : ℝ) * (scale d).radius, hL,
    actualMatrix_surjective_of_packetMap d n (hN n (le_max_left _ _))⟩

theorem globalInterpolation_of_eventual_packets
    (hpacket : ∀ ν : ℝ, 2 < ν → ∀ d : FixedData ν,
      ∀ᶠ n : ℕ in atTop, Function.Surjective (packetMap d n)) :
    GlobalInterpolationStatement := by
  intro ν hν d L
  exact cofinal_actualMatrix_of_eventual_packets d (hpacket ν hν d) L

end PiExponent.AdmissibleMatrixInterpolation

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_AdmissibleMatrixGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.AdmissibleMatrixInterpolation
open AlgebraicGeometry CategoryTheory Filter
open PiExponentSeshadri.Geometry
open DeterminantContradiction AdmissibleBlowupGeometry AdmissibleJetPackets
attribute [local irreducible] WeightedCompactification.lineBundle
  WeightedCompactification.affineChartMap
  AffineJetCoefficientInterface.Frame AffineJetCoefficientInterface.Sections
  AffineJetCoefficientInterface.coefficient
variable {ν : ℝ} (d : FixedData ν)

theorem globalInterpolation_of_eventual_jetRestriction_q68_oai
    (hjet : ∀ ν : ℝ, 2 < ν → ∀ d : FixedData ν,
      ∀ᶠ n : ℕ in atTop, Function.Surjective
        (BlowupJetSurjectivity.jetRestriction (centerIdeal d) (hyperplane d) n)) :
    GlobalInterpolationStatement := by
  apply globalInterpolation_of_eventual_packets
  intro ν hν d
  exact eventual_packets_of_eventual_jetRestriction_q68 d (hjet ν hν d)

end PiExponent.AdmissibleMatrixInterpolation

end

end OAI
end

theorem solution : type_of% @OAI.PiExponent.AdmissibleMatrixInterpolation.globalInterpolation_of_eventual_jetRestriction_q68_oai := @OAI.PiExponent.AdmissibleMatrixInterpolation.globalInterpolation_of_eventual_jetRestriction_q68_oai
