-- Prove2me | solution 1 for OAI.PiExponent.AdmissibleJetPackets.formalPackets_surjective_of_jetRestriction_q68
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T09:34:22.622981+00:00
-- url     : https://prove2.me/submissions/43a16037-9d05-473b-9cbb-87cdae5ebb86

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ068A044

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

theorem coordinatePowerIdeal_pow_le_rational (v : σ → ℚ) (hv : ∀ i, 0 ≤ v i)
    (e : σ → ℕ) (H : ℚ) (he : ∀ i, H ≤ (e i : ℚ) * v i) (n : ℕ) :
    (coordinatePowerIdeal e : Ideal (MvPowerSeries σ R)) ^ n ≤
      rationalWeightedIdeal v hv (n * H) := by
  classical
  apply ideal_pow_le_rationalWeightedIdeal v hv _ H _ n
  apply Ideal.span_le.mpr
  rintro _ ⟨i, rfl⟩ d hd
  rw [coeff_X_pow]
  split_ifs with h
  · subst d
    rw [Finsupp.weight_single, nsmul_eq_mul] at hd
    exact False.elim ((not_lt_of_ge (he i)) hd)
  · rfl

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
-- module Solutions.OAIQ068_PI.PiExponent_Jets_PolynomialJetPackets
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.PolynomialJetPackets
open MvPowerSeries JetGeometry

theorem polynomial_packet_surjective {R : Type*} [CommRing R] {n : ℕ}
    (v : Fin n → ℚ) (hv : ∀ i, 0 < v i) (H : ℚ) :
    Function.Surjective (fun p : MvPolynomial (Fin n) R =>
      rationalCoefficientPacket v H (p : MvPowerSeries (Fin n) R)) := by
  classical
  let I := {d : Fin n →₀ ℕ // Finsupp.weight v d < H}
  let : Fintype I := Fintype.ofEquiv _ (FormalMatrixBridge.rationalJetIndexEquiv v hv H).symm
  intro packet
  change I → R at packet
  let p : MvPolynomial (Fin n) R := ∑ d : I, MvPolynomial.monomial d.val (packet d)
  refine ⟨p, ?_⟩
  funext d
  change coeff d.val (p : MvPowerSeries (Fin n) R) = packet d
  simp only [p, MvPolynomial.coeff_coe, MvPolynomial.coeff_sum,
    MvPolynomial.coeff_monomial, Subtype.val_inj]
  change (∑ x : I, if x = (d : I) then packet x else 0) = packet d
  exact Fintype.sum_ite_eq' (d : I) packet

end PiExponent.PolynomialJetPackets

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Jets_AlgebraicJetPackets
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.AlgebraicJetPackets

open MvPolynomial
variable {R : Type*} [CommRing R] {m : ℕ}

theorem liftSeries_polynomial (p : Polynomial R) :
    FormalLogJet.liftSeries m (p : PowerSeries R) =
      Polynomial.aeval (MvPowerSeries.X (0 : Fin (m+1))) p := by
  have h : (FormalLogJet.liftSeries (R := R) m).comp Polynomial.coeToPowerSeries.ringHom =
      (Polynomial.aeval (MvPowerSeries.X (0 : Fin (m+1)))).toRingHom := by
    apply Polynomial.ringHom_ext
    · intro r
      simp [MvPowerSeries.algebraMap_apply]
    · simp
  exact RingHom.congr_fun h p

theorem truncatedFormalJet_eq_polynomial (c : Fin m → ℂ) (T : Fin m → ℕ)
    (P : PiExponentApprox.FramePolynomial m) :
    FormalLogTruncation.truncatedFormalJet c T P =
      ((triangularMap c (fun i => PowerSeries.trunc (T i) (PowerSeries.log ℂ)) P) :
        MvPowerSeries (Fin (m+1)) ℂ) := by
  have h : FormalLogTruncation.truncatedFormalJet c T =
      (MvPolynomial.coeToMvPowerSeries.algHom ℂ).comp
        (triangularMap c (fun i => PowerSeries.trunc (T i) (PowerSeries.log ℂ))) := by
    apply MvPolynomial.algHom_ext
    intro i
    cases i using Fin.cases with
    | zero =>
      simp [FormalLogTruncation.truncatedFormalJet]
    | succ i =>
      simp only [FormalLogTruncation.truncatedFormalJet, MvPolynomial.aeval_X,
        Fin.cases_succ, AlgHom.comp_apply, triangularMap_X_succ, map_add]
      rw [liftSeries_polynomial, ← Polynomial.aeval_algHom_apply]
      simp [MvPowerSeries.algebraMap_apply]
  simpa using AlgHom.congr_fun h P

theorem truncatedFormalJet_inverse (c : Fin m → ℂ) (T : Fin m → ℕ)
    (P : MvPolynomial (Fin (m+1)) ℂ) :
    FormalLogTruncation.truncatedFormalJet c T
      (inverseTriangularMap c (fun i => PowerSeries.trunc (T i) (PowerSeries.log ℂ)) P) =
      (P : MvPowerSeries (Fin (m+1)) ℂ) := by
  rw [truncatedFormalJet_eq_polynomial]
  have h := AlgHom.congr_fun
    (triangularMap_comp_inverse c (fun i => PowerSeries.trunc (T i) (PowerSeries.log ℂ))) P
  simpa using congrArg (fun Q : MvPolynomial (Fin (m+1)) ℂ =>
    (Q : MvPowerSeries (Fin (m+1)) ℂ)) h

theorem truncatedFormalJet_packet_surjective (c : Fin m → ℂ) (T : Fin m → ℕ)
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 < v i) (H : ℚ) :
    Function.Surjective (fun P : PiExponentApprox.FramePolynomial m =>
      JetGeometry.rationalCoefficientPacket v H (FormalLogTruncation.truncatedFormalJet c T P)) := by
  intro packet
  obtain ⟨P, hP⟩ := PolynomialJetPackets.polynomial_packet_surjective v hv H packet
  refine ⟨inverseTriangularMap c (fun i => PowerSeries.trunc (T i) (PowerSeries.log ℂ)) P, ?_⟩
  simpa only [truncatedFormalJet_inverse] using hP

theorem formalJet_packet_surjective (c : Fin m → ℂ)
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 < v i) (H : ℚ) :
    Function.Surjective (fun P : PiExponentApprox.FramePolynomial m =>
      JetGeometry.rationalCoefficientPacket v H (FormalLogJet.formalJet c P)) := by
  let T : Fin m → ℕ := fun i => Nat.ceil (v i.succ / v 0)
  have hT : ∀ i, v i.succ ≤ (T i : ℚ) * v 0 := by
    intro i
    exact (div_le_iff₀ (hv 0)).mp (Nat.le_ceil _)
  have ht : Function.Surjective (fun P : PiExponentApprox.FramePolynomial m =>
      fun _ : Unit => JetGeometry.rationalCoefficientPacket v H
        (FormalLogTruncation.truncatedFormalJet c T P)) := by
    intro packets
    obtain ⟨P, hP⟩ := truncatedFormalJet_packet_surjective c T v hv H (packets ())
    refine ⟨P, ?_⟩
    funext j
    cases j
    exact hP
  have hs := (FormalLogTruncation.formalLog_packets_surjective_iff_truncated
    v (fun i => (hv i).le) H T hT (fun _ : Unit => c) (fun P => P)).mpr ht
  intro packet
  obtain ⟨P, hP⟩ := hs (fun _ => packet)
  exact ⟨P, congrFun hP ()⟩

end PiExponent.AlgebraicJetPackets

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Jets_CompactJetPolynomial
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponent.CompactJetPolynomial

open MvPolynomial AlgebraicJetPackets
open scoped BigOperators

variable {k : Type*} [Field k] {m : ℕ}

theorem truncatedFormalJet_coordinates (c : Fin m → ℂ) (T : Fin m → ℕ)
    (i : Fin (m+1)) :
    FormalLogTruncation.truncatedFormalJet c T (coordinates c (logPolynomials T) i) =
      MvPowerSeries.X i := by
  change FormalLogTruncation.truncatedFormalJet c T
    (inverseTriangularMap c (fun j => PowerSeries.trunc (T j) (PowerSeries.log ℂ)) (X i)) = _
  rw [truncatedFormalJet_inverse]
  simp

theorem map_powerIdeal_truncatedFormalJet (c : Fin m → ℂ) (T : Fin m → ℕ)
    (e : Fin (m+1) → ℕ) :
    (powerIdeal c (logPolynomials T) e).map
      (FormalLogTruncation.truncatedFormalJet c T).toRingHom =
        JetGeometry.coordinatePowerIdeal (R := ℂ) e := by
  rw [powerIdeal, Ideal.map_span, ← Set.range_comp]
  apply congrArg Ideal.span
  apply congrArg Set.range
  funext i
  change FormalLogTruncation.truncatedFormalJet c T
    (coordinates c (logPolynomials T) i ^ e i) = MvPowerSeries.X i ^ e i
  rw [map_pow, truncatedFormalJet_coordinates]

theorem map_powerIdeal_pow_truncatedFormalJet (c : Fin m → ℂ) (T : Fin m → ℕ)
    (e : Fin (m+1) → ℕ) (n : ℕ) :
    (powerIdeal c (logPolynomials T) e ^ n).map
      (FormalLogTruncation.truncatedFormalJet c T).toRingHom =
        JetGeometry.coordinatePowerIdeal (R := ℂ) e ^ n := by
  rw [Ideal.map_pow, map_powerIdeal_truncatedFormalJet]

theorem truncatedFormalJet_mem_weighted_of_mem_pow (c : Fin m → ℂ) (T : Fin m → ℕ)
    (e : Fin (m+1) → ℕ) (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 ≤ v i)
    (R : ℚ) (he : ∀ i, R ≤ (e i : ℚ) * v i) (n : ℕ)
    (P : MvPolynomial (Fin (m+1)) ℂ) (hP : P ∈ powerIdeal c (logPolynomials T) e ^ n) :
    FormalLogTruncation.truncatedFormalJet c T P ∈
      JetGeometry.rationalWeightedIdeal v hv (n * R) := by
  apply JetGeometry.coordinatePowerIdeal_pow_le_rational v hv e R he n
  rw [← map_powerIdeal_pow_truncatedFormalJet c T e n]
  exact Ideal.mem_map_of_mem _ hP

theorem formalJet_mem_weighted_of_mem_pow (c : Fin m → ℂ) (T : Fin m → ℕ)
    (e : Fin (m+1) → ℕ) (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 ≤ v i)
    (hT : ∀ i, v i.succ ≤ (T i : ℚ) * v 0)
    (R : ℚ) (he : ∀ i, R ≤ (e i : ℚ) * v i) (n : ℕ)
    (P : MvPolynomial (Fin (m+1)) ℂ) (hP : P ∈ powerIdeal c (logPolynomials T) e ^ n) :
    FormalLogJet.formalJet c P ∈ JetGeometry.rationalWeightedIdeal v hv (n * R) := by
  rw [← FormalLogTruncation.shiftMap_truncatedFormalJet c T P]
  exact FormalLogTruncation.shiftMap_mem_rationalWeightedIdeal
    (fun i => FormalLogTruncation.logTail (T i))
    (fun i => FormalLogTruncation.logTail_constantCoeff (T i)) v hv
    (fun i => FormalLogTruncation.logTail_mem_rationalWeightedIdeal v hv (T i) (v i.succ) (hT i))
    (n * R) _ (truncatedFormalJet_mem_weighted_of_mem_pow c T e v hv R he n P hP)

end PiExponent.CompactJetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Jets_CompactLogJetIdeal
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped BigOperators
namespace PiExponent.CompactLogJetIdeal
open CompactJetPolynomial

variable {m : ℕ}

theorem polynomialIdeal_pow_le {J : Type*} [Fintype J]
    (c : J → Fin m → ℂ) (T : Fin m → ℕ) (e : Fin (m+1) → ℕ) (n : ℕ) (a : J) :
    polynomialIdeal c T e ^ n ≤ powerIdeal (c a) (logPolynomials T) e ^ n := by
  classical
  apply pow_le_pow_left'
  exact Ideal.prod_le_inf.trans (Finset.inf_le (Finset.mem_univ a))

end PiExponent.CompactLogJetIdeal
end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_AdmissibleBlowupGeometry
attribute [-instance] _root_.OAI.PiExponent.AdmissibleCurveImage.projection_restrict_isIso _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.AdmissibleBlowupGeometry
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry
open WeightedGeometryScale
variable {ν Λ D : ℝ} (d : AdmissibleParameters ν Λ D)

theorem centerIdeal_restrict : (centerIdeal d).comap (affineChart d) =
    CompactLogJetIdeal.affineIdeal d.curveCenters (logCutoff d) (scale d).jetPowers :=
  CompactLogJetIdeal.restrict_compactIdeal _ _ _ _

theorem centerIdeal_support_subset_chart :
    ((centerIdeal d).support : Set (compactification d)) ⊆ (affineChart d).opensRange := by
  rw [centerIdeal_support]
  intro x hx
  obtain ⟨j,z,rfl⟩ := Set.mem_iUnion.mp hx
  exact ⟨CompactLogJetIdeal.point (d.curveCenters j) z,rfl⟩

end PiExponent.AdmissibleBlowupGeometry

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Jets_AffineJetSupport
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.ExceptionalRepresentedTypes.instAddCommGroupSections _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.IdealModule.closedInclusion_mono _root_.OAI.PiExponentSeshadri.IdealModule.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.AffineJetSupport
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open PiExponent.BlowupJetSurjectivity
variable {X Y : Scheme}

private theorem map_bijective_of_eq {T : Type*} [Category T] [Quiver.IsThin T]
    (F : Tᵒᵖ ⥤ AddCommGrpCat) {U V : T}
    (h : U = V) (i : U ⟶ V) : Function.Bijective (F.map i.op) := by
  subst V
  have hi : i = 𝟙 U := Subsingleton.elim _ _
  subst i
  rw [op_id]
  erw [F.map_id]
  exact Function.bijective_id

theorem restriction_surjective_of_iso {M N : X.Modules} (e : M ≅ N) (U : X.Opens)
    (h : Function.Surjective (N.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op)) :
    Function.Surjective (M.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op) := by
  intro s
  obtain ⟨t, ht⟩ := h (e.hom.app U s)
  obtain ⟨r, hr⟩ := (ConcreteCategory.bijective_of_isIso (e.hom.app ⊤)).surjective t
  refine ⟨r, (ConcreteCategory.bijective_of_isIso (e.hom.app U)).injective ?_⟩
  have hn := CategoryTheory.congr_fun
    (e.hom.mapPresheaf.naturality (homOfLE (le_top : U ≤ ⊤)).op) r
  change e.hom.app U (M.presheaf.map _ r) = N.presheaf.map _ (e.hom.app ⊤ r) at hn
  rw [hn, hr, ht]

theorem pushforward_restriction_bijective (f : Y ⟶ X) (M : Y.Modules) (U : X.Opens)
    (hU : f ⁻¹ᵁ U = ⊤) :
    Function.Bijective (((Scheme.Modules.pushforward f).obj M).presheaf.map
      (homOfLE (le_top : U ≤ ⊤)).op) := by
  rw [Scheme.Modules.pushforward_obj_presheaf_map]
  have he : f ⁻¹ᵁ U = f ⁻¹ᵁ (⊤ : X.Opens) := by simp [hU]
  exact map_bijective_of_eq M.presheaf he _

theorem subscheme_preimage_eq_top (I : X.IdealSheafData) (U : X.Opens)
    (hs : (I.support : Set X) ⊆ U) : I.subschemeι ⁻¹ᵁ U = ⊤ := by
  apply top_unique
  intro x hx
  apply hs
  rw [← I.range_subschemeι]
  exact ⟨x, rfl⟩

theorem twistedQuotient_restriction_surjective (I : X.IdealSheafData)
    (A : LineBundle X) (n : ℕ) (U : X.Opens)
    (hs : (I.support : Set X) ⊆ U) :
    Function.Surjective (((moduleTwistFunctor A n).obj (jetQuotient I)).presheaf.map
      (homOfLE (le_top : U ≤ ⊤)).op) := by
  apply restriction_surjective_of_iso
    (ProjectionFormula.twistIso I.subschemeι (PiExponentSeshadri.IdealModule.unit I.subscheme) A n).symm U
  exact (pushforward_restriction_bijective I.subschemeι _ U
    (subscheme_preimage_eq_top I U hs)).surjective

theorem globalQuotientValue_surjective (I : X.IdealSheafData) (A : LineBundle X) (n : ℕ)
    (U : X.affineOpens) (e : A.sheaf.restrict U.1.ι ≅ structureSheaf U.1.toScheme)
    (hs : (I.support : Set X) ⊆ U.1) :
    Function.Surjective (globalQuotientValue I A n U e) :=
  (localQuotientEquiv I A n U e).surjective.comp
    ((twistedQuotient_restriction_surjective I A n U.1 hs).comp
      (moduleSectionEquiv ((moduleTwistFunctor A n).obj (jetQuotient I))).surjective)

end PiExponent.AffineJetSupport
end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Jets_AffineJetQuotient
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.ExceptionalRepresentedTypes.instAddCommGroupSections _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.IdealModule.closedInclusion_mono _root_.OAI.PiExponentSeshadri.IdealModule.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.AffineJetQuotient
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open PiExponent.BlowupJetSurjectivity PiExponent.AffineJetSupport
variable {X : Scheme}

theorem localQuotientEquiv_apply (I : X.IdealSheafData) (A : LineBundle X) (n : ℕ)
    (U : X.affineOpens) (e : A.sheaf.restrict U.1.ι ≅ structureSheaf U.1.toScheme)
    (s : Γ((moduleTwistFunctor A n).obj (jetQuotient I),U.1)) :
    localQuotientEquiv I A n U e s =
      (I.subschemeObjIso U).hom ((untwistSectionsIso A U.1 e n (jetQuotient I)).hom s) := rfl

theorem globalQuotientValue_jetRestriction (I : X.IdealSheafData)
    (A : LineBundle X) (n : ℕ) (U : X.affineOpens)
    (e : A.sheaf.restrict U.1.ι ≅ structureSheaf U.1.toScheme)
    (s : GlobalSections X (modulePow X A.sheaf n)) :
    globalQuotientValue (I^n) A n U e (jetRestriction I A n s) =
      Ideal.Quotient.mk ((I^n).ideal U) (globalSectionCoefficient A n U e s) := by
  unfold globalQuotientValue
  erw [moduleSectionEquiv_apply, section_value_natural, localQuotientEquiv_apply]
  let q := PiExponentSeshadri.IdealModule.structureMap (I^n).subschemeι
  let t := s ≫ (moduleTwistUnitIso A n).inv
  change ((I^n).subschemeObjIso U).hom
    ((untwistSectionsIso A U.1 e n (jetQuotient (I^n))).hom
      (((moduleTwistFunctor A n).map q).app U.1 (t.app U.1 (1 : Γ(X,U.1))))) = _
  have hn := CategoryTheory.congr_fun (untwistSectionsIso_natural A U.1 e n q)
    (t.app U.1 (1 : Γ(X,U.1)))
  change (untwistSectionsIso A U.1 e n (jetQuotient (I^n))).hom
      (((moduleTwistFunctor A n).map q).app U.1 (t.app U.1 (1 : Γ(X,U.1)))) =
    q.app U.1 ((untwistSectionsIso A U.1 e n (structureSheaf X)).hom (t.app U.1 (1 : Γ(X,U.1)))) at hn
  rw [hn]
  change ((I^n).subschemeObjIso U).hom
    ((I^n).subschemeι.app U.1 (globalSectionCoefficient A n U e s)) = _
  rw [Scheme.IdealSheafData.subschemeι_app]
  exact ((I^n).subschemeObjIso U).inv_hom_id_apply _

theorem coefficient_quotient_surjective_of_jetRestriction
    (I : X.IdealSheafData) (A : LineBundle X) (n : ℕ) (U : X.affineOpens)
    (e : A.sheaf.restrict U.1.ι ≅ structureSheaf U.1.toScheme)
    (hs : ((I^n).support : Set X) ⊆ U.1)
    (hjet : Function.Surjective (jetRestriction I A n)) :
    Function.Surjective (fun s : GlobalSections X (modulePow X A.sheaf n) =>
      Ideal.Quotient.mk ((I^n).ideal U) (globalSectionCoefficient A n U e s)) := by
  intro q
  obtain ⟨t, ht⟩ := globalQuotientValue_surjective (I^n) A n U e hs q
  obtain ⟨s, rfl⟩ := hjet t
  exact ⟨s, (globalQuotientValue_jetRestriction I A n U e s).symm.trans ht⟩

end PiExponent.AffineJetQuotient
end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Jets_AffineJetPolynomial
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.ExceptionalRepresentedTypes.instAddCommGroupSections _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.AffineJetPolynomial
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open PiExponent.BlowupJetSurjectivity PiExponent.AffineJetSupport PiExponent.AffineJetQuotient
open PiExponent.ExceptionalAffineChart
open PiExponentSeshadri.IdealPullback
variable {X : Scheme} {R : Type} [CommRing R]

theorem map_ideal_functionsOnOpenEquiv (I : X.IdealSheafData)
    (j : Spec (CommRingCat.of R) ⟶ X) [IsOpenImmersion j]
    (J : Ideal R) (hJ : I.comap j = specIdeal J) :
    (I.ideal (chartOpen j)).map (functionsOnOpenEquiv j).toRingHom = J := by
  let : IsAffine j.opensRange.toScheme := isAffineOpen_opensRange j
  change (I.ideal (chartOpen j)).map
    ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom.comp
      (j.isoOpensRange.hom.appTop.hom.comp (chartOpen j).1.topIso.inv.hom)) = J
  dsimp +instances only [chartOpen]
  rw [← Ideal.map_map, ← Ideal.map_map]
  erw [← comap_ι_top I (chartOpen j)]
  erw [← comap_top (I.comap j.opensRange.ι) j.isoOpensRange.hom]
  rw [← Scheme.IdealSheafData.comap_comp]
  change ((I.comap (j.isoOpensRange.hom ≫ j.opensRange.ι)).ideal
    ⟨⊤, isAffineOpen_top _⟩).map (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom = J
  rw [j.isoOpensRange_hom_ι, hJ, specIdeal_top, Ideal.map_map]
  have he : (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom = RingHom.id _ := by
    apply RingHom.ext
    intro r
    exact (Scheme.ΓSpecIso (CommRingCat.of R)).inv_hom_id_apply r
  rw [he, Ideal.map_id]

theorem polynomialQuotient_surjective_of_jetRestriction
    (I : X.IdealSheafData) (A : LineBundle X) (n : ℕ)
    (j : Spec (CommRingCat.of R) ⟶ X) [IsOpenImmersion j]
    (e : A.sheaf.restrict (chartOpen j).1.ι ≅ structureSheaf (chartOpen j).1.toScheme)
    (J : Ideal R) (hJ : I.comap j = specIdeal J)
    (hs : ((I^n).support : Set X) ⊆ j.opensRange)
    (hjet : Function.Surjective (jetRestriction I A n)) :
    Function.Surjective (fun s : GlobalSections X (modulePow X A.sheaf n) =>
      Ideal.Quotient.mk (J^n) (polynomialCoefficient j A n e s)) := by
  have hpow : (I^n).comap j = specIdeal (J^n) := by
    rw [comap_pow, hJ, specIdeal_pow]
  have hmap := map_ideal_functionsOnOpenEquiv (I^n) j (J^n) hpow
  have hsource := coefficient_quotient_surjective_of_jetRestriction I A n (chartOpen j) e hs hjet
  intro q
  obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective q
  obtain ⟨s, hs⟩ := hsource (Ideal.Quotient.mk ((I^n).ideal (chartOpen j))
    ((functionsOnOpenEquiv j).symm P))
  refine ⟨s, Ideal.Quotient.eq.mpr ?_⟩
  have hs' := (Ideal.Quotient.eq (R := Γ(X,(chartOpen j).1))
    (I := (I^n).ideal (chartOpen j))).mp hs
  have hm := Ideal.mem_map_of_mem (functionsOnOpenEquiv j).toRingHom hs'
  erw [hmap] at hm
  let c : Γ(X,j.opensRange) := globalSectionCoefficient A n (chartOpen j) e s
  change (functionsOnOpenEquiv j) (c - (functionsOnOpenEquiv j).symm P) ∈ J^n at hm
  rw [(functionsOnOpenEquiv j).map_sub] at hm
  simpa only [RingEquiv.apply_symm_apply, polynomialCoefficient, c] using hm

end PiExponent.AffineJetPolynomial
end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Jets_JetPowerIdealCoprime
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.RamifiedLocalLength.translatedPowerLocalMap_isLocalHom _root_.OAI.PiExponent.SeparablePointLength.pointLocalMap_isLocalHom _root_.OAI.PiExponent.SeparablePointLength.point_liesOver _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.JetPowerIdealCoprime
open MvPolynomial CompactJetPolynomial

variable {k : Type*} [Field k] {m : ℕ}

theorem pointIdeal_injective {σ : Type*} :
    Function.Injective (WeightedBezout.pointIdeal (k := k) (σ := σ)) := by
  intro a b hab
  funext i
  have hx : X i - C (a i) ∈ WeightedBezout.pointIdeal b := by
    rw [← hab]
    simp
  have hzero := (WeightedBezout.mem_pointIdeal b _).mp hx
  have hz : b i - a i = 0 := by simpa using hzero
  exact (sub_eq_zero.mp hz).symm

theorem center_pointIdeal_injective :
    Function.Injective (fun c : Fin m → k => WeightedBezout.pointIdeal (center c)) := by
  intro a b hab
  have h := pointIdeal_injective hab
  funext i
  exact congrFun h i.succ

theorem powerIdeal_pairwise_isCoprime {J : Type*}
    (c : J → Fin m → k) (hc : Function.Injective c)
    (G : Fin m → Polynomial k) (hG : ∀ i, (G i).eval 0 = 0)
    (e : Fin (m+1) → ℕ) (he : ∀ i, 0 < e i) :
    Pairwise (fun i j => IsCoprime (powerIdeal (c i) G e) (powerIdeal (c j) G e)) := by
  intro i j hij
  have hp : IsCoprime (WeightedBezout.pointIdeal (center (c i)))
      (WeightedBezout.pointIdeal (center (c j))) := by
    apply Ideal.isCoprime_of_isMaximal
    intro heq
    exact hij (hc (center_pointIdeal_injective heq))
  apply Ideal.isCoprime_iff_sup_eq.mpr
  apply Ideal.radical_eq_top.mp
  rw [Ideal.radical_sup, radical_powerIdeal (c i) G hG e he,
    radical_powerIdeal (c j) G hG e he, hp.sup_eq, Ideal.radical_top]

theorem powerIdeal_pow_pairwise_isCoprime {J : Type*}
    (c : J → Fin m → k) (hc : Function.Injective c)
    (G : Fin m → Polynomial k) (hG : ∀ i, (G i).eval 0 = 0)
    (e : Fin (m+1) → ℕ) (he : ∀ i, 0 < e i) (n : ℕ) :
    Pairwise (fun i j => IsCoprime (powerIdeal (c i) G e ^ n) (powerIdeal (c j) G e ^ n)) := by
  intro i j hij
  exact (powerIdeal_pairwise_isCoprime c hc G hG e he hij).pow

end PiExponent.JetPowerIdealCoprime

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Jets_AffineJetPackets
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.AffineJetPackets
open CompactJetPolynomial
open scoped BigOperators

variable {m : ℕ}

theorem formalJet_packet_eq_of_sub_mem_pow
    (c : Fin m → ℂ) (T : Fin m → ℕ) (e : Fin (m+1) → ℕ)
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 ≤ v i)
    (hT : ∀ i, v i.succ ≤ (T i : ℚ) * v 0)
    (R : ℚ) (he : ∀ i, R ≤ (e i : ℚ) * v i) (n : ℕ)
    (P Q : PiExponentApprox.FramePolynomial m)
    (hPQ : P - Q ∈ powerIdeal c (logPolynomials T) e ^ n) :
    JetGeometry.rationalCoefficientPacket v (n * R) (FormalLogJet.formalJet c P) =
      JetGeometry.rationalCoefficientPacket v (n * R) (FormalLogJet.formalJet c Q) := by
  apply (FormalLogTruncation.rationalCoefficientPacket_eq_iff v hv (n * R) _ _).mpr
  simpa only [map_sub] using formalJet_mem_weighted_of_mem_pow c T e v hv hT R he n
    (P - Q) hPQ

theorem formalJet_packets_surjective {J : Type*} [Fintype J]
    (c : J → Fin m → ℂ) (hc : Function.Injective c)
    (T : Fin m → ℕ) (e : Fin (m+1) → ℕ) (hepos : ∀ i, 0 < e i)
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 < v i)
    (hT : ∀ i, v i.succ ≤ (T i : ℚ) * v 0)
    (R : ℚ) (he : ∀ i, R ≤ (e i : ℚ) * v i) (n : ℕ) :
    Function.Surjective (fun P : PiExponentApprox.FramePolynomial m => fun j =>
      JetGeometry.rationalCoefficientPacket v (n * R) (FormalLogJet.formalJet (c j) P)) := by
  classical
  intro packets
  choose P hP using fun j => AlgebraicJetPackets.formalJet_packet_surjective (c j)
    v hv (n * R) (packets j)
  have hcop := JetPowerIdealCoprime.powerIdeal_pow_pairwise_isCoprime c hc
    (logPolynomials T) (logPolynomials_eval_zero T) e hepos n
  obtain ⟨Q, hQ⟩ := Ideal.exists_forall_sub_mem_ideal hcop P
  refine ⟨Q, ?_⟩
  funext j
  exact (formalJet_packet_eq_of_sub_mem_pow (c j) T e v (fun i => (hv i).le)
    hT R he n Q (P j) (hQ j)).trans (hP j)

theorem packets_surjective_of_polynomialIdeal_quotient {α J : Type*} [Fintype J]
    (c : J → Fin m → ℂ) (hc : Function.Injective c)
    (T : Fin m → ℕ) (e : Fin (m+1) → ℕ) (hepos : ∀ i, 0 < e i)
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 < v i)
    (hT : ∀ i, v i.succ ≤ (T i : ℚ) * v 0)
    (R : ℚ) (he : ∀ i, R ≤ (e i : ℚ) * v i) (n : ℕ)
    (f : α → PiExponentApprox.FramePolynomial m)
    (hf : Function.Surjective (fun a =>
      Ideal.Quotient.mk (CompactLogJetIdeal.polynomialIdeal c T e ^ n) (f a))) :
    Function.Surjective (fun a j =>
      JetGeometry.rationalCoefficientPacket v (n * R) (FormalLogJet.formalJet (c j) (f a))) := by
  intro packets
  obtain ⟨P, hP⟩ := formalJet_packets_surjective c hc T e hepos v hv hT R he n packets
  obtain ⟨a, ha⟩ := hf (Ideal.Quotient.mk _ P)
  have hdiff : f a - P ∈ CompactLogJetIdeal.polynomialIdeal c T e ^ n :=
    Ideal.Quotient.eq.mp ha
  refine ⟨a, ?_⟩
  funext j
  exact (formalJet_packet_eq_of_sub_mem_pow (c j) T e v (fun i => (hv i).le)
    hT R he n (f a) P (CompactLogJetIdeal.polynomialIdeal_pow_le c T e n j hdiff)).trans
      (congrFun hP j)

end PiExponent.AffineJetPackets

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Jets_AffineJetFramedPackets
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.ExceptionalRepresentedTypes.instAddCommGroupSections _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.AffineJetFramedPackets
open AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry PiExponentSeshadri.IdealPullback
open PiExponent.AffineJetCoefficientInterface PiExponent.BlowupJetSurjectivity
variable {X : Scheme} {m : ℕ} {J : Type} [Fintype J]

theorem surjective_of_jetRestriction
    (c : J → Fin m → ℂ) (hc : Function.Injective c)
    (T : Fin m → ℕ) (e : Fin (m+1) → ℕ) (hepos : ∀ i, 0 < e i)
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 < v i)
    (hT : ∀ i, v i.succ ≤ (T i : ℚ) * v 0)
    (R : ℚ) (he : ∀ i, R ≤ (e i : ℚ) * v i) (n : ℕ)
    (j : Spec (CommRingCat.of (PiExponentApprox.FramePolynomial m)) ⟶ X) [IsOpenImmersion j]
    (I : X.IdealSheafData) (A : LineBundle X) (frame : Frame j A)
    (hI : I.comap j = specIdeal (CompactLogJetIdeal.polynomialIdeal c T e))
    (hs : ((I^n).support : Set X) ⊆ j.opensRange)
    (hjet : Function.Surjective (jetRestriction I A n)) :
    Function.Surjective (fun s : Sections A n => fun k =>
      JetGeometry.rationalCoefficientPacket v (n * R)
        (FormalLogJet.formalJet (c k) (coefficient j A n frame s))) := by
  apply AffineJetPackets.packets_surjective_of_polynomialIdeal_quotient c hc T e hepos
    v hv hT R he n (coefficient j A n frame)
  exact AffineJetPolynomial.polynomialQuotient_surjective_of_jetRestriction
    I A n j frame (CompactLogJetIdeal.polynomialIdeal c T e) hI hs hjet

end PiExponent.AffineJetFramedPackets
end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Jets_AdmissibleJetPackets
attribute [-instance] _root_.OAI.PiExponent.AdmissibleCurveImage.projection_restrict_isIso _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.ExceptionalRepresentedTypes.instAddCommGroupSections _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.AdmissibleJetPackets
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry
open PiExponent.AdmissibleBlowupGeometry
open PiExponent.BlowupJetSurjectivity PiExponent.ExceptionalAffineChart
attribute [local irreducible] AdmissibleBlowupGeometry.affineChart AdmissibleBlowupGeometry.hyperplane
  AdmissibleBlowupGeometry.centerIdeal
  AffineJetCoefficientInterface.Frame AffineJetCoefficientInterface.Sections
  AffineJetCoefficientInterface.coefficient
variable {ν Λ D : ℝ} (d : AdmissibleParameters ν Λ D)

theorem formalPackets_surjective_of_jetRestriction_q68_oai (n : ℕ)
    (e : AffineJetCoefficientInterface.Frame (affineChart d) (hyperplane d))
    (hjet : Function.Surjective (jetRestriction (centerIdeal d) (hyperplane d) n)) :
    Function.Surjective (fun s j =>
      JetGeometry.rationalCoefficientPacket d.curveJetWeights (n * (scale d).radius)
        (FormalLogJet.formalJet (d.curveCenters j) (sectionPolynomial d n e s))) := by
  have hc : Function.Injective d.curveCenters := by
    let i : Fin d.m := ⟨0, by have := d.m_pos; omega⟩
    intro j k h
    exact d.curveCenters_injective i (congrFun h i)
  have he : ∀ i, (scale d).radius ≤ ((scale d).jetPowers i : ℚ) * d.curveJetWeights i := by
    intro i
    rw [mul_comm, (scale d).jetPowers_eq]
  have hs : (((centerIdeal d)^n).support : Set (compactification d)) ⊆
      (affineChart d).opensRange := by
    cases n with
    | zero => simp
    | succ n => simpa using centerIdeal_support_subset_chart d
  exact AffineJetFramedPackets.surjective_of_jetRestriction d.curveCenters hc
    (logCutoff d) (scale d).jetPowers (scale d).jetPowers_pos
    d.curveJetWeights d.curveJetWeights_pos (fun i => (logCutoff_strict d i).le)
    (scale d).radius he n (affineChart d) (centerIdeal d) (hyperplane d) e
    (centerIdeal_restrict d) hs hjet

end PiExponent.AdmissibleJetPackets
end

end OAI
end

theorem solution : type_of% @OAI.PiExponent.AdmissibleJetPackets.formalPackets_surjective_of_jetRestriction_q68_oai := @OAI.PiExponent.AdmissibleJetPackets.formalPackets_surjective_of_jetRestriction_q68_oai
