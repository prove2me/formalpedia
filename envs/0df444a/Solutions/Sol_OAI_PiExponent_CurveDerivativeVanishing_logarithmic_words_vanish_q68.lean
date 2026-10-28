-- Prove2me | solution 1 for OAI.PiExponent.CurveDerivativeVanishing.logarithmic_words_vanish_q68
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T09:17:05.143436+00:00
-- url     : https://prove2.me/submissions/26facb52-110a-4c32-8299-c19aad90b891

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ068A009
import Definitions.Def_OAIQ068A029
import Definitions.Def_OAIQ068A031
import Definitions.Def_OAIQ068A032

section
-- module Solutions.OAIQ068_PI.PiExponent_Jets_FormalJetDerivatives
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.FormalJetDerivatives
open MvPowerSeries
open PiExponent.JetGeometry

variable {σ R : Type*} [CommRing R]

theorem pderiv_mem_rationalWeightedIdeal (v : σ → ℚ) (hv : ∀ i, 0 ≤ v i)
    (H : ℚ) (f : MvPowerSeries σ R)
    (hf : f ∈ rationalWeightedIdeal v hv H) (i : σ) :
    pderiv R i f ∈ rationalWeightedIdeal v hv (H - v i) := by
  intro d hd
  rw [coeff_pderiv, hf, zero_mul]
  rw [map_add, Finsupp.weight_single, one_nsmul]
  linarith

theorem mul_pderiv_mem_rationalWeightedIdeal (v : σ → ℚ) (hv : ∀ i, 0 ≤ v i)
    (H : ℚ) (f g : MvPowerSeries σ R)
    (hf : f ∈ rationalWeightedIdeal v hv H) (i : σ) :
    g * pderiv R i f ∈ rationalWeightedIdeal v hv (H - v i) :=
  (rationalWeightedIdeal v hv (H - v i)).mul_mem_left g
    (pderiv_mem_rationalWeightedIdeal v hv H f hf i)

theorem jetFrame_mem_rationalWeightedIdeal {m : ℕ}
    (v : Fin (m + 1) → ℚ) (hv : ∀ i, 0 ≤ v i)
    (H : ℚ) (f : MvPowerSeries (Fin (m + 1)) R)
    (hf : f ∈ rationalWeightedIdeal v hv H) (i : Fin (m + 1)) :
    jetFrame m i f ∈ rationalWeightedIdeal v hv (H - v i) := by
  by_cases hi : i = 0
  · subst i
    rw [jetFrame_zero]
    exact mul_pderiv_mem_rationalWeightedIdeal v hv H f (1 + X 0) hf 0
  · rw [jetFrame_pos m i hi]
    exact pderiv_mem_rationalWeightedIdeal v hv H f hf i

theorem jetFrameWord_mem_rationalWeightedIdeal {m : ℕ}
    (v : Fin (m + 1) → ℚ) (hv : ∀ i, 0 ≤ v i)
    (H : ℚ) (f : MvPowerSeries (Fin (m + 1)) R)
    (hf : f ∈ rationalWeightedIdeal v hv H) (word : List (Fin (m + 1))) :
    jetFrameWord m word f ∈ rationalWeightedIdeal v hv (H - (word.map v).sum) := by
  induction word with
  | nil => simpa [jetFrameWord] using hf
  | cons i word ih =>
    have hh := jetFrame_mem_rationalWeightedIdeal v hv
      (H - (word.map v).sum) (jetFrameWord m word f) ih i
    simpa only [jetFrameWord, List.foldr_cons, List.map_cons, List.sum_cons,
      sub_sub, add_comm] using hh

end PiExponent.FormalJetDerivatives

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Polynomials_PolynomialFrameDegree
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentApprox

noncomputable section

open MvPolynomial

theorem monomialWeight_add {m : ℕ} (w : Fin (m + 1) → ℝ)
    (d e : Fin (m + 1) →₀ ℕ) :
    monomialWeight w (d + e) = monomialWeight w d + monomialWeight w e := by
  simp [monomialWeight, Finsupp.add_apply, Nat.cast_add, add_mul, Finset.sum_add_distrib]

theorem monomialWeight_single {m : ℕ} (w : Fin (m + 1) → ℝ)
    (i : Fin (m + 1)) : monomialWeight w (Finsupp.single i 1) = w i := by
  classical
  simp [monomialWeight, Finsupp.single_apply]

theorem HasWeightedDegreeLE.zero {m : ℕ} (w : Fin (m + 1) → ℝ) (N : ℝ) :
    HasWeightedDegreeLE w N (0 : MvPolynomial (Fin (m + 1)) ℂ) := by
  simp [HasWeightedDegreeLE]

theorem HasWeightedDegreeLE.mono {m : ℕ} {w : Fin (m + 1) → ℝ} {N M : ℝ}
    {p : MvPolynomial (Fin (m + 1)) ℂ} (hp : HasWeightedDegreeLE w N p)
    (hNM : N ≤ M) : HasWeightedDegreeLE w M p :=
  fun d hd => (hp d hd).trans hNM

theorem HasWeightedDegreeLE.add {m : ℕ} {w : Fin (m + 1) → ℝ} {N : ℝ}
    {p q : MvPolynomial (Fin (m + 1)) ℂ}
    (hp : HasWeightedDegreeLE w N p) (hq : HasWeightedDegreeLE w N q) :
    HasWeightedDegreeLE w N (p + q) := by
  intro d hd
  rcases Finset.mem_union.mp (MvPolynomial.support_add hd) with hd | hd
  · exact hp d hd
  · exact hq d hd

theorem HasWeightedDegreeLE.sum {m : ℕ} {α : Type*} {w : Fin (m + 1) → ℝ}
    {N : ℝ} (s : Finset α) (p : α → MvPolynomial (Fin (m + 1)) ℂ)
    (hp : ∀ a ∈ s, HasWeightedDegreeLE w N (p a)) :
    HasWeightedDegreeLE w N (∑ a ∈ s, p a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using HasWeightedDegreeLE.zero w N
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact (hp a (Finset.mem_insert_self a s)).add
        (ih (fun b hb => hp b (Finset.mem_insert_of_mem hb)))

theorem pderiv_support_shift {m : ℕ} (i : Fin (m + 1))
    (p : MvPolynomial (Fin (m + 1)) ℂ) (d : Fin (m + 1) →₀ ℕ)
    (hd : d ∈ (MvPolynomial.pderiv i p).support) : d + Finsupp.single i 1 ∈ p.support := by
  apply MvPolynomial.mem_support_iff.mpr
  intro hz
  have hcoeff := MvPolynomial.mem_support_iff.mp hd
  apply hcoeff
  rw [MvPolynomial.coeff_pderiv, hz, zero_mul]

theorem HasWeightedDegreeLE.pderiv {m : ℕ} {w : Fin (m + 1) → ℝ} {N : ℝ}
    {p : MvPolynomial (Fin (m + 1)) ℂ} (hp : HasWeightedDegreeLE w N p)
    (i : Fin (m + 1)) : HasWeightedDegreeLE w (N - w i) (MvPolynomial.pderiv i p) := by
  intro d hd
  apply (le_sub_iff_add_le).mpr
  have h := hp (d + Finsupp.single i 1) (pderiv_support_shift i p d hd)
  simpa only [monomialWeight_add, monomialWeight_single] using h

theorem HasWeightedDegreeLE.X_mul {m : ℕ} {w : Fin (m + 1) → ℝ} {N : ℝ}
    {p : MvPolynomial (Fin (m + 1)) ℂ} (hp : HasWeightedDegreeLE w N p)
    (i : Fin (m + 1)) : HasWeightedDegreeLE w (N + w i) (MvPolynomial.X i * p) := by
  intro d hd
  have hsupp := MvPolynomial.support_X_mul i p
  rw [hsupp] at hd
  obtain ⟨e, he, hed⟩ := Finset.mem_map.mp hd
  have heq : Finsupp.single i 1 + e = d := hed
  rw [← heq, monomialWeight_add, monomialWeight_single, add_comm (w i)]
  exact add_le_add (hp e he) (le_refl (w i))

theorem HasWeightedDegreeLE.X_mul_pderiv {m : ℕ} {w : Fin (m + 1) → ℝ} {N : ℝ}
    {p : MvPolynomial (Fin (m + 1)) ℂ} (hp : HasWeightedDegreeLE w N p)
    (i : Fin (m + 1)) : HasWeightedDegreeLE w N (MvPolynomial.X i * MvPolynomial.pderiv i p) := by
  simpa only [sub_add_cancel] using (hp.pderiv i).X_mul i

theorem HasWeightedDegreeLE.pderiv_preserves {m : ℕ} {w : Fin (m + 1) → ℝ}
    {N : ℝ} {p : MvPolynomial (Fin (m + 1)) ℂ}
    (hp : HasWeightedDegreeLE w N p) (i : Fin (m + 1)) (hi : 0 ≤ w i) :
    HasWeightedDegreeLE w N (MvPolynomial.pderiv i p) :=
  (hp.pderiv i).mono (sub_le_self N hi)

end

end PiExponentApprox

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Polynomials_PolynomialFrame
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentApprox

noncomputable section

theorem derivation_finset_sum_apply {α : Type*} (m : ℕ) (s : Finset α)
    (D : α → Derivation ℂ (FramePolynomial m) (FramePolynomial m))
    (p : FramePolynomial m) : (∑ a ∈ s, D a) p = ∑ a ∈ s, D a p := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, Derivation.zero_apply]
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, Derivation.add_apply, ih]

@[simp] theorem logarithmicDerivation_apply (m : ℕ) (p : FramePolynomial m) :
    logarithmicDerivation m p =
      MvPolynomial.X (0 : Fin (m + 1)) * MvPolynomial.pderiv 0 p +
        ∑ i : Fin m, MvPolynomial.pderiv i.succ p := by
  simp only [logarithmicDerivation, Derivation.add_apply, Derivation.smul_apply,
    derivation_finset_sum_apply, smul_eq_mul]

theorem HasWeightedDegreeLE.logarithmicDerivation {m : ℕ}
    {w : Fin (m + 1) → ℝ} {N : ℝ} {p : FramePolynomial m}
    (hp : HasWeightedDegreeLE w N p) (hw : ∀ i, 0 ≤ w i) :
    HasWeightedDegreeLE w N (PiExponentApprox.logarithmicDerivation m p) := by
  rw [logarithmicDerivation_apply]
  apply (hp.X_mul_pderiv 0).add
  exact HasWeightedDegreeLE.sum Finset.univ _
    (fun i _ => hp.pderiv_preserves i.succ (hw i.succ))

theorem HasWeightedDegreeLE.polynomialFrame {m : ℕ}
    {w : Fin (m + 1) → ℝ} {N : ℝ} {p : FramePolynomial m}
    (hp : HasWeightedDegreeLE w N p) (hw : ∀ i, 0 ≤ w i) (i : Fin (m + 1)) :
    HasWeightedDegreeLE w N (PiExponentApprox.polynomialFrame m i p) := by
  by_cases hi : i = 0
  · subst i
    rw [polynomialFrame_zero]
    exact hp.logarithmicDerivation hw
  · rw [polynomialFrame_pos m i hi]
    exact hp.pderiv_preserves i (hw i)

theorem HasWeightedDegreeLE.polynomialFrameWord {m : ℕ}
    {w : Fin (m + 1) → ℝ} {N : ℝ} {p : FramePolynomial m}
    (hp : HasWeightedDegreeLE w N p) (hw : ∀ i, 0 ≤ w i)
    (word : List (Fin (m + 1))) :
    HasWeightedDegreeLE w N (PiExponentApprox.polynomialFrameWord m word p) := by
  induction word with
  | nil => exact hp
  | cons i word ih => exact ih.polynomialFrame hw i

end
end PiExponentApprox

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Jets_FormalLogJet
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.FormalLogJet
open MvPowerSeries
open PiExponent.FormalJetDerivatives

variable {R : Type*} [CommRing R]

theorem pderiv_zero_liftSeries (m : ℕ) (f : PowerSeries R) :
    pderiv R 0 (liftSeries m f) = liftSeries m (PowerSeries.derivative R f) := by
  ext d
  rw [coeff_pderiv, coeff_liftSeries, coeff_liftSeries, PowerSeries.coeff_derivative]
  have ht : (d + Finsupp.single (0 : Fin (m+1)) 1).tail = d.tail := by
    ext i
    simp [Finsupp.tail_apply]
  simp only [ht, Finsupp.add_apply, Finsupp.single_eq_same]
  split_ifs <;> simp_all

theorem pderiv_succ_liftSeries (m : ℕ) (i : Fin m) (f : PowerSeries R) :
    pderiv R i.succ (liftSeries m f) = 0 := by
  ext d
  rw [coeff_pderiv, coeff_liftSeries, coeff_zero]
  have ht : (d + Finsupp.single i.succ 1).tail ≠ 0 := by
    intro h
    have hi := DFunLike.congr_fun h i
    simp [Finsupp.tail_apply] at hi
  simp [ht]

@[simp] theorem pderiv_succ_formalLog (m : ℕ) (i : Fin m) :
    pderiv ℂ i.succ (formalLog m) = 0 := pderiv_succ_liftSeries m i _

theorem _root_.PowerSeries.derivative_log_mul_one_add_X {A : Type*} [CommRing A] [Algebra ℚ A] :
    PowerSeries.derivative A (PowerSeries.log A) * (1 + PowerSeries.X) = 1 := by
  rw [PowerSeries.deriv_log]
  ext n
  rcases n with _ | n
  · simp
  · rw [mul_add, mul_one, map_add, PowerSeries.coeff_succ_mul_X]
    simp [PowerSeries.coeff_mk, pow_succ]

theorem one_add_X_mul_pderiv_formalLog (m : ℕ) :
    (1 + X 0) * pderiv ℂ 0 (formalLog m) = 1 := by
  have h := congrArg (liftSeries m) (PowerSeries.derivative_log_mul_one_add_X (A := ℂ))
  rw [map_mul, map_add, map_one, liftSeries_X] at h
  rw [formalLog, pderiv_zero_liftSeries, mul_comm]
  exact h

theorem derivation_map_of_X {σ S : Type*} [CommRing S] [Algebra R S]
    (φ : MvPolynomial σ R →ₐ[R] S)
    (D : Derivation R (MvPolynomial σ R) (MvPolynomial σ R))
    (δ : Derivation R S S)
    (hX : ∀ i, φ (D (MvPolynomial.X i)) = δ (φ (MvPolynomial.X i)))
    (p : MvPolynomial σ R) : φ (D p) = δ (φ p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    simp only [Derivation.leibniz, smul_eq_mul, map_add, map_mul, hp, hX]

theorem formalJet_frame_X {m : ℕ} (c : Fin m → ℂ) (i j : Fin (m+1)) :
    formalJet c (PiExponentApprox.polynomialFrame m i (MvPolynomial.X j)) =
      jetFrame m i (formalJet c (MvPolynomial.X j)) := by
  classical
  cases i using Fin.cases with
  | zero =>
    cases j using Fin.cases with
    | zero =>
      simp [PiExponentApprox.polynomialFrame_zero,
        PiExponentApprox.logarithmicDerivation_apply, MvPolynomial.pderiv_X]
    | succ j =>
      simp [PiExponentApprox.polynomialFrame_zero,
        PiExponentApprox.logarithmicDerivation_apply, MvPolynomial.pderiv_X,
        Pi.single_apply, MvPowerSeries.pderiv_X_of_ne,
        one_add_X_mul_pderiv_formalLog]
  | succ i =>
    rw [PiExponentApprox.polynomialFrame_pos m i.succ (Fin.succ_ne_zero i),
      jetFrame_pos m i.succ (Fin.succ_ne_zero i)]
    cases j using Fin.cases with
    | zero => simp [MvPowerSeries.pderiv_X_of_ne (Ne.symm (Fin.succ_ne_zero i))]
    | succ j =>
      by_cases hij : i = j
      · subst j; simp
      · simp [MvPowerSeries.pderiv_X_of_ne, Ne.symm hij]

theorem formalJet_polynomialFrame {m : ℕ} (c : Fin m → ℂ)
    (i : Fin (m+1)) (p : PiExponentApprox.FramePolynomial m) :
    formalJet c (PiExponentApprox.polynomialFrame m i p) =
      jetFrame m i (formalJet c p) :=
  derivation_map_of_X (formalJet c) (PiExponentApprox.polynomialFrame m i)
    (jetFrame m i) (formalJet_frame_X c i) p

theorem formalJet_polynomialFrameWord {m : ℕ} (c : Fin m → ℂ)
    (word : List (Fin (m+1))) (p : PiExponentApprox.FramePolynomial m) :
    formalJet c (PiExponentApprox.polynomialFrameWord m word p) =
      jetFrameWord m word (formalJet c p) := by
  induction word with
  | nil => rfl
  | cons i word ih =>
    rw [PiExponentApprox.polynomialFrameWord_cons, formalJet_polynomialFrame, ih]
    rfl

theorem formalJet_polynomialFrameWord_vanishing {m : ℕ} (c : Fin m → ℂ)
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 ≤ v i) (H : ℚ)
    (p : PiExponentApprox.FramePolynomial m)
    (hp : formalJet c p ∈ JetGeometry.rationalWeightedIdeal v hv H)
    (word : List (Fin (m+1))) :
    formalJet c (PiExponentApprox.polynomialFrameWord m word p) ∈
      JetGeometry.rationalWeightedIdeal v hv (H - (word.map v).sum) := by
  rw [formalJet_polynomialFrameWord]
  exact jetFrameWord_mem_rationalWeightedIdeal v hv H (formalJet c p) hp word

end PiExponent.FormalLogJet

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Analysis_FormalLogTruncation
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
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

end PiExponent.FormalLogTruncation

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_FrameEquationFamily
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.FrameEquationFamily

open scoped BigOperators
open PiExponentApprox

theorem monomialWeight_eq_weight {m : ℕ} (W : Fin (m + 1) → ℝ)
    (d : Fin (m + 1) →₀ ℕ) :
    monomialWeight W d = Finsupp.weight W d := by
  simp only [monomialWeight, Finsupp.weight_eq_sum, nsmul_eq_mul]

theorem hasWeightedDegreeLE_iff_supportBound {m : ℕ} (W : Fin (m + 1) → ℝ)
    (N : ℝ) (F : FramePolynomial m) :
    HasWeightedDegreeLE W N F ↔ WeightedSliceDegree.SupportBound W N F := by
  simp only [HasWeightedDegreeLE, WeightedSliceDegree.SupportBound, monomialWeight_eq_weight]

end PiExponent.FrameEquationFamily

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_CurveZeroPole
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.CurveNormalizationModel.infinityChartInclusion_isOpenImmersion _root_.OAI.PiExponent.CurveNormalizationModel.infinityOverlap_isOpenImmersion _root_.OAI.PiExponent.CurveNormalizationModel.parameterChartProjection_isFinite _root_.OAI.PiExponent.CurveNormalizationModel.parameterChart_noetherian _root_.OAI.PiExponent.CurveNormalizationModel.zeroChartInclusion_isOpenImmersion _root_.OAI.PiExponent.CurveNormalizationModel.zeroOverlap_isOpenImmersion _root_.OAI.PiExponent.CurveValuationCenter.parameterValuationCenter_isPrime _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Polynomial nonZeroDivisors

namespace PiExponent.CurveZeroPole

theorem fiberDegree_eq_rank {R : Type*} [CommRing R] [IsDomain R]
    (S : Type*) [CommRing S] [Algebra R S]
    [Module.Finite R S] [Module.Flat R S]
    (p : Ideal R) [p.IsPrime] :
    fiberDegree S p = Module.finrank R S := by
  let := (Algebra.QuasiFinite.finite_primesOver (R := R) (S := S) p).fintype
  exact Ideal.sum_ramification_inertia_eq_finrank p S

theorem fiberDegree_eq_fractionField_rank
    (R K S L : Type*) [CommRing R] [IsDomain R] [Field K]
    [CommRing S] [Field L] [Algebra R S] [Algebra K L]
    [Algebra R K] [Algebra S L] [Algebra R L]
    [IsScalarTower R K L] [IsScalarTower R S L]
    [IsFractionRing R K] [IsFractionRing S L]
    [Module.Finite R S] [Module.Flat R S]
    (p : Ideal R) [p.IsPrime] :
    fiberDegree S p = Module.finrank K L := by
  rw [fiberDegree_eq_rank, IsFractionRing.finrank_eq R K S L]

theorem functionField_fiberDegree
    (F E : Type*) [Field F] [Field E]
    [Algebra F[X] E] [Algebra (RatFunc F) E]
    [IsScalarTower F[X] (RatFunc F) E]
    [FunctionField F E] [Algebra.IsSeparable (RatFunc F) E]
    (p : Ideal F[X]) [p.IsPrime] :
    fiberDegree (FunctionField.ringOfIntegers F E) p =
      Module.finrank (RatFunc F) E := by
  let : Module.IsTorsionFree F[X] (FunctionField.ringOfIntegers F E) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      (FunctionField.ringOfIntegers.algebraMap_injective F E)
  exact fiberDegree_eq_fractionField_rank F[X] (RatFunc F)
    (FunctionField.ringOfIntegers F E) E p

theorem parameter_inverse_degree_eq
    {F E : Type*} [Field F] [Field E] [Algebra F E] (f : E) :
    Module.finrank (IntermediateField.adjoin F {f⁻¹}) E =
      Module.finrank (IntermediateField.adjoin F {f}) E := by
  rw [adjoin_inverse_eq]

theorem parameter_finrank {F E : Type*} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f) :
    let := parameterAlgebra f hf
    Module.finrank (RatFunc F) E = Module.finrank (IntermediateField.adjoin F {f}) E := by
  let := parameterAlgebra f hf
  apply Algebra.finrank_eq_of_equiv_equiv
    (RatFunc.algEquivOfTranscendental f hf).toRingEquiv (RingEquiv.refl E)
  rfl

theorem parameterFiberDegree_eq {F E : Type*} [Field F] [CharZero F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E] :
    parameterFiberDegree f hf = Module.finrank (IntermediateField.adjoin F {f}) E := by
  let := parameterAlgebra f hf
  let := parameterPolynomialAlgebra f hf
  let := parameter_scalarTower f hf
  let := parameter_finite f hf
  change fiberDegree (FunctionField.ringOfIntegers F E) (zeroPrime F) = _
  rw [functionField_fiberDegree]
  exact parameter_finrank f hf

theorem zeroFiber_inertiaDeg_eq_one (F S : Type*) [Field F] [IsAlgClosed F]
    [CommRing S] [Algebra F[X] S] [Module.Finite F[X] S]
    (q : Ideal S) [q.IsPrime] [q.LiesOver (zeroPrime F)] :
    q.inertiaDeg F[X] = 1 := by
  have : q.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal q (zeroPrime F)
  let : Field (F[X] ⧸ zeroPrime F) := Ideal.Quotient.field _
  let : Field (S ⧸ q) := Ideal.Quotient.field _
  let : IsAlgClosed (F[X] ⧸ zeroPrime F) :=
    IsAlgClosed.of_ringEquiv F _ (zeroPrimeQuotientEquiv F).symm
  rw [Ideal.inertiaDeg_eq_of_isMaximal (zeroPrime F) q]
  apply Module.finrank_of_bijective_algebraMap
  apply IsAlgClosed.algebraMap_bijective_of_isIntegral

theorem zeroFiberLength_eq_fiberDegree (F S : Type*) [Field F] [IsAlgClosed F]
    [CommRing S] [Algebra F[X] S] [Module.Finite F[X] S] :
    zeroFiberLength F S = fiberDegree S (zeroPrime F) := by
  unfold zeroFiberLength fiberDegree
  apply Finset.sum_congr rfl
  intro q _
  rw [zeroFiber_inertiaDeg_eq_one F S q.1, mul_one,
    Ideal.ramificationIdx_eq (zeroPrime F) q.1]
  have hm : (zeroPrime F).map (algebraMap F[X] (Localization.AtPrime q.1)) =
      Ideal.span {algebraMap F[X] (Localization.AtPrime q.1) Polynomial.X} := by
    calc
      _ = (Ideal.span {Polynomial.X}).map
          (algebraMap F[X] (Localization.AtPrime q.1)) :=
        congrArg (Ideal.map (algebraMap F[X] (Localization.AtPrime q.1))) (zeroPrime_eq_span_X F)
      _ = _ := by rw [Ideal.map_span, Set.image_singleton]
  exact congrArg (fun I : Ideal (Localization.AtPrime q.1) =>
    (Module.length (Localization.AtPrime q.1) ((Localization.AtPrime q.1) ⧸ I)).toNat) hm.symm

theorem parameterZeroLength_eq_degree
    {F E : Type*} [Field F] [CharZero F] [IsAlgClosed F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E] :
    parameterZeroLength f hf = Module.finrank (IntermediateField.adjoin F {f}) E := by
  let := parameterAlgebra f hf
  let := parameterPolynomialAlgebra f hf
  let := parameter_scalarTower f hf
  let := parameter_finite f hf
  change zeroFiberLength F (FunctionField.ringOfIntegers F E) = _
  rw [zeroFiberLength_eq_fiberDegree]
  exact parameterFiberDegree_eq f hf

theorem zero_pole_length_eq
    {F E : Type*} [Field F] [CharZero F] [IsAlgClosed F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E] :
    letI : FiniteDimensional (IntermediateField.adjoin F {f⁻¹}) E :=
      (adjoin_inverse_eq (F := F) f).symm ▸ inferInstance
    parameterZeroLength f hf = parameterZeroLength f⁻¹ (transcendental_inverse f hf) := by
  let : FiniteDimensional (IntermediateField.adjoin F {f⁻¹}) E :=
    (adjoin_inverse_eq (F := F) f).symm ▸ inferInstance
  rw [parameterZeroLength_eq_degree, parameterZeroLength_eq_degree, parameter_inverse_degree_eq]

theorem primeFieldValuation_algebraMap
    (S E : Type*) [CommRing S] [IsDedekindDomain S]
    [Field E] [Algebra S E] [IsFractionRing S E]
    (q : IsDedekindDomain.HeightOneSpectrum S) (a : S) (ha : a ≠ 0) :
    primeFieldValuation S E q (algebraMap S E a) =
      CurveLocalOrder.enatToIntegerOrder
        (Module.length (Localization.AtPrime q.asIdeal)
          ((Localization.AtPrime q.asIdeal) ⧸
            Ideal.span {algebraMap S (Localization.AtPrime q.asIdeal) a})) := by
  let A := Localization.AtPrime q.asIdeal
  let := IsLocalization.localizationAlgebraOfSubmonoidLe A E
    q.asIdeal.primeCompl S⁰ q.asIdeal.primeCompl_le_nonZeroDivisors
  let := IsLocalization.localization_isScalarTower_of_submonoid_le A E
    q.asIdeal.primeCompl S⁰ q.asIdeal.primeCompl_le_nonZeroDivisors
  let := IsFractionRing.isFractionRing_of_isDomain_of_isLocalization q.asIdeal.primeCompl A E
  let := IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain S q.ne_bot A
  change CurveLocalOrder.fractionAddValuation A E (algebraMap S E a) = _
  rw [IsScalarTower.algebraMap_apply S A E]
  apply CurveLocalOrder.fraction_order_eq_principal_colength
  exact (map_ne_zero_iff _ (IsLocalization.injective A
    q.asIdeal.primeCompl_le_nonZeroDivisors)).mpr ha

theorem primeField_integerOrder_algebraMap
    (S E : Type*) [CommRing S] [IsDedekindDomain S]
    [Field E] [Algebra S E] [IsFractionRing S E]
    (q : IsDedekindDomain.HeightOneSpectrum S) (a : S) (ha : a ≠ 0) :
    WeightedCurveDegree.integerOrder (primeFieldValuation S E q)
      (Units.mk0 (algebraMap S E a) ((map_ne_zero_iff _ (IsFractionRing.injective S E)).mpr ha)) =
      ((Module.length (Localization.AtPrime q.asIdeal)
        ((Localization.AtPrime q.asIdeal) ⧸
          Ideal.span {algebraMap S (Localization.AtPrime q.asIdeal) a})).toNat : ℤ) := by
  let A := Localization.AtPrime q.asIdeal
  let := IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain S q.ne_bot A
  have ha' : algebraMap S A a ≠ 0 :=
    (map_ne_zero_iff _ (IsLocalization.injective A
      q.asIdeal.primeCompl_le_nonZeroDivisors)).mpr ha
  apply WithTop.coe_injective
  rw [WeightedCurveDegree.coe_integerOrder]
  change primeFieldValuation S E q (algebraMap S E a) = _
  rw [primeFieldValuation_algebraMap S E q a ha]
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp
    (CurveLocalOrder.principal_colength_ne_top ha')
  change CurveLocalOrder.enatToIntegerOrder
    (Module.length A (A ⧸ Ideal.span {algebraMap S A a})) = _
  rw [← hn]
  simp

theorem zeroFiberIntegerOrderSum_eq_length (F S E : Type*) [Field F] [CommRing S]
    [IsDedekindDomain S] [Field E] [Algebra F[X] S] [FaithfulSMul F[X] S]
    [Module.Finite F[X] S] [Algebra S E] [IsFractionRing S E]
    [Algebra F[X] E] [IsScalarTower F[X] S E] :
    zeroFiberIntegerOrderSum F S E = (zeroFiberLength F S : ℤ) := by
  unfold zeroFiberIntegerOrderSum zeroFiberLength
  rw [Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro q _
  have hx : algebraMap F[X] S Polynomial.X ≠ 0 :=
    (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective F[X] S)).mpr Polynomial.X_ne_zero
  have he := primeField_integerOrder_algebraMap S E
    (zeroFiberHeightOne F S q) (algebraMap F[X] S Polynomial.X) hx
  calc
    _ = WeightedCurveDegree.integerOrder
        (primeFieldValuation S E (zeroFiberHeightOne F S q))
        (Units.mk0 (algebraMap S E (algebraMap F[X] S Polynomial.X))
          ((map_ne_zero_iff _ (IsFractionRing.injective S E)).mpr hx)) := by
      congr 1
      ext
      exact IsScalarTower.algebraMap_apply F[X] S E Polynomial.X
    _ = _ := he
    _ = _ := by
      let A := Localization.AtPrime q.1
      have hi : Ideal.span {algebraMap S A (algebraMap F[X] S Polynomial.X)} =
          Ideal.span {algebraMap F[X] A Polynomial.X} :=
        congrArg (fun z : A => Ideal.span {z})
          (IsScalarTower.algebraMap_apply F[X] S A Polynomial.X).symm
      exact congrArg (fun I : Ideal A => ((Module.length A (A ⧸ I)).toNat : ℤ)) hi

theorem parameterZeroOrder_eq_length
    {F E : Type*} [Field F] [CharZero F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E] :
    parameterZeroOrder f hf = (parameterZeroLength f hf : ℤ) := by
  let := parameterAlgebra f hf
  let := parameterPolynomialAlgebra f hf
  let := parameter_scalarTower f hf
  let := parameter_finite f hf
  let : Module.IsTorsionFree F[X] (FunctionField.ringOfIntegers F E) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      (FunctionField.ringOfIntegers.algebraMap_injective F E)
  exact zeroFiberIntegerOrderSum_eq_length F (FunctionField.ringOfIntegers F E) E

theorem zero_pole_order_eq
    {F E : Type*} [Field F] [CharZero F] [IsAlgClosed F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E] :
    letI : FiniteDimensional (IntermediateField.adjoin F {f⁻¹}) E :=
      (adjoin_inverse_eq (F := F) f).symm ▸ inferInstance
    parameterZeroOrder f hf = parameterZeroOrder f⁻¹ (transcendental_inverse f hf) := by
  let : FiniteDimensional (IntermediateField.adjoin F {f⁻¹}) E :=
    (adjoin_inverse_eq (F := F) f).symm ▸ inferInstance
  rw [parameterZeroOrder_eq_length, parameterZeroOrder_eq_length, zero_pole_length_eq]

theorem parameterZeroOrder_eq_sum
    {F E : Type*} [Field F] [CharZero F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E] :
    letI := parameterZeroPlacesFintype f hf
    parameterZeroOrder f hf =
      ∑ q : parameterZeroPlaces f hf,
        WeightedCurveDegree.integerOrder (parameterPlaceValuation f hf q)
          (Units.mk0 f hf.ne_zero) := by
  let := parameterAlgebra f hf
  let := parameterPolynomialAlgebra f hf
  let := parameter_scalarTower f hf
  let := parameter_finite f hf
  let : Module.IsTorsionFree F[X] (FunctionField.ringOfIntegers F E) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      (FunctionField.ringOfIntegers.algebraMap_injective F E)
  dsimp only [parameterZeroOrder, zeroFiberIntegerOrderSum, parameterPlaceValuation]
  apply Finset.sum_congr rfl
  intro q _
  congr 1
  ext
  change parameterEmbedding f hf RatFunc.X = f
  exact parameterEmbedding_X f hf

end PiExponent.CurveZeroPole

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_CurveProductFormula
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.CurveNormalizationModel.infinityChartInclusion_isOpenImmersion _root_.OAI.PiExponent.CurveNormalizationModel.infinityOverlap_isOpenImmersion _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.PlaceValuationRing.constantsAlgebra _root_.OAI.PiExponent.PlaceValuationRing.discreteValuationRing _root_.OAI.PiExponent.PlaceValuationRing.scalarTower _root_.OAI.PiExponent.PlaceValuationRing.valuation_nontrivial _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace PiExponent.CurveProductFormula
open PiExponent.CurveZeroPole PiExponent.CurveValuationCenter
open PiExponent.WeightedCurveDegree

theorem sum_positiveOrders_eq
    {F E : Type*} [Field F] [CharZero F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E] :
    ∑ p ∈ positivePlaces f hf, placeOrder p (Units.mk0 f hf.ne_zero) = parameterZeroOrder f hf := by
  let := positivePlacesFintype f hf
  let := parameterZeroPlacesFintype f hf
  rw [Finset.sum_subtype (positivePlaces f hf) (mem_positivePlaces f hf)]
  calc
    _ = ∑ q : parameterZeroPlaces f hf,
        placeOrder (parameterNormalizedPlace f hf q) (Units.mk0 f hf.ne_zero) :=
      ((positivePlaceEquivZeroPlaces f hf).symm.sum_comp
        (fun p => placeOrder p.1 (Units.mk0 f hf.ne_zero))).symm
    _ = _ := (parameterZeroOrder_eq_sum f hf).symm

theorem parameterZeroOrder_inst_irrel {F E : Type*} [Field F] [CharZero F] [Field E] [Algebra F E]
    (g : E) (hg : Transcendental F g)
    (i1 i2 : FiniteDimensional (IntermediateField.adjoin F {g}) E) :
    @parameterZeroOrder F E _ _ _ _ g hg i1 = @parameterZeroOrder F E _ _ _ _ g hg i2 := by
  cases Subsingleton.elim i1 i2
  rfl

theorem principalDivisor_degree_zero
    {F E : Type*} [Field F] [CharZero F] [IsAlgClosed F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E] :
    (principalDivisor f hf).sum (fun _ n => n) = 0 := by
  classical
  let : FiniteDimensional (IntermediateField.adjoin F {f⁻¹}) E :=
    (adjoin_inverse_eq (F := F) f).symm ▸ inferInstance
  let z : Eˣ := Units.mk0 f hf.ne_zero
  let zi : Eˣ := Units.mk0 f⁻¹ (transcendental_inverse f hf).ne_zero
  have hiz : zi = z⁻¹ := by ext; simp [zi, z]
  have hsup : (principalDivisor f hf).support ⊆
      positivePlaces f hf ∪ positivePlaces f⁻¹ (transcendental_inverse f hf) := by
    intro p hp
    have hn : placeOrder p z ≠ 0 := by simpa [z] using Finsupp.mem_support_iff.mp hp
    simpa only [Finset.mem_union, mem_positivePlaces, z, Units.val_mk0] using
      (order_ne_zero_iff_positive_or_inverse p z).mp hn
  have hdisj : Disjoint (positivePlaces f hf)
      (positivePlaces f⁻¹ (transcendental_inverse f hf)) := by
    apply Finset.disjoint_left.mpr
    intro p hp hi
    have hp' : 0 < placeOrder p z :=
      (valuation_pos_iff_order_pos p z).mp ((mem_positivePlaces f hf p).mp hp)
    have hi' : 0 < placeOrder p zi :=
      (valuation_pos_iff_order_pos p zi).mp
        ((mem_positivePlaces f⁻¹ (transcendental_inverse f hf) p).mp hi)
    rw [hiz, placeOrder_inv] at hi'
    omega
  rw [Finsupp.sum_of_support_subset _ hsup _ (by intro _ _; rfl)]
  simp only [principalDivisor_apply]
  rw [Finset.sum_union hdisj, sum_positiveOrders_eq]
  have hi : (∑ p ∈ positivePlaces f⁻¹ (transcendental_inverse f hf), placeOrder p z) =
      -parameterZeroOrder f⁻¹ (transcendental_inverse f hf) := by
    calc
      _ = ∑ p ∈ positivePlaces f⁻¹ (transcendental_inverse f hf), -(placeOrder p zi) := by
        apply Finset.sum_congr rfl
        intro p _
        rw [hiz, placeOrder_inv, neg_neg]
      _ = -(∑ p ∈ positivePlaces f⁻¹ (transcendental_inverse f hf), placeOrder p zi) :=
        Finset.sum_neg_distrib (fun p => placeOrder p zi)
      _ = _ := congrArg Neg.neg (sum_positiveOrders_eq f⁻¹ (transcendental_inverse f hf))
  change parameterZeroOrder f hf + (∑ p ∈ positivePlaces f⁻¹ (transcendental_inverse f hf),
    placeOrder p z) = 0
  have h3 : parameterZeroOrder f hf = parameterZeroOrder f⁻¹ (transcendental_inverse f hf) :=
    (zero_pole_order_eq f hf).trans (parameterZeroOrder_inst_irrel _ _ _ _)
  rw [hi, h3]
  exact add_neg_cancel _

end PiExponent.CurveProductFormula

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Jets_FormalBranchOrderRational
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponent.FormalBranchOrder

open MvPowerSeries

variable {σ τ R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

theorem rational_weight_le_of_contact
    (v : σ → ℚ) (μ : ℚ) (a : σ → MvPowerSeries τ S)
    (hcontact : ∀ i (k : ℕ), (a i).order = (k : ℕ∞) → μ * v i ≤ (k : ℚ))
    (d : σ →₀ ℕ) (n : ℕ)
    (hbound : d.weight (order ∘ a) ≤ (n : ℕ∞)) :
    μ * d.weight v ≤ (n : ℚ) := by
  classical
  have hfinite : ∀ i ∈ d.support, (a i).order ≠ ⊤ := by
    intro i hi
    apply ne_top_of_le_ne_top (by simp : (n : ℕ∞) ≠ ⊤)
    exact (Finsupp.le_weight_of_ne_zero' (order ∘ a)
      (Finsupp.mem_support_iff.mp hi)).trans hbound
  have hsum :
      ((∑ i ∈ d.support, d i * (a i).order.toNat : ℕ) : ℕ∞) =
        d.weight (order ∘ a) := by
    simp only [Nat.cast_sum, Nat.cast_mul, Finsupp.weight_apply,
      Finsupp.sum, Function.comp_apply, nsmul_eq_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [ENat.natCast_toNat (hfinite i hi)]
  have hnat : (∑ i ∈ d.support, d i * (a i).order.toNat : ℕ) ≤ n := by
    exact_mod_cast hsum.symm ▸ hbound
  calc
    μ * d.weight v = ∑ i ∈ d.support, (d i : ℚ) * (μ * v i) := by
      simp only [Finsupp.weight_apply, Finsupp.sum, nsmul_eq_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ ≤ ∑ i ∈ d.support, (d i : ℚ) * ((a i).order.toNat : ℚ) := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left
        (hcontact i _ (ENat.natCast_toNat (hfinite i hi)).symm) (by positivity)
    _ ≤ (n : ℚ) := by exact_mod_cast hnat

theorem rational_order_subst_of_jet_vanishing
    (v : σ → ℚ) (μ H : ℚ) (hμ : 0 ≤ μ)
    (f : MvPowerSeries σ R) (a : σ → MvPowerSeries τ S)
    (ha : HasSubst a)
    (hjet : ∀ d : σ →₀ ℕ, d.weight v < H → coeff d f = 0)
    (hcontact : ∀ i (k : ℕ), (a i).order = (k : ℕ∞) → μ * v i ≤ (k : ℚ)) :
    (⌈μ * H⌉₊ : ℕ∞) ≤ (f.subst a).order := by
  classical
  by_cases htop : (f.subst a).order = ⊤
  · rw [htop]
    exact le_top
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp htop
  rw [← hn, ENat.natCast_le_natCast, Nat.ceil_le]
  obtain ⟨d, hd⟩ := ENat.exists_eq_iInf
    (fun d : σ →₀ ℕ => ⨅ _ : coeff d f ≠ 0, d.weight (order ∘ a))
  have hbound : (⨅ _ : coeff d f ≠ 0, d.weight (order ∘ a)) ≤ (n : ℕ∞) :=
    hd.le.trans ((le_weightedOrder_subst (fun _ : τ => 1) ha f).trans hn.ge)
  have hdne : coeff d f ≠ 0 := by
    intro he
    simp [he] at hbound
  have hbound' : d.weight (order ∘ a) ≤ (n : ℕ∞) := by
    simpa [hdne] using hbound
  have hH : H ≤ d.weight v := by
    by_contra! h
    exact hdne (hjet d h)
  exact (mul_le_mul_of_nonneg_left hH hμ).trans
    (rational_weight_le_of_contact v μ a hcontact d n hbound')

theorem rational_order_subst_of_mem_weightedIdeal
    (v : σ → ℚ) (hv : ∀ i, 0 ≤ v i) (μ H : ℚ) (hμ : 0 ≤ μ)
    (f : MvPowerSeries σ R) (a : σ → MvPowerSeries τ S)
    (ha : HasSubst a) (hf : f ∈ JetGeometry.rationalWeightedIdeal v hv H)
    (hcontact : ∀ i (k : ℕ), (a i).order = (k : ℕ∞) → μ * v i ≤ (k : ℚ)) :
    (⌈μ * H⌉₊ : ℕ∞) ≤ (f.subst a).order :=
  rational_order_subst_of_jet_vanishing v μ H hμ f a ha hf hcontact

theorem rational_powerSeries_order_subst_of_mem_weightedIdeal
    (v : σ → ℚ) (hv : ∀ i, 0 ≤ v i) (μ H : ℚ) (hμ : 0 ≤ μ)
    (f : MvPowerSeries σ R) (a : σ → PowerSeries S)
    (ha : HasSubst a) (hf : f ∈ JetGeometry.rationalWeightedIdeal v hv H)
    (hcontact : ∀ i (k : ℕ), (a i).order = (k : ℕ∞) → μ * v i ≤ (k : ℚ)) :
    (⌈μ * H⌉₊ : ℕ∞) ≤ PowerSeries.order (f.subst a) := by
  simp only [PowerSeries.order_eq_order] at hcontact ⊢
  exact rational_order_subst_of_mem_weightedIdeal v hv μ H hμ f a ha hf hcontact

end PiExponent.FormalBranchOrder

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Jets_FormalBranchEvaluation
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.FormalBranchEvaluation
open MvPowerSeries
open FormalLogJet FormalLogTruncation

theorem subst_liftSeries {m : ℕ} (a : Fin (m+1) → PowerSeries ℂ) (ha : HasSubst a)
    (f : PowerSeries ℂ) :
    subst a (liftSeries m f) = PowerSeries.subst (a 0) f := by
  rw [liftSeries_eq_toMvPowerSeries, PowerSeries.subst_toMvPowerSeries ha]

theorem formalJet_subst_branch {m : ℕ} (c : Fin m → ℂ) (y : PowerSeries ℂ)
    (x : Fin m → PowerSeries ℂ) (hy : PowerSeries.constantCoeff y = 1)
    (hx : ∀ i, PowerSeries.constantCoeff (x i) = c i)
    (p : PiExponentApprox.FramePolynomial m) :
    subst (branchCoordinates c y x) (formalJet c p) =
      MvPolynomial.aeval (Fin.cases y x) p := by
  let ha := branchCoordinates_hasSubst c y x hy hx
  have heq : (substAlgHom ha).comp (formalJet c) = MvPolynomial.aeval (Fin.cases y x) := by
    apply MvPolynomial.algHom_ext
    intro i
    cases i using Fin.cases with
    | zero =>
      simp only [AlgHom.comp_apply, formalJet_Y, map_add, map_one, substAlgHom_X,
        MvPolynomial.aeval_X, Fin.cases_zero]
      change 1 + (y-1) = y
      ring
    | succ i =>
      simp only [AlgHom.comp_apply, formalJet_X, map_add,
        MvPolynomial.aeval_X, Fin.cases_succ]
      rw [substAlgHom_X]
      have hl : substAlgHom ha (formalLog m) = PowerSeries.subst (y-1) (PowerSeries.log ℂ) := by
        rw [substAlgHom_apply, formalLog, subst_liftSeries _ ha]
        rfl
      rw [hl, substAlgHom_apply, subst_C]
      change PowerSeries.C (c i) +
        (x i - PowerSeries.C (c i) - PowerSeries.subst (y-1) (PowerSeries.log ℂ)) +
        PowerSeries.subst (y-1) (PowerSeries.log ℂ) = x i
      ring
  simpa only [AlgHom.comp_apply, substAlgHom_apply] using AlgHom.congr_fun heq p

theorem polynomialFrameWord_branch_order {m : ℕ}
    (c : Fin m → ℂ) (y : PowerSeries ℂ) (x : Fin m → PowerSeries ℂ)
    (hy : PowerSeries.constantCoeff y = 1)
    (hx : ∀ i, PowerSeries.constantCoeff (x i) = c i)
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 ≤ v i) (μ H : ℚ) (hμ : 0 ≤ μ)
    (p : PiExponentApprox.FramePolynomial m)
    (hp : formalJet c p ∈ JetGeometry.rationalWeightedIdeal v hv H)
    (hcontact : ∀ i (k : ℕ), (branchCoordinates c y x i).order = (k : ℕ∞) →
      μ * v i ≤ (k : ℚ)) (word : List (Fin (m+1))) :
    (⌈μ * (H - (word.map v).sum)⌉₊ : ℕ∞) ≤
      PowerSeries.order (MvPolynomial.aeval (Fin.cases y x)
        (PiExponentApprox.polynomialFrameWord m word p)) := by
  have h := FormalBranchOrder.rational_powerSeries_order_subst_of_mem_weightedIdeal
    v hv μ (H - (word.map v).sum) hμ
    (formalJet c (PiExponentApprox.polynomialFrameWord m word p)) (branchCoordinates c y x)
    (branchCoordinates_hasSubst c y x hy hx)
    (formalJet_polynomialFrameWord_vanishing c v hv H p hp word) hcontact
  rwa [formalJet_subst_branch c y x hy hx] at h

theorem polynomialFrameWord_branch_order_toNat {m : ℕ}
    (c : Fin m → ℂ) (y : PowerSeries ℂ) (x : Fin m → PowerSeries ℂ)
    (hy : PowerSeries.constantCoeff y = 1)
    (hx : ∀ i, PowerSeries.constantCoeff (x i) = c i)
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 ≤ v i) (μ H : ℚ) (hμ : 0 ≤ μ)
    (p : PiExponentApprox.FramePolynomial m)
    (hp : formalJet c p ∈ JetGeometry.rationalWeightedIdeal v hv H)
    (hcontact : ∀ i (k : ℕ), (branchCoordinates c y x i).order = (k : ℕ∞) →
      μ * v i ≤ (k : ℚ)) (word : List (Fin (m+1)))
    (hne : MvPolynomial.aeval (Fin.cases y x)
      (PiExponentApprox.polynomialFrameWord m word p) ≠ 0) :
    μ * (H - (word.map v).sum) ≤
      ((PowerSeries.order (MvPolynomial.aeval (Fin.cases y x)
        (PiExponentApprox.polynomialFrameWord m word p))).toNat : ℚ) := by
  have h := polynomialFrameWord_branch_order c y x hy hx v hv μ H hμ p hp hcontact word
  have hn := PowerSeries.order_eq_top.not.mpr hne
  have hh := ENat.toNat_le_toNat h hn
  exact Nat.ceil_le.mp (by simpa using hh)

end PiExponent.FormalBranchEvaluation

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Jets_DVRBranchJet
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.DVRBranchJet
open PiExponentApprox FormalBranchEvaluation

variable {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Algebra ℂ A] [Algebra.IsIntegral ℂ (IsLocalRing.ResidueField A)]

theorem expansion_aeval {n : ℕ} (x : Fin n → A) (p : MvPolynomial (Fin n) ℂ) :
    DVRBranch.expansion ℂ A (MvPolynomial.aeval x p) =
      MvPolynomial.aeval (fun i => DVRBranch.expansion ℂ A (x i)) p := by
  have h : (DVRBranch.expansion ℂ A).comp (MvPolynomial.aeval x) =
      MvPolynomial.aeval (fun i => DVRBranch.expansion ℂ A (x i)) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp
  exact AlgHom.congr_fun h p

theorem coordinates_centered {m : ℕ} (c : Fin m → ℂ) (y : A) (x : Fin m → A)
    (hy : CurveLocalOrder.residueAugmentation ℂ A y = 1)
    (hx : ∀ i, CurveLocalOrder.residueAugmentation ℂ A (x i) = c i) :
    ∀ i, PowerSeries.constantCoeff (coordinates c y x i) = 0 := by
  intro i
  have ht : MvPowerSeries.constantCoeff (DVRBranch.expansion ℂ A y - 1) = 0 := by
    change PowerSeries.constantCoeff (DVRBranch.expansion ℂ A y - 1) = 0
    simp [hy]
  cases i using Fin.cases with
  | zero => exact ht
  | succ i =>
    change PowerSeries.constantCoeff
      (DVRBranch.expansion ℂ A (x i) - PowerSeries.C (c i) -
        PowerSeries.subst (DVRBranch.expansion ℂ A y - 1) (PowerSeries.log ℂ)) = 0
    change MvPowerSeries.constantCoeff
      (DVRBranch.expansion ℂ A (x i) - PowerSeries.C (c i) -
        PowerSeries.subst (DVRBranch.expansion ℂ A y - 1) (PowerSeries.log ℂ)) = 0
    rw [map_sub, PowerSeries.constantCoeff_subst_eq_zero ht _ PowerSeries.constantCoeff_log,
      sub_zero, map_sub]
    change PowerSeries.constantCoeff (DVRBranch.expansion ℂ A (x i)) -
      PowerSeries.constantCoeff (PowerSeries.C (c i)) = 0
    rw [DVRBranch.expansion_constantCoeff, hx i, PowerSeries.constantCoeff_C, sub_self]

theorem contact_pos {m : ℕ} (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 < v i)
    (c : Fin m → ℂ) (y : A) (x : Fin m → A)
    (hy : CurveLocalOrder.residueAugmentation ℂ A y = 1)
    (hx : ∀ i, CurveLocalOrder.residueAugmentation ℂ A (x i) = c i)
    (hnc : y ≠ 1 ∨ ∃ i, x i ≠ algebraMap ℂ A (c i)) :
    0 < contact v c y x hnc :=
  BranchContact.contact_pos v hv _ _ (coordinates_centered c y x hy hx)

theorem frameWord_addVal_lower {m : ℕ}
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 < v i) (H : ℚ)
    (c : Fin m → ℂ) (y : A) (x : Fin m → A)
    (hy : CurveLocalOrder.residueAugmentation ℂ A y = 1)
    (hx : ∀ i, CurveLocalOrder.residueAugmentation ℂ A (x i) = c i)
    (hnc : y ≠ 1 ∨ ∃ i, x i ≠ algebraMap ℂ A (c i))
    (p : FramePolynomial m)
    (hp : FormalLogJet.formalJet c p ∈
      JetGeometry.rationalWeightedIdeal v (fun i => (hv i).le) H)
    (word : List (Fin (m+1)))
    (hne : MvPolynomial.aeval (Fin.cases y x) (polynomialFrameWord m word p) ≠ 0) :
    contact v c y x hnc * (H - (word.map v).sum) ≤
      ((IsDiscreteValuationRing.addVal A
        (MvPolynomial.aeval (Fin.cases y x) (polynomialFrameWord m word p))).toNat : ℚ) := by
  have heval (q : FramePolynomial m) :
      DVRBranch.expansion ℂ A (MvPolynomial.aeval (Fin.cases y x) q) =
      MvPolynomial.aeval (Fin.cases (DVRBranch.expansion ℂ A y)
        (fun i => DVRBranch.expansion ℂ A (x i))) q := by
    rw [expansion_aeval]
    apply congrArg (fun z => MvPolynomial.aeval z q)
    funext i
    cases i using Fin.cases <;> rfl
  have hne' : MvPolynomial.aeval (Fin.cases (DVRBranch.expansion ℂ A y)
      (fun i => DVRBranch.expansion ℂ A (x i))) (polynomialFrameWord m word p) ≠ 0 := by
    rw [← heval]
    exact (map_ne_zero_iff _ (DVRBranch.expansion_injective ℂ A)).mpr hne
  have hb := polynomialFrameWord_branch_order_toNat c (DVRBranch.expansion ℂ A y)
    (fun i => DVRBranch.expansion ℂ A (x i))
    (by simpa using hy) (fun i => by simpa using hx i)
    v (fun i => (hv i).le) (contact v c y x hnc) H
    (contact_pos v hv c y x hy hx hnc).le p hp
    (BranchContact.contact_bound v hv _ _) word hne'
  rw [← heval, DVRBranch.expansion_order] at hb
  exact hb

theorem frameWord_colength_lower {m : ℕ}
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 < v i) (H : ℚ)
    (c : Fin m → ℂ) (y : A) (x : Fin m → A)
    (hy : CurveLocalOrder.residueAugmentation ℂ A y = 1)
    (hx : ∀ i, CurveLocalOrder.residueAugmentation ℂ A (x i) = c i)
    (hnc : y ≠ 1 ∨ ∃ i, x i ≠ algebraMap ℂ A (c i))
    (p : FramePolynomial m)
    (hp : FormalLogJet.formalJet c p ∈
      JetGeometry.rationalWeightedIdeal v (fun i => (hv i).le) H)
    (word : List (Fin (m+1)))
    (hne : MvPolynomial.aeval (Fin.cases y x) (polynomialFrameWord m word p) ≠ 0) :
    contact v c y x hnc * (H - (word.map v).sum) ≤
      ((Module.length A (A ⧸ Ideal.span {
        MvPolynomial.aeval (Fin.cases y x) (polynomialFrameWord m word p)})).toNat : ℚ) := by
  rw [CurveLocalOrder.length_quotient_span_eq_addVal hne]
  exact frameWord_addVal_lower v hv H c y x hy hx hnc p hp word hne

end PiExponent.DVRBranchJet

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Polynomials_PolynomialPoleBound
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace PiExponent.PolynomialPoleBound

variable {K C σ : Type*} [Field K] [CommRing C] [Algebra C K]

theorem monomial_order_lower (v : AddValuation K (WithTop ℝ))
    (x : σ → K) (w : σ → ℝ) (D : ℝ)
    (hx : ∀ i, ((-w i * D : ℝ) : WithTop ℝ) ≤ v (x i))
    (hc : ∀ c : C, (0 : WithTop ℝ) ≤ v (algebraMap C K c))
    (d : σ →₀ ℕ) (c : C) :
    ((-Finsupp.weight w d * D : ℝ) : WithTop ℝ) ≤
      v (MvPolynomial.aeval x (MvPolynomial.monomial d c)) := by
  classical
  rw [MvPolynomial.aeval_monomial, v.map_mul, Finsupp.prod, valuation_prod]
  have heq : ((-Finsupp.weight w d * D : ℝ) : WithTop ℝ) =
      ∑ i ∈ d.support, d i • ((-w i * D : ℝ) : WithTop ℝ) := by
    simp only [← WithTop.coe_nsmul, ← WithTop.coe_sum]
    apply congrArg (fun r : ℝ => (r : WithTop ℝ))
    simp only [Finsupp.weight_apply, Finsupp.sum, nsmul_eq_mul,
      Finset.sum_mul, neg_mul]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [heq]
  calc
    (∑ i ∈ d.support, d i • ((-w i * D : ℝ) : WithTop ℝ)) ≤
      ∑ i ∈ d.support, v (x i ^ d i) := by
        apply Finset.sum_le_sum
        intro i hi
        rw [v.map_pow]
        exact nsmul_le_nsmul_right (hx i) (d i)
    _ ≤ v (algebraMap C K c) + ∑ i ∈ d.support, v (x i ^ d i) :=
      le_add_of_nonneg_left (hc c)

theorem polynomial_order_lower (v : AddValuation K (WithTop ℝ))
    (x : σ → K) (w : σ → ℝ) (D N : ℝ) (hD : 0 ≤ D)
    (hx : ∀ i, ((-w i * D : ℝ) : WithTop ℝ) ≤ v (x i))
    (hc : ∀ c : C, (0 : WithTop ℝ) ≤ v (algebraMap C K c))
    (p : MvPolynomial σ C)
    (hp : ∀ d ∈ p.support, Finsupp.weight w d ≤ N) :
    ((-N * D : ℝ) : WithTop ℝ) ≤ v (MvPolynomial.aeval x p) := by
  classical
  rw [p.as_sum, map_sum]
  apply v.map_le_sum
  intro d hd
  have hnum : -N * D ≤ -Finsupp.weight w d * D :=
    mul_le_mul_of_nonneg_right (neg_le_neg (hp d hd)) hD
  exact (WithTop.coe_le_coe.mpr hnum).trans (monomial_order_lower v x w D hx hc d _)

end PiExponent.PolynomialPoleBound

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Polynomials_WeightedPolynomialPole
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.WeightedPolynomialPole
open WeightedCurveDegree PolynomialPoleBound

variable {K ι : Type*} [Field K] [Fintype ι]

theorem coordinate_order_lower (v : AddValuation K (WithTop ℤ))
    (x : ι → K) (w : ι → ℚ) (hw : ∀ i, 0 < w i) (i : ι) :
    ((-(w i : ℝ) * (coordinatePole v x w : ℝ) : ℝ) : WithTop ℝ) ≤
      realValuation v (x i) := by
  by_cases hx : x i = 0
  · simp [hx]
  · rw [realValuation_of_ne_zero v (x i) hx]
    apply WithTop.coe_le_coe.mpr
    have h := (div_le_iff₀ (hw i)).mp
      (div_le_weightedPole w (fun j => (coordinateOrder v (x j) : ℚ)) i)
    have hq : -(w i) * coordinatePole v x w ≤ (coordinateOrder v (x i) : ℚ) := by
      dsimp [coordinatePole]
      nlinarith
    exact_mod_cast hq

end PiExponent.WeightedPolynomialPole

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_CurveContactSum
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.PlaceValuationRing.constantsAlgebra _root_.OAI.PiExponent.PlaceValuationRing.discreteValuationRing _root_.OAI.PiExponent.PlaceValuationRing.scalarTower _root_.OAI.PiExponent.PlaceValuationRing.valuation_nontrivial _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace PiExponent.CurveContactSum

open WeightedPolynomialPole WeightedCurveDegree CurveValuationCenter PolynomialPoleBound

theorem contact_sum_le_of_principal_sum
    {P : Type*} (z : P →₀ ℤ) (pole : P →₀ ℚ)
    (hz : z.sum (fun _ n => n) = 0) (hpole_nonneg : ∀ p, 0 ≤ pole p)
    (S : Finset P) (μ : P → ℝ) (N B : ℝ) (hN : 0 ≤ N)
    (hlocal : ∀ p ∈ S, B * μ p ≤ (z p : ℝ))
    (hglobal : ∀ p, -N * (pole p : ℝ) ≤ (z p : ℝ)) :
    B * (∑ p ∈ S, μ p) ≤ N * pole.sum (fun _ n => (n : ℝ)) := by
  classical
  let T := S ∪ z.support ∪ pole.support
  have hST : S ⊆ T := by intro p hp; simp [T, hp]
  have hzT : z.support ⊆ T := by intro p hp; simp [T, hp]
  have hpT : pole.support ⊆ T := by intro p hp; simp [T, hp]
  have hzsum : (∑ p ∈ T, (z p : ℝ)) = 0 := by
    have hh := z.sum_of_support_subset hzT (fun _ n => n) (by simp)
    have hi : (∑ p ∈ T, z p) = 0 := hh.symm.trans hz
    exact_mod_cast hi
  have hpsum : (∑ p ∈ T, (pole p : ℝ)) = pole.sum (fun _ n => (n : ℝ)) :=
    (pole.sum_of_support_subset hpT (fun _ n => (n : ℝ)) (by simp)).symm
  calc
    B * (∑ p ∈ S, μ p) = ∑ p ∈ S, B * μ p := Finset.mul_sum _ _ _
    _ ≤ ∑ p ∈ S, ((z p : ℝ) + N * (pole p : ℝ)) := by
      apply Finset.sum_le_sum
      intro p hp
      exact (hlocal p hp).trans (le_add_of_nonneg_right
        (mul_nonneg hN (by exact_mod_cast hpole_nonneg p)))
    _ ≤ ∑ p ∈ T, ((z p : ℝ) + N * (pole p : ℝ)) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hST
      intro p hp hnot
      have hh := hglobal p
      linarith
    _ = N * pole.sum (fun _ n => (n : ℝ)) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, hzsum, zero_add, hpsum]

theorem coordinateOrderDivisor_degree_zero {E : Type*} [Field E] [Algebra ℂ E]
    (hfinite : ∀ f : E, Transcendental ℂ f → FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (f : E) : (coordinateOrderDivisor hfinite f).sum (fun _ n => n) = 0 := by
  classical
  by_cases ht : Transcendental ℂ f
  · let := hfinite f ht
    rw [coordinateOrderDivisor, dite_eq_left ht]
    exact CurveProductFormula.principalDivisor_degree_zero f ht
  · simp [coordinateOrderDivisor, ht]

theorem constants_real_nonneg {E : Type*} [Field E] [Algebra ℂ E]
    (p : NormalizedPlace ℂ E) (c : ℂ) :
    0 ≤ realValuation p.valuation (algebraMap ℂ E c) := by
  have h := (show Monotone (WithTop.map (fun z : ℤ => (z : ℝ))) from
    (Int.cast_mono (R := ℝ)).withTop_map) (p.constants_nonneg c)
  have hz : WithTop.map (fun z : ℤ => (z : ℝ)) (0 : WithTop ℤ) = (0 : WithTop ℝ) := by
    change (((0 : ℤ) : ℝ) : WithTop ℝ) = 0
    norm_num
  rw [hz] at h
  exact h

theorem polynomial_order_lower {E ι : Type*} [Field E] [Algebra ℂ E] [Fintype ι]
    (x : ι → E) (w : ι → ℚ) (hw : ∀ i, 0 < w i) (N : ℝ)
    (f : MvPolynomial ι ℂ)
    (hdegree : ∀ d ∈ f.support, Finsupp.weight (fun i => (w i : ℝ)) d ≤ N)
    (hne : MvPolynomial.aeval x f ≠ 0) (p : NormalizedPlace ℂ E) :
    -N * (coordinatePole p.valuation x w : ℝ) ≤
      (coordinateOrder p.valuation (MvPolynomial.aeval x f) : ℝ) := by
  have h := PolynomialPoleBound.polynomial_order_lower (realValuation p.valuation) x
    (fun i => (w i : ℝ)) (coordinatePole p.valuation x w : ℝ) N
    (by exact_mod_cast weightedPole_nonneg w (fun i => (coordinateOrder p.valuation (x i) : ℚ)))
    (coordinate_order_lower p.valuation x w hw) (constants_real_nonneg p) f hdegree
  rw [realValuation_of_ne_zero _ _ hne] at h
  exact WithTop.coe_le_coe.mp h

theorem polynomial_contact_sum_le {E ι : Type*} [Field E] [Algebra ℂ E] [Fintype ι]
    (hfinite : ∀ f : E, Transcendental ℂ f → FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (x : ι → E) (w : ι → ℚ) (hw : ∀ i, 0 < w i) (N B : ℝ) (hN : 0 ≤ N)
    (f : MvPolynomial ι ℂ)
    (hdegree : ∀ d ∈ f.support, Finsupp.weight (fun i => (w i : ℝ)) d ≤ N)
    (hne : MvPolynomial.aeval x f ≠ 0)
    (S : Finset (NormalizedPlace ℂ E)) (μ : NormalizedPlace ℂ E → ℝ)
    (hlocal : ∀ p ∈ S, B * μ p ≤
      (coordinateOrder p.valuation (MvPolynomial.aeval x f) : ℝ)) :
    B * (∑ p ∈ S, μ p) ≤ N * weightedDegree hfinite x w := by
  refine contact_sum_le_of_principal_sum
    (coordinateOrderDivisor hfinite (MvPolynomial.aeval x f)) (weightedPoleDivisor hfinite x w)
    (coordinateOrderDivisor_degree_zero hfinite _) ?_ S μ N B hN ?_ ?_
  · intro p
    exact weightedPole_nonneg w (fun i => (coordinateOrder p.valuation (x i) : ℚ))
  · intro p hp
    simpa only [coordinateOrderDivisor_apply] using hlocal p hp
  · intro p
    simpa only [weightedPoleDivisor_apply, coordinateOrderDivisor_apply] using
      polynomial_order_lower x w hw N f hdegree hne p

theorem polynomial_eq_zero_of_excess_contact
    {E ι : Type*} [Field E] [Algebra ℂ E] [Fintype ι]
    (hfinite : ∀ f : E, Transcendental ℂ f → FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (x : ι → E) (w : ι → ℚ) (hw : ∀ i, 0 < w i) (N B : ℝ) (hN : 0 ≤ N)
    (f : MvPolynomial ι ℂ)
    (hdegree : ∀ d ∈ f.support, Finsupp.weight (fun i => (w i : ℝ)) d ≤ N)
    (S : Finset (NormalizedPlace ℂ E)) (μ : NormalizedPlace ℂ E → ℝ)
    (hlocal : MvPolynomial.aeval x f ≠ 0 → ∀ p ∈ S, B * μ p ≤
      (coordinateOrder p.valuation (MvPolynomial.aeval x f) : ℝ))
    (hexcess : N * weightedDegree hfinite x w < B * (∑ p ∈ S, μ p)) :
    MvPolynomial.aeval x f = 0 := by
  by_contra hne
  exact (not_le_of_gt hexcess)
    (polynomial_contact_sum_le hfinite x w hw N B hN f hdegree hne S μ (hlocal hne))

end PiExponent.CurveContactSum

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_PlaceCenteredBranch
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.PlaceCenteredBranch

open CurveValuationCenter CurveCenters PlaceValuationRing WeightedPolynomialPole

variable {E ι : Type*} [Field E] [Algebra ℂ E]

theorem coordinateOrder_aeval_eq_length
    (p : NormalizedPlace ℂ E) (z : ι → E) (c : ι → ℂ) (hc : Centered z c p)
    (f : MvPolynomial ι ℂ) (hne : MvPolynomial.aeval z f ≠ 0) :
    coordinateOrder p.valuation (MvPolynomial.aeval z f) =
      ((Module.length (ring p) ((ring p) ⧸
        Ideal.span {MvPolynomial.aeval (lift p z c hc) f})).toNat : ℤ) := by
  have hn : MvPolynomial.aeval (lift p z c hc) f ≠ 0 := by
    intro h
    apply hne
    rw [← lift_aeval p z c hc f, h, map_zero]
  rw [coordinateOrder, dite_eq_right hne, valuation_eq_fractionAddValuation p]
  have hu : Units.mk0 (MvPolynomial.aeval z f) hne =
      Units.mk0 (algebraMap (ring p) E (MvPolynomial.aeval (lift p z c hc) f))
        ((map_ne_zero_iff _ (IsFractionRing.injective (ring p) E)).mpr hn) := by
    apply Units.ext
    exact (lift_aeval p z c hc f).symm
  rw [hu]
  exact CurveLocalOrder.integerOrder_field_image_eq_length hn

variable (p : NormalizedPlace ℂ E)
    [Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p))]

theorem logContact_pos {m : ℕ} (z : Fin (m+1) → E) (c : Fin m → ℂ)
    (hc : Centered z (Fin.cases 1 c) p)
    (hnc : ∃ i : Fin (m+1), z i ≠ algebraMap ℂ E ((Fin.cases (1 : ℂ) c : Fin (m+1) → ℂ) i))
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 < v i) : 0 < logContact p z c hc hnc v := by
  exact DVRBranchJet.contact_pos v hv c _ _
    (lift_residue p z (Fin.cases 1 c) hc 0)
    (fun i => lift_residue p z (Fin.cases 1 c) hc i.succ) _

theorem logWord_field_order_lower {m : ℕ} (z : Fin (m+1) → E) (c : Fin m → ℂ)
    (hc : Centered z (Fin.cases 1 c) p)
    (hnc : ∃ i : Fin (m+1), z i ≠ algebraMap ℂ E ((Fin.cases (1 : ℂ) c : Fin (m+1) → ℂ) i))
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 < v i) (H : ℚ)
    (f : PiExponentApprox.FramePolynomial m)
    (hf : FormalLogJet.formalJet c f ∈ JetGeometry.rationalWeightedIdeal v (fun i => (hv i).le) H)
    (word : List (Fin (m+1)))
    (hne : MvPolynomial.aeval z (PiExponentApprox.polynomialFrameWord m word f) ≠ 0) :
    logContact p z c hc hnc v * (H - (word.map v).sum) ≤
      (coordinateOrder p.valuation
        (MvPolynomial.aeval z (PiExponentApprox.polynomialFrameWord m word f)) : ℚ) := by
  let x := lift p z (Fin.cases 1 c) hc
  have he : (fun i => Fin.cases (x 0) (fun j => x j.succ) i) = x := by
    funext i
    cases i using Fin.cases <;> rfl
  have hn : MvPolynomial.aeval x (PiExponentApprox.polynomialFrameWord m word f) ≠ 0 := by
    intro hz
    apply hne
    rw [← lift_aeval p z (Fin.cases 1 c) hc, hz, map_zero]
  have hb := DVRBranchJet.frameWord_colength_lower v hv H c (x 0) (fun i => x i.succ)
    (lift_residue p z (Fin.cases 1 c) hc 0)
    (fun i => lift_residue p z (Fin.cases 1 c) hc i.succ)
    (logLift_nonconstant p z c hc hnc) f hf word (he.symm ▸ hn)
  have heval := congrArg (fun u : Fin (m+1) → ring p =>
    MvPolynomial.aeval u (PiExponentApprox.polynomialFrameWord m word f)) he
  rw [heval] at hb
  rw [coordinateOrder_aeval_eq_length p z (Fin.cases 1 c) hc _ hne]
  simpa only [Int.cast_natCast, logContact, x] using hb

end PiExponent.PlaceCenteredBranch

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_CurveContactFamily
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.CurveContactFamily

open CurveValuationCenter CurveCenters PlaceValuationRing

variable {E : Type*} [Field E] {m K : ℕ}

variable [Algebra ℂ E]

theorem contact_pos
    (hres : ∀ p : NormalizedPlace ℂ E,
      Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p)))
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (z : Fin (m+1) → E) (c : Fin K → Fin m → ℂ)
    (hz : ∃ i, Transcendental ℂ (z i)) (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 < v i)
    (p : NormalizedPlace ℂ E) (hp : p ∈ places hfinite z c hz) :
    0 < contact hres hfinite z c hz v p := by
  let := hres p
  simpa only [contact, dite_eq_left hp] using
    PlaceCenteredBranch.logContact_pos p z (c (center hfinite z c hz p hp))
      (centered hfinite z c hz p hp) (nonconstant z _ hz) v hv

theorem contact_nonneg
    (hres : ∀ p : NormalizedPlace ℂ E,
      Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p)))
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (z : Fin (m+1) → E) (c : Fin K → Fin m → ℂ)
    (hz : ∃ i, Transcendental ℂ (z i)) (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 < v i)
    (p : NormalizedPlace ℂ E) : 0 ≤ contact hres hfinite z c hz v p := by
  by_cases hp : p ∈ places hfinite z c hz
  · exact (contact_pos hres hfinite z c hz v hv p hp).le
  · simp only [contact, dite_eq_right hp, le_refl]

theorem logWord_order_lower
    (hres : ∀ p : NormalizedPlace ℂ E,
      Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p)))
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (z : Fin (m+1) → E) (c : Fin K → Fin m → ℂ)
    (hz : ∃ i, Transcendental ℂ (z i)) (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 < v i)
    (H : ℚ) (F : PiExponentApprox.FramePolynomial m)
    (hF : ∀ j, FormalLogJet.formalJet (c j) F ∈
      JetGeometry.rationalWeightedIdeal v (fun i => (hv i).le) H)
    (word : List (Fin (m+1)))
    (hne : MvPolynomial.aeval z (PiExponentApprox.polynomialFrameWord m word F) ≠ 0)
    (p : NormalizedPlace ℂ E) (hp : p ∈ places hfinite z c hz) :
    contact hres hfinite z c hz v p * (H - (word.map v).sum) ≤
      (WeightedPolynomialPole.coordinateOrder p.valuation
        (MvPolynomial.aeval z (PiExponentApprox.polynomialFrameWord m word F)) : ℚ) := by
  let := hres p
  have h := PlaceCenteredBranch.logWord_field_order_lower p z
    (c (center hfinite z c hz p hp)) (centered hfinite z c hz p hp)
    (nonconstant z _ hz) v hv H F (hF _) word hne
  simpa only [contact, dite_eq_left hp] using h

end PiExponent.CurveContactFamily
end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_CurveDerivativeVanishing
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace PiExponent.CurveDerivativeVanishing

open PiExponentApprox CurveValuationCenter PlaceValuationRing CurveContactFamily

theorem cast_word_cost {ι : Type*} (v : ι → ℚ) (word : List ι) :
    (((word.map v).sum : ℚ) : ℝ) = (word.map (fun i => (v i : ℝ))).sum := by
  induction word with
  | nil => simp
  | cons i word ih => simp [ih]

theorem logarithmic_words_vanish_q68_oai
    {E : Type*} [Field E] [Algebra ℂ E] {m K : ℕ}
    (hres : ∀ p : NormalizedPlace ℂ E,
      Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p)))
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (z : Fin (m+1) → E) (c : Fin K → Fin m → ℂ)
    (hz : ∃ i, Transcendental ℂ (z i))
    (w v : Fin (m+1) → ℚ) (hw : ∀ i, 0 < w i) (hv : ∀ i, 0 < v i)
    (sigma : ℚ) (hsigma : 0 < sigma) (N : ℕ) (hN : 0 < N)
    (F : FramePolynomial m)
    (hF : HasWeightedDegreeLE (fun i => (w i : ℝ)) N F)
    (hjet : ∀ j, FormalLogJet.formalJet (c j) F ∈
      JetGeometry.rationalWeightedIdeal v (fun i => (hv i).le) ((1+3*sigma)*N))
    (hexcess : CurveContactSum.weightedDegree hfinite z w <
      (1+(sigma : ℝ)) * ∑ p ∈ places hfinite z c hz, (contact hres hfinite z c hz v p : ℝ)) :
    ∀ word : List (Fin (m+1)),
      frameWordCost (fun i => (v i : ℝ)) word ≤ (sigma : ℝ)*N →
        MvPolynomial.aeval z (polynomialFrameWord m word F) = 0 := by
  intro word hword
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hsigR : (0 : ℝ) < sigma := by exact_mod_cast hsigma
  have hcost : (word.map v).sum ≤ sigma*N := by
    change (word.map (fun i => (v i : ℝ))).sum ≤ (sigma : ℝ)*N at hword
    rw [← cast_word_cost v word] at hword
    exact_mod_cast hword
  have hdegree : ∀ d ∈ (polynomialFrameWord m word F).support,
      Finsupp.weight (fun i => (w i : ℝ)) d ≤ (N : ℝ) := by
    apply (FrameEquationFamily.hasWeightedDegreeLE_iff_supportBound _ _ _).mp
    exact hF.polynomialFrameWord (fun i => by exact_mod_cast (hw i).le) word
  have hsum : 0 ≤ ∑ p ∈ places hfinite z c hz, (contact hres hfinite z c hz v p : ℝ) := by
    apply Finset.sum_nonneg
    intro p hp
    exact_mod_cast contact_nonneg hres hfinite z c hz v hv p
  apply CurveContactSum.polynomial_eq_zero_of_excess_contact hfinite z w hw
    (N : ℝ) ((1+2*(sigma : ℝ))*N) hNR.le (polynomialFrameWord m word F) hdegree
    (places hfinite z c hz) (fun p => (contact hres hfinite z c hz v p : ℝ))
  · intro hne p hp
    have hret : (1+2*sigma)*(N : ℚ) ≤ (1+3*sigma)*N - (word.map v).sum := by
      nlinarith
    have hlocal := logWord_order_lower hres hfinite z c hz v hv ((1+3*sigma)*N)
      F hjet word hne p hp
    have hq := (mul_le_mul_of_nonneg_left hret
      (contact_nonneg hres hfinite z c hz v hv p)).trans hlocal
    have hr : (contact hres hfinite z c hz v p : ℝ) * ((1+2*(sigma : ℝ))*N) ≤
        (WeightedPolynomialPole.coordinateOrder p.valuation
          (MvPolynomial.aeval z (polynomialFrameWord m word F)) : ℝ) := by
      exact_mod_cast hq
    simpa only [mul_comm] using hr
  · calc
      (N : ℝ) * CurveContactSum.weightedDegree hfinite z w <
          N * ((1+(sigma : ℝ)) * ∑ p ∈ places hfinite z c hz,
            (contact hres hfinite z c hz v p : ℝ)) := mul_lt_mul_of_pos_left hexcess hNR
      _ = (1+(sigma : ℝ)) * (N * ∑ p ∈ places hfinite z c hz,
          (contact hres hfinite z c hz v p : ℝ)) := by ring
      _ ≤ (1+2*(sigma : ℝ)) * (N * ∑ p ∈ places hfinite z c hz,
          (contact hres hfinite z c hz v p : ℝ)) :=
        mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hNR.le hsum)
      _ = _ := by ring

end PiExponent.CurveDerivativeVanishing
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.PiExponent.CurveDerivativeVanishing.logarithmic_words_vanish_q68_oai.{u_1} := @OAI.PiExponent.CurveDerivativeVanishing.logarithmic_words_vanish_q68_oai.{u_1}
