-- Prove2me | solution 1 for OAI.PiExponent.CurveInequality.excess_implies_zeroth_eq_one_q68
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T09:18:35.858152+00:00
-- url     : https://prove2.me/submissions/eca550ef-cb60-45f4-b956-457897c15dc9

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ068A026
import Definitions.Def_OAIQ068A029
import Theorems.Thm_OAI_PiExponent_CurveComponentRigidity_coordinate_constant_of_persistent_comparison_q68
import Theorems.Thm_OAI_PiExponent_CurveDerivativeVanishing_logarithmic_words_vanish_q68
import Theorems.Thm_OAI_PiExponent_TransverseSliceComparison_comparison_of_normal_basis_q68

section
-- module Solutions.OAIQ068_PI.PiExponent_Polynomials_PolynomialFrameDegree
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
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
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
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
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_FrameEquationFamily
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.FrameEquationFamily

open scoped BigOperators
open PiExponentApprox

theorem span_equations {m : ℕ} (cost : Fin (m + 1) → ℝ) (bound : ℝ)
    (F : FramePolynomial m) :
    Ideal.span (Set.range (equations cost bound F)) =
      frameDerivativeIdeal cost bound F := by
  unfold frameDerivativeIdeal
  congr 1
  ext g
  constructor
  · rintro ⟨word, rfl⟩
    exact ⟨word.1, word.2, rfl⟩
  · rintro ⟨word, hword, rfl⟩
    exact ⟨⟨word, hword⟩, rfl⟩

theorem monomialWeight_eq_weight {m : ℕ} (W : Fin (m + 1) → ℝ)
    (d : Fin (m + 1) →₀ ℕ) :
    monomialWeight W d = Finsupp.weight W d := by
  simp only [monomialWeight, Finsupp.weight_eq_sum, nsmul_eq_mul]

theorem hasWeightedDegreeLE_iff_supportBound {m : ℕ} (W : Fin (m + 1) → ℝ)
    (N : ℝ) (F : FramePolynomial m) :
    HasWeightedDegreeLE W N F ↔ WeightedSliceDegree.SupportBound W N F := by
  simp only [HasWeightedDegreeLE, WeightedSliceDegree.SupportBound, monomialWeight_eq_weight]

theorem equation_hasWeightedDegreeLE {m : ℕ} (cost W : Fin (m + 1) → ℝ)
    (bound N : ℝ) (F : FramePolynomial m)
    (hF : HasWeightedDegreeLE W N F) (hW : ∀ i, 0 ≤ W i)
    (word : BoundedWords cost bound) :
    HasWeightedDegreeLE W N (equations cost bound F word) :=
  hF.polynomialFrameWord hW word.1

theorem equation_supportBound {m : ℕ} (cost W : Fin (m + 1) → ℝ)
    (bound N : ℝ) (F : FramePolynomial m)
    (hF : HasWeightedDegreeLE W N F) (hW : ∀ i, 0 ≤ W i)
    (word : BoundedWords cost bound) :
    WeightedSliceDegree.SupportBound W N (equations cost bound F word) :=
  (hasWeightedDegreeLE_iff_supportBound W N _).mp
    (equation_hasWeightedDegreeLE cost W bound N F hF hW word)

end PiExponent.FrameEquationFamily

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Jets_NormalBasisRigidity
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponent.NormalBasisRigidity

open Set Submodule Module

variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]

lemma IsNormalBasis.card_eq {v : ι → V} {A : Finset ι}
    (hA : IsNormalBasis (K := K) v A) : A.card = Module.finrank K V := by
  classical
  have hli : LinearIndependent K (fun i : A => v i) := hA.1
  let b : Basis A K V := Basis.mk hli (by
    have hr : Set.range (fun i : A => v i) = v '' (A : Set ι) := by
      ext x
      simp
    rw [hr, hA.2])
  exact (Module.finrank_eq_card_finset_basis b).symm

end PiExponent.NormalBasisRigidity

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_RectangularVolume
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

namespace PiExponent

theorem two_le_rectangularCutoff {k : ℕ} (hk : 0 < k) (κ : Fin k → ℝ)
    (hκ : ∀ i, 0 < κ i) {T : ℝ} (i : Fin k)
    (hT : (k : ℝ) * κ i < T) :
    2 ≤ rectangularCutoff κ T i := by
  have hd : 0 < (k : ℝ) * κ i :=
    mul_pos (by exact_mod_cast hk) (hκ i)
  have h : (1 : ℝ) < T / ((k : ℝ) * κ i) :=
    (lt_div_iff₀ hd).mpr (by simpa using hT)
  exact Nat.lt_ceil.mpr (by simpa using h)

end PiExponent

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Jets_NormalBasisProducts
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.NormalBasisProducts

open scoped BigOperators
open NormalBasisRigidity

variable {ι K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem enumeration_linearIndependent {v : ι → V} (A B : Finset ι)
    (hcard : A.card = B.card) (hB : IsNormalBasis (K := K) v B) :
    LinearIndependent K (fun i => v (enumeration A B hcard i)) := by
  have hli : LinearIndependent K (fun i : B => v i) := hB.1
  exact hli.comp (fun i => B.equivFin.symm (Fin.cast hcard i))
    (B.equivFin.symm.injective.comp (Fin.cast_injective hcard))

theorem prod_equivFin {M : Type*} [CommMonoid M] (A : Finset ι) (f : ι → M) :
    (∏ i : Fin A.card, f (A.equivFin.symm i)) = ∏ i ∈ A, f i := by
  calc
    _ = ∏ i : A, f i := Fintype.prod_equiv A.equivFin.symm _ _ (fun _ => rfl)
    _ = _ := Finset.prod_coe_sort A f

theorem prod_enumeration {M : Type*} [CommMonoid M]
    (A B : Finset ι) (hcard : A.card = B.card) (f : ι → M) :
    (∏ i : Fin A.card, f (enumeration A B hcard i)) = ∏ i ∈ B, f i := by
  calc
    _ = ∏ i : Fin B.card, f (B.equivFin.symm i) :=
      Fintype.prod_equiv (finCongr hcard) _ _ (fun _ => rfl)
    _ = _ := prod_equivFin B f

theorem eventually_uniform_cutoff (n : ℕ)
    (cost : Fin n → ℝ) (hcost : ∀ i, 0 < cost i)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℝ in Filter.atTop, ∀ k : ℕ, 0 < k → k ≤ n →
      ∀ B : Fin k → Fin n, ∀ i,
        2 ≤ rectangularCutoff (fun j => cost (B j)) (epsilon * N) i := by
  have ht : Filter.Tendsto (fun N : ℝ => epsilon * N) Filter.atTop Filter.atTop :=
    Filter.tendsto_id.const_mul_atTop hepsilon
  have hb : ∀ᶠ N : ℝ in Filter.atTop, ∀ j : Fin n,
      (n : ℝ) * cost j < epsilon * N :=
    Filter.eventually_all.mpr (fun j =>
      ht.eventually (Filter.eventually_gt_atTop ((n : ℝ) * cost j)))
  filter_upwards [hb] with N hN
  intro k hk hkn B i
  have hdim : (k : ℝ) ≤ n := by exact_mod_cast hkn
  apply two_le_rectangularCutoff hk (fun j => cost (B j)) (fun j => hcost _) i
  exact (mul_le_mul_of_nonneg_right hdim (hcost _).le).trans_lt (hN (B i))

theorem rectangular_factor_le_constant (m k : ℕ) (sigma : ℝ)
    (hsigma : 0 < sigma) (hkm : k ≤ m + 2) :
    (k : ℝ) ^ k * (((m : ℝ) + 2) / sigma) ^ k ≤
      2 * ((m : ℝ) + 2) ^ (m + 2) *
        (1 + ((m : ℝ) + 2) / sigma) ^ (m + 2) := by
  have hbase : 0 ≤ ((m : ℝ) + 2) / sigma := by positivity
  have hdim : (k : ℝ) ≤ (m : ℝ) + 2 := by exact_mod_cast hkm
  have hp : (k : ℝ) ^ k ≤ ((m : ℝ) + 2) ^ (m + 2) := by
    calc
      _ ≤ ((m : ℝ) + 2) ^ k := pow_le_pow_left₀ (Nat.cast_nonneg k) hdim k
      _ ≤ _ := pow_le_pow_right₀ (by have := (Nat.cast_nonneg m : (0 : ℝ) ≤ m); linarith) hkm
  have hfactor : (k : ℝ) ^ k ≤ 2 * ((m : ℝ) + 2) ^ (m + 2) := hp.trans (by
    have h : 0 ≤ ((m : ℝ) + 2) ^ (m + 2) := by positivity
    linarith)
  have hpow : (((m : ℝ) + 2) / sigma) ^ k ≤
      (1 + ((m : ℝ) + 2) / sigma) ^ (m + 2) := by
    calc
      _ ≤ (1 + ((m : ℝ) + 2) / sigma) ^ k :=
        pow_le_pow_left₀ hbase (le_add_of_nonneg_left zero_le_one) k
      _ ≤ _ := pow_le_pow_right₀ (le_add_of_nonneg_right hbase) hkm
  exact mul_le_mul hfactor hpow (pow_nonneg hbase _) (by positivity)

theorem rectangular_comparison_le_constant {m k : ℕ}
    (hkm : k ≤ m + 2) (kappa : Fin k → ℝ) (sigma : ℝ)
    (hsigma : 0 < sigma) (hkappa : ∀ i, 0 ≤ kappa i) :
    (k : ℝ) ^ k * (∏ i, kappa i) / (sigma / ((m : ℝ) + 2)) ^ k ≤
      (2 * ((m : ℝ) + 2) ^ (m + 2) *
        (1 + ((m : ℝ) + 2) / sigma) ^ (m + 2)) * ∏ i, kappa i := by
  have h := rectangular_factor_le_constant m k sigma hsigma hkm
  have hp : 0 ≤ ∏ i, kappa i := Finset.prod_nonneg (fun i _ => hkappa i)
  have hh := mul_le_mul_of_nonneg_right h hp
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  simp only [div_eq_mul_inv, mul_pow, mul_inv_rev, inv_pow, inv_inv]
  ring

end PiExponent.NormalBasisProducts
end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_PersistentWeightComparison
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.PersistentWeightComparison

open scoped BigOperators
open PiExponentApprox NormalBasisRigidity NormalBasisProducts

theorem eventually_uniformRectangles (n : ℕ) (cost : Fin n → ℝ)
    (hcost : ∀ i, 0 < cost i) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℝ in Filter.atTop, UniformRectangles n cost epsilon N :=
  eventually_uniform_cutoff n cost hcost epsilon hepsilon

theorem logarithmic_normal_comparison {m : ℕ}
    (rho : Fin (m + 1) → ℚ) (hrho : ∀ i, 0 < rho i)
    (cost : Fin (m + 1) → ℝ) (hcost : ∀ i, 0 < cost i)
    (sigma N : ℝ) (hsigma : 0 < sigma) (hN : 0 < N)
    (hrect : UniformRectangles (m + 1) cost (sigma / ((m : ℝ) + 2)) N)
    (F : FramePolynomial m) (hF : HasWeightedDegreeLE (fun i => (rho i : ℝ)) N F)
    (bound : ℝ) (Q : Ideal (FramePolynomial m)) [Q.IsPrime]
    (hY : MvPolynomial.X (0 : Fin (m + 1)) ∉ Q)
    (hQ : Q ∈ (frameDerivativeIdeal cost bound F).minimalPrimes)
    (hvanish : ∀ p ∈ frameDerivativeIdeal cost bound F,
      ∀ word : List (Fin (m + 1)),
        frameWordCost cost word ≤ (sigma / ((m : ℝ) + 2)) * N →
          polynomialFrameWord m word p ∈ Q) :
    CurveComponentRigidity.NormalProductComparison Q hY
      (fun i => (rho i : ℝ)) cost (comparisonConstant m sigma) := by
  intro A B hA hB
  have hcard : A.card = B.card := hA.card_eq.trans hB.card_eq.symm
  by_cases hk0 : A.card = 0
  · have hA0 : A = ∅ := Finset.card_eq_zero.mp hk0
    have hB0 : B = ∅ := Finset.card_eq_zero.mp (hcard.symm.trans hk0)
    have hc := rectangular_factor_le_constant m 0 sigma hsigma (by omega)
    simpa [hA0, hB0, comparisonConstant] using hc
  have hk : 0 < A.card := Nat.pos_of_ne_zero hk0
  have hka : A.card ≤ m + 1 := by simpa using Finset.card_le_univ A
  have hepsilon : 0 < sigma / ((m : ℝ) + 2) := by positivity
  have hrhoR (i : Fin (m + 1)) : (0 : ℝ) < rho i := by exact_mod_cast hrho i
  have hdegree : ∀ j, ∀ d ∈ (FrameEquationFamily.equations cost bound F j).support,
      (∑ i ∈ d.support, (d i : ℝ) * (rho i : ℝ)) ≤ N := by
    intro j
    have h := FrameEquationFamily.equation_supportBound cost (fun i => (rho i : ℝ))
      bound N F hF (fun i => (hrhoR i).le) j
    simpa only [WeightedSliceDegree.SupportBound, Finsupp.weight_apply, Finsupp.sum,
      nsmul_eq_mul] using h
  have hcomp := TransverseSliceComparison.comparison_of_normal_basis_q68 Q
    (CurveComponentRigidity.residueY_ne_zero Q hY) A hk hA
    (enumeration A B hcard) (enumeration_linearIndependent A B hcard hB)
    (FrameEquationFamily.equations cost bound F)
    (by simpa only [FrameEquationFamily.span_equations] using hQ)
    rho hrho cost hcost (sigma / ((m : ℝ) + 2)) N hepsilon hN hdegree
    (hrect A.card hk hka (enumeration A B hcard))
    (by simpa only [FrameEquationFamily.span_equations] using hvanish)
  exact hcomp.trans (by
    have hc := rectangular_comparison_le_constant (m := m) (k := A.card)
      (by omega) (fun i => cost (enumeration A B hcard i)) sigma hsigma
      (fun i => (hcost _).le)
    simpa only [prod_enumeration A B hcard cost, comparisonConstant] using hc)

theorem logarithmic_persistent_comparison {m : ℕ}
    (rho : Fin (m + 1) → ℚ) (hrho : ∀ i, 0 < rho i)
    (cost : Fin (m + 1) → ℝ) (hcost : ∀ i, 0 < cost i)
    (sigma N : ℝ) (hsigma : 0 < sigma) (hN : 0 < N)
    (hrect : UniformRectangles (m + 1) cost (sigma / ((m : ℝ) + 2)) N)
    (F : FramePolynomial m) (hF : HasWeightedDegreeLE (fun i => (rho i : ℝ)) N F)
    (P : Ideal (FramePolynomial m)) (hY : MvPolynomial.X (0 : Fin (m + 1)) ∉ P) :
    CurveComponentRigidity.PersistentNormalComparison (fun i => (rho i : ℝ)) cost
      (comparisonConstant m sigma) ((sigma / ((m : ℝ) + 2)) * N) F P hY := by
  intro r hr Q hQ hQP hQr hQnext hQlo hQhi hvanish
  let := hQ
  exact logarithmic_normal_comparison rho hrho cost hcost sigma N hsigma hN hrect
    F hF _ Q (fun h => hY (hQP h)) hQr hvanish

end PiExponent.PersistentWeightComparison
end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_CurveContactSum
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.PlaceValuationRing.constantsAlgebra _root_.OAI.PiExponent.PlaceValuationRing.discreteValuationRing _root_.OAI.PiExponent.PlaceValuationRing.valuation_nontrivial _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace PiExponent.CurveContactSum

open WeightedPolynomialPole WeightedCurveDegree CurveValuationCenter PolynomialPoleBound

theorem weightedDegree_nonneg {E ι : Type*} [Field E] [Algebra ℂ E] [Fintype ι]
    (hfinite : ∀ f : E, Transcendental ℂ f → FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (x : ι → E) (w : ι → ℚ) : 0 ≤ weightedDegree hfinite x w := by
  apply Finset.sum_nonneg
  intro p hp
  change (0 : ℝ) ≤ (coordinatePole p.valuation x w : ℚ)
  exact_mod_cast weightedPole_nonneg w (fun i => (coordinateOrder p.valuation (x i) : ℚ))

end PiExponent.CurveContactSum

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_CurveCenters
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.PlaceValuationRing.constantsAlgebra _root_.OAI.PiExponent.PlaceValuationRing.discreteValuationRing _root_.OAI.PiExponent.PlaceValuationRing.valuation_nontrivial _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.CurveCenters

open CurveValuationCenter

variable {E ι J : Type*} [Field E] [Algebra ℂ E]

theorem Centered.constant_coordinate {x : ι → E} {a : ι → ℂ} {p : NormalizedPlace ℂ E}
    (ha : Centered x a p) (i : ι) (c : ℂ) (hc : x i = algebraMap ℂ E c) : c = a i := by
  by_contra hne
  have h := ha i
  rw [hc, ← map_sub, CurveProductFormula.valuation_constant_eq_zero p _ (sub_ne_zero.mpr hne)] at h
  exact lt_irrefl _ h

end PiExponent.CurveCenters
end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_CurveFieldRigidity
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.PlaceValuationRing.constantsAlgebra _root_.OAI.PiExponent.PlaceValuationRing.discreteValuationRing _root_.OAI.PiExponent.PlaceValuationRing.valuation_nontrivial _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.CurveFieldRigidity

open scoped BigOperators
open PiExponentApprox PersistentWeightComparison CurveCenters CurveValuationCenter

variable {E : Type*} [Field E] [Algebra ℂ E]

theorem logarithmic_coordinate_eq_one {m : ℕ}
    (x : Fin (m+1) → E) (a : Fin (m+1) → ℂ) (ha : a 0 = 1)
    (p : NormalizedPlace ℂ E) (hp : Centered x a p)
    (hheight : (coordinateKernel x).height ≤ m)
    (rho : Fin (m+1) → ℚ) (hrho : ∀ i, 0 < rho i)
    (cost : Fin (m+1) → ℝ) (hcost : ∀ i, 0 < cost i)
    (sigma N : ℝ) (hsigma : 0 < sigma) (hN : 0 < N)
    (hrect : UniformRectangles (m+1) cost (sigma / ((m : ℝ)+2)) N)
    (F : FramePolynomial m) (hF0 : F ≠ 0)
    (hF : HasWeightedDegreeLE (fun i => (rho i : ℝ)) N F)
    (hvanish : ∀ word : List (Fin (m+1)), frameWordCost cost word ≤ sigma*N →
      MvPolynomial.aeval x (polynomialFrameWord m word F) = 0)
    (hseparated : ∀ A B : Finset (Fin (m+1)), A.card = B.card →
      ∀ i, i ≠ 0 → i ∈ A → i ∉ B →
      (∀ j, i < j → (j ∈ A ↔ j ∈ B)) →
      comparisonConstant m sigma * (∏ j ∈ B, cost j) < ∏ j ∈ A, (rho j : ℝ)) :
    x 0 = 1 := by
  have hx0 : x 0 ≠ 0 := by
    intro hz
    have hc := hp.constant_coordinate 0 0 (by simpa using hz)
    rw [ha] at hc
    exact zero_ne_one hc
  have hY : MvPolynomial.X (0 : Fin (m+1)) ∉ coordinateKernel x := by
    simpa only [mem_coordinateKernel, MvPolynomial.aeval_X] using hx0
  have hepsilon : 0 < sigma / ((m : ℝ)+2) := by positivity
  have hbound : ((m : ℝ)+2) * ((sigma / ((m : ℝ)+2))*N) = sigma*N := by
    have hm : (m : ℝ)+2 ≠ 0 := by positivity
    field_simp
  obtain ⟨c, hc⟩ := CurveComponentRigidity.coordinate_constant_of_persistent_comparison_q68
    (fun i => (rho i : ℝ)) cost (comparisonConstant m sigma)
    ((sigma / ((m : ℝ)+2))*N) (fun i => (hcost i).le) (by positivity)
    F hF0 (coordinateKernel x) inferInstance hheight hY
    (fun word hword => hvanish word (by simpa only [hbound] using hword))
    (logarithmic_persistent_comparison rho hrho cost hcost sigma N hsigma hN hrect
      F hF (coordinateKernel x) hY) hseparated
  have hxc : x 0 = algebraMap ℂ E c := by
    simpa only [mem_coordinateKernel, map_sub, MvPolynomial.aeval_X,
      MvPolynomial.aeval_C, sub_eq_zero] using hc
  have hc1 := hp.constant_coordinate 0 c hxc
  rw [ha] at hc1
  simpa only [hc1, map_one] using hxc

end PiExponent.CurveFieldRigidity
end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Polynomials_SimplexFloor
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter Topology

namespace PiExponent

theorem tendsto_natFloor_affine_atTop {a : ℝ} (ha : 0 < a) (b : ℝ) :
    Tendsto (fun x : ℝ => ⌊a * x + b⌋₊) atTop atTop :=
  tendsto_nat_floor_atTop.comp
    (tendsto_atTop_add_const_right atTop b (Tendsto.const_mul_atTop ha tendsto_id))

theorem tendsto_natFloor_affine_div {a : ℝ} (ha : 0 < a) (b : ℝ) :
    Tendsto (fun x : ℝ => (⌊a * x + b⌋₊ : ℝ) / x) atTop (𝓝 a) := by
  have hy : Tendsto (fun x : ℝ => a * x + b) atTop atTop :=
    tendsto_atTop_add_const_right atTop b (Tendsto.const_mul_atTop ha tendsto_id)
  have hratio : Tendsto (fun x : ℝ => (a * x + b) / x) atTop (𝓝 a) := by
    have h : Tendsto (fun x : ℝ => a + b * x⁻¹) atTop (𝓝 (a + b * 0)) :=
      tendsto_const_nhds.add (tendsto_const_nhds.mul
      (tendsto_inv_atTop_zero : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0)))
    simp only [mul_zero, add_zero] at h
    apply h.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    field_simp
  have h := (tendsto_nat_floor_div_atTop.comp hy).mul hratio
  simp only [one_mul] at h
  apply h.congr'
  filter_upwards [hy.eventually (eventually_gt_atTop (0 : ℝ))] with x hx
  change (⌊a * x + b⌋₊ : ℝ) / (a * x + b) * ((a * x + b) / x) = _
  field_simp

theorem tendsto_normalized_natFloor_affine {f : ℕ → ℝ} {d : ℕ} {L a : ℝ}
    (hf : Tendsto (fun n : ℕ => f n / (n : ℝ) ^ d) atTop (𝓝 L))
    (ha : 0 < a) (b : ℝ) :
    Tendsto (fun x : ℝ => f ⌊a * x + b⌋₊ / x ^ d) atTop (𝓝 (L * a ^ d)) := by
  have hfloor := tendsto_natFloor_affine_atTop ha b
  have h := (hf.comp hfloor).mul ((tendsto_natFloor_affine_div ha b).pow d)
  apply h.congr'
  filter_upwards [hfloor.eventually (eventually_ge_atTop 1)] with x hx
  have hn : (⌊a * x + b⌋₊ : ℝ) ≠ 0 := by
    exact_mod_cast (by omega : ⌊a * x + b⌋₊ ≠ 0)
  simp only [Function.comp_apply]
  rw [div_pow]
  field_simp

end PiExponent

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Polynomials_SimplexUnweighted
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

namespace PiExponent

theorem card_unweightedSimplex (d N : ℕ) :
    (unweightedSimplex d N).card = (N + d).choose d := by
  classical
  let target : Finset (Fin (d + 1) →₀ ℕ) := Finset.univ.finsuppAntidiag N
  have hc : target.card = (N + d).choose d := by
    rw [Finset.card_finsuppAntidiag_nat_eq_choose]
    simp only [Finset.card_univ, Fintype.card_fin]
    rw [show d + 1 + N - 1 = N + d by omega, Nat.choose_symm_add]
  rw [← hc]
  let f : (Fin d → ℕ) → (Fin (d + 1) →₀ ℕ) := fun a =>
    Finsupp.equivFunOnFinite.symm (Fin.cons (N - ∑ i, a i) a)
  apply Finset.card_bij (fun a _ => f a)
  · intro a ha
    apply Finset.mem_finsuppAntidiag.mpr
    constructor
    · simp only [f, Finsupp.coe_equivFunOnFinite_symm, Fin.sum_univ_succ,
        Fin.cons_zero, Fin.cons_succ]
      exact Nat.sub_add_cancel (mem_unweightedSimplex.mp ha)
    · exact Finset.subset_univ _
  · intro a ha b hb hab
    funext i
    have h := congrArg (fun g : Fin (d + 1) →₀ ℕ => g i.succ) hab
    simpa only [f, Finsupp.coe_equivFunOnFinite_symm, Fin.cons_succ] using h
  · intro b hb
    obtain ⟨hs, _⟩ := Finset.mem_finsuppAntidiag.mp hb
    have hs' : b 0 + ∑ i : Fin d, b i.succ = N := by
      simpa only [Fin.sum_univ_succ] using hs
    refine ⟨fun i => b i.succ, mem_unweightedSimplex.mpr (by omega), ?_⟩
    apply Finsupp.ext
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · change N - ∑ j : Fin d, b j.succ = b 0
      omega
    · change b j.succ = b j.succ
      rfl

open Filter Topology Asymptotics

theorem tendsto_choose_normalized (d : ℕ) :
    Tendsto (fun N : ℕ => (N.choose d : ℝ) / (N : ℝ) ^ d)
      atTop (𝓝 (1 / (d.factorial : ℝ))) := by
  have h := (isEquivalent_choose d).div
    (IsEquivalent.refl : (fun N : ℕ => (N : ℝ) ^ d) ~[atTop]
      (fun N : ℕ => (N : ℝ) ^ d))
  apply h.symm.tendsto_nhds
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  change 1 / (d.factorial : ℝ) = ((N : ℝ) ^ d / (d.factorial : ℝ)) / (N : ℝ) ^ d
  field_simp

theorem tendsto_choose_add_normalized (d c : ℕ) :
    Tendsto (fun N : ℕ => ((N + c).choose d : ℝ) / (N : ℝ) ^ d)
      atTop (𝓝 (1 / (d.factorial : ℝ))) := by
  have h₁ := (tendsto_choose_normalized d).comp (tendsto_add_atTop_nat c)
  have h₂ : Tendsto (fun N : ℕ => ((N + c : ℕ) : ℝ) / (N : ℝ))
      atTop (𝓝 1) := by
    simpa [Nat.cast_add, add_comm] using
      (tendsto_add_mul_div_add_mul_atTop_nhds (c : ℝ) 0 1 (d := 1) (by norm_num))
  have h := h₁.mul (h₂.pow d)
  simp only [one_pow, mul_one] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hn : ((N + c : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (by omega : N + c ≠ 0)
  simp only [Function.comp_apply]
  rw [div_pow]
  field_simp

theorem tendsto_card_unweightedSimplex (d : ℕ) :
    Tendsto (fun N : ℕ => ((unweightedSimplex d N).card : ℝ) / (N : ℝ) ^ d)
      atTop (𝓝 (1 / (d.factorial : ℝ))) := by
  simpa only [card_unweightedSimplex] using tendsto_choose_add_normalized d d

theorem tendsto_card_unweightedSimplex_add (d c : ℕ) :
    Tendsto (fun N : ℕ => ((unweightedSimplex d (N + c)).card : ℝ) / (N : ℝ) ^ d)
      atTop (𝓝 (1 / (d.factorial : ℝ))) := by
  simpa only [card_unweightedSimplex, Nat.add_assoc] using
    tendsto_choose_add_normalized d (c + d)

end PiExponent

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Polynomials_SimplexCounting
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

namespace PiExponent

theorem mem_natWeightedSimplex {d : ℕ} {w : Fin d → ℕ}
    (hw : ∀ i, 0 < w i) {N : ℕ} {a : Fin d → ℕ} :
    a ∈ natWeightedSimplex w N ↔ ∑ i, w i * a i ≤ N := by
  constructor
  · exact fun h => (Finset.mem_filter.mp h).2
  · intro h
    refine Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr ?_, h⟩
    intro i
    apply Finset.mem_range.mpr
    have h₁ : a i ≤ w i * a i := Nat.le_mul_of_pos_left (a i) (hw i)
    have h₂ : w i * a i ≤ ∑ j, w j * a j :=
      Finset.single_le_sum (f := fun j => w j * a j)
        (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    omega

theorem simplex_count_lower_sandwich {d : ℕ} (w : Fin d → ℕ)
    (hw : ∀ i, 0 < w i) (N : ℕ) :
    (natWeightedSimplex (fun _ : Fin d => 1) N).card ≤
      (natWeightedSimplex w N).card * ∏ i, w i := by
  rw [← card_residueRectangle, ← Finset.card_product]
  let f : (Fin d → ℕ) → (Fin d → ℕ) × (Fin d → ℕ) :=
    fun b => (fun i => b i / w i, fun i => b i % w i)
  apply Finset.card_le_card_of_injOn f
  · intro b hb
    apply Finset.mem_product.mpr
    constructor
    · apply (mem_natWeightedSimplex hw).mpr
      have hb' := (mem_natWeightedSimplex (fun _ => by decide)).mp hb
      simp only [one_mul] at hb'
      exact (Finset.sum_le_sum (fun i _ => Nat.mul_div_le (b i) (w i))).trans hb'
    · exact mem_residueRectangle.mpr (fun i => Nat.mod_lt (b i) (hw i))
  · intro a ha b hb hab
    have hq := congrArg Prod.fst hab
    have hr := congrArg Prod.snd hab
    funext i
    have hqi := congrFun hq i
    have hri := congrFun hr i
    change a i / w i = b i / w i at hqi
    change a i % w i = b i % w i at hri
    have ha' := Nat.div_add_mod (a i) (w i)
    have hb' := Nat.div_add_mod (b i) (w i)
    calc
      a i = w i * (a i / w i) + a i % w i := ha'.symm
      _ = w i * (b i / w i) + b i % w i := by rw [hqi, hri]
      _ = b i := hb'

theorem simplex_count_upper_sandwich {d : ℕ} (w : Fin d → ℕ)
    (hw : ∀ i, 0 < w i) (N : ℕ) :
    (natWeightedSimplex w N).card * (∏ i, w i) ≤
      (natWeightedSimplex (fun _ : Fin d => 1) (N + ∑ i, (w i - 1))).card := by
  rw [← card_residueRectangle, ← Finset.card_product]
  let f : ((Fin d → ℕ) × (Fin d → ℕ)) → (Fin d → ℕ) :=
    fun ar i => w i * ar.1 i + ar.2 i
  apply Finset.card_le_card_of_injOn f
  · intro ar har
    obtain ⟨ha, hr⟩ := Finset.mem_product.mp har
    apply (mem_natWeightedSimplex (fun _ => by decide)).mpr
    simp only [one_mul]
    change ∑ i, (w i * ar.1 i + ar.2 i) ≤ _
    rw [Finset.sum_add_distrib]
    apply Nat.add_le_add ((mem_natWeightedSimplex hw).mp ha)
    apply Finset.sum_le_sum
    intro i hi
    have := mem_residueRectangle.mp hr i
    omega
  · intro ar har bs hbs hab
    obtain ⟨ha, hr⟩ := Finset.mem_product.mp har
    obtain ⟨hb, hs⟩ := Finset.mem_product.mp hbs
    apply Prod.ext
    · funext i
      have hi := congrFun hab i
      change w i * ar.1 i + ar.2 i = w i * bs.1 i + bs.2 i at hi
      have hri := mem_residueRectangle.mp hr i
      have hsi := mem_residueRectangle.mp hs i
      have hdiv := congrArg (fun n => n / w i) hi
      rw [Nat.add_div_of_dvd_right (Nat.dvd_mul_right (w i) (ar.1 i)),
        Nat.add_div_of_dvd_right (Nat.dvd_mul_right (w i) (bs.1 i))] at hdiv
      simpa [Nat.div_eq_of_lt hri, Nat.div_eq_of_lt hsi,
        Nat.mul_div_cancel_left _ (hw i)] using hdiv
    · funext i
      have hi := congrFun hab i
      change w i * ar.1 i + ar.2 i = w i * bs.1 i + bs.2 i at hi
      have hri := mem_residueRectangle.mp hr i
      have hsi := mem_residueRectangle.mp hs i
      have hmod := congrArg (fun n => n % w i) hi
      simpa [Nat.add_mod, Nat.mod_eq_of_lt hri, Nat.mod_eq_of_lt hsi] using hmod

@[simp] theorem natWeightedSimplex_one (d N : ℕ) :
    natWeightedSimplex (fun _ : Fin d => 1) N = unweightedSimplex d N := by
  ext a
  rw [mem_natWeightedSimplex (w := fun _ : Fin d => 1) (fun _ => by decide), mem_unweightedSimplex]
  simp only [one_mul]

open Filter Topology

theorem tendsto_card_natWeightedSimplex {d : ℕ} (w : Fin d → ℕ)
    (hw : ∀ i, 0 < w i) :
    Tendsto (fun N : ℕ => ((natWeightedSimplex w N).card : ℝ) / (N : ℝ) ^ d)
      atTop (𝓝 (1 / ((d.factorial : ℝ) * ∏ i, (w i : ℝ)))) := by
  let P : ℝ := ∏ i, (w i : ℝ)
  have hP : 0 < P := Finset.prod_pos (fun i _ => by exact_mod_cast hw i)
  have hs : Tendsto
      (fun N : ℕ => ((natWeightedSimplex w N).card : ℝ) * P / (N : ℝ) ^ d)
      atTop (𝓝 (1 / (d.factorial : ℝ))) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      (tendsto_card_unweightedSimplex d)
      (tendsto_card_unweightedSimplex_add d (∑ i, (w i - 1)))
    · intro N
      apply div_le_div_of_nonneg_right _ (by positivity)
      have h := simplex_count_lower_sandwich w hw N
      rw [natWeightedSimplex_one] at h
      dsimp [P]
      exact_mod_cast h
    · intro N
      apply div_le_div_of_nonneg_right _ (by positivity)
      have h := simplex_count_upper_sandwich w hw N
      rw [natWeightedSimplex_one] at h
      dsimp [P]
      exact_mod_cast h
  have h := hs.div_const P
  have heq : 1 / (d.factorial : ℝ) / P =
      1 / ((d.factorial : ℝ) * ∏ i, (w i : ℝ)) := by
    simp only [P, div_div]
  rw [heq] at h
  apply h.congr'
  exact Filter.Eventually.of_forall (fun N => by
    change ((natWeightedSimplex w N).card : ℝ) * P / (N : ℝ) ^ d / P = _
    field_simp)

theorem realWeightedSimplex_scaled {d : ℕ} (w : Fin d → ℕ)
    (hw : ∀ i, 0 < w i) {c H : ℝ} (hc : 0 < c) (hH : 0 ≤ H) :
    realWeightedSimplex (fun i => (w i : ℝ) / c) H =
      natWeightedSimplex w ⌊c * H⌋₊ := by
  ext a
  rw [mem_realWeightedSimplex (fun i => div_pos (by exact_mod_cast hw i) hc),
    mem_natWeightedSimplex hw, Nat.le_floor_iff (mul_nonneg hc.le hH)]
  have hs : (∑ i, (w i : ℝ) / c * (a i : ℝ)) =
      ((∑ i, w i * a i : ℕ) : ℝ) / c := by
    simp [Nat.cast_sum, Nat.cast_mul, Finset.sum_div, div_mul_eq_mul_div]
  rw [hs, div_le_iff₀ hc, mul_comm H c]

theorem tendsto_card_realWeightedSimplex_scaled {d : ℕ} (w : Fin d → ℕ)
    (hw : ∀ i, 0 < w i) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun H : ℝ => ((realWeightedSimplex (fun i => (w i : ℝ) / c) H).card : ℝ) / H ^ d)
      atTop (𝓝 ((1 / ((d.factorial : ℝ) * ∏ i, (w i : ℝ))) * c ^ d)) := by
  have h := tendsto_normalized_natFloor_affine
    (tendsto_card_natWeightedSimplex w hw) hc 0
  apply h.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with H hH
  simp only [add_zero, realWeightedSimplex_scaled w hw hc hH]

theorem tendsto_card_strictWeightedSimplex_scaled {d : ℕ} (w : Fin d → ℕ)
    (hw : ∀ i, 0 < w i) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun H : ℝ => ((strictWeightedSimplex (fun i => (w i : ℝ) / c) H).card : ℝ) / H ^ d)
      atTop (𝓝 ((1 / ((d.factorial : ℝ) * ∏ i, (w i : ℝ))) * c ^ d)) := by
  have hlo := tendsto_normalized_natFloor_affine
    (tendsto_card_natWeightedSimplex w hw) hc (-1)
  have hhi := tendsto_card_realWeightedSimplex_scaled w hw hc
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi
  · filter_upwards [eventually_ge_atTop (1 / c)] with H hH
    have hHpos : 0 < H := (div_pos zero_lt_one hc).trans_le hH
    have hcH : 1 ≤ c * H := by
      have := (div_le_iff₀ hc).mp hH
      nlinarith
    apply div_le_div_of_nonneg_right _ (pow_nonneg hHpos.le d)
    exact_mod_cast (Finset.card_le_card (show
      natWeightedSimplex w ⌊c * H + -1⌋₊ ⊆
      strictWeightedSimplex (fun i => (w i : ℝ) / c) H from by
        intro a ha
        apply (mem_strictWeightedSimplex (fun i => div_pos (by exact_mod_cast hw i) hc)).mpr
        have ha' := (mem_natWeightedSimplex hw).mp ha
        have hs : ((∑ i, w i * a i : ℕ) : ℝ) ≤ c * H + -1 :=
          (Nat.le_floor_iff (by linarith)).mp ha'
        have heq : (∑ i, (w i : ℝ) / c * (a i : ℝ)) =
            ((∑ i, w i * a i : ℕ) : ℝ) / c := by
          simp [Nat.cast_sum, Nat.cast_mul, Finset.sum_div, div_mul_eq_mul_div]
        rw [heq, div_lt_iff₀ hc]
        nlinarith))
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with H hH
    apply div_le_div_of_nonneg_right _ (pow_nonneg hH d)
    exact_mod_cast (Finset.card_le_card (Finset.filter_subset
      (fun a : Fin d → ℕ => ∑ i, (w i : ℝ) / c * (a i : ℝ) < H)
      (realWeightedSimplex (fun i => (w i : ℝ) / c) H)))

end PiExponent

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Polynomials_SimplexRational
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators
open Filter Topology

namespace PiExponent

theorem common_denominator_simplex_constant {d D : ℕ} {ρ : Fin d → ℚ}
    {w : Fin d → ℕ} (hD : 0 < D) (hw : ∀ i, 0 < w i)
    (hweights : ∀ i, (ρ i : ℝ) = (w i : ℝ) / (D : ℝ)) :
    (1 / ((d.factorial : ℝ) * ∏ i, (w i : ℝ))) * (D : ℝ) ^ d =
      1 / ((d.factorial : ℝ) * ∏ i, (ρ i : ℝ)) := by
  have hprod : (∏ i, (ρ i : ℝ)) = (∏ i, (w i : ℝ)) / (D : ℝ) ^ d := by
    simp_rw [hweights]
    rw [Finset.prod_div_distrib]
    simp
  have hDne : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
  have hPne : (∏ i, (w i : ℝ)) ≠ 0 :=
    (Finset.prod_pos (fun i _ => by exact_mod_cast hw i)).ne'
  have hfac : (d.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero d
  rw [hprod]
  field_simp

theorem tendsto_card_realWeightedSimplex_rational {d : ℕ}
    (ρ : Fin d → ℚ) (hρ : ∀ i, 0 < ρ i) :
    Tendsto (fun H : ℝ =>
      ((realWeightedSimplex (fun i => (ρ i : ℝ)) H).card : ℝ) / H ^ d)
      atTop (𝓝 (1 / ((d.factorial : ℝ) * ∏ i, (ρ i : ℝ)))) := by
  obtain ⟨D, hD, w, hw, hweights⟩ := positive_rational_weights_common_denominator ρ hρ
  have h := tendsto_card_realWeightedSimplex_scaled w hw
    (show (0 : ℝ) < D by exact_mod_cast hD)
  rw [common_denominator_simplex_constant hD hw hweights] at h
  simpa only [← hweights] using h

theorem tendsto_card_strictWeightedSimplex_rational {d : ℕ}
    (ρ : Fin d → ℚ) (hρ : ∀ i, 0 < ρ i) :
    Tendsto (fun H : ℝ =>
      ((strictWeightedSimplex (fun i => (ρ i : ℝ)) H).card : ℝ) / H ^ d)
      atTop (𝓝 (1 / ((d.factorial : ℝ) * ∏ i, (ρ i : ℝ)))) := by
  obtain ⟨D, hD, w, hw, hweights⟩ := positive_rational_weights_common_denominator ρ hρ
  have h := tendsto_card_strictWeightedSimplex_scaled w hw
    (show (0 : ℝ) < D by exact_mod_cast hD)
  rw [common_denominator_simplex_constant hD hw hweights] at h
  simpa only [← hweights] using h

end PiExponent

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Polynomials_AuxiliaryPolynomial
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
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

theorem polynomialOfCoefficients_injective {d : ℕ} (S : Finset (Fin d → ℕ)) :
    Function.Injective (polynomialOfCoefficients S) := by
  intro x y h
  funext a
  have := congrArg (fun p : MvPolynomial (Fin d) ℂ =>
    p.coeff (InterpolationMatrix.exponentVector a.val)) h
  simpa only [polynomialOfCoefficients_coeff] using this

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

theorem polynomialOfCoefficients_weighted {m : ℕ} (W : Fin (m + 1) → ℝ)
    (hW : ∀ i, 0 < W i) (N : ℝ)
    (x : ↥(realWeightedSimplex W N) → ℂ) :
    PiExponentApprox.HasWeightedDegreeLE W N
      (polynomialOfCoefficients (realWeightedSimplex W N) x) := by
  classical
  intro e he
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp
    (polynomialOfCoefficients_support _ x he)
  have h := (mem_realWeightedSimplex hW).mp ha
  simpa only [PiExponentApprox.monomialWeight,
    InterpolationMatrix.exponentVector_apply, mul_comm] using h

theorem exists_nonzero_kernel_of_card_lt {C R : Type*} [Fintype C] [Fintype R]
    (E : (C → ℂ) →ₗ[ℂ] (R → ℂ)) (h : Fintype.card R < Fintype.card C) :
    ∃ x : C → ℂ, x ≠ 0 ∧ E x = 0 := by
  have hk : LinearMap.ker E ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt
    (by simpa only [Module.finrank_fintype_fun_eq_card] using h)
  obtain ⟨x, hx, hn⟩ := (LinearMap.ker E).ne_bot_iff.mp hk
  exact ⟨x, hn, LinearMap.mem_ker.mp hx⟩

theorem tendsto_card_strictWeightedSimplex_scale {d : ℕ} (V : Fin d → ℚ)
    (hV : ∀ i, 0 < V i) {a : ℝ} (ha : 0 < a) :
    Tendsto (fun N : ℝ =>
      ((strictWeightedSimplex (fun i => (V i : ℝ)) (a * N)).card : ℝ) / N ^ d)
      atTop (𝓝 (a ^ d / ((d.factorial : ℝ) * ∏ i, (V i : ℝ)))) := by
  have ht : Tendsto (fun N : ℝ => a * N) atTop atTop :=
    Tendsto.const_mul_atTop ha tendsto_id
  have h := ((tendsto_card_strictWeightedSimplex_rational V hV).comp ht).mul_const (a ^ d)
  have heq : 1 / ((d.factorial : ℝ) * ∏ i, (V i : ℝ)) * a ^ d =
      a ^ d / ((d.factorial : ℝ) * ∏ i, (V i : ℝ)) := by ring
  rw [heq] at h
  apply h.congr'
  exact Eventually.of_forall (fun N => by
    simp only [Function.comp_apply, mul_pow]
    field_simp)

theorem eventually_auxiliary_card_lt {d : ℕ} (W V : Fin d → ℚ)
    (hW : ∀ i, 0 < W i) (hV : ∀ i, 0 < V i) (K : ℕ)
    {a : ℝ} (ha : 0 < a)
    (hvol : (K : ℝ) * a ^ d * (∏ i, (W i : ℝ)) / (∏ i, (V i : ℝ)) < 1) :
    ∀ᶠ N : ℝ in atTop,
      K * (strictWeightedSimplex (fun i => (V i : ℝ)) (a * N)).card <
        (realWeightedSimplex (fun i => (W i : ℝ)) N).card := by
  have hPW : 0 < ∏ i, (W i : ℝ) := Finset.prod_pos (fun i _ => by exact_mod_cast hW i)
  have hPV : 0 < ∏ i, (V i : ℝ) := Finset.prod_pos (fun i _ => by exact_mod_cast hV i)
  have hF : (0 : ℝ) < d.factorial := by exact_mod_cast Nat.factorial_pos d
  have hconst : (K : ℝ) * (a ^ d / ((d.factorial : ℝ) * ∏ i, (V i : ℝ))) <
      1 / ((d.factorial : ℝ) * ∏ i, (W i : ℝ)) := by
    have hmain := (div_lt_one hPV).mp hvol
    apply (lt_div_iff₀ (mul_pos hF hPW)).mpr
    have heq : (K : ℝ) * (a ^ d / ((d.factorial : ℝ) * ∏ i, (V i : ℝ))) *
        ((d.factorial : ℝ) * ∏ i, (W i : ℝ)) =
        (K : ℝ) * a ^ d * (∏ i, (W i : ℝ)) / (∏ i, (V i : ℝ)) := by
      field_simp
    rw [heq]
    exact hvol
  have hsmall := ((tendsto_card_strictWeightedSimplex_scale V hV ha).const_mul (K : ℝ)).eventually_lt
    (tendsto_card_realWeightedSimplex_rational W hW) hconst
  filter_upwards [hsmall, eventually_gt_atTop (0 : ℝ)] with N hN hNpos
  have hscaled : ((K * (strictWeightedSimplex (fun i => (V i : ℝ)) (a * N)).card : ℕ) : ℝ) /
      N ^ d < ((realWeightedSimplex (fun i => (W i : ℝ)) N).card : ℝ) / N ^ d := by
    simpa only [Nat.cast_mul, mul_div_assoc] using hN
  exact_mod_cast (div_lt_div_iff_of_pos_right (pow_pos hNpos d)).mp hscaled

theorem eventually_exists_auxiliaryPolynomial {m : ℕ} (W V : Fin (m + 1) → ℚ)
    (hW : ∀ i, 0 < W i) (hV : ∀ i, 0 < V i) (K : ℕ)
    {a : ℝ} (ha : 0 < a)
    (hvol : (K : ℝ) * a ^ (m + 1) * (∏ i, (W i : ℝ)) / (∏ i, (V i : ℝ)) < 1) :
    ∀ᶠ N : ℝ in atTop,
      ∀ E : PiExponentApprox.FramePolynomial m →ₗ[ℂ]
        ((Fin K × ↥(strictWeightedSimplex (fun i => (V i : ℝ)) (a * N))) → ℂ),
      ∃ p : PiExponentApprox.FramePolynomial m, p ≠ 0 ∧
        PiExponentApprox.HasWeightedDegreeLE (fun i => (W i : ℝ)) N p ∧ E p = 0 := by
  classical
  filter_upwards [eventually_auxiliary_card_lt W V hW hV K ha hvol] with N hN
  intro E
  let S := realWeightedSimplex (fun i => (W i : ℝ)) N
  let A := E.comp (polynomialOfCoefficients S)
  have hcard : Fintype.card (Fin K × ↥(strictWeightedSimplex (fun i => (V i : ℝ)) (a * N))) <
      Fintype.card S := by simpa [S] using hN
  obtain ⟨x, hx, hAx⟩ := exists_nonzero_kernel_of_card_lt A hcard
  refine ⟨polynomialOfCoefficients S x, ?_, ?_, hAx⟩
  · intro hp
    apply hx
    apply polynomialOfCoefficients_injective S
    simpa using hp
  · exact polynomialOfCoefficients_weighted (fun i => (W i : ℝ))
      (fun i => by exact_mod_cast hW i) N x

end PiExponent

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Jets_FormalAuxiliaryJet
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open Filter Topology
namespace PiExponent

theorem eventually_exists_formalJet_auxiliaryPolynomial {m : ℕ}
    (W V : Fin (m+1) → ℚ) (hW : ∀ i, 0 < W i) (hV : ∀ i, 0 < V i)
    (K : ℕ) {a : ℝ} (ha : 0 < a)
    (hvol : (K : ℝ) * a^(m+1) * (∏ i, (W i : ℝ)) / (∏ i, (V i : ℝ)) < 1)
    (c : Fin K → Fin m → ℂ) :
    ∀ᶠ N : ℝ in atTop, ∃ p : PiExponentApprox.FramePolynomial m, p ≠ 0 ∧
      PiExponentApprox.HasWeightedDegreeLE (fun i => (W i : ℝ)) N p ∧
      ∀ j d, Finsupp.weight (fun i => (V i : ℝ)) d < a*N →
        MvPowerSeries.coeff d (FormalLogJet.formalJet (c j) p) = 0 := by
  filter_upwards [eventually_exists_auxiliaryPolynomial W V hW hV K ha hvol] with N hN
  obtain ⟨p, hp, hw, he⟩ := hN (formalJetEvaluation K (fun i => (V i : ℝ)) (a*N) c)
  refine ⟨p, hp, hw, ?_⟩
  intro j d hd
  have hmem : (fun i => d i) ∈ strictWeightedSimplex (fun i => (V i : ℝ)) (a*N) := by
    apply (mem_strictWeightedSimplex (fun i => by exact_mod_cast hV i)).mpr
    simpa [Finsupp.weight_eq_sum, nsmul_eq_mul, mul_comm] using hd
  have hh := congrFun he (j, ⟨(fun i => d i), hmem⟩)
  have hd' : InterpolationMatrix.exponentVector (fun i => d i) = d := by ext i; rfl
  simpa [formalJetEvaluation, hd'] using hh

theorem eventually_exists_formalJet_auxiliaryPolynomial_nat {m : ℕ}
    (W V : Fin (m+1) → ℚ) (hW : ∀ i, 0 < W i) (hV : ∀ i, 0 < V i)
    (K : ℕ) {a : ℚ} (ha : 0 < a)
    (hvol : (K : ℝ) * (a : ℝ)^(m+1) * (∏ i, (W i : ℝ)) / (∏ i, (V i : ℝ)) < 1)
    (c : Fin K → Fin m → ℂ) :
    ∀ᶠ N : ℕ in atTop, ∃ p : PiExponentApprox.FramePolynomial m, p ≠ 0 ∧
      PiExponentApprox.HasWeightedDegreeLE (fun i => (W i : ℝ)) N p ∧
      ∀ j, FormalLogJet.formalJet (c j) p ∈
        JetGeometry.rationalWeightedIdeal V (fun i => le_of_lt (hV i)) (a*N) := by
  have h := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
    (eventually_exists_formalJet_auxiliaryPolynomial W V hW hV K
      (by exact_mod_cast ha) hvol c)
  filter_upwards [h] with N hN
  obtain ⟨p, hp, hw, hv⟩ := hN
  refine ⟨p, hp, hw, ?_⟩
  intro j d hd
  apply hv j d
  have hcast : ((Finsupp.weight V d : ℚ) : ℝ) < (a : ℝ)*(N : ℝ) := by exact_mod_cast hd
  simpa [Finsupp.weight_eq_sum, nsmul_eq_mul] using hcast

end PiExponent

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_CurveInequality
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open Filter Topology
namespace PiExponent.CurveInequality

open PiExponentApprox CurveValuationCenter PlaceValuationRing CurveContactFamily
open PersistentWeightComparison


theorem excess_implies_zeroth_eq_one_q68_oai
    {E : Type*} [Field E] [Algebra ℂ E] {m K : ℕ}
    (hres : ∀ p : NormalizedPlace ℂ E,
      Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p)))
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (z : Fin (m+1) → E) (c : Fin K → Fin m → ℂ)
    (hz : ∃ i, Transcendental ℂ (z i))
    (hheight : (CurveFieldRigidity.coordinateKernel z).height ≤ m)
    (w v : Fin (m+1) → ℚ) (hw : ∀ i, 0 < w i) (hv : ∀ i, 0 < v i)
    (sigma : ℚ) (hsigma : 0 < sigma)
    (hvol : (K : ℝ) * (1+3*(sigma : ℝ))^(m+1) *
      (∏ i, (w i : ℝ)) / (∏ i, (v i : ℝ)) < 1)
    (hseparated : ∀ A B : Finset (Fin (m+1)), A.card = B.card →
      ∀ i, i ≠ 0 → i ∈ A → i ∉ B →
      (∀ j, i < j → (j ∈ A ↔ j ∈ B)) →
      comparisonConstant m sigma * (∏ j ∈ B, (v j : ℝ)) < ∏ j ∈ A, (w j : ℝ))
    (hexcess : CurveContactSum.weightedDegree hfinite z w <
      (1+(sigma : ℝ)) * ∑ p ∈ places hfinite z c hz, (contact hres hfinite z c hz v p : ℝ)) :
    z 0 = 1 := by
  have hvR (i : Fin (m+1)) : (0 : ℝ) < v i := by exact_mod_cast hv i
  have hsR : (0 : ℝ) < sigma := by exact_mod_cast hsigma
  have haux := eventually_exists_formalJet_auxiliaryPolynomial_nat w v hw hv K
    (a := 1+3*sigma) (by positivity) (by simpa using hvol) c
  have hrect := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
    (eventually_uniformRectangles (m+1) (fun i => (v i : ℝ)) hvR
      ((sigma : ℝ)/((m : ℝ)+2)) (by positivity))
  obtain ⟨N, hauxN, hrectN, hN⟩ :=
    (haux.and (hrect.and (eventually_gt_atTop (0 : ℕ)))).exists
  obtain ⟨F, hF0, hF, hjet⟩ := hauxN
  have hwords := CurveDerivativeVanishing.logarithmic_words_vanish_q68 hres hfinite z c hz
    w v hw hv sigma hsigma N hN F hF hjet hexcess
  have hS : (places hfinite z c hz).Nonempty := by
    by_contra h
    have he : places hfinite z c hz = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    rw [he, Finset.sum_empty, mul_zero] at hexcess
    exact (not_lt_of_ge (CurveContactSum.weightedDegree_nonneg hfinite z w)) hexcess
  obtain ⟨p,hp⟩ := hS
  exact CurveFieldRigidity.logarithmic_coordinate_eq_one z
    (fullCenter (c (center hfinite z c hz p hp))) rfl p
    (centered hfinite z c hz p hp) hheight w hw (fun i => (v i : ℝ)) hvR
    sigma N hsR (by exact_mod_cast hN) hrectN F hF0 hF hwords hseparated

end PiExponent.CurveInequality
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.PiExponent.CurveInequality.excess_implies_zeroth_eq_one_q68_oai.{u_1} := @OAI.PiExponent.CurveInequality.excess_implies_zeroth_eq_one_q68_oai.{u_1}
