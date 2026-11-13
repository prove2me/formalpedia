-- Prove2me | solution 1 for OAI.KadisonKastler.exists_unitary_boundary_intertwiner
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T05:09:02.437266+00:00
-- url     : https://prove2.me/submissions/1fdc2c53-baed-47ed-b2b6-181d7876eba7

import Mathlib
import Mathlib.Algebra.Star.StarAlgHom
import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.Topology.ContinuousMap.Bounded.Star
import Mathlib.Topology.MetricSpace.Cauchy
import Definitions.Def_Q260K007
import Definitions.Def_Q260K017

section
-- module Solutions.OAIQ075_KS.KadisonKastler_Polar
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-!
# Polar unitaries close to the identity

We construct the polar factor of an invertible element using the positive
square root supplied by continuous functional calculus.
-/

namespace KadisonKastler

open scoped CStarAlgebra

noncomputable section

variable {A : Type*} [CStarAlgebra A]

section Ordered

variable [PartialOrder A] [StarOrderedRing A]

omit [PartialOrder A] [StarOrderedRing A] in
/-- Inverting a unit close to one gives the usual geometric-series bound. -/
theorem norm_unit_inv_le_of_near_one [Nontrivial A] (t : Aˣ)
    (ht : ‖(t : A) - 1‖ < 1) :
    ‖((t⁻¹ : Aˣ) : A)‖ ≤ (1 - ‖(t : A) - 1‖)⁻¹ := by
  have hpos : 0 < 1 - ‖(t : A) - 1‖ := sub_pos.mpr ht
  have hidentity : ((t⁻¹ : Aˣ) : A) - 1 =
      ((t⁻¹ : Aˣ) : A) * (1 - (t : A)) := by
    rw [mul_sub, mul_one, Units.inv_mul]
  have htriangle := norm_le_norm_sub_add (((t⁻¹ : Aˣ) : A)) (1 : A)
  have hproduct := norm_mul_le (((t⁻¹ : Aˣ) : A)) (1 - (t : A))
  rw [← hidentity, norm_sub_rev (1 : A) (t : A)] at hproduct
  rw [norm_one] at htriangle
  have hbound : (1 - ‖(t : A) - 1‖) * ‖((t⁻¹ : Aˣ) : A)‖ ≤ 1 := by nlinarith
  simpa only [mul_one] using (le_inv_mul_iff₀ hpos).mpr hbound

/-- A positive unit with upper bounds on its norm and inverse lies within
the same radius of the identity. -/
theorem norm_positive_unit_sub_one_le [Nontrivial A] (s : Aˣ) (hs : 0 ≤ (s : A)) {r : ℝ}
    (hr : 0 ≤ r) (hr₁ : r < 1) (hnorm : ‖(s : A)‖ ≤ 1 + r)
    (hinv : ‖((s⁻¹ : Aˣ) : A)‖ ≤ (1 - r)⁻¹) :
    ‖(s : A) - 1‖ ≤ r := by
  have hrepr : cfc (fun x : ℝ => x - 1) (s : A) = (s : A) - 1 := by
    rw [cfc_sub (fun x : ℝ => x) (fun _ : ℝ => 1) (s : A),
      cfc_id' ℝ (s : A), cfc_const_one ℝ (s : A)]
  rw [← hrepr]
  apply norm_cfc_le hr
  intro x hx
  have hx₀ : 0 ≤ x := spectrum_nonneg_of_nonneg hs hx
  have hxne : x ≠ 0 := by
    intro hzero
    exact spectrum.zero_notMem ℝ s.isUnit (hzero ▸ hx)
  have hxpos : 0 < x := lt_of_le_of_ne hx₀ (Ne.symm hxne)
  have hxupper : x ≤ 1 + r :=
    (Real.le_norm_self x).trans ((spectrum.norm_le_norm_of_mem hx).trans hnorm)
  have hxinv : x⁻¹ ≤ (1 - r)⁻¹ :=
    (Real.le_norm_self (x⁻¹)).trans
      ((spectrum.norm_le_norm_of_mem (spectrum.inv₀_mem_inv hx)).trans hinv)
  have hxlower : 1 - r ≤ x :=
    (inv_le_inv₀ hxpos (sub_pos.mpr hr₁)).mp hxinv
  rw [Real.norm_eq_abs]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Taking the absolute value of a unit does not increase its distance from
one, provided that distance is less than one. -/
theorem norm_abs_sub_one_le [Nontrivial A] (t : Aˣ)
    (ht : ‖(t : A) - 1‖ < 1) :
    ‖CFC.abs (t : A) - 1‖ ≤ ‖(t : A) - 1‖ := by
  obtain ⟨u, hu⟩ := exists_unitary_mul_abs t
  let s : Aˣ := (isUnit_abs t).unit
  have hs : (s : A) = CFC.abs (t : A) := (isUnit_abs t).unit_spec
  have hdecomp : (u : A) * (s : A) = (t : A) := by rwa [hs]
  have hinveq : ((s⁻¹ : Aˣ) : A) = ((t⁻¹ : Aˣ) : A) * (u : A) := by
    calc
      ((s⁻¹ : Aˣ) : A) =
          (((t⁻¹ : Aˣ) : A) * (t : A)) * ((s⁻¹ : Aˣ) : A) := by simp
      _ = (((t⁻¹ : Aˣ) : A) * ((u : A) * (s : A))) * ((s⁻¹ : Aˣ) : A) := by
        rw [hdecomp]
      _ = ((t⁻¹ : Aˣ) : A) * (u : A) := by
        simp only [mul_assoc, Units.mul_inv, mul_one]
  have hsinv : ‖((s⁻¹ : Aˣ) : A)‖ = ‖((t⁻¹ : Aˣ) : A)‖ := by
    rw [hinveq, CStarRing.norm_mul_coe_unitary]
  have hsnorm : ‖(s : A)‖ ≤ 1 + ‖(t : A) - 1‖ := by
    rw [hs, CFC.norm_abs]
    have h := norm_le_norm_sub_add (t : A) (1 : A)
    simpa only [norm_one, add_comm] using h
  rw [← hs]
  apply norm_positive_unit_sub_one_le s (by rw [hs]; exact CFC.abs_nonneg _)
    (norm_nonneg _) ht hsnorm
  rw [hsinv]
  exact norm_unit_inv_le_of_near_one t ht

/-- The polar unitary of a unit close to one is within twice that distance
of one. -/
theorem exists_polar_unitary_near_one_of_unit [Nontrivial A] (t : Aˣ)
    (ht : ‖(t : A) - 1‖ < 1) :
    ∃ u : unitary A, (u : A) * CFC.abs (t : A) = (t : A) ∧
      ‖(u : A) - 1‖ ≤ 2 * ‖(t : A) - 1‖ := by
  obtain ⟨u, hu⟩ := exists_unitary_mul_abs t
  refine ⟨u, hu, ?_⟩
  have hdiff : (u : A) - (t : A) = (u : A) * (1 - CFC.abs (t : A)) := by
    rw [mul_sub, mul_one, hu]
  calc
    ‖(u : A) - 1‖ ≤ ‖(u : A) - (t : A)‖ + ‖(t : A) - 1‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ = ‖1 - CFC.abs (t : A)‖ + ‖(t : A) - 1‖ := by
      rw [hdiff, CStarRing.norm_coe_unitary_mul]
    _ ≤ ‖(t : A) - 1‖ + ‖(t : A) - 1‖ := by
      apply add_le_add _ le_rfl
      simpa only [norm_sub_rev] using norm_abs_sub_one_le t ht
    _ = 2 * ‖(t : A) - 1‖ := by ring

/-- Every element within distance one of the identity has a unitary polar
factor within twice its original distance of the identity. -/
theorem exists_polar_unitary_near_one (T : A) (hT : ‖T - 1‖ < 1) :
    ∃ u : unitary A, (u : A) * CFC.abs T = T ∧ ‖(u : A) - 1‖ ≤ 2 * ‖T - 1‖ := by
  nontriviality A
  let t : Aˣ := Units.ofNearby 1 T (by simpa using hT)
  have ht : (t : A) = T := rfl
  simpa only [ht] using exists_polar_unitary_near_one_of_unit t (by rwa [ht])

end Ordered

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_BoundaryImprovement
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The quadratic step in boundary cocycle correction

Only the structural properties of the boundary mean occur here.  The mean
need not be normal.  Covariance cancellation and polar normalization give
the quadratic improvement used in the measurable iteration.
-/

namespace KadisonKastler

open scoped CStarAlgebra

noncomputable section

universe u v

variable {A : Type u} {B : Type v} [CStarAlgebra A] [CStarAlgebra B]

namespace BimoduleMean

variable {ι : B →⋆ₐ[ℂ] A} (m : BimoduleMean ι)

/-- Averaging preserves the error from a field independent of the mean variable. -/
theorem norm_sub_le (x : A) (b : B) {e : ℝ} (h : ‖x - ι b‖ ≤ e) :
    ‖m.toCLM x - b‖ ≤ e := by
  rw [← m.fixed b, ← map_sub]
  exact (m.norm_le _).trans h

end BimoduleMean

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_BoundaryIntertwiner
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedStarGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.boundedSequenceCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Averaging and polar normalization of a boundary intertwiner

A supplied equivariant bimodule mean gives a near-identity semilinear
intertwiner. Continuous functional calculus passes its transformation law
to the unitary polar factor.
-/

namespace KadisonKastler

open scoped CStarAlgebra BoundedContinuousFunction

noncomputable section

variable {B : Type*} [CStarAlgebra B]

attribute [local instance] OAI.KadisonKastler.boundaryIntertwinerOrder
attribute [local instance] OAI.KadisonKastler.boundaryIntertwinerStarOrder
/-- Left multiplication by a unitary does not change the absolute value. -/
theorem abs_unitary_mul (u : unitary B) (b : B) :
    CFC.abs ((u : B) * b) = CFC.abs b := by
  unfold CFC.abs
  congr 1
  rw [star_mul]
  calc
    star b * star (u : B) * ((u : B) * b) =
        star b * (star (u : B) * (u : B)) * b := by noncomm_ring
    _ = star b * b := by
      rw [Unitary.star_mul_self_of_mem u.property, mul_one]

/-- Right multiplication by a unitary conjugates the absolute value. -/
theorem abs_mul_unitary (b : B) (u : unitary B) :
    CFC.abs (b * (u : B)) = star (u : B) * CFC.abs b * (u : B) := by
  have hm := starAlgHom_map_abs
    (Unitary.conjStarAlgAut ℂ B (star u)).toStarAlgHom b
  have hr : CFC.abs (star (u : B) * b * (u : B)) = CFC.abs (b * (u : B)) := by
    rw [mul_assoc]
    exact abs_unitary_mul (star u) (b * (u : B))
  simpa only [StarAlgEquiv.toStarAlgHom_apply, Unitary.conjStarAlgAut_star_apply, hr]
    using hm.symm

/-- The absolute value satisfies the semilinear covariance forced by an
invertible intertwiner of unitaries. -/
theorem abs_semilinear_intertwines (a : B ≃⋆ₐ[ℂ] B) (b : B)
    (u v : unitary B) (hb : b * (u : B) = (v : B) * a b) :
    CFC.abs b * (u : B) = (u : B) * a (CFC.abs b) := by
  have hconj : star (u : B) * CFC.abs b * (u : B) = a (CFC.abs b) := by
    calc
      _ = CFC.abs (b * (u : B)) := (abs_mul_unitary b u).symm
      _ = CFC.abs ((v : B) * a b) := congrArg CFC.abs hb
      _ = CFC.abs (a b) := abs_unitary_mul v (a b)
      _ = a (CFC.abs b) := (starAlgHom_map_abs a.toStarAlgHom b).symm
  calc
    CFC.abs b * (u : B) =
        (u : B) * (star (u : B) * CFC.abs b * (u : B)) := by
      simp only [← mul_assoc, Unitary.mul_star_self_of_mem u.property, one_mul]
    _ = (u : B) * a (CFC.abs b) := by rw [hconj]

/-- An invertible semilinear intertwiner passes its law to its polar unitary. -/
theorem polar_unitary_semilinear_intertwines (a : B ≃⋆ₐ[ℂ] B) (b : B)
    (hunit : IsUnit b) (u v L : unitary B)
    (hb : b * (u : B) = (v : B) * a b)
    (hL : (L : B) * CFC.abs b = b) :
    (L : B) * (u : B) = (v : B) * a (L : B) := by
  have ha : IsUnit (CFC.abs b) := by
    obtain ⟨t, rfl⟩ := hunit
    exact isUnit_abs t
  have haa : IsUnit (a (CFC.abs b)) := ha.map a.toMonoidHom
  apply haa.mul_right_cancel
  calc
    ((L : B) * (u : B)) * a (CFC.abs b) =
        (L : B) * ((u : B) * a (CFC.abs b)) := mul_assoc _ _ _
    _ = (L : B) * (CFC.abs b * (u : B)) := by
      rw [abs_semilinear_intertwines a b u v hb]
    _ = b * (u : B) := by rw [← mul_assoc, hL]
    _ = (v : B) * a b := hb
    _ = ((v : B) * a (L : B)) * a (CFC.abs b) := by rw [mul_assoc, ← map_mul, hL]

variable {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]

attribute [local instance] OAI.KadisonKastler.boundaryIntertwinerFunctionCStar
/-- Averaging the genuine field `S_t U_t*` produces the semilinear intertwiner. -/
theorem averaged_boundary_intertwiner
    (α : G →* (B ≃⋆ₐ[ℂ] B))
    (m : BimoduleMean (boundaryConstant (G := G) (B := B)))
    (hm : ∀ g f, m.toCLM (boundaryTranslate α g f) = α g (m.toCLM f))
    (S : unitary (G →ᵇ B))
    (hS : ∀ g h, S.val g * α g (S.val h) = S.val (g * h))
    (U : G →* unitary B) (hU : ∀ g t, α g (U t : B) = (U t : B))
    {δ : ℝ} (hclose : ∀ g, ‖S.val g - (U g : B)‖ ≤ δ) :
    ∃ b : B, ‖b - 1‖ ≤ δ ∧
      ∀ g, b * (U g : B) = S.val g * α g b := by
  let H : unitary (G →ᵇ B) := S * star (boundedUnitaryFamily U)
  have hδ : 0 ≤ δ := (norm_nonneg _).trans (hclose 1)
  have hH : ‖(H : G →ᵇ B) - 1‖ ≤ δ := by
    apply (BoundedContinuousFunction.norm_le hδ).mpr
    intro t
    have heq : S.val t * star (U t : B) - 1 =
        (S.val t - (U t : B)) * star (U t : B) := by
      rw [sub_mul, Unitary.mul_star_self_of_mem (U t).property]
    change ‖S.val t * star (U t : B) - 1‖ ≤ δ
    rw [heq]
    simpa only [← Unitary.coe_star, CStarRing.norm_mul_coe_unitary] using hclose t
  have hfield (g : G) :
      boundaryConstant (G := G) (S.val g) * boundaryTranslate α g (H : G →ᵇ B) =
        (H : G →ᵇ B) * boundaryConstant (G := G) (U g : B) := by
    ext t
    have hUg : star (U (g⁻¹ * t)) = star (U t) * U g := by
      simp only [map_mul, map_inv, Unitary.star_eq_inv, mul_inv_rev, inv_inv]
    have hUgB : star (U (g⁻¹ * t) : B) = star (U t : B) * (U g : B) := by
      simpa only [Unitary.coe_star, Submonoid.coe_mul] using
        congrArg (fun w : unitary B => (w : B)) hUg
    have hc : S.val g * α g (S.val (g⁻¹ * t)) = S.val t := by
      simpa only [mul_inv_cancel_left] using hS g (g⁻¹ * t)
    change S.val g * α g (S.val (g⁻¹ * t) * star (U (g⁻¹ * t) : B)) =
      (S.val t * star (U t : B)) * (U g : B)
    rw [map_mul, map_star, hU, ← mul_assoc, hc, hUgB, mul_assoc]
  refine ⟨m.toCLM (H : G →ᵇ B), ?_, ?_⟩
  · apply m.norm_sub_le (H : G →ᵇ B) 1
    simpa only [map_one] using hH
  · intro g
    have he := congrArg m.toCLM (hfield g)
    rw [m.map_left, m.map_right, hm] at he
    exact he.symm

/-- The averaged boundary intertwiner has a near-identity unitary polar
factor satisfying the same semilinear intertwining equation. -/
theorem exists_unitary_boundary_intertwiner_oai
    (α : G →* (B ≃⋆ₐ[ℂ] B))
    (m : BimoduleMean (boundaryConstant (G := G) (B := B)))
    (hm : ∀ g f, m.toCLM (boundaryTranslate α g f) = α g (m.toCLM f))
    (S : unitary (G →ᵇ B))
    (hS : ∀ g h, S.val g * α g (S.val h) = S.val (g * h))
    (U : G →* unitary B) (hU : ∀ g t, α g (U t : B) = (U t : B))
    {δ : ℝ} (hδ : δ < 1) (hclose : ∀ g, ‖S.val g - (U g : B)‖ ≤ δ) :
    ∃ L : unitary B, (∀ g, (L : B) * (U g : B) = S.val g * α g (L : B)) ∧
      ‖(L : B) - 1‖ ≤ 2 * δ := by
  obtain ⟨b, hb, hbi⟩ := averaged_boundary_intertwiner α m hm S hS U hU hclose
  have hnear : ‖b - 1‖ < 1 := hb.trans_lt hδ
  have hunit : IsUnit b := by
    nontriviality B
    exact (Units.ofNearby 1 b (by simpa using hnear)).isUnit
  obtain ⟨L, hL, hLn⟩ := exists_polar_unitary_near_one b hnear
  refine ⟨L, ?_, hLn.trans (mul_le_mul_of_nonneg_left hb (by norm_num))⟩
  intro g
  exact polar_unitary_semilinear_intertwines (α g) b hunit (U g)
    (unitaryFamilyEval S g) L (hbi g) hL

end

end KadisonKastler

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.KadisonKastler.exists_unitary_boundary_intertwiner_oai.{u_1, u_2} := @OAI.KadisonKastler.exists_unitary_boundary_intertwiner_oai.{u_1, u_2}
