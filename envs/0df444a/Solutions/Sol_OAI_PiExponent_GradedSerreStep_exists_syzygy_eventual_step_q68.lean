-- Prove2me | solution 1 for OAI.PiExponent.GradedSerreStep.exists_syzygy_eventual_step_q68
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T09:09:15.783901+00:00
-- url     : https://prove2.me/submissions/7c1f400c-1394-463d-adbc-1d29528c0675

import Mathlib
import Definitions.Def_OAIQ068A025

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_ProjectiveMonomialCech
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.ProjectiveMonomialCohomology.degreeZero_finite _root_.OAI.PiExponent.ProjectiveMonomialCohomology.negativeCycles_finite _root_.OAI.PiExponent.ProjectiveMonomialFinite.allNegative_finite _root_.OAI.PiExponent.ProjectiveMonomialFinite.allNonnegative_finite _root_.OAI.PiExponent.ProjectiveMonomialFinite.monomial_subsingleton _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.ProjectiveMonomialCech

noncomputable section

open scoped BigOperators

variable {ι K : Type*} [Fintype ι] [AddCommGroup K]

theorem exists_nonnegative_coordinate [Nonempty ι] {d : ℤ}
    (hd : 0 ≤ d) (a : Monomial ι d) : ∃ i, 0 ≤ a.val i := by
  by_contra h
  have hneg : ∀ i, a.val i < 0 := fun i => lt_of_not_ge (fun hi => h ⟨i, hi⟩)
  have htotal : (∑ i, a.val i) < 0 :=
    Finset.sum_neg (fun i _ => hneg i) Finset.univ_nonempty
  rw [a.property] at htotal
  exact (not_lt_of_ge hd) htotal

end
end PiExponent.ProjectiveMonomialCech

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_ProjectiveMonomialCechHigher
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.ProjectiveMonomialCohomology.degreeZero_finite _root_.OAI.PiExponent.ProjectiveMonomialCohomology.negativeCycles_finite _root_.OAI.PiExponent.ProjectiveMonomialFinite.allNegative_finite _root_.OAI.PiExponent.ProjectiveMonomialFinite.allNonnegative_finite _root_.OAI.PiExponent.ProjectiveMonomialFinite.monomial_subsingleton _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.ProjectiveMonomialCechHigher

noncomputable section
open scoped BigOperators
open ProjectiveMonomialCech

variable {ι A K : Type*} [AddCommGroup A]

variable [Fintype ι] [AddCommGroup K]

theorem contraction_regular {d : ℤ} {q : ℕ} (pivot : Monomial ι d → ι)
    (hpivot : ∀ a : Monomial ι d, 0 ≤ a.val (pivot a))
    (c : Cochain ι (Laurent ι K d) (q + 1)) (hc : Regular c) :
    Regular (contraction pivot c) := by
  intro t a ha k hk
  obtain ⟨j, hj⟩ := hc (Fin.cons (pivot a) t) a ha k hk
  cases j using Fin.cases with
  | zero =>
      simp only [Fin.cons_zero] at hj
      rw [← hj] at hk
      exact False.elim ((not_lt_of_ge (hpivot a)) hk)
  | succ j => exact ⟨j, by simpa only [Fin.cons_succ] using hj⟩

theorem exact_of_pivot {d : ℤ} {q : ℕ} (pivot : Monomial ι d → ι)
    (hpivot : ∀ a : Monomial ι d, 0 ≤ a.val (pivot a))
    (c : Cochain ι (Laurent ι K d) (q + 1)) (hc : Regular c)
    (hcocycle : differential c = 0) :
    ∃ b : Cochain ι (Laurent ι K d) q, Regular b ∧ differential b = c := by
  refine ⟨contraction pivot c, contraction_regular pivot hpivot c hc, ?_⟩
  have h := contraction_identity pivot c
  rw [hcocycle] at h
  have hz : contraction pivot (0 : Cochain ι (Laurent ι K d) (q + 2)) = 0 := by
    funext t
    ext a
    rfl
  rw [hz, zero_add] at h
  exact h

theorem nonnegative_twist_cech_exact_all_positive {d : ℤ} (hd : 0 ≤ d) {q : ℕ}
    (c : Cochain ι (Laurent ι K d) (q + 1)) (hc : Regular c)
    (hcocycle : differential c = 0) :
    ∃ b : Cochain ι (Laurent ι K d) q, Regular b ∧ differential b = c := by
  classical
  cases isEmpty_or_nonempty ι with
  | inl h =>
      refine ⟨fun t => isEmptyElim (t 0), ?_, ?_⟩
      · intro t
        exact isEmptyElim (t 0)
      · funext t
        exact isEmptyElim (t 0)
  | inr h =>
      let pivot : Monomial ι d → ι :=
        fun a => Classical.choose (exists_nonnegative_coordinate hd a)
      have hpivot : ∀ a : Monomial ι d, 0 ≤ a.val (pivot a) :=
        fun a => Classical.choose_spec (exists_nonnegative_coordinate hd a)
      exact exact_of_pivot pivot hpivot c hc hcocycle

end
end PiExponent.ProjectiveMonomialCechHigher

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Polynomials_GradedSerre
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.ProjectiveMonomialCohomology.degreeZero_finite _root_.OAI.PiExponent.ProjectiveMonomialCohomology.negativeCycles_finite _root_.OAI.PiExponent.ProjectiveMonomialFinite.allNegative_finite _root_.OAI.PiExponent.ProjectiveMonomialFinite.allNonnegative_finite _root_.OAI.PiExponent.ProjectiveMonomialFinite.monomial_subsingleton _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.GradedSerre

noncomputable section
open scoped BigOperators

variable {R M ι σ : Type*} [Ring R] [AddCommGroup M] [Module R M]
  [DecidableEq ι] [SetLike σ M] [AddSubmonoidClass σ M]
  (𝓜 : ι → σ) [DirectSum.Decomposition 𝓜]

theorem span_homogeneous_eq (K : Submodule R M) (hK : K.IsHomogeneous 𝓜) :
    Submodule.span R {x : M | x ∈ K ∧ ∃ d, x ∈ 𝓜 d} = K := by
  classical
  apply le_antisymm
  · exact Submodule.span_le.mpr (fun x hx => hx.1)
  · intro x hx
    rw [← DirectSum.sum_support_decompose 𝓜 x]
    apply Submodule.sum_mem
    intro d hd
    exact Submodule.subset_span ⟨hK d hx, d, (DirectSum.decompose 𝓜 x d).property⟩

theorem exists_finite_homogeneous_generators (K : Submodule R M)
    (hK : K.IsHomogeneous 𝓜) (hfg : K.FG) :
    ∃ (s : Finset M) (degree : s → ι),
      (∀ j : s, j.val ∈ K ∧ j.val ∈ 𝓜 (degree j)) ∧
      Submodule.span R (s : Set M) = K := by
  classical
  have hspan := span_homogeneous_eq 𝓜 K hK
  have hfg' : (Submodule.span R {x : M | x ∈ K ∧ ∃ d, x ∈ 𝓜 d}).FG := by
    rwa [hspan]
  obtain ⟨s, hs, hspan'⟩ :=
    (Submodule.fg_span_iff_fg_span_finset_subset _).mp hfg'
  have hdegree : ∀ j : s, ∃ d, j.val ∈ K ∧ j.val ∈ 𝓜 d := by
    intro j
    obtain ⟨hj, d, hd⟩ := hs j.property
    exact ⟨d, hj, hd⟩
  choose degree hdegree using hdegree
  exact ⟨s, degree, hdegree, hspan'.symm.trans hspan⟩

section IntegerGrading
variable {A P σA σP : Type*} [Ring A] [AddCommGroup P] [Module A P]
  [SetLike σA A] [AddSubgroupClass σA A]
  [SetLike σP P] [AddSubgroupClass σP P]
  (𝒜 : ℤ → σA) (𝓟 : ℤ → σP)
  [DirectSum.Decomposition 𝒜] [DirectSum.Decomposition 𝓟]
  [SetLike.GradedSMul 𝒜 𝓟]

theorem decompose_smul_homogeneous {m : P} {w : ℤ} (hm : m ∈ 𝓟 w)
    (a : A) (d : ℤ) :
    (DirectSum.decompose 𝓟 (a • m) d : P) =
      (DirectSum.decompose 𝒜 a (d - w) : A) • m := by
  induction a using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp
  | homogeneous a =>
      rename_i k
      have ham : (a : A) • m ∈ 𝓟 (k + w) :=
        SetLike.GradedSMul.smul_mem a.property hm
      by_cases h : k + w = d
      · have hk : k = d - w := by omega
        rw [← h, DirectSum.decompose_of_mem_same 𝓟 ham]
        rw [show k + w - w = k by omega, DirectSum.decompose_of_mem_same 𝒜 a.property]
      · rw [DirectSum.decompose_of_mem_ne 𝓟 ham h,
          DirectSum.decompose_of_mem_ne 𝒜 a.property (by omega), zero_smul]
  | add a b ha hb =>
      simp only [add_smul, DirectSum.decompose_add, DirectSum.add_apply, AddMemClass.coe_add]
      rw [ha, hb]

theorem free_cover_degree_compatible {J : Type*} [Fintype J]
    (w : J → ℤ) (v : J → P) (hv : ∀ j, v j ∈ 𝓟 (w j))
    (d : ℤ) (a : J → A) :
    Fintype.linearCombination A v
        (DirectSum.decompose (ShiftedFreeGrading.piece 𝒜 w) a d : J → A) =
      (DirectSum.decompose 𝓟 (Fintype.linearCombination A v a) d : P) := by
  classical
  simp only [Fintype.linearCombination_apply, DirectSum.decompose_sum,
    DirectSum.sum_apply, AddSubmonoidClass.coe_finsetSum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [ShiftedFreeGrading.decompose_apply]
  exact (decompose_smul_homogeneous 𝒜 𝓟 (hv j) (a j) d).symm

theorem exists_graded_free_map (K : Submodule A P) (hK : K.IsHomogeneous 𝓟)
    (hfg : K.FG) :
    ∃ (n : ℕ) (w : Fin n → ℤ) (f : (Fin n → A) →ₗ[A] P),
      LinearMap.range f = K ∧
      ∀ d x, f (DirectSum.decompose (ShiftedFreeGrading.piece 𝒜 w) x d : Fin n → A) =
        (DirectSum.decompose 𝓟 (f x) d : P) := by
  classical
  obtain ⟨s, degree, hs, hspan⟩ := exists_finite_homogeneous_generators 𝓟 K hK hfg
  let e : s ≃ Fin s.card := s.equivFin
  let v : Fin s.card → P := fun j => (e.symm j).val
  let w : Fin s.card → ℤ := fun j => degree (e.symm j)
  refine ⟨s.card, w, Fintype.linearCombination A v, ?_, ?_⟩
  · rw [Fintype.range_linearCombination]
    have hv : Set.range v = (s : Set P) := by
      ext x
      constructor
      · rintro ⟨j, rfl⟩
        exact (e.symm j).property
      · intro hx
        refine ⟨e ⟨x, hx⟩, ?_⟩
        simp only [v, Equiv.symm_apply_apply]
    rw [hv]
    exact hspan
  · exact free_cover_degree_compatible 𝒜 𝓟 w v (fun j => (hs (e.symm j)).2)

end IntegerGrading

section FreeTwistCech
open ProjectiveMonomialCech ProjectiveMonomialCechHigher
variable {J C B : Type*} [Fintype J] [Fintype C] [AddCommGroup B]

theorem compatible_vertices_are_polynomial [Nonempty C] {d : ℤ} (hd : 0 ≤ d)
    (c : C → Laurent C B d) (hc : ∀ j, RegularOn {j} (c j))
    (heq : ∀ i j, c i = c j) :
    ∃ f : Laurent C B d, RegularOn ∅ f ∧ ∀ j, c j = f := by
  classical
  let p : C := Classical.choice inferInstance
  refine ⟨c p, ?_, fun j => heq j p⟩
  intro a ha k hk
  obtain ⟨j, hj⟩ := exists_nonnegative_coordinate hd a
  have hcoeff : c j a ≠ 0 := by rw [heq j p]; exact ha
  have hkj := hc j a hcoeff k hk
  have hkj' : k = j := hkj
  exact False.elim ((not_lt_of_ge hj) (hkj' ▸ hk))

end FreeTwistCech

end
end PiExponent.GradedSerre

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Polynomials_GradedLocalizationExact
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.GradedLocalizationExact

noncomputable section

variable {R M N P σR σM σN σP : Type*}
  [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]
  [SetLike σR R]
  [SetLike σM M] [AddSubgroupClass σM M]
  [SetLike σN N] [AddSubgroupClass σN N]
  [SetLike σP P] [AddSubgroupClass σP P]

theorem fraction_cancel (a : R) (m : M) (n k : ℕ) :
    fraction a (a ^ k • m) (n + k) = fraction a m n := by
  simpa only [fraction, powerDenominator_add, Submonoid.smul_def,
    powerDenominator_val] using
    LocalizedModule.mk_cancel_common_right (powerDenominator a n) (powerDenominator a k) m

variable (𝒜 : ℤ → σR) (𝓜 : ℤ → σM)
  [SetLike.GradedMonoid 𝒜] [SetLike.GradedSMul 𝒜 𝓜]
  (a : R) (e : ℤ) (ha : a ∈ 𝒜 e)

variable (𝓝 : ℤ → σN) [SetLike.GradedSMul 𝒜 𝓝]

section Decomposition
variable [DirectSum.Decomposition 𝓜] [DirectSum.Decomposition 𝓝]

theorem homogeneous_preimage (f : M →ₗ[R] N)
    (hf : ∀ i x, f (DirectSum.decompose 𝓜 x i : M) =
      (DirectSum.decompose 𝓝 (f x) i : N))
    {d : ℤ} {y : N} (hy : y ∈ 𝓝 d) (hrange : y ∈ LinearMap.range f) :
    ∃ x : M, x ∈ 𝓜 d ∧ f x = y := by
  obtain ⟨x, hx⟩ := hrange
  refine ⟨DirectSum.decompose 𝓜 x d, (DirectSum.decompose 𝓜 x d).property, ?_⟩
  rw [hf, hx, DirectSum.decompose_of_mem_same 𝓝 hy]

theorem pieceMap_surjective (d : ℤ) (f : M →ₗ[R] N)
    (hf : ∀ i x, f (DirectSum.decompose 𝓜 x i : M) =
      (DirectSum.decompose 𝓝 (f x) i : N)) (hsurj : Function.Surjective f) :
    Function.Surjective
      (pieceMap 𝒜 𝓜 a e ha 𝓝 d f (preserves_of_compatible 𝓜 𝓝 f hf)) := by
  intro z
  obtain ⟨n, y, hy, hz⟩ := z.property
  obtain ⟨x, hx, hxy⟩ := homogeneous_preimage 𝓜 𝓝 f hf hy (hsurj y)
  refine ⟨⟨fraction a x n, n, x, hx, rfl⟩, ?_⟩
  apply Subtype.ext
  change localizedMap a f (fraction a x n) = z.val
  rw [localizedMap_fraction, hxy, ← hz]

variable (𝓟 : ℤ → σP) [SetLike.GradedSMul 𝒜 𝓟] [DirectSum.Decomposition 𝓟]

theorem pieceMap_exact (d : ℤ) (f : M →ₗ[R] N) (g : N →ₗ[R] P)
    (hf : ∀ i x, f (DirectSum.decompose 𝓜 x i : M) =
      (DirectSum.decompose 𝓝 (f x) i : N))
    (hg : ∀ i x, g (DirectSum.decompose 𝓝 x i : N) =
      (DirectSum.decompose 𝓟 (g x) i : P))
    (hex : Function.Exact f g) :
    Function.Exact
      (pieceMap 𝒜 𝓜 a e ha 𝓝 d f (preserves_of_compatible 𝓜 𝓝 f hf))
      (pieceMap 𝒜 𝓝 a e ha 𝓟 d g (preserves_of_compatible 𝓝 𝓟 g hg)) := by
  intro z
  constructor
  · intro hz
    obtain ⟨n, y, hy, hzy⟩ := z.property
    have hzero : localizedMap a g z.val = 0 := congrArg Subtype.val hz
    rw [hzy, localizedMap_fraction, fraction_eq_zero] at hzero
    obtain ⟨k, hk⟩ := hzero
    have hclear : g (a ^ k • y) = 0 := by rw [map_smul, hk]
    have hy' : a ^ k • y ∈ 𝓝 (d + ((n + k : ℕ) : ℤ) * e) := by
      have h := power_smul_mem 𝒜 𝓝 a e ha hy k
      convert h using 1
      all_goals try with_reducible_and_instances rfl
      push_cast
      ring_nf
    obtain ⟨x, hx, hxy⟩ := homogeneous_preimage 𝓜 𝓝 f hf hy' ((hex _).mp hclear)
    refine ⟨⟨fraction a x (n + k), n + k, x, hx, rfl⟩, ?_⟩
    apply Subtype.ext
    change localizedMap a f (fraction a x (n + k)) = z.val
    rw [localizedMap_fraction, hxy, fraction_cancel, ← hzy]
  · rintro ⟨x, rfl⟩
    apply Subtype.ext
    obtain ⟨n, y, hy, hxy⟩ := x.property
    change localizedMap a g (localizedMap a f x.val) = 0
    rw [hxy, localizedMap_fraction, localizedMap_fraction,
      hex.apply_apply_eq_zero, fraction_zero]

end Decomposition

end
end PiExponent.GradedLocalizationExact

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_GradedCech
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.ProjectiveMonomialCohomology.degreeZero_finite _root_.OAI.PiExponent.ProjectiveMonomialCohomology.negativeCycles_finite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.GradedCech
noncomputable section
open scoped BigOperators
open GradedLocalizationExact

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

theorem restriction_refl (a : R) : restriction (M := M) a a dvd_rfl = LinearMap.id := by
  apply IsLocalizedModule.ext (Submonoid.powers a)
    (LocalizedModule.mkLinearMap (Submonoid.powers a) M)
    (divisor_powers_isUnit a a dvd_rfl)
  apply LinearMap.ext
  intro m
  exact restriction_mk_one a a dvd_rfl m

theorem restriction_comp (a b c : R) (hab : a ∣ b) (hbc : b ∣ c) :
    (restriction b c hbc).comp (restriction (M := M) a b hab) =
      restriction a c (hab.trans hbc) := by
  apply IsLocalizedModule.ext (Submonoid.powers a)
    (LocalizedModule.mkLinearMap (Submonoid.powers a) M)
    (divisor_powers_isUnit a c (hab.trans hbc))
  apply LinearMap.ext
  intro m
  simp only [LinearMap.comp_apply, LocalizedModule.mkLinearMap_apply, restriction_mk_one]

theorem restriction_localizedMap {N : Type*} [AddCommGroup N] [Module R N]
    (a c : R) (hac : a ∣ c) (f : M →ₗ[R] N) :
    (localizedMap c f).comp (restriction (M := M) a c hac) =
      (restriction (M := N) a c hac).comp (localizedMap a f) := by
  apply IsLocalizedModule.ext (Submonoid.powers a)
    (LocalizedModule.mkLinearMap (Submonoid.powers a) M)
    (divisor_powers_isUnit (M := N) a c hac)
  apply LinearMap.ext
  intro m
  simp only [LinearMap.comp_apply, LocalizedModule.mkLinearMap_apply]
  rw [show LocalizedModule.mk m (1 : Submonoid.powers a) = fraction a m 0 by
    simp only [fraction, powerDenominator_zero]]
  rw [restriction_fraction_zero, localizedMap_fraction,
    localizedMap_fraction, restriction_fraction_zero]

variable {σR σM : Type*} [SetLike σR R]
  [SetLike σM M] [AddSubgroupClass σM M]
  (𝒜 : ℤ → σR) (𝓜 : ℤ → σM)
  [SetLike.GradedMonoid 𝒜] [SetLike.GradedSMul 𝒜 𝓜]

section Cover
variable {J : Type*} [DecidableEq J] (x : J → R) (hx : ∀ j, x j ∈ 𝒜 1)

@[simp] theorem setRestriction_refl (s : Finset J) (d : ℤ)
    (z : IntersectionPiece 𝒜 𝓜 x hx s d) : setRestriction 𝒜 𝓜 x hx (s := s) le_rfl d z = z := by
  apply Subtype.ext
  rw [setRestriction_coe, restriction_refl]
  rfl

theorem setRestriction_comp {s t u : Finset J} (hst : s ⊆ t) (htu : t ⊆ u)
    (d : ℤ) (z : IntersectionPiece 𝒜 𝓜 x hx s d) :
    setRestriction 𝒜 𝓜 x hx htu d (setRestriction 𝒜 𝓜 x hx hst d z) =
      setRestriction 𝒜 𝓜 x hx (hst.trans htu) d z := by
  apply Subtype.ext
  simp only [setRestriction_coe]
  exact DFunLike.congr_fun (restriction_comp (coverProduct x s) (coverProduct x t)
    (coverProduct x u) (coverProduct_dvd 𝒜 x hx hst) (coverProduct_dvd 𝒜 x hx htu)) z.val

theorem differential_sub (d : ℤ) {q : ℕ} (c b : Cochain 𝒜 𝓜 x hx d q) :
    differential 𝒜 𝓜 x hx d (c - b) = differential 𝒜 𝓜 x hx d c - differential 𝒜 𝓜 x hx d b := by
  funext t
  simp only [differential, Pi.sub_apply, map_sub, smul_sub, Finset.sum_sub_distrib]

theorem evaluate_differential (d : ℤ) {L : Type*} (s : Finset J) (f : L → J)
    (hf : ∀ l, f l ∈ s) {q : ℕ} (c : Cochain 𝒜 𝓜 x hx d q) :
    evaluate 𝒜 𝓜 x hx d s f hf (differential 𝒜 𝓜 x hx d c) =
      ProjectiveMonomialCechHigher.differential (evaluate 𝒜 𝓜 x hx d s f hf c) := by
  funext t
  simp only [evaluate, differential, ProjectiveMonomialCechHigher.differential,
    map_sum, map_zsmul, setRestriction_comp]
  rfl

theorem differential_squared (d : ℤ) {q : ℕ} (c : Cochain 𝒜 𝓜 x hx d q) :
    differential 𝒜 𝓜 x hx d (differential 𝒜 𝓜 x hx d c) = 0 := by
  funext t
  have ht : ∀ i, t i ∈ tupleSet t := fun i =>
    Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  have h := congrFun (ProjectiveMonomialCechHigher.differential_squared
    (evaluate 𝒜 𝓜 x hx d (tupleSet t) t ht c)) id
  rw [← evaluate_differential, ← evaluate_differential] at h
  change setRestriction 𝒜 𝓜 x hx le_rfl d
    (differential 𝒜 𝓜 x hx d (differential 𝒜 𝓜 x hx d c) t) = 0 at h
  simpa only [setRestriction_refl, Pi.zero_apply] using h

section Maps
variable {N σN : Type*} [AddCommGroup N] [Module R N]
  [SetLike σN N] [AddSubgroupClass σN N]
  (𝓝 : ℤ → σN) [SetLike.GradedSMul 𝒜 𝓝]
  (f : M →ₗ[R] N) (hf : ∀ i m, m ∈ 𝓜 i → f m ∈ 𝓝 i)

theorem pieceMap_setRestriction {s t : Finset J} (hst : s ⊆ t) (d : ℤ)
    (z : IntersectionPiece 𝒜 𝓜 x hx s d) :
    pieceMap 𝒜 𝓜 (coverProduct x t) _ (coverProduct_mem 𝒜 x hx t) 𝓝 d f hf
        (setRestriction 𝒜 𝓜 x hx hst d z) =
      setRestriction 𝒜 𝓝 x hx hst d
        (pieceMap 𝒜 𝓜 (coverProduct x s) _ (coverProduct_mem 𝒜 x hx s) 𝓝 d f hf z) := by
  apply Subtype.ext
  simp only [pieceMap_coe, setRestriction_coe]
  exact DFunLike.congr_fun (restriction_localizedMap (coverProduct x s) (coverProduct x t)
    (coverProduct_dvd 𝒜 x hx hst) f) z.val

theorem cochainMap_differential (d : ℤ) {q : ℕ} (c : Cochain 𝒜 𝓜 x hx d q) :
    cochainMap 𝒜 𝓜 x hx 𝓝 f hf d (q + 1) (differential 𝒜 𝓜 x hx d c) =
      differential 𝒜 𝓝 x hx d (cochainMap 𝒜 𝓜 x hx 𝓝 f hf d q c) := by
  funext t
  simp only [cochainMap, AddMonoidHom.coe_mk, ZeroHom.coe_mk, differential,
    map_sum, map_zsmul, pieceMap_setRestriction]

theorem cochainMap_injective (d : ℤ) (q : ℕ) (hinj : Function.Injective f) :
    Function.Injective (cochainMap 𝒜 𝓜 x hx 𝓝 f hf d q) := by
  intro c b h
  funext t
  apply Subtype.ext
  have ht := congrArg Subtype.val (congrFun h t)
  exact (IsLocalizedModule.map_injective (Submonoid.powers (coverProduct x (tupleSet t)))
    (LocalizedModule.mkLinearMap _ M) (LocalizedModule.mkLinearMap _ N) f hinj) ht

theorem augmentation_natural (d : ℤ) (m : 𝓜 d) :
    cochainMap 𝒜 𝓜 x hx 𝓝 f hf d 0 (augmentation 𝒜 𝓜 x hx d m) =
      augmentation 𝒜 𝓝 x hx d (globalPieceMap 𝓜 𝓝 f hf d m) := by
  funext t
  apply Subtype.ext
  change localizedMap (coverProduct x (tupleSet t)) f
      (fraction (coverProduct x (tupleSet t)) (m : M) 0) =
    fraction (coverProduct x (tupleSet t)) (f m) 0
  exact localizedMap_fraction _ f m 0

end Maps

section Exactness
variable {N P σN σP : Type*} [AddCommGroup N] [Module R N]
  [AddCommGroup P] [Module R P]
  [SetLike σN N] [AddSubgroupClass σN N]
  [SetLike σP P] [AddSubgroupClass σP P]
  (𝓝 : ℤ → σN) (𝓟 : ℤ → σP)
  [SetLike.GradedSMul 𝒜 𝓝] [SetLike.GradedSMul 𝒜 𝓟]
  [DirectSum.Decomposition 𝓜] [DirectSum.Decomposition 𝓝] [DirectSum.Decomposition 𝓟]

theorem cochainMap_surjective (d : ℤ) (q : ℕ) (f : M →ₗ[R] N)
    (hf : ∀ i z, f (DirectSum.decompose 𝓜 z i : M) =
      (DirectSum.decompose 𝓝 (f z) i : N)) (hsurj : Function.Surjective f) :
    Function.Surjective (cochainMap 𝒜 𝓜 x hx 𝓝 f
      (preserves_of_compatible 𝓜 𝓝 f hf) d q) := by
  intro c
  have ht (t : Fin (q + 1) → J) := pieceMap_surjective 𝒜 𝓜
    (coverProduct x (tupleSet t)) _ (coverProduct_mem 𝒜 x hx (tupleSet t))
    𝓝 d f hf hsurj (c t)
  choose b hb using ht
  exact ⟨b, funext hb⟩

theorem cochainMap_exact (d : ℤ) (q : ℕ) (f : M →ₗ[R] N) (g : N →ₗ[R] P)
    (hf : ∀ i z, f (DirectSum.decompose 𝓜 z i : M) =
      (DirectSum.decompose 𝓝 (f z) i : N))
    (hg : ∀ i z, g (DirectSum.decompose 𝓝 z i : N) =
      (DirectSum.decompose 𝓟 (g z) i : P)) (hex : Function.Exact f g) :
    Function.Exact
      (cochainMap 𝒜 𝓜 x hx 𝓝 f (preserves_of_compatible 𝓜 𝓝 f hf) d q)
      (cochainMap 𝒜 𝓝 x hx 𝓟 g (preserves_of_compatible 𝓝 𝓟 g hg) d q) := by
  intro c
  have hlocal (t : Fin (q + 1) → J) := pieceMap_exact 𝒜 𝓜
    (coverProduct x (tupleSet t)) _ (coverProduct_mem 𝒜 x hx (tupleSet t))
    𝓝 𝓟 d f g hf hg hex
  constructor
  · intro hc
    have ht (t : Fin (q + 1) → J) := (hlocal t (c t)).mp (congrFun hc t)
    choose b hb using ht
    exact ⟨b, funext hb⟩
  · rintro ⟨b, rfl⟩
    funext t
    exact (hlocal t).apply_apply_eq_zero (b t)

end Exactness

end Cover

end
end PiExponent.GradedCech

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_GradedCechRecovery
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.GradedCechRecovery

theorem augmentation_surjective_on_closed
    {P M A₀ A₁ A₂ B₀ B₁ B₂ C₀ C₁ : Type*}
    [AddCommGroup P] [AddCommGroup M]
    [AddCommGroup A₀] [AddCommGroup A₁] [AddCommGroup A₂]
    [AddCommGroup B₀] [AddCommGroup B₁] [AddCommGroup B₂]
    [AddCommGroup C₀] [AddCommGroup C₁]
    (a₀ : A₀ →+ A₁) (a₁ : A₁ →+ A₂)
    (b₀ : B₀ →+ B₁) (b₁ : B₁ →+ B₂) (c₀ : C₀ →+ C₁)
    (f₀ : A₀ →+ B₀) (f₁ : A₁ →+ B₁) (f₂ : A₂ →+ B₂)
    (g₀ : B₀ →+ C₀) (g₁ : B₁ →+ C₁)
    (εB : P →+ B₀) (εC : M →+ C₀) (g : P →+ M)
    (hg₀ : Function.Surjective g₀)
    (hker : ∀ z : B₁, g₁ z = 0 → ∃ y : A₁, f₁ y = z)
    (hf₂ : Function.Injective f₂)
    (hff₀ : ∀ x, b₀ (f₀ x) = f₁ (a₀ x))
    (hff₁ : ∀ x, b₁ (f₁ x) = f₂ (a₁ x))
    (hgg : ∀ x, g₁ (b₀ x) = c₀ (g₀ x))
    (hzero : ∀ x, g₀ (f₀ x) = 0)
    (hdiff : ∀ x, b₁ (b₀ x) = 0)
    (hε : ∀ x, εC (g x) = g₀ (εB x))
    (hfree : ∀ x : B₀, b₀ x = 0 → ∃ p : P, εB p = x)
    (hkernel : ∀ x : A₁, a₁ x = 0 → ∃ y : A₀, a₀ y = x) :
    ∀ x : C₀, c₀ x = 0 → ∃ m : M, εC m = x := by
  intro x hx
  obtain ⟨b, hb⟩ := hg₀ x
  have hdb : g₁ (b₀ b) = 0 := by rw [hgg, hb, hx]
  obtain ⟨a, ha⟩ := hker (b₀ b) hdb
  have hclosed : a₁ a = 0 := by
    apply hf₂
    rw [map_zero, ← hff₁, ha, hdiff]
  obtain ⟨v, hv⟩ := hkernel a hclosed
  have hcorrected : b₀ (b - f₀ v) = 0 := by
    rw [map_sub, hff₀, hv, ha, sub_self]
  obtain ⟨p, hp⟩ := hfree (b - f₀ v) hcorrected
  refine ⟨g p, ?_⟩
  rw [hε, hp, map_sub, hzero, sub_zero, hb]

end PiExponent.GradedCechRecovery

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Polynomials_HomogeneousSubmoduleGrading
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.HomogeneousSubmoduleGrading
noncomputable section
open DirectSum
variable {R M σM : Type*} [Ring R] [AddCommGroup M] [Module R M]
  [SetLike σM M] [AddSubgroupClass σM M]
  (𝓜 : ℤ → σM) [DirectSum.Decomposition 𝓜]
  (K : Submodule R M) (hK : K.IsHomogeneous 𝓜)

theorem subtype_degree_compatible (d : ℤ) (m : K) :
    K.subtype (DirectSum.decompose (piece 𝓜 K hK) m d : K) =
      (DirectSum.decompose 𝓜 (K.subtype m) d : M) := rfl

end
end PiExponent.HomogeneousSubmoduleGrading

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_GradedCechExactness
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.GradedCechExactness
noncomputable section
open PiExponent.GradedCech PiExponent.GradedLocalizationExact
variable {R K F M σR σK σF σM J : Type*} [CommRing R]
  [AddCommGroup K] [Module R K] [AddCommGroup F] [Module R F]
  [AddCommGroup M] [Module R M]
  [SetLike σR R]
  [SetLike σK K] [AddSubgroupClass σK K]
  [SetLike σF F] [AddSubgroupClass σF F]
  [SetLike σM M] [AddSubgroupClass σM M]
  (𝒜 : ℤ → σR) (𝓚 : ℤ → σK) (𝓕 : ℤ → σF) (𝓜 : ℤ → σM)
  [SetLike.GradedMonoid 𝒜] [SetLike.GradedSMul 𝒜 𝓚]
  [SetLike.GradedSMul 𝒜 𝓕] [SetLike.GradedSMul 𝒜 𝓜]
  [DirectSum.Decomposition 𝓚] [DirectSum.Decomposition 𝓕] [DirectSum.Decomposition 𝓜]
  [DecidableEq J] (x : J → R) (hx : ∀ j, x j ∈ 𝒜 1)
  (f : K →ₗ[R] F) (g : F →ₗ[R] M)
  (hf : ∀ i z, f (DirectSum.decompose 𝓚 z i : K) =
    (DirectSum.decompose 𝓕 (f z) i : F))
  (hg : ∀ i z, g (DirectSum.decompose 𝓕 z i : F) =
    (DirectSum.decompose 𝓜 (g z) i : M))
  (hinj : Function.Injective f) (hex : Function.Exact f g) (hsurj : Function.Surjective g)

include hf hg hinj hex hsurj in

theorem augmentation_recovery_of_shortExact (d : ℤ)
    (hfree : ∀ c : Cochain 𝒜 𝓕 x hx d 0,
      differential 𝒜 𝓕 x hx d c = 0 → ∃ p : 𝓕 d, augmentation 𝒜 𝓕 x hx d p = c)
    (hkernel : ∀ c : Cochain 𝒜 𝓚 x hx d 1,
      differential 𝒜 𝓚 x hx d c = 0 → ∃ b : Cochain 𝒜 𝓚 x hx d 0,
        differential 𝒜 𝓚 x hx d b = c) :
    ∀ c : Cochain 𝒜 𝓜 x hx d 0,
      differential 𝒜 𝓜 x hx d c = 0 → ∃ m : 𝓜 d, augmentation 𝒜 𝓜 x hx d m = c := by
  let pf := preserves_of_compatible 𝓚 𝓕 f hf
  let pg := preserves_of_compatible 𝓕 𝓜 g hg
  apply GradedCechRecovery.augmentation_surjective_on_closed
    (differentialHom 𝒜 𝓚 x hx d 0) (differentialHom 𝒜 𝓚 x hx d 1)
    (differentialHom 𝒜 𝓕 x hx d 0) (differentialHom 𝒜 𝓕 x hx d 1)
    (differentialHom 𝒜 𝓜 x hx d 0)
    (cochainMap 𝒜 𝓚 x hx 𝓕 f pf d 0) (cochainMap 𝒜 𝓚 x hx 𝓕 f pf d 1)
    (cochainMap 𝒜 𝓚 x hx 𝓕 f pf d 2)
    (cochainMap 𝒜 𝓕 x hx 𝓜 g pg d 0) (cochainMap 𝒜 𝓕 x hx 𝓜 g pg d 1)
    (augmentation 𝒜 𝓕 x hx d) (augmentation 𝒜 𝓜 x hx d)
    (globalPieceMap 𝓕 𝓜 g pg d)
  · exact cochainMap_surjective 𝒜 𝓕 x hx 𝓜 d 0 g hg hsurj
  · intro c hc
    exact (cochainMap_exact 𝒜 𝓚 x hx 𝓕 𝓜 d 1 f g hf hg hex c).mp hc
  · exact cochainMap_injective 𝒜 𝓚 x hx 𝓕 f pf d 2 hinj
  · intro c
    exact (cochainMap_differential 𝒜 𝓚 x hx 𝓕 f pf d c).symm
  · intro c
    exact (cochainMap_differential 𝒜 𝓚 x hx 𝓕 f pf d c).symm
  · intro c
    exact cochainMap_differential 𝒜 𝓕 x hx 𝓜 g pg d c
  · intro c
    exact (cochainMap_exact 𝒜 𝓚 x hx 𝓕 𝓜 d 0 f g hf hg hex).apply_apply_eq_zero c
  · exact differential_squared 𝒜 𝓕 x hx d
  · intro p
    exact (augmentation_natural 𝒜 𝓕 x hx 𝓜 g pg d p).symm
  · exact hfree
  · exact hkernel

include hf hg hinj hex hsurj in

theorem primitives_of_shortExact (d : ℤ) (q : ℕ)
    (hfree : ∀ c : Cochain 𝒜 𝓕 x hx d (q + 1),
      differential 𝒜 𝓕 x hx d c = 0 → ∃ b : Cochain 𝒜 𝓕 x hx d q,
        differential 𝒜 𝓕 x hx d b = c)
    (hkernel : ∀ c : Cochain 𝒜 𝓚 x hx d (q + 1 + 1),
      differential 𝒜 𝓚 x hx d c = 0 → ∃ b : Cochain 𝒜 𝓚 x hx d (q + 1),
        differential 𝒜 𝓚 x hx d b = c) :
    ∀ c : Cochain 𝒜 𝓜 x hx d (q + 1),
      differential 𝒜 𝓜 x hx d c = 0 → ∃ b : Cochain 𝒜 𝓜 x hx d q,
        differential 𝒜 𝓜 x hx d b = c := by
  let pf := preserves_of_compatible 𝓚 𝓕 f hf
  let pg := preserves_of_compatible 𝓕 𝓜 g hg
  intro c hc
  obtain ⟨b, hb⟩ := cochainMap_surjective 𝒜 𝓕 x hx 𝓜 d (q + 1) g hg hsurj c
  have hdb : cochainMap 𝒜 𝓕 x hx 𝓜 g pg d (q + 1 + 1)
      (differential 𝒜 𝓕 x hx d b) = 0 := by
    rw [cochainMap_differential, hb, hc]
  obtain ⟨a, ha⟩ := (cochainMap_exact 𝒜 𝓚 x hx 𝓕 𝓜 d (q + 1 + 1)
    f g hf hg hex (differential 𝒜 𝓕 x hx d b)).mp hdb
  have hclosed : differential 𝒜 𝓚 x hx d a = 0 := by
    apply cochainMap_injective 𝒜 𝓚 x hx 𝓕 f pf d (q + 1 + 1 + 1) hinj
    rw [map_zero, cochainMap_differential, ha, differential_squared]
  obtain ⟨v, hv⟩ := hkernel a hclosed
  have hcorrected : differential 𝒜 𝓕 x hx d
      (b - cochainMap 𝒜 𝓚 x hx 𝓕 f pf d (q + 1) v) = 0 := by
    rw [differential_sub, ← cochainMap_differential, hv, ha, sub_self]
  obtain ⟨p, hp⟩ := hfree _ hcorrected
  refine ⟨cochainMap 𝒜 𝓕 x hx 𝓜 g pg d q p, ?_⟩
  rw [← cochainMap_differential, hp, map_sub,
    (cochainMap_exact 𝒜 𝓚 x hx 𝓕 𝓜 d (q + 1) f g hf hg hex).apply_apply_eq_zero,
    sub_zero, hb]

end
end PiExponent.GradedCechExactness

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_GradedH0
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.ProjectiveMonomialCohomology.degreeZero_finite _root_.OAI.PiExponent.ProjectiveMonomialCohomology.negativeCycles_finite _root_.OAI.PiExponent.ProjectiveMonomialFinite.allNegative_finite _root_.OAI.PiExponent.ProjectiveMonomialFinite.allNonnegative_finite _root_.OAI.PiExponent.ProjectiveMonomialFinite.monomial_subsingleton _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.GradedH0
noncomputable section
open scoped BigOperators
open ProjectiveMonomialCech
variable {ι R : Type*} [Fintype ι] [CommRing R]

theorem zeroth_cocycle_vertices_eq {d : ℤ}
    (c : ProjectiveMonomialCechHigher.Cochain ι (Laurent ι R d) 0)
    (hc : ProjectiveMonomialCechHigher.differential c = 0) (i j : ι) :
    c (fun _ => i) = c (fun _ => j) := by
  have h := congrFun hc (![i, j] : Fin 2 → ι)
  simp only [ProjectiveMonomialCechHigher.differential, Fin.sum_univ_succ,
    Fin.val_zero, pow_zero, one_zsmul, Fin.val_succ, Fin.sum_univ_zero,
    add_zero, Nat.zero_add, pow_one, neg_one_zsmul, Pi.zero_apply] at h
  have hi : (![i, j] : Fin 2 → ι) ∘ (0 : Fin 2).succAbove = (fun _ => j) := by
    funext k
    fin_cases k
    rfl
  have hj : (![i, j] : Fin 2 → ι) ∘ (Fin.succ (0 : Fin 1)).succAbove = (fun _ => i) := by
    funext k
    fin_cases k
    rfl
  rw [hi, hj] at h
  exact (eq_of_sub_eq_zero (by simpa only [sub_eq_add_neg] using h)).symm

end
end PiExponent.GradedH0

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_GradedPolynomialLaurent
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.ProjectiveMonomialCohomology.degreeZero_finite _root_.OAI.PiExponent.ProjectiveMonomialCohomology.negativeCycles_finite _root_.OAI.PiExponent.ProjectiveMonomialFinite.allNegative_finite _root_.OAI.PiExponent.ProjectiveMonomialFinite.allNonnegative_finite _root_.OAI.PiExponent.ProjectiveMonomialFinite.monomial_subsingleton _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.GradedPolynomialLaurent
noncomputable section
open scoped BigOperators
open PiExponent.GradedCech PiExponent.GradedLocalizationExact PiExponent.ProjectiveMonomialCech
attribute [local instance] Classical.propDecidable MvPolynomial.weightedGradedAlgebra
variable {J R : Type*} [CommRing R]

theorem polynomialToGroupAlgebra_injective :
    Function.Injective (polynomialToGroupAlgebra (J := J) (R := R)) := by
  apply AddMonoidAlgebra.mapDomain_injective
  intro a b hab
  ext j
  exact Int.natCast_inj.mp (congrFun hab j)

theorem ringLocalizationMap_injective (s : Finset J) :
    Function.Injective (ringLocalizationMap (R := R) s) := by
  apply (IsLocalization.injective_iff_map_algebraMap_eq
    (Submonoid.powers (product (R := R) s)) (ringLocalizationMap s)).mpr
  intro p q
  constructor
  · exact congrArg _
  · intro h
    rw [ringLocalizationMap_base, ringLocalizationMap_base] at h
    exact congrArg _ (polynomialToGroupAlgebra_injective h)

theorem moduleToGroupAlgebra_injective (s : Finset J) :
    Function.Injective (moduleToGroupAlgebra (R := R) s) :=
  (ringLocalizationMap_injective s).comp (moduleRingEquiv s).injective

variable [Fintype J]

omit [Fintype J] in
theorem natExponentHom_injective : Function.Injective (natExponentHom (J := J)) := by
  intro a b hab
  ext j
  exact Int.natCast_inj.mp (congrFun hab j)

omit [Fintype J] in
@[simp] theorem polynomialToGroupAlgebra_coefficient (p : MvPolynomial J R) (b : J →₀ ℕ) :
    (polynomialToGroupAlgebra p).coeff (natExponentHom b) = p.coeff b :=
  Finsupp.mapDomain_apply natExponentHom_injective (AddMonoidAlgebra.coeff p) b

theorem polynomialToGroupAlgebra_support {d : ℤ} (p : MvPolynomial J R)
    (hp : p.IsWeightedHomogeneous (1 : J → ℤ) d) (a : J → ℤ)
    (ha : (polynomialToGroupAlgebra p).coeff a ≠ 0) :
    (∑ j, a j = d) ∧ ∀ j, 0 ≤ a j := by
  obtain ⟨b, rfl⟩ := Finsupp.mem_range_of_mapDomain_ne_zero ha
  rw [polynomialToGroupAlgebra_coefficient] at ha
  constructor
  · simpa only [Finsupp.weight_eq_sum, Pi.one_apply, nsmul_eq_mul, mul_one,
      natExponentHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk] using hp ha
  · intro j
    exact Int.natCast_nonneg _

theorem piece_support (s : Finset J) (d : ℤ) (z : Piece (R := R) s d)
    (a : J → ℤ) (ha : (moduleToGroupAlgebra s z.val).coeff a ≠ 0) :
    (∑ j, a j = d) ∧ ∀ j, j ∉ s → 0 ≤ a j := by
  obtain ⟨n, p, hp, hz⟩ := z.property
  rw [hz, moduleToGroupAlgebra_fraction_coefficient] at ha
  obtain ⟨hd, hn⟩ := polynomialToGroupAlgebra_support p hp _ ha
  constructor
  · simp only [Pi.add_apply, Finset.sum_add_distrib,
      sum_productExponent, nsmul_eq_mul, Pi.mul_apply, Pi.natCast_apply, ← Finset.mul_sum] at hd
    omega
  · intro j hj
    simpa only [Pi.add_apply, Pi.smul_apply, productExponent_apply, ite_eq_right hj,
      smul_zero, add_zero] using hn j

theorem pieceToLaurent_regular (s : Finset J) (d : ℤ) (z : Piece (R := R) s d) :
    RegularOn (s : Set J) (pieceToLaurent s d z) := by
  intro a ha j hj
  by_contra hjs
  exact (not_lt_of_ge ((piece_support s d z a.val ha).2 j hjs)) hj

theorem pieceToLaurent_injective (s : Finset J) (d : ℤ) :
    Function.Injective (pieceToLaurent (R := R) s d) := by
  intro z w h
  apply Subtype.ext
  apply moduleToGroupAlgebra_injective s
  ext a
  by_cases ha : ∑ j, a j = d
  · exact congrArg (fun l : Laurent J R d => l ⟨a, ha⟩) h
  · have hz : (moduleToGroupAlgebra s z.val).coeff a = 0 := by
      by_contra hz
      exact ha (piece_support s d z a hz).1
    have hw : (moduleToGroupAlgebra s w.val).coeff a = 0 := by
      by_contra hw
      exact ha (piece_support s d w a hw).1
    rw [hz, hw]

theorem exists_cleared_exponent (s : Finset J) (a : J → ℤ)
    (ha : ∀ j, j ∉ s → 0 ≤ a j) :
    ∃ (n : ℕ) (b : J →₀ ℕ), natExponentHom b = a + n • productExponent s := by
  classical
  let n : ℕ := ∑ j, (-a j).toNat
  have hnn : ∀ j, 0 ≤ a j + (n : ℤ) := by
    intro j
    have hn : (-a j).toNat ≤ n :=
      Finset.single_le_sum (fun k _ => Nat.zero_le ((-a k).toNat)) (Finset.mem_univ j)
    have hn' : ((-a j).toNat : ℤ) ≤ (n : ℤ) := by exact_mod_cast hn
    omega
  have hnonneg : ∀ j, 0 ≤ (a + n • productExponent s) j := by
    intro j
    by_cases hj : j ∈ s
    · simpa [Pi.add_apply, Pi.smul_apply, nsmul_eq_mul, productExponent_apply, hj] using hnn j
    · simpa only [Pi.add_apply, Pi.smul_apply, productExponent_apply, ite_eq_right hj,
        smul_zero, add_zero] using ha j hj
  refine ⟨n, Finsupp.equivFunOnFinite.symm (fun j => ((a + n • productExponent s) j).toNat), ?_⟩
  funext j
  exact Int.toNat_of_nonneg (hnonneg j)

theorem single_in_piece_range (s : Finset J) (d : ℤ) (a : Monomial J d) (r : R)
    (ha : ∀ j, j ∉ s → 0 ≤ a.val j) :
    ∃ z : Piece (R := R) s d, pieceToLaurent s d z = Finsupp.single a r := by
  classical
  obtain ⟨n, b, hb⟩ := exists_cleared_exponent s a.val ha
  have hdeg : Finsupp.weight (1 : J → ℤ) b = d + (n : ℤ) * (s.card : ℤ) := by
    simp only [Finsupp.weight_eq_sum, Pi.one_apply, nsmul_eq_mul, mul_one]
    change (∑ j, natExponentHom b j) = _
    rw [hb]
    simp only [Pi.add_apply, Finset.sum_add_distrib,
      sum_productExponent, nsmul_eq_mul, Pi.mul_apply, Pi.natCast_apply, ← Finset.mul_sum, a.property]
  let z : Piece (R := R) s d := ⟨fraction (product s) (MvPolynomial.monomial b r) n,
    n, MvPolynomial.monomial b r, MvPolynomial.isWeightedHomogeneous_monomial _ b r hdeg, rfl⟩
  have hz : moduleToGroupAlgebra s z.val = AddMonoidAlgebra.single a.val r := by
    change moduleToGroupAlgebra s (fraction (product s) (MvPolynomial.monomial b r) n) = _
    rw [moduleToGroupAlgebra_fraction]
    change AddMonoidAlgebra.mapDomain _ (AddMonoidAlgebra.single b r) * _ = _
    rw [AddMonoidAlgebra.mapDomain_single, AddMonoidAlgebra.single_mul_single, hb]
    simp
  refine ⟨z, ?_⟩
  ext a'
  rw [pieceToLaurent_coefficient, hz]
  simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
  congr 1
  exact propext Subtype.val_inj

theorem pieceToLaurent_surjective_regular (s : Finset J) (d : ℤ) (p : Laurent J R d)
    (hp : RegularOn (s : Set J) p) :
    ∃ z : Piece (R := R) s d, pieceToLaurent s d z = p := by
  classical
  have hs : ∀ a ∈ p.support, ∃ z : Piece (R := R) s d,
      pieceToLaurent s d z = Finsupp.single a (p a) := by
    intro a ha
    apply single_in_piece_range
    intro j hj
    by_contra hn
    exact hj (hp a (Finsupp.mem_support_iff.mp ha) j (lt_of_not_ge hn))
  choose z hz using hs
  refine ⟨∑ a ∈ p.support, if h : a ∈ p.support then z a h else 0, ?_⟩
  rw [map_sum]
  calc
    _ = ∑ a ∈ p.support, Finsupp.single a (p a) := by
      apply Finset.sum_congr rfl
      intro a ha
      simp only [dite_eq_left ha, hz]
    _ = p := p.sum_single

omit [Fintype J] in
theorem moduleToGroupAlgebra_smul (s : Finset J) (p : MvPolynomial J R)
    (z : LocalizedModule (Submonoid.powers (product (R := R) s)) (MvPolynomial J R)) :
    moduleToGroupAlgebra s (p • z) = polynomialToGroupAlgebra p * moduleToGroupAlgebra s z := by
  change ringLocalizationMap s (moduleRingEquiv s (p • z)) =
    polynomialToGroupAlgebra p * ringLocalizationMap s (moduleRingEquiv s z)
  rw [map_smul, Algebra.smul_def, map_mul, ringLocalizationMap_base]

omit [Fintype J] in
theorem moduleToGroupAlgebra_restriction (s t : Finset J)
    (hst : product (R := R) s ∣ product t)
    (z : LocalizedModule (Submonoid.powers (product (R := R) s)) (MvPolynomial J R)) :
    moduleToGroupAlgebra t (restriction (product s) (product t) hst z) =
      moduleToGroupAlgebra s z := by
  induction z using LocalizedModule.induction_on with
  | _ p den =>
    obtain ⟨n, hn⟩ := den.property
    have hden : den = powerDenominator (product (R := R) s) n := Subtype.ext hn.symm
    subst den
    change moduleToGroupAlgebra t (restriction (product s) (product t) hst
      (fraction (product s) p n)) = moduleToGroupAlgebra s (fraction (product s) p n)
    apply ((product_isUnit (R := R) s).pow n).mul_left_cancel
    rw [← map_pow, ← moduleToGroupAlgebra_smul, ← moduleToGroupAlgebra_smul,
      ← map_smul, power_smul_fraction, restriction_fraction_zero]
    simp only [moduleToGroupAlgebra_fraction, zero_smul, neg_zero]

theorem pieceToLaurent_restriction [DecidableEq J] {s t : Finset J} (hst : s ⊆ t)
    (d : ℤ) (z : Piece (R := R) s d) :
    pieceToLaurent t d (setRestriction grading grading MvPolynomial.X variable_mem hst d z) =
      pieceToLaurent s d z := by
  ext a
  change (moduleToGroupAlgebra t (restriction (product s) (product t)
    (coverProduct_dvd grading MvPolynomial.X variable_mem hst) z.val)).coeff a.val =
    (moduleToGroupAlgebra s z.val).coeff a.val
  exact congrArg (fun l : GroupAlgebra (J := J) (R := R) => l.coeff a.val)
    (moduleToGroupAlgebra_restriction s t
      (coverProduct_dvd grading MvPolynomial.X variable_mem hst) z.val)

end
end PiExponent.GradedPolynomialLaurent

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_GradedPolynomialCech
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.ProjectiveMonomialCohomology.degreeZero_finite _root_.OAI.PiExponent.ProjectiveMonomialCohomology.negativeCycles_finite _root_.OAI.PiExponent.ProjectiveMonomialFinite.allNegative_finite _root_.OAI.PiExponent.ProjectiveMonomialFinite.allNonnegative_finite _root_.OAI.PiExponent.ProjectiveMonomialFinite.monomial_subsingleton _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.GradedPolynomialCech
noncomputable section
open scoped BigOperators
open PiExponent.GradedLocalizationExact PiExponent.GradedCech PiExponent.GradedPolynomialLaurent PiExponent.ProjectiveMonomialCech
attribute [local instance] MvPolynomial.weightedGradedAlgebra
variable {J R : Type*} [Fintype J] [DecidableEq J] [CommRing R]

theorem cochainToLaurent_injective (d : ℤ) (q : ℕ) :
    Function.Injective (cochainToLaurent (J := J) (R := R) d q) := by
  intro c b h
  funext t
  exact pieceToLaurent_injective (tupleSet t) d (congrFun h t)

theorem cochainToLaurent_regular (d : ℤ) (q : ℕ)
    (c : Cochain (grading (J := J) (R := R)) (grading (J := J) (R := R)) MvPolynomial.X variable_mem d q) :
    ProjectiveMonomialCechHigher.Regular (cochainToLaurent d q c) := by
  intro t a ha j hj
  have h := pieceToLaurent_regular (tupleSet t) d (c t) a ha j hj
  obtain ⟨k, _, hk⟩ := Finset.mem_image.mp h
  exact ⟨k, hk⟩

theorem cochainToLaurent_surjective_regular (d : ℤ) (q : ℕ)
    (c : ProjectiveMonomialCechHigher.Cochain J (Laurent J R d) q)
    (hc : ProjectiveMonomialCechHigher.Regular c) :
    ∃ b, cochainToLaurent d q b = c := by
  have ht (t : Fin (q + 1) → J) : ∃ b : Piece (R := R) (tupleSet t) d,
      pieceToLaurent (tupleSet t) d b = c t := by
    apply pieceToLaurent_surjective_regular
    intro a ha j hj
    obtain ⟨k, hk⟩ := hc t a ha j hj
    exact Finset.mem_image.mpr ⟨k, Finset.mem_univ _, hk⟩
  choose b hb using ht
  exact ⟨b, funext hb⟩

theorem cochainToLaurent_differential (d : ℤ) (q : ℕ)
    (c : Cochain (grading (J := J) (R := R)) (grading (J := J) (R := R)) MvPolynomial.X variable_mem d q) :
    cochainToLaurent d (q + 1) (differential (grading (J := J) (R := R)) (grading (J := J) (R := R)) MvPolynomial.X variable_mem d c) =
      ProjectiveMonomialCechHigher.differential (cochainToLaurent d q c) := by
  funext t
  change intersectionToLaurent (tupleSet t) d
      (∑ k : Fin (q + 2), (-1 : ℤ) ^ k.val •
        setRestriction (grading (J := J) (R := R)) (grading (J := J) (R := R))
          MvPolynomial.X variable_mem (tupleSet_comp_subset t k.succAbove) d (c (t ∘ k.succAbove))) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [map_zsmul]
  apply congrArg (fun z : Laurent J R d => (-1 : ℤ) ^ k.val • z)
  exact pieceToLaurent_restriction (R := R) (tupleSet_comp_subset t k.succAbove) d
    ⟨(c (t ∘ k.succAbove)).val, (c (t ∘ k.succAbove)).property⟩

theorem nonnegative_polynomial_cech_exact (d : ℤ) (hd : 0 ≤ d) (q : ℕ)
    (c : Cochain (grading (J := J) (R := R)) (grading (J := J) (R := R)) MvPolynomial.X variable_mem d (q + 1))
    (hc : differential (grading (J := J) (R := R)) (grading (J := J) (R := R)) MvPolynomial.X variable_mem d c = 0) :
    ∃ b : Cochain (grading (J := J) (R := R)) (grading (J := J) (R := R)) MvPolynomial.X variable_mem d q,
      differential (grading (J := J) (R := R)) (grading (J := J) (R := R)) MvPolynomial.X variable_mem d b = c := by
  have hclosed : ProjectiveMonomialCechHigher.differential (cochainToLaurent d (q + 1) c) = 0 := by
    rw [← cochainToLaurent_differential, hc, map_zero]
  obtain ⟨b, hb, hdb⟩ := ProjectiveMonomialCechHigher.nonnegative_twist_cech_exact_all_positive
    hd (cochainToLaurent d (q + 1) c) (cochainToLaurent_regular d (q + 1) c) hclosed
  obtain ⟨a, ha⟩ := cochainToLaurent_surjective_regular d q b hb
  refine ⟨a, ?_⟩
  apply cochainToLaurent_injective d (q + 1)
  rw [cochainToLaurent_differential, ha, hdb]

theorem nonnegative_polynomial_augmentation_recovery (d : ℤ) (hd : 0 ≤ d)
    (c : Cochain (grading (J := J) (R := R)) (grading (J := J) (R := R)) (MvPolynomial.X : J → MvPolynomial J R)
      variable_mem d 0)
    (hc : differential (grading (J := J) (R := R)) (grading (J := J) (R := R)) MvPolynomial.X variable_mem d c = 0) :
    ∃ m : (grading (J := J) (R := R)) d,
      augmentation (grading (J := J) (R := R)) (grading (J := J) (R := R)) MvPolynomial.X variable_mem d m = c := by
  classical
  cases isEmpty_or_nonempty J with
  | inl h =>
      refine ⟨0, ?_⟩
      funext t
      exact isEmptyElim (t 0)
  | inr h =>
      have hclosed : ProjectiveMonomialCechHigher.differential (cochainToLaurent d 0 c) = 0 := by
        rw [← cochainToLaurent_differential, hc, map_zero]
      have hreg (j : J) : RegularOn {j} (cochainToLaurent d 0 c (fun _ => j)) := by
        simpa only [Set.range_const] using cochainToLaurent_regular d 0 c (fun _ => j)
      obtain ⟨p, hpreg, hp⟩ := GradedSerre.compatible_vertices_are_polynomial hd
        (fun j => cochainToLaurent d 0 c (fun _ => j)) hreg
        (GradedH0.zeroth_cocycle_vertices_eq _ hclosed)
      obtain ⟨z, hzL⟩ := pieceToLaurent_surjective_regular (R := R) ∅ d p (by simpa using hpreg)
      obtain ⟨n, m, hm, hz⟩ := z.property
      have hm' : m ∈ (grading (J := J) (R := R)) d := by simpa using hm
      refine ⟨⟨m, hm'⟩, ?_⟩
      funext t
      apply pieceToLaurent_injective (tupleSet t) d
      have ht : t = fun _ => t 0 := by
        funext i
        exact congrArg t (show i = 0 by omega)
      calc
        _ = pieceToLaurent ∅ d z := by
          ext a
          change (moduleToGroupAlgebra (tupleSet t) (fraction (product (tupleSet t)) m 0)).coeff a.val =
            (moduleToGroupAlgebra ∅ z.val).coeff a.val
          rw [hz]
          simp only [moduleToGroupAlgebra_fraction_coefficient, zero_smul,
            productExponent, Finset.sum_empty, smul_zero, add_zero]
        _ = p := hzL
        _ = pieceToLaurent (tupleSet t) d (c t) := by
          change p = cochainToLaurent d 0 c t
          rw [ht, hp]

end
end PiExponent.GradedPolynomialCech

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Polynomials_GradedLocalizationFree
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.GradedLocalizationFree

noncomputable section
open scoped BigOperators
open GradedLocalizationExact

variable {R J σR : Type*} [CommRing R] [Fintype J]
  [SetLike σR R] [AddSubgroupClass σR R]

theorem coordinateMap_injective (a : R) : Function.Injective (coordinateMap (J := J) a) := by
  classical
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm ?_ bot_le
  intro z hz
  change coordinateMap a z = 0 at hz
  change z = 0
  induction z using LocalizedModule.induction_on with
  | _ v s =>
    obtain ⟨n, hn⟩ := s.property
    have hs : s = powerDenominator a n := Subtype.ext hn.symm
    subst s
    change coordinateMap a (fraction a v n) = 0 at hz
    have hcoord : ∀ j, ∃ k : ℕ, a ^ k • v j = 0 := by
      intro j
      apply (fraction_eq_zero a (v j) n).mp
      have h := congrFun hz j
      simpa only [coordinateMap_fraction, Pi.zero_apply] using h
    choose k hk using hcoord
    let K : ℕ := ∑ j, k j
    apply (fraction_eq_zero a v n).mpr
    refine ⟨K, ?_⟩
    funext j
    have hj : k j ≤ K := Finset.single_le_sum (fun i _ => Nat.zero_le (k i))
      (Finset.mem_univ j)
    change a ^ K • v j = 0
    calc
      a ^ K • v j = (a ^ (K - k j) * a ^ k j) • v j := by
        rw [← pow_add, Nat.sub_add_cancel hj]
      _ = 0 := by rw [mul_smul, hk j, smul_zero]

variable (𝒜 : ℤ → σR) [SetLike.GradedMonoid 𝒜]
  (w : J → ℤ) (a : R) (e : ℤ) (ha : a ∈ 𝒜 e) (d : ℤ)

theorem coordinatePieces_injective : Function.Injective (coordinatePieces 𝒜 w a e ha d) := by
  intro z z' h
  apply Subtype.ext
  apply coordinateMap_injective a
  funext j
  exact congrArg Subtype.val (congrFun h j)

theorem coordinatePieces_surjective : Function.Surjective (coordinatePieces 𝒜 w a e ha d) := by
  classical
  intro z
  have hz : ∀ j, ∃ (n : ℕ) (m : R),
      m ∈ 𝒜 (d - w j + (n : ℤ) * e) ∧ (z j).val = fraction a m n :=
    fun j => (z j).property
  choose n m hm hzm using hz
  let N : ℕ := ∑ j, n j
  have hn (j : J) : n j ≤ N := Finset.single_le_sum
    (fun i _ => Nat.zero_le (n i)) (Finset.mem_univ j)
  let v : J → R := fun j => a ^ (N - n j) • m j
  have hv : v ∈ ShiftedFreeGrading.piece 𝒜 w (d + (N : ℤ) * e) := by
    intro j
    have h := power_smul_mem 𝒜 𝒜 a e ha (hm j) (N - n j)
    change v j ∈ 𝒜 (d + (N : ℤ) * e - w j)
    dsimp only [v]
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    rw [Nat.cast_sub (hn j)]
    ring_nf
  refine ⟨⟨fraction a v N, N, v, hv, rfl⟩, ?_⟩
  funext j
  apply Subtype.ext
  change coordinateMap a (fraction a v N) j = (z j).val
  rw [coordinateMap_fraction, hzm]
  change fraction a (a ^ (N - n j) • m j) N = fraction a (m j) (n j)
  have hc := fraction_cancel a (m j) (n j) (N - n j)
  simpa only [Nat.add_sub_of_le (hn j)] using hc

end
end PiExponent.GradedLocalizationFree

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_GradedFreeCech
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.GradedFreeCech
noncomputable section
open PiExponent.GradedCech PiExponent.GradedLocalizationFree
open PiExponent.GradedPolynomialLaurent PiExponent.GradedLocalizationExact
attribute [local instance] MvPolynomial.weightedGradedAlgebra
variable {J R B : Type*} [DecidableEq J] [CommRing R] [Fintype B]
  (w : B → ℤ)

theorem coordinateCochain_injective (d : ℤ) (q : ℕ) :
    Function.Injective (coordinateCochain (J := J) (R := R) w d q) := by
  intro c e h
  funext t
  apply coordinatePieces_injective (grading (J := J) (R := R)) w (product (tupleSet t)) _ (product_mem _) d
  funext b
  exact congrFun (congrFun h b) t

theorem coordinateCochain_surjective (d : ℤ) (q : ℕ) :
    Function.Surjective (coordinateCochain (J := J) (R := R) w d q) := by
  intro c
  have ht (t : Fin (q + 1) → J) := coordinatePieces_surjective (grading (J := J) (R := R)) w
    (product (R := R) (tupleSet t)) _ (product_mem _) d (fun b => c b t)
  choose e he using ht
  refine ⟨e, ?_⟩
  funext b t
  exact congrFun (he t) b

theorem coordinate_restriction {s t : Finset J} (hst : s ⊆ t) (d : ℤ)
    (z : IntersectionPiece (grading (J := J) (R := R)) (ShiftedFreeGrading.piece (grading (J := J) (R := R)) w)
      MvPolynomial.X variable_mem s d) (b : B) :
    coordinatePieces (grading (J := J) (R := R)) w (product t) _ (product_mem _) d
      (setRestriction (grading (J := J) (R := R)) (ShiftedFreeGrading.piece (grading (J := J) (R := R)) w)
        MvPolynomial.X variable_mem hst d z) b =
      setRestriction (grading (J := J) (R := R)) (grading (J := J) (R := R)) MvPolynomial.X variable_mem hst (d - w b)
        (coordinatePieces (grading (J := J) (R := R)) w (product s) _ (product_mem _) d z b) := by
  apply Subtype.ext
  change localizedMap (product t) (LinearMap.proj b)
      (restriction (product s) (product t)
        (coverProduct_dvd (grading (J := J) (R := R)) MvPolynomial.X variable_mem hst) z.val) =
    restriction (product s) (product t)
      (coverProduct_dvd (grading (J := J) (R := R)) MvPolynomial.X variable_mem hst) (localizedMap (product s) (LinearMap.proj b) z.val)
  exact DFunLike.congr_fun (restriction_localizedMap (product s) (product t)
    (coverProduct_dvd (grading (J := J) (R := R)) MvPolynomial.X variable_mem hst) (LinearMap.proj b)) z.val

theorem coordinateCochain_differential (d : ℤ) (q : ℕ)
    (c : Cochain (grading (J := J) (R := R)) (ShiftedFreeGrading.piece (grading (J := J) (R := R)) w)
      (MvPolynomial.X : J → MvPolynomial J R) variable_mem d q) (b : B) :
    coordinateCochain w d (q + 1)
        (differential (grading (J := J) (R := R)) (ShiftedFreeGrading.piece (grading (J := J) (R := R)) w) MvPolynomial.X variable_mem d c) b =
      differential (grading (J := J) (R := R)) (grading (J := J) (R := R)) MvPolynomial.X variable_mem (d - w b)
        (coordinateCochain w d q c b) := by
  funext t
  change (coordinateIntersection w (tupleSet t) d
    (∑ k : Fin (q + 2), (-1 : ℤ) ^ k.val •
      setRestriction (grading (J := J) (R := R)) (ShiftedFreeGrading.piece (grading (J := J) (R := R)) w)
        MvPolynomial.X variable_mem (tupleSet_comp_subset t k.succAbove) d (c (t ∘ k.succAbove)))) b = _
  rw [map_sum]
  simp only [Finset.sum_apply, differential]
  apply Finset.sum_congr rfl
  intro k _
  rw [map_zsmul]
  change (-1 : ℤ) ^ k.val • coordinateIntersection w (tupleSet t) d
      (setRestriction (grading (J := J) (R := R)) (ShiftedFreeGrading.piece (grading (J := J) (R := R)) w)
        MvPolynomial.X variable_mem (tupleSet_comp_subset t k.succAbove) d (c (t ∘ k.succAbove))) b = _
  apply congrArg (fun z => (-1 : ℤ) ^ k.val • z)
  exact coordinate_restriction w (tupleSet_comp_subset t k.succAbove) d (c (t ∘ k.succAbove)) b

variable [Fintype J]

theorem free_cech_exact (d : ℤ) (hd : ∀ b, 0 ≤ d - w b) (q : ℕ)
    (c : Cochain (grading (J := J) (R := R)) (ShiftedFreeGrading.piece (grading (J := J) (R := R)) w)
      (MvPolynomial.X : J → MvPolynomial J R) variable_mem d (q + 1))
    (hc : differential (grading (J := J) (R := R)) (ShiftedFreeGrading.piece (grading (J := J) (R := R)) w)
      MvPolynomial.X variable_mem d c = 0) :
    ∃ a : Cochain (grading (J := J) (R := R)) (ShiftedFreeGrading.piece (grading (J := J) (R := R)) w)
      MvPolynomial.X variable_mem d q,
      differential (grading (J := J) (R := R)) (ShiftedFreeGrading.piece (grading (J := J) (R := R)) w) MvPolynomial.X variable_mem d a = c := by
  have hclosed (b : B) : differential (grading (J := J) (R := R)) (grading (J := J) (R := R)) MvPolynomial.X variable_mem (d - w b)
      (coordinateCochain w d (q + 1) c b) = 0 := by
    rw [← coordinateCochain_differential, hc, map_zero]
    rfl
  have hpr (b : B) := GradedPolynomialCech.nonnegative_polynomial_cech_exact
    (d - w b) (hd b) q (coordinateCochain w d (q + 1) c b) (hclosed b)
  choose p hp using hpr
  obtain ⟨a, ha⟩ := coordinateCochain_surjective (J := J) (R := R) w d q p
  refine ⟨a, ?_⟩
  apply coordinateCochain_injective w d (q + 1)
  funext b
  rw [coordinateCochain_differential, ha, hp]

omit [Fintype J] in
theorem coordinateCochain_augmentation (d : ℤ)
    (m : ShiftedFreeGrading.piece (grading (J := J) (R := R)) w d) (b : B) :
    coordinateCochain w d 0
      (augmentation (grading (J := J) (R := R)) (ShiftedFreeGrading.piece (grading (J := J) (R := R)) w)
        MvPolynomial.X variable_mem d m) b =
    augmentation (grading (J := J) (R := R)) (grading (J := J) (R := R))
      MvPolynomial.X variable_mem (d - w b) ⟨m.val b, m.property b⟩ := by
  funext t
  apply Subtype.ext
  change coordinateMap (product (tupleSet t)) (fraction (product (tupleSet t)) m.val 0) b =
    fraction (product (tupleSet t)) (m.val b) 0
  exact coordinateMap_fraction _ m.val 0 b

theorem free_augmentation_recovery (d : ℤ) (hd : ∀ b, 0 ≤ d - w b)
    (c : Cochain (grading (J := J) (R := R)) (ShiftedFreeGrading.piece (grading (J := J) (R := R)) w)
      MvPolynomial.X variable_mem d 0)
    (hc : differential (grading (J := J) (R := R)) (ShiftedFreeGrading.piece (grading (J := J) (R := R)) w)
      MvPolynomial.X variable_mem d c = 0) :
    ∃ m : ShiftedFreeGrading.piece (grading (J := J) (R := R)) w d,
      augmentation (grading (J := J) (R := R)) (ShiftedFreeGrading.piece (grading (J := J) (R := R)) w)
        MvPolynomial.X variable_mem d m = c := by
  have hclosed (b : B) : differential (grading (J := J) (R := R)) (grading (J := J) (R := R))
      MvPolynomial.X variable_mem (d - w b) (coordinateCochain w d 0 c b) = 0 := by
    rw [← coordinateCochain_differential, hc, map_zero]
    rfl
  have hrec (b : B) := GradedPolynomialCech.nonnegative_polynomial_augmentation_recovery
    (d - w b) (hd b) (coordinateCochain w d 0 c b) (hclosed b)
  choose m hm using hrec
  refine ⟨⟨fun b => (m b).val, fun b => (m b).property⟩, ?_⟩
  apply coordinateCochain_injective w d 0
  funext b
  rw [coordinateCochain_augmentation]
  exact hm b

end
end PiExponent.GradedFreeCech

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Polynomials_GradedSerreStep
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.GradedSerreStep
noncomputable section
open PiExponent.GradedCech PiExponent.GradedPolynomialLaurent
attribute [local instance] MvPolynomial.weightedGradedAlgebra
variable {J R M σM : Type*} [Fintype J] [DecidableEq J] [CommRing R]
  [IsNoetherianRing R] [AddCommGroup M] [Module (MvPolynomial J R) M]
  [Module.Finite (MvPolynomial J R) M] [SetLike σM M] [AddSubgroupClass σM M]
  (𝓜 : ℤ → σM) [DirectSum.Decomposition 𝓜]
  [SetLike.GradedSMul (grading (J := J) (R := R)) 𝓜]

omit [IsNoetherianRing R] in
theorem exists_syzygy_eventual_step_q68_oai :
    ∃ (rank : ℕ) (w : Fin rank → ℤ) (g : (Fin rank → MvPolynomial J R) →ₗ[MvPolynomial J R] M),
      ∃ (hg : ∀ d z, g (DirectSum.decompose (ShiftedFreeGrading.piece (grading (J := J) (R := R)) w) z d :
          Fin rank → MvPolynomial J R) = (DirectSum.decompose 𝓜 (g z) d : M)),
        Function.Surjective g ∧
        let hK := GradedSerre.kernel_homogeneous (ShiftedFreeGrading.piece (grading (J := J) (R := R)) w) 𝓜 g hg
        let 𝓚 := HomogeneousSubmoduleGrading.piece (ShiftedFreeGrading.piece (grading (J := J) (R := R)) w) g.ker hK
        ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
          (HasPrimitive (J := J) (R := R) 𝓚 n 0 → HasRecovery (J := J) (R := R) 𝓜 n) ∧
          ∀ q : ℕ, HasPrimitive (J := J) (R := R) 𝓚 n (q + 1) → HasPrimitive (J := J) (R := R) 𝓜 n q := by
  obtain ⟨rank, w, g, hrange, hg⟩ := GradedSerre.exists_graded_free_map
    (grading (J := J) (R := R)) 𝓜 (⊤ : Submodule (MvPolynomial J R) M)
    (fun _ _ _ => trivial) Module.Finite.fg_top
  have hsurj : Function.Surjective g := LinearMap.range_eq_top.mp hrange
  refine ⟨rank, w, g, hg, hsurj, ?_⟩
  let 𝓕 := ShiftedFreeGrading.piece (grading (J := J) (R := R)) w
  let hK := GradedSerre.kernel_homogeneous 𝓕 𝓜 g hg
  let 𝓚 := HomogeneousSubmoduleGrading.piece 𝓕 g.ker hK
  change ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    (HasPrimitive (J := J) (R := R) 𝓚 n 0 → HasRecovery (J := J) (R := R) 𝓜 n) ∧
    ∀ q : ℕ, HasPrimitive (J := J) (R := R) 𝓚 n (q + 1) → HasPrimitive (J := J) (R := R) 𝓜 n q
  refine ⟨∑ b, (w b).toNat, ?_⟩
  intro n hn
  have hdeg (b : Fin rank) : 0 ≤ (n : ℤ) - w b := by
    have hb : (w b).toNat ≤ ∑ b, (w b).toNat :=
      Finset.single_le_sum (fun b _ => Nat.zero_le ((w b).toNat)) (Finset.mem_univ b)
    have hb' : ((w b).toNat : ℤ) ≤ (n : ℤ) := by exact_mod_cast hb.trans hn
    omega
  have hf : ∀ d z, g.ker.subtype (DirectSum.decompose 𝓚 z d : g.ker) =
      (DirectSum.decompose 𝓕 (g.ker.subtype z) d : Fin rank → MvPolynomial J R) :=
    HomogeneousSubmoduleGrading.subtype_degree_compatible 𝓕 g.ker hK
  constructor
  · intro hk
    exact GradedCechExactness.augmentation_recovery_of_shortExact
      (grading (J := J) (R := R)) 𝓚 𝓕 𝓜 MvPolynomial.X variable_mem
      g.ker.subtype g hf hg Subtype.val_injective (LinearMap.exact_subtype_ker_map g) hsurj n
      (GradedFreeCech.free_augmentation_recovery w n hdeg) hk
  · intro q hk
    exact GradedCechExactness.primitives_of_shortExact
      (grading (J := J) (R := R)) 𝓚 𝓕 𝓜 MvPolynomial.X variable_mem
      g.ker.subtype g hf hg Subtype.val_injective (LinearMap.exact_subtype_ker_map g) hsurj n q
      (GradedFreeCech.free_cech_exact w n hdeg q) hk

end
end PiExponent.GradedSerreStep

end OAI
end

theorem solution.{u_1, u_2, u_3, u_4} : type_of% @OAI.PiExponent.GradedSerreStep.exists_syzygy_eventual_step_q68_oai.{u_1, u_2, u_3, u_4} := @OAI.PiExponent.GradedSerreStep.exists_syzygy_eventual_step_q68_oai.{u_1, u_2, u_3, u_4}
