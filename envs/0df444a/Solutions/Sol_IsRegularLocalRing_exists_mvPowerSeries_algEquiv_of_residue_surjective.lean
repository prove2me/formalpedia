-- Prove2me | solution 1 for IsRegularLocalRing.exists_mvPowerSeries_algEquiv_of_residue_surjective
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-11-16T17:16:42.916097+00:00
-- url     : https://prove2.me/submissions/6fca695a-3021-476b-8211-172cdddeec0e

import Mathlib

universe u v w

section

set_option autoImplicit false
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
noncomputable section

open IsLocalRing

namespace PhilipponCompleteLocalPowerSeriesPresentation

variable (K : Type u) [CommRing K] (A : Type v) [CommRing A] [Algebra K A]

/-- Evaluate a finite set of formal parameters in a complete adic algebra.
The coefficients may lie in a separate universe. -/
theorem exists_map (I : Ideal A) [IsAdicComplete I A]
    {σ : Type w} [Finite σ] (a : σ → A) (ha : ∀ i, a i ∈ I) :
    ∃ f : MvPowerSeries σ K →+* A,
      (∀ c : K, f (MvPowerSeries.C c) = algebraMap K A c) ∧
      (∀ i : σ, f (MvPowerSeries.X i) = a i) := by
  letI : UniformSpace K := ⊥
  letI : WithIdeal A := ⟨I⟩
  have hcomplete : CompleteSpace A ∧ T2Space A :=
    (IsAdic.isAdicComplete_iff (I := I) rfl).mp inferInstance
  letI : CompleteSpace A := hcomplete.1
  letI : T2Space A := hcomplete.2
  have hcont : Continuous (algebraMap K A) := continuous_of_discreteTopology
  have heval : MvPowerSeries.HasEval a := by
    constructor
    · intro i
      exact WithIdeal.isTopologicallyNilpotent_of_mem (ha i)
    · simp only [Filter.cofinite_eq_bot]
      exact Filter.tendsto_bot
  refine ⟨MvPowerSeries.eval₂Hom hcont heval, ?_, ?_⟩
  · intro c
    simp [MvPowerSeries.coe_eval₂Hom]
  · intro i
    simp [MvPowerSeries.coe_eval₂Hom]

/-- Parameters generating the maximal ideal give a surjection whenever
the coefficient map is surjective on the residue field. -/
theorem surjective [IsLocalRing A] [IsAdicComplete (maximalIdeal A) A]
    (hres : Function.Surjective ((residue A).comp (algebraMap K A)))
    {σ : Type w} [Finite σ] (a : σ → A)
    (ha : Ideal.span (Set.range a) = maximalIdeal A)
    (f : MvPowerSeries σ K →+* A)
    (hC : ∀ c : K, f (MvPowerSeries.C c) = algebraMap K A c)
    (hX : ∀ i : σ, f (MvPowerSeries.X i) = a i) :
    Function.Surjective f := by
  let J : Ideal (MvPowerSeries σ K) := Ideal.span (Set.range MvPowerSeries.X)
  have hmap : J.map f = maximalIdeal A := by
    change (Ideal.span (Set.range MvPowerSeries.X)).map f = _
    rw [Ideal.map_span, ← Set.range_comp]
    simpa only [Function.comp_def, hX] using ha
  letI : IsHausdorff (J.map f) A := hmap ▸ inferInstance
  apply surjective_of_mk_map_comp_surjective (I := J) f
  intro q
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective q
  obtain ⟨c, hc⟩ := hres (residue A z)
  refine ⟨MvPowerSeries.C c, ?_⟩
  change Ideal.Quotient.mk (J.map f) (f (MvPowerSeries.C c)) =
    Ideal.Quotient.mk (J.map f) z
  rw [hC, Ideal.Quotient.eq, hmap]
  exact Ideal.Quotient.eq.mp hc

theorem exists_surjective [IsLocalRing A] [IsAdicComplete (maximalIdeal A) A]
    (hres : Function.Surjective ((residue A).comp (algebraMap K A)))
    {σ : Type w} [Finite σ] (a : σ → A)
    (ha : Ideal.span (Set.range a) = maximalIdeal A) :
    ∃ f : MvPowerSeries σ K →ₐ[K] A,
      Function.Surjective f ∧ ∀ i : σ, f (MvPowerSeries.X i) = a i := by
  obtain ⟨f, hC, hX⟩ := exists_map K A (maximalIdeal A) a
    (fun i => ha ▸ Ideal.subset_span (Set.mem_range_self i))
  let φ : MvPowerSeries σ K →ₐ[K] A := { f with commutes' := hC }
  exact ⟨φ, surjective K A hres a ha f hC hX, hX⟩

end PhilipponCompleteLocalPowerSeriesPresentation

end
end

section

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
noncomputable section

open IsLocalRing

namespace PhilipponPowerSeriesRegularity

/-- A power series variable preserves regularity of a Noetherian local ring. -/
theorem powerSeries (R : Type*) [CommRing R] [IsRegularLocalRing R] :
    IsRegularLocalRing (PowerSeries R) := by
  have hX : PowerSeries.X ∈ maximalIdeal (PowerSeries R) := by
    change ¬ IsUnit (PowerSeries.X : PowerSeries R)
    rw [PowerSeries.isUnit_iff_constantCoeff, PowerSeries.constantCoeff_X]
    exact not_isUnit_zero
  have hgen := PowerSeries.spanFinrank_le_spanFinrank_map_constantCoeff_add_one_of_X_mem hX
  have hmap : (maximalIdeal (PowerSeries R)).map (PowerSeries.constantCoeff : PowerSeries R →+* R) =
      maximalIdeal R := map_maximalIdeal_of_surjective (R := PowerSeries R) (S := R)
        (PowerSeries.constantCoeff (R := R)) PowerSeries.constantCoeff_surj
  rw [hmap] at hgen
  apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le (PowerSeries R)
  calc ((maximalIdeal (PowerSeries R)).spanFinrank : WithBot ℕ∞)
      ≤ (((maximalIdeal R).spanFinrank + 1 : ℕ) : WithBot ℕ∞) := by exact_mod_cast hgen
    _ = ringKrullDim R + 1 := by
      push_cast
      rw [IsRegularLocalRing.spanFinrank_maximalIdeal]
    _ ≤ ringKrullDim (PowerSeries R) := ringKrullDim_succ_le_ringKrullDim_powerseries

theorem fin (R : Type*) [CommRing R] [IsRegularLocalRing R] (n : ℕ) :
    IsRegularLocalRing (MvPowerSeries (Fin n) R) := by
  induction n with
  | zero =>
      exact IsRegularLocalRing.of_ringEquiv (MvPowerSeries.isEmptyEquiv (Fin 0) R).toRingEquiv.symm
  | succ n ih =>
      letI := ih
      letI := powerSeries (MvPowerSeries (Fin n) R)
      exact IsRegularLocalRing.of_ringEquiv (MvPowerSeries.finSuccEquiv R n).toRingEquiv.symm

/-- The formal regular local models needed for completed nodal charts. -/
theorem mvPowerSeries (R : Type*) [CommRing R] [IsRegularLocalRing R]
    (σ : Type*) [Finite σ] : IsRegularLocalRing (MvPowerSeries σ R) := by
  classical
  letI := Fintype.ofFinite σ
  letI := fin R (Fintype.card σ)
  exact IsRegularLocalRing.of_ringEquiv
    (MvPowerSeries.renameEquiv R (Fintype.equivFin σ)).toRingEquiv.symm

end PhilipponPowerSeriesRegularity

end
end

section

set_option autoImplicit false
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace PhilipponMultiplicity.Chardin
open MvPowerSeries

/-- The residue ideal of a power-series ring in finitely many variables is
the ideal of its parameters. This connects constant coefficients with the
existing adic-completeness theorem. -/
theorem powerSeries_constantCoeff_ker (σ R : Type*) [Finite σ] [CommRing R] :
    RingHom.ker (constantCoeff : MvPowerSeries σ R →+* R) =
      Ideal.span (Set.range X) := by
  let I := MvPolynomial.idealOfVars σ R
  let e := toAdicCompletionAlgEquiv σ R
  have hmap : Ideal.map e.toRingEquiv (Ideal.span (Set.range X)) =
      I.map (algebraMap (MvPolynomial σ R) (AdicCompletion I (MvPolynomial σ R))) := by
    change Ideal.map e.toRingEquiv (Ideal.span (Set.range X)) =
      Ideal.map _ (Ideal.span (Set.range MvPolynomial.X))
    simp_rw [Ideal.map_span, ← Set.range_comp]
    congr 2
    ext i
    simp [e, I, AdicCompletion.algebraMap_apply, ← MvPolynomial.coe_X,
      toAdicCompletion_coe]
  have hpre : (RingHom.ker (AdicCompletion.evalOneₐ I).toRingHom).comap e.toRingEquiv =
      Ideal.span (Set.range X) := by
    rw [AdicCompletion.ker_evalOneₐ_eq_map I (MvPolynomial.idealOfVars_fg σ R), ← hmap]
    exact Ideal.comap_map_of_bijective e.toRingEquiv e.bijective
  rw [← hpre]
  ext f
  change constantCoeff f = 0 ↔ AdicCompletion.evalOneₐ I (e f) = 0
  have heval : AdicCompletion.evalOneₐ I (e f) = Ideal.Quotient.mk I (truncTotal 1 f) := rfl
  rw [heval, Ideal.Quotient.eq_zero_iff_mem]
  change constantCoeff f = 0 ↔ truncTotal 1 f ∈ MvPolynomial.idealOfVars σ R
  rw [← pow_one (MvPolynomial.idealOfVars σ R), MvPolynomial.mem_pow_idealOfVars_iff']
  constructor
  · intro hf d hd
    have hd0 : d = 0 := (Finsupp.degree_eq_zero_iff d).mp (by omega)
    subst d
    rw [coeff_truncTotal f (by simp), coeff_zero_eq_constantCoeff]
    exact hf
  · intro hf
    have h := hf 0 (by simp)
    rwa [coeff_truncTotal f (by simp), coeff_zero_eq_constantCoeff] at h

theorem powerSeries_complete_constantCoeff_ker (σ R : Type*) [Finite σ] [CommRing R] :
    IsAdicComplete (RingHom.ker (constantCoeff : MvPowerSeries σ R →+* R))
      (MvPowerSeries σ R) := by
  rw [powerSeries_constantCoeff_ker]
  infer_instance

end PhilipponMultiplicity.Chardin

end
end

section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
noncomputable section

open IsLocalRing

namespace PhilipponCompleteRegularLocalStructure

variable (K : Type u) [Field K]

theorem maximalIdeal_eq_span_X (σ : Type w) [Finite σ] :
    maximalIdeal (MvPowerSeries σ K) = Ideal.span (Set.range MvPowerSeries.X) := by
  rw [← PhilipponMultiplicity.Chardin.powerSeries_constantCoeff_ker σ K]
  ext f
  change (¬ IsUnit f) ↔ MvPowerSeries.constantCoeff f = 0
  simp only [MvPowerSeries.isUnit_iff_constantCoeff, isUnit_iff_ne_zero, not_not]

theorem spanFinrank_maximalIdeal_le_card (σ : Type w) [Finite σ] :
    (maximalIdeal (MvPowerSeries σ K)).spanFinrank ≤ Nat.card σ := by
  rw [maximalIdeal_eq_span_X K σ]
  calc
    (Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ K))).spanFinrank
        ≤ (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ K)).ncard :=
      Submodule.spanFinrank_span_le_ncard_of_finite (Set.finite_range _)
    _ ≤ Nat.card σ := by
      simpa only [Set.image_univ, Set.ncard_univ] using
        (Set.ncard_image_le (s := Set.univ) (f := (MvPowerSeries.X : σ → MvPowerSeries σ K))
          (Set.finite_univ : (Set.univ : Set σ).Finite))

/-- A surjective formal presentation using no more parameters than the
regular target's dimension has zero kernel. This uses that power series
over a field form a domain, rather than a general regular-domain theorem. -/
theorem injective_of_surjective
    {A : Type v} [CommRing A] [IsRegularLocalRing A]
    {σ : Type w} [Finite σ] (f : MvPowerSeries σ K →+* A)
    (hf : Function.Surjective f)
    (hcard : Nat.card σ ≤ (maximalIdeal A).spanFinrank) :
    Function.Injective f := by
  letI := PhilipponPowerSeriesRegularity.mvPowerSeries K σ
  apply (RingHom.injective_iff_ker_eq_bot f).mpr
  apply le_antisymm _ bot_le
  intro x hx
  change x = 0
  by_contra hx0
  have hdim := ringKrullDim_succ_le_of_surjective f hf
    (mem_nonZeroDivisors_iff_ne_zero.mpr hx0) hx
  rw [← IsRegularLocalRing.spanFinrank_maximalIdeal (R := A),
    ← IsRegularLocalRing.spanFinrank_maximalIdeal (R := MvPowerSeries σ K)] at hdim
  have hnat : (maximalIdeal A).spanFinrank + 1 ≤
      (maximalIdeal (MvPowerSeries σ K)).spanFinrank := by exact_mod_cast hdim
  have hle := spanFinrank_maximalIdeal_le_card K σ
  omega

variable (A : Type v) [CommRing A] [IsRegularLocalRing A] [Algebra K A]
    [IsAdicComplete (maximalIdeal A) A]

/-- Any chosen minimal generating family of the maximal ideal gives a
coefficient-preserving formal-coordinate isomorphism. -/
theorem equiv_of_generators
    (hres : Function.Surjective ((residue A).comp (algebraMap K A)))
    {σ : Type w} [Finite σ] (a : σ → A)
    (ha : Ideal.span (Set.range a) = maximalIdeal A)
    (hcard : Nat.card σ ≤ (maximalIdeal A).spanFinrank) :
    ∃ e : MvPowerSeries σ K ≃ₐ[K] A, ∀ i : σ, e (MvPowerSeries.X i) = a i := by
  obtain ⟨f, hf, hX⟩ :=
    PhilipponCompleteLocalPowerSeriesPresentation.exists_surjective K A hres a ha
  let e := AlgEquiv.ofBijective f ⟨injective_of_surjective K f.toRingHom hf hcard, hf⟩
  exact ⟨e, hX⟩

/-- The equicharacteristic regular complete-local structure theorem with
an explicitly supplied coefficient field inducing the residue field. -/
theorem exists_fin_equiv
    (hres : Function.Surjective ((residue A).comp (algebraMap K A))) :
    ∃ r : ℕ, Nonempty (MvPowerSeries (Fin r) K ≃ₐ[K] A) := by
  classical
  obtain ⟨s, hcard, hs⟩ :=
    Submodule.FG.exists_span_finset_card_eq_spanFinrank
      (maximalIdeal A).fg_of_isNoetherianRing
  have hs' : Ideal.span (Set.range (fun z : s => (z : A))) = maximalIdeal A := by
    simpa using hs
  have hcard' : Nat.card s ≤ (maximalIdeal A).spanFinrank := by simpa using hcard.le
  obtain ⟨e, _⟩ := equiv_of_generators K A hres (fun z : s => (z : A)) hs' hcard'
  exact ⟨Fintype.card s, ⟨(MvPowerSeries.renameEquiv K (Fintype.equivFin s)).symm.trans e⟩⟩

end PhilipponCompleteRegularLocalStructure

end
end

set_option autoImplicit false
open IsLocalRing

theorem solution
    (K : Type u) [Field K] (A : Type v) [CommRing A]
    [IsRegularLocalRing A] [Algebra K A] [IsAdicComplete (maximalIdeal A) A]
    (hres : Function.Surjective ((residue A).comp (algebraMap K A))) :
    ∃ r : ℕ, Nonempty (MvPowerSeries (Fin r) K ≃ₐ[K] A) := by
  exact PhilipponCompleteRegularLocalStructure.exists_fin_equiv K A hres

#print axioms PhilipponCompleteLocalPowerSeriesPresentation.exists_map
#print axioms PhilipponCompleteLocalPowerSeriesPresentation.surjective
#print axioms PhilipponCompleteLocalPowerSeriesPresentation.exists_surjective
#print axioms PhilipponPowerSeriesRegularity.powerSeries
#print axioms PhilipponPowerSeriesRegularity.fin
#print axioms PhilipponPowerSeriesRegularity.mvPowerSeries
#print axioms PhilipponMultiplicity.Chardin.powerSeries_complete_constantCoeff_ker
#print axioms PhilipponCompleteRegularLocalStructure.maximalIdeal_eq_span_X
#print axioms PhilipponCompleteRegularLocalStructure.spanFinrank_maximalIdeal_le_card
#print axioms PhilipponCompleteRegularLocalStructure.injective_of_surjective
#print axioms PhilipponCompleteRegularLocalStructure.equiv_of_generators
#print axioms PhilipponCompleteRegularLocalStructure.exists_fin_equiv
#print axioms solution
