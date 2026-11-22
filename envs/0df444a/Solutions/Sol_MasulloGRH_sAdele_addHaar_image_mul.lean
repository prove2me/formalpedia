-- Prove2me | solution 1 for MasulloGRH.sAdele_addHaar_image_mul
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T12:46:59.123814+00:00
-- url     : https://prove2.me/submissions/aa9f5b5f-f35b-4197-91c6-c01e50fa1325

import Mathlib
import Definitions.Def_MasulloGRH_SAdeles
import Definitions.Def_NumberField_Completion_Finite

open MeasureTheory NumberField IsDedekindDomain
open scoped ENNReal

set_option autoImplicit false

/-!
# The modulus of an `S`-idele is its `S`-idelic norm

Plan of the proof.

* `distribHaarChar_ringEquiv`, `distribHaarChar_pi`, `distribHaarChar_prod`: the Haar character
  (`MeasureTheory.distribHaarChar`) is invariant under topological ring isomorphisms and is
  multiplicative over finite products of second countable locally compact rings.
* `distribHaarChar_real`, `distribHaarChar_complex`, `distribHaarChar_infinitePlace_completion`:
  at an infinite place the Haar character is `‖·‖ ^ mult`.
* `distribHaarChar_adicCompletion`: at a finite place the Haar character is the normalized norm.
  (This part follows the proof of the platform theorem
  `LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm`, itself taken from the FLT
  project, here for a number field in an arbitrary universe.)
* `distribHaarChar_sAdele` and `solution`: assembly.
-/

namespace Sol_MasulloGRH_sAdele_addHaar_image_mul

set_option linter.style.haveILetI false

open TopologicalSpace Set
open scoped NNReal Pointwise WithZero

section General

/-- The Haar character is transported by a ring isomorphism that is a homeomorphism. -/
theorem distribHaarChar_ringEquiv {A B : Type*} [Ring A] [TopologicalSpace A] [IsTopologicalRing A]
    [LocallyCompactSpace A] [Ring B] [TopologicalSpace B] [IsTopologicalRing B]
    [LocallyCompactSpace B] (e : A ≃+* B) (he : Continuous e) (he' : Continuous e.symm) (u : Aˣ) :
    distribHaarChar A u = distribHaarChar B (Units.map (e : A →* B) u) := by
  letI : MeasurableSpace A := borel A
  haveI : BorelSpace A := ⟨rfl⟩
  letI : MeasurableSpace B := borel B
  haveI : BorelSpace B := ⟨rfl⟩
  obtain ⟨K⟩ : Nonempty (PositiveCompacts B) := inferInstance
  let μ : Measure B := Measure.addHaarMeasure K
  let eh : B ≃ₜ A :=
    { e.symm.toEquiv with continuous_toFun := he', continuous_invFun := he }
  let ν : Measure A := μ.map eh
  haveI : ν.IsAddHaarMeasure := AddEquiv.isAddHaarMeasure_map μ e.symm.toAddEquiv he' he
  haveI : ν.Regular := Measure.Regular.map eh
  have hν : ∀ s : Set A, ν s = μ (eh ⁻¹' s) := fun s => eh.toMeasurableEquiv.map_apply s
  have hK : eh ⁻¹' (e ⁻¹' (K : Set B)) = K := by
    ext y
    change e (e.symm y) ∈ (K : Set B) ↔ y ∈ (K : Set B)
    rw [RingEquiv.apply_symm_apply]
  have hs : ν (e ⁻¹' (K : Set B)) = 1 := by
    rw [hν, hK]; exact Measure.addHaarMeasure_self
  have hsm : eh ⁻¹' (u • (e ⁻¹' (K : Set B))) = Units.map (e : A →* B) u • (K : Set B) := by
    ext y
    change e.symm y ∈ u • (e ⁻¹' (K : Set B)) ↔ y ∈ Units.map (e : A →* B) u • (K : Set B)
    rw [Set.mem_smul_set_iff_inv_smul_mem, Set.mem_smul_set_iff_inv_smul_mem, Set.mem_preimage,
      Units.smul_def, Units.smul_def, smul_eq_mul, smul_eq_mul, map_mul,
      RingEquiv.apply_symm_apply, ← map_inv]
    rfl
  refine distribHaarChar_eq_of_measure_smul_eq_mul (μ := ν) (s := e ⁻¹' (K : Set B))
    (by rw [hs]; exact one_ne_zero) (by rw [hs]; exact ENNReal.one_ne_top) ?_
  rw [hν, hsm, hs, mul_one, ← distribHaarChar_mul μ, Measure.addHaarMeasure_self, mul_one]

/-- The Haar character of a finite product of locally compact second countable rings is the
product of the Haar characters of the components. -/
theorem distribHaarChar_pi {ι : Type*} [Fintype ι] {A : ι → Type*} [∀ i, Ring (A i)]
    [∀ i, TopologicalSpace (A i)] [∀ i, IsTopologicalRing (A i)]
    [∀ i, LocallyCompactSpace (A i)] [∀ i, SecondCountableTopology (A i)]
    (u : (∀ i, A i)ˣ) :
    distribHaarChar (∀ i, A i) u = ∏ i, distribHaarChar (A i) (MulEquiv.piUnits u i) := by
  letI : ∀ i, MeasurableSpace (A i) := fun i => borel (A i)
  haveI : ∀ i, BorelSpace (A i) := fun i => ⟨rfl⟩
  have hne : ∀ i, Nonempty (PositiveCompacts (A i)) := fun i => inferInstance
  choose K _ using fun i => exists_true_iff_nonempty.mpr (hne i)
  let μ : ∀ i, Measure (A i) := fun i => Measure.addHaarMeasure (K i)
  let box : Set (∀ i, A i) := Set.univ.pi fun i => (K i : Set (A i))
  have hbox : Measure.pi μ box = 1 := by
    rw [Measure.pi_pi]
    exact Finset.prod_eq_one fun i _ => Measure.addHaarMeasure_self
  have hcompact : IsCompact box := isCompact_univ_pi fun i => (K i).isCompact
  have hint : (interior box).Nonempty := by
    rw [interior_pi_set Set.finite_univ]
    exact Set.univ_pi_nonempty_iff.mpr fun i => (K i).interior_nonempty
  haveI : (Measure.pi μ).Regular :=
    Measure.regular_of_isAddLeftInvariant hcompact hint (by rw [hbox]; exact ENNReal.one_ne_top)
  have hsmul : u • box = Set.univ.pi fun i => (MulEquiv.piUnits u i) • (K i : Set (A i)) := by
    ext x
    simp only [Set.mem_smul_set_iff_inv_smul_mem, Set.mem_pi, Set.mem_univ, true_imp_iff, box]
    rfl
  refine distribHaarChar_eq_of_measure_smul_eq_mul (μ := Measure.pi μ) (s := box)
    (by rw [hbox]; exact one_ne_zero) (by rw [hbox]; exact ENNReal.one_ne_top) ?_
  rw [hsmul, Measure.pi_pi, hbox, mul_one, ENNReal.ofNNReal_finsetProd]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← distribHaarChar_mul (μ i), Measure.addHaarMeasure_self, mul_one]

/-- The Haar character of a product of two locally compact second countable rings is the
product of the Haar characters of the components. -/
theorem distribHaarChar_prod {A B : Type*} [Ring A] [TopologicalSpace A] [IsTopologicalRing A]
    [LocallyCompactSpace A] [SecondCountableTopology A] [Ring B] [TopologicalSpace B]
    [IsTopologicalRing B] [LocallyCompactSpace B] [SecondCountableTopology B] (u : (A × B)ˣ) :
    distribHaarChar (A × B) u =
      distribHaarChar A (MulEquiv.prodUnits u).1 * distribHaarChar B (MulEquiv.prodUnits u).2 := by
  letI : MeasurableSpace A := borel A
  haveI : BorelSpace A := ⟨rfl⟩
  letI : MeasurableSpace B := borel B
  haveI : BorelSpace B := ⟨rfl⟩
  obtain ⟨K⟩ : Nonempty (PositiveCompacts A) := inferInstance
  obtain ⟨L⟩ : Nonempty (PositiveCompacts B) := inferInstance
  let μ : Measure A := Measure.addHaarMeasure K
  let ν : Measure B := Measure.addHaarMeasure L
  let box : Set (A × B) := (K : Set A) ×ˢ (L : Set B)
  have hbox : μ.prod ν box = 1 := by
    rw [Measure.prod_prod, Measure.addHaarMeasure_self, Measure.addHaarMeasure_self, mul_one]
  have hcompact : IsCompact box := K.isCompact.prod L.isCompact
  have hint : (interior box).Nonempty := by
    rw [interior_prod_eq]
    exact K.interior_nonempty.prod L.interior_nonempty
  haveI : (μ.prod ν).Regular :=
    Measure.regular_of_isAddLeftInvariant hcompact hint (by rw [hbox]; exact ENNReal.one_ne_top)
  have hsmul : u • box =
      ((MulEquiv.prodUnits u).1 • (K : Set A)) ×ˢ ((MulEquiv.prodUnits u).2 • (L : Set B)) := by
    ext x
    simp only [Set.mem_smul_set_iff_inv_smul_mem, Set.mem_prod, box]
    rfl
  refine distribHaarChar_eq_of_measure_smul_eq_mul (μ := μ.prod ν) (s := box)
    (by rw [hbox]; exact one_ne_zero) (by rw [hbox]; exact ENNReal.one_ne_top) ?_
  rw [hsmul, Measure.prod_prod, hbox, mul_one, ENNReal.coe_mul, ← distribHaarChar_mul μ,
    ← distribHaarChar_mul ν, Measure.addHaarMeasure_self, Measure.addHaarMeasure_self, mul_one,
    mul_one]

end General

section Archimedean

theorem distribHaarChar_real (u : ℝˣ) : distribHaarChar ℝ u = ‖(u : ℝ)‖₊ := by
  refine distribHaarChar_eq_of_measure_smul_eq_mul (μ := (volume : Measure ℝ))
    (s := Set.Icc (0 : ℝ) 1) (by simp) (by simp) ?_
  rw [show u • Set.Icc (0 : ℝ) 1 = (u : ℝ) • Set.Icc (0 : ℝ) 1 from rfl, Measure.addHaar_smul,
    Module.finrank_self, pow_one, ← Real.enorm_eq_ofReal_abs, enorm_eq_nnnorm]

theorem distribHaarChar_complex (u : ℂˣ) : distribHaarChar ℂ u = ‖(u : ℂ)‖₊ ^ 2 := by
  refine distribHaarChar_eq_of_measure_smul_eq_mul (μ := (volume : Measure ℂ))
    (s := Metric.closedBall (0 : ℂ) 1)
    (Metric.measure_closedBall_pos volume 0 one_pos).ne'
    (isCompact_closedBall (0 : ℂ) 1).measure_lt_top.ne ?_
  have himage : u • Metric.closedBall (0 : ℂ) 1
      = ⇑(Algebra.lmul ℝ ℂ (u : ℂ)) '' Metric.closedBall (0 : ℂ) 1 := by
    rw [← Set.image_smul]
    rfl
  rw [himage, Measure.addHaar_image_linearMap, ← Algebra.norm_apply, Algebra.norm_complex_eq]
  congr 1
  change ENNReal.ofReal |Complex.normSq (u : ℂ)| = ((‖(u : ℂ)‖₊ ^ 2 : ℝ≥0) : ℝ≥0∞)
  rw [abs_of_nonneg (Complex.normSq_nonneg _), Complex.normSq_eq_norm_sq,
    ← ENNReal.ofReal_coe_nnreal]
  simp

variable {F : Type*} [Field F]

open InfinitePlace in
/-- The Haar character of the completion at an infinite place is the normalized absolute value:
`‖·‖` at a real place and `‖·‖ ^ 2` at a complex place. -/
theorem distribHaarChar_infinitePlace_completion (w : InfinitePlace F) (u : (w.Completion)ˣ) :
    distribHaarChar w.Completion u = ‖(u : w.Completion)‖₊ ^ w.mult := by
  rcases w.isReal_or_isComplex with hw | hw
  · have hiso : Isometry (Completion.ringEquivRealOfIsReal hw) :=
      (Completion.isometryEquivRealOfIsReal hw).isometry
    have hnorm : ‖Completion.ringEquivRealOfIsReal hw (u : w.Completion)‖₊
        = ‖(u : w.Completion)‖₊ :=
      NNReal.eq (hiso.norm_map_of_map_zero (map_zero _) _)
    rw [distribHaarChar_ringEquiv (Completion.ringEquivRealOfIsReal hw) hiso.continuous
      (Completion.isometryEquivRealOfIsReal hw).symm.continuous u, distribHaarChar_real]
    rw [show w.mult = 1 by simp [InfinitePlace.mult, hw], pow_one]
    exact hnorm
  · have hiso : Isometry (Completion.ringEquivComplexOfIsComplex hw) :=
      (Completion.isometryEquivComplexOfIsComplex hw).isometry
    have hnorm : ‖Completion.ringEquivComplexOfIsComplex hw (u : w.Completion)‖₊
        = ‖(u : w.Completion)‖₊ :=
      NNReal.eq (hiso.norm_map_of_map_zero (map_zero _) _)
    rw [distribHaarChar_ringEquiv (Completion.ringEquivComplexOfIsComplex hw) hiso.continuous
      (Completion.isometryEquivComplexOfIsComplex hw).symm.continuous u, distribHaarChar_complex]
    rw [show w.mult = 2 by
      simp [InfinitePlace.mult, InfinitePlace.not_isReal_iff_isComplex.mpr hw]]
    exact congrArg (· ^ 2) hnorm

theorem secondCountableTopology_infinitePlace_completion (w : InfinitePlace F) :
    SecondCountableTopology w.Completion := by
  rcases w.isReal_or_isComplex with hw | hw
  · exact (InfinitePlace.Completion.isometryEquivRealOfIsReal
      hw).toHomeomorph.isEmbedding.secondCountableTopology
  · exact (InfinitePlace.Completion.isometryEquivComplexOfIsComplex
      hw).toHomeomorph.isEmbedding.secondCountableTopology

end Archimedean


noncomputable section FinitePlace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open IsDedekindDomain.HeightOneSpectrum IsLocalRing


variable (F : Type*) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

theorem card_residueField_eq_absNorm :
    Nat.card (ResidueField (v.adicCompletionIntegers F)) = Ideal.absNorm v.asIdeal := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  exact Nat.card_congr (HeightOneSpectrum.ResidueFieldEquivCompletionResidueField F v).toEquiv.symm

variable {F v}

theorem exists_out_add_mul {ϖ : v.adicCompletionIntegers F} (hϖ : Irreducible ϖ)
    (Y : v.adicCompletionIntegers F) :
    ∃ z : v.adicCompletionIntegers F,
      Y = Quotient.out (residue (v.adicCompletionIntegers F) Y) + ϖ * z := by
  have hout : residue (v.adicCompletionIntegers F)
      (Quotient.out (residue (v.adicCompletionIntegers F) Y))
      = residue (v.adicCompletionIntegers F) Y := Quotient.out_eq _
  have hzero : residue (v.adicCompletionIntegers F)
      (Y - Quotient.out (residue (v.adicCompletionIntegers F) Y)) = 0 := by
    rw [map_sub, hout, sub_self]
  set w : v.adicCompletionIntegers F
      := Y - Quotient.out (residue (v.adicCompletionIntegers F) Y) with hw
  have hmem : w ∈ maximalIdeal (v.adicCompletionIntegers F) :=
    Ideal.Quotient.eq_zero_iff_mem.mp hzero
  rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at hmem
  obtain ⟨z, hz⟩ := hmem
  refine ⟨z, ?_⟩
  have hsub : Y - Quotient.out (residue (v.adicCompletionIntegers F) Y) = ϖ * z := by
    rw [← hw]; exact hz
  exact sub_eq_iff_eq_add'.mp hsub

theorem residue_out_add_mul {ϖ : v.adicCompletionIntegers F} (hϖ : Irreducible ϖ)
    (k : ResidueField (v.adicCompletionIntegers F)) (z : v.adicCompletionIntegers F) :
    residue (v.adicCompletionIntegers F) (Quotient.out k + ϖ * z) = k := by
  have hϖ0 : residue (v.adicCompletionIntegers F) ϖ = 0 := by
    refine Ideal.Quotient.eq_zero_iff_mem.mpr ?_
    rw [hϖ.maximalIdeal_eq]
    exact Ideal.mem_span_singleton_self ϖ
  have hout : residue (v.adicCompletionIntegers F) (Quotient.out k) = k := Quotient.out_eq _
  rw [map_add, map_mul, hϖ0, zero_mul, add_zero, hout]

abbrev cosetMap (ϖ : v.adicCompletionIntegers F)
    (k : ResidueField (v.adicCompletionIntegers F)) (y : v.adicCompletion F) :
    v.adicCompletion F :=
  ((Quotient.out k : v.adicCompletionIntegers F) : v.adicCompletion F)
    + ((ϖ : v.adicCompletionIntegers F) : v.adicCompletion F) * y

set_option maxHeartbeats 6400000 in
set_option maxSynthPendingDepth 3 in
theorem integers_eq_iUnion_image {ϖ : v.adicCompletionIntegers F} (hϖ : Irreducible ϖ) :
    (v.adicCompletionIntegers F : Set (v.adicCompletion F))
      = ⋃ k : ResidueField (v.adicCompletionIntegers F),
          cosetMap ϖ k '' (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
  ext y
  constructor
  · intro hy
    obtain ⟨z, hz⟩ := exists_out_add_mul hϖ (⟨y, hy⟩ : v.adicCompletionIntegers F)
    refine mem_iUnion.mpr ⟨residue (v.adicCompletionIntegers F) ⟨y, hy⟩, ?_⟩
    refine ⟨(z : v.adicCompletion F), z.2, ?_⟩
    have hco := congrArg
      (fun w : v.adicCompletionIntegers F => (w : v.adicCompletion F)) hz
    push_cast at hco
    exact hco.symm
  · intro hy
    obtain ⟨k, hk⟩ := mem_iUnion.mp hy
    obtain ⟨z, hz, hzy⟩ := hk
    obtain ⟨X, hXy⟩ : ∃ X : v.adicCompletionIntegers F, (X : v.adicCompletion F) = y :=
      ⟨Quotient.out k + ϖ * ⟨z, hz⟩, by push_cast; exact hzy⟩
    rw [← hXy]
    exact X.2

set_option maxHeartbeats 6400000 in
set_option maxSynthPendingDepth 3 in
theorem pairwise_disjoint_image {ϖ : v.adicCompletionIntegers F} (hϖ : Irreducible ϖ) :
    Pairwise (Function.onFun Disjoint fun k : ResidueField (v.adicCompletionIntegers F) =>
      cosetMap ϖ k '' (v.adicCompletionIntegers F : Set (v.adicCompletion F))) := by
  intro k k' hkk'
  refine Set.disjoint_left.mpr fun y hy hy' => hkk' ?_
  obtain ⟨z, hz, hzy⟩ := hy
  obtain ⟨z', hz', hzy'⟩ := hy'
  have hKeq : ((Quotient.out k + ϖ * ⟨z, hz⟩ : v.adicCompletionIntegers F) :
      v.adicCompletion F)
      = ((Quotient.out k' + ϖ * ⟨z', hz'⟩ : v.adicCompletionIntegers F) :
          v.adicCompletion F) := by
    push_cast
    rw [show ((Quotient.out k : v.adicCompletionIntegers F) : v.adicCompletion F)
          + ((ϖ : v.adicCompletionIntegers F) : v.adicCompletion F) * z = y from hzy,
        show ((Quotient.out k' : v.adicCompletionIntegers F) : v.adicCompletion F)
          + ((ϖ : v.adicCompletionIntegers F) : v.adicCompletion F) * z' = y from hzy']
  have hAeq : (Quotient.out k + ϖ * ⟨z, hz⟩ : v.adicCompletionIntegers F)
      = (Quotient.out k' + ϖ * ⟨z', hz'⟩ : v.adicCompletionIntegers F) :=
    Subtype.coe_injective hKeq
  have := congrArg (residue (v.adicCompletionIntegers F)) hAeq
  rwa [residue_out_add_mul hϖ, residue_out_add_mul hϖ] at this

set_option maxHeartbeats 6400000 in
set_option maxSynthPendingDepth 3 in
theorem cosetMap_image_eq {ϖ : v.adicCompletionIntegers F}
    (k : ResidueField (v.adicCompletionIntegers F)) :
    cosetMap ϖ k '' (v.adicCompletionIntegers F : Set (v.adicCompletion F))
      = ((Quotient.out k : v.adicCompletionIntegers F) : v.adicCompletion F) +ᵥ
          (((ϖ : v.adicCompletionIntegers F) : v.adicCompletion F) •
            (v.adicCompletionIntegers F : Set (v.adicCompletion F))) := by
  rw [← Set.image_vadd, ← Set.image_smul, ← Set.image_comp]
  rfl

set_option maxHeartbeats 6400000 in
set_option maxSynthPendingDepth 3 in
theorem measure_integers_eq_card_mul [MeasurableSpace (v.adicCompletion F)]
    [BorelSpace (v.adicCompletion F)] (μ : Measure (v.adicCompletion F))
    [μ.IsAddHaarMeasure] {ϖ : v.adicCompletionIntegers F} (hϖ : Irreducible ϖ) :
    μ (v.adicCompletionIntegers F : Set (v.adicCompletion F))
      = (Nat.card (ResidueField (v.adicCompletionIntegers F)) : ℝ≥0∞)
        * μ (((ϖ : v.adicCompletionIntegers F) : v.adicCompletion F) •
            (v.adicCompletionIntegers F : Set (v.adicCompletion F))) := by
  have hϖ0 : ((ϖ : v.adicCompletionIntegers F) : v.adicCompletion F) ≠ 0 := by
    simpa using (Subtype.coe_injective.ne_iff.mpr hϖ.ne_zero)
  have hTopen : IsOpen (((ϖ : v.adicCompletionIntegers F) : v.adicCompletion F) •
      (v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
    (NumberField.isOpenAdicCompletionIntegers F v).smul₀ hϖ0
  have hTmeas := hTopen.measurableSet
  have hbridge : ∀ k : ResidueField (v.adicCompletionIntegers F),
      cosetMap ϖ k '' (v.adicCompletionIntegers F : Set (v.adicCompletion F))
        = ((Quotient.out k : v.adicCompletionIntegers F) : v.adicCompletion F) +ᵥ
            (((ϖ : v.adicCompletionIntegers F) : v.adicCompletion F) •
              (v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
    fun k => cosetMap_image_eq k
  calc μ (v.adicCompletionIntegers F : Set (v.adicCompletion F))
      = μ (⋃ k : ResidueField (v.adicCompletionIntegers F),
          cosetMap ϖ k '' (v.adicCompletionIntegers F : Set (v.adicCompletion F))) := by
        rw [← integers_eq_iUnion_image hϖ]
    _ = ∑' k : ResidueField (v.adicCompletionIntegers F),
          μ (cosetMap ϖ k '' (v.adicCompletionIntegers F : Set (v.adicCompletion F))) := by
        refine measure_iUnion ?_ fun k => ?_
        · intro k k' hkk'
          exact pairwise_disjoint_image hϖ hkk'
        · rw [hbridge k]
          exact hTmeas.const_vadd _
    _ = ∑' k : ResidueField (v.adicCompletionIntegers F),
          μ (((Quotient.out k : v.adicCompletionIntegers F) : v.adicCompletion F) +ᵥ
            (((ϖ : v.adicCompletionIntegers F) : v.adicCompletion F) •
              (v.adicCompletionIntegers F : Set (v.adicCompletion F)))) := by
        exact tsum_congr fun k => by rw [hbridge k]
    _ = ∑' _ : ResidueField (v.adicCompletionIntegers F),
          μ (((ϖ : v.adicCompletionIntegers F) : v.adicCompletion F) •
            (v.adicCompletionIntegers F : Set (v.adicCompletion F))) := by
        refine tsum_congr fun k => ?_
        exact measure_vadd _ _ _
    _ = (Nat.card (ResidueField (v.adicCompletionIntegers F)) : ℝ≥0∞)
        * μ (((ϖ : v.adicCompletionIntegers F) : v.adicCompletion F) •
            (v.adicCompletionIntegers F : Set (v.adicCompletion F))) := by
        haveI : Fintype (ResidueField (v.adicCompletionIntegers F)) := Fintype.ofFinite _
        rw [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          Nat.card_eq_fintype_card]

/-- A reference Haar measure on `F_v`, normalized to give mass `1` to the integers. -/
def integersPositiveCompacts : TopologicalSpace.PositiveCompacts (v.adicCompletion F) :=
  ⟨⟨(v.adicCompletionIntegers F : Set (v.adicCompletion F)),
      NumberField.isCompactAdicCompletionIntegers F v⟩, by
    rw [interior_eq_iff_isOpen.mpr (NumberField.isOpenAdicCompletionIntegers F v)]
    exact ⟨0, Subring.zero_mem _⟩⟩

theorem distribHaarChar_mk0_irreducible {ϖ : v.adicCompletionIntegers F} (hϖ : Irreducible ϖ)
    (h0 : ((ϖ : v.adicCompletionIntegers F) : v.adicCompletion F) ≠ 0) :
    distribHaarChar (v.adicCompletion F) (Units.mk0 _ h0)
      = ((Nat.card (ResidueField (v.adicCompletionIntegers F)) : ℝ≥0))⁻¹ := by
  letI : MeasurableSpace (v.adicCompletion F) := borel _
  haveI : BorelSpace (v.adicCompletion F) := ⟨rfl⟩
  set S := (v.adicCompletionIntegers F : Set (v.adicCompletion F)) with hS
  have hK : IsCompact S := NumberField.isCompactAdicCompletionIntegers F v
  have hO : IsOpen S := NumberField.isOpenAdicCompletionIntegers F v
  set μ : Measure (v.adicCompletion F) := MeasureTheory.Measure.addHaarMeasure
    (integersPositiveCompacts (F := F) (v := v)) with hμ
  have hq0 : (Nat.card (ResidueField (v.adicCompletionIntegers F)) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast Nat.pos_iff_ne_zero.mp Nat.card_pos
  have hS0 : μ S ≠ 0 := hO.measure_ne_zero μ ⟨0, Subring.zero_mem _⟩
  have hSfin : μ S ≠ ⊤ := hK.measure_lt_top.ne
  refine distribHaarChar_eq_of_measure_smul_eq_mul (μ := μ) (s := S) hS0 hSfin ?_
  have hcount := measure_integers_eq_card_mul μ hϖ
  show μ (((ϖ : v.adicCompletionIntegers F) : v.adicCompletion F) • S)
      = ((Nat.card (ResidueField (v.adicCompletionIntegers F)) : ℝ≥0))⁻¹ * μ S
  rw [ENNReal.coe_inv (by exact_mod_cast Nat.pos_iff_ne_zero.mp Nat.card_pos), ENNReal.coe_natCast]
  rw [hcount]
  rw [← mul_assoc, ENNReal.inv_mul_cancel hq0 (ENNReal.natCast_ne_top _), one_mul]

variable (F v)

theorem smul_coe_adicCompletionIntegers_eq (u : (v.adicCompletion F)ˣ)
    (hu : Valued.v (u : v.adicCompletion F) = 1) :
    u • (v.adicCompletionIntegers F : Set (v.adicCompletion F))
      = (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
  ext x
  rw [Set.mem_smul_set_iff_inv_smul_mem, SetLike.mem_coe, SetLike.mem_coe,
    mem_adicCompletionIntegers, mem_adicCompletionIntegers, Units.smul_def, smul_eq_mul, map_mul,
    Units.val_inv_eq_inv_val, map_inv₀, hu, inv_one, one_mul]

theorem distribHaarChar_eq_one_of_valued_eq_one (u : (v.adicCompletion F)ˣ)
    (hu : Valued.v (u : v.adicCompletion F) = 1) :
    distribHaarChar (v.adicCompletion F) u = 1 := by
  letI : MeasurableSpace (v.adicCompletion F) := borel _
  haveI : BorelSpace (v.adicCompletion F) := ⟨rfl⟩
  have hself : Measure.addHaarMeasure (integersPositiveCompacts (F := F) (v := v))
      (v.adicCompletionIntegers F : Set (v.adicCompletion F)) = 1 :=
    Measure.addHaarMeasure_self (K₀ := integersPositiveCompacts (F := F) (v := v))
  refine distribHaarChar_eq_of_measure_smul_eq_mul
    (μ := Measure.addHaarMeasure (integersPositiveCompacts (F := F) (v := v)))
    (s := (v.adicCompletionIntegers F : Set (v.adicCompletion F))) ?_ ?_ ?_
  · rw [hself]; exact one_ne_zero
  · rw [hself]; exact ENNReal.one_ne_top
  · rw [smul_coe_adicCompletionIntegers_eq F v u hu, hself, ENNReal.coe_one, one_mul]

theorem withZero_lt_one_iff_le_exp_neg_one (x : ℤᵐ⁰) : x < 1 ↔ x ≤ WithZero.exp (-1 : ℤ) := by
  rw [← WithZero.lt_mul_exp_iff_le WithZero.exp_ne_zero, ← WithZero.exp_add]
  norm_num

theorem isUnit_adicCompletionIntegers_iff (a : v.adicCompletionIntegers F) :
    IsUnit a ↔ Valued.v (a : v.adicCompletion F) = 1 := by
  rw [ValuationSubring.valuation_eq_one_iff]
  exact ((Valuation.isEquiv_valuation_valuationSubring Valued.v).eq_one_iff_eq_one).symm

theorem exists_valued_eq_exp_neg_one :
    ∃ ϖ : (v.adicCompletion F)ˣ, Valued.v (ϖ : v.adicCompletion F) = WithZero.exp (-1 : ℤ) := by
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
  have hval : Valued.v ((π : F) : v.adicCompletion F) = WithZero.exp (-1 : ℤ) := by
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hπ]
  have h0 : ((π : F) : v.adicCompletion F) ≠ 0 := fun h => by
    rw [h, map_zero] at hval
    exact WithZero.exp_ne_zero hval.symm
  exact ⟨Units.mk0 _ h0, hval⟩

theorem irreducible_of_valued_eq_exp_neg_one (ϖ : v.adicCompletionIntegers F)
    (hϖ : Valued.v ((ϖ : v.adicCompletionIntegers F) : v.adicCompletion F)
      = WithZero.exp (-1 : ℤ)) : Irreducible ϖ := by
  refine irreducible_iff.mpr ⟨?_, ?_⟩
  · rw [isUnit_adicCompletionIntegers_iff, hϖ, ← WithZero.exp_zero]
    exact fun h => by norm_num [WithZero.exp_inj] at h
  · intro a b hab
    have ha : Valued.v (a : v.adicCompletion F) ≤ 1 := (mem_adicCompletionIntegers (𝓞 F) F v).mp a.2
    have hb : Valued.v (b : v.adicCompletion F) ≤ 1 := (mem_adicCompletionIntegers (𝓞 F) F v).mp b.2
    have hprod : Valued.v (a : v.adicCompletion F) * Valued.v (b : v.adicCompletion F)
        = WithZero.exp (-1 : ℤ) := by
      rw [← map_mul, ← MulMemClass.coe_mul, ← hab, hϖ]
    rw [isUnit_adicCompletionIntegers_iff, isUnit_adicCompletionIntegers_iff]
    by_contra h
    push Not at h
    have ha' : Valued.v (a : v.adicCompletion F) ≤ WithZero.exp (-1 : ℤ) :=
      (withZero_lt_one_iff_le_exp_neg_one _).mp (lt_of_le_of_ne ha h.1)
    have hb' : Valued.v (b : v.adicCompletion F) ≤ WithZero.exp (-1 : ℤ) :=
      (withZero_lt_one_iff_le_exp_neg_one _).mp (lt_of_le_of_ne hb h.2)
    have hle := mul_le_mul' ha' hb'
    rw [hprod, ← WithZero.exp_add, WithZero.exp_le_exp] at hle
    norm_num at hle

theorem distribHaarChar_of_valued_eq_exp_neg_one (ϖ : (v.adicCompletion F)ˣ)
    (hϖ : Valued.v (ϖ : v.adicCompletion F) = WithZero.exp (-1 : ℤ)) :
    distribHaarChar (v.adicCompletion F) ϖ = ((Ideal.absNorm v.asIdeal : ℝ≥0))⁻¹ := by
  have hmem : (ϖ : v.adicCompletion F) ∈ v.adicCompletionIntegers F := by
    rw [mem_adicCompletionIntegers, hϖ, ← WithZero.exp_zero]
    exact WithZero.exp_le_exp.mpr (by norm_num)
  have hirr : Irreducible (⟨_, hmem⟩ : v.adicCompletionIntegers F) :=
    irreducible_of_valued_eq_exp_neg_one F v ⟨_, hmem⟩ hϖ
  have h0 : (((⟨_, hmem⟩ : v.adicCompletionIntegers F) : v.adicCompletionIntegers F) :
      v.adicCompletion F) ≠ 0 := ϖ.ne_zero
  have hmk : Units.mk0 _ h0 = ϖ := Units.ext rfl
  have h := distribHaarChar_mk0_irreducible hirr h0
  rw [hmk, card_residueField_eq_absNorm F v] at h
  exact h

theorem toNNReal_exp {e : ℝ≥0} (he : e ≠ 0) (n : ℤ) :
    WithZeroMulInt.toNNReal he (WithZero.exp n) = e ^ n := by
  have h : WithZero.unzero (WithZero.exp_ne_zero : WithZero.exp n ≠ 0) = Multiplicative.ofAdd n :=
    WithZero.unzero_coe _
  rw [WithZeroMulInt.toNNReal_neg_apply he WithZero.exp_ne_zero, h, toAdd_ofAdd]

theorem distribHaarChar_eq_toNNReal_valued (x : (v.adicCompletion F)ˣ) :
    distribHaarChar (v.adicCompletion F) x
      = WithZeroMulInt.toNNReal (NumberField.HeightOneSpectrum.absNorm_ne_zero v)
          (Valued.v (x : v.adicCompletion F)) := by
  have hvx : Valued.v (x : v.adicCompletion F) ≠ 0 := (Valuation.ne_zero_iff _).mpr x.ne_zero
  obtain ⟨n, hn⟩ : ∃ n : ℤ, Valued.v (x : v.adicCompletion F) = WithZero.exp n :=
    ⟨WithZero.log (Valued.v (x : v.adicCompletion F)), (WithZero.exp_log hvx).symm⟩
  obtain ⟨ϖ, hϖ⟩ := exists_valued_eq_exp_neg_one F v
  set u : (v.adicCompletion F)ˣ := x * ϖ ^ n with hu_def
  have hu : Valued.v (u : v.adicCompletion F) = 1 := by
    rw [hu_def, Units.val_mul, Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀, hn,
      hϖ, ← WithZero.exp_zsmul, smul_eq_mul, mul_neg, mul_one,
      ← WithZero.exp_add, add_neg_cancel, WithZero.exp_zero]
  have hx_eq : x = u * ϖ ^ (-n) := by
    rw [hu_def, mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero, mul_one]
  have hϖmod := distribHaarChar_of_valued_eq_exp_neg_one F v ϖ hϖ
  have humod := distribHaarChar_eq_one_of_valued_eq_one F v u hu
  conv_lhs => rw [hx_eq]
  rw [map_mul, map_zpow, humod, hϖmod, one_mul, inv_zpow', neg_neg, hn, toNNReal_exp]

theorem distribHaarChar_adicCompletion (x : (v.adicCompletion F)ˣ) :
    distribHaarChar (v.adicCompletion F) x = ‖(x : v.adicCompletion F)‖₊ := by
  refine NNReal.coe_injective ?_
  rw [distribHaarChar_eq_toNNReal_valued, coe_nnnorm, NumberField.FinitePlace.norm_def]


end FinitePlace

section Assembly

open MasulloGRH

variable {F : Type*} [Field F] [NumberField F]

theorem secondCountableTopology_sAdeleRing (Sf : Finset (HeightOneSpectrum (𝓞 F))) :
    SecondCountableTopology (SAdeleRing F Sf) := by
  haveI : ∀ w : InfinitePlace F, SecondCountableTopology w.Completion :=
    secondCountableTopology_infinitePlace_completion
  haveI : SecondCountableTopology (InfiniteAdeleRing F) :=
    inferInstanceAs (SecondCountableTopology ((w : InfinitePlace F) → w.Completion))
  infer_instance

/-- The Haar character of the `S`-adele ring is the `S`-idelic norm. -/
theorem distribHaarChar_sAdele (Sf : Finset (HeightOneSpectrum (𝓞 F))) (g : SIdeleGroup F Sf) :
    (distribHaarChar (SAdeleRing F Sf) g : ℝ) = sIdeleNorm Sf g := by
  haveI : ∀ w : InfinitePlace F, SecondCountableTopology w.Completion :=
    secondCountableTopology_infinitePlace_completion
  haveI : SecondCountableTopology (InfiniteAdeleRing F) :=
    inferInstanceAs (SecondCountableTopology ((w : InfinitePlace F) → w.Completion))
  have h1 : distribHaarChar (InfiniteAdeleRing F) (MulEquiv.prodUnits g).1
      = ∏ w : InfinitePlace F, ‖(g : SAdeleRing F Sf).1 w‖₊ ^ w.mult := by
    refine (distribHaarChar_pi (A := fun w : InfinitePlace F => w.Completion)
      (MulEquiv.prodUnits g).1).trans ?_
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [distribHaarChar_infinitePlace_completion]
    rfl
  have h2 : distribHaarChar ((v : Sf) → (v : HeightOneSpectrum (𝓞 F)).adicCompletion F)
      (MulEquiv.prodUnits g).2 = ∏ v : Sf, ‖(g : SAdeleRing F Sf).2 v‖₊ := by
    refine (distribHaarChar_pi
      (A := fun v : Sf => (v : HeightOneSpectrum (𝓞 F)).adicCompletion F)
      (MulEquiv.prodUnits g).2).trans ?_
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [distribHaarChar_adicCompletion]
    rfl
  rw [distribHaarChar_prod g, h1, h2, sIdeleNorm]
  push_cast
  rfl

theorem addHaar_image_mul (Sf : Finset (HeightOneSpectrum (𝓞 F)))
    [MeasurableSpace (SAdeleRing F Sf)] [BorelSpace (SAdeleRing F Sf)]
    (μ : Measure (SAdeleRing F Sf)) [μ.IsAddHaarMeasure]
    (g : SIdeleGroup F Sf) (B : Set (SAdeleRing F Sf)) :
    μ ((fun x : SAdeleRing F Sf => (g : SAdeleRing F Sf) * x) '' B) =
      ENNReal.ofReal (sIdeleNorm Sf g) * μ B := by
  haveI : SecondCountableTopology (SAdeleRing F Sf) := secondCountableTopology_sAdeleRing Sf
  obtain ⟨K⟩ : Nonempty (PositiveCompacts (SAdeleRing F Sf)) := inferInstance
  haveI : μ.Regular :=
    Measure.regular_of_isAddLeftInvariant K.isCompact K.interior_nonempty
      K.isCompact.measure_lt_top.ne
  rw [← distribHaarChar_sAdele Sf g, ENNReal.ofReal_coe_nnreal, distribHaarChar_mul μ g B,
    ← Set.image_smul]
  rfl

end Assembly

end Sol_MasulloGRH_sAdele_addHaar_image_mul

open MasulloGRH

theorem solution
    (F : Type*) [Field F] [NumberField F] (Sf : Finset (HeightOneSpectrum (𝓞 F)))
    [MeasurableSpace (SAdeleRing F Sf)] [BorelSpace (SAdeleRing F Sf)]
    (μ : Measure (SAdeleRing F Sf)) [μ.IsAddHaarMeasure]
    (g : SIdeleGroup F Sf) (B : Set (SAdeleRing F Sf)) (hB : MeasurableSet B) :
    μ ((fun x : SAdeleRing F Sf => (g : SAdeleRing F Sf) * x) '' B) =
      ENNReal.ofReal (sIdeleNorm Sf g) * μ B :=
  Sol_MasulloGRH_sAdele_addHaar_image_mul.addHaar_image_mul Sf μ g B
