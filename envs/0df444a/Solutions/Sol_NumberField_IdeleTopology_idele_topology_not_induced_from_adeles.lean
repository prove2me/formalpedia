-- Prove2me | solution 1 for NumberField.IdeleTopology.idele_topology_not_induced_from_adeles
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T12:25:14.070946+00:00
-- url     : https://prove2.me/submissions/f9178134-296d-44c9-87a6-c662fa00469f

import Mathlib

open NumberField IsDedekindDomain

set_option autoImplicit false

namespace Sol_NumberField_IdeleTopology_idele_topology_not_induced_from_adeles

open Filter Topology RestrictedProduct IsDedekindDomain.HeightOneSpectrum

section
variable (F : Type*) [Field F] [NumberField F]

/-- The ring of integers of a number field has infinitely many nonzero prime ideals:
above every rational prime there is one. -/
theorem infinite_heightOneSpectrum : Infinite (HeightOneSpectrum (𝓞 F)) := by
  have key : ∀ p : Nat.Primes, ∃ v : HeightOneSpectrum (𝓞 F),
      v.asIdeal.comap (algebraMap ℤ (𝓞 F)) = Ideal.span {((p : ℕ) : ℤ)} := by
    intro p
    have hp : Prime ((p : ℕ) : ℤ) := Nat.prime_iff_prime_int.mp p.2
    have : (Ideal.span {((p : ℕ) : ℤ)}).IsMaximal :=
      PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
    have hker : RingHom.ker (algebraMap ℤ (𝓞 F)) ≤ Ideal.span {((p : ℕ) : ℤ)} := by
      rw [(RingHom.injective_iff_ker_eq_bot _).mp (FaithfulSMul.algebraMap_injective ℤ (𝓞 F))]
      exact bot_le
    obtain ⟨Q, hQmax, hQ⟩ :=
      Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 F) (Ideal.span {((p : ℕ) : ℤ)}) hker
    refine ⟨⟨Q, hQmax.isPrime, ?_⟩, hQ⟩
    rintro rfl
    have hmem : ((p : ℕ) : ℤ) ∈ Ideal.comap (algebraMap ℤ (𝓞 F)) ⊥ := by
      rw [hQ]; exact Ideal.subset_span rfl
    rw [Ideal.mem_comap, Ideal.mem_bot] at hmem
    have h0 : ((p : ℕ) : ℤ) = 0 :=
      FaithfulSMul.algebraMap_injective ℤ (𝓞 F) (by rw [hmem, map_zero])
    exact hp.ne_zero h0
  choose f hf using key
  refine Infinite.of_injective f ?_
  intro p q hpq
  have h : Ideal.span {((p : ℕ) : ℤ)} = Ideal.span {((q : ℕ) : ℤ)} := by
    rw [← hf p, ← hf q, hpq]
  rw [Ideal.span_singleton_eq_span_singleton, Int.associated_iff_natAbs] at h
  exact Subtype.ext (by simpa using h)

end

variable {F : Type*} [Field F] [NumberField F]

/-- The family of coordinates equal to `c` at the place `v` and to `1` at all other places. -/
noncomputable def spikeFun (v : HeightOneSpectrum (𝓞 F)) (c : v.adicCompletion F) :
    (w : HeightOneSpectrum (𝓞 F)) → w.adicCompletion F := by
  classical exact Function.update (fun _ => 1) v c

theorem spikeFun_same (v : HeightOneSpectrum (𝓞 F)) (c : v.adicCompletion F) :
    spikeFun v c v = c := by
  simp [spikeFun]

theorem spikeFun_of_ne (v : HeightOneSpectrum (𝓞 F)) (c : v.adicCompletion F)
    {w : HeightOneSpectrum (𝓞 F)} (h : w ≠ v) : spikeFun v c w = 1 := by
  classical
  simp [spikeFun, Function.update_of_ne h]

theorem spikeFun_mem (v : HeightOneSpectrum (𝓞 F)) (c : v.adicCompletion F)
    (hc : c ∈ v.adicCompletionIntegers F) (w : HeightOneSpectrum (𝓞 F)) :
    spikeFun v c w ∈ w.adicCompletionIntegers F := by
  by_cases h : w = v
  · subst h
    rw [spikeFun_same]
    exact hc
  · rw [spikeFun_of_ne v c h]
    exact one_mem _

/-- The finite adele with coordinate `c` (an integer of `F_v`) at `v` and `1` elsewhere. -/
noncomputable def spike (v : HeightOneSpectrum (𝓞 F)) (c : v.adicCompletion F)
    (hc : c ∈ v.adicCompletionIntegers F) : FiniteAdeleRing (𝓞 F) F :=
  structureMap (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F)
    (fun w => (w.adicCompletionIntegers F : Set (w.adicCompletion F))) cofinite
    (fun w => ⟨spikeFun v c w, spikeFun_mem v c hc w⟩)

theorem spike_apply (v : HeightOneSpectrum (𝓞 F)) (c : v.adicCompletion F)
    (hc : c ∈ v.adicCompletionIntegers F) (w : HeightOneSpectrum (𝓞 F)) :
    spike v c hc w = spikeFun v c w := rfl

theorem tendsto_spike (c : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F)
    (hc : ∀ v, c v ∈ v.adicCompletionIntegers F) :
    Tendsto (fun v => spike v (c v) (hc v)) cofinite (𝓝 (1 : FiniteAdeleRing (𝓞 F) F)) := by
  have h1 : (1 : FiniteAdeleRing (𝓞 F) F) =
      structureMap (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F)
        (fun w => (w.adicCompletionIntegers F : Set (w.adicCompletion F))) cofinite
        (fun w => ⟨1, one_mem _⟩) := rfl
  rw [h1]
  refine (isEmbedding_structureMap.continuous.tendsto _).comp ?_
  rw [tendsto_pi_nhds]
  intro w
  refine tendsto_nhds_of_eventually_eq ?_
  have hne : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, v ≠ w :=
    (Set.finite_singleton w).compl_mem_cofinite
  filter_upwards [hne] with v hv
  exact Subtype.ext (spikeFun_of_ne v (c v) hv.symm)

/-- The adele `(1, spike v c)`. -/
noncomputable def aspike (v : HeightOneSpectrum (𝓞 F)) (c : v.adicCompletion F)
    (hc : c ∈ v.adicCompletionIntegers F) : AdeleRing (𝓞 F) F :=
  ((1 : InfiniteAdeleRing F), spike v c hc)

theorem tendsto_aspike (c : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F)
    (hc : ∀ v, c v ∈ v.adicCompletionIntegers F) :
    Tendsto (fun v => aspike v (c v) (hc v)) cofinite (𝓝 (1 : AdeleRing (𝓞 F) F)) := by
  have h1 : (1 : AdeleRing (𝓞 F) F) =
      ((1 : InfiniteAdeleRing F), (1 : FiniteAdeleRing (𝓞 F) F)) := rfl
  rw [h1]
  exact Tendsto.prodMk_nhds tendsto_const_nhds (tendsto_spike c hc)

theorem coord_mul_inverse {x : AdeleRing (𝓞 F) F} (hx : IsUnit x) (w : HeightOneSpectrum (𝓞 F)) :
    x.2 w * (Ring.inverse x).2 w = 1 := by
  have h := Ring.mul_inverse_cancel x hx
  have h2 : (x * Ring.inverse x).2 w = (1 : AdeleRing (𝓞 F) F).2 w := by rw [h]
  exact h2

theorem isUnit_aspike (v : HeightOneSpectrum (𝓞 F)) (c : v.adicCompletion F)
    (hc : c ∈ v.adicCompletionIntegers F) (hc0 : c ≠ 0) : IsUnit (aspike v c hc) := by
  have hfin : IsUnit (spike v c hc) := by
    rw [FiniteAdeleRing.isUnit_iff]
    refine ⟨fun w => ?_, ?_⟩
    · rw [spike_apply]
      by_cases h : w = v
      · subst h
        rw [spikeFun_same]
        exact hc0
      · rw [spikeFun_of_ne v c h]
        exact one_ne_zero
    · have hne : ∀ᶠ w : HeightOneSpectrum (𝓞 F) in cofinite, w ≠ v :=
        (Set.finite_singleton v).compl_mem_cofinite
      filter_upwards [hne] with w hw
      rw [spike_apply, spikeFun_of_ne v c hw, map_one]
  exact Prod.isUnit_iff.mpr ⟨isUnit_one, hfin⟩

theorem not_tendsto_inverse [Infinite (HeightOneSpectrum (𝓞 F))]
    (c : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F)
    (hc : ∀ v, c v ∈ v.adicCompletionIntegers F) (hc0 : ∀ v, c v ≠ 0)
    (hc1 : ∀ v, Valued.v (c v) < 1) :
    ¬ Tendsto (fun v => Ring.inverse (aspike v (c v) (hc v))) cofinite
      (𝓝 (1 : AdeleRing (𝓞 F) F)) := by
  intro ht
  have hopen : IsOpen {y : AdeleRing (𝓞 F) F | ∀ w, y.2 w ∈ w.adicCompletionIntegers F} := by
    have h := isOpen_forall_mem (R := fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F)
      (A := fun w => (w.adicCompletionIntegers F : Set (w.adicCompletion F)))
      (fun w => Valued.isOpen_valuationSubring _)
    exact h.preimage continuous_snd
  have h1 : (1 : AdeleRing (𝓞 F) F) ∈
      {y : AdeleRing (𝓞 F) F | ∀ w, y.2 w ∈ w.adicCompletionIntegers F} := fun w => one_mem _
  obtain ⟨v, hv⟩ := (ht.eventually (hopen.mem_nhds h1)).exists
  have hmul := coord_mul_inverse (isUnit_aspike v (c v) (hc v) (hc0 v)) v
  have hcoord : (aspike v (c v) (hc v)).2 v = c v := spikeFun_same v (c v)
  rw [hcoord] at hmul
  have hy : Valued.v ((Ring.inverse (aspike v (c v) (hc v))).2 v) ≤ 1 := hv v
  have hval : Valued.v (c v) * Valued.v ((Ring.inverse (aspike v (c v) (hc v))).2 v) = 1 := by
    rw [← map_mul, hmul, map_one]
  have hlt : Valued.v (c v) * Valued.v ((Ring.inverse (aspike v (c v) (hc v))).2 v) < 1 :=
    lt_of_le_of_lt (mul_le_mul' le_rfl hy) (by simpa using hc1 v)
  exact absurd hval hlt.ne

end Sol_NumberField_IdeleTopology_idele_topology_not_induced_from_adeles

open Sol_NumberField_IdeleTopology_idele_topology_not_induced_from_adeles in
open Filter Topology IsDedekindDomain.HeightOneSpectrum in
theorem solution (F : Type*) [Field F] [NumberField F] :
    ¬ Topology.IsInducing (Units.val : (AdeleRing (𝓞 F) F)ˣ → AdeleRing (𝓞 F) F) ∧
    ¬ ContinuousOn (Ring.inverse : AdeleRing (𝓞 F) F → AdeleRing (𝓞 F) F)
        {a : AdeleRing (𝓞 F) F | IsUnit a} ∧
    interior {a : AdeleRing (𝓞 F) F | IsUnit a} = ∅ := by
  have : Infinite (HeightOneSpectrum (𝓞 F)) := infinite_heightOneSpectrum F
  -- a uniformizer at every finite place
  choose π hπ using fun v : HeightOneSpectrum (𝓞 F) => v.valuation_exists_uniformizer F
  let c : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F := fun v => (π v : v.adicCompletion F)
  have hval : ∀ v, Valued.v (c v) = WithZero.exp (-1 : ℤ) := fun v => by
    rw [valuedAdicCompletion_eq_valuation', hπ]
  have hc1 : ∀ v, Valued.v (c v) < 1 := fun v => by
    rw [hval, ← WithZero.exp_zero]
    exact WithZero.exp_lt_exp.mpr (by norm_num)
  have hc : ∀ v, c v ∈ v.adicCompletionIntegers F := fun v =>
    (mem_adicCompletionIntegers (𝓞 F) F v).mpr (hc1 v).le
  have hc0 : ∀ v, c v ≠ 0 := fun v h => by
    have := hval v
    rw [h, map_zero] at this
    exact WithZero.exp_ne_zero this.symm
  have hunit : ∀ v, IsUnit (aspike v (c v) (hc v)) := fun v => isUnit_aspike v (c v) (hc v) (hc0 v)
  refine ⟨?_, ?_, ?_⟩
  · -- `Units.val` is not inducing
    intro hind
    let u : HeightOneSpectrum (𝓞 F) → (AdeleRing (𝓞 F) F)ˣ := fun v => (hunit v).unit
    have hu : Tendsto u cofinite (𝓝 1) := by
      rw [hind.tendsto_nhds_iff]
      exact tendsto_aspike c hc
    have hinv : Tendsto (fun v => (u v)⁻¹) cofinite (𝓝 (1 : (AdeleRing (𝓞 F) F)ˣ)) := by
      have := hu.inv
      rwa [inv_one] at this
    have hvalinv : Tendsto (fun v => (((u v)⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F))
        cofinite (𝓝 (1 : AdeleRing (𝓞 F) F)) :=
      (Units.continuous_val.tendsto 1).comp hinv
    refine not_tendsto_inverse c hc hc0 hc1 ?_
    have heq : (fun v => Ring.inverse (aspike v (c v) (hc v))) =
        fun v => (((u v)⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) := by
      funext v
      exact Ring.inverse_unit (u v)
    rw [heq]
    exact hvalinv
  · -- inversion is not continuous for the subspace topology
    intro hcont
    have h1 : ContinuousWithinAt Ring.inverse {a : AdeleRing (𝓞 F) F | IsUnit a} 1 :=
      hcont 1 isUnit_one
    have hw : Tendsto (fun v => aspike v (c v) (hc v)) cofinite
        (𝓝[{a : AdeleRing (𝓞 F) F | IsUnit a}] 1) :=
      tendsto_nhdsWithin_iff.mpr ⟨tendsto_aspike c hc, Eventually.of_forall hunit⟩
    have ht := h1.tendsto.comp hw
    rw [Ring.inverse_one] at ht
    exact not_tendsto_inverse c hc hc0 hc1 ht
  · -- the set of units has empty interior
    rw [Set.eq_empty_iff_forall_notMem]
    intro x hx
    have hU : interior {a : AdeleRing (𝓞 F) F | IsUnit a} ∈ 𝓝 x := isOpen_interior.mem_nhds hx
    have ht : Tendsto (fun v : HeightOneSpectrum (𝓞 F) => x * aspike v 0 (zero_mem _)) cofinite
        (𝓝 x) := by
      have h := (tendsto_const_nhds (x := x) (f := cofinite)).mul
        (tendsto_aspike (F := F) (fun _ => 0) (fun _ => zero_mem _))
      rwa [mul_one] at h
    obtain ⟨v, hv⟩ := (ht.eventually hU).exists
    have hxu : IsUnit (x * aspike v 0 (zero_mem _)) :=
      interior_subset (s := {a : AdeleRing (𝓞 F) F | IsUnit a}) hv
    have hmul := coord_mul_inverse hxu v
    have h0 : (x * aspike v 0 (zero_mem _)).2 v = 0 := by
      have h0' : (x * aspike v 0 (zero_mem _)).2 v = x.2 v * spikeFun v 0 v := rfl
      rw [h0', spikeFun_same, mul_zero]
    rw [h0, zero_mul] at hmul
    exact zero_ne_one hmul
