-- Prove2me | solution 1 for NumberField.exists_addSubgroup_discreteTopology_units_log_valuation_sum_eq_neg_sum_log_absNorm_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/9775515b-fe5c-5588-9660-565f8951db1a

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_exists_addSubgroup_discreteTopology_units_log_valuation_sum_eq_neg_sum_log_absNorm_mul

set_option autoImplicit false
set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain

noncomputable section

namespace SUnitLogLatticeR4

variable (K : Type) [Field K] [NumberField K] (T : Finset (HeightOneSpectrum (𝓞 K)))

abbrev eI : InfinitePlace K ≃ Fin (Fintype.card (InfinitePlace K)) := Fintype.equivFin _

def archLog (u : Kˣ) : Fin (Fintype.card (InfinitePlace K)) → ℝ :=
  fun i => (((eI K).symm i).mult : ℝ) * Real.log (((eI K).symm i) (u : K))

def ordVec (u : Kˣ) : Fin T.card → ℤ :=
  fun j => Multiplicative.toAdd ((T.equivFin.symm j).1.valuationOfNeZero u)

def Log (u : Kˣ) : (Fin (Fintype.card (InfinitePlace K)) → ℝ) × (Fin T.card → ℤ) :=
  (archLog K u, ordVec K T u)

theorem Log_def (u : Kˣ) : Log K T u =
    (fun i => (((Fintype.equivFin (InfinitePlace K)).symm i).mult : ℝ) *
        Real.log (((Fintype.equivFin (InfinitePlace K)).symm i) (u : K)),
      fun j => Multiplicative.toAdd ((T.equivFin.symm j).1.valuationOfNeZero u)) := rfl

theorem infinitePlace_pos (w : InfinitePlace K) (u : Kˣ) : 0 < w (u : K) :=
  InfinitePlace.pos_iff.mpr u.ne_zero

theorem Log_mul (u u' : Kˣ) : Log K T (u * u') = Log K T u + Log K T u' := by
  ext i
  · simp only [Log, archLog, Prod.fst_add, Pi.add_apply, Units.val_mul, map_mul]
    rw [Real.log_mul (infinitePlace_pos K _ u).ne' (infinitePlace_pos K _ u').ne', mul_add]
  · simp only [Log, ordVec, Prod.snd_add, Pi.add_apply, map_mul, toAdd_mul]

theorem Log_one : Log K T 1 = 0 := by
  have h := Log_mul K T 1 1
  rw [mul_one] at h

  have : Log K T 1 + Log K T 1 = Log K T 1 + 0 := by rw [add_zero]; exact h.symm
  exact add_left_cancel this

theorem Log_inv (u : Kˣ) : Log K T u⁻¹ = -Log K T u := by
  have h := Log_mul K T u u⁻¹
  rw [mul_inv_cancel, Log_one] at h
  exact (neg_eq_of_add_eq_zero_right h.symm).symm

def IsTUnit (u : Kˣ) : Prop := ∀ v : HeightOneSpectrum (𝓞 K), v ∉ T → v.valuationOfNeZero u = 1

theorem isTUnit_one : IsTUnit K T 1 := fun _ _ => map_one _

theorem IsTUnit.mul {u u' : Kˣ} (hu : IsTUnit K T u) (hu' : IsTUnit K T u') :
    IsTUnit K T (u * u') := fun v hv => by rw [map_mul, hu v hv, hu' v hv, mul_one]

theorem IsTUnit.inv {u : Kˣ} (hu : IsTUnit K T u) : IsTUnit K T u⁻¹ :=
  fun v hv => by rw [map_inv, hu v hv, inv_one]

def Λ : AddSubgroup ((Fin (Fintype.card (InfinitePlace K)) → ℝ) × (Fin T.card → ℤ)) where
  carrier := {γ | ∃ u : Kˣ, IsTUnit K T u ∧ Log K T u = γ}
  zero_mem' := ⟨1, isTUnit_one K T, Log_one K T⟩
  add_mem' := by
    rintro _ _ ⟨u, hu, rfl⟩ ⟨u', hu', rfl⟩
    exact ⟨u * u', hu.mul K T hu', Log_mul K T u u'⟩
  neg_mem' := by
    rintro _ ⟨u, hu, rfl⟩
    exact ⟨u⁻¹, hu.inv K T, Log_inv K T u⟩

theorem mem_Λ (γ : (Fin (Fintype.card (InfinitePlace K)) → ℝ) × (Fin T.card → ℤ)) :
    γ ∈ Λ K T ↔ ∃ u : Kˣ, IsTUnit K T u ∧ Log K T u = γ := Iff.rfl

theorem valuation_eq_coe (v : HeightOneSpectrum (𝓞 K)) (u : Kˣ) :
    v.valuation K (u : K) = ((v.valuationOfNeZero u : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) :=
  (HeightOneSpectrum.valuationOfNeZero_eq v u).symm

theorem valuation_ne_zero (v : HeightOneSpectrum (𝓞 K)) (u : Kˣ) : v.valuation K (u : K) ≠ 0 := by
  rw [valuation_eq_coe]; exact WithZero.coe_ne_zero

theorem unzero_valuation (v : HeightOneSpectrum (𝓞 K)) (u : Kˣ) :
    WithZero.unzero (valuation_ne_zero K v u) = v.valuationOfNeZero u := by
  rw [← WithZero.coe_inj, WithZero.coe_unzero, valuation_eq_coe]

theorem exists_integer_of_isTUnit_of_ordVec_eq_zero {u : Kˣ} (hu : IsTUnit K T u)
    (h0 : ordVec K T u = 0) : ∃ x : 𝓞 K, (x : K) = u := by
  have hall : ∀ v : HeightOneSpectrum (𝓞 K), v.valuationOfNeZero u = 1 := by
    intro v
    by_cases hv : v ∈ T
    · have := congr_fun h0 (T.equivFin ⟨v, hv⟩)
      simp only [ordVec, Equiv.symm_apply_apply, Pi.zero_apply, toAdd_eq_zero] at this
      exact this
    · exact hu v hv
  have hle : ∀ v : HeightOneSpectrum (𝓞 K), v.valuation K (u : K) ≤ 1 := fun v => by
    rw [valuation_eq_coe, hall v]; exact le_of_eq WithZero.coe_one
  obtain ⟨x, hx⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one K (u : K) hle
  exact ⟨x, hx⟩

def smallSet : Set ((Fin (Fintype.card (InfinitePlace K)) → ℝ) × (Fin T.card → ℤ)) :=
  Log K T '' {u : Kˣ | (u : K) ∈ {x : K | IsIntegral ℤ x ∧ ∀ φ : K →+* ℂ, ‖φ x‖ ≤ Real.exp 1}}

theorem smallSet_finite : (smallSet K T).Finite := by
  refine Set.Finite.image _ ?_
  have hF := NumberField.Embeddings.finite_of_norm_le K ℂ (Real.exp 1)
  exact hF.preimage (Units.val_injective.injOn)

def isolator : Set ((Fin (Fintype.card (InfinitePlace K)) → ℝ) × (Fin T.card → ℤ)) :=
  {γ | γ.2 = 0 ∧ ∀ i, |γ.1 i| < 1} \ (smallSet K T \ {0})

theorem isOpen_isolator : IsOpen (isolator K T) := by
  refine IsOpen.sdiff ?_ ((smallSet_finite K T).subset Set.diff_subset).isClosed
  refine IsOpen.inter ?_ ?_
  ·
    have : IsOpen ({n : Fin T.card → ℤ | n = 0}) := isOpen_discrete _
    exact this.preimage continuous_snd
  · have h : IsOpen (⋂ i, {γ : (Fin (Fintype.card (InfinitePlace K)) → ℝ) × (Fin T.card → ℤ) | |γ.1 i| < 1}) :=
      isOpen_iInter_of_finite fun i =>
        isOpen_lt (continuous_abs.comp ((continuous_apply i).comp continuous_fst)) continuous_const
    convert h using 1
    ext γ
    simp only [Set.mem_iInter, Set.mem_setOf_eq]
    exact Iff.rfl

theorem zero_mem_isolator : (0 : (Fin (Fintype.card (InfinitePlace K)) → ℝ) × (Fin T.card → ℤ)) ∈
    isolator K T := by
  refine ⟨⟨rfl, fun i => by simp⟩, fun h => h.2 rfl⟩

theorem Log_mem_smallSet {u : Kˣ} (hu : IsTUnit K T u) (h2 : (Log K T u).2 = 0)
    (h1 : ∀ i, |(Log K T u).1 i| < 1) : Log K T u ∈ smallSet K T := by
  refine ⟨u, ⟨?_, fun φ => ?_⟩, rfl⟩
  · obtain ⟨x, hx⟩ := exists_integer_of_isTUnit_of_ordVec_eq_zero K T hu h2
    rw [← hx]; exact x.isIntegral_coe
  ·
    set w : InfinitePlace K := InfinitePlace.mk φ with hw
    have hwφ : w (u : K) = ‖φ (u : K)‖ := InfinitePlace.apply φ _
    have hi := h1 (eI K w)
    simp only [Log, archLog, Equiv.symm_apply_apply] at hi
    have hpos : 0 < w (u : K) := infinitePlace_pos K w u
    have hlog : Real.log (w (u : K)) < 1 := by
      have hm : (1 : ℝ) ≤ w.mult := InfinitePlace.one_le_mult
      have habs : |Real.log (w (u : K))| < 1 := by
        have h' : |(w.mult : ℝ)| * |Real.log (w (u : K))| < 1 := by rwa [← abs_mul]
        rw [abs_of_nonneg (zero_le_one.trans hm)] at h'
        calc |Real.log (w (u : K))| = 1 * |Real.log (w (u : K))| := (one_mul _).symm
          _ ≤ (w.mult : ℝ) * |Real.log (w (u : K))| :=
            mul_le_mul_of_nonneg_right hm (abs_nonneg _)
          _ < 1 := h'
      exact (le_abs_self _).trans_lt habs
    rw [← hwφ]
    calc w (u : K) = Real.exp (Real.log (w (u : K))) := (Real.exp_log hpos).symm
      _ ≤ Real.exp 1 := Real.exp_le_exp.mpr hlog.le

theorem Λ_inter_isolator (γ : (Fin (Fintype.card (InfinitePlace K)) → ℝ) × (Fin T.card → ℤ))
    (hγ : γ ∈ Λ K T) (hγ' : γ ∈ isolator K T) : γ = 0 := by
  obtain ⟨u, hu, rfl⟩ := hγ
  obtain ⟨⟨h2, h1⟩, hns⟩ := hγ'
  by_contra hne
  exact hns ⟨Log_mem_smallSet K T hu h2 h1, hne⟩

theorem discreteTopology_Λ : DiscreteTopology (Λ K T) := by
  rw [discreteTopology_iff_isOpen_singleton_zero]
  have hopen : IsOpen ((Subtype.val : Λ K T → _) ⁻¹' isolator K T) :=
    (isOpen_isolator K T).preimage continuous_subtype_val
  convert hopen using 1
  ext ⟨γ, hγ⟩
  simp only [Set.mem_singleton_iff, Set.mem_preimage]
  constructor
  · rintro h
    rw [Subtype.ext_iff] at h
    simp only [AddSubgroup.coe_zero] at h
    rw [h]; exact zero_mem_isolator K T
  · intro h
    exact Subtype.ext (Λ_inter_isolator K T γ hγ h)

theorem norm_embedding_units (v : HeightOneSpectrum (𝓞 K)) (u : Kˣ) :
    ‖FinitePlace.embedding v (u : K)‖ =
      ((Ideal.absNorm v.asIdeal : NNReal) : ℝ) ^ Multiplicative.toAdd (v.valuationOfNeZero u) := by
  rw [FinitePlace.norm_embedding', WithZeroMulInt.toNNReal_neg_apply _ (valuation_ne_zero K v u),
    unzero_valuation]
  push_cast
  rfl

theorem finprod_finitePlace_units {u : Kˣ} (hu : IsTUnit K T u) :
    ∏ᶠ w : FinitePlace K, w (u : K) =
      ∏ v ∈ T, ((Ideal.absNorm v.asIdeal : NNReal) : ℝ) ^ Multiplicative.toAdd (v.valuationOfNeZero u) := by
  simp only [← finprod_comp_equiv FinitePlace.equivHeightOneSpectrum.symm,
    FinitePlace.equivHeightOneSpectrum_symm_apply, norm_embedding_units]
  refine finprod_eq_prod_of_mulSupport_subset _ fun v hv => ?_
  simp only [Function.mem_mulSupport, Finset.mem_coe] at hv ⊢
  by_contra hvT
  exact hv (by rw [hu v hvT, toAdd_one, zpow_zero])

theorem absNorm_real_pos (v : HeightOneSpectrum (𝓞 K)) : (0 : ℝ) < ((Ideal.absNorm v.asIdeal : NNReal) : ℝ) := by
  have := NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v
  exact_mod_cast (zero_lt_one.trans this)

theorem sum_archLog_add_sum_eq_zero {u : Kˣ} (hu : IsTUnit K T u) :
    (∑ w : InfinitePlace K, (w.mult : ℝ) * Real.log (w (u : K))) +
      ∑ v ∈ T, ((Multiplicative.toAdd (v.valuationOfNeZero u) : ℤ) : ℝ) *
        Real.log ((Ideal.absNorm v.asIdeal : NNReal) : ℝ) = 0 := by
  have hpf := NumberField.prod_abs_eq_one (K := K) (x := (u : K)) u.ne_zero
  rw [finprod_finitePlace_units K T hu] at hpf
  have hA : ∀ w ∈ (Finset.univ : Finset (InfinitePlace K)), w (u : K) ^ w.mult ≠ 0 :=
    fun w _ => pow_ne_zero _ (infinitePlace_pos K w u).ne'
  have hB : ∀ v ∈ T, ((Ideal.absNorm v.asIdeal : NNReal) : ℝ) ^
      Multiplicative.toAdd (v.valuationOfNeZero u) ≠ 0 :=
    fun v _ => zpow_ne_zero _ (absNorm_real_pos K v).ne'
  have hlog := congrArg Real.log hpf
  rw [Real.log_one, Real.log_mul (Finset.prod_ne_zero_iff.mpr hA) (Finset.prod_ne_zero_iff.mpr hB),
    Real.log_prod hA, Real.log_prod hB] at hlog
  simp only [Real.log_pow, Real.log_zpow] at hlog
  exact hlog

theorem sum_Log_fst_eq {u : Kˣ} (hu : IsTUnit K T u) :
    ∑ i, (Log K T u).1 i =
      ∑ j, -Real.log (Ideal.absNorm (T.equivFin.symm j).1.asIdeal : ℝ) * ((Log K T u).2 j : ℝ) := by
  have h := sum_archLog_add_sum_eq_zero K T hu

  have h1 : ∑ i, (Log K T u).1 i = ∑ w : InfinitePlace K, (w.mult : ℝ) * Real.log (w (u : K)) := by
    simp only [Log, archLog]
    exact (eI K).symm.sum_comp (fun w : InfinitePlace K => (w.mult : ℝ) * Real.log (w (u : K)))
  have h2 : ∑ j, -Real.log (Ideal.absNorm (T.equivFin.symm j).1.asIdeal : ℝ) * ((Log K T u).2 j : ℝ) =
      -∑ v ∈ T, ((Multiplicative.toAdd (v.valuationOfNeZero u) : ℤ) : ℝ) *
        Real.log ((Ideal.absNorm v.asIdeal : NNReal) : ℝ) := by
    simp only [Log, ordVec]
    rw [← Finset.sum_neg_distrib, ← Finset.sum_coe_sort T]
    rw [← T.equivFin.symm.sum_comp]
    refine Finset.sum_congr rfl fun j _ => ?_
    push_cast
    ring
  rw [h1, h2]
  linarith

theorem Log_eq_zero_iff {u : Kˣ} (hu : IsTUnit K T u) :
    Log K T u = 0 ↔ ∃ ζ : (𝓞 K)ˣ, ζ ∈ NumberField.Units.torsion K ∧ ((ζ : 𝓞 K) : K) = (u : K) := by
  constructor
  · intro h0
    have h2 : ordVec K T u = 0 := congrArg Prod.snd h0
    have h1 : archLog K u = 0 := congrArg Prod.fst h0
    obtain ⟨x, hx⟩ := exists_integer_of_isTUnit_of_ordVec_eq_zero K T hu h2
    have h0' : Log K T u⁻¹ = 0 := by rw [Log_inv, h0, neg_zero]
    obtain ⟨y, hy⟩ := exists_integer_of_isTUnit_of_ordVec_eq_zero K T (hu.inv K T) (congrArg Prod.snd h0')
    have hxy : x * y = 1 := by
      apply RingOfIntegers.ext
      have hm : ((x * y : 𝓞 K) : K) = (x : K) * (y : K) := map_mul (algebraMap (𝓞 K) K) x y
      rw [hm, hx, hy, Units.val_inv_eq_inv_val, mul_inv_cancel₀ u.ne_zero]
      exact (map_one (algebraMap (𝓞 K) K)).symm
    have hyx : y * x = 1 := by rw [mul_comm]; exact hxy
    refine ⟨⟨x, y, hxy, hyx⟩, ?_, hx⟩
    rw [NumberField.Units.mem_torsion]
    intro w
    change w ((x : 𝓞 K) : K) = 1
    rw [hx]
    have hi := congr_fun h1 (eI K w)
    simp only [archLog, Equiv.symm_apply_apply, Pi.zero_apply, mul_eq_zero, Nat.cast_eq_zero,
      InfinitePlace.mult_ne_zero, false_or] at hi
    have hpos := infinitePlace_pos K w u
    rcases Real.log_eq_zero.mp hi with h | h | h
    · exact absurd h hpos.ne'
    · exact h
    · linarith
  · rintro ⟨ζ, hζ, hζu⟩
    rw [NumberField.Units.mem_torsion] at hζ
    have huζ : u = Units.map (algebraMap (𝓞 K) K : 𝓞 K →* K) ζ := by
      ext; simp [← hζu]
    ext i
    · simp only [Log, archLog, Prod.fst_zero, Pi.zero_apply]
      have := hζ ((eI K).symm i)
      rw [← RingOfIntegers.coe_eq_algebraMap, hζu] at this
      rw [this, Real.log_one, mul_zero]
    · simp only [Log, ordVec, Prod.snd_zero, Pi.zero_apply, toAdd_eq_zero]
      rw [huζ]
      exact HeightOneSpectrum.valuation_of_unit_eq _ ζ

theorem main :
    ∃ (Λ : AddSubgroup ((Fin (Fintype.card (InfinitePlace K)) → ℝ) × (Fin T.card → ℤ)))
      (Log : Kˣ → (Fin (Fintype.card (InfinitePlace K)) → ℝ) × (Fin T.card → ℤ)),
      (∀ u : Kˣ, Log u =
        (fun i => (((Fintype.equivFin (InfinitePlace K)).symm i).mult : ℝ) *
            Real.log (((Fintype.equivFin (InfinitePlace K)).symm i) (u : K)),
          fun j => Multiplicative.toAdd ((T.equivFin.symm j).1.valuationOfNeZero u))) ∧
      (∀ u u' : Kˣ, Log (u * u') = Log u + Log u') ∧
      (∀ γ, γ ∈ Λ ↔ ∃ u : Kˣ,
        (∀ v : HeightOneSpectrum (𝓞 K), v ∉ T → v.valuationOfNeZero u = 1) ∧ Log u = γ) ∧
      DiscreteTopology Λ ∧
      (∀ γ ∈ Λ, ∑ i, γ.1 i =
        ∑ j, -Real.log (Ideal.absNorm (T.equivFin.symm j).1.asIdeal : ℝ) * (γ.2 j : ℝ)) ∧
      (∀ u : Kˣ, (∀ v : HeightOneSpectrum (𝓞 K), v ∉ T → v.valuationOfNeZero u = 1) →
        (Log u = 0 ↔ ∃ ζ : (𝓞 K)ˣ, ζ ∈ NumberField.Units.torsion K ∧ ((ζ : 𝓞 K) : K) = (u : K))) := by
  refine ⟨Λ K T, Log K T, Log_def K T, Log_mul K T, fun γ => mem_Λ K T γ, discreteTopology_Λ K T,
    ?_, fun u hu => Log_eq_zero_iff K T hu⟩
  rintro γ ⟨u, hu, rfl⟩
  exact sum_Log_fst_eq K T hu

end SUnitLogLatticeR4

end

theorem solution
    (K : Type) [Field K] [NumberField K] (T : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ (Λ : AddSubgroup ((Fin (Fintype.card (InfinitePlace K)) → ℝ) × (Fin T.card → ℤ)))
      (Log : Kˣ → (Fin (Fintype.card (InfinitePlace K)) → ℝ) × (Fin T.card → ℤ)),
      (∀ u : Kˣ, Log u =
        (fun i => (((Fintype.equivFin (InfinitePlace K)).symm i).mult : ℝ) *
            Real.log (((Fintype.equivFin (InfinitePlace K)).symm i) (u : K)),
          fun j => Multiplicative.toAdd ((T.equivFin.symm j).1.valuationOfNeZero u))) ∧
      (∀ u u' : Kˣ, Log (u * u') = Log u + Log u') ∧
      (∀ γ, γ ∈ Λ ↔ ∃ u : Kˣ,
        (∀ v : HeightOneSpectrum (𝓞 K), v ∉ T → v.valuationOfNeZero u = 1) ∧ Log u = γ) ∧
      DiscreteTopology Λ ∧
      (∀ γ ∈ Λ, ∑ i, γ.1 i =
        ∑ j, -Real.log (Ideal.absNorm (T.equivFin.symm j).1.asIdeal : ℝ) * (γ.2 j : ℝ)) ∧
      (∀ u : Kˣ, (∀ v : HeightOneSpectrum (𝓞 K), v ∉ T → v.valuationOfNeZero u = 1) →
        (Log u = 0 ↔ ∃ ζ : (𝓞 K)ˣ, ζ ∈ NumberField.Units.torsion K ∧ ((ζ : 𝓞 K) : K) = (u : K))) :=
  SUnitLogLatticeR4.main K T

end S_NumberField_exists_addSubgroup_discreteTopology_units_log_valuation_sum_eq_neg_sum_log_absNorm_mul
end P2MW
export P2MW.S_NumberField_exists_addSubgroup_discreteTopology_units_log_valuation_sum_eq_neg_sum_log_absNorm_mul (solution)
