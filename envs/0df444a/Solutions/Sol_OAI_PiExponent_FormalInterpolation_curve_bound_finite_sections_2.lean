-- Prove2me | solution 2 for OAI.PiExponent.FormalInterpolation.curve_bound_finite_sections
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-24T08:35:02.388256+00:00
-- url     : https://prove2.me/submissions/2578ba34-472d-4cd4-be87-ef94c2bf3933

import Mathlib
import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion

open OAI.PiExponent.FormalInterpolation

namespace S108CC

variable {E : Type} [Field E] [Algebra ℂ E]

lemma transc_of_trdeg (hE : Algebra.trdeg ℂ E = 1) (z : E)
    (hz : IntermediateField.adjoin ℂ {z} = ⊤) : Transcendental ℂ z := by
  intro halg
  have h1 : Algebra.IsAlgebraic ℂ (IntermediateField.adjoin ℂ {z}) :=
    IntermediateField.isAlgebraic_adjoin_simple halg.isIntegral
  have : Algebra.IsAlgebraic ℂ E := by
    refine ⟨fun y => ?_⟩
    have hy : y ∈ IntermediateField.adjoin ℂ {z} := hz ▸ IntermediateField.mem_top
    exact (IntermediateField.isAlgebraic_iff (x := ⟨y, hy⟩)).mp (h1.isAlgebraic _)
  rw [trdeg_eq_zero_iff.mpr this] at hE
  exact zero_ne_one hE

noncomputable def τ (z : E) (hz : Transcendental ℂ z) : RatFunc ℂ →ₐ[ℂ] E :=
  RatFunc.liftAlgHom (Polynomial.aeval z)
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ ((transcendental_iff_injective).1 hz))

lemma τ_X (z : E) (hz : Transcendental ℂ z) : τ z hz RatFunc.X = z := by
  rw [← RatFunc.algebraMap_X, ← div_one (algebraMap _ _ Polynomial.X),
    ← map_one (algebraMap (Polynomial ℂ) (RatFunc ℂ))]
  simp only [τ]
  rw [RatFunc.liftAlgHom_apply_div]
  simp

lemma surj_of (f : RatFunc ℂ →ₐ[ℂ] E) (z : E) (hz : IntermediateField.adjoin ℂ {z} = ⊤)
    (hzf : z ∈ f.fieldRange) : Function.Surjective f := by
  intro y
  have : IntermediateField.adjoin ℂ {z} ≤ f.fieldRange := by
    rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]; exact hzf
  rw [hz] at this
  exact (AlgHom.mem_fieldRange).1 (this IntermediateField.mem_top)

lemma m_transc (z : E) (hz : Transcendental ℂ z) : Transcendental ℂ (z / (z - 1)) := by
  intro h
  have hz1 : z - 1 ≠ 0 := by
    intro h0; apply hz; rw [sub_eq_zero.mp h0]; exact isAlgebraic_one
  have h2 : IsAlgebraic ℂ (z / (z - 1) - 1) := h.sub isAlgebraic_one
  have h3 : z / (z - 1) - 1 = (z - 1)⁻¹ := by field_simp; ring
  rw [h3, IsAlgebraic.inv_iff] at h2
  apply hz
  simpa using h2.add (isAlgebraic_one (R := ℂ) (A := E))

lemma ne1 (z : E) (hz : Transcendental ℂ z) : z - 1 ≠ 0 := by
  intro h0; apply hz; rw [sub_eq_zero.mp h0]; exact isAlgebraic_one

lemma bij (z : E) (hz : Transcendental ℂ z) (hgen : IntermediateField.adjoin ℂ {z} = ⊤) :
    Function.Bijective (τ z hz) :=
  ⟨(τ z hz).toRingHom.injective, surj_of _ z hgen (AlgHom.mem_fieldRange.2 ⟨RatFunc.X, τ_X z hz⟩)⟩

lemma bijm (z : E) (hz : Transcendental ℂ z) (hgen : IntermediateField.adjoin ℂ {z} = ⊤) :
    Function.Bijective (τ (z / (z - 1)) (m_transc z hz)) := by
  have hz1 := ne1 z hz
  refine ⟨(τ _ _).toRingHom.injective, surj_of _ z hgen ?_⟩
  have hmm1 : z / (z - 1) - 1 ≠ 0 := by
    rw [show z / (z - 1) - 1 = (z - 1)⁻¹ by field_simp; ring]; exact inv_ne_zero hz1
  refine AlgHom.mem_fieldRange.2 ⟨RatFunc.X / (RatFunc.X - 1), ?_⟩
  rw [map_div₀, map_sub, map_one, τ_X]
  field_simp
  ring

/-- the Möbius automorphism `z ↦ z/(z-1)` -/
noncomputable def σ (z : E) (hz : Transcendental ℂ z) (hgen : IntermediateField.adjoin ℂ {z} = ⊤) :
    E ≃ₐ[ℂ] E :=
  (AlgEquiv.ofBijective _ (bij z hz hgen)).symm.trans (AlgEquiv.ofBijective _ (bijm z hz hgen))

lemma σ_apply (z : E) (hz : Transcendental ℂ z) (hgen : IntermediateField.adjoin ℂ {z} = ⊤) :
    σ z hz hgen z = z / (z - 1) := by
  have : (AlgEquiv.ofBijective _ (bij z hz hgen)).symm z = RatFunc.X := by
    rw [AlgEquiv.symm_apply_eq]; simp [τ_X]
  simp only [σ, AlgEquiv.trans_apply, this, AlgEquiv.ofBijective_apply, τ_X]

@[simp] lemma comap_ap {F : Type} [Field F] (f : F →+* E) (v : AddValuation E (WithTop ℤ)) (r : F) :
    v.comap f r = v (f r) := rfl

def Φ (s : E ≃ₐ[ℂ] E) : PolynomialCurvePlace E ≃ PolynomialCurvePlace E where
  toFun ν := ⟨ν.1.comap (s : E →+* E), fun b hb => by
      simpa [comap_ap] using ν.2.1 b hb, fun k => by
      obtain ⟨f, hf⟩ := ν.2.2 k
      exact ⟨s.symm f, by simpa [comap_ap] using hf⟩⟩
  invFun ν := ⟨ν.1.comap (s.symm : E →+* E), fun b hb => by
      simpa [comap_ap] using ν.2.1 b hb, fun k => by
      obtain ⟨f, hf⟩ := ν.2.2 k
      exact ⟨s f, by simpa [comap_ap] using hf⟩⟩
  left_inv ν := by
    apply Subtype.ext; apply AddValuation.ext; intro r; simp [comap_ap]
  right_inv ν := by
    apply Subtype.ext; apply AddValuation.ext; intro r; simp [comap_ap]

lemma Φ_apply (s : E ≃ₐ[ℂ] E) (ν : PolynomialCurvePlace E) (r : E) : (Φ s ν).1 r = ν.1 (s r) := rfl

lemma nonneg_aeval (ν : AddValuation E (WithTop ℤ)) (hν : ∀ b : ℂ, b ≠ 0 → ν (algebraMap ℂ E b) = 0)
    {d : ℕ} (x : Fin d → E) (hx : ∀ i, 0 ≤ ν (x i)) (g : MvPolynomial (Fin d) ℂ) :
    0 ≤ ν (MvPolynomial.aeval x g) := by
  induction g using MvPolynomial.induction_on with
  | C a =>
    rw [MvPolynomial.aeval_C]
    by_cases ha : a = 0
    · simp [ha]
    · rw [hν a ha]
  | add p q hp hq => rw [map_add]; exact le_trans (le_min hp hq) (ν.map_add _ _)
  | mul_X p i hp => rw [map_mul, ν.map_mul, MvPolynomial.aeval_X]; exact add_nonneg hp (hx i)

noncomputable abbrev I1 : Ideal (MvPolynomial (Fin 1) ℂ) := Ideal.span {MvPolynomial.X 0 - 1}

lemma pole_eq (ν : PolynomialCurvePlace E) (x : Fin 1 → E) :
    polynomialCurvePole ν x (fun _ => (1 : ℚ)) = max 0 (-(polynomialCurveOrder ν (x 0) : ℝ)) := by
  unfold polynomialCurvePole
  apply le_antisymm
  · apply Finset.sup'_le
    intro i _
    rcases i with _ | j
    · exact le_max_left _ _
    · fin_cases j; simp
  · apply max_le
    · exact Finset.le_sup' (f := fun i : Option (Fin 1) => i.elim 0 (fun j =>
        -(polynomialCurveOrder ν (x j) : Real) / ((1 : ℚ) : Real))) (Finset.mem_univ none)
    · have := Finset.le_sup' (f := fun i : Option (Fin 1) => i.elim 0 (fun j =>
        -(polynomialCurveOrder ν (x j) : Real) / ((1 : ℚ) : Real))) (Finset.mem_univ (some 0))
      exact le_trans (by simp) this

lemma contact_eq (ν : PolynomialCurvePlace E) (x : Fin 1 → E) (B : ℕ)
    (hB : ν.1 (x 0 - 1) = ((B : ℤ) : WithTop ℤ)) (hA : 0 ≤ ν.1 (x 0)) :
    polynomialCurveIdealContact ν x I1 = B := by
  unfold polynomialCurveIdealContact
  rw [if_pos (by intro i; fin_cases i; exact hA)]
  apply le_antisymm
  · apply Nat.sInf_le
    refine ⟨MvPolynomial.X 0 - 1, Ideal.subset_span rfl, ?_⟩
    simpa using hB
  · apply le_csInf
    · exact ⟨B, MvPolynomial.X 0 - 1, Ideal.subset_span rfl, by simpa using hB⟩
    · rintro k ⟨f, hf, hk⟩
      obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 hf
      have h0 := nonneg_aeval ν.1 ν.2.1 x (by intro i; fin_cases i; exact hA) a
      have hx1 : MvPolynomial.aeval x (MvPolynomial.X 0 - 1 : MvPolynomial (Fin 1) ℂ) = x 0 - 1 := by
        simp
      rw [map_mul, ν.1.map_mul, hx1, hB] at hk
      have : ((B : ℤ) : WithTop ℤ) ≤ (k : ℤ) := by
        rw [← hk]; exact le_add_of_nonneg_left h0
      exact_mod_cast WithTop.coe_le_coe.1 this

lemma contact_eq_zero (ν : PolynomialCurvePlace E) (x : Fin 1 → E) (hA : ¬ 0 ≤ ν.1 (x 0)) :
    polynomialCurveIdealContact ν x I1 = 0 := by
  unfold polynomialCurveIdealContact
  rw [if_neg (by intro h; exact hA (h 0))]

lemma key (x : Fin 1 → E) (hz : Transcendental ℂ (x 0))
    (hgen : IntermediateField.adjoin ℂ {x 0} = ⊤) (ν : PolynomialCurvePlace E) :
    (polynomialCurveIdealContact ν x I1 : ℝ) =
      polynomialCurvePole (Φ (σ (x 0) hz hgen) ν) x (fun _ => (1 : ℚ)) := by
  have hx0 : x 0 ≠ 0 := by intro h; apply hz; rw [h]; exact isAlgebraic_zero
  have hx1 := ne1 (x 0) hz
  obtain ⟨A, hA⟩ := WithTop.ne_top_iff_exists.1 ((ν.1.ne_top_iff).2 hx0)
  obtain ⟨B, hB⟩ := WithTop.ne_top_iff_exists.1 ((ν.1.ne_top_iff).2 hx1)
  rw [pole_eq]
  have hord : polynomialCurveOrder (Φ (σ (x 0) hz hgen) ν) (x 0) = A - B := by
    unfold polynomialCurveOrder
    rw [Φ_apply, σ_apply, ν.1.map_div, ← hA, ← hB]
    rw [show ((A : WithTop ℤ) - (B : WithTop ℤ)) = ((A - B : ℤ) : WithTop ℤ) from rfl, WithTop.untop₀_coe]
  rw [hord]
  have h1 : ν.1 1 = 0 := ν.1.map_one
  rcases lt_trichotomy A 0 with hneg | hzero | hpos
  · have hBA : B = A := by
      have : ν.1 (x 0 - 1) = ν.1 (x 0) := ν.1.map_sub_eq_of_lt_left (by rw [h1, ← hA]; exact_mod_cast hneg)
      rw [← hA, ← hB] at this; exact_mod_cast this
    rw [contact_eq_zero ν x (by rw [← hA]; exact_mod_cast hneg.not_ge)]
    subst hBA; simp
  · subst hzero
    have hB0 : 0 ≤ B := by
      have := ν.1.map_sub (x 0) 1
      rw [h1, ← hA, ← hB] at this; simpa using this
    rw [contact_eq ν x B.toNat (by rw [← hB, Int.toNat_of_nonneg hB0]) (by rw [← hA]; simp)]
    have : ((B.toNat : ℕ) : ℝ) = (B : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hB0
    rw [this]; simp [hB0]
  · have hB0 : B = 0 := by
      have : ν.1 (x 0 - 1) = ν.1 1 := ν.1.map_sub_eq_of_lt_right (by rw [h1, ← hA]; exact_mod_cast hpos)
      rw [h1, ← hB] at this; exact_mod_cast this
    rw [contact_eq ν x 0 (by rw [← hB, hB0]; rfl) (by rw [← hA]; exact_mod_cast hpos.le)]
    subst hB0; simp; exact_mod_cast hpos.le

lemma hcurve : WeightedIdealCurveBound I1 (fun _ => (1 : ℚ)) 1 := by
  intro E _ _ _ htr x hx
  have hgen : IntermediateField.adjoin ℂ {x 0} = ⊤ := by
    rw [Set.range_unique] at hx; exact hx
  have hz := transc_of_trdeg htr (x 0) hgen
  calc (∑ᶠ nu : PolynomialCurvePlace E, (polynomialCurveIdealContact nu x I1 : Real))
      = ∑ᶠ nu : PolynomialCurvePlace E,
          polynomialCurvePole (Φ (σ (x 0) hz hgen) nu) x (fun _ => (1 : ℚ)) :=
        finsum_congr (key x hz hgen)
    _ = ∑ᶠ nu : PolynomialCurvePlace E, polynomialCurvePole nu x (fun _ => (1 : ℚ)) :=
        finsum_comp_equiv (f := fun nu : PolynomialCurvePlace E =>
          polynomialCurvePole nu x (fun _ => (1 : ℚ))) (Φ (σ (x 0) hz hgen))
    _ ≤ ((1 : ℚ) : Real) * ∑ᶠ nu : PolynomialCurvePlace E,
          polynomialCurvePole nu x (fun _ => (1 : ℚ)) := by simp

lemma hfin : Module.Finite ℂ (MvPolynomial (Fin 1) ℂ ⧸ I1) := by
  have hsurj : Function.Surjective (Algebra.linearMap ℂ (MvPolynomial (Fin 1) ℂ ⧸ I1)) := by
    intro q
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective q
    have hX : Ideal.Quotient.mk I1 (MvPolynomial.X 0) = 1 := by
      rw [← map_one (Ideal.Quotient.mk I1), Ideal.Quotient.eq]
      exact Ideal.subset_span rfl
    suffices h : Ideal.Quotient.mk I1 f ∈ (⊥ : Subalgebra ℂ (MvPolynomial (Fin 1) ℂ ⧸ I1)) by
      obtain ⟨c, hc⟩ := Algebra.mem_bot.1 h
      exact ⟨c, hc⟩
    induction f using MvPolynomial.induction_on with
    | C a => exact Algebra.mem_bot.2 ⟨a, rfl⟩
    | add p q hp hq => rw [map_add]; exact add_mem hp hq
    | mul_X p i hp =>
      fin_cases i
      rw [map_mul]; simp only [Fin.zero_eta, Fin.isValue, hX, mul_one]; exact hp
  exact Module.Finite.of_surjective _ hsurj

end S108CC

open S108CC in
theorem solution : ¬ (∀ {d : Nat} (I : Ideal (MvPolynomial (Fin d) Complex))
    (hfinite : Module.Finite Complex (MvPolynomial (Fin d) Complex ⧸ I))
    (w : Fin d → Rat) (hw : ∀ i, 0 < (w i : Real))
    (rho : Rat) (hrho : 0 ≤ rho)
    (hcurve : WeightedIdealCurveBound I w rho)
    (eps : Real) (heps : 0 < eps),
    ∃ (s : Nat) (S : Finset (MvPolynomial (Fin d) Complex)),
      0 < s ∧
      (∀ f ∈ S, f ∈ I ^ s) ∧
      ∀ i : Fin d, ∃ n : Nat, 0 < n ∧
        MvPolynomial.X i ^ n ∈ Ideal.span (S : Set (MvPolynomial (Fin d) Complex)) ∧
        (n : Real) * (w i : Real) < (s : Real) * ((rho : Real) + eps)) := by
  intro h
  obtain ⟨s, F, hs, hF, hi⟩ :=
    h I1 hfin (fun _ => 1) (by simp) 1 (by norm_num) hcurve 1 one_pos
  obtain ⟨n, -, hX, -⟩ := hi 0
  have hmem : (MvPolynomial.X 0 : MvPolynomial (Fin 1) ℂ) ^ n ∈ I1 := by
    have h1 : Ideal.span (F : Set _) ≤ I1 ^ s := Ideal.span_le.2 (fun f hf => hF f hf)
    exact Ideal.pow_le_self (by omega) (h1 hX)
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 hmem
  have := congrArg (MvPolynomial.eval (fun _ => (1 : ℂ))) ha
  simp at this
