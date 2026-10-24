-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.logarithmic_jet_bound_controls_center_contact
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T19:13:34.568859+00:00
-- url     : https://prove2.me/submissions/dec398dc-16b6-402b-aadb-5c97087c831e

import Definitions.Def_OAI_PiExponent_LogarithmicWordContact
import Definitions.Def_OAI_PiExponent_LogarithmicInterpolationNumerics
import Mathlib

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.FormalInterpolation

namespace PiL36

/-- power series vanishing at all coefficients with `a 0 ≤ N` -/
def J (m N : ℕ) : Ideal (MvPowerSeries (Fin (m + 1)) ℂ) where
  carrier := {f | ∀ a : Fin (m + 1) →₀ ℕ, a 0 ≤ N → MvPowerSeries.coeff a f = 0}
  add_mem' := by
    intro f g hf hg a ha
    simp [hf a ha, hg a ha]
  zero_mem' := by intro a _; simp
  smul_mem' := by
    intro c f hf a ha
    simp only [smul_eq_mul, MvPowerSeries.coeff_mul]
    apply Finset.sum_eq_zero
    intro p hp
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    have : p.2 0 ≤ N := by
      have := congrArg (fun q => q 0) hp
      simp at this; omega
    simp [hf p.2 this]

lemma coeff_liftSeries (m : ℕ) (p : PowerSeries ℂ) (a : Fin (m + 1) →₀ ℕ) :
    MvPowerSeries.coeff a (liftSeries m p) =
      if (∀ i : Fin m, a i.succ = 0) then PowerSeries.coeff (a 0) p else 0 := by
  conv_lhs => rw [← Finsupp.cons_tail a, ← MvPowerSeries.coeff_coeff_finSuccEquiv]
  have : (MvPowerSeries.finSuccEquiv ℂ m) (liftSeries m p) = PowerSeries.map MvPowerSeries.C p := by
    simp [liftSeries]
  rw [this, PowerSeries.coeff_map, MvPowerSeries.coeff_C]
  congr 1
  apply propext
  constructor
  · intro h i; have := congrArg (fun f => f i) h; simpa [Finsupp.tail, Fin.tail] using this
  · intro h; ext i; simp [Finsupp.tail, Fin.tail, h i]

/-- truncated log as a polynomial in `X 0` -/
noncomputable def LN (m N : ℕ) : MvPolynomial (Fin (m + 1)) ℂ :=
  ∑ k ∈ Finset.range (N + 1),
    MvPolynomial.monomial (Finsupp.single 0 k) (PowerSeries.coeff k (PowerSeries.log ℂ))

lemma LN_mem (m N : ℕ) :
    ((LN m N : MvPolynomial (Fin (m + 1)) ℂ) : MvPowerSeries (Fin (m + 1)) ℂ) -
      liftSeries m (PowerSeries.log ℂ) ∈ J m N := by
  intro a ha
  rw [map_sub, MvPolynomial.coeff_coe, coeff_liftSeries, LN, MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial]
  split_ifs with h
  · have ha' : a = Finsupp.single 0 (a 0) := by
      ext i; refine Fin.cases ?_ (fun i => ?_) i
      · simp
      · simp [h i]
    rw [Finset.sum_eq_single (a 0)]
    · rw [if_pos ha'.symm, sub_self]
    · intro k _ hk; rw [if_neg]; intro h'; apply hk; rw [← h']; simp
    · intro hk; simp at hk; omega
  · rw [Finset.sum_eq_zero, sub_zero]
    intro k _
    rw [if_neg]
    intro h'; apply h; intro i; rw [← h']; simp
  
noncomputable def sig {m : ℕ} (c : Fin m → ℂ) (N : ℕ) :
    MvPolynomial (Fin (m + 1)) ℂ →ₐ[ℂ] MvPolynomial (Fin (m + 1)) ℂ :=
  MvPolynomial.aeval (Fin.cases (1 + MvPolynomial.X 0)
    (fun i => MvPolynomial.C (c i) + MvPolynomial.X i.succ + LN m N))

lemma coeff_sig {m : ℕ} (c : Fin m → ℂ) (N : ℕ) (G : MvPolynomial (Fin (m + 1)) ℂ)
    (a : Fin (m + 1) →₀ ℕ) (ha : a 0 ≤ N) :
    MvPolynomial.coeff a (sig c N G) = MvPowerSeries.coeff a (formalJet c G) := by
  let co := MvPolynomial.coeToMvPowerSeries.algHom (σ := Fin (m + 1)) (R := ℂ) ℂ
  have key : (Ideal.Quotient.mkₐ ℂ (J m N)).comp (co.comp (sig c N)) =
      (Ideal.Quotient.mkₐ ℂ (J m N)).comp (formalJet c) := by
    apply MvPolynomial.algHom_ext
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · simp [co, sig, formalJet]
    · simp only [AlgHom.comp_apply, sig, formalJet, MvPolynomial.aeval_X, Fin.cases_succ]
      rw [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq]
      have := LN_mem m N
      convert this using 1
      simp [co]
  have h := congrArg (fun f => f G) key
  simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq] at h
  have := h a ha
  rw [map_sub, sub_eq_zero] at this
  rw [← this]
  simp [co]


/-- real lower bound for an extended integer -/
def Ge (z : WithTop ℤ) (r : ℝ) : Prop := ∀ k : ℤ, z = k → r ≤ k

lemma Ge_top (r : ℝ) : Ge ⊤ r := by intro k hk; exact absurd hk (by simp)

lemma Ge_of_le {z z' : WithTop ℤ} {r : ℝ} (h : z ≤ z') (hz : Ge z r) : Ge z' r := by
  intro k hk
  subst hk
  obtain ⟨j, rfl⟩ : ∃ j : ℤ, z = j := by
    cases z with
    | top => exact absurd h (by simp)
    | coe j => exact ⟨j, rfl⟩
  have := hz j rfl
  have hj : j ≤ k := by exact_mod_cast h
  have : (j:ℝ) ≤ k := by exact_mod_cast hj
  linarith

lemma Ge_weaken {z : WithTop ℤ} {r r' : ℝ} (h : r' ≤ r) (hz : Ge z r) : Ge z r' :=
  fun k hk => le_trans h (hz k hk)

lemma Ge_add {z z' : WithTop ℤ} {r r' : ℝ} (hz : Ge z r) (hz' : Ge z' r') : Ge (z + z') (r + r') := by
  intro k hk
  cases z with
  | top => simp at hk
  | coe j =>
    cases z' with
    | top => simp at hk
    | coe j' =>
      have : j + j' = k := by exact_mod_cast hk
      have h1 := hz j rfl; have h2 := hz' j' rfl
      rw [← this]; push_cast; linarith

lemma Ge_min {z z' : WithTop ℤ} {r : ℝ} (hz : Ge z r) (hz' : Ge z' r) : Ge (min z z') r := by
  rcases min_choice z z' with h | h <;> rw [h] <;> assumption

lemma Ge_nsmul {z : WithTop ℤ} {r : ℝ} (n : ℕ) (hz : Ge z r) : Ge (n • z) (n * r) := by
  induction n with
  | zero => intro k hk; simp at hk; subst hk; simp
  | succ n ih =>
    rw [succ_nsmul]
    have := Ge_add ih hz
    convert this using 1; push_cast; ring

lemma Ge_of_nsmul {z : WithTop ℤ} {r : ℝ} (n : ℕ) (hn : 0 < n) (hz : Ge (n • z) r) :
    Ge z (r / n) := by
  intro k hk
  subst hk
  have := hz (n * k) (by rw [← WithTop.coe_nsmul, nsmul_eq_mul])
  rw [div_le_iff₀ (by exact_mod_cast hn)]
  push_cast at this; linarith

lemma Ge_zero {z : WithTop ℤ} (h : 0 ≤ z) : Ge z 0 := by
  intro k hk; subst hk; have : (0:ℤ) ≤ k := by exact_mod_cast h
  exact_mod_cast this

section val
variable {E : Type} [Field E] (ν : AddValuation E (WithTop ℤ))

lemma Ge_sum {ι : Type*} (s : Finset ι) (f : ι → E) (r : ℝ) (h : ∀ i ∈ s, Ge (ν (f i)) r) :
    Ge (ν (∑ i ∈ s, f i)) r := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [AddValuation.map_zero, Ge_top]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact Ge_of_le (ν.map_add _ _) (Ge_min (h a (by simp))
      (ih (fun i hi => h i (by simp [hi]))))

lemma Ge_prod {ι : Type*} (s : Finset ι) (f : ι → E) (r : ι → ℝ) (h : ∀ i ∈ s, Ge (ν (f i)) (r i)) :
    Ge (ν (∏ i ∈ s, f i)) (∑ i ∈ s, r i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty, AddValuation.map_one, Finset.sum_empty]; exact Ge_zero le_rfl
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, ν.map_mul]
    exact Ge_add (h a (by simp)) (ih (fun i hi => h i (by simp [hi])))

lemma Ge_sub {f g : E} {r : ℝ} (hf : Ge (ν f) r) (hg : Ge (ν g) r) : Ge (ν (f - g)) r :=
  Ge_of_le (ν.map_sub _ _) (Ge_min hf hg)

end val

end PiL36

open PiL36 in
theorem solution
    {m K : Nat} (c : Fin K → Fin m → Complex)
    (hc : ∀ i : Fin m, Function.Injective (fun j : Fin K => c j i))
    (hm : 1 ≤ m) (hK : 1 ≤ K)
    (v : Fin (m + 1) → Rat) (hv : ∀ i, 0 < (v i : Real))
    (R : Rat) (e : Fin (m + 1) → Nat)
    (hR : 0 < R) (he : ∀ i, 0 < e i)
    (hscale : ∀ i, (R : Real) = (e i : Real) * (v i : Real))
    (E : Type) [Field E] [Algebra Complex E] [Algebra.EssFiniteType Complex E]
    (htrdeg : Algebra.trdeg Complex E = 1) (x : Fin (m + 1) → E)
    (hgen : IntermediateField.adjoin Complex (Set.range x) = ⊤)
    (H : Real) (G : MvPolynomial (Fin (m + 1)) Complex)
    (hjet : logarithmicJetBound c v H G)
    (nu : PolynomialCurvePlace E) (j : Fin K)
    (hcontact : 0 < (polynomialCurveIdealContact nu x
      (logarithmicCenterIdeal (c j) (fun _ => e 0) e) : Real))
    (hne : MvPolynomial.aeval x G ≠ 0) :
    H * (polynomialCurveIdealContact nu x
        (logarithmicCenterIdeal (c j) (fun _ => e 0) e) : Real) ≤
      (R : Real) * (polynomialCurveOrder nu (MvPolynomial.aeval x G) : Real) := by
  classical
  set κ := polynomialCurveIdealContact nu x (logarithmicCenterIdeal (c j) (fun _ => e 0) e) with hκ
  set ν := nu.1
  have hRr : (0:ℝ) < R := by exact_mod_cast hR
  -- integrality of the coordinates and the contact bound
  have hint : ∀ i, (0 : WithTop ℤ) ≤ ν (x i) := by
    by_contra hcon
    have : κ = 0 := by
      rw [hκ]; unfold polynomialCurveIdealContact; rw [if_neg hcon]
    rw [this] at hcontact; simp at hcontact
  have hpoly : ∀ P : MvPolynomial (Fin (m + 1)) ℂ, (0 : WithTop ℤ) ≤ ν (MvPolynomial.aeval x P) := by
    intro P
    induction P using MvPolynomial.induction_on with
    | C b =>
      rw [MvPolynomial.aeval_C]
      by_cases hb : b = 0
      · subst hb; simp [AddValuation.map_zero]
      · rw [nu.2.1 b hb]
    | add p q hp hq => rw [map_add]; exact le_trans (le_min hp hq) (ν.map_add _ _)
    | mul_X p i hp =>
      rw [map_mul, ν.map_mul, MvPolynomial.aeval_X]; exact add_nonneg hp (hint i)
  have hcont : ∀ f ∈ logarithmicCenterIdeal (c j) (fun _ => e 0) e,
      Ge (ν (MvPolynomial.aeval x f)) κ := by
    intro f hf k hk
    have hk0 : 0 ≤ k := by have := hpoly f; rw [hk] at this; exact_mod_cast this
    have hle : κ ≤ k.toNat := by
      rw [hκ]; unfold polynomialCurveIdealContact; rw [if_pos hint]
      apply Nat.sInf_le
      exact ⟨f, hf, by rw [hk]; congr 1; omega⟩
    have : ((κ:ℕ):ℝ) ≤ (k.toNat : ℝ) := by exact_mod_cast hle
    have h2 : ((k.toNat : ℕ) : ℝ) = (k : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hk0
    linarith
  have hcoord : ∀ i, Ge (ν (MvPolynomial.aeval x (logarithmicCoordinate (c j) (fun _ => e 0) i)))
      (κ / e i) := by
    intro i
    apply Ge_of_nsmul (e i) (he i)
    rw [← ν.map_pow, ← map_pow]
    exact hcont _ (Ideal.subset_span ⟨i, rfl⟩)
  have hv0 : (0:ℝ) < v 0 := hv 0
  obtain ⟨N, hN1, hN2⟩ : ∃ N : ℕ, e 0 ≤ N ∧ H ≤ ((N:ℝ) + 1) * v 0 := by
    obtain ⟨N, hN⟩ := exists_nat_ge (max (e 0 : ℝ) (H / v 0))
    refine ⟨N, by exact_mod_cast (le_max_left _ _).trans hN, ?_⟩
    have : H / v 0 ≤ N := (le_max_right _ _).trans hN
    rw [div_le_iff₀ hv0] at this; nlinarith
  let l : ℕ → ℂ := fun k => PowerSeries.coeff k (PowerSeries.log ℂ)
  let u0 : E := x 0 - 1
  let y : Fin (m + 1) → E := Fin.cases u0 (fun i => x i.succ - algebraMap ℂ E (c j i) -
    ∑ k ∈ Finset.range (N + 1), algebraMap ℂ E (l k) * u0 ^ k)
  have hLN : MvPolynomial.aeval y (LN m N) =
      ∑ k ∈ Finset.range (N + 1), algebraMap ℂ E (l k) * u0 ^ k := by
    simp [LN, MvPolynomial.aeval_monomial, y, l]
  have hG : MvPolynomial.aeval x G = MvPolynomial.aeval y (sig (c j) N G) := by
    have : (MvPolynomial.aeval y).comp (sig (c j) N) = MvPolynomial.aeval x := by
      apply MvPolynomial.algHom_ext
      intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · simp [sig, y, u0]
      · simp only [AlgHom.comp_apply, sig, MvPolynomial.aeval_X, Fin.cases_succ, map_add,
          MvPolynomial.aeval_C, hLN]
        simp only [y, Fin.cases_succ]; ring
    rw [← this]; rfl
  have hκ0 : (0:ℝ) ≤ κ := Nat.cast_nonneg _
  have hconst : ∀ b : ℂ, Ge (ν (algebraMap ℂ E b)) 0 := by
    intro b
    have := hpoly (MvPolynomial.C b); rw [MvPolynomial.aeval_C] at this; exact Ge_zero this
  have hu0 : Ge (ν u0) (κ / e 0) := by
    have := hcoord 0
    simpa [logarithmicCoordinate, u0] using this
  have hscale' : ∀ i, (κ:ℝ) / e i = κ * v i / R := by
    intro i
    have hei : (0:ℝ) < e i := by exact_mod_cast he i
    have hvi := (hv i).ne'
    rw [hscale i]; field_simp
  have hy : ∀ i, Ge (ν (y i)) (κ * v i / R) := by
    intro i
    rw [← hscale' i]
    refine Fin.cases ?_ (fun i => ?_) i
    · exact hu0
    · have hU := hcoord i.succ
      have he0 : 0 < e 0 := he 0
      have htr : Polynomial.aeval u0 (InterpolationMatrix.truncatedLog (e 0)) =
          ∑ k ∈ Finset.range (e 0), algebraMap ℂ E (l k) * u0 ^ k := by
        obtain ⟨n, hn⟩ : ∃ n, e 0 = n + 1 := ⟨e 0 - 1, by omega⟩
        rw [Polynomial.aeval_eq_sum_range' (n := e 0)]
        · apply Finset.sum_congr rfl
          intro k hk
          rw [Finset.mem_range] at hk
          simp [InterpolationMatrix.truncatedLog, PowerSeries.coeff_trunc, hk, l, Algebra.smul_def]
        · rw [hn, InterpolationMatrix.truncatedLog]; exact PowerSeries.natDegree_trunc_lt _ _
      have hUeq : MvPolynomial.aeval x (logarithmicCoordinate (c j) (fun _ => e 0) i.succ) =
          x i.succ - algebraMap ℂ E (c j i) -
            ∑ k ∈ Finset.range (e 0), algebraMap ℂ E (l k) * u0 ^ k := by
        rw [← htr]
        simp only [logarithmicCoordinate, Fin.cases_succ, map_sub, MvPolynomial.aeval_X,
          MvPolynomial.aeval_C, u0]
        rw [← Polynomial.aeval_algHom_apply]; simp
      have hyeq : y i.succ = MvPolynomial.aeval x (logarithmicCoordinate (c j) (fun _ => e 0) i.succ) -
          ∑ k ∈ Finset.Ico (e 0) (N + 1), algebraMap ℂ E (l k) * u0 ^ k := by
        rw [hUeq]
        simp only [y, Fin.cases_succ]
        rw [← Finset.sum_range_add_sum_Ico _ (by omega : e 0 ≤ N + 1)]; ring
      rw [hyeq]
      apply Ge_sub _ hU
      apply Ge_sum
      intro k hk
      rw [Finset.mem_Ico] at hk
      rw [ν.map_mul, ν.map_pow]
      have h1 := Ge_add (hconst (l k)) (Ge_nsmul k hu0)
      apply Ge_weaken _ h1
      have hei : (1:ℝ) ≤ e i.succ := by exact_mod_cast he i.succ
      have he0' : (0:ℝ) < e 0 := by exact_mod_cast he0
      have hk' : (e 0 : ℝ) ≤ k := by exact_mod_cast hk.1
      have : (κ:ℝ) / e i.succ ≤ κ := div_le_self hκ0 hei
      have : (κ:ℝ) ≤ k * (κ / e 0) := by
        rw [mul_div_assoc', le_div_iff₀ he0']; nlinarith
      linarith
  have hsupp : ∀ a ∈ (sig (c j) N G).support, H ≤ ∑ i, (v i : ℝ) * (a i : ℝ) := by
    intro a ha
    by_contra hlt
    push Not at hlt
    by_cases ha0 : a 0 ≤ N
    · rw [MvPolynomial.mem_support_iff, coeff_sig (c j) N G a ha0] at ha
      exact ha (hjet j a hlt)
    · have hrest : 0 ≤ ∑ i : Fin m, (v i.succ : ℝ) * (a i.succ : ℝ) :=
        Finset.sum_nonneg (fun i _ => mul_nonneg (hv _).le (Nat.cast_nonneg _))
      rw [Fin.sum_univ_succ] at hlt
      have : ((N:ℝ) + 1) ≤ a 0 := by exact_mod_cast (by omega : N + 1 ≤ a 0)
      nlinarith
  have hbound : Ge (ν (MvPolynomial.aeval x G)) (κ * H / R) := by
    rw [hG, (sig (c j) N G).as_sum, map_sum]
    apply Ge_sum
    intro a ha
    rw [MvPolynomial.aeval_monomial, ν.map_mul, Finsupp.prod]
    have h1 := Ge_add (hconst (MvPolynomial.coeff a (sig (c j) N G)))
      (Ge_prod ν a.support (fun i => y i ^ a i) (fun i => a i * (κ * v i / R))
        (fun i _ => by rw [ν.map_pow]; exact Ge_nsmul _ (hy i)))
    apply Ge_weaken _ h1
    have hsub : ∑ i ∈ a.support, (a i : ℝ) * (κ * v i / R) = ∑ i, (a i : ℝ) * (κ * v i / R) :=
      Finset.sum_subset (Finset.subset_univ _) (fun i _ hi => by
        simp [Finsupp.notMem_support_iff.mp hi])
    rw [hsub, zero_add]
    have : ∑ i, (a i : ℝ) * (κ * v i / R) = κ / R * ∑ i, (v i : ℝ) * (a i : ℝ) := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
    rw [this, mul_div_right_comm]
    exact mul_le_mul_of_nonneg_left (hsupp a ha) (div_nonneg hκ0 hRr.le)
  obtain ⟨k, hk⟩ : ∃ k : ℤ, ν (MvPolynomial.aeval x G) = k := by
    have := (ν.ne_top_iff).mpr hne
    exact WithTop.ne_top_iff_exists.mp this |>.imp fun k hk => hk.symm
  have hord : polynomialCurveOrder nu (MvPolynomial.aeval x G) = k := by
    unfold polynomialCurveOrder; rw [show nu.1 = ν from rfl, hk]; rfl
  rw [hord]
  have := hbound k hk
  rw [div_le_iff₀ hRr] at this
  linarith
