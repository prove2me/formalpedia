-- Prove2me | solution 1 for LefebvreVariations.algebraic_mul_pow_sub_pow_finite
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Shiv__0
-- created : 2026-11-27T06:45:16.456141+00:00
-- url     : https://prove2.me/submissions/ac5ad58d-0faa-4839-b605-34e4d3295892
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.NumberTheory.Real.Irrational
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases
import Theorems.Thm_SubspaceTheorem_p_adic_subspace_theorem

set_option autoImplicit false

/-!
Reduction of `LefebvreVariations.algebraic_mul_pow_sub_pow_finite` to
`SubspaceTheorem.p_adic_subspace_theorem`.
-/

private lemma natAbs_cast_real (z : ℤ) : ((z.natAbs : ℕ) : ℝ) = |(z : ℝ)| := by
  cases z with
  | ofNat n => simp
  | negSucc n =>
    rw [Int.natAbs_negSucc, Int.cast_negSucc, abs_of_neg (neg_lt_zero.mpr (by positivity))]
    push_cast
    ring

private lemma padic_norm_int_le_one (p : ℕ) [Fact p.Prime] (z : ℤ) :
    ‖(z : ℚ_[p])‖ ≤ 1 := by
  rw [← Rat.cast_intCast (α := ℚ_[p]) z, Padic.eq_padicNorm]
  exact_mod_cast padicNorm.of_int z

private lemma prod_primeFactors_padic_norm_pow (b : ℕ) (hb : 1 ≤ b) (k : ℕ) :
    (∏ p : {p : ℕ // p ∈ b.primeFactors},
      haveI : Fact p.1.Prime := ⟨Nat.prime_of_mem_primeFactors p.2⟩
      ‖((b ^ k : ℤ) : ℚ_[p.1])‖) = ((b : ℝ) ^ k)⁻¹ := by
  have hb0 : b ≠ 0 := by omega
  have hbk0 : b ^ k ≠ 0 := pow_ne_zero k hb0
  have hterm : ∀ p : {p : ℕ // p ∈ b.primeFactors},
      (haveI : Fact p.1.Prime := ⟨Nat.prime_of_mem_primeFactors p.2⟩
       ‖((b ^ k : ℤ) : ℚ_[p.1])‖) =
        ((p.1 : ℝ) ^ (b.factorization p.1)) ^ (-(k : ℤ)) := by
    rintro ⟨p, hp⟩
    have : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hp⟩
    rw [← Rat.cast_intCast (α := ℚ_[p]) (b ^ k : ℤ), Padic.eq_padicNorm]
    have hq0 : (((b ^ k : ℤ) : ℚ)) ≠ 0 := by exact_mod_cast hbk0
    have hnat_q : ((b ^ k : ℤ) : ℚ) = ((b ^ k : ℕ) : ℚ) := by push_cast; rfl
    rw [hnat_q] at hq0 ⊢
    rw [padicNorm.eq_zpow_of_nonzero hq0, padicValRat.of_nat, padicValNat.pow]
    have hfac : padicValNat p b = b.factorization p :=
      (Nat.factorization_def b (Fact.out)).symm
    rw [hfac]
    push_cast
    rw [← zpow_natCast (p : ℝ), ← zpow_mul]
    congr 1
    ring
  simp_rw [hterm]
  rw [Finset.prod_coe_sort b.primeFactors (fun p => ((p : ℝ) ^ (b.factorization p)) ^ (-(k : ℤ)))]
  rw [Finset.prod_zpow]
  have hnat : (∏ p ∈ b.primeFactors, (p : ℝ) ^ (b.factorization p)) = (b : ℝ) :=
    mod_cast (Nat.prod_primeFactors_pow_factorization hb0).symm
  rw [hnat, zpow_neg, zpow_natCast]

private lemma exists_nonzero_annihilator {n : ℕ} (V : Submodule ℚ (Fin n → ℚ)) (hV : V ≠ ⊤) :
    ∃ a : Fin n → ℚ, a ≠ 0 ∧ ∀ v ∈ V, ∑ j : Fin n, a j * v j = 0 := by
  obtain ⟨f, hf0, hker⟩ := Submodule.exists_le_ker_of_lt_top V (lt_top_iff_ne_top.mpr hV)
  refine ⟨fun j => f (Pi.single j 1), ?_, ?_⟩
  · intro ha
    apply hf0
    ext j
    have := congr_fun ha j
    simpa using this
  · intro v hv
    have hvsum : v = ∑ j : Fin n, v j • Pi.single j (1 : ℚ) := by
      ext i
      simp [Finset.sum_apply, Pi.single_apply]
    have hfv : f v = 0 := hker hv
    rw [hvsum, map_sum] at hfv
    simp only [map_smul, smul_eq_mul] at hfv
    calc ∑ j : Fin n, f (Pi.single j 1) * v j
        = ∑ j : Fin n, v j * f (Pi.single j 1) :=
          Finset.sum_congr rfl fun j _ => mul_comm _ _
      _ = 0 := hfv

private lemma isAlgebraic_rat_cast_real (q : ℚ) : IsAlgebraic ℚ (q : ℝ) := by
  simpa using (isAlgebraic_algebraMap q : IsAlgebraic ℚ (algebraMap ℚ ℝ q))

private lemma rpow_neg_le_one {b : ℕ} (hb : 2 ≤ b) {y : ℝ} (hy : 0 ≤ y) :
    (b : ℝ) ^ (-y) ≤ 1 := by
  have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast (show 1 ≤ b by omega)
  calc (b : ℝ) ^ (-y) ≤ (b : ℝ) ^ (0 : ℝ) := Real.rpow_le_rpow_of_exponent_le hb1 (by linarith)
    _ = 1 := Real.rpow_zero _

private lemma finite_int_abs_le (C : ℝ) : {p : ℤ | |(p : ℝ)| ≤ C}.Finite := by
  refine (Set.finite_Icc (-⌈C⌉) ⌈C⌉).subset ?_
  intro p hp
  rw [Set.mem_Icc]
  have hp' : |(p : ℝ)| ≤ C := hp
  have hle : (p : ℝ) ≤ ⌈C⌉ := (le_abs_self (p : ℝ)).trans (hp'.trans (Int.le_ceil C))
  have hge : (-⌈C⌉ : ℝ) ≤ p := by
    have := neg_le_of_abs_le hp'
    linarith [Int.le_ceil C]
  exact ⟨by exact_mod_cast hge, by exact_mod_cast hle⟩

private lemma finite_pair_nat_int_of_bound (R : ℕ) (C : ℝ) :
    {rp : ℕ × ℤ | rp.1 < R ∧ |(rp.2 : ℝ)| ≤ C}.Finite :=
  ((Set.finite_lt_nat R).prod (finite_int_abs_le C)).subset fun _ h => ⟨h.1, h.2⟩

private lemma rpow_neg_lt_of_large {b : ℕ} (hb : 2 ≤ b) {ε c : ℝ} (hε : 0 < ε) (hc : 0 < c) :
    ∃ N : ℕ, ∀ n ≥ N, (b : ℝ) ^ (-(ε * (n : ℝ))) < c := by
  have hb1 : (1 : ℝ) < b := by exact_mod_cast (show 1 < b by omega)
  have hb_pos : (0 : ℝ) < b := by positivity
  have ht := tendsto_pow_atTop_nhds_zero_of_lt_one (r := (b : ℝ) ^ (-ε))
    (by positivity) (by
      rw [Real.rpow_neg hb_pos.le, inv_lt_one_iff₀]
      right
      exact Real.one_lt_rpow hb1 hε)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp ((tendsto_order.1 ht).2 c hc)
  refine ⟨N, fun n hn => ?_⟩
  have h1 := hN n hn
  rwa [← Real.rpow_natCast, ← Real.rpow_mul hb_pos.le, neg_mul] at h1

private lemma abs_int_le_of_approx {ξ : ℝ} {b r s : ℕ} (hb : 2 ≤ b) {p : ℤ}
    (h1 : |ξ * ((b : ℝ) ^ (r + s) - (b : ℝ) ^ r) - p| < 1) :
    |(p : ℝ)| ≤ (|ξ| + 1) * (b : ℝ) ^ (r + s) := by
  have hb1 : (1 : ℝ) < b := by exact_mod_cast (show 1 < b by omega)
  have htri : |(p : ℝ)| ≤ |ξ * ((b : ℝ) ^ (r + s) - (b : ℝ) ^ r) - p| +
      |ξ * ((b : ℝ) ^ (r + s) - (b : ℝ) ^ r)| := by
    calc |(p : ℝ)| = |-(ξ * ((b : ℝ) ^ (r + s) - (b : ℝ) ^ r) - p) +
          ξ * ((b : ℝ) ^ (r + s) - (b : ℝ) ^ r)| := by ring_nf
      _ ≤ _ := abs_add_le _ _
      _ = _ := by rw [abs_neg]
  have hdiff : |(b : ℝ) ^ (r + s) - (b : ℝ) ^ r| ≤ (b : ℝ) ^ (r + s) := by
    have hle : (b : ℝ) ^ r ≤ (b : ℝ) ^ (r + s) := pow_le_pow_right₀ hb1.le (Nat.le_add_right r s)
    rw [abs_of_nonneg (sub_nonneg.mpr hle)]
    linarith [show (0 : ℝ) ≤ (b : ℝ) ^ r by positivity]
  have hpow1 : 1 ≤ (b : ℝ) ^ (r + s) := one_le_pow₀ hb1.le
  rw [abs_mul] at htri
  nlinarith [abs_nonneg ξ]

private lemma fixed_s_finite (ξ : ℝ) (hξ : IsAlgebraic ℚ ξ) (hi : Irrational ξ)
    (b : ℕ) (hb : 2 ≤ b) (ε : ℝ) (hε : 0 < ε) (s : ℕ) (hs : 1 ≤ s) :
    {rp : ℕ × ℤ | |ξ * ((b : ℝ) ^ (rp.1 + s) - (b : ℝ) ^ rp.1) - rp.2| <
      (b : ℝ) ^ (-(ε * ((rp.1 + s : ℕ) : ℝ)))}.Finite := by
  let qbs : ℚ := (b : ℚ) ^ s - 1
  have hqbs_pos : (0 : ℚ) < qbs := by
    have hb1q : (1 : ℚ) < b := by exact_mod_cast (show 1 < b by omega)
    have : (1 : ℚ) < (b : ℚ) ^ s := one_lt_pow₀ hb1q (by omega)
    dsimp [qbs]; linarith
  have hqbs_ne : qbs ≠ 0 := hqbs_pos.ne'
  let α : ℝ := ξ * (qbs : ℝ)
  have hα_alg : IsAlgebraic ℚ α := by
    rw [isAlgebraic_iff_isIntegral] at hξ ⊢
    exact hξ.mul (isAlgebraic_iff_isIntegral.mp (isAlgebraic_rat_cast_real qbs))
  have hα_irr : Irrational α := hi.mul_ratCast hqbs_ne
  have hα_expr : ∀ r : ℕ, ξ * ((b : ℝ) ^ (r + s) - (b : ℝ) ^ r) = α * (b : ℝ) ^ r := by
    intro r
    dsimp [α, qbs]
    push_cast
    rw [pow_add]
    ring
  let L_inf : Matrix (Fin 2) (Fin 2) ℝ := ![![1, 0], ![α, -1]]
  have hL_inf_alg : ∀ i j, IsAlgebraic ℚ (L_inf i j) := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [L_inf]
    · exact isAlgebraic_one
    · exact isAlgebraic_zero
    · exact hα_alg
    · exact isAlgebraic_iff_isIntegral.mpr (isAlgebraic_iff_isIntegral.mp isAlgebraic_one).neg
  have hL_inf_det : L_inf.det ≠ 0 := by
    rw [Matrix.det_fin_two]
    simp [L_inf]
  let L_p : ∀ p : ℕ, [Fact p.Prime] → Matrix (Fin 2) (Fin 2) ℚ_[p] := fun _ _ => 1
  have hL_p_alg : ∀ (p : ℕ) [Fact p.Prime], p ∈ b.primeFactors → ∀ i j, IsAlgebraic ℚ (L_p p i j) := by
    intro p _ _ i j
    by_cases hij : i = j
    · subst hij; simp [L_p, isAlgebraic_one]
    · simp [L_p, hij, isAlgebraic_zero]
  have hL_p_det : ∀ (p : ℕ) [Fact p.Prime], p ∈ b.primeFactors → (L_p p).det ≠ 0 := by
    intro p _ _
    simp [L_p]
  obtain ⟨T, hT_prop, hT_cover⟩ := SubspaceTheorem.p_adic_subspace_theorem
    2 (le_refl 2) b.primeFactors (fun p hp => Nat.prime_of_mem_primeFactors hp)
    L_inf hL_inf_alg hL_inf_det L_p hL_p_alg hL_p_det (ε / 2) (half_pos hε)
  have hb1 : (1 : ℝ) < b := by exact_mod_cast (show 1 < b by omega)
  have hb_pos : (0 : ℝ) < b := by positivity
  obtain ⟨R0, hR0⟩ : ∃ R0 : ℕ, ∀ r ≥ R0, |α| + 1 < (b : ℝ) ^ r := by
    obtain ⟨R0, hR0⟩ := pow_unbounded_of_one_lt (|α| + 1) hb1
    refine ⟨R0, fun r hr => lt_of_lt_of_le hR0 ?_⟩
    exact pow_le_pow_right₀ hb1.le hr
  let A : Set (ℕ × ℤ) := {rp : ℕ × ℤ | |ξ * ((b : ℝ) ^ (rp.1 + s) - (b : ℝ) ^ rp.1) - rp.2| <
    (b : ℝ) ^ (-(ε * ((rp.1 + s : ℕ) : ℝ)))}
  have hA_sub : A ⊆ {rp ∈ A | rp.1 < R0} ∪
      ⋃ V ∈ T, {rp ∈ A | R0 ≤ rp.1 ∧ ![(((b : ℤ) ^ rp.1 : ℤ) : ℚ), (rp.2 : ℚ)] ∈ V} := by
    intro rp hrp
    by_cases hr : rp.1 < R0
    · exact Or.inl ⟨hrp, hr⟩
    · refine Or.inr ?_
      have hr_ge : R0 ≤ rp.1 := Nat.le_of_not_lt hr
      have hrp_orig : |ξ * ((b : ℝ) ^ (rp.1 + s) - (b : ℝ) ^ rp.1) - rp.2| <
          (b : ℝ) ^ (-(ε * ((rp.1 + s : ℕ) : ℝ))) := hrp
      have hrp' : |α * (b : ℝ) ^ rp.1 - rp.2| < (b : ℝ) ^ (-(ε * (rp.1 : ℝ))) := by
        rw [hα_expr] at hrp_orig
        refine lt_of_lt_of_le hrp_orig ?_
        apply Real.rpow_le_rpow_of_exponent_le hb1.le
        have : (rp.1 : ℝ) ≤ ((rp.1 + s : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_right rp.1 s
        linarith [mul_le_mul_of_nonneg_left this hε.le]
      let x : Fin 2 → ℤ := ![((b : ℤ) ^ rp.1), rp.2]
      have hx0 : x ≠ 0 := by
        intro h0
        have h00 := congr_fun h0 0
        simp [x] at h00
        omega
      have hlt1 : (b : ℝ) ^ (-(ε * (rp.1 : ℝ))) ≤ 1 := rpow_neg_le_one hb (by positivity)
      have hp_le : |(rp.2 : ℝ)| ≤ (|α| + 1) * (b : ℝ) ^ rp.1 := by
        have htri : |(rp.2 : ℝ)| ≤ |α * (b : ℝ) ^ rp.1 - rp.2| + |α * (b : ℝ) ^ rp.1| := by
          calc |(rp.2 : ℝ)| = |-(α * (b : ℝ) ^ rp.1 - rp.2) + α * (b : ℝ) ^ rp.1| := by ring_nf
            _ ≤ |-(α * (b : ℝ) ^ rp.1 - rp.2)| + |α * (b : ℝ) ^ rp.1| := abs_add_le _ _
            _ = |α * (b : ℝ) ^ rp.1 - rp.2| + |α * (b : ℝ) ^ rp.1| := by rw [abs_neg]
        have hpow_nonneg : (0 : ℝ) ≤ (b : ℝ) ^ rp.1 := by positivity
        have h1 : (b : ℝ) ^ rp.1 ≥ 1 := one_le_pow₀ hb1.le
        rw [abs_mul, abs_of_nonneg hpow_nonneg] at htri
        linarith [hrp', hlt1]
      have hsup : ((Finset.univ.sup (fun i => (x i).natAbs) : ℕ) : ℝ) ≤ (|α| + 1) * (b : ℝ) ^ rp.1 := by
        obtain ⟨i, _, hi_eq⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty
          (fun j => (x j).natAbs)
        rw [hi_eq]
        fin_cases i
        · dsimp [x]
          rw [natAbs_cast_real, abs_of_nonneg (by positivity)]
          push_cast
          nlinarith [abs_nonneg α, pow_pos hb_pos rp.1]
        · dsimp [x]
          rw [natAbs_cast_real]
          exact hp_le
      have hsup_pos_nat : 0 < Finset.univ.sup (fun i => (x i).natAbs) := by
        have hx0_nat : 0 < (x 0).natAbs := by
          dsimp [x]
          rw [Int.natAbs_pos]
          exact pow_ne_zero _ (by omega)
        exact lt_of_lt_of_le hx0_nat (Finset.le_sup (f := fun i => (x i).natAbs) (Finset.mem_univ 0))
      have hsup_pos : (0 : ℝ) < (Finset.univ.sup (fun i => (x i).natAbs) : ℕ) := by
        exact_mod_cast hsup_pos_nat
      have hprod_inf : (∏ i : Fin 2, |L_inf.mulVec (fun j => (x j : ℝ)) i|) =
          (b : ℝ) ^ rp.1 * |α * (b : ℝ) ^ rp.1 - rp.2| := by
        rw [Fin.prod_univ_two]
        have h0 : L_inf.mulVec (fun j => (x j : ℝ)) 0 = (b : ℝ) ^ rp.1 := by
          simp [L_inf, Matrix.mulVec, dotProduct, Fin.sum_univ_two, x]
        have h1 : L_inf.mulVec (fun j => (x j : ℝ)) 1 = α * (b : ℝ) ^ rp.1 - rp.2 := by
          simp [L_inf, Matrix.mulVec, dotProduct, Fin.sum_univ_two, x]
          ring
        rw [h0, h1, abs_of_nonneg (by positivity)]
      have hprod_p : (∏ p : {p : ℕ // p ∈ b.primeFactors},
          haveI : Fact p.1.Prime := ⟨Nat.prime_of_mem_primeFactors p.2⟩
          ∏ i : Fin 2, ‖(L_p p.1).mulVec (fun j => (x j : ℚ_[p.1])) i‖) ≤ ((b : ℝ) ^ rp.1)⁻¹ := by
        have hsplit : ∀ p : {p : ℕ // p ∈ b.primeFactors},
            (haveI : Fact p.1.Prime := ⟨Nat.prime_of_mem_primeFactors p.2⟩
             ∏ i : Fin 2, ‖(L_p p.1).mulVec (fun j => (x j : ℚ_[p.1])) i‖) =
            (haveI : Fact p.1.Prime := ⟨Nat.prime_of_mem_primeFactors p.2⟩
             ‖((b ^ rp.1 : ℤ) : ℚ_[p.1])‖) *
            (haveI : Fact p.1.Prime := ⟨Nat.prime_of_mem_primeFactors p.2⟩
             ‖(rp.2 : ℚ_[p.1])‖) := by
          rintro ⟨p, hp⟩
          have : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hp⟩
          rw [Fin.prod_univ_two]
          simp [L_p, x]
        simp_rw [hsplit]
        rw [Finset.prod_mul_distrib, prod_primeFactors_padic_norm_pow b (by omega) rp.1]
        refine mul_le_of_le_one_right (by positivity) ?_
        refine Finset.prod_le_one (fun p _ => by positivity) fun p _ => ?_
        have : Fact p.1.Prime := ⟨Nat.prime_of_mem_primeFactors p.2⟩
        exact padic_norm_int_le_one p.1 rp.2
      have hineq : (∏ i : Fin 2, |L_inf.mulVec (fun j => (x j : ℝ)) i|) *
          (∏ p : {p : ℕ // p ∈ b.primeFactors},
            haveI : Fact p.1.Prime := ⟨Nat.prime_of_mem_primeFactors p.2⟩
            ∏ i : Fin 2, ‖(L_p p.1).mulVec (fun j => (x j : ℚ_[p.1])) i‖) <
          ((Finset.univ.sup (fun i => (x i).natAbs) : ℕ) : ℝ) ^ (-(ε / 2)) := by
        have hle1 : (∏ i : Fin 2, |L_inf.mulVec (fun j => (x j : ℝ)) i|) *
            (∏ p : {p : ℕ // p ∈ b.primeFactors},
              haveI : Fact p.1.Prime := ⟨Nat.prime_of_mem_primeFactors p.2⟩
              ∏ i : Fin 2, ‖(L_p p.1).mulVec (fun j => (x j : ℚ_[p.1])) i‖) ≤
            |α * (b : ℝ) ^ rp.1 - rp.2| := by
          rw [hprod_inf]
          have hmul := mul_le_mul_of_nonneg_left hprod_p
            (by positivity : 0 ≤ (b : ℝ) ^ rp.1 * |α * (b : ℝ) ^ rp.1 - rp.2|)
          calc (b : ℝ) ^ rp.1 * |α * (b : ℝ) ^ rp.1 - rp.2| *
                (∏ p : {p : ℕ // p ∈ b.primeFactors},
                  haveI : Fact p.1.Prime := ⟨Nat.prime_of_mem_primeFactors p.2⟩
                  ∏ i : Fin 2, ‖(L_p p.1).mulVec (fun j => (x j : ℚ_[p.1])) i‖)
              ≤ (b : ℝ) ^ rp.1 * |α * (b : ℝ) ^ rp.1 - rp.2| * ((b : ℝ) ^ rp.1)⁻¹ := hmul
            _ = |α * (b : ℝ) ^ rp.1 - rp.2| := by
                have hbn : (b : ℝ) ^ rp.1 ≠ 0 := by positivity
                field_simp
        have hlt2 : (b : ℝ) ^ (-(ε * (rp.1 : ℝ))) <
            ((Finset.univ.sup (fun i => (x i).natAbs) : ℕ) : ℝ) ^ (-(ε / 2)) := by
          have hbr_gt := hR0 rp.1 hr_ge
          have hpow2 : (|α| + 1) * (b : ℝ) ^ rp.1 < ((b : ℝ) ^ rp.1) ^ (2 : ℝ) := by
            rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, sq]
            exact mul_lt_mul_of_pos_right hbr_gt (by positivity)
          have hsup_lt : ((Finset.univ.sup (fun i => (x i).natAbs) : ℕ) : ℝ) <
              ((b : ℝ) ^ rp.1) ^ (2 : ℝ) := lt_of_le_of_lt hsup hpow2
          have hrpow_lt : (((b : ℝ) ^ rp.1) ^ (2 : ℝ)) ^ (-(ε / 2)) <
              ((Finset.univ.sup (fun i => (x i).natAbs) : ℕ) : ℝ) ^ (-(ε / 2)) :=
            Real.rpow_lt_rpow_of_neg hsup_pos hsup_lt (by linarith)
          have hsimp : (((b : ℝ) ^ rp.1) ^ (2 : ℝ)) ^ (-(ε / 2)) = (b : ℝ) ^ (-(ε * (rp.1 : ℝ))) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hb_pos.le, ← Real.rpow_mul hb_pos.le]
            congr 1; ring
          rwa [hsimp] at hrpow_lt
        exact lt_trans (hle1.trans_lt hrp') hlt2
      obtain ⟨V, hVT, hxV⟩ := hT_cover x hx0 hineq
      refine Set.mem_iUnion₂.mpr ⟨V, hVT, hrp, hr_ge, ?_⟩
      convert hxV using 1
      ext j; fin_cases j <;> simp [x]
  refine Set.Finite.subset ?_ hA_sub
  refine Set.Finite.union ?_ (T.finite_toSet.biUnion fun V hVT => ?_)
  · refine (finite_pair_nat_int_of_bound R0 ((|ξ| + 1) * (b : ℝ) ^ (R0 + s))).subset ?_
    rintro ⟨r, p⟩ ⟨hrp, hr⟩
    refine ⟨hr, ?_⟩
    have hrp' : |ξ * ((b : ℝ) ^ (r + s) - (b : ℝ) ^ r) - p| <
        (b : ℝ) ^ (-(ε * ((r + s : ℕ) : ℝ))) := hrp
    have hlt1 : (b : ℝ) ^ (-(ε * ((r + s : ℕ) : ℝ))) ≤ 1 := rpow_neg_le_one hb (by positivity)
    have h1 : |ξ * ((b : ℝ) ^ (r + s) - (b : ℝ) ^ r) - p| < 1 := lt_of_lt_of_le hrp' hlt1
    have hle_p := abs_int_le_of_approx hb h1
    have hbrs : (b : ℝ) ^ (r + s) ≤ (b : ℝ) ^ (R0 + s) := pow_le_pow_right₀ hb1.le (by omega)
    nlinarith [abs_nonneg ξ]
  · obtain ⟨a, ha0, haV⟩ := exists_nonzero_annihilator V (hT_prop V hVT)
    by_cases ha1 : a 1 = 0
    · have ha0_ne : a 0 ≠ 0 := by
        intro h0
        apply ha0; ext j; fin_cases j <;> assumption
      have hempty : {rp ∈ A | R0 ≤ rp.1 ∧ ![(((b : ℤ) ^ rp.1 : ℤ) : ℚ), (rp.2 : ℚ)] ∈ V} = ∅ := by
        ext ⟨r, p⟩
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨_, _, hV⟩
        have hsum := haV _ hV
        simp only [Fin.sum_univ_two, ha1, zero_mul, add_zero] at hsum
        dsimp at hsum
        have hpow_ne : (((b : ℤ) ^ r : ℤ) : ℚ) ≠ 0 := by
          exact_mod_cast pow_ne_zero r (by omega : (b : ℤ) ≠ 0)
        exact absurd (mul_eq_zero.mp hsum) (not_or.mpr ⟨ha0_ne, hpow_ne⟩)
      rw [hempty]; exact Set.finite_empty
    · let q : ℚ := -(a 0 / a 1)
      have hdiff_pos : 0 < |α - (q : ℝ)| := abs_pos.mpr (sub_ne_zero.mpr (hα_irr.ne_rat q))
      obtain ⟨R1, hR1⟩ := rpow_neg_lt_of_large hb hε hdiff_pos
      refine (finite_pair_nat_int_of_bound R1 ((|α| + 1) * (b : ℝ) ^ R1)).subset ?_
      rintro ⟨r, p⟩ ⟨hrp, _, hV⟩
      have hrp_orig : |ξ * ((b : ℝ) ^ (r + s) - (b : ℝ) ^ r) - p| <
          (b : ℝ) ^ (-(ε * ((r + s : ℕ) : ℝ))) := hrp
      have hsum := haV _ hV
      simp only [Fin.sum_univ_two] at hsum
      dsimp at hsum
      have hp_eq : (p : ℚ) = q * ((b : ℚ) ^ r) := by
        dsimp [q]
        field_simp [ha1]
        have hcast : (((b : ℤ) ^ r : ℤ) : ℚ) = (b : ℚ) ^ r := by push_cast; rfl
        rw [hcast] at hsum
        linarith
      have hp_real : (p : ℝ) = (q : ℝ) * (b : ℝ) ^ r := by
        have := congr_arg (Rat.cast : ℚ → ℝ) hp_eq
        simpa using this
      have hlt_b : (b : ℝ) ^ (-(ε * (r : ℝ))) > |α - (q : ℝ)| := by
        have hrp1 : |α * (b : ℝ) ^ r - p| < (b : ℝ) ^ (-(ε * ((r + s : ℕ) : ℝ))) := by
          simpa [hα_expr r] using hrp_orig
        have hrp2 : (b : ℝ) ^ (-(ε * ((r + s : ℕ) : ℝ))) ≤ (b : ℝ) ^ (-(ε * (r : ℝ))) := by
          apply Real.rpow_le_rpow_of_exponent_le hb1.le
          have : (r : ℝ) ≤ ((r + s : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_right r s
          linarith [mul_le_mul_of_nonneg_left this hε.le]
        have hbr1 : 1 ≤ (b : ℝ) ^ r := one_le_pow₀ hb1.le
        have hfac : |α * (b : ℝ) ^ r - p| = (b : ℝ) ^ r * |α - q| := by
          rw [hp_real, show α * (b : ℝ) ^ r - q * (b : ℝ) ^ r = (b : ℝ) ^ r * (α - q) by ring,
            abs_mul, abs_of_nonneg (by positivity)]
        have hge : |α - q| ≤ |α * (b : ℝ) ^ r - p| := by
          rw [hfac]
          exact le_mul_of_one_le_left (abs_nonneg _) hbr1
        linarith
      have hr_lt : r < R1 := by
        by_contra hnot
        have := hR1 r (Nat.le_of_not_lt hnot)
        linarith
      refine ⟨hr_lt, ?_⟩
      have hlt1 : (b : ℝ) ^ (-(ε * ((r + s : ℕ) : ℝ))) ≤ 1 := rpow_neg_le_one hb (by positivity)
      have hrp1 : |α * (b : ℝ) ^ r - (p : ℝ)| < 1 :=
        lt_of_lt_of_le (by simpa [hα_expr r] using hrp_orig) hlt1
      have htri : |(p : ℝ)| ≤ |α * (b : ℝ) ^ r - (p : ℝ)| + |α * (b : ℝ) ^ r| := by
        calc |(p : ℝ)| = |-(α * (b : ℝ) ^ r - (p : ℝ)) + α * (b : ℝ) ^ r| := by ring_nf
          _ ≤ _ := abs_add_le _ _
          _ = _ := by rw [abs_neg]
      have hpow_le : (b : ℝ) ^ r ≤ (b : ℝ) ^ R1 := pow_le_pow_right₀ hb1.le hr_lt.le
      have hpow1 : 1 ≤ (b : ℝ) ^ R1 := one_le_pow₀ hb1.le
      have hpow_nonneg : (0 : ℝ) ≤ (b : ℝ) ^ r := pow_nonneg hb_pos.le r
      rw [abs_mul, abs_of_nonneg hpow_nonneg] at htri
      dsimp
      nlinarith [abs_nonneg α]

theorem solution (ξ : ℝ) (hξ : IsAlgebraic ℚ ξ) (hi : Irrational ξ)
    (b : ℕ) (hb : 2 ≤ b) (ε : ℝ) (hε : 0 < ε) :
    {t : ℕ × ℕ × ℤ | 1 ≤ t.2.1 ∧
      |ξ * ((b : ℝ) ^ (t.1 + t.2.1) - (b : ℝ) ^ t.1) - t.2.2| <
        (b : ℝ) ^ (-(ε * ((t.1 + t.2.1 : ℕ) : ℝ)))}.Finite := by
  let L_inf : Matrix (Fin 3) (Fin 3) ℝ :=
    ![![1, 0, 0], ![0, 1, 0], ![ξ, -ξ, -1]]
  have hL_inf_alg : ∀ i j, IsAlgebraic ℚ (L_inf i j) := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [L_inf]
    · exact isAlgebraic_one
    · exact isAlgebraic_zero
    · exact isAlgebraic_zero
    · exact isAlgebraic_zero
    · exact isAlgebraic_one
    · exact isAlgebraic_zero
    · exact hξ
    · exact isAlgebraic_iff_isIntegral.mpr (isAlgebraic_iff_isIntegral.mp hξ).neg
    · exact isAlgebraic_iff_isIntegral.mpr (isAlgebraic_iff_isIntegral.mp isAlgebraic_one).neg
  have hL_inf_det : L_inf.det ≠ 0 := by
    rw [Matrix.det_fin_three]
    simp [L_inf]
  let L_p : ∀ p : ℕ, [Fact p.Prime] → Matrix (Fin 3) (Fin 3) ℚ_[p] := fun _ _ => 1
  have hL_p_alg : ∀ (p : ℕ) [Fact p.Prime], p ∈ b.primeFactors → ∀ i j, IsAlgebraic ℚ (L_p p i j) := by
    intro p _ _ i j
    by_cases hij : i = j
    · subst hij; simp [L_p, isAlgebraic_one]
    · simp [L_p, hij, isAlgebraic_zero]
  have hL_p_det : ∀ (p : ℕ) [Fact p.Prime], p ∈ b.primeFactors → (L_p p).det ≠ 0 := by
    intro p _ _
    simp [L_p]
  obtain ⟨T, hT_prop, hT_cover⟩ := SubspaceTheorem.p_adic_subspace_theorem
    3 (by omega) b.primeFactors (fun p hp => Nat.prime_of_mem_primeFactors hp)
    L_inf hL_inf_alg hL_inf_det L_p hL_p_alg hL_p_det (ε / 2) (half_pos hε)
  have hb1 : (1 : ℝ) < b := by exact_mod_cast (show 1 < b by omega)
  have hb_pos : (0 : ℝ) < b := by positivity
  obtain ⟨N0, hN0⟩ : ∃ N0 : ℕ, ∀ n ≥ N0, |ξ| + 1 < (b : ℝ) ^ n := by
    obtain ⟨N0, hN0⟩ := pow_unbounded_of_one_lt (|ξ| + 1) hb1
    refine ⟨N0, fun n hn => lt_of_lt_of_le hN0 ?_⟩
    exact pow_le_pow_right₀ hb1.le hn
  let A : Set (ℕ × ℕ × ℤ) := {t : ℕ × ℕ × ℤ | 1 ≤ t.2.1 ∧
    |ξ * ((b : ℝ) ^ (t.1 + t.2.1) - (b : ℝ) ^ t.1) - t.2.2| <
      (b : ℝ) ^ (-(ε * ((t.1 + t.2.1 : ℕ) : ℝ)))}
  have hA_sub : A ⊆ {t ∈ A | t.1 + t.2.1 < N0} ∪
      ⋃ V ∈ T, {t ∈ A | N0 ≤ t.1 + t.2.1 ∧
        ![(((b : ℤ) ^ (t.1 + t.2.1) : ℤ) : ℚ), (((b : ℤ) ^ t.1 : ℤ) : ℚ), (t.2.2 : ℚ)] ∈ V} := by
    intro t ht
    by_cases hN : t.1 + t.2.1 < N0
    · exact Or.inl ⟨ht, hN⟩
    · refine Or.inr ?_
      have hN_ge : N0 ≤ t.1 + t.2.1 := Nat.le_of_not_lt hN
      let x : Fin 3 → ℤ := ![(b : ℤ) ^ (t.1 + t.2.1), (b : ℤ) ^ t.1, t.2.2]
      have hx0 : x ≠ 0 := by
        intro h0
        have h00 := congr_fun h0 0
        simp [x] at h00
        omega
      have hlt1 : (b : ℝ) ^ (-(ε * ((t.1 + t.2.1 : ℕ) : ℝ))) ≤ 1 :=
        rpow_neg_le_one hb (by positivity)
      have h1 : |ξ * ((b : ℝ) ^ (t.1 + t.2.1) - (b : ℝ) ^ t.1) - t.2.2| < 1 :=
        lt_of_lt_of_le ht.2 hlt1
      have hp_le : |(t.2.2 : ℝ)| ≤ (|ξ| + 1) * (b : ℝ) ^ (t.1 + t.2.1) :=
        abs_int_le_of_approx hb h1
      have hsup : ((Finset.univ.sup (fun i => (x i).natAbs) : ℕ) : ℝ) ≤
          (|ξ| + 1) * (b : ℝ) ^ (t.1 + t.2.1) := by
        obtain ⟨i, _, hi_eq⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty
          (fun j => (x j).natAbs)
        rw [hi_eq]
        fin_cases i
        · dsimp [x]
          rw [natAbs_cast_real, abs_of_nonneg (by positivity)]
          push_cast
          nlinarith [abs_nonneg ξ, pow_pos hb_pos (t.1 + t.2.1)]
        · dsimp [x]
          rw [natAbs_cast_real, abs_of_nonneg (by positivity)]
          push_cast
          have hle : (b : ℝ) ^ t.1 ≤ (b : ℝ) ^ (t.1 + t.2.1) :=
            pow_le_pow_right₀ hb1.le (Nat.le_add_right t.1 t.2.1)
          nlinarith [abs_nonneg ξ, pow_pos hb_pos (t.1 + t.2.1)]
        · dsimp [x]
          rw [natAbs_cast_real]
          exact hp_le
      have hsup_pos_nat : 0 < Finset.univ.sup (fun i => (x i).natAbs) := by
        have hx0_nat : 0 < (x 0).natAbs := by
          dsimp [x]
          rw [Int.natAbs_pos]
          exact pow_ne_zero _ (by omega)
        exact lt_of_lt_of_le hx0_nat (Finset.le_sup (f := fun i => (x i).natAbs) (Finset.mem_univ 0))
      have hsup_pos : (0 : ℝ) < (Finset.univ.sup (fun i => (x i).natAbs) : ℕ) := by
        exact_mod_cast hsup_pos_nat
      have hprod_inf : (∏ i : Fin 3, |L_inf.mulVec (fun j => (x j : ℝ)) i|) =
          (b : ℝ) ^ (t.1 + t.2.1) * (b : ℝ) ^ t.1 *
            |ξ * ((b : ℝ) ^ (t.1 + t.2.1) - (b : ℝ) ^ t.1) - t.2.2| := by
        rw [Fin.prod_univ_three]
        have h0 : L_inf.mulVec (fun j => (x j : ℝ)) 0 = (b : ℝ) ^ (t.1 + t.2.1) := by
          simp [L_inf, Matrix.mulVec, dotProduct, Fin.sum_univ_three, x]
        have h1' : L_inf.mulVec (fun j => (x j : ℝ)) 1 = (b : ℝ) ^ t.1 := by
          simp [L_inf, Matrix.mulVec, dotProduct, Fin.sum_univ_three, x]
        have h2 : L_inf.mulVec (fun j => (x j : ℝ)) 2 =
            ξ * ((b : ℝ) ^ (t.1 + t.2.1) - (b : ℝ) ^ t.1) - t.2.2 := by
          simp [L_inf, Matrix.mulVec, dotProduct, Fin.sum_univ_three, x]
          ring
        rw [h0, h1', h2, abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
      have hprod_p : (∏ p : {p : ℕ // p ∈ b.primeFactors},
          haveI : Fact p.1.Prime := ⟨Nat.prime_of_mem_primeFactors p.2⟩
          ∏ i : Fin 3, ‖(L_p p.1).mulVec (fun j => (x j : ℚ_[p.1])) i‖) ≤
          ((b : ℝ) ^ (t.1 + t.2.1))⁻¹ * ((b : ℝ) ^ t.1)⁻¹ := by
        have hsplit : ∀ p : {p : ℕ // p ∈ b.primeFactors},
            (haveI : Fact p.1.Prime := ⟨Nat.prime_of_mem_primeFactors p.2⟩
             ∏ i : Fin 3, ‖(L_p p.1).mulVec (fun j => (x j : ℚ_[p.1])) i‖) =
            (haveI : Fact p.1.Prime := ⟨Nat.prime_of_mem_primeFactors p.2⟩
             ‖((b ^ (t.1 + t.2.1) : ℤ) : ℚ_[p.1])‖) *
            ((haveI : Fact p.1.Prime := ⟨Nat.prime_of_mem_primeFactors p.2⟩
             ‖((b ^ t.1 : ℤ) : ℚ_[p.1])‖) *
            (haveI : Fact p.1.Prime := ⟨Nat.prime_of_mem_primeFactors p.2⟩
             ‖(t.2.2 : ℚ_[p.1])‖)) := by
          rintro ⟨p, hp⟩
          have : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hp⟩
          rw [Fin.prod_univ_three]
          simp [L_p, x, mul_assoc]
        simp_rw [hsplit, Finset.prod_mul_distrib]
        rw [prod_primeFactors_padic_norm_pow b (by omega) (t.1 + t.2.1),
            prod_primeFactors_padic_norm_pow b (by omega) t.1]
        have hp_le1 : (∏ p : {p : ℕ // p ∈ b.primeFactors},
            haveI : Fact p.1.Prime := ⟨Nat.prime_of_mem_primeFactors p.2⟩
            ‖(t.2.2 : ℚ_[p.1])‖) ≤ 1 := by
          refine Finset.prod_le_one (fun p _ => by positivity) fun p _ => ?_
          have : Fact p.1.Prime := ⟨Nat.prime_of_mem_primeFactors p.2⟩
          exact padic_norm_int_le_one p.1 t.2.2
        have hmul_le := mul_le_mul_of_nonneg_left hp_le1 (by positivity : 0 ≤ ((b : ℝ) ^ t.1)⁻¹)
        rw [mul_one] at hmul_le
        exact mul_le_mul_of_nonneg_left hmul_le (by positivity)
      have hineq : (∏ i : Fin 3, |L_inf.mulVec (fun j => (x j : ℝ)) i|) *
          (∏ p : {p : ℕ // p ∈ b.primeFactors},
            haveI : Fact p.1.Prime := ⟨Nat.prime_of_mem_primeFactors p.2⟩
            ∏ i : Fin 3, ‖(L_p p.1).mulVec (fun j => (x j : ℚ_[p.1])) i‖) <
          ((Finset.univ.sup (fun i => (x i).natAbs) : ℕ) : ℝ) ^ (-(ε / 2)) := by
        have hle1 : (∏ i : Fin 3, |L_inf.mulVec (fun j => (x j : ℝ)) i|) *
            (∏ p : {p : ℕ // p ∈ b.primeFactors},
              haveI : Fact p.1.Prime := ⟨Nat.prime_of_mem_primeFactors p.2⟩
              ∏ i : Fin 3, ‖(L_p p.1).mulVec (fun j => (x j : ℚ_[p.1])) i‖) ≤
            |ξ * ((b : ℝ) ^ (t.1 + t.2.1) - (b : ℝ) ^ t.1) - t.2.2| := by
          rw [hprod_inf]
          have hmul := mul_le_mul_of_nonneg_left hprod_p
            (by positivity : 0 ≤ (b : ℝ) ^ (t.1 + t.2.1) * (b : ℝ) ^ t.1 *
              |ξ * ((b : ℝ) ^ (t.1 + t.2.1) - (b : ℝ) ^ t.1) - t.2.2|)
          calc _ ≤ (b : ℝ) ^ (t.1 + t.2.1) * (b : ℝ) ^ t.1 *
                |ξ * ((b : ℝ) ^ (t.1 + t.2.1) - (b : ℝ) ^ t.1) - t.2.2| *
                (((b : ℝ) ^ (t.1 + t.2.1))⁻¹ * ((b : ℝ) ^ t.1)⁻¹) := hmul
            _ = |ξ * ((b : ℝ) ^ (t.1 + t.2.1) - (b : ℝ) ^ t.1) - t.2.2| := by
                have hbn1 : (b : ℝ) ^ (t.1 + t.2.1) ≠ 0 := by positivity
                have hbn2 : (b : ℝ) ^ t.1 ≠ 0 := by positivity
                field_simp
        have hlt2 : (b : ℝ) ^ (-(ε * ((t.1 + t.2.1 : ℕ) : ℝ))) <
            ((Finset.univ.sup (fun i => (x i).natAbs) : ℕ) : ℝ) ^ (-(ε / 2)) := by
          have hbr_gt := hN0 (t.1 + t.2.1) hN_ge
          have hpow2 : (|ξ| + 1) * (b : ℝ) ^ (t.1 + t.2.1) < ((b : ℝ) ^ (t.1 + t.2.1)) ^ (2 : ℝ) := by
            rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, sq]
            exact mul_lt_mul_of_pos_right hbr_gt (by positivity)
          have hsup_lt : ((Finset.univ.sup (fun i => (x i).natAbs) : ℕ) : ℝ) <
              ((b : ℝ) ^ (t.1 + t.2.1)) ^ (2 : ℝ) := lt_of_le_of_lt hsup hpow2
          have hrpow_lt : (((b : ℝ) ^ (t.1 + t.2.1)) ^ (2 : ℝ)) ^ (-(ε / 2)) <
              ((Finset.univ.sup (fun i => (x i).natAbs) : ℕ) : ℝ) ^ (-(ε / 2)) :=
            Real.rpow_lt_rpow_of_neg hsup_pos hsup_lt (by linarith)
          have hsimp : (((b : ℝ) ^ (t.1 + t.2.1)) ^ (2 : ℝ)) ^ (-(ε / 2)) =
              (b : ℝ) ^ (-(ε * ((t.1 + t.2.1 : ℕ) : ℝ))) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hb_pos.le, ← Real.rpow_mul hb_pos.le]
            congr 1; ring
          rwa [hsimp] at hrpow_lt
        exact lt_trans (hle1.trans_lt ht.2) hlt2
      obtain ⟨V, hVT, hxV⟩ := hT_cover x hx0 hineq
      refine Set.mem_iUnion₂.mpr ⟨V, hVT, ht, hN_ge, ?_⟩
      convert hxV using 1
      ext j; fin_cases j <;> simp [x]
  refine Set.Finite.subset ?_ hA_sub
  refine Set.Finite.union ?_ (T.finite_toSet.biUnion fun V hVT => ?_)
  · have hsub : {t ∈ A | t.1 + t.2.1 < N0} ⊆
        (fun rp : ℕ × (ℕ × ℤ) => (rp.1, rp.2.1, rp.2.2)) ''
          ({r : ℕ | r < N0} ×ˢ {sp : ℕ × ℤ | sp.1 < N0 ∧ |(sp.2 : ℝ)| ≤ (|ξ| + 1) * (b : ℝ) ^ N0}) := by
      rintro ⟨r, s, p⟩ ⟨ht, hrN⟩
      dsimp at hrN
      refine ⟨(r, (s, p)), ⟨?_, ?_, ?_⟩, rfl⟩
      · dsimp; omega
      · dsimp; omega
      have hlt1 : (b : ℝ) ^ (-(ε * ((r + s : ℕ) : ℝ))) ≤ 1 := rpow_neg_le_one hb (by positivity)
      have h1 : |ξ * ((b : ℝ) ^ (r + s) - (b : ℝ) ^ r) - p| < 1 := lt_of_lt_of_le ht.2 hlt1
      have hle_p := abs_int_le_of_approx hb h1
      have hbrs : (b : ℝ) ^ (r + s) ≤ (b : ℝ) ^ N0 := pow_le_pow_right₀ hb1.le hrN.le
      nlinarith [abs_nonneg ξ]
    exact ((Set.finite_lt_nat N0).prod (finite_pair_nat_int_of_bound N0 ((|ξ| + 1) * (b : ℝ) ^ N0))).image
      _ |>.subset hsub
  · obtain ⟨a, ha0, haV⟩ := exists_nonzero_annihilator V (hT_prop V hVT)
    by_cases ha2 : a 2 = 0
    · by_cases ha0_zero : a 0 = 0
      · have ha1_ne : a 1 ≠ 0 := by
          intro h1
          apply ha0; ext j; fin_cases j <;> assumption
        have hempty : {t ∈ A | N0 ≤ t.1 + t.2.1 ∧
            ![(((b : ℤ) ^ (t.1 + t.2.1) : ℤ) : ℚ), (((b : ℤ) ^ t.1 : ℤ) : ℚ), (t.2.2 : ℚ)] ∈ V} = ∅ := by
          ext ⟨r, s, p⟩
          simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
          rintro ⟨_, _, hV⟩
          have hsum := haV _ hV
          simp only [Fin.sum_univ_three, ha0_zero, ha2, zero_mul, zero_add, add_zero] at hsum
          dsimp at hsum
          have hpow_ne : (((b : ℤ) ^ r : ℤ) : ℚ) ≠ 0 := by
            exact_mod_cast pow_ne_zero r (by omega : (b : ℤ) ≠ 0)
          exact absurd (mul_eq_zero.mp hsum) (not_or.mpr ⟨ha1_ne, hpow_ne⟩)
        rw [hempty]; exact Set.finite_empty
      · have ha0_ne : a 0 ≠ 0 := ha0_zero
        by_cases hs_ex : ∃ s0 : ℕ, 1 ≤ s0 ∧ a 0 * (b : ℚ) ^ s0 + a 1 = 0
        · obtain ⟨s0, hs0_pos, hs0_eq⟩ := hs_ex
          have hs0_uniq : ∀ s : ℕ, 1 ≤ s → a 0 * (b : ℚ) ^ s + a 1 = 0 → s = s0 := by
            intro s _ hs_eq
            have hpow_eq : (b : ℚ) ^ s = (b : ℚ) ^ s0 := by
              apply mul_left_cancel₀ ha0_ne
              linarith
            have hb1q : (1 : ℚ) < b := by exact_mod_cast (show 1 < b by omega)
            exact (pow_right_strictMono₀ hb1q).injective hpow_eq
          refine ((fixed_s_finite ξ hξ hi b hb ε hε s0 hs0_pos).image
            (fun rp : ℕ × ℤ => (rp.1, s0, rp.2))).subset ?_
          rintro ⟨r, s, p⟩ ⟨ht, _, hV⟩
          have hsum := haV _ hV
          simp only [Fin.sum_univ_three, ha2, zero_mul, add_zero] at hsum
          dsimp at hsum
          have hfact : (b : ℚ) ^ r * (a 0 * (b : ℚ) ^ s + a 1) = 0 := by
            have h1 : (((b : ℤ) ^ (r + s) : ℤ) : ℚ) = (b : ℚ) ^ r * (b : ℚ) ^ s := by
              push_cast; rw [pow_add]
            have h2 : (((b : ℤ) ^ r : ℤ) : ℚ) = (b : ℚ) ^ r := by push_cast; rfl
            rw [h1, h2] at hsum
            linarith
          have hbr_ne : (b : ℚ) ^ r ≠ 0 := pow_ne_zero r (by exact_mod_cast (show b ≠ 0 by omega))
          have hs_eq : a 0 * (b : ℚ) ^ s + a 1 = 0 := (mul_eq_zero.mp hfact).resolve_left hbr_ne
          have hs_is : s = s0 := hs0_uniq s ht.1 hs_eq
          subst hs_is
          exact ⟨(r, p), ht.2, rfl⟩
        · have hempty : {t ∈ A | N0 ≤ t.1 + t.2.1 ∧
              ![(((b : ℤ) ^ (t.1 + t.2.1) : ℤ) : ℚ), (((b : ℤ) ^ t.1 : ℤ) : ℚ), (t.2.2 : ℚ)] ∈ V} = ∅ := by
            ext ⟨r, s, p⟩
            simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
            rintro ⟨ht, _, hV⟩
            have hsum := haV _ hV
            simp only [Fin.sum_univ_three, ha2, zero_mul, add_zero] at hsum
            dsimp at hsum
            have hfact : (b : ℚ) ^ r * (a 0 * (b : ℚ) ^ s + a 1) = 0 := by
              have h1 : (((b : ℤ) ^ (r + s) : ℤ) : ℚ) = (b : ℚ) ^ r * (b : ℚ) ^ s := by
                push_cast; rw [pow_add]
              have h2 : (((b : ℤ) ^ r : ℤ) : ℚ) = (b : ℚ) ^ r := by push_cast; rfl
              rw [h1, h2] at hsum
              linarith
            have hbr_ne : (b : ℚ) ^ r ≠ 0 := pow_ne_zero r (by exact_mod_cast (show b ≠ 0 by omega))
            exact hs_ex ⟨s, ht.1, (mul_eq_zero.mp hfact).resolve_left hbr_ne⟩
          rw [hempty]; exact Set.finite_empty
    · let u : ℚ := -(a 0 / a 2)
      let v : ℚ := -(a 1 / a 2)
      have hxu : ξ - (u : ℝ) ≠ 0 := sub_ne_zero.mpr (hi.ne_rat u)
      have hxu_pos : 0 < |ξ - (u : ℝ)| := abs_pos.mpr hxu
      obtain ⟨S0, hS0⟩ : ∃ S0 : ℕ, (|ξ + (v : ℝ)| + 1) / |ξ - (u : ℝ)| < (b : ℝ) ^ S0 :=
        pow_unbounded_of_one_lt _ hb1
      have hs_fin : ∀ s : ℕ, s < S0 → 1 ≤ s →
          {rp : ℕ × ℤ | (rp.1, s, rp.2) ∈ A ∧
            ![(((b : ℤ) ^ (rp.1 + s) : ℤ) : ℚ), (((b : ℤ) ^ rp.1 : ℤ) : ℚ), (rp.2 : ℚ)] ∈ V}.Finite := by
        intro s _ _
        let qbs : ℚ := (b : ℚ) ^ s - 1
        have hqbs_ne : qbs ≠ 0 := by
          have hb1q : (1 : ℚ) < b := by exact_mod_cast (show 1 < b by omega)
          have : (1 : ℚ) < (b : ℚ) ^ s := one_lt_pow₀ hb1q (by omega)
          dsimp [qbs]; linarith
        let qs : ℚ := (u * (b : ℚ) ^ s + v) / qbs
        have hcs_pos : 0 < |ξ * (qbs : ℝ) - (u * (b : ℝ) ^ s + v)| := by
          have heq : ξ * (qbs : ℝ) - (u * (b : ℝ) ^ s + v) = (qbs : ℝ) * (ξ - (qs : ℝ)) := by
            dsimp [qs]
            have hqbs_r : (qbs : ℝ) ≠ 0 := by exact_mod_cast hqbs_ne
            push_cast
            field_simp [hqbs_r]
          rw [heq, abs_mul]
          have hqbs_r : (qbs : ℝ) ≠ 0 := by exact_mod_cast hqbs_ne
          exact mul_pos (abs_pos.mpr hqbs_r) (abs_pos.mpr (sub_ne_zero.mpr (hi.ne_rat qs)))
        obtain ⟨R1, hR1⟩ := rpow_neg_lt_of_large hb hε hcs_pos
        refine (finite_pair_nat_int_of_bound R1 ((|ξ| + 1) * (b : ℝ) ^ (R1 + s))).subset ?_
        rintro ⟨r, p⟩ ⟨ht, hV⟩
        have hsum := haV _ hV
        simp only [Fin.sum_univ_three] at hsum
        dsimp at hsum
        have hp_eq : (p : ℚ) = u * (b : ℚ) ^ (r + s) + v * (b : ℚ) ^ r := by
          dsimp [u, v]
          field_simp [ha2]
          have h1 : (((b : ℤ) ^ (r + s) : ℤ) : ℚ) = (b : ℚ) ^ (r + s) := by push_cast; rfl
          have h2 : (((b : ℤ) ^ r : ℤ) : ℚ) = (b : ℚ) ^ r := by push_cast; rfl
          rw [h1, h2] at hsum
          linarith
        have hp_real : (p : ℝ) = (u : ℝ) * (b : ℝ) ^ (r + s) + (v : ℝ) * (b : ℝ) ^ r := by
          have := congr_arg (Rat.cast : ℚ → ℝ) hp_eq
          simpa using this
        have hfac : |ξ * ((b : ℝ) ^ (r + s) - (b : ℝ) ^ r) - p| =
            (b : ℝ) ^ r * |ξ * (qbs : ℝ) - (u * (b : ℝ) ^ s + v)| := by
          rw [hp_real]
          dsimp [qbs]
          push_cast
          rw [pow_add]
          have hring : ξ * ((b : ℝ) ^ r * (b : ℝ) ^ s - (b : ℝ) ^ r) -
              ((u : ℝ) * ((b : ℝ) ^ r * (b : ℝ) ^ s) + (v : ℝ) * (b : ℝ) ^ r) =
              (b : ℝ) ^ r * (ξ * ((b : ℝ) ^ s - 1) - ((u : ℝ) * (b : ℝ) ^ s + v)) := by ring
          rw [hring, abs_mul, abs_of_nonneg (by positivity)]
        have hbr1 : 1 ≤ (b : ℝ) ^ r := one_le_pow₀ hb1.le
        have hge : |ξ * (qbs : ℝ) - (u * (b : ℝ) ^ s + v)| ≤
            |ξ * ((b : ℝ) ^ (r + s) - (b : ℝ) ^ r) - p| := by
          rw [hfac]
          exact le_mul_of_one_le_left (abs_nonneg _) hbr1
        have hlt_r : (b : ℝ) ^ (-(ε * (r : ℝ))) > |ξ * (qbs : ℝ) - (u * (b : ℝ) ^ s + v)| := by
          have hle_exp : (b : ℝ) ^ (-(ε * ((r + s : ℕ) : ℝ))) ≤ (b : ℝ) ^ (-(ε * (r : ℝ))) := by
            apply Real.rpow_le_rpow_of_exponent_le hb1.le
            have : (r : ℝ) ≤ ((r + s : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_right r s
            linarith [mul_le_mul_of_nonneg_left this hε.le]
          have ht2 : |ξ * ((b : ℝ) ^ (r + s) - (b : ℝ) ^ r) - p| <
              (b : ℝ) ^ (-(ε * ((r + s : ℕ) : ℝ))) := ht.2
          linarith
        have hr_lt : r < R1 := by
          by_contra hnot
          have := hR1 r (Nat.le_of_not_lt hnot)
          linarith
        refine ⟨hr_lt, ?_⟩
        have hlt1 : (b : ℝ) ^ (-(ε * ((r + s : ℕ) : ℝ))) ≤ 1 := rpow_neg_le_one hb (by positivity)
        have h1 : |ξ * ((b : ℝ) ^ (r + s) - (b : ℝ) ^ r) - p| < 1 := lt_of_lt_of_le ht.2 hlt1
        have hle_p := abs_int_le_of_approx hb h1
        have hbrs : (b : ℝ) ^ (r + s) ≤ (b : ℝ) ^ (R1 + s) := pow_le_pow_right₀ hb1.le (by omega)
        dsimp
        nlinarith [abs_nonneg ξ]
      have hsub_union : {t ∈ A | N0 ≤ t.1 + t.2.1 ∧
            ![(((b : ℤ) ^ (t.1 + t.2.1) : ℤ) : ℚ), (((b : ℤ) ^ t.1 : ℤ) : ℚ), (t.2.2 : ℚ)] ∈ V} ⊆
          ⋃ s ∈ Finset.Ico 1 S0, (fun rp : ℕ × ℤ => (rp.1, s, rp.2)) ''
            {rp : ℕ × ℤ | (rp.1, s, rp.2) ∈ A ∧
              ![(((b : ℤ) ^ (rp.1 + s) : ℤ) : ℚ), (((b : ℤ) ^ rp.1 : ℤ) : ℚ), (rp.2 : ℚ)] ∈ V} := by
        rintro ⟨r, s, p⟩ ⟨ht, _, hV⟩
        have hsum := haV _ hV
        simp only [Fin.sum_univ_three] at hsum
        dsimp at hsum
        have hp_eq : (p : ℚ) = u * (b : ℚ) ^ (r + s) + v * (b : ℚ) ^ r := by
          dsimp [u, v]
          field_simp [ha2]
          have h1 : (((b : ℤ) ^ (r + s) : ℤ) : ℚ) = (b : ℚ) ^ (r + s) := by push_cast; rfl
          have h2 : (((b : ℤ) ^ r : ℤ) : ℚ) = (b : ℚ) ^ r := by push_cast; rfl
          rw [h1, h2] at hsum
          linarith
        have hp_real : (p : ℝ) = (u : ℝ) * (b : ℝ) ^ (r + s) + (v : ℝ) * (b : ℝ) ^ r := by
          have := congr_arg (Rat.cast : ℚ → ℝ) hp_eq
          simpa using this
        have hlt1 : (b : ℝ) ^ (-(ε * ((r + s : ℕ) : ℝ))) ≤ 1 := rpow_neg_le_one hb (by positivity)
        have h1 : |ξ * ((b : ℝ) ^ (r + s) - (b : ℝ) ^ r) - p| < 1 := lt_of_lt_of_le ht.2 hlt1
        have hfac : |ξ * ((b : ℝ) ^ (r + s) - (b : ℝ) ^ r) - p| =
            (b : ℝ) ^ r * |(ξ - (u : ℝ)) * (b : ℝ) ^ s - (ξ + (v : ℝ))| := by
          rw [hp_real, pow_add]
          have hring : ξ * ((b : ℝ) ^ r * (b : ℝ) ^ s - (b : ℝ) ^ r) -
              ((u : ℝ) * ((b : ℝ) ^ r * (b : ℝ) ^ s) + (v : ℝ) * (b : ℝ) ^ r) =
              (b : ℝ) ^ r * ((ξ - (u : ℝ)) * (b : ℝ) ^ s - (ξ + (v : ℝ))) := by ring
          rw [hring, abs_mul, abs_of_nonneg (by positivity)]
        have hbr1 : 1 ≤ (b : ℝ) ^ r := one_le_pow₀ hb1.le
        have hlt_s : |(ξ - (u : ℝ)) * (b : ℝ) ^ s - (ξ + (v : ℝ))| < 1 := by
          rw [hfac] at h1
          nlinarith [abs_nonneg ((ξ - (u : ℝ)) * (b : ℝ) ^ s - (ξ + (v : ℝ)))]
        have htri_s : |(ξ - (u : ℝ)) * (b : ℝ) ^ s| < |ξ + (v : ℝ)| + 1 := by
          have := abs_sub_abs_le_abs_sub ((ξ - (u : ℝ)) * (b : ℝ) ^ s) (ξ + (v : ℝ))
          linarith
        have hpow_s_nonneg : (0 : ℝ) ≤ (b : ℝ) ^ s := pow_nonneg hb_pos.le s
        rw [abs_mul, abs_of_nonneg hpow_s_nonneg] at htri_s
        have hbs_lt : (b : ℝ) ^ s < (|ξ + (v : ℝ)| + 1) / |ξ - (u : ℝ)| :=
          (lt_div_iff₀' hxu_pos).mpr htri_s
        have hs_lt : s < S0 := (pow_lt_pow_iff_right₀ hb1).mp (hbs_lt.trans hS0)
        refine Set.mem_iUnion₂.mpr ⟨s, Finset.mem_Ico.mpr ⟨ht.1, hs_lt⟩, (r, p), ⟨ht, hV⟩, rfl⟩
      refine Set.Finite.subset ((Finset.Ico 1 S0).finite_toSet.biUnion fun s hs => ?_) hsub_union
      rw [Finset.mem_coe, Finset.mem_Ico] at hs
      exact Set.Finite.image _ (hs_fin s hs.2 hs.1)
