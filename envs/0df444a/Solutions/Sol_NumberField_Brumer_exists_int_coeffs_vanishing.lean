-- Prove2me | solution 1 for NumberField.Brumer.exists_int_coeffs_vanishing
-- status  : ACCEPTED   (prove)
-- author  : @ebayuser
-- created : 2026-10-04T09:30:37.809792+00:00
-- url     : https://prove2.me/submissions/997da8dc-88ce-43be-aaf7-2b0baeb08dbe

import Mathlib

open NumberField

namespace NumberField.Brumer.L1Aux

open Matrix in
attribute [local instance] Matrix.seminormedAddCommGroup in
theorem siegel {α β : Type*} [Fintype α] [Fintype β] (A : Matrix α β ℤ)
    (hβ : 0 < Fintype.card β) (hcard : 2 * Fintype.card α ≤ Fintype.card β) {B : ℝ}
    (hB : 1 ≤ B) (hA : ∀ a b, |(A a b : ℝ)| ≤ B) :
    ∃ t : β → ℤ, t ≠ 0 ∧ (∀ a, ∑ b, A a b * t b = 0) ∧
      ∀ b, |(t b : ℝ)| ≤ Fintype.card β * B := by
  classical
  rcases Nat.eq_zero_or_pos (Fintype.card α) with h0 | h0
  · obtain ⟨b0⟩ := Fintype.card_pos_iff.1 hβ
    refine ⟨Pi.single b0 1, ?_, ?_, ?_⟩
    · intro h
      have := congrFun h b0
      simp at this
    · intro a
      exact absurd (Fintype.card_pos_iff.2 ⟨a⟩) (by omega)
    · intro b
      have hb1 : |((Pi.single b0 (1 : ℤ) : β → ℤ) b : ℝ)| ≤ 1 := by
        by_cases hb : b = b0
        · subst hb; simp
        · simp [hb]
      have : (1 : ℝ) ≤ Fintype.card β * B := by
        have : (1 : ℝ) ≤ Fintype.card β := by exact_mod_cast hβ
        nlinarith
      linarith
  · have hlt : Fintype.card α < Fintype.card β := by omega
    obtain ⟨t, ht0, htA, htn⟩ := Int.Matrix.exists_ne_zero_int_vec_norm_le A hlt h0
    refine ⟨t, ht0, ?_, ?_⟩
    · intro a
      have := congrFun htA a
      simpa [Matrix.mulVec, dotProduct] using this
    · intro b
      have hAn : ‖A‖ ≤ B := by
        rw [Matrix.norm_le_iff (by linarith)]
        intro i j
        rw [Int.norm_eq_abs]
        exact hA i j
      have hbase : 1 ≤ (Fintype.card β : ℝ) * max 1 ‖A‖ := by
        have : (1 : ℝ) ≤ Fintype.card β := by exact_mod_cast hβ
        nlinarith [le_max_left 1 ‖A‖]
      have he : ((Fintype.card α : ℝ) / (Fintype.card β - Fintype.card α)) ≤ 1 := by
        have h1 : (2 * Fintype.card α : ℝ) ≤ Fintype.card β := by exact_mod_cast hcard
        have h2 : (0 : ℝ) < Fintype.card β - Fintype.card α := by
          have : (Fintype.card α : ℝ) < Fintype.card β := by exact_mod_cast hlt
          linarith
        rw [div_le_one h2]
        linarith
      calc |(t b : ℝ)| = ‖t b‖ := (Int.norm_eq_abs _).symm
        _ ≤ ‖t‖ := norm_le_pi_norm t b
        _ ≤ _ := htn
        _ ≤ ((Fintype.card β : ℝ) * max 1 ‖A‖) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hbase he
        _ = (Fintype.card β : ℝ) * max 1 ‖A‖ := Real.rpow_one _
        _ ≤ Fintype.card β * B := by
            gcongr
            exact max_le hB hAn

variable (L : Type*) [Field L] [NumberField L]

/-- The reindexed integral basis. -/
noncomputable def nb [DecidableEq (L →+* ℂ)] : Module.Basis (L →+* ℂ) ℤ (𝓞 L) :=
  (RingOfIntegers.basis L).reindex (equivReindex L).symm

theorem coord_bound [DecidableEq (L →+* ℂ)] :
    ∃ c₀ : ℝ, 0 ≤ c₀ ∧ ∀ (x : 𝓞 L) (r : L →+* ℂ),
      |((nb L).repr x r : ℝ)| ≤ c₀ * house (algebraMap (𝓞 L) L x) := by
  have key : ∃ c : ℝ, ∀ (x : 𝓞 L) (r : L →+* ℂ),
      |((nb L).repr x r : ℝ)| ≤ c * house (algebraMap (𝓞 L) L x) := by
    exact ⟨_, fun x r => by
      have remark := NumberField.house.basis_repr_norm_le_const_mul_house L x r
      simp only [Module.Basis.repr_reindex, Finsupp.mapDomain_equiv_apply,
        integralBasis_repr_apply, eq_intCast, Rat.cast_intCast,
          Complex.norm_intCast] at remark
      simp only [nb, Module.Basis.repr_reindex, Finsupp.mapDomain_equiv_apply]
      exact remark⟩
  obtain ⟨c, hc⟩ := key
  refine ⟨max 0 c, le_max_left _ _, fun x r => (hc x r).trans ?_⟩
  exact mul_le_mul_of_nonneg_right (le_max_right _ _) (house_nonneg _)

theorem int_mult {n : ℕ} (a c : Fin n → L) :
    ∃ y : ℤ, y ≠ 0 ∧ (∀ i, IsIntegral ℤ ((y : L) * a i)) ∧ ∀ i, IsIntegral ℤ ((y : L) * c i) := by
  classical
  obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ (L := L)
    (Finset.univ.image a ∪ Finset.univ.image c)
  refine ⟨y, hy0, fun i => ?_, fun i => ?_⟩
  · have := hy (a i) (by simp)
    simpa [zsmul_eq_mul] using this
  · have := hy (c i) (by simp)
    simpa [zsmul_eq_mul] using this

/-- The integral element `D^e * α(m, ℓ, λ)`, computed inside `𝓞 L`. -/
noncomputable def beta {n : ℕ} (y : ℤ) (a' c' : Fin n → 𝓞 L) (k : Fin n) (N q ℓ : ℕ)
    (m : Fin n → ℕ) (lam : Fin n → Fin N) : 𝓞 L :=
  (∏ i, a' i ^ (lam i : ℕ) * (y : 𝓞 L) ^ (N - lam i)) ^ (q * ℓ) *
    ∏ i, (c' k * ((lam i : ℕ) : 𝓞 L) - c' i * ((lam k : ℕ) : 𝓞 L)) ^ m i

omit [NumberField L] in
theorem beta_eq {n : ℕ} (y : ℤ) (a c : Fin n → L) (a' c' : Fin n → 𝓞 L) (k : Fin n)
    (N q ℓ : ℕ) (m : Fin n → ℕ) (lam : Fin n → Fin N)
    (ha : ∀ i, algebraMap (𝓞 L) L (a' i) = y * a i)
    (hc : ∀ i, algebraMap (𝓞 L) L (c' i) = y * c i) :
    algebraMap (𝓞 L) L (beta L y a' c' k N q ℓ m lam) =
      (y : L) ^ (n * N * (q * ℓ) + ∑ i, m i) *
        ((∏ i, a i ^ (lam i : ℕ)) ^ (q * ℓ) *
          ∏ i, (c k * ((lam i : ℕ) : L) - c i * ((lam k : ℕ) : L)) ^ m i) := by
  simp only [beta, map_mul, map_pow, map_prod, map_sub, map_natCast, map_intCast, ha, hc]
  have h1 : ∏ i, ((y : L) * a i) ^ (lam i : ℕ) * (y : L) ^ (N - lam i) =
      (y : L) ^ (n * N) * ∏ i, a i ^ (lam i : ℕ) := by
    rw [show (y : L) ^ (n * N) = ∏ _i : Fin n, (y : L) ^ N by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul, mul_comm]]
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    have hle : (lam i : ℕ) + (N - lam i) = N := by have := (lam i).2; omega
    rw [show (y : L) ^ N = (y : L) ^ (lam i : ℕ) * (y : L) ^ (N - lam i) by
      rw [← pow_add, hle], mul_pow]
    ring
  have h2 : ∏ i, ((y : L) * c k * ((lam i : ℕ) : L) - (y : L) * c i * ((lam k : ℕ) : L)) ^ m i =
      (y : L) ^ (∑ i, m i) * ∏ i, (c k * ((lam i : ℕ) : L) - c i * ((lam k : ℕ) : L)) ^ m i := by
    rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [show (y : L) * c k * ((lam i : ℕ) : L) - (y : L) * c i * ((lam k : ℕ) : L) =
      (y : L) * (c k * ((lam i : ℕ) : L) - c i * ((lam k : ℕ) : L)) by ring, mul_pow]
  rw [h1, h2, mul_pow, ← pow_mul, pow_add]
  ring

theorem house_prod_le' {ι : Type*} (s : Finset ι) (f : ι → L) :
    house (∏ i ∈ s, f i) ≤ ∏ i ∈ s, house (f i) := by
  simpa [house, map_prod] using Finset.norm_prod_le s (fun i => canonicalEmbedding L (f i))

theorem house_sub_le (x z : L) : house (x - z) ≤ house x + house z := by
  rw [sub_eq_add_neg]
  refine (house_add_le _ _).trans ?_
  simp [house, map_neg, norm_neg]

theorem house_beta {n : ℕ} (y : ℤ) (a' c' : Fin n → 𝓞 L) (k : Fin n) (N q ℓ : ℕ)
    (m : Fin n → ℕ) (lam : Fin n → Fin N) (A₁ Hc : ℝ) (hy : |(y : ℝ)| ≤ A₁)
    (ha : ∀ i, house (algebraMap (𝓞 L) L (a' i)) ≤ A₁)
    (hc : ∀ i, house (algebraMap (𝓞 L) L (c' i)) ≤ Hc) (hHc : 0 ≤ Hc) :
    house (algebraMap (𝓞 L) L (beta L y a' c' k N q ℓ m lam)) ≤
      (A₁ ^ (n * N)) ^ (q * ℓ) * (2 * Hc * N) ^ (∑ i, m i) := by
  have hA0 : 0 ≤ A₁ := (abs_nonneg _).trans hy
  simp only [beta, map_mul, map_pow, map_prod, map_sub, map_natCast, map_intCast]
  refine (house_mul_le _ _).trans (mul_le_mul ?_ ?_ (house_nonneg _) (by positivity))
  · refine (house_pow_le _ _).trans (pow_le_pow_left₀ (house_nonneg _) ?_ _)
    refine (house_prod_le' L _ _).trans ?_
    rw [show A₁ ^ (n * N) = ∏ _i : Fin n, A₁ ^ N by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul, mul_comm]]
    refine Finset.prod_le_prod (fun i _ => house_nonneg _) fun i _ => ?_
    have hle : (lam i : ℕ) + (N - lam i) = N := by have := (lam i).2; omega
    rw [show A₁ ^ N = A₁ ^ (lam i : ℕ) * A₁ ^ (N - lam i) by rw [← pow_add, hle]]
    refine (house_mul_le _ _).trans (mul_le_mul ?_ ?_ (house_nonneg _) (by positivity))
    · exact (house_pow_le _ _).trans (pow_le_pow_left₀ (house_nonneg _) (ha i) _)
    · refine (house_pow_le _ _).trans (pow_le_pow_left₀ (house_nonneg _) ?_ _)
      rw [house_intCast]
      simpa using hy
  · refine (house_prod_le' L _ _).trans ?_
    rw [← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_le_prod (fun i _ => house_nonneg _) fun i _ => ?_
    refine (house_pow_le _ _).trans (pow_le_pow_left₀ (house_nonneg _) ?_ _)
    have hN : ∀ j : Fin n, ((lam j : ℕ) : ℝ) ≤ N := fun j => by exact_mod_cast (lam j).2.le
    have hm : ∀ j j' : Fin n, house (algebraMap (𝓞 L) L (c' j) * ((lam j' : ℕ) : L)) ≤ Hc * N := by
      intro j j'
      rw [mul_comm, house_nat_mul]
      rw [mul_comm]
      exact mul_le_mul (hc j) (hN j') (Nat.cast_nonneg _) hHc
    refine (house_sub_le L _ _).trans ?_
    linarith [hm k i, hm i k]

theorem card_M {n S : ℕ} (k : Fin n) :
    Fintype.card {m : Fin n → Fin (S + 1) // m k = 0 ∧ ∑ i, (m i : ℕ) ≤ S} ≤ (S + 1) ^ (n - 1) := by
  classical
  calc _ ≤ Fintype.card ({i // i ≠ k} → Fin (S + 1)) :=
        Fintype.card_le_of_injective (fun m i => m.1 i.1) (by
          intro m m' h
          apply Subtype.ext
          funext i
          by_cases hi : i = k
          · subst hi; rw [m.2.1, m'.2.1]
          · exact congrFun h ⟨i, hi⟩)
    _ = _ := by simp

end NumberField.Brumer.L1Aux

open NumberField.Brumer.L1Aux in
theorem solution {L : Type*} [Field L] [NumberField L] (n : ℕ)
    (a c : Fin n → L) (k : Fin n) (q : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ N S H : ℕ, 0 < N →
      2 * Module.finrank ℚ L * (S + 1) ^ (n - 1) * H ≤ N ^ n →
      ∃ P : (Fin n → Fin N) → ℤ, P ≠ 0 ∧
        (∀ lam, |(P lam : ℝ)| ≤ (N : ℝ) ^ n * C ^ (N * H + S) * (N : ℝ) ^ S) ∧
        ∀ m : Fin n → ℕ, ∑ i, m i ≤ S → ∀ ℓ : ℕ, 1 ≤ ℓ → ℓ ≤ H →
          ∑ lam : Fin n → Fin N, (P lam : L) * (∏ i, a i ^ (lam i : ℕ)) ^ (q * ℓ) *
            ∏ i, (c k * ((lam i : ℕ) : L) - c i * ((lam k : ℕ) : L)) ^ m i = 0 := by
  classical
  obtain ⟨y, hy0, hya, hyc⟩ := int_mult L a c
  let a' : Fin n → 𝓞 L := fun i => ⟨(y : L) * a i, hya i⟩
  let c' : Fin n → 𝓞 L := fun i => ⟨(y : L) * c i, hyc i⟩
  have ha' : ∀ i, algebraMap (𝓞 L) L (a' i) = y * a i := fun i => rfl
  have hc' : ∀ i, algebraMap (𝓞 L) L (c' i) = y * c i := fun i => rfl
  obtain ⟨c₀, hc₀, hcoord⟩ := coord_bound L
  set A₁ : ℝ := 1 + |(y : ℝ)| + ∑ i, house (algebraMap (𝓞 L) L (a' i)) with hA₁def
  set Hc : ℝ := 1 + ∑ i, house (algebraMap (𝓞 L) L (c' i)) with hHcdef
  have hsa : 0 ≤ ∑ i, house (algebraMap (𝓞 L) L (a' i)) :=
    Finset.sum_nonneg fun i _ => house_nonneg _
  have hsc : 0 ≤ ∑ i, house (algebraMap (𝓞 L) L (c' i)) :=
    Finset.sum_nonneg fun i _ => house_nonneg _
  have hA₁1 : 1 ≤ A₁ := by have := abs_nonneg (y : ℝ); linarith
  have hyA : |(y : ℝ)| ≤ A₁ := by linarith
  have haA : ∀ i, house (algebraMap (𝓞 L) L (a' i)) ≤ A₁ := fun i => by
    have := Finset.single_le_sum (f := fun j => house (algebraMap (𝓞 L) L (a' j)))
      (fun j _ => house_nonneg _) (Finset.mem_univ i)
    have := abs_nonneg (y : ℝ)
    linarith
  have hHc1 : 1 ≤ Hc := by linarith
  have hcH : ∀ i, house (algebraMap (𝓞 L) L (c' i)) ≤ Hc := fun i => by
    have := Finset.single_le_sum (f := fun j => house (algebraMap (𝓞 L) L (c' j)))
      (fun j _ => house_nonneg _) (Finset.mem_univ i)
    linarith
  have hX1 : 1 ≤ (1 + c₀) * A₁ ^ (n * q) :=
    one_le_mul_of_one_le_of_one_le (by linarith) (one_le_pow₀ hA₁1)
  have hY1 : 1 ≤ 2 * Hc := by linarith
  set C : ℝ := (1 + c₀) * A₁ ^ (n * q) * (2 * Hc) with hCdef
  have hXC : (1 + c₀) * A₁ ^ (n * q) ≤ C := le_mul_of_one_le_right (by linarith) hY1
  have hYC : 2 * Hc ≤ C := le_mul_of_one_le_left (by linarith) hX1
  have hC1 : 1 ≤ C := one_le_mul_of_one_le_of_one_le hX1 hY1
  refine ⟨C, hC1, ?_⟩
  intro N S H hN hcount
  let M := {m : Fin n → Fin (S + 1) // m k = 0 ∧ ∑ i, (m i : ℕ) ≤ S}
  let Amat : Matrix (M × Fin H × (L →+* ℂ)) (Fin n → Fin N) ℤ := fun e lam =>
    (nb L).repr (beta L y a' c' k N q (e.2.1.val + 1) (fun i => (e.1.1 i : ℕ)) lam) e.2.2
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hB : 1 ≤ C ^ (N * H + S) * (N : ℝ) ^ S :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ hC1) (one_le_pow₀ hNr)
  have hent : ∀ e lam, |(Amat e lam : ℝ)| ≤ C ^ (N * H + S) * (N : ℝ) ^ S := by
    rintro ⟨mm, ℓ, r⟩ lam
    have hℓ := ℓ.2
    have hNH : N * H ≠ 0 := Nat.mul_ne_zero (by omega) (by omega)
    have h1 := hcoord (beta L y a' c' k N q (ℓ.val + 1) (fun i => (mm.1 i : ℕ)) lam) r
    have h2 := house_beta L y a' c' k N q (ℓ.val + 1) (fun i => (mm.1 i : ℕ)) lam A₁ Hc hyA
      haA hcH (by linarith)
    refine h1.trans ?_
    have e1 : c₀ ≤ (1 + c₀) ^ (N * H) := (by linarith : c₀ ≤ 1 + c₀).trans
      (le_self_pow₀ (by linarith) hNH)
    have e2 : (A₁ ^ (n * N)) ^ (q * (ℓ.val + 1)) ≤ (A₁ ^ (n * q)) ^ (N * H) := by
      rw [← pow_mul, ← pow_mul]
      exact pow_le_pow_right₀ hA₁1 (by
        rw [show n * N * (q * (ℓ.val + 1)) = n * q * (N * (ℓ.val + 1)) by ring]
        exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (by omega)))
    have e3 : (2 * Hc * N) ^ (∑ i, (mm.1 i : ℕ)) ≤ (2 * Hc) ^ S * (N : ℝ) ^ S := by
      rw [← mul_pow]
      exact pow_le_pow_right₀ (one_le_mul_of_one_le_of_one_le hY1 hNr) mm.2.2
    calc c₀ * house _ ≤ c₀ * ((A₁ ^ (n * N)) ^ (q * (ℓ.val + 1)) *
          (2 * Hc * N) ^ (∑ i, (mm.1 i : ℕ))) := mul_le_mul_of_nonneg_left h2 hc₀
      _ ≤ (1 + c₀) ^ (N * H) * ((A₁ ^ (n * q)) ^ (N * H) * ((2 * Hc) ^ S * (N : ℝ) ^ S)) := by
          gcongr
      _ = ((1 + c₀) * A₁ ^ (n * q)) ^ (N * H) * (2 * Hc) ^ S * (N : ℝ) ^ S := by
          rw [mul_pow (1 + c₀) (A₁ ^ (n * q))]; ring
      _ ≤ C ^ (N * H) * C ^ S * (N : ℝ) ^ S := by gcongr
      _ = C ^ (N * H + S) * (N : ℝ) ^ S := by rw [pow_add]
  have hcardβ : Fintype.card (Fin n → Fin N) = N ^ n := by simp
  have hβ : 0 < Fintype.card (Fin n → Fin N) := by rw [hcardβ]; positivity
  have hcard : 2 * Fintype.card (M × Fin H × (L →+* ℂ)) ≤ Fintype.card (Fin n → Fin N) := by
    rw [hcardβ, Fintype.card_prod, Fintype.card_prod, Fintype.card_fin, Embeddings.card]
    calc 2 * (Fintype.card M * (H * Module.finrank ℚ L))
        ≤ 2 * ((S + 1) ^ (n - 1) * (H * Module.finrank ℚ L)) := by
          gcongr
          exact card_M k
      _ = 2 * Module.finrank ℚ L * (S + 1) ^ (n - 1) * H := by ring
      _ ≤ N ^ n := hcount
  obtain ⟨t, ht0, hteq, htb⟩ := siegel Amat hβ hcard hB hent
  refine ⟨t, ht0, ?_, ?_⟩
  · intro lam
    have := htb lam
    rw [hcardβ] at this
    push_cast at this
    linarith
  · intro m hm ℓ hℓ1 hℓH
    by_cases hmk : m k = 0
    · obtain ⟨ℓ0, rfl⟩ : ∃ ℓ0, ℓ = ℓ0 + 1 := ⟨ℓ - 1, by omega⟩
      have hmi : ∀ i, m i < S + 1 := fun i => by
        have := Finset.single_le_sum (f := m) (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
        omega
      let mm : M := ⟨fun i => ⟨m i, hmi i⟩, Fin.ext (by simpa using hmk), hm⟩
      have key : ∀ r, ∑ lam, Amat (mm, ⟨ℓ0, by omega⟩, r) lam * t lam = 0 := fun r => hteq _
      have hsum : ∑ lam, t lam • beta L y a' c' k N q (ℓ0 + 1) m lam = 0 := by
        apply (nb L).ext_elem
        intro r
        simp only [map_sum, map_zsmul, Finsupp.coe_finsetSum, Finset.sum_apply,
          Finsupp.smul_apply, smul_eq_mul, map_zero, Finsupp.coe_zero, Pi.zero_apply]
        rw [← key r]
        refine Finset.sum_congr rfl fun lam _ => ?_
        rw [mul_comm]
      have h2 := congrArg (algebraMap (𝓞 L) L) hsum
      simp only [map_sum, map_zsmul, map_zero, beta_eq L y a c a' c' k N q _ m _ ha' hc'] at h2
      have hy' : (y : L) ^ (n * N * (q * (ℓ0 + 1)) + ∑ i, m i) ≠ 0 :=
        pow_ne_zero _ (Int.cast_ne_zero.2 hy0)
      have h3 : (y : L) ^ (n * N * (q * (ℓ0 + 1)) + ∑ i, m i) *
          ∑ lam : Fin n → Fin N, (t lam : L) * (∏ i, a i ^ (lam i : ℕ)) ^ (q * (ℓ0 + 1)) *
            ∏ i, (c k * ((lam i : ℕ) : L) - c i * ((lam k : ℕ) : L)) ^ m i = 0 := by
        rw [Finset.mul_sum, ← h2]
        refine Finset.sum_congr rfl fun lam _ => ?_
        rw [zsmul_eq_mul]
        ring
      exact (mul_eq_zero.1 h3).resolve_left hy'
    · apply Finset.sum_eq_zero
      intro lam _
      rw [Finset.prod_eq_zero
        (f := fun i => (c k * ((lam i : ℕ) : L) - c i * ((lam k : ℕ) : L)) ^ m i)
        (Finset.mem_univ k) (by simp [hmk]), mul_zero]
