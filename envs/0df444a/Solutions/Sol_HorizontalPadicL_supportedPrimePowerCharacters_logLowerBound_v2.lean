-- Prove2me | solution 1 for HorizontalPadicL.supportedPrimePowerCharacters_logLowerBound_v2
-- status  : ACCEPTED   (prove)
-- author  : @davidloeffler
-- created : 2026-09-25T14:11:22.625278+00:00
-- url     : https://prove2.me/submissions/daa3aa53-b5b2-4bdf-a38d-1c5f66291472

import Definitions.Def_KN_PrimePowerPropagationV2
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.MulChar.Duality
import Mathlib.RingTheory.IntegralDomain
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace HorizontalPadicL.LogLowerBound

open HorizontalPadicL Filter Real

/-! ### Chebyshev-type bounds -/

/-- Eventually `log y ≤ ε y`. -/
lemma eventually_log_le_mul {ε : ℝ} (hε : 0 < ε) : ∀ᶠ y : ℝ in atTop, log y ≤ ε * y := by
  filter_upwards [Real.isLittleO_log_id_atTop.bound hε, eventually_ge_atTop 1] with y hy hy1
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (log_nonneg hy1),
    abs_of_nonneg (by simp only [id]; linarith)] at hy
  simpa using hy

/-- Eventually `K ≤ y / log y`. -/
lemma eventually_le_div_log (K : ℝ) : ∀ᶠ y : ℝ in atTop, K ≤ y / log y := by
  filter_upwards [eventually_log_le_mul (ε := 1 / (|K| + 1)) (by positivity),
    eventually_ge_atTop 3] with y hy hy3
  have hlog : 0 < log y := log_pos (by linarith)
  rw [le_div_iff₀ hlog]
  have hK : K ≤ |K| + 1 := by linarith [le_abs_self K]
  have : log y * (|K| + 1) ≤ y := by
    have h := mul_le_mul_of_nonneg_right hy (by positivity : (0 : ℝ) ≤ |K| + 1)
    rwa [mul_comm (1 / (|K| + 1)) y, mul_assoc, one_div_mul_cancel (by positivity),
      mul_one] at h
  nlinarith

/-- A Chebyshev lower bound for `π`. -/
lemma eventually_primeCounting_ge :
    ∀ᶠ y : ℝ in atTop, log 2 / 2 * y / log y ≤ (Nat.primeCounting ⌊y⌋₊ : ℝ) := by
  have h2 : 0 < log 2 := log_pos one_lt_two
  have hlog : ∀ᶠ y : ℝ in atTop, log (y + 2) ≤ log 2 / 8 * (y + 2) :=
    (tendsto_atTop_add_const_right atTop 2 tendsto_id).eventually
      (eventually_log_le_mul (by positivity))
  filter_upwards [hlog, eventually_ge_atTop 4] with y hy hy4
  have hlogy : 0 < log y := log_pos (by linarith)
  refine le_trans ?_ (Chebyshev.pi_ge' (by linarith))
  refine div_le_div_of_nonneg_right ?_ hlogy.le
  nlinarith

/-! ### Auxiliary prime indices -/

section Indices

variable (ℓ : ℕ → ℕ) (hinj : Function.Injective ℓ) (A : Finset ℕ)

/-- Indices outside `A` whose prime is at most `y`. -/
def idx (y : ℝ) : Finset ℕ :=
  ((Finset.range (⌊y⌋₊ + 1)).preimage ℓ hinj.injOn).filter (· ∉ A)

variable {ℓ hinj A}

lemma mem_idx {y : ℝ} {i : ℕ} : i ∈ idx ℓ hinj A y ↔ ℓ i ≤ ⌊y⌋₊ ∧ i ∉ A := by
  simp [idx]

lemma mem_idx_iff_real {y : ℝ} (hy : 0 ≤ y) {i : ℕ} :
    i ∈ idx ℓ hinj A y ↔ (ℓ i : ℝ) ≤ y ∧ i ∉ A := by
  rw [mem_idx, Nat.le_floor_iff hy]

lemma idx_mono {y z : ℝ} (h : y ≤ z) : idx ℓ hinj A y ⊆ idx ℓ hinj A z := by
  intro i hi
  rw [mem_idx] at hi ⊢
  exact ⟨hi.1.trans (Nat.floor_le_floor h), hi.2⟩

lemma card_idx_le (hprime : ∀ n, (ℓ n).Prime) (y : ℝ) :
    (idx ℓ hinj A y).card ≤ Nat.primeCounting ⌊y⌋₊ := by
  rw [Nat.primeCounting_eq_primeCounting'_succ, ← Nat.primesBelow_card_eq_primeCounting']
  refine Finset.card_le_card_of_injOn ℓ (fun i hi => ?_) hinj.injOn
  rw [Finset.mem_coe, mem_idx] at hi
  simp only [Finset.mem_coe, Nat.primesBelow, Finset.mem_filter, Finset.mem_range]
  exact ⟨Nat.lt_succ_of_le hi.1, hprime i⟩

/-- A Chebyshev upper bound for the auxiliary prime counts. -/
lemma eventually_card_idx_le (hprime : ∀ n, (ℓ n).Prime) :
    ∀ᶠ y : ℝ in atTop, ((idx ℓ hinj A y).card : ℝ) ≤ (log 4 + 1) * y / log y := by
  filter_upwards [Chebyshev.eventually_primeCounting_le one_pos] with y hy
  exact le_trans (by exact_mod_cast card_idx_le hprime y) hy

/-- Natural density and Chebyshev give a lower bound for the auxiliary prime counts. -/
lemma eventually_card_idx_ge (hprime : ∀ n, (ℓ n).Prime) {δ : ℝ} (hδ : 0 < δ)
    (hdensity : HasPrimeNaturalDensity (Set.range ℓ) δ) :
    ∀ᶠ y : ℝ in atTop, δ * log 2 / 8 * y / log y ≤ ((idx ℓ hinj A y).card : ℝ) := by
  classical
  have h2 : 0 < log 2 := log_pos one_lt_two
  -- The density ratio eventually exceeds `δ / 2`.
  have hd : ∀ᶠ X : ℕ in atTop, δ / 2 <
      (((Finset.range X).filter fun q => q.Prime ∧ q ∈ Set.range ℓ).card : ℝ) /
        (((Finset.range X).filter Nat.Prime).card : ℝ) := by
    have := (tendsto_order.1 hdensity).1 (δ / 2) (by linarith)
    convert this using 3
  have hX : Tendsto (fun y : ℝ => ⌊y⌋₊ + 1) atTop atTop :=
    (tendsto_add_atTop_nat 1).comp tendsto_nat_floor_atTop
  filter_upwards [hX.eventually hd, eventually_primeCounting_ge,
    eventually_le_div_log (8 * A.card / (δ * log 2)), eventually_ge_atTop 3]
    with y hy hpi hK hy3
  have hlog : 0 < log y := log_pos (by linarith)
  set X := ⌊y⌋₊ + 1
  have hden : ((Finset.range X).filter Nat.Prime).card = Nat.primeCounting ⌊y⌋₊ := by
    rw [Nat.primeCounting_eq_primeCounting'_succ, ← Nat.primesBelow_card_eq_primeCounting']
    rfl
  -- The numerator is controlled by the auxiliary indices plus `A`.
  have hnum : ((Finset.range X).filter fun q => q.Prime ∧ q ∈ Set.range ℓ).card ≤
      (idx ℓ hinj A y).card + A.card := by
    set T := (Finset.range X).preimage ℓ hinj.injOn
    have h1 : ((Finset.range X).filter fun q => q.Prime ∧ q ∈ Set.range ℓ) ⊆ T.image ℓ := by
      intro q hq
      simp only [Finset.mem_filter, Finset.mem_range] at hq
      obtain ⟨i, rfl⟩ := hq.2.2
      exact Finset.mem_image_of_mem ℓ (by simp [T, hq.1])
    have h2 : T ⊆ idx ℓ hinj A y ∪ A := by
      intro i hi
      by_cases hiA : i ∈ A
      · exact Finset.mem_union_right _ hiA
      · refine Finset.mem_union_left _ ?_
        simp only [T, Finset.mem_preimage, Finset.mem_range] at hi
        exact mem_idx.mpr ⟨Nat.lt_succ_iff.mp hi, hiA⟩
    calc _ ≤ (T.image ℓ).card := Finset.card_le_card h1
      _ ≤ T.card := Finset.card_image_le
      _ ≤ (idx ℓ hinj A y ∪ A).card := Finset.card_le_card h2
      _ ≤ _ := Finset.card_union_le _ _
  have hdenpos : (0 : ℝ) < ((Finset.range X).filter Nat.Prime).card := by
    by_contra h
    have h0 : (((Finset.range X).filter Nat.Prime).card : ℝ) = 0 :=
      le_antisymm (not_lt.mp h) (Nat.cast_nonneg _)
    rw [h0, div_zero] at hy
    linarith
  rw [lt_div_iff₀ hdenpos, hden] at hy
  have hnum' : (((Finset.range X).filter fun q => q.Prime ∧ q ∈ Set.range ℓ).card : ℝ) ≤
      (idx ℓ hinj A y).card + A.card := by exact_mod_cast hnum
  have hpi' : δ / 2 * (log 2 / 2 * y / log y) ≤ δ / 2 * (Nat.primeCounting ⌊y⌋₊ : ℝ) :=
    mul_le_mul_of_nonneg_left hpi (by positivity)
  have hA : (A.card : ℝ) ≤ δ * log 2 / 8 * y / log y := by
    have := mul_le_mul_of_nonneg_left hK (by positivity : (0 : ℝ) ≤ δ * log 2 / 8)
    rw [mul_div_assoc]
    calc (A.card : ℝ) = δ * log 2 / 8 * (8 * A.card / (δ * log 2)) := by
          field_simp
      _ ≤ _ := this
  have key : δ / 2 * (log 2 / 2 * y / log y) = 2 * (δ * log 2 / 8 * y / log y) := by ring
  linarith

end Indices

/-! ### Squarefree products of auxiliary primes -/

section Products

variable {ℓ : ℕ → ℕ} {hinj : Function.Injective ℓ} {A : Finset ℕ}

/-- The product of the auxiliary primes indexed by `S`. -/
def prodIdx (ℓ : ℕ → ℕ) (S : Finset ℕ) : ℕ := ∏ i ∈ S, ℓ i

lemma prodIdx_pos (hprime : ∀ n, (ℓ n).Prime) (S : Finset ℕ) : 0 < prodIdx ℓ S :=
  Finset.prod_pos fun i _ => (hprime i).pos

lemma prime_dvd_prodIdx_iff (hprime : ∀ n, (ℓ n).Prime) (hinj : Function.Injective ℓ)
    (S : Finset ℕ) (i : ℕ) : ℓ i ∣ prodIdx ℓ S ↔ i ∈ S := by
  refine ⟨fun h => ?_, fun h => Finset.dvd_prod_of_mem ℓ h⟩
  obtain ⟨j, hj, hdvd⟩ := ((hprime i).prime.dvd_finsetProd_iff ℓ).mp h
  have := (Nat.prime_dvd_prime_iff_eq (hprime i) (hprime j)).mp hdvd
  rwa [hinj this]

lemma prodIdx_injective (hprime : ∀ n, (ℓ n).Prime) (hinj : Function.Injective ℓ)
    {S T : Finset ℕ} (h : prodIdx ℓ S = prodIdx ℓ T) : S = T := by
  ext i
  rw [← prime_dvd_prodIdx_iff hprime hinj, ← prime_dvd_prodIdx_iff hprime hinj, h]

lemma le_prodIdx (hprime : ∀ n, (ℓ n).Prime) {S : Finset ℕ} {i : ℕ} (hi : i ∈ S) :
    ℓ i ≤ prodIdx ℓ S :=
  Nat.le_of_dvd (prodIdx_pos hprime S) (Finset.dvd_prod_of_mem ℓ hi)

lemma prodIdx_insert {S : Finset ℕ} {i : ℕ} (hi : i ∉ S) :
    prodIdx ℓ (insert i S) = ℓ i * prodIdx ℓ S := Finset.prod_insert hi

variable (ℓ hinj A)

/-- Index sets outside `A` whose product is at most `Y`. -/
def fam (Y : ℝ) : Finset (Finset ℕ) :=
  (idx ℓ hinj A Y).powerset.filter fun S => (prodIdx ℓ S : ℝ) ≤ Y

/-- The reciprocal sum over squarefree auxiliary products up to `Y`. -/
def H (Y : ℝ) : ℝ := ∑ S ∈ fam ℓ hinj A Y, 1 / (prodIdx ℓ S : ℝ)

/-- The reciprocal sum of the auxiliary primes in `(W, V]`. -/
def blockSum (W V : ℝ) : ℝ := ∑ i ∈ idx ℓ hinj A V \ idx ℓ hinj A W, 1 / (ℓ i : ℝ)

variable {ℓ hinj A}

lemma mem_fam (hprime : ∀ n, (ℓ n).Prime) {Y : ℝ} (hY : 0 ≤ Y) {S : Finset ℕ} :
    S ∈ fam ℓ hinj A Y ↔ Disjoint S A ∧ (prodIdx ℓ S : ℝ) ≤ Y := by
  simp only [fam, Finset.mem_filter, Finset.mem_powerset]
  constructor
  · rintro ⟨hS, hle⟩
    refine ⟨Finset.disjoint_left.mpr fun i hi => ((mem_idx).mp (hS hi)).2, hle⟩
  · rintro ⟨hdisj, hle⟩
    refine ⟨fun i hi => (mem_idx_iff_real hY).mpr ⟨le_trans ?_ hle,
      Finset.disjoint_left.mp hdisj hi⟩, hle⟩
    exact_mod_cast le_prodIdx hprime hi

lemma fam_mono (hprime : ∀ n, (ℓ n).Prime) {W Y : ℝ} (hW : 0 ≤ W) (h : W ≤ Y) :
    fam ℓ hinj A W ⊆ fam ℓ hinj A Y := by
  intro S hS
  rw [mem_fam hprime hW] at hS
  rw [mem_fam hprime (hW.trans h)]
  exact ⟨hS.1, hS.2.trans h⟩

lemma H_nonneg (Y : ℝ) : 0 ≤ H ℓ hinj A Y :=
  Finset.sum_nonneg fun _ _ => by positivity

lemma H_mono (hprime : ∀ n, (ℓ n).Prime) {W Y : ℝ} (hW : 0 ≤ W) (h : W ≤ Y) :
    H ℓ hinj A W ≤ H ℓ hinj A Y :=
  Finset.sum_le_sum_of_subset_of_nonneg (fam_mono hprime hW h) fun _ _ _ => by positivity

lemma one_le_H (hprime : ∀ n, (ℓ n).Prime) {Y : ℝ} (hY : 1 ≤ Y) : 1 ≤ H ℓ hinj A Y := by
  have hmem : (∅ : Finset ℕ) ∈ fam ℓ hinj A Y :=
    (mem_fam hprime (by linarith)).mpr ⟨Finset.disjoint_empty_left _, by simpa [prodIdx]⟩
  have := Finset.single_le_sum (f := fun S => 1 / (prodIdx ℓ S : ℝ))
    (fun _ _ => by positivity) hmem
  simpa [H, prodIdx] using this

lemma blockSum_nonneg (W V : ℝ) : 0 ≤ blockSum ℓ hinj A W V :=
  Finset.sum_nonneg fun _ _ => by positivity

/-- The multiplicative recursion for the reciprocal sums. -/
lemma H_rec (hprime : ∀ n, (ℓ n).Prime) {W Y : ℝ} (hW : 1 ≤ W) (hWY : W * W ≤ Y) :
    H ℓ hinj A W * (1 + blockSum ℓ hinj A W (Y / W)) ≤ H ℓ hinj A Y := by
  classical
  have hW0 : 0 < W := by linarith
  have hY0 : 0 ≤ Y := by nlinarith
  set D := idx ℓ hinj A (Y / W) \ idx ℓ hinj A W
  have hD : ∀ i ∈ D, W < (ℓ i : ℝ) ∧ (ℓ i : ℝ) ≤ Y / W ∧ i ∉ A := by
    intro i hi
    rw [Finset.mem_sdiff, mem_idx_iff_real (by positivity), mem_idx_iff_real hW0.le] at hi
    exact ⟨lt_of_not_ge fun h => hi.2 ⟨h, hi.1.2⟩, hi.1.1, hi.1.2⟩
  set F : Finset ℕ × ℕ → Finset ℕ := fun q => insert q.2 q.1
  have hnotmem : ∀ q ∈ fam ℓ hinj A W ×ˢ D, q.2 ∉ q.1 := by
    rintro ⟨S, i⟩ hq hi
    rw [Finset.mem_product] at hq
    have h1 := (hD i hq.2).1
    have h2 : (ℓ i : ℝ) ≤ prodIdx ℓ S := by exact_mod_cast le_prodIdx hprime hi
    have h3 := ((mem_fam hprime hW0.le).mp hq.1).2
    linarith
  have hsmall : ∀ q ∈ fam ℓ hinj A W ×ˢ D, ∀ j ∈ q.1, (ℓ j : ℝ) ≤ W := by
    rintro ⟨S, i⟩ hq j hj
    rw [Finset.mem_product] at hq
    have h2 : (ℓ j : ℝ) ≤ prodIdx ℓ S := by exact_mod_cast le_prodIdx hprime hj
    exact h2.trans ((mem_fam hprime hW0.le).mp hq.1).2
  have hinjF : Set.InjOn F (fam ℓ hinj A W ×ˢ D : Finset _) := by
    rintro ⟨S, i⟩ hq ⟨S', i'⟩ hq' heq
    simp only [F] at heq
    have hi : i = i' := by
      by_contra hne
      have : i ∈ insert i' S' := heq ▸ Finset.mem_insert_self i S
      rcases Finset.mem_insert.mp this with h | h
      · exact hne h
      · have := hsmall _ hq' i h
        have := (hD i (Finset.mem_product.mp hq).2).1
        linarith
    subst hi
    have := congrArg (fun T => Finset.erase T i) heq
    simp only [Finset.erase_insert (hnotmem _ hq), Finset.erase_insert (hnotmem _ hq')] at this
    rw [this]
  have himage : (fam ℓ hinj A W ×ˢ D).image F ⊆ fam ℓ hinj A Y \ fam ℓ hinj A W := by
    intro T hT
    obtain ⟨⟨S, i⟩, hq, rfl⟩ := Finset.mem_image.mp hT
    have hq' := Finset.mem_product.mp hq
    have hSW := (mem_fam hprime hW0.le).mp hq'.1
    obtain ⟨hi1, hi2, hiA⟩ := hD i hq'.2
    have hprod : (prodIdx ℓ (insert i S) : ℝ) = ℓ i * prodIdx ℓ S := by
      rw [prodIdx_insert (hnotmem _ hq)]; push_cast; ring
    have hpos : (0 : ℝ) < prodIdx ℓ S := by exact_mod_cast prodIdx_pos hprime S
    rw [Finset.mem_sdiff, mem_fam hprime hY0, mem_fam hprime hW0.le]
    refine ⟨⟨Finset.disjoint_insert_left.mpr ⟨hiA, hSW.1⟩, ?_⟩, fun h => ?_⟩
    · rw [hprod]
      calc (ℓ i : ℝ) * prodIdx ℓ S ≤ Y / W * W :=
            mul_le_mul hi2 hSW.2 hpos.le (by positivity)
        _ = Y := by field_simp
    · have := h.2
      rw [hprod] at this
      have h1 : (1 : ℝ) ≤ prodIdx ℓ S := by exact_mod_cast prodIdx_pos hprime S
      nlinarith
  have hdisj : Disjoint (fam ℓ hinj A W) ((fam ℓ hinj A W ×ˢ D).image F) :=
    Finset.disjoint_of_subset_right himage Finset.disjoint_sdiff
  have hsub : fam ℓ hinj A W ∪ (fam ℓ hinj A W ×ˢ D).image F ⊆ fam ℓ hinj A Y :=
    Finset.union_subset (fam_mono hprime hW0.le (by nlinarith))
      (himage.trans Finset.sdiff_subset)
  have hsum : ∑ T ∈ (fam ℓ hinj A W ×ˢ D).image F, 1 / (prodIdx ℓ T : ℝ) =
      H ℓ hinj A W * blockSum ℓ hinj A W (Y / W) := by
    rw [Finset.sum_image hinjF, H, blockSum, Finset.sum_mul_sum, Finset.sum_product]
    refine Finset.sum_congr rfl fun S hS => Finset.sum_congr rfl fun i hi => ?_
    have hni : i ∉ S := hnotmem (S, i) (Finset.mem_product.mpr ⟨hS, hi⟩)
    simp only [F, prodIdx_insert hni]
    push_cast
    field_simp
  calc H ℓ hinj A W * (1 + blockSum ℓ hinj A W (Y / W))
      = H ℓ hinj A W + ∑ T ∈ (fam ℓ hinj A W ×ˢ D).image F, 1 / (prodIdx ℓ T : ℝ) := by
        rw [hsum]; ring
    _ = ∑ T ∈ fam ℓ hinj A W ∪ (fam ℓ hinj A W ×ˢ D).image F, 1 / (prodIdx ℓ T : ℝ) := by
        rw [Finset.sum_union hdisj, H]
    _ ≤ H ℓ hinj A Y :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity

end Products

/-! ### Blocks of auxiliary primes and the growth of `H` -/

section Growth

variable {ℓ : ℕ → ℕ} {hinj : Function.Injective ℓ} {A : Finset ℕ}

lemma blockSum_self (W : ℝ) : blockSum ℓ hinj A W W = 0 := by
  simp [blockSum]

lemma blockSum_add {W V U : ℝ} (hWV : W ≤ V) (hVU : V ≤ U) :
    blockSum ℓ hinj A W U = blockSum ℓ hinj A W V + blockSum ℓ hinj A V U := by
  classical
  have hsplit : idx ℓ hinj A U \ idx ℓ hinj A W =
      (idx ℓ hinj A V \ idx ℓ hinj A W) ∪ (idx ℓ hinj A U \ idx ℓ hinj A V) := by
    ext i
    simp only [Finset.mem_sdiff, Finset.mem_union]
    constructor
    · rintro ⟨hU, hW⟩
      by_cases hV : i ∈ idx ℓ hinj A V
      · exact Or.inl ⟨hV, hW⟩
      · exact Or.inr ⟨hU, hV⟩
    · rintro (⟨hV, hW⟩ | ⟨hU, hV⟩)
      · exact ⟨idx_mono hVU hV, hW⟩
      · exact ⟨hU, fun hW => hV (idx_mono hWV hW)⟩
  have hdisj : Disjoint (idx ℓ hinj A V \ idx ℓ hinj A W) (idx ℓ hinj A U \ idx ℓ hinj A V) := by
    rw [Finset.disjoint_left]
    intro i h1 h2
    exact (Finset.mem_sdiff.mp h2).2 (Finset.mem_sdiff.mp h1).1
  rw [blockSum, hsplit, Finset.sum_union hdisj, blockSum, blockSum]

lemma blockSum_ge {W V : ℝ} (hW : 0 ≤ W) (hWV : W ≤ V) :
    (((idx ℓ hinj A V).card : ℝ) - (idx ℓ hinj A W).card) / V ≤ blockSum ℓ hinj A W V := by
  classical
  have hV : 0 ≤ V := hW.trans hWV
  have hsub : idx ℓ hinj A W ⊆ idx ℓ hinj A V := idx_mono hWV
  rcases eq_or_lt_of_le hV with hV0 | hVpos
  · rw [← hV0, div_zero]; exact blockSum_nonneg _ _
  have hcard : ((idx ℓ hinj A V \ idx ℓ hinj A W).card : ℝ) =
      (idx ℓ hinj A V).card - (idx ℓ hinj A W).card := by
    rw [Finset.card_sdiff_of_subset hsub, Nat.cast_sub (Finset.card_le_card hsub)]
  rw [← hcard, blockSum]
  have hconst : ((idx ℓ hinj A V \ idx ℓ hinj A W).card : ℝ) / V =
      ∑ _i ∈ idx ℓ hinj A V \ idx ℓ hinj A W, 1 / V := by
    rw [Finset.sum_const, nsmul_eq_mul]; ring
  rw [hconst]
  refine Finset.sum_le_sum fun i hi => ?_
  have hi' := ((mem_idx_iff_real hV).mp (Finset.mem_sdiff.mp hi).1).1
  have hpos : (0 : ℝ) < ℓ i := by
    rcases eq_or_lt_of_le (Nat.cast_nonneg (ℓ i) : (0 : ℝ) ≤ ℓ i) with h | h
    · -- `ℓ i = 0` cannot lie in `(W, V]` when the counts differ; handle by bounding by `0`
      exfalso
      have hiW : i ∈ idx ℓ hinj A W := (mem_idx_iff_real hW).mpr
        ⟨by rw [← h]; exact hW, ((mem_idx_iff_real hV).mp (Finset.mem_sdiff.mp hi).1).2⟩
      exact (Finset.mem_sdiff.mp hi).2 hiW
    · exact h
  exact one_div_le_one_div_of_le hpos hi'

variable (hprime : ∀ n, (ℓ n).Prime) {δ : ℝ} (hδ : 0 < δ)
  (hdensity : HasPrimeNaturalDensity (Set.range ℓ) δ)

include hprime hδ hdensity in
/-- A single `B`-adic block of auxiliary primes contributes at least `c / t`. -/
lemma exists_block_bound :
    ∃ B : ℝ, 1 < B ∧ ∃ c : ℝ, 0 < c ∧ ∃ t₀ : ℕ, 1 ≤ t₀ ∧ ∀ t ≥ t₀,
      c / t ≤ blockSum ℓ hinj A (B ^ t) (B ^ (t + 1)) := by
  set c₁ := δ * log 2 / 8 with hc₁
  set c₂ := log 4 + 1 with hc₂
  have hc₁pos : 0 < c₁ := by have := log_pos one_lt_two; positivity
  have hc₂pos : 0 < c₂ := by have := log_pos (by norm_num : (1 : ℝ) < 4); positivity
  obtain ⟨y₀, hy₀⟩ := Filter.eventually_atTop.mp
    ((eventually_card_idx_ge (hinj := hinj) (A := A) hprime hδ hdensity).and
      ((eventually_card_idx_le (hinj := hinj) (A := A) hprime).and (eventually_ge_atTop 1)))
  set B := max 2 (4 * c₂ / c₁) with hB
  have hB2 : 2 ≤ B := le_max_left _ _
  have hBc : 4 * c₂ / c₁ ≤ B := le_max_right _ _
  have hB1 : 1 < B := by linarith
  have hlogB : 0 < log B := log_pos hB1
  obtain ⟨t₀, ht₀⟩ := Filter.eventually_atTop.mp
    ((tendsto_pow_atTop_atTop_of_one_lt hB1).eventually (eventually_ge_atTop y₀))
  refine ⟨B, hB1, c₁ / (4 * log B), by positivity, max t₀ 1, le_max_right _ _, fun t ht => ?_⟩
  have ht1 : 1 ≤ t := le_trans (le_max_right _ _) ht
  have htpos : (0 : ℝ) < t := by exact_mod_cast ht1
  have hBt : y₀ ≤ B ^ t := ht₀ t (le_trans (le_max_left _ _) ht)
  have hBt1 : y₀ ≤ B ^ (t + 1) := hBt.trans (pow_le_pow_right₀ hB1.le (Nat.le_succ t))
  obtain ⟨hlow, -, -⟩ := hy₀ _ hBt1
  obtain ⟨-, hup, -⟩ := hy₀ _ hBt
  have hPt : (0 : ℝ) < B ^ t := by positivity
  have hlog1 : log (B ^ (t + 1)) = (t + 1) * log B := by rw [log_pow]; push_cast; ring
  have hlog0 : log (B ^ t) = t * log B := by rw [log_pow]
  rw [hlog1] at hlow
  rw [hlog0] at hup
  refine le_trans ?_ (blockSum_ge (by positivity) (pow_le_pow_right₀ hB1.le (Nat.le_succ t)))
  rw [le_div_iff₀ (by positivity)]
  have e1 : c₁ * B ^ (t + 1) / ((t + 1) * log B) ≥ c₁ * B ^ (t + 1) / (2 * t * log B) := by
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    have : (t : ℝ) + 1 ≤ 2 * t := by linarith [show (1 : ℝ) ≤ t by exact_mod_cast ht1]
    nlinarith
  have e2 : c₂ * B ^ t / (t * log B) ≤ c₁ * B ^ (t + 1) / (4 * t * log B) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity), pow_succ]
    have : 4 * c₂ ≤ c₁ * B := by
      have := mul_le_mul_of_nonneg_left hBc hc₁pos.le
      rwa [mul_div_cancel₀ _ hc₁pos.ne'] at this
    have hpos : 0 ≤ B ^ t * (t * log B) := by positivity
    nlinarith
  have e3 : c₁ / (4 * log B) / t * B ^ (t + 1) =
      c₁ * B ^ (t + 1) / (2 * t * log B) - c₁ * B ^ (t + 1) / (4 * t * log B) := by
    field_simp; ring
  rw [e3]
  have hlow' : c₁ * B ^ (t + 1) / ((t + 1) * log B) ≤ (idx ℓ hinj A (B ^ (t + 1))).card := by
    rw [hc₁]; exact hlow
  have hup' : ((idx ℓ hinj A (B ^ t)).card : ℝ) ≤ c₂ * B ^ t / (t * log B) := by
    rw [hc₂]; exact hup
  linarith

include hprime hδ hdensity in
/-- The reciprocal sums over squarefree auxiliary products grow like a power of `log`. -/
lemma exists_H_lower :
    ∃ α₀ : ℝ, 0 < α₀ ∧ ∃ c₃ : ℝ, 0 < c₃ ∧ ∃ Y₀ : ℝ, 1 ≤ Y₀ ∧ ∀ Y ≥ Y₀,
      c₃ * log Y ^ α₀ ≤ H ℓ hinj A Y := by
  obtain ⟨B, hB1, c, hc, t₀, ht₀1, hblock⟩ := exists_block_bound (hinj := hinj) (A := A)
    hprime hδ hdensity
  have hB0 : 0 < B := by linarith
  have hlogB : 0 < log B := log_pos hB1
  -- Many consecutive blocks.
  have hmulti : ∀ j ≥ t₀, ∀ r ≤ j, (r : ℝ) * c / (2 * j) ≤
      blockSum ℓ hinj A (B ^ j) (B ^ (j + r)) := by
    intro j hj r
    induction r with
    | zero => intro _; simp [blockSum_self]
    | succ r ih =>
      intro hr
      have hjpos : (0 : ℝ) < j := by exact_mod_cast (lt_of_lt_of_le ht₀1 hj)
      rw [show j + (r + 1) = (j + r) + 1 by ring,
        blockSum_add (pow_le_pow_right₀ hB1.le (Nat.le_add_right j r))
          (pow_le_pow_right₀ hB1.le (Nat.le_succ _))]
      have h1 := ih (Nat.le_of_succ_le hr)
      have h2 := hblock (j + r) (le_trans hj (Nat.le_add_right j r))
      have h3 : c / (2 * j) ≤ c / ((j + r : ℕ) : ℝ) := by
        apply div_le_div_of_nonneg_left hc.le (Nat.cast_pos.mpr (by omega))
        push_cast
        have : (r : ℝ) + 1 ≤ j := by exact_mod_cast hr
        linarith
      have e : ((r + 1 : ℕ) : ℝ) * c / (2 * j) = r * c / (2 * j) + c / (2 * j) := by
        push_cast; ring
      rw [e]
      linarith
  set s₀ := c / 2 with hs₀
  have hs₀pos : 0 < s₀ := by positivity
  have hstep : ∀ j ≥ t₀, (1 + s₀) * H ℓ hinj A (B ^ j) ≤ H ℓ hinj A (B ^ (3 * j)) := by
    intro j hj
    have hjpos : (0 : ℝ) < j := by exact_mod_cast (lt_of_lt_of_le ht₀1 hj)
    have hW : 1 ≤ B ^ j := one_le_pow₀ hB1.le
    have hWY : B ^ j * B ^ j ≤ B ^ (3 * j) := by
      rw [← pow_add]; exact pow_le_pow_right₀ hB1.le (by omega)
    have hrec := H_rec (hinj := hinj) (A := A) hprime hW hWY
    have hdiv : B ^ (3 * j) / B ^ j = B ^ (j + j) := by
      rw [div_eq_iff (by positivity), ← pow_add]; congr 1; ring
    rw [hdiv] at hrec
    have hbs := hmulti j hj j le_rfl
    have : (j : ℝ) * c / (2 * j) = s₀ := by rw [hs₀]; field_simp
    rw [this] at hbs
    have hH := H_nonneg (ℓ := ℓ) (hinj := hinj) (A := A) (B ^ j)
    nlinarith
  have hiter : ∀ r : ℕ, (1 + s₀) ^ r ≤ H ℓ hinj A (B ^ (3 ^ r * t₀)) := by
    intro r
    induction r with
    | zero => simpa using one_le_H (hinj := hinj) (A := A) hprime (one_le_pow₀ hB1.le)
    | succ r ih =>
      have h := hstep (3 ^ r * t₀) (Nat.le_mul_of_pos_left _ (by positivity))
      rw [show 3 * (3 ^ r * t₀) = 3 ^ (r + 1) * t₀ by ring] at h
      rw [pow_succ]
      nlinarith
  set α₀ := log (1 + s₀) / log 3 with hα₀
  have hlog3 : 0 < log 3 := log_pos (by norm_num)
  have hα₀pos : 0 < α₀ := div_pos (log_pos (by linarith)) hlog3
  have h3α : (3 : ℝ) ^ α₀ = 1 + s₀ := by
    rw [Real.rpow_def_of_pos (by norm_num), hα₀, mul_div_cancel₀ _ hlog3.ne',
      exp_log (by linarith)]
  set K := (t₀ : ℝ) * log B with hK
  have hKpos : 0 < K := mul_pos (Nat.cast_pos.mpr (by omega)) hlogB
  refine ⟨α₀, hα₀pos, 1 / ((1 + s₀) * K ^ α₀), by positivity, B ^ t₀,
    one_le_pow₀ hB1.le, fun Y hY => ?_⟩
  have hY1 : 1 ≤ Y := le_trans (one_le_pow₀ hB1.le) hY
  -- Locate `Y` between consecutive iterates.
  have hex : ∃ r : ℕ, Y < B ^ (3 ^ (r + 1) * t₀) := by
    obtain ⟨n, hn⟩ := (tendsto_pow_atTop_atTop_of_one_lt hB1).eventually_gt_atTop Y |>.exists_forall_of_atTop
    refine ⟨n, hn _ ?_⟩
    calc n ≤ 3 ^ (n + 1) := (Nat.lt_pow_self (by norm_num)).le.trans
          (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ n))
      _ ≤ 3 ^ (n + 1) * t₀ := Nat.le_mul_of_pos_right _ ht₀1
  classical
  set r := Nat.find hex with hr
  have hYup : Y < B ^ (3 ^ (r + 1) * t₀) := Nat.find_spec hex
  have hYlow : B ^ (3 ^ r * t₀) ≤ Y := by
    rcases Nat.eq_zero_or_pos r with h0 | hpos
    · rw [h0]; simpa using hY
    · obtain ⟨r', hr'⟩ := Nat.exists_eq_add_one_of_ne_zero hpos.ne'
      have := Nat.find_min hex (show r' < Nat.find hex by omega)
      rw [hr']
      exact not_lt.mp this
  have hHY : (1 + s₀) ^ r ≤ H ℓ hinj A Y :=
    (hiter r).trans (H_mono (hinj := hinj) (A := A) hprime (by positivity) hYlow)
  have hlogY : log Y ≤ (3 : ℝ) ^ (r + 1) * K := by
    have := (log_lt_log (by linarith) hYup).le
    rw [log_pow] at this
    rw [hK]; push_cast at this; linarith
  have hlogY0 : 0 ≤ log Y := log_nonneg hY1
  have hpow : log Y ^ α₀ ≤ (1 + s₀) ^ (r + 1) * K ^ α₀ := by
    calc log Y ^ α₀ ≤ ((3 : ℝ) ^ (r + 1) * K) ^ α₀ :=
          Real.rpow_le_rpow hlogY0 hlogY hα₀pos.le
      _ = ((3 : ℝ) ^ (r + 1)) ^ α₀ * K ^ α₀ := Real.mul_rpow (by positivity) hKpos.le
      _ = (1 + s₀) ^ (r + 1) * K ^ α₀ := by
          rw [← h3α, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
            ← Real.rpow_mul (by norm_num), mul_comm α₀]
  have hKα : 0 < K ^ α₀ := Real.rpow_pos_of_pos hKpos _
  calc 1 / ((1 + s₀) * K ^ α₀) * log Y ^ α₀
      ≤ 1 / ((1 + s₀) * K ^ α₀) * ((1 + s₀) ^ (r + 1) * K ^ α₀) :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = (1 + s₀) ^ r := by field_simp; ring
    _ ≤ H ℓ hinj A Y := hHY

end Growth

/-! ### Characters on squarefree auxiliary products -/

section Characters

/-- Every divisor of `q - 1` is the order of a Dirichlet character modulo the prime `q`. -/
lemma exists_char_orderOf {q d : ℕ} [Fact q.Prime] (hd : d ∣ q - 1) :
    ∃ χ : DirichletCharacter MTT.Qbar q, orderOf χ = d := by
  obtain ⟨e⟩ := MulChar.mulEquiv_units (ZMod q) MTT.Qbar
  have : IsCyclic (MulChar (ZMod q) MTT.Qbar) := (MulEquiv.isCyclic e).mpr inferInstance
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := MulChar (ZMod q) MTT.Qbar)
  have hcard : Nat.card (MulChar (ZMod q) MTT.Qbar) = q - 1 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
      Nat.totient_prime Fact.out]
  rw [hcard] at hg
  have hne : orderOf g ≠ 0 := by
    rw [hg]; exact Nat.sub_ne_zero_of_lt (Fact.out : q.Prime).one_lt
  exact ⟨g ^ (orderOf g / d), orderOf_pow_orderOf_div hne (hg ▸ hd)⟩

/-- A product of multiplicative characters evaluated at a unit. -/
lemma mulChar_prod_apply {M R ι : Type*} [CommMonoid M] [CommRing R] (s : Finset ι)
    (f : ι → MulChar M R) {x : M} (hx : IsUnit x) : (∏ i ∈ s, f i) x = ∏ i ∈ s, f i x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [MulChar.one_apply hx]
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.prod_insert ha, MulChar.coeToFun_mul,
      Pi.mul_apply, ih]

/-- A Dirichlet character agrees with its level change at naturals prime to the larger level. -/
lemma changeLevel_natCast {n m : ℕ} [NeZero m] (χ : DirichletCharacter MTT.Qbar n)
    (hnm : n ∣ m) (z : ℕ) (hz : Nat.Coprime z m) :
    DirichletCharacter.changeLevel hnm χ (z : ZMod m) = χ (z : ZMod n) := by
  have := DirichletCharacter.changeLevel_eq_cast_of_dvd χ hnm (ZMod.unitOfCoprime z hz)
  simpa only [ZMod.coe_unitOfCoprime, ZMod.cast_natCast hnm] using this

variable {p m : ℕ} [Fact p.Prime] {ℓ : ℕ → ℕ} (hprime : ∀ n, (ℓ n).Prime)
  (hinj : Function.Injective ℓ) (hcong : ∀ n, Nat.ModEq (p ^ m) (ℓ n) 1)

include hprime hcong in
lemma exists_local_char (i : ℕ) :
    ∃ χ : DirichletCharacter MTT.Qbar (ℓ i), orderOf χ = p ^ m := by
  have : Fact (ℓ i).Prime := ⟨hprime i⟩
  exact exists_char_orderOf ((Nat.modEq_iff_dvd' (hprime i).one_lt.le).mp (hcong i).symm)

/-- The chosen local character of exact order `p^m` modulo `ℓ i`. -/
def localChar (i : ℕ) : DirichletCharacter MTT.Qbar (ℓ i) :=
  Classical.choose (exists_local_char hprime hcong i)

lemma orderOf_localChar (i : ℕ) : orderOf (localChar hprime hcong i) = p ^ m :=
  Classical.choose_spec (exists_local_char hprime hcong i)

omit [Fact p.Prime] in
lemma dvd_prodIdx {S : Finset ℕ} {i : ℕ} (hi : i ∈ S) : ℓ i ∣ prodIdx ℓ S :=
  Finset.dvd_prod_of_mem ℓ hi

/-- The product of the local characters at level `∏_{i ∈ S} ℓ i`. -/
def prodChar (S : Finset ℕ) : DirichletCharacter MTT.Qbar (prodIdx ℓ S) :=
  ∏ i ∈ S.attach, DirichletCharacter.changeLevel (dvd_prodIdx i.2)
    (localChar hprime hcong i.1)

lemma prodChar_natCast (S : Finset ℕ) (z : ℕ) (hz : Nat.Coprime z (prodIdx ℓ S)) :
    prodChar hprime hcong S (z : ZMod (prodIdx ℓ S)) =
      ∏ i ∈ S.attach, localChar hprime hcong i.1 (z : ZMod (ℓ i.1)) := by
  have : NeZero (prodIdx ℓ S) := ⟨(prodIdx_pos hprime S).ne'⟩
  rw [prodChar, mulChar_prod_apply _ _ ((ZMod.isUnit_iff_coprime z _).mpr hz)]
  exact Finset.prod_congr rfl fun i _ => changeLevel_natCast _ _ z hz

lemma prodChar_pow_eq_one (S : Finset ℕ) : prodChar hprime hcong S ^ (p ^ m) = 1 := by
  rw [prodChar, ← Finset.prod_pow]
  refine Finset.prod_eq_one fun i _ => ?_
  rw [← map_pow, ← orderOf_localChar hprime hcong i.1, pow_orderOf_eq_one, map_one]

include hinj in
/-- Evaluate the product character at `z ≡ x (mod ℓ i₀)` and `z ≡ 1` at the other primes. -/
lemma prodChar_eval_single {S : Finset ℕ} {i₀ : ℕ} (hi₀ : i₀ ∈ S) (x : ℕ)
    (hx : Nat.Coprime x (ℓ i₀)) :
    ∃ z : ℕ, Nat.Coprime z (prodIdx ℓ S) ∧ z ≡ 1 [MOD prodIdx ℓ (S.erase i₀)] ∧
      prodChar hprime hcong S (z : ZMod (prodIdx ℓ S)) =
        localChar hprime hcong i₀ (x : ZMod (ℓ i₀)) := by
  have hsplit : ℓ i₀ * prodIdx ℓ (S.erase i₀) = prodIdx ℓ S := Finset.mul_prod_erase S ℓ hi₀
  have hcop : Nat.Coprime (ℓ i₀) (prodIdx ℓ (S.erase i₀)) := by
    refine Nat.Coprime.prod_right fun j hj => ?_
    exact (Nat.coprime_primes (hprime i₀) (hprime j)).mpr fun h =>
      (Finset.ne_of_mem_erase hj) (hinj h).symm
  obtain ⟨z, hz1, hz2⟩ := Nat.chineseRemainder hcop x 1
  have hzℓ : Nat.Coprime z (ℓ i₀) := by rw [Nat.Coprime, Nat.ModEq.gcd_eq hz1]; exact hx
  have hzM : Nat.Coprime z (prodIdx ℓ (S.erase i₀)) := by
    rw [Nat.Coprime, Nat.ModEq.gcd_eq hz2, Nat.gcd_one_left]
  have hzS : Nat.Coprime z (prodIdx ℓ S) := hsplit ▸ Nat.Coprime.mul_right hzℓ hzM
  refine ⟨z, hzS, hz2, ?_⟩
  rw [prodChar_natCast hprime hcong S z hzS,
    Finset.prod_eq_single_of_mem (⟨i₀, hi₀⟩ : {x // x ∈ S}) (Finset.mem_attach _ _) ?_]
  · exact congrArg _ ((ZMod.natCast_eq_natCast_iff _ _ _).mpr hz1)
  · rintro ⟨j, hj⟩ - hne
    have hj' : j ∈ S.erase i₀ := Finset.mem_erase.mpr ⟨fun h => hne (Subtype.ext h), hj⟩
    have h1 : (z : ZMod (ℓ j)) = 1 := by
      rw [← Nat.cast_one, ZMod.natCast_eq_natCast_iff]
      exact hz2.of_dvd (Finset.dvd_prod_of_mem ℓ hj')
    rw [h1, map_one]

/-- A nontrivial Dirichlet character takes a value different from `1` at a unit, which we
represent by a natural number. -/
lemma exists_natCast_ne_one {q : ℕ} [NeZero q] {χ : DirichletCharacter MTT.Qbar q}
    (hχ : χ ≠ 1) : ∃ x : ℕ, Nat.Coprime x q ∧ χ (x : ZMod q) ≠ 1 := by
  by_contra h
  push Not at h
  refine hχ (MulChar.ext fun u => ?_)
  set x := (u : ZMod q).val with hxdef
  have hxu : (u : ZMod q) = (x : ZMod q) := by rw [hxdef, ZMod.natCast_zmod_val]
  have hx : Nat.Coprime x q := (ZMod.isUnit_iff_coprime _ _).mp (by rw [← hxu]; exact u.isUnit)
  rw [MulChar.one_apply_coe, hxu]
  exact h x hx

include hinj in
lemma orderOf_prodChar {S : Finset ℕ} (hS : S.Nonempty) :
    orderOf (prodChar hprime hcong S) = p ^ m := by
  obtain ⟨i₀, hi₀⟩ := hS
  refine Nat.dvd_antisymm (orderOf_dvd_of_pow_eq_one (prodChar_pow_eq_one hprime hcong S)) ?_
  rw [← orderOf_localChar hprime hcong i₀]
  refine orderOf_dvd_of_pow_eq_one (MulChar.ext fun u => ?_)
  have : NeZero (ℓ i₀) := ⟨(hprime i₀).ne_zero⟩
  set x := (u : ZMod (ℓ i₀)).val with hxdef
  have hxu : (u : ZMod (ℓ i₀)) = (x : ZMod (ℓ i₀)) := by rw [hxdef, ZMod.natCast_zmod_val]
  have hx : Nat.Coprime x (ℓ i₀) :=
    (ZMod.isUnit_iff_coprime _ _).mp (by rw [← hxu]; exact u.isUnit)
  obtain ⟨z, hzS, -, hz⟩ := prodChar_eval_single hprime hinj hcong hi₀ x hx
  have hNZ : NeZero (prodIdx ℓ S) := ⟨(prodIdx_pos hprime S).ne'⟩
  have hk := pow_orderOf_eq_one (prodChar hprime hcong S)
  have hzu : IsUnit (z : ZMod (prodIdx ℓ S)) := (ZMod.isUnit_iff_coprime _ _).mpr hzS
  have h1 := congrArg (fun φ : DirichletCharacter MTT.Qbar (prodIdx ℓ S) => φ z) hk
  have hk0 : orderOf (prodChar hprime hcong S) ≠ 0 :=
    (orderOf_pos_iff.mpr (isOfFinOrder_iff_pow_eq_one.mpr ⟨p ^ m,
      pow_pos (Fact.out : p.Prime).pos m, prodChar_pow_eq_one hprime hcong S⟩)).ne'
  rw [MulChar.pow_apply' _ hk0, hz, MulChar.one_apply hzu] at h1
  rw [MulChar.pow_apply_coe, MulChar.one_apply_coe, hxu, h1]

include hprime hinj in
lemma prodIdx_dvd_of_forall (S : Finset ℕ) (c : ℕ) (h : ∀ i ∈ S, ℓ i ∣ c) :
    prodIdx ℓ S ∣ c := by
  induction S using Finset.induction_on with
  | empty => simp [prodIdx]
  | insert a S ha ih =>
    rw [prodIdx_insert ha]
    refine Nat.Coprime.mul_dvd_of_dvd_of_dvd ?_ (h a (Finset.mem_insert_self a S))
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))
    exact Nat.Coprime.prod_right fun j hj =>
      (Nat.coprime_primes (hprime a) (hprime j)).mpr fun hij => ha (hinj hij ▸ hj)

include hinj in
lemma prodChar_isPrimitive (hm : 0 < m) (S : Finset ℕ) :
    (prodChar hprime hcong S).IsPrimitive := by
  have hNZ : NeZero (prodIdx ℓ S) := ⟨(prodIdx_pos hprime S).ne'⟩
  set d := (prodChar hprime hcong S).conductor with hddef
  have hd : d ∣ prodIdx ℓ S := DirichletCharacter.conductor_dvd_level _
  by_contra hne
  have hne' : d ≠ prodIdx ℓ S := hne
  obtain ⟨i₀, hi₀, hndvd⟩ : ∃ i ∈ S, ¬ ℓ i ∣ d := by
    by_contra h
    push Not at h
    exact hne' (Nat.dvd_antisymm hd (prodIdx_dvd_of_forall hprime hinj S d h))
  have hMdvd : prodIdx ℓ (S.erase i₀) ∣ prodIdx ℓ S :=
    Finset.prod_dvd_prod_of_subset _ _ _ (Finset.erase_subset i₀ S)
  have hdM : d ∣ prodIdx ℓ (S.erase i₀) := by
    have hd' := hd
    rw [prodIdx, ← Finset.mul_prod_erase S ℓ hi₀] at hd'
    exact (Nat.Coprime.dvd_mul_left
      (Nat.Coprime.symm ((hprime i₀).coprime_iff_not_dvd.mpr hndvd))).mp hd'
  have hft : (prodChar hprime hcong S).FactorsThrough (prodIdx ℓ (S.erase i₀)) :=
    DirichletCharacter.FactorsThrough.mono _
      (DirichletCharacter.factorsThrough_conductor _) hdM hMdvd
  rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap hMdvd] at hft
  have hℓZ : NeZero (ℓ i₀) := ⟨(hprime i₀).ne_zero⟩
  have hχne : localChar hprime hcong i₀ ≠ 1 := by
    intro h
    have := orderOf_localChar hprime hcong i₀
    rw [h, orderOf_one] at this
    exact (Nat.one_lt_pow hm.ne' (Fact.out : p.Prime).one_lt).ne this
  obtain ⟨x, hx, hxne⟩ := exists_natCast_ne_one hχne
  obtain ⟨z, hzS, hz1, hzval⟩ := prodChar_eval_single hprime hinj hcong hi₀ x hx
  have hw : ZMod.unitOfCoprime z hzS ∈ (ZMod.unitsMap hMdvd).ker := by
    rw [MonoidHom.mem_ker, Units.ext_iff, ZMod.unitsMap_val, ZMod.coe_unitOfCoprime,
      ZMod.cast_natCast hMdvd, Units.val_one, ← Nat.cast_one, ZMod.natCast_eq_natCast_iff]
    exact hz1
  have h1 := hft hw
  rw [MonoidHom.mem_ker, Units.ext_iff, MulChar.coe_toUnitHom, ZMod.coe_unitOfCoprime,
    Units.val_one, hzval] at h1
  exact hxne h1

end Characters

/-! ### Counting the supported characters -/

section Counting

/-- Primitive characters of bounded conductor form a finite set. -/
lemma finite_primitive_conductor_le (Y : ℝ) :
    {χ : DirichletCharacterWithLevel |
      χ.2.IsPrimitive ∧ (χ.2.conductor : ℝ) ≤ Y}.Finite := by
  have hbase : {N : {N : ℕ // 0 < N} | N.1 ≤ ⌊Y⌋₊}.Finite :=
    (Set.finite_le_nat ⌊Y⌋₊).preimage Subtype.val_injective.injOn
  have hfib : ∀ b ∈ {N : {N : ℕ // 0 < N} | N.1 ≤ ⌊Y⌋₊},
      ((Sigma.fst : DirichletCharacterWithLevel → {N : ℕ // 0 < N}) ⁻¹' {b}).Finite := by
    intro b _
    refine (Set.finite_range (Sigma.mk (β := fun N : {N : ℕ // 0 < N} =>
      DirichletCharacter MTT.Qbar N.1) b)).subset ?_
    rintro ⟨a, x⟩ hx
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx
    subst hx
    exact ⟨x, rfl⟩
  refine (hbase.preimage' hfib).subset ?_
  rintro χ ⟨hprim, hle⟩
  simp only [Set.mem_preimage, Set.mem_ofPred_eq]
  have hc : χ.2.conductor = χ.1.1 := hprim
  rw [← hc]
  exact Nat.le_floor hle

/-- Weakening the exponent of a logarithmic lower bound. -/
lemma hasLogPowerLowerBound_mono {g : ℝ → ℕ} {α β : ℝ} (hβα : β ≤ α)
    (h : HasLogPowerLowerBound g α) : HasLogPowerLowerBound g β := by
  obtain ⟨c, X₀, hc, hX₀, hb⟩ := h
  refine ⟨c, max X₀ (exp 1), hc, le_trans hX₀ (le_max_left _ _), fun X hX => ?_⟩
  have hXe : exp 1 ≤ X := le_trans (le_max_right _ _) hX
  have hlog : 1 ≤ log X := by
    rw [← log_exp 1]; exact log_le_log (exp_pos 1) hXe
  have hX0 : 0 ≤ X := le_trans (exp_pos 1).le hXe
  refine le_trans ?_ (hb X (le_trans (le_max_left _ _) hX))
  exact div_le_div_of_nonneg_left (by positivity) (rpow_pos_of_pos (by linarith) _)
    (rpow_le_rpow_of_exponent_le hlog (by linarith))

variable {p m : ℕ} [Fact p.Prime] {ℓ : ℕ → ℕ} (hprime : ∀ n, (ℓ n).Prime)
  (hinj : Function.Injective ℓ) (hcong : ∀ n, Nat.ModEq (p ^ m) (ℓ n) 1) {A : Finset ℕ}

include hprime hinj hcong

/-- The character with level attached to an index set. -/
def charOf (S : Finset ℕ) : DirichletCharacterWithLevel :=
  ⟨⟨prodIdx ℓ S, prodIdx_pos hprime S⟩, prodChar hprime hcong S⟩

lemma charOf_injective {S T : Finset ℕ} (h : charOf hprime hcong S = charOf hprime hcong T) :
    S = T :=
  prodIdx_injective hprime hinj (congrArg (fun χ : DirichletCharacterWithLevel => χ.1.1) h)

lemma charOf_mem (hm : 0 < m) {S : Finset ℕ} (hS : S.Nonempty) (hdisj : Disjoint S A) :
    charOf hprime hcong S ∈ supportedPrimePowerCharacters ℓ A p m :=
  ⟨prodChar_isPrimitive hprime hinj hcong hm S, orderOf_prodChar hprime hinj hcong hS, S,
    hdisj, DirichletCharacter.conductor_dvd_level _⟩

lemma charOf_conductor (hm : 0 < m) (S : Finset ℕ) :
    (charOf hprime hcong S).2.conductor = prodIdx ℓ S :=
  prodChar_isPrimitive hprime hinj hcong hm S

lemma card_idx_le_add_one (y : ℝ) (hy : 0 ≤ y) : ((idx ℓ hinj A y).card : ℝ) ≤ y + 1 := by
  have h : (idx ℓ hinj A y).card ≤ (Finset.range (⌊y⌋₊ + 1)).card := by
    refine Finset.card_le_card_of_injOn ℓ (fun i hi => ?_) hinj.injOn
    rw [Finset.mem_coe, mem_idx] at hi
    simp [Nat.lt_succ_iff, hi.1]
  rw [Finset.card_range] at h
  have := Nat.floor_le hy
  have h' : ((idx ℓ hinj A y).card : ℝ) ≤ (⌊y⌋₊ : ℝ) + 1 := by exact_mod_cast h
  linarith

/-- Pairs `(S, i)` with `S` a small product and `i` a large new prime give distinct supported
characters. -/
lemma sum_card_le_count (hm : 0 < m) {Z X : ℝ} (hZ : 1 ≤ Z) :
    (∑ S ∈ fam ℓ hinj A Z,
        ((idx ℓ hinj A (X / prodIdx ℓ S) \ idx ℓ hinj A Z).card : ℝ)) ≤
      characterConductorCount (supportedPrimePowerCharacters ℓ A p m) X := by
  classical
  have hZ0 : 0 < Z := by linarith
  set P := (fam ℓ hinj A Z).sigma fun S => idx ℓ hinj A (X / prodIdx ℓ S) \ idx ℓ hinj A Z
  have hP : ∀ q ∈ P, q.2 ∉ q.1 ∧ Z < (ℓ q.2 : ℝ) ∧
      (ℓ q.2 : ℝ) * prodIdx ℓ q.1 ≤ X ∧ Disjoint (insert q.2 q.1) A ∧
      ∀ j ∈ q.1, (ℓ j : ℝ) ≤ Z := by
    rintro ⟨S, i⟩ hq
    rw [Finset.mem_sigma] at hq
    obtain ⟨hS, hi⟩ := hq
    have hSZ := (mem_fam hprime hZ0.le).mp hS
    have hpos : (0 : ℝ) < prodIdx ℓ S := by exact_mod_cast prodIdx_pos hprime S
    rw [Finset.mem_sdiff] at hi
    have hiA : i ∉ A := (mem_idx.mp hi.1).2
    have hiZ : Z < ℓ i := lt_of_not_ge fun h => hi.2 ((mem_idx_iff_real hZ0.le).mpr ⟨h, hiA⟩)
    have hsmall : ∀ j ∈ S, (ℓ j : ℝ) ≤ Z := fun j hj =>
      (show (ℓ j : ℝ) ≤ prodIdx ℓ S by exact_mod_cast le_prodIdx hprime hj).trans hSZ.2
    refine ⟨fun h => by linarith [hsmall i h], hiZ, ?_,
      Finset.disjoint_insert_left.mpr ⟨hiA, hSZ.1⟩, hsmall⟩
    have hX0 : 0 ≤ X / prodIdx ℓ S := by
      rcases le_or_gt 0 X with hX | hX
      · positivity
      · exfalso
        have := (mem_idx.mp hi.1).1
        rw [Nat.floor_eq_zero.mpr (by
          exact lt_of_lt_of_le (div_neg_of_neg_of_pos hX hpos) zero_le_one)] at this
        exact (hprime i).ne_zero (Nat.le_zero.mp this)
    have := ((mem_idx_iff_real hX0).mp hi.1).1
    rwa [le_div_iff₀ hpos] at this
  set f : (Σ _ : Finset ℕ, ℕ) → DirichletCharacterWithLevel :=
    fun q => charOf hprime hcong (insert q.2 q.1)
  have hinjf : Set.InjOn f P := by
    rintro ⟨S, i⟩ hq ⟨S', i'⟩ hq' heq
    have hT := charOf_injective hprime hinj hcong heq
    obtain ⟨hni, hiZ, -, -, hsm⟩ := hP _ hq
    obtain ⟨hni', hiZ', -, -, hsm'⟩ := hP _ hq'
    simp only at hT hni hni' hiZ hiZ' hsm hsm'
    have hii : i = i' := by
      by_contra hne
      have : i ∈ insert i' S' := hT ▸ Finset.mem_insert_self i S
      rcases Finset.mem_insert.mp this with h | h
      · exact hne h
      · linarith [hsm' i h]
    subst hii
    have := congrArg (fun T => Finset.erase T i) hT
    simp only [Finset.erase_insert hni, Finset.erase_insert hni'] at this
    subst this
    rfl
  have hmaps : ∀ q ∈ P, f q ∈ {χ | χ ∈ supportedPrimePowerCharacters ℓ A p m ∧
      (χ.2.conductor : ℝ) ≤ X} := by
    intro q hq
    obtain ⟨hni, -, hle, hdisj, -⟩ := hP q hq
    refine ⟨charOf_mem hprime hinj hcong hm (Finset.insert_nonempty _ _) hdisj, ?_⟩
    simp only [f]
    rw [charOf_conductor hprime hinj hcong hm, prodIdx_insert hni]
    push_cast
    exact hle
  have hfin : {χ | χ ∈ supportedPrimePowerCharacters ℓ A p m ∧
      (χ.2.conductor : ℝ) ≤ X}.Finite :=
    (finite_primitive_conductor_le X).subset fun χ hχ => ⟨hχ.1.1, hχ.2⟩
  have hcard := Set.ncard_le_ncard_of_injOn f hmaps hinjf hfin
  rw [Set.ncard_coe_finset, Finset.card_sigma] at hcard
  unfold characterConductorCount
  exact_mod_cast hcard

end Counting

/-! ### The logarithmic lower bound -/

section Final

variable {p m : ℕ} [Fact p.Prime] {ℓ : ℕ → ℕ} (hprime : ∀ n, (ℓ n).Prime)
  (hinj : Function.Injective ℓ) (hcong : ∀ n, Nat.ModEq (p ^ m) (ℓ n) 1) {A : Finset ℕ}
  {δ : ℝ} (hδ : 0 < δ) (hdensity : HasPrimeNaturalDensity (Set.range ℓ) δ)

include hprime hinj hcong hδ hdensity in
lemma exists_hasLogPowerLowerBound (hm : 0 < m) :
    ∃ α₀ : ℝ, 0 < α₀ ∧
      HasLogPowerLowerBound (characterConductorCount (supportedPrimePowerCharacters ℓ A p m)) α₀ := by
  obtain ⟨α₀, hα₀, c₃, hc₃, Y₀, hY₀1, hH⟩ :=
    exists_H_lower (hinj := hinj) (A := A) hprime hδ hdensity
  set c₁ := δ * log 2 / 8 with hc₁
  have hc₁pos : 0 < c₁ := by have := log_pos one_lt_two; positivity
  obtain ⟨y₀, hy₀⟩ := Filter.eventually_atTop.mp
    (eventually_card_idx_ge (hinj := hinj) (A := A) hprime hδ hdensity)
  obtain ⟨Z₁, hZ₁⟩ := Filter.eventually_atTop.mp (eventually_log_le_mul (ε := c₁ / 12)
    (by positivity))
  set Z₂ := max (max Y₀ Z₁) (max y₀ 2) with hZ₂
  have hZ₂Y : Y₀ ≤ Z₂ := le_trans (le_max_left _ _) (le_max_left _ _)
  have hZ₂Z : Z₁ ≤ Z₂ := le_trans (le_max_right _ _) (le_max_left _ _)
  have hZ₂y : y₀ ≤ Z₂ := le_trans (le_max_left _ _) (le_max_right _ _)
  have hZ₂2 : 2 ≤ Z₂ := le_trans (le_max_right _ _) (le_max_right _ _)
  -- The bound at `X = Z³`.
  have hcube : ∀ Z ≥ Z₂, c₁ / 2 * (Z ^ 3 / log (Z ^ 3)) * H ℓ hinj A Z ≤
      characterConductorCount (supportedPrimePowerCharacters ℓ A p m) (Z ^ 3) := by
    intro Z hZ
    have hZ2 : 2 ≤ Z := hZ₂2.trans hZ
    have hZ1 : 1 ≤ Z := by linarith
    have hZ0 : 0 < Z := by linarith
    have hlogZ : 0 < log Z := log_pos (by linarith)
    have hlogX : log (Z ^ 3) = 3 * log Z := by rw [log_pow]; push_cast; ring
    have hlogXpos : 0 < log (Z ^ 3) := by rw [hlogX]; positivity
    have hlogZle : log Z ≤ c₁ / 12 * Z := hZ₁ Z (hZ₂Z.trans hZ)
    refine le_trans ?_ (sum_card_le_count hprime hinj hcong hm (X := Z ^ 3) hZ1)
    rw [H, Finset.mul_sum]
    refine Finset.sum_le_sum fun S hS => ?_
    have hSZ := (mem_fam hprime hZ0.le).mp hS
    set P : ℝ := (prodIdx ℓ S : ℝ) with hPdef
    have hP1 : 1 ≤ P := by rw [hPdef]; exact_mod_cast prodIdx_pos hprime S
    have hPZ : P ≤ Z := hSZ.2
    have hXP : Z ^ 2 ≤ Z ^ 3 / P := by
      rw [le_div_iff₀ (by linarith)]
      calc Z ^ 2 * P ≤ Z ^ 2 * Z := mul_le_mul_of_nonneg_left hPZ (by positivity)
        _ = Z ^ 3 := by ring
    have hXPy : y₀ ≤ Z ^ 3 / P := by nlinarith [hZ₂y.trans hZ]
    have hlow : c₁ * (Z ^ 3 / P) / log (Z ^ 3 / P) ≤ (idx ℓ hinj A (Z ^ 3 / P)).card := by
      rw [hc₁]; exact hy₀ _ hXPy
    have hlogXP : 0 < log (Z ^ 3 / P) := log_pos (by nlinarith)
    have hlogle : log (Z ^ 3 / P) ≤ log (Z ^ 3) :=
      log_le_log (by positivity) (div_le_self (by positivity) hP1)
    have h1 : c₁ * (Z ^ 3 / P) / log (Z ^ 3) ≤ (idx ℓ hinj A (Z ^ 3 / P)).card := by
      refine le_trans ?_ hlow
      rw [mul_div_assoc, mul_div_assoc]
      exact mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_left (by positivity) hlogXP hlogle) hc₁pos.le
    have h2 := card_idx_le_add_one (p := p) (m := m) hprime hinj hcong (A := A) Z hZ0.le
    have h3 : ((idx ℓ hinj A (Z ^ 3 / P)).card : ℝ) - (idx ℓ hinj A Z).card ≤
        ((idx ℓ hinj A (Z ^ 3 / P) \ idx ℓ hinj A Z).card : ℝ) := by
      have : (idx ℓ hinj A (Z ^ 3 / P)).card ≤
          (idx ℓ hinj A (Z ^ 3 / P) \ idx ℓ hinj A Z).card + (idx ℓ hinj A Z).card :=
        Finset.card_le_card_sdiff_add_card
      have : ((idx ℓ hinj A (Z ^ 3 / P)).card : ℝ) ≤
          ((idx ℓ hinj A (Z ^ 3 / P) \ idx ℓ hinj A Z).card : ℝ) + (idx ℓ hinj A Z).card := by
        exact_mod_cast this
      linarith
    -- The subtracted term is at most half of the main term.
    have h4 : Z + 1 ≤ c₁ / 2 * (Z ^ 3 / P) / log (Z ^ 3) := by
      rw [le_div_iff₀ hlogXpos, hlogX]
      have hZP : Z ^ 2 ≤ Z ^ 3 / P := hXP
      nlinarith
    have e : c₁ / 2 * (Z ^ 3 / log (Z ^ 3)) * (1 / P) = c₁ / 2 * (Z ^ 3 / P) / log (Z ^ 3) := by
      field_simp
    rw [e]
    have e2 : c₁ * (Z ^ 3 / P) / log (Z ^ 3) = 2 * (c₁ / 2 * (Z ^ 3 / P) / log (Z ^ 3)) := by
      ring
    linarith
  -- Convert to arbitrary `X` via `Z = X^(1/3)`.
  set C := c₁ / 2 * c₃ / (3 : ℝ) ^ α₀
  have hC : 0 < C := by positivity
  refine ⟨α₀, hα₀, C, Z₂ ^ 3, hC, one_le_pow₀ (by linarith), fun X hX => ?_⟩
  have hX0 : 0 < X := lt_of_lt_of_le (by positivity) hX
  set Z := X ^ (1 / 3 : ℝ) with hZdef
  have hZ3 : Z ^ 3 = X := by
    rw [hZdef, ← Real.rpow_natCast, ← Real.rpow_mul hX0.le]; norm_num
  have hZge : Z₂ ≤ Z := by
    have h := Real.rpow_le_rpow (by positivity) hX (by norm_num : (0 : ℝ) ≤ 1 / 3)
    rwa [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), show ((3 : ℕ) : ℝ) * (1 / 3) = 1
      by norm_num, Real.rpow_one] at h
  have hZ2 : 2 ≤ Z := hZ₂2.trans hZge
  have hlogZ : 0 < log Z := log_pos (by linarith)
  have hlogX : log X = 3 * log Z := by rw [← hZ3, log_pow]; push_cast; ring
  have hlogXpos : 0 < log X := by rw [hlogX]; positivity
  have hHZ := hH Z (hZ₂Y.trans hZge)
  have hmain := hcube Z hZge
  rw [hZ3] at hmain
  have hrpow : log X ^ (1 - α₀) = log X / log X ^ α₀ := by
    rw [Real.rpow_sub hlogXpos, Real.rpow_one]
  have hlogZα : log Z ^ α₀ = log X ^ α₀ / (3 : ℝ) ^ α₀ := by
    rw [hlogX, Real.mul_rpow (by norm_num) hlogZ.le]
    field_simp
  have h3α : (0 : ℝ) < 3 ^ α₀ := by positivity
  have hLα : 0 < log X ^ α₀ := Real.rpow_pos_of_pos hlogXpos _
  calc C * X / log X ^ (1 - α₀) = c₁ / 2 * (X / log X) * (c₃ * log Z ^ α₀) := by
        rw [hrpow, hlogZα]; simp only [C]; field_simp
    _ ≤ c₁ / 2 * (X / log X) * H ℓ hinj A Z :=
        mul_le_mul_of_nonneg_left hHZ (by positivity)
    _ ≤ _ := hmain

end Final

end HorizontalPadicL.LogLowerBound

open HorizontalPadicL HorizontalPadicL.LogLowerBound in
theorem solution
    (p m : ℕ) [Fact p.Prime] (hm : 0 < m)
    (ℓ : ℕ → ℕ) (hprime : ∀ n, (ℓ n).Prime)
    (hinj : Function.Injective ℓ) (hcong : ∀ n, Nat.ModEq (p ^ m) (ℓ n) 1)
    (δ : ℝ) (hδ : 0 < δ)
    (hdensity : HasPrimeNaturalDensity (Set.range ℓ) δ)
    (A : Finset ℕ) :
    ∃ α : ℝ, 0 < α ∧ α < ((p ^ m - 1 : ℕ) : ℝ) * δ ∧
      HasLogPowerLowerBound
        (characterConductorCount (supportedPrimePowerCharacters ℓ A p m)) α := by
  obtain ⟨α₀, hα₀, hbound⟩ :=
    exists_hasLogPowerLowerBound (A := A) hprime hinj hcong hδ hdensity hm
  have hp := (Fact.out : p.Prime)
  have hpm : 2 ≤ p ^ m := le_trans hp.two_le (Nat.le_self_pow hm.ne' p)
  have hκ : 0 < ((p ^ m - 1 : ℕ) : ℝ) * δ := by
    have : (1 : ℝ) ≤ ((p ^ m - 1 : ℕ) : ℝ) := by
      exact_mod_cast (show 1 ≤ p ^ m - 1 by omega)
    positivity
  refine ⟨min α₀ (((p ^ m - 1 : ℕ) : ℝ) * δ / 2), lt_min hα₀ (by linarith), ?_,
    hasLogPowerLowerBound_mono (min_le_left _ _) hbound⟩
  exact lt_of_le_of_lt (min_le_right _ _) (by linarith)
