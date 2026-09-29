-- Prove2me | solution 1 for Gilbreath.chase_hunter_tao_finite_criterion
-- status  : ACCEPTED   (prove)
-- author  : @EvanLLL
-- created : 2026-09-25T09:53:47.177195+00:00
-- url     : https://prove2.me/submissions/6cf92511-15e5-4932-ba32-6e734537bac0

import Definitions.Def_gilbreath_triangle


-- BEGIN GilbreathDeterministicBridge_20260924.lean

namespace Gilbreath

private theorem absDiff_two_mul (a : ℕ → ℕ) (n : ℕ) :
    absDiff (fun j => 2 * a j) n = 2 * absDiff a n := by
  simp only [absDiff, Nat.cast_mul, Nat.cast_ofNat]
  have h : (2 : ℤ) * (a (n + 1) : ℤ) - 2 * (a n : ℤ) =
      2 * ((a (n + 1) : ℤ) - (a n : ℤ)) := by ring
  rw [h, Int.natAbs_mul]
  norm_num

theorem iterAbsDiff_two_mul (a : ℕ → ℕ) (k n : ℕ) :
    iterAbsDiff (fun j => 2 * a j) k n = 2 * iterAbsDiff a k n := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih =>
      change absDiff (iterAbsDiff (fun j => 2 * a j) k) n =
        2 * absDiff (iterAbsDiff a k) n
      have hf : iterAbsDiff (fun j => 2 * a j) k =
          fun j => 2 * iterAbsDiff a k j := by
        funext j
        exact ih j
      rw [hf]
      exact absDiff_two_mul (iterAbsDiff a k) n

theorem iterAbsDiff_shift (a : ℕ → ℕ) (k n : ℕ) :
    iterAbsDiff (fun j => a (j + 1)) k n = iterAbsDiff a k (n + 1) := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih =>
      change absDiff (iterAbsDiff (fun j => a (j + 1)) k) n =
        absDiff (iterAbsDiff a k) (n + 1)
      simp [absDiff, ih, Nat.add_assoc]

theorem half_tail_exists
    (h_even : ∀ n, Even (d 1 (n + 1))) :
    ∃ b : ℕ → ℕ, ∀ n, d 1 (n + 1) = 2 * b n := by
  choose b hb using h_even
  refine ⟨b, ?_⟩
  intro n
  simpa [two_mul] using hb n

theorem d_normalized_tail (b : ℕ → ℕ)
    (hb : ∀ n, d 1 (n + 1) = 2 * b n) (k n : ℕ) :
    d (k + 1) (n + 1) = 2 * iterAbsDiff b k n := by
  have hd : d (k + 1) = iterAbsDiff (d 1) k := by
    simpa [Nat.add_comm] using (iterAbsDiff_d 1 k).symm
  rw [hd]
  rw [← iterAbsDiff_shift (d 1) k n]
  have hfun : (fun j => d 1 (j + 1)) = fun j => 2 * b j := by
    funext j
    exact hb j
  rw [hfun, iterAbsDiff_two_mul]

theorem zero_two_blocks_of_normalized_tail (b : ℕ → ℕ)
    (hb : ∀ n, d 1 (n + 1) = 2 * b n)
    (hgood : ∀ k, iterAbsDiff b k 0 = 0 ∨ iterAbsDiff b k 0 = 1)
    (K : ℕ) :
    ∃ k m : ℕ, 1 ≤ k ∧ k + m = K + 1 ∧
      ∀ n, 1 ≤ n → n ≤ m + 1 → d k n = 0 ∨ d k n = 2 := by
  refine ⟨K + 1, 0, by omega, by omega, ?_⟩
  intro n hn hnm
  have hn1 : n = 1 := by omega
  subst n
  have hd := d_normalized_tail b hb K 0
  rcases hgood K with hz | ho
  · left
    simpa [hz] using hd
  · right
    simpa [ho] using hd

end Gilbreath

-- END GilbreathDeterministicBridge_20260924.lean


-- BEGIN GilbreathDeterministicSplit_20260925.lean

namespace Gilbreath

/-!
A zero-based transcription of Chase--Hunter--Tao, Theorem 1.6
(arXiv:2607.08712v1, pp. 7--8). The paper uses input indices 1..N;
here input a 0 corresponds to its a₁.
-/

def FiniteCriterionBounds (N N' M L : ℕ) (R : ℕ → ℕ) : Prop :=
  1 ≤ N' ∧ N' ≤ N ∧ 1 ≤ M ∧ 1 ≤ L ∧
  1 < R 0 ∧
  (∀ m, m < M → R m < R (m + 1)) ∧
  2 * R M + N' < N ∧
  (∀ m, 1 ≤ m → m ≤ M → 4 * R (m - 1) ≤ R m) ∧
  100 * L * 8 ^ M ≤ R 0

def NoLongZeroBlock (a : ℕ → ℕ) (N L : ℕ) : Prop :=
  ¬ ∃ i j : ℕ,
    i + L ≤ N ∧ j + i + L ≤ N ∧
    ∀ t < L, iterAbsDiff a i (j + t) = 0

def NoLongShallowTwoBlock
    (a : ℕ → ℕ) (N N' M : ℕ) (R : ℕ → ℕ) : Prop :=
  ¬ ∃ m d i k j : ℕ,
    1 ≤ m ∧ m ≤ M ∧
    2 ^ (M - m) < d ∧ d ≤ 2 ^ (M - m + 1) ∧
    i ≤ 2 * R (m - 1) ∧
    R m ≤ k + 3 * R (m - 1) ∧
    N' ≤ j + 1 ∧ j + i + k + 1 ≤ N ∧
    ∀ t < k, iterAbsDiff a i (j + t) = 0 ∨
      iterAbsDiff a i (j + t) = d

/-- The precise finite implication to be formalized from Theorem 1.6.
This is a proposition, not an asserted or proved theorem. -/
def FiniteDeterministicCriterion : Prop :=
  ∀ (a : ℕ → ℕ) (N N' M L : ℕ) (R : ℕ → ℕ),
    FiniteCriterionBounds N N' M L R →
    (∀ j < N, a j ≤ 2 ^ M) →
    NoLongZeroBlock a N L →
    NoLongShallowTwoBlock a N N' M R →
    iterAbsDiff a (N - 1) 0 = 0 ∨
      iterAbsDiff a (N - 1) 0 = 1

/-- The open arithmetic work needed to apply the finite criterion to the
halved prime-gap tail. This proposition asserts parameter choices at every
finite length and is not established by the cited paper. -/
def PrimeGapCriterionConditions (b : ℕ → ℕ) : Prop :=
  ∃ N₀ : ℕ,
    (∀ N, 1 ≤ N → N ≤ N₀ →
      iterAbsDiff b (N - 1) 0 = 0 ∨
      iterAbsDiff b (N - 1) 0 = 1) ∧
    (∀ N, N₀ < N →
      ∃ N' M L : ℕ, ∃ R : ℕ → ℕ,
        FiniteCriterionBounds N N' M L R ∧
        (∀ j < N, b j ≤ 2 ^ M) ∧
        NoLongZeroBlock b N L ∧
        NoLongShallowTwoBlock b N N' M R)

/-- A checked reduction of the platform target to the published finite
criterion and the still-open prime-gap conditions. -/
theorem zero_two_blocks_of_finite_criterion
    (b : ℕ → ℕ)
    (hb : ∀ n, d 1 (n + 1) = 2 * b n)
    (hfinite : FiniteDeterministicCriterion)
    (hgaps : PrimeGapCriterionConditions b)
    (K : ℕ) :
    ∃ k m : ℕ, 1 ≤ k ∧ k + m = K + 1 ∧
      ∀ n, 1 ≤ n → n ≤ m + 1 → d k n = 0 ∨ d k n = 2 := by
  obtain ⟨N₀, hsmall, hlarge⟩ := hgaps
  apply zero_two_blocks_of_normalized_tail b hb
  intro k
  by_cases hk : k + 1 ≤ N₀
  · simpa using hsmall (k + 1) (by omega) hk
  · obtain ⟨N', M, L, R, hbounds, hinput, hzero, htwo⟩ :=
      hlarge (k + 1) (by omega)
    simpa using hfinite b (k + 1) N' M L R
      hbounds hinput hzero htwo

end Gilbreath

-- END GilbreathDeterministicSplit_20260925.lean


-- BEGIN GilbreathFiniteCriterionLemmas_20260925.lean

namespace Gilbreath

/-- Chase--Hunter--Tao, Lemma 3.7(ii), for an entire row. -/
theorem iterAbsDiff_bounded (a : ℕ → ℕ) (B : ℕ)
    (ha : ∀ n, a n ≤ B) (k n : ℕ) :
    iterAbsDiff a k n ≤ B := by
  induction k generalizing n with
  | zero => exact ha n
  | succ k ih =>
      change absDiff (iterAbsDiff a k) n ≤ B
      unfold absDiff
      have hleft := ih n
      have hright := ih (n + 1)
      omega

/-- Chase--Hunter--Tao, Lemma 3.7(iii), for an entire row. -/
theorem iterAbsDiff_zero_or (a : ℕ → ℕ) (D : ℕ)
    (ha : ∀ n, a n = 0 ∨ a n = D) (k n : ℕ) :
    iterAbsDiff a k n = 0 ∨ iterAbsDiff a k n = D := by
  induction k generalizing n with
  | zero => exact ha n
  | succ k ih =>
      have hleft := ih n
      have hright := ih (n + 1)
      rcases hleft with hleft | hleft <;>
        rcases hright with hright | hright <;>
        simp [iterAbsDiff, absDiff, hleft, hright]

/-- Lemma 3.7(ii) for a finite ancestor block of length k+1. -/
theorem iterAbsDiff_bounded_window (a : ℕ → ℕ) (B : ℕ) :
    ∀ k n : ℕ,
      (∀ t, t ≤ k → a (n + t) ≤ B) →
      iterAbsDiff a k n ≤ B := by
  intro k
  induction k with
  | zero =>
      intro n h
      simpa using h 0 (by omega)
  | succ k ih =>
      intro n h
      have hl : iterAbsDiff a k n ≤ B := ih n (by
        intro t ht
        exact h t (by omega))
      have hr : iterAbsDiff a k (n + 1) ≤ B := ih (n + 1) (by
        intro t ht
        have heq : n + 1 + t = n + (t + 1) := by omega
        rw [heq]
        exact h (t + 1) (by omega))
      change absDiff (iterAbsDiff a k) n ≤ B
      unfold absDiff
      omega

/-- Lemma 3.7(iii) for a finite ancestor block of length k+1. -/
theorem iterAbsDiff_zero_or_window (a : ℕ → ℕ) (D : ℕ) :
    ∀ k n : ℕ,
      (∀ t, t ≤ k → a (n + t) = 0 ∨ a (n + t) = D) →
      iterAbsDiff a k n = 0 ∨ iterAbsDiff a k n = D := by
  intro k
  induction k with
  | zero =>
      intro n h
      simpa using h 0 (by omega)
  | succ k ih =>
      intro n h
      have hl : iterAbsDiff a k n = 0 ∨ iterAbsDiff a k n = D := ih n (by
        intro t ht
        exact h t (by omega))
      have hr : iterAbsDiff a k (n + 1) = 0 ∨
          iterAbsDiff a k (n + 1) = D := ih (n + 1) (by
        intro t ht
        have heq : n + 1 + t = n + (t + 1) := by omega
        rw [heq]
        exact h (t + 1) (by omega))
      rcases hl with hl | hl <;>
        rcases hr with hr | hr <;>
        simp [iterAbsDiff, absDiff, hl, hr]

end Gilbreath

-- END GilbreathFiniteCriterionLemmas_20260925.lean


-- BEGIN GilbreathParentage_20260925.lean

namespace Gilbreath

private theorem abs_step_orientation (x y D : ℕ)
    (h : Int.natAbs ((y : ℤ) - (x : ℤ)) = D) :
    y + D = x ∨ x + D = y := by
  omega

private theorem two_value_next (r D x y : ℕ)
    (hr : r < D) (hy : y < 2 * D)
    (hx : x = r ∨ x = r + D)
    (hxy : Int.natAbs ((y : ℤ) - (x : ℤ)) = 0 ∨
      Int.natAbs ((y : ℤ) - (x : ℤ)) = D) :
    y = r ∨ y = r + D := by
  rcases hxy with hz | hd
  · have : y = x := by omega
    omega
  · rcases abs_step_orientation x y D hd with hleft | hright
    · omega
    · omega

/-- The two-value part of Chase--Hunter--Tao, Lemma 3.8. -/
theorem parent_block_two_values (a : ℕ → ℕ) (n k D : ℕ)
    (hD : 0 < D)
    (hbound : ∀ t, t ≤ k → a (n + t) < 2 * D)
    (hchild : ∀ t, t < k →
      absDiff a (n + t) = 0 ∨ absDiff a (n + t) = D) :
    ∃ r, r < D ∧
      ∀ t, t ≤ k → a (n + t) = r ∨ a (n + t) = r + D := by
  let r := if a n < D then a n else a n - D
  have hr : r < D := by
    dsimp [r]
    split_ifs with h
    · exact h
    · have hb : a n < 2 * D := by simpa using hbound 0 (by omega)
      omega
  have hstart : a n = r ∨ a n = r + D := by
    dsimp [r]
    split_ifs with h
    · exact Or.inl rfl
    · right
      have hb : a n < 2 * D := by simpa using hbound 0 (by omega)
      omega
  refine ⟨r, hr, ?_⟩
  intro t
  induction t with
  | zero =>
      intro _
      simpa using hstart
  | succ t ih =>
      intro ht
      have hprev := ih (by omega)
      have hnextBound := hbound (t + 1) (by omega)
      have hdiff := hchild t (by omega)
      have hstep : Int.natAbs
          ((a (n + t + 1) : ℤ) - (a (n + t) : ℤ)) = 0 ∨
          Int.natAbs
          ((a (n + t + 1) : ℤ) - (a (n + t) : ℤ)) = D := by
        simpa [absDiff, Nat.add_assoc] using hdiff
      have hn := two_value_next r D (a (n + t)) (a (n + t + 1))
        hr (by simpa [Nat.add_assoc] using hnextBound) hprev hstep
      simpa [Nat.add_assoc] using hn

/-- A nonzero child difference forces both parent values to occur. -/
theorem parent_block_attains_both (a : ℕ → ℕ) (n k D : ℕ)
    (hD : 0 < D)
    (hbound : ∀ t, t ≤ k → a (n + t) < 2 * D)
    (hchild : ∀ t, t < k →
      absDiff a (n + t) = 0 ∨ absDiff a (n + t) = D)
    (hatt : ∃ t, t < k ∧ absDiff a (n + t) = D) :
    ∃ r, r < D ∧
      (∀ t, t ≤ k → a (n + t) = r ∨ a (n + t) = r + D) ∧
      (∃ u, u ≤ k ∧ a (n + u) = r) ∧
      (∃ v, v ≤ k ∧ a (n + v) = r + D) := by
  obtain ⟨r, hr, hparent⟩ :=
    parent_block_two_values a n k D hD hbound hchild
  obtain ⟨t, htk, hd⟩ := hatt
  have hl := hparent t (by omega)
  have hr' : a (n + t + 1) = r ∨ a (n + t + 1) = r + D := by
    simpa [Nat.add_assoc] using hparent (t + 1) (by omega)
  have horient : a (n + t + 1) + D = a (n + t) ∨
      a (n + t) + D = a (n + t + 1) := by
    apply abs_step_orientation
    simpa [absDiff, Nat.add_assoc] using hd
  have hpair :
      (a (n + t) = r ∧ a (n + t + 1) = r + D) ∨
      (a (n + t) = r + D ∧ a (n + t + 1) = r) := by
    rcases hl with hl | hl <;> rcases hr' with hr' | hr' <;>
      omega
  rcases hpair with ⟨hl, hr'⟩ | ⟨hl, hr'⟩
  · refine ⟨r, hr, hparent, ⟨t, by omega, hl⟩, ⟨t + 1, by omega, ?_⟩⟩
    simpa [Nat.add_assoc] using hr'
  · refine ⟨r, hr, hparent, ⟨t + 1, by omega, ?_⟩, ⟨t, by omega, hl⟩⟩
    simpa [Nat.add_assoc] using hr'

/-- A local, zero-based form of Chase--Hunter--Tao, Lemma 3.8. -/
theorem parent_block_trichotomy (a : ℕ → ℕ) (n k D : ℕ)
    (hD : 0 < D)
    (hchild : ∀ t, t < k →
      absDiff a (n + t) = 0 ∨ absDiff a (n + t) = D)
    (hatt : ∃ t, t < k ∧ absDiff a (n + t) = D) :
    (∃ u, u ≤ k ∧ 2 * D ≤ a (n + u)) ∨
    ((∀ t, t ≤ k → a (n + t) = 0 ∨ a (n + t) = D) ∧
      (∃ u, u ≤ k ∧ a (n + u) = 0) ∧
      (∃ v, v ≤ k ∧ a (n + v) = D)) ∨
    (∃ r, 0 < r ∧ r < D ∧
      (∀ t, t ≤ k → a (n + t) = r ∨ a (n + t) = r + D) ∧
      (∃ u, u ≤ k ∧ a (n + u) = r) ∧
      (∃ v, v ≤ k ∧ a (n + v) = r + D)) := by
  by_cases hbig : ∃ u, u ≤ k ∧ 2 * D ≤ a (n + u)
  · exact Or.inl hbig
  · right
    have hbound : ∀ t, t ≤ k → a (n + t) < 2 * D := by
      intro t ht
      by_contra hn
      apply hbig
      exact ⟨t, ht, by omega⟩
    obtain ⟨r, hr, hparent, hattR, hattRD⟩ :=
      parent_block_attains_both a n k D hD hbound hchild hatt
    by_cases hz : r = 0
    · left
      refine ⟨?_, ?_, ?_⟩
      · intro t ht
        simpa [hz] using hparent t ht
      · obtain ⟨u, hu, hv⟩ := hattR
        exact ⟨u, hu, by simpa [hz] using hv⟩
      · obtain ⟨v, hv, hw⟩ := hattRD
        exact ⟨v, hv, by simpa [hz] using hw⟩
    · right
      exact ⟨r, by omega, hr, hparent, hattR, hattRD⟩

end Gilbreath

-- END GilbreathParentage_20260925.lean


-- BEGIN GilbreathFiniteCriterionDevelopment_20260925.lean

namespace Gilbreath

theorem iterAbsDiff_add (a : ℕ → ℕ) (i h : ℕ) :
    iterAbsDiff (iterAbsDiff a i) h = iterAbsDiff a (i + h) := by
  induction h with
  | zero => simp
  | succ h ih =>
      rw [iterAbsDiff_succ, ih, ← Nat.add_assoc, iterAbsDiff_succ]

/-- Lemma 3.7(ii) inside a finite triangle. -/
theorem finite_triangle_bounded (a : ℕ → ℕ) (N B i j : ℕ)
    (hinput : ∀ t < N, a t ≤ B)
    (hvalid : i + j < N) :
    iterAbsDiff a i j ≤ B := by
  apply iterAbsDiff_bounded_window a B i j
  intro t ht
  exact hinput (j + t) (by omega)

/-- A large descendant forces a large value in its finite ancestor window. -/
theorem ancestor_window_above (a : ℕ → ℕ) (i j depth D : ℕ)
    (hlarge : D ≤ iterAbsDiff a (i + depth) j) :
    ∃ t, t ≤ depth ∧ D ≤ iterAbsDiff a i (j + t) := by
  by_cases hD : D = 0
  · exact ⟨0, by omega, by simp [hD]⟩
  · by_contra hnone
    have hsmall : ∀ t, t ≤ depth →
        iterAbsDiff a i (j + t) ≤ D - 1 := by
      intro t ht
      have hn : ¬ D ≤ iterAbsDiff a i (j + t) := by
        intro hd
        exact hnone ⟨t, ht, hd⟩
      omega
    have hb := iterAbsDiff_bounded_window
      (iterAbsDiff a i) (D - 1) depth j hsmall
    have hbelow : iterAbsDiff a (i + depth) j ≤ D - 1 := by
      simpa only [iterAbsDiff_add] using hb
    omega

/-- An adjacent pair of scales where a finite property first fails. -/
private theorem first_failed_scale (P : ℕ → Prop) (M : ℕ)
    (hzero : P 0) (hlast : ¬ P M) :
    ∃ m, 1 ≤ m ∧ m ≤ M ∧ P (m - 1) ∧ ¬ P m := by
  induction M with
  | zero => exact False.elim (hlast hzero)
  | succ M ih =>
      by_cases hprev : P M
      · exact ⟨M + 1, by omega, by omega, by simpa using hprev, hlast⟩
      · obtain ⟨m, hm, hmM, hgood, hbad⟩ := ih hprev
        exact ⟨m, hm, by omega, hgood, hbad⟩

/-- Boundedness of the portion of one row inside the right subtriangle. -/
def RightTriangleRowBounded
    (a : ℕ → ℕ) (N N' row B : ℕ) : Prop :=
  ∀ j, N' ≤ j + 1 → row + j < N → iterAbsDiff a row j ≤ B

/-- The first failing scale contains a point between two adjacent dyadic
bounds, as in the scale-selection part of CHT Proposition 5.3. -/
theorem first_dyadic_scale_transition
    (a : ℕ → ℕ) (N N' M : ℕ) (R : ℕ → ℕ)
    (hR : ∀ m, m < M → R m < R (m + 1))
    (hstart : RightTriangleRowBounded a N N' (R 0) (2 ^ M))
    (hend : ¬ RightTriangleRowBounded a N N' (R M) 1) :
    ∃ m j, 1 ≤ m ∧ m ≤ M ∧
      N' ≤ j + 1 ∧ R m + j < N ∧
      2 ^ (M - m) < iterAbsDiff a (R m) j ∧
      (∀ depth offset, depth + offset ≤ R m - R (m - 1) →
        iterAbsDiff a (R (m - 1) + depth) (j + offset) ≤
          2 ^ (M - m + 1)) := by
  let P : ℕ → Prop := fun m =>
    RightTriangleRowBounded a N N' (R m) (2 ^ (M - m))
  have hzero : P 0 := by simpa [P] using hstart
  have hlast : ¬ P M := by simpa [P] using hend
  obtain ⟨m, hm, hmM, hgood, hbad⟩ :=
    first_failed_scale P M hzero hlast
  have hwitness :
      ∃ j, N' ≤ j + 1 ∧ R m + j < N ∧
        2 ^ (M - m) < iterAbsDiff a (R m) j := by
    by_contra hnone
    apply hbad
    intro j hj hvalid
    by_contra hnotle
    apply hnone
    exact ⟨j, hj, hvalid, by omega⟩
  obtain ⟨j, hj, hvalid, hbig⟩ := hwitness
  have hRstep : R (m - 1) ≤ R m := by
    have heq : m - 1 + 1 = m := by omega
    have hlt := hR (m - 1) (by omega)
    rw [heq] at hlt
    omega
  let depth := R m - R (m - 1)
  have hsum : R (m - 1) + depth = R m := by
    dsimp [depth]
    omega
  have htriangle (d s : ℕ) (hds : d + s ≤ depth) :
      iterAbsDiff a (R (m - 1) + d) (j + s) ≤
        2 ^ (M - (m - 1)) := by
    have hwindow : ∀ t, t ≤ d →
        iterAbsDiff a (R (m - 1)) ((j + s) + t) ≤
          2 ^ (M - (m - 1)) := by
      intro t ht
      apply hgood ((j + s) + t)
      · omega
      · omega
    have hb := iterAbsDiff_bounded_window
      (iterAbsDiff a (R (m - 1)))
      (2 ^ (M - (m - 1))) d (j + s) hwindow
    simpa only [iterAbsDiff_add] using hb
  have hexp : M - (m - 1) = M - m + 1 := by omega
  refine ⟨m, j, hm, hmM, hj, hvalid, hbig, ?_⟩
  intro d s hds
  simpa [hexp] using htriangle d s hds

/-- Lemma 3.7(iii): descendants of a finite {0,D} block
remain {0,D}-valued. -/
theorem finite_two_block_inherits (a : ℕ → ℕ) (i j k D : ℕ)
    (hblock : ∀ t < k,
      iterAbsDiff a i (j + t) = 0 ∨
      iterAbsDiff a i (j + t) = D)
    (depth t : ℕ) (hdepth : depth < k) (ht : t + depth < k) :
    iterAbsDiff a (i + depth) (j + t) = 0 ∨
      iterAbsDiff a (i + depth) (j + t) = D := by
  have hwindow :
      ∀ s, s ≤ depth →
        iterAbsDiff a i (j + t + s) = 0 ∨
        iterAbsDiff a i (j + t + s) = D := by
    intro s hs
    simpa [Nat.add_assoc] using hblock (t + s) (by omega)
  have h := iterAbsDiff_zero_or_window
    (iterAbsDiff a i) D depth (j + t) hwindow
  simpa [iterAbsDiff_add] using h

/-- Consequence (ii') in Section 5: a sufficiently long
{0,D}-valued block cannot contain only zeros. -/
theorem long_two_block_attains (a : ℕ → ℕ) (N L i j k D : ℕ)
    (hzero : NoLongZeroBlock a N L)
    (hvalid : j + i + k ≤ N)
    (hL : L ≤ k)
    (hblock : ∀ t < k,
      iterAbsDiff a i (j + t) = 0 ∨
      iterAbsDiff a i (j + t) = D) :
    ∃ t, t < L ∧ iterAbsDiff a i (j + t) = D := by
  by_contra hnone
  have hallzero : ∀ t < L, iterAbsDiff a i (j + t) = 0 := by
    intro t ht
    rcases hblock t (by omega) with hz | hd
    · exact hz
    · exfalso
      exact hnone ⟨t, ht, hd⟩
  apply hzero
  exact ⟨i, j, by omega, by omega, hallzero⟩

/-- The parent dichotomy used in the induction of CHT Lemma 5.1.
A two-valued child block either has a two-valued parent block, or
some parent value is strictly larger than its nonzero child value. -/
theorem parent_block_dichotomy (a : ℕ → ℕ) (i j k D : ℕ)
    (hi : 0 < i) (hD : 0 < D)
    (hchild : ∀ t < k,
      iterAbsDiff a i (j + t) = 0 ∨
      iterAbsDiff a i (j + t) = D)
    (hatt : ∃ t, t < k ∧ iterAbsDiff a i (j + t) = D) :
    ((∀ t, t ≤ k →
      iterAbsDiff a (i - 1) (j + t) = 0 ∨
      iterAbsDiff a (i - 1) (j + t) = D) ∧
     (∃ t, t ≤ k ∧ iterAbsDiff a (i - 1) (j + t) = D)) ∨
    (∃ t, t ≤ k ∧ D < iterAbsDiff a (i - 1) (j + t)) := by
  have heq : i - 1 + 1 = i := by omega
  have hrow (n : ℕ) :
      iterAbsDiff a i n = absDiff (iterAbsDiff a (i - 1)) n := by
    calc
      iterAbsDiff a i n =
          iterAbsDiff a (i - 1 + 1) n := by rw [heq]
      _ = absDiff (iterAbsDiff a (i - 1)) n := by
        rw [iterAbsDiff_succ]
  have hchild' : ∀ t < k,
      absDiff (iterAbsDiff a (i - 1)) (j + t) = 0 ∨
      absDiff (iterAbsDiff a (i - 1)) (j + t) = D := by
    intro t ht
    simpa only [hrow] using hchild t ht
  have hatt' : ∃ t, t < k ∧
      absDiff (iterAbsDiff a (i - 1)) (j + t) = D := by
    obtain ⟨t, ht, hd⟩ := hatt
    exact ⟨t, ht, by simpa only [hrow] using hd⟩
  rcases parent_block_trichotomy
      (iterAbsDiff a (i - 1)) j k D hD hchild' hatt' with
    hbig | htwo | hshift
  · right
    obtain ⟨t, ht, hv⟩ := hbig
    exact ⟨t, ht, by omega⟩
  · exact Or.inl ⟨htwo.1, htwo.2.2⟩
  · right
    obtain ⟨r, hr, _, _, _, ⟨t, ht, hv⟩⟩ := hshift
    exact ⟨t, ht, by omega⟩

/-- The critical length-L parent step in the proof of CHT Lemma 5.1.
If the parent has no value above D, both length-L subblocks must attain D. -/
theorem parent_block_large_or_two_attaining
    (a : ℕ → ℕ) (N L i j D : ℕ)
    (hi : 0 < i) (hD : 0 < D)
    (hzero : NoLongZeroBlock a N L)
    (hvalid : j + i + L ≤ N)
    (hchild : ∀ t < L,
      iterAbsDiff a i (j + t) = 0 ∨
      iterAbsDiff a i (j + t) = D)
    (hatt : ∃ t, t < L ∧ iterAbsDiff a i (j + t) = D) :
    (∃ t, t ≤ L ∧ D < iterAbsDiff a (i - 1) (j + t)) ∨
    ((∃ u, u < L ∧ iterAbsDiff a (i - 1) (j + u) = D) ∧
     (∃ v, v < L ∧ iterAbsDiff a (i - 1) (j + 1 + v) = D)) := by
  rcases parent_block_dichotomy a i j L D hi hD hchild hatt with
    htwo | hlarge
  · right
    constructor
    · obtain ⟨u, hu, hv⟩ :=
        long_two_block_attains a N L (i - 1) j L D
          hzero (by omega) (by omega)
          (by
            intro t ht
            exact htwo.1 t (by omega))
      exact ⟨u, hu, hv⟩
    · obtain ⟨v, hv, hw⟩ :=
        long_two_block_attains a N L (i - 1) (j + 1) L D
          hzero (by omega) (by omega)
          (by
            intro t ht
            simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
              htwo.1 (t + 1) (by omega))
      exact ⟨v, hv, by simpa [Nat.add_assoc] using hw⟩
  · exact Or.inl hlarge

end Gilbreath

-- END GilbreathFiniteCriterionDevelopment_20260925.lean


-- BEGIN GilbreathCoarseMonotonicity_20260925.lean

namespace Gilbreath

private theorem nat_dist_smoke (x y : ℕ) :
    Nat.dist x y ≤ x + y := by
  unfold Nat.dist
  omega

private theorem centered_block_distance (i j k q t : ℕ)
    (hk : 1 ≤ k) (ht : t < k) :
    2 * Nat.dist (j + t) q ≤
      Nat.dist (2 * q + i) (2 * j + i + k - 1) + (k - 1) := by
  unfold Nat.dist
  omega

/-- The same-depth starting case of the doubled-coordinate bound in
CHT Lemma 5.1. The selected point is an entry of the given block. -/
theorem coarse_inductive_same_row_base
    (i j k q t B D L : ℕ)
    (hk : 1 ≤ k) (ht : t < k) (hkL : k ≤ L)
    (hDB : D ≤ B) :
    2 * Nat.dist (j + t) q ≤
      (Nat.dist (2 * q + i) (2 * j + i + k - 1) - (k - 1)) +
        (B - D + 1) * (2 * L + 1) := by
  have hgeom := centered_block_distance i j k q t hk ht
  have hcoef : 1 ≤ B - D + 1 := by omega
  have hbudget : 2 * L + 1 ≤ (B - D + 1) * (2 * L + 1) := by
    simpa using Nat.mul_le_mul_right (2 * L + 1) hcoef
  omega

/-- The doubled-coordinate inductive statement of CHT Lemma 5.1,
restricted to a finite triangle. -/
def CoarseInductiveClaim
    (a : ℕ → ℕ) (N B L i : ℕ) : Prop :=
  ∀ j k D i' q : ℕ,
    1 ≤ k → k ≤ L → i + j + k ≤ N →
    1 ≤ D → D ≤ B →
    (∀ t < k, iterAbsDiff a i (j + t) = 0 ∨
      iterAbsDiff a i (j + t) = D) →
    (∃ t, t < k ∧ iterAbsDiff a i (j + t) = D) →
    i' ≤ i → i' + q < N →
    ∃ p, i' + p < N ∧
      j ≤ p ∧ p ≤ j + (i - i') + (k - 1) ∧
      D ≤ iterAbsDiff a i' p ∧
      2 * Nat.dist p q ≤
        (Nat.dist (2 * q + i') (2 * j + i + k - 1) -
          (i - i') - (k - 1)) +
          (B - D + 1) * (2 * L + 1)

/-- The same-row branch of the inductive claim. -/
theorem coarse_claim_same_row
    (a : ℕ → ℕ) (N B L i j k D q : ℕ)
    (hk : 1 ≤ k) (hkL : k ≤ L) (hvalid : i + j + k ≤ N)
    (hDB : D ≤ B)
    (hatt : ∃ t, t < k ∧ iterAbsDiff a i (j + t) = D) :
    ∃ p, i + p < N ∧
      j ≤ p ∧ p ≤ j + (k - 1) ∧
      D ≤ iterAbsDiff a i p ∧
      2 * Nat.dist p q ≤
        (Nat.dist (2 * q + i) (2 * j + i + k - 1) -
          (i - i) - (k - 1)) +
          (B - D + 1) * (2 * L + 1) := by
  obtain ⟨t, ht, hv⟩ := hatt
  refine ⟨j + t, by omega, by omega, by omega, by omega, ?_⟩
  simpa using coarse_inductive_same_row_base
    i j k q t B D L hk ht hkL hDB

/-- The parent step of CHT Lemma 5.1 when the full parent block still
fits inside the length budget and remains two-valued. -/
theorem coarse_parent_same_value_step
    (a : ℕ → ℕ) (N B L i j k D i' q : ℕ)
    (hi : 0 < i) (hk : 1 ≤ k) (hkp : k + 1 ≤ L)
    (hvalid : i + j + k ≤ N)
    (hD : 1 ≤ D) (hDB : D ≤ B)
    (hparent : ∀ t < k + 1,
      iterAbsDiff a (i - 1) (j + t) = 0 ∨
      iterAbsDiff a (i - 1) (j + t) = D)
    (hatt : ∃ t, t < k + 1 ∧
      iterAbsDiff a (i - 1) (j + t) = D)
    (hIH : CoarseInductiveClaim a N B L (i - 1))
    (hi' : i' < i) (hq : i' + q < N) :
    ∃ p, i' + p < N ∧
      j ≤ p ∧ p ≤ j + (i - i') + (k - 1) ∧
      D ≤ iterAbsDiff a i' p ∧
      2 * Nat.dist p q ≤
        (Nat.dist (2 * q + i') (2 * j + i + k - 1) -
          (i - i') - (k - 1)) +
          (B - D + 1) * (2 * L + 1) := by
  obtain ⟨p, hpvalid, hpconeL, hpconeR, hpvalue, hpbound⟩ :=
    hIH j (k + 1) D i' q
      (by omega) hkp (by omega) hD hDB
      hparent hatt (by omega) hq
  have hcenter :
      2 * j + (i - 1) + (k + 1) - 1 =
        2 * j + i + k - 1 := by omega
  refine ⟨p, hpvalid, by omega, by omega, hpvalue, ?_⟩
  rw [hcenter] at hpbound
  omega

/-- The length-L cropping branch of CHT Lemma 5.1. The two shifted
parent blocks both attain D, so choose the one nearer the target point. -/
theorem coarse_parent_cropped_step
    (a : ℕ → ℕ) (N B L i j D i' q : ℕ)
    (hi : 0 < i) (hL : 2 ≤ L)
    (hvalid : i + j + L ≤ N)
    (hD : 1 ≤ D) (hDB : D ≤ B)
    (hparent : ∀ t < L + 1,
      iterAbsDiff a (i - 1) (j + t) = 0 ∨
      iterAbsDiff a (i - 1) (j + t) = D)
    (hleft : ∃ t, t < L ∧
      iterAbsDiff a (i - 1) (j + t) = D)
    (hright : ∃ t, t < L ∧
      iterAbsDiff a (i - 1) (j + 1 + t) = D)
    (hIH : CoarseInductiveClaim a N B L (i - 1))
    (hi' : i' < i) (hq : i' + q < N) :
    ∃ p, i' + p < N ∧
      j ≤ p ∧ p ≤ j + (i - i') + (L - 1) ∧
      D ≤ iterAbsDiff a i' p ∧
      2 * Nat.dist p q ≤
        (Nat.dist (2 * q + i') (2 * j + i + L - 1) -
          (i - i') - (L - 1)) +
          (B - D + 1) * (2 * L + 1) := by
  have hcenterLeft :
      (2 * j + (i - 1) + L - 1) + 1 =
        2 * j + i + L - 1 := by omega
  have hcenterRight :
      2 * (j + 1) + (i - 1) + L - 1 =
        (2 * j + i + L - 1) + 1 := by omega
  have hparentRight : ∀ t < L,
      iterAbsDiff a (i - 1) ((j + 1) + t) = 0 ∨
      iterAbsDiff a (i - 1) ((j + 1) + t) = D := by
    intro t ht
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      hparent (t + 1) (by omega)
  by_cases hside : 2 * q + i' ≤ 2 * j + i + L - 1
  · obtain ⟨p, hpvalid, hpconeL, hpconeR, hpvalue, hpbound⟩ :=
      hIH j L D i' q (by omega) (by omega) (by omega)
        hD hDB (by
          intro t ht
          exact hparent t (by omega)) hleft
        (by omega) hq
    refine ⟨p, hpvalid, by omega, by omega, hpvalue, ?_⟩
    unfold Nat.dist at hpbound ⊢
    omega
  · obtain ⟨p, hpvalid, hpconeL, hpconeR, hpvalue, hpbound⟩ :=
      hIH (j + 1) L D i' q (by omega) (by omega) (by omega)
        hD hDB hparentRight
        (by
          obtain ⟨t, ht, hv⟩ := hright
          exact ⟨t, ht, by simpa [Nat.add_assoc] using hv⟩)
        (by omega) hq
    refine ⟨p, hpvalid, by omega, by omega, hpvalue, ?_⟩
    unfold Nat.dist at hpbound ⊢
    omega

/-- The increasing-value branch of CHT Lemma 5.1. A larger parent
value pays for the movement to its location. -/
theorem coarse_parent_larger_step
    (a : ℕ → ℕ) (N B L i j k D i' q t : ℕ)
    (hi : 0 < i) (hk : 1 ≤ k) (hkL : k ≤ L)
    (hvalid : i + j + k ≤ N)
    (hD : 1 ≤ D) (hDB : D ≤ B)
    (hinput : ∀ u < N, a u ≤ B)
    (ht : t ≤ k)
    (hbig : D < iterAbsDiff a (i - 1) (j + t))
    (hIH : CoarseInductiveClaim a N B L (i - 1))
    (hi' : i' < i) (hq : i' + q < N) :
    ∃ p, i' + p < N ∧
      j ≤ p ∧ p ≤ j + (i - i') + (k - 1) ∧
      D ≤ iterAbsDiff a i' p ∧
      2 * Nat.dist p q ≤
        (Nat.dist (2 * q + i') (2 * j + i + k - 1) -
          (i - i') - (k - 1)) +
          (B - D + 1) * (2 * L + 1) := by
  let D' := iterAbsDiff a (i - 1) (j + t)
  have hD' : 1 ≤ D' := by dsimp [D']; omega
  have hDB' : D' ≤ B := by
    apply finite_triangle_bounded a N B (i - 1) (j + t) hinput
    omega
  have hparent : ∀ s < 1,
      iterAbsDiff a (i - 1) ((j + t) + s) = 0 ∨
      iterAbsDiff a (i - 1) ((j + t) + s) = D' := by
    intro s hs
    have hs0 : s = 0 := by omega
    subst s
    exact Or.inr (by simp [D'])
  have hatt : ∃ s, s < 1 ∧
      iterAbsDiff a (i - 1) ((j + t) + s) = D' :=
    ⟨0, by omega, by simp [D']⟩
  obtain ⟨p, hpvalid, hpconeL, hpconeR, hpvalue, hpbound⟩ :=
    hIH (j + t) 1 D' i' q
      (by omega) (by omega) (by omega)
      hD' hDB' hparent hatt (by omega) hq
  have hcenter :
      Nat.dist (2 * j + i + k - 1)
        (2 * (j + t) + (i - 1) + 1 - 1) ≤ k := by
    unfold Nat.dist
    omega
  have hdist :
      Nat.dist (2 * q + i')
        (2 * (j + t) + (i - 1) + 1 - 1) ≤
      Nat.dist (2 * q + i') (2 * j + i + k - 1) + k := by
    have htri := Nat.dist.triangle_inequality
      (2 * q + i') (2 * j + i + k - 1)
      (2 * (j + t) + (i - 1) + 1 - 1)
    omega
  have hgeom :
      (Nat.dist (2 * q + i')
        (2 * (j + t) + (i - 1) + 1 - 1) -
        ((i - 1) - i') - (1 - 1)) ≤
      (Nat.dist (2 * q + i') (2 * j + i + k - 1) -
        (i - i') - (k - 1)) + (2 * L + 1) := by
    omega
  have hfactor : (B - D' + 1) + 1 ≤ B - D + 1 := by
    dsimp [D'] at *
    omega
  have hgain :
      (B - D' + 1) * (2 * L + 1) + (2 * L + 1) ≤
        (B - D + 1) * (2 * L + 1) := by
    calc
      _ = ((B - D' + 1) + 1) * (2 * L + 1) := by ring
      _ ≤ _ := Nat.mul_le_mul_right (2 * L + 1) hfactor
  refine ⟨p, hpvalid, by omega, by omega, by omega, ?_⟩
  omega

/-- A length-one nonzero child cannot have a two-valued parent under
the no-single-zero condition. -/
private theorem singleton_parent_two_impossible
    (a : ℕ → ℕ) (N i j D : ℕ)
    (hi : 0 < i) (hD : 0 < D)
    (hzero : NoLongZeroBlock a N 1)
    (hvalid : i + j + 1 ≤ N)
    (hchild : iterAbsDiff a i j = D)
    (hparent : ∀ t, t ≤ 1 →
      iterAbsDiff a (i - 1) (j + t) = 0 ∨
      iterAbsDiff a (i - 1) (j + t) = D) : False := by
  obtain ⟨u, hu, hv⟩ :=
    long_two_block_attains a N 1 (i - 1) j 1 D
      hzero (by omega) (by omega)
      (by
        intro t ht
        exact hparent t (by omega))
  have hu0 : u = 0 := by omega
  have hleft : iterAbsDiff a (i - 1) j = D := by
    simpa [hu0] using hv
  obtain ⟨v, hv, hw⟩ :=
    long_two_block_attains a N 1 (i - 1) (j + 1) 1 D
      hzero (by omega) (by omega)
      (by
        intro t ht
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          hparent (t + 1) (by omega))
  have hv0 : v = 0 := by omega
  have hright : iterAbsDiff a (i - 1) (j + 1) = D := by
    simpa [hv0] using hw
  have heq : i - 1 + 1 = i := by omega
  have hrow :
      iterAbsDiff a i j =
        absDiff (iterAbsDiff a (i - 1)) j := by
    calc
      iterAbsDiff a i j = iterAbsDiff a (i - 1 + 1) j := by rw [heq]
      _ = absDiff (iterAbsDiff a (i - 1)) j := by
        rw [iterAbsDiff_succ]
  have hdiffzero :
      absDiff (iterAbsDiff a (i - 1)) j = 0 := by
    simp [absDiff, hleft, hright]
  rw [hrow, hdiffzero] at hchild
  omega

/-- Chase--Hunter--Tao Lemma 5.1 in doubled coordinates, for the
zero-based finite difference triangle. -/
theorem coarse_inductive_claim
    (a : ℕ → ℕ) (N B L : ℕ)
    (hinput : ∀ u < N, a u ≤ B)
    (hzero : NoLongZeroBlock a N L) :
    ∀ i, CoarseInductiveClaim a N B L i := by
  intro i
  induction i with
  | zero =>
      intro j k D i' q hk hkL hvalid hD hDB hchild hatt hi' hq
      have hi'0 : i' = 0 := by omega
      subst i'
      simpa using coarse_claim_same_row a N B L 0 j k D q
        hk hkL hvalid hDB hatt
  | succ i ih =>
      intro j k D i' q hk hkL hvalid hD hDB hchild hatt hi' hq
      by_cases hsame : i' = i + 1
      · subst i'
        simpa using coarse_claim_same_row a N B L (i + 1) j k D q
          hk hkL hvalid hDB hatt
      · have hbefore : i' < i + 1 := by omega
        rcases parent_block_dichotomy a (i + 1) j k D
            (by omega) (by omega) hchild hatt with
          htwo | hlarge
        · obtain ⟨hparent, hparentAtt⟩ := htwo
          have hparentBlock : ∀ t < k + 1,
              iterAbsDiff a i (j + t) = 0 ∨
              iterAbsDiff a i (j + t) = D := by
            intro t ht
            simpa using hparent t (by omega)
          have hparentAttBlock : ∃ t, t < k + 1 ∧
              iterAbsDiff a i (j + t) = D := by
            obtain ⟨t, ht, hv⟩ := hparentAtt
            exact ⟨t, by omega, by simpa using hv⟩
          by_cases hkp : k + 1 ≤ L
          · exact coarse_parent_same_value_step
              a N B L (i + 1) j k D i' q
              (by omega) hk hkp hvalid hD hDB
              (by simpa using hparentBlock)
              (by simpa using hparentAttBlock)
              (by simpa using ih) hbefore hq
          · have hkL_eq : k = L := by omega
            subst k
            by_cases hL1 : L = 1
            · subst L
              have hchildOne : iterAbsDiff a (i + 1) j = D := by
                obtain ⟨t, ht, hv⟩ := hatt
                have ht0 : t = 0 := by omega
                simpa [ht0] using hv
              exact False.elim
                (singleton_parent_two_impossible a N (i + 1) j D
                  (by omega) (by omega) hzero hvalid hchildOne
                  (by
                    intro t ht
                    simpa using hparent t ht))
            · have hL2 : 2 ≤ L := by omega
              have hleft : ∃ t, t < L ∧
                  iterAbsDiff a i (j + t) = D :=
                long_two_block_attains a N L i j L D
                  hzero (by omega) (by omega)
                  (by
                    intro t ht
                    exact hparentBlock t (by omega))
              have hright : ∃ t, t < L ∧
                  iterAbsDiff a i (j + 1 + t) = D := by
                obtain ⟨t, ht, hv⟩ :=
                  long_two_block_attains a N L i (j + 1) L D
                    hzero (by omega) (by omega)
                    (by
                      intro t ht
                      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
                        hparentBlock (t + 1) (by omega))
                exact ⟨t, ht, by simpa [Nat.add_assoc] using hv⟩
              exact coarse_parent_cropped_step
                a N B L (i + 1) j D i' q
                (by omega) hL2 hvalid hD hDB
                (by simpa using hparentBlock) hleft hright
                (by simpa using ih) hbefore hq
        · obtain ⟨t, ht, hv⟩ := hlarge
          exact coarse_parent_larger_step
            a N B L (i + 1) j k D i' q t
            (by omega) hk hkL hvalid hD hDB hinput
            ht hv (by simpa using ih) hbefore hq

/-- Chase--Hunter--Tao Lemma 5.2, with doubled horizontal distance
and an explicit finite-cone witness. -/
theorem coarse_monotonicity
    (a : ℕ → ℕ) (N B L i j D i' q : ℕ)
    (hinput : ∀ u < N, a u ≤ B)
    (hzero : NoLongZeroBlock a N L)
    (hL : 1 ≤ L) (hvalid : i + j < N)
    (hD : 1 ≤ D) (hDB : D ≤ B)
    (hpoint : iterAbsDiff a i j = D)
    (hi' : i' ≤ i)
    (hqleft : j ≤ q) (hqright : q ≤ j + (i - i')) :
    ∃ p, i' + p < N ∧
      j ≤ p ∧ p ≤ j + (i - i') ∧
      D ≤ iterAbsDiff a i' p ∧
      2 * Nat.dist p q ≤ B * (2 * L + 1) := by
  have hqvalid : i' + q < N := by omega
  have hblock : ∀ t < 1,
      iterAbsDiff a i (j + t) = 0 ∨
      iterAbsDiff a i (j + t) = D := by
    intro t ht
    have ht0 : t = 0 := by omega
    exact Or.inr (by simpa [ht0] using hpoint)
  have hatt : ∃ t, t < 1 ∧ iterAbsDiff a i (j + t) = D :=
    ⟨0, by omega, by simpa using hpoint⟩
  obtain ⟨p, hpvalid, hpleft, hpright, hpvalue, hpbound⟩ :=
    (coarse_inductive_claim a N B L hinput hzero i)
      j 1 D i' q
      (by omega) hL (by omega) hD hDB hblock hatt hi' hqvalid
  have hdist :
      Nat.dist (2 * q + i') (2 * j + i + 1 - 1) ≤ i - i' := by
    unfold Nat.dist
    omega
  have hfactor : B - D + 1 ≤ B := by omega
  have hbudget :
      (B - D + 1) * (2 * L + 1) ≤ B * (2 * L + 1) :=
    Nat.mul_le_mul_right (2 * L + 1) hfactor
  refine ⟨p, hpvalid, hpleft, by simpa using hpright, hpvalue, ?_⟩
  omega

/-- A sufficiently wide right-hand row must contain a value above one
when the bottom vertex does. This supplies the last-scale failure in
CHT Proposition 5.3, subject to a numerical margin. -/
theorem right_row_not_one_bounded_of_bottom
    (a : ℕ → ℕ) (N N' row B L : ℕ)
    (hinput : ∀ u < N, a u ≤ B)
    (hzero : NoLongZeroBlock a N L)
    (hL : 1 ≤ L) (hN' : 1 ≤ N')
    (hroom : row + (N' - 1 + B * (L + 1)) < N)
    (hbottom : 1 < iterAbsDiff a (N - 1) 0) :
    ¬ RightTriangleRowBounded a N N' row 1 := by
  let D := iterAbsDiff a (N - 1) 0
  let q := N' - 1 + B * (L + 1)
  have hN : 1 ≤ N := by omega
  have hrow : row ≤ N - 1 := by omega
  have hDB : D ≤ B := by
    apply finite_triangle_bounded a N B (N - 1) 0 hinput
    omega
  obtain ⟨p, hpvalid, _, _, hpvalue, hpdist⟩ :=
    coarse_monotonicity a N B L (N - 1) 0 D row q
      hinput hzero hL (by omega) (by dsimp [D]; omega)
      hDB rfl hrow (by omega) (by omega)
  have hbudget :
      B * (2 * L + 1) ≤ 2 * (B * (L + 1)) := by
    nlinarith
  have hdistA : Nat.dist p q ≤ B * (L + 1) := by omega
  have hpstart : N' ≤ p + 1 := by
    unfold Nat.dist at hdistA
    dsimp [q] at hdistA
    omega
  intro hbound
  have hone := hbound p hpstart hpvalid
  dsimp [D] at hpvalue
  omega

/-- The numerical separation in the deterministic criterion leaves
room for the coarse-monotonicity witness in the last right-hand row. -/
theorem finite_criterion_right_row_room
    (N N' M L : ℕ) (R : ℕ → ℕ)
    (hbounds : FiniteCriterionBounds N N' M L R) :
    R M + (N' - 1 + 2 ^ M * (L + 1)) < N := by
  rcases hbounds with
    ⟨hN', _, _, hL, _, hinc, hterminal, _, hlarge⟩
  have hR0 : ∀ n, n ≤ M → R 0 ≤ R n := by
    intro n hn
    induction n with
    | zero => exact le_rfl
    | succ n ih =>
        exact le_trans (ih (by omega))
          (le_of_lt (hinc n (by omega)))
  have hpow : (2 : ℕ) ^ M ≤ 8 ^ M := by
    gcongr
    omega
  have hAL : L + 1 ≤ 2 * L := by omega
  have hA : 2 ^ M * (L + 1) ≤ 100 * L * 8 ^ M := by
    calc
      _ ≤ 2 ^ M * (2 * L) := Nat.mul_le_mul_left _ hAL
      _ ≤ 8 ^ M * (2 * L) := Nat.mul_le_mul_right _ hpow
      _ = (2 * L) * 8 ^ M := by ring
      _ ≤ (100 * L) * 8 ^ M :=
        Nat.mul_le_mul_right _ (by omega)
      _ = 100 * L * 8 ^ M := by ring
  have hAM : 2 ^ M * (L + 1) ≤ R M :=
    le_trans (le_trans hA hlarge) (hR0 M (by omega))
  omega

/-- The last-scale failure required for the dyadic transition follows
from the finite criterion's own hypotheses. -/
theorem finite_criterion_last_scale_fails
    (a : ℕ → ℕ) (N N' M L : ℕ) (R : ℕ → ℕ)
    (hbounds : FiniteCriterionBounds N N' M L R)
    (hinput : ∀ u < N, a u ≤ 2 ^ M)
    (hzero : NoLongZeroBlock a N L)
    (hbottom : 1 < iterAbsDiff a (N - 1) 0) :
    ¬ RightTriangleRowBounded a N N' (R M) 1 := by
  have hN' : 1 ≤ N' := hbounds.1
  have hL : 1 ≤ L := hbounds.2.2.2.1
  exact right_row_not_one_bounded_of_bottom
    a N N' (R M) (2 ^ M) L
    hinput hzero hL hN'
    (finite_criterion_right_row_room N N' M L R hbounds)
    hbottom

/-- Chase--Hunter--Tao Proposition 5.3, in its scale-selection and
bounded-subtriangle form. The remaining geometric properties of the
triangle are encoded by the indices in the conclusion. -/
theorem finite_criterion_locates_large_triangle
    (a : ℕ → ℕ) (N N' M L : ℕ) (R : ℕ → ℕ)
    (hbounds : FiniteCriterionBounds N N' M L R)
    (hinput : ∀ u < N, a u ≤ 2 ^ M)
    (hzero : NoLongZeroBlock a N L)
    (hbottom : 1 < iterAbsDiff a (N - 1) 0) :
    ∃ m j, 1 ≤ m ∧ m ≤ M ∧
      N' ≤ j + 1 ∧ R m + j < N ∧
      2 ^ (M - m) < iterAbsDiff a (R m) j ∧
      (∀ depth offset, depth + offset ≤ R m - R (m - 1) →
        iterAbsDiff a (R (m - 1) + depth) (j + offset) ≤
          2 ^ (M - m + 1)) := by
  have hinc : ∀ m, m < M → R m < R (m + 1) := by
    rcases hbounds with ⟨_, _, _, _, _, hinc, _, _, _⟩
    exact hinc
  have hstart :
      RightTriangleRowBounded a N N' (R 0) (2 ^ M) := by
    intro j _ hvalid
    exact finite_triangle_bounded a N (2 ^ M) (R 0) j
      hinput (by omega)
  exact first_dyadic_scale_transition
    a N N' M R hinc hstart
    (finite_criterion_last_scale_fails
      a N N' M L R hbounds hinput hzero hbottom)

end Gilbreath

-- END GilbreathCoarseMonotonicity_20260925.lean


-- BEGIN GilbreathGoodBlocks_20260925.lean

namespace Gilbreath

/-- The nonzero values of two long-overlapping two-valued blocks agree.
This is the value-uniqueness core of CHT Lemma 5.5(i). -/
theorem long_two_block_overlap_same_value
    (a : ℕ → ℕ) (N L i j k j' k' s D E : ℕ)
    (hzero : NoLongZeroBlock a N L)
    (hD : 0 < D)
    (hvalid : i + s + L ≤ N)
    (hleft : j ≤ s) (hleftEnd : s + L ≤ j + k)
    (hright : j' ≤ s) (hrightEnd : s + L ≤ j' + k')
    (hblockD : ∀ t < k,
      iterAbsDiff a i (j + t) = 0 ∨
      iterAbsDiff a i (j + t) = D)
    (hblockE : ∀ t < k',
      iterAbsDiff a i (j' + t) = 0 ∨
      iterAbsDiff a i (j' + t) = E) :
    D = E := by
  have hoverlapD : ∀ t < L,
      iterAbsDiff a i (s + t) = 0 ∨
      iterAbsDiff a i (s + t) = D := by
    intro t ht
    have hindex : j + (s + t - j) = s + t := by omega
    simpa [hindex] using hblockD (s + t - j) (by omega)
  obtain ⟨t, ht, hvalueD⟩ :=
    long_two_block_attains a N L i s L D
      hzero (by omega) (by omega) hoverlapD
  have hindexE : j' + (s + t - j') = s + t := by omega
  have hvalueE :=
    hblockE (s + t - j') (by omega)
  rw [hindexE] at hvalueE
  rcases hvalueE with hz | hE
  · omega
  · omega

/-- A two-valued block maximal inside the half-open row interval
[left,right). This is the row-local part of a CHT good block. -/
def IsMaximalTwoBlock
    (a : ℕ → ℕ) (i left right j k D : ℕ) : Prop :=
  left ≤ j ∧ j + k ≤ right ∧ 1 ≤ k ∧
  (∀ t < k, iterAbsDiff a i (j + t) = 0 ∨
    iterAbsDiff a i (j + t) = D) ∧
  (∃ t, t < k ∧ iterAbsDiff a i (j + t) = D) ∧
  (j = left ∨
    ¬ (iterAbsDiff a i (j - 1) = 0 ∨
       iterAbsDiff a i (j - 1) = D)) ∧
  (j + k = right ∨
    ¬ (iterAbsDiff a i (j + k) = 0 ∨
       iterAbsDiff a i (j + k) = D))

/-- Two maximal blocks with the same nonzero value and a common entry
have the same endpoints. -/
theorem maximal_two_block_unique_on_overlap
    (a : ℕ → ℕ) (i left right j k j' k' D : ℕ)
    (hfirst : IsMaximalTwoBlock a i left right j k D)
    (hsecond : IsMaximalTwoBlock a i left right j' k' D)
    (hoverlap1 : j < j' + k')
    (hoverlap2 : j' < j + k) :
    j = j' ∧ k = k' := by
  rcases hfirst with
    ⟨hlo, hhi, hk, hblock, _, hmaxL, hmaxR⟩
  rcases hsecond with
    ⟨hlo', hhi', hk', hblock', _, hmaxL', hmaxR'⟩
  have hnotFirstLeft : ¬ j < j' := by
    intro hlt
    rcases hmaxL' with hborder | hstop
    · omega
    · have hindex : j + (j' - 1 - j) = j' - 1 := by omega
      have hv := hblock (j' - 1 - j) (by omega)
      rw [hindex] at hv
      exact hstop hv
  have hnotSecondLeft : ¬ j' < j := by
    intro hlt
    rcases hmaxL with hborder | hstop
    · omega
    · have hindex : j' + (j - 1 - j') = j - 1 := by omega
      have hv := hblock' (j - 1 - j') (by omega)
      rw [hindex] at hv
      exact hstop hv
  have hstart : j = j' := by omega
  subst j'
  have hnotShorter : ¬ k < k' := by
    intro hlt
    rcases hmaxR with hborder | hstop
    · omega
    · exact hstop (hblock' k (by omega))
  have hnotLonger : ¬ k' < k := by
    intro hlt
    rcases hmaxR' with hborder | hstop
    · omega
    · exact hstop (hblock k' (by omega))
  exact ⟨rfl, by omega⟩

/-- CHT Lemma 5.5(i): distinct maximal two-valued blocks cannot
overlap in a segment of length L. -/
theorem maximal_two_blocks_equal_of_long_overlap
    (a : ℕ → ℕ) (N L i left right j k j' k' s D E : ℕ)
    (hzero : NoLongZeroBlock a N L)
    (hL : 1 ≤ L) (hD : 0 < D)
    (hfirst : IsMaximalTwoBlock a i left right j k D)
    (hsecond : IsMaximalTwoBlock a i left right j' k' E)
    (hvalid : i + s + L ≤ N)
    (hleft : j ≤ s) (hleftEnd : s + L ≤ j + k)
    (hright : j' ≤ s) (hrightEnd : s + L ≤ j' + k') :
    j = j' ∧ k = k' ∧ D = E := by
  have hblockD : ∀ t < k,
      iterAbsDiff a i (j + t) = 0 ∨
      iterAbsDiff a i (j + t) = D :=
    hfirst.2.2.2.1
  have hblockE : ∀ t < k',
      iterAbsDiff a i (j' + t) = 0 ∨
      iterAbsDiff a i (j' + t) = E :=
    hsecond.2.2.2.1
  have hDE := long_two_block_overlap_same_value
    a N L i j k j' k' s D E hzero hD
    hvalid hleft hleftEnd hright hrightEnd
    hblockD hblockE
  subst E
  obtain ⟨hj, hk⟩ :=
    maximal_two_block_unique_on_overlap
      a i left right j k j' k' D
      hfirst hsecond (by omega) (by omega)
  exact ⟨hj, hk, rfl⟩

/-- Every nonzero entry in a finite row interval belongs to a maximal
two-valued block with that nonzero value. -/
theorem maximal_two_block_exists_through_point
    (a : ℕ → ℕ) (i left right p D : ℕ)
    (hleft : left ≤ p) (hright : p < right)
    (hpD : iterAbsDiff a i p = D) :
    ∃ j k, IsMaximalTwoBlock a i left right j k D ∧
      j ≤ p ∧ p < j + k := by
  classical
  let Two (x : ℕ) : Prop :=
    iterAbsDiff a i x = 0 ∨ iterAbsDiff a i x = D
  have hpTwo : Two p := Or.inr hpD
  let LeftOK (j : ℕ) : Prop :=
    left ≤ j ∧ j ≤ p ∧
      ∀ x, j ≤ x → x ≤ p → Two x
  have hLeftExists : ∃ j, LeftOK j := by
    refine ⟨p, hleft, le_refl p, ?_⟩
    intro x hx hxp
    have hxp' : x = p := by omega
    simpa [hxp'] using hpTwo
  let j := Nat.find hLeftExists
  have hjOK : LeftOK j := Nat.find_spec hLeftExists
  have hjleft : left ≤ j := hjOK.1
  have hjp : j ≤ p := hjOK.2.1
  have hjsegment : ∀ x, j ≤ x → x ≤ p → Two x := hjOK.2.2
  have hjmax : j = left ∨ ¬ Two (j - 1) := by
    by_cases hborder : j = left
    · exact Or.inl hborder
    · right
      intro hprev
      have hprevious : LeftOK (j - 1) := by
        refine ⟨by omega, by omega, ?_⟩
        intro x hx hxp
        by_cases hsame : x = j - 1
        · simpa [hsame] using hprev
        · exact hjsegment x (by omega) hxp
      have hmin : j ≤ j - 1 := Nat.find_min' hLeftExists hprevious
      omega
  let Bad (x : ℕ) : Prop :=
    p < x ∧ x < right ∧ ¬ Two x
  by_cases hBadExists : ∃ x, Bad x
  · let e := Nat.find hBadExists
    have heBad : Bad e := Nat.find_spec hBadExists
    have heSegment : ∀ x, p ≤ x → x < e → Two x := by
      intro x hpx hxe
      by_cases hxEq : x = p
      · simpa [hxEq] using hpTwo
      · by_contra hnotTwo
        have hxBad : Bad x := ⟨by omega, by omega, hnotTwo⟩
        have hmin : e ≤ x := Nat.find_min' hBadExists hxBad
        omega
    have hemax : e = right ∨ ¬ Two e := Or.inr heBad.2.2
    have hpe : p < e := heBad.1
    have heright : e ≤ right := by omega
    refine ⟨j, e - j, ?_, hjp, by omega⟩
    have hsum : j + (e - j) = e := by omega
    unfold IsMaximalTwoBlock
    refine ⟨hjleft, by omega, by omega, ?_, ?_, hjmax, ?_⟩
    · intro t ht
      by_cases hxp : j + t ≤ p
      · exact hjsegment (j + t) (by omega) hxp
      · exact heSegment (j + t) (by omega) (by omega)
    · refine ⟨p - j, by omega, ?_⟩
      have hindex : j + (p - j) = p := by omega
      simpa [hindex] using hpD
    · simpa [hsum, Two] using hemax
  · have heSegment : ∀ x, p ≤ x → x < right → Two x := by
      intro x hpx hxr
      by_cases hxEq : x = p
      · simpa [hxEq] using hpTwo
      · by_contra hnotTwo
        exact hBadExists ⟨x, by omega, hxr, hnotTwo⟩
    refine ⟨j, right - j, ?_, hjp, by omega⟩
    have hsum : j + (right - j) = right := by omega
    unfold IsMaximalTwoBlock
    refine ⟨hjleft, by omega, by omega, ?_, ?_, hjmax, ?_⟩
    · intro t ht
      by_cases hxp : j + t ≤ p
      · exact hjsegment (j + t) (by omega) hxp
      · exact heSegment (j + t) (by omega) (by omega)
    · refine ⟨p - j, by omega, ?_⟩
      have hindex : j + (p - j) = p := by omega
      simpa [hindex] using hpD
    · exact Or.inl hsum

/-- Every length-(L+1) subblock of a shifted two-valued parent block
attains its upper value, or its child would be an L-long zero block. -/
theorem shifted_parent_subblock_attains_upper
    (a : ℕ → ℕ) (N L i j k s r D : ℕ)
    (hi : 0 < i)
    (hzero : NoLongZeroBlock a N L)
    (hvalid : j + (i - 1) + k ≤ N)
    (hsub : s + L + 1 ≤ k)
    (hparent : ∀ t < k,
      iterAbsDiff a (i - 1) (j + t) = r ∨
      iterAbsDiff a (i - 1) (j + t) = r + D) :
    ∃ t, t < L + 1 ∧
      iterAbsDiff a (i - 1) (j + s + t) = r + D := by
  by_contra hnone
  have hconstant : ∀ t, t ≤ L →
      iterAbsDiff a (i - 1) (j + s + t) = r := by
    intro t ht
    have hindex : j + s + t = j + (s + t) := by omega
    have hv := hparent (s + t) (by omega)
    rw [← hindex] at hv
    rcases hv with hv | hv
    · exact hv
    · exfalso
      exact hnone ⟨t, by omega, hv⟩
  have heq : i - 1 + 1 = i := by omega
  have hchildZero : ∀ t < L,
      iterAbsDiff a i ((j + s) + t) = 0 := by
    intro t ht
    have hl := hconstant t (by omega)
    have hr := hconstant (t + 1) (by omega)
    have hrow :
        iterAbsDiff a i ((j + s) + t) =
          absDiff (iterAbsDiff a (i - 1)) ((j + s) + t) := by
      calc
        iterAbsDiff a i ((j + s) + t) =
            iterAbsDiff a (i - 1 + 1) ((j + s) + t) := by rw [heq]
        _ = absDiff (iterAbsDiff a (i - 1)) ((j + s) + t) := by
          rw [iterAbsDiff_succ]
    rw [hrow]
    change Int.natAbs
      ((iterAbsDiff a (i - 1) (((j + s) + t) + 1) : ℤ) -
       (iterAbsDiff a (i - 1) ((j + s) + t) : ℤ)) = 0
    have hindex : ((j + s) + t) + 1 = j + s + (t + 1) := by omega
    rw [hindex, hr, hl]
    simp
  apply hzero
  refine ⟨i, j + s, by omega, by omega, ?_⟩
  exact hchildZero

/-- Under an ambient bound below 2D, a two-valued child has either
a {0,D} parent or a positively shifted {r,r+D} parent. -/
theorem bounded_parent_two_or_shifted
    (a : ℕ → ℕ) (i j k D B : ℕ)
    (hi : 0 < i) (hD : 0 < D) (hB : B < 2 * D)
    (hparentBound : ∀ t, t ≤ k →
      iterAbsDiff a (i - 1) (j + t) ≤ B)
    (hchild : ∀ t < k,
      iterAbsDiff a i (j + t) = 0 ∨
      iterAbsDiff a i (j + t) = D)
    (hatt : ∃ t, t < k ∧ iterAbsDiff a i (j + t) = D) :
    ((∀ t, t ≤ k →
      iterAbsDiff a (i - 1) (j + t) = 0 ∨
      iterAbsDiff a (i - 1) (j + t) = D) ∧
     (∃ t, t ≤ k ∧ iterAbsDiff a (i - 1) (j + t) = D)) ∨
    (∃ r, 0 < r ∧ r < D ∧
      (∀ t, t ≤ k →
        iterAbsDiff a (i - 1) (j + t) = r ∨
        iterAbsDiff a (i - 1) (j + t) = r + D) ∧
      (∃ t, t ≤ k ∧
        iterAbsDiff a (i - 1) (j + t) = r + D) ∧
      D < r + D ∧ r + D ≤ B) := by
  have heq : i - 1 + 1 = i := by omega
  have hrow (n : ℕ) :
      iterAbsDiff a i n = absDiff (iterAbsDiff a (i - 1)) n := by
    calc
      iterAbsDiff a i n = iterAbsDiff a (i - 1 + 1) n := by rw [heq]
      _ = absDiff (iterAbsDiff a (i - 1)) n := by
        rw [iterAbsDiff_succ]
  have hchild' : ∀ t < k,
      absDiff (iterAbsDiff a (i - 1)) (j + t) = 0 ∨
      absDiff (iterAbsDiff a (i - 1)) (j + t) = D := by
    intro t ht
    simpa only [hrow] using hchild t ht
  have hatt' : ∃ t, t < k ∧
      absDiff (iterAbsDiff a (i - 1)) (j + t) = D := by
    obtain ⟨t, ht, hv⟩ := hatt
    exact ⟨t, ht, by simpa only [hrow] using hv⟩
  rcases parent_block_trichotomy
      (iterAbsDiff a (i - 1)) j k D hD hchild' hatt' with
    hbig | htwo | hshift
  · obtain ⟨t, ht, hv⟩ := hbig
    have hb := hparentBound t ht
    omega
  · exact Or.inl ⟨htwo.1, htwo.2.2⟩
  · right
    obtain ⟨r, hr, hrD, hvals, _, ⟨t, ht, hv⟩⟩ := hshift
    have hb := hparentBound t ht
    exact ⟨r, hr, hrD, hvals, ⟨t, ht, hv⟩,
      by omega, by omega⟩

/-- A difference of two entries in {0,D} is again in {0,D}. -/
private theorem absDiff_two_values
    (f : ℕ → ℕ) (D n : ℕ)
    (hl : f n = 0 ∨ f n = D)
    (hr : f (n + 1) = 0 ∨ f (n + 1) = D) :
    absDiff f n = 0 ∨ absDiff f n = D := by
  rcases hl with hl | hl <;> rcases hr with hr | hr <;>
    simp [absDiff, hl, hr]

/-- A two-valued parent of a maximal child block is itself maximal
in the one-entry-wider parent row. -/
theorem parent_maximal_of_child_maximal
    (a : ℕ → ℕ) (i left right j k D : ℕ)
    (hi : 0 < i)
    (hchildGood : IsMaximalTwoBlock a i left right j k D)
    (hparentTwo : ∀ t, t ≤ k →
      iterAbsDiff a (i - 1) (j + t) = 0 ∨
      iterAbsDiff a (i - 1) (j + t) = D)
    (hparentAtt : ∃ t, t ≤ k ∧
      iterAbsDiff a (i - 1) (j + t) = D) :
    IsMaximalTwoBlock a (i - 1) left (right + 1)
      j (k + 1) D := by
  rcases hchildGood with
    ⟨hlo, hhi, hk, _, _, hmaxLeft, hmaxRight⟩
  have heq : i - 1 + 1 = i := by omega
  have hrow (n : ℕ) :
      iterAbsDiff a i n = absDiff (iterAbsDiff a (i - 1)) n := by
    calc
      iterAbsDiff a i n = iterAbsDiff a (i - 1 + 1) n := by rw [heq]
      _ = absDiff (iterAbsDiff a (i - 1)) n := by
        rw [iterAbsDiff_succ]
  unfold IsMaximalTwoBlock
  refine ⟨hlo, by omega, by omega, ?_, ?_, ?_, ?_⟩
  · intro t ht
    exact hparentTwo t (by omega)
  · obtain ⟨t, ht, hv⟩ := hparentAtt
    exact ⟨t, by omega, hv⟩
  · by_cases hborder : j = left
    · exact Or.inl hborder
    · have hstop :
          ¬ (iterAbsDiff a i (j - 1) = 0 ∨
             iterAbsDiff a i (j - 1) = D) := by
        rcases hmaxLeft with hborder' | hstop
        · contradiction
        · exact hstop
      right
      intro hprev
      have hindex : (j - 1) + 1 = j := by omega
      have hcurrent :
          iterAbsDiff a (i - 1) ((j - 1) + 1) = 0 ∨
          iterAbsDiff a (i - 1) ((j - 1) + 1) = D := by
        simpa [hindex] using hparentTwo 0 (by omega)
      have hchildExtend :
          iterAbsDiff a i (j - 1) = 0 ∨
          iterAbsDiff a i (j - 1) = D := by
        simpa only [hrow] using
          absDiff_two_values
            (iterAbsDiff a (i - 1)) D (j - 1) hprev hcurrent
      exact hstop hchildExtend
  · rcases hmaxRight with hborder | hstop
    · exact Or.inl (by omega)
    · right
      intro hnext
      have hindex : j + (k + 1) = (j + k) + 1 := by omega
      have hnext' :
          iterAbsDiff a (i - 1) ((j + k) + 1) = 0 ∨
          iterAbsDiff a (i - 1) ((j + k) + 1) = D := by
        simpa [hindex] using hnext
      have hchildExtend :
          iterAbsDiff a i (j + k) = 0 ∨
          iterAbsDiff a i (j + k) = D := by
        simpa only [hrow] using
          absDiff_two_values
            (iterAbsDiff a (i - 1)) D (j + k)
            (hparentTwo k (by omega)) hnext'
      exact hstop hchildExtend

/-- CHT Lemma 5.5(ii), for a good child whose parent lies in the
ambient triangle but is not itself a good block of the same value. -/
theorem good_block_non_good_parent_has_larger_value
    (a : ℕ → ℕ) (N L i left right j k D B : ℕ)
    (hi : 0 < i) (hD : 0 < D) (hB : B < 2 * D)
    (hzero : NoLongZeroBlock a N L)
    (hvalid : j + (i - 1) + (k + 1) ≤ N)
    (hchildGood : IsMaximalTwoBlock a i left right j k D)
    (hparentBound : ∀ t, t ≤ k →
      iterAbsDiff a (i - 1) (j + t) ≤ B)
    (hparentNotGood :
      ¬ IsMaximalTwoBlock a (i - 1) left (right + 1)
        j (k + 1) D) :
    ∃ D', D < D' ∧ D' ≤ B ∧
      (∃ t, t < k + 1 ∧
        iterAbsDiff a (i - 1) (j + t) = D') ∧
      ∀ s, s + L + 1 ≤ k + 1 →
        ∃ t, t < L + 1 ∧
          iterAbsDiff a (i - 1) (j + s + t) = D' := by
  have hchild : ∀ t < k,
      iterAbsDiff a i (j + t) = 0 ∨
      iterAbsDiff a i (j + t) = D :=
    hchildGood.2.2.2.1
  have hatt : ∃ t, t < k ∧ iterAbsDiff a i (j + t) = D :=
    hchildGood.2.2.2.2.1
  rcases bounded_parent_two_or_shifted a i j k D B
      hi hD hB hparentBound hchild hatt with
    htwo | hshift
  · exact False.elim
      (hparentNotGood
        (parent_maximal_of_child_maximal
          a i left right j k D hi hchildGood htwo.1 htwo.2))
  · obtain ⟨r, hr, hrD, hparent, ⟨t, ht, hv⟩,
        hlarge, hupper⟩ := hshift
    refine ⟨r + D, hlarge, hupper, ⟨t, by omega, hv⟩, ?_⟩
    intro s hs
    exact shifted_parent_subblock_attains_upper
      a N L i j (k + 1) s r D
      hi hzero hvalid hs
      (by
        intro t ht
        exact hparent t (by omega))

/-- A two-valued child extension whose parent contains D cannot have
the positively shifted parentage pattern. -/
private theorem extended_child_forces_two_valued_parent
    (a : ℕ → ℕ) (i j k D B : ℕ)
    (hi : 0 < i) (hD : 0 < D) (hB : B < 2 * D)
    (hparentBound : ∀ t, t ≤ k →
      iterAbsDiff a (i - 1) (j + t) ≤ B)
    (hchild : ∀ t < k,
      iterAbsDiff a i (j + t) = 0 ∨
      iterAbsDiff a i (j + t) = D)
    (hattChild : ∃ t, t < k ∧
      iterAbsDiff a i (j + t) = D)
    (hattParent : ∃ t, t ≤ k ∧
      iterAbsDiff a (i - 1) (j + t) = D) :
    ∀ t, t ≤ k →
      iterAbsDiff a (i - 1) (j + t) = 0 ∨
      iterAbsDiff a (i - 1) (j + t) = D := by
  rcases bounded_parent_two_or_shifted a i j k D B
      hi hD hB hparentBound hchild hattChild with
    htwo | hshift
  · exact htwo.1
  · obtain ⟨r, hr, hrD, hvals, _, _, _⟩ := hshift
    obtain ⟨t, ht, hv⟩ := hattParent
    rcases hvals t ht with hlow | hhigh
    · omega
    · omega

/-- The immediate-descendant case of CHT Lemma 5.5(iii): a descendant
long enough to avoid being all zero remains a good block. -/
theorem maximal_two_block_immediate_descendant
    (a : ℕ → ℕ) (N L i left right j k D B : ℕ)
    (hzero : NoLongZeroBlock a N L)
    (hvalid : i + j + k ≤ N)
    (hk : 2 ≤ k) (hL : L ≤ k - 1)
    (hD : 0 < D) (hB : B < 2 * D)
    (hgood : IsMaximalTwoBlock a i left right j k D)
    (hambient : ∀ x, left ≤ x → x < right →
      iterAbsDiff a i x ≤ B) :
    IsMaximalTwoBlock a (i + 1) left (right - 1)
      j (k - 1) D := by
  rcases hgood with
    ⟨hlo, hhi, _, hparentTwo, hparentAtt, hmaxLeft, hmaxRight⟩
  have hchildTwo : ∀ t < k - 1,
      iterAbsDiff a (i + 1) (j + t) = 0 ∨
      iterAbsDiff a (i + 1) (j + t) = D := by
    intro t ht
    exact finite_two_block_inherits a i j k D hparentTwo
      1 t (by omega) (by omega)
  have hchildAtt : ∃ t, t < k - 1 ∧
      iterAbsDiff a (i + 1) (j + t) = D := by
    obtain ⟨t, ht, hv⟩ :=
      long_two_block_attains a N L (i + 1) j (k - 1) D
        hzero (by omega) hL hchildTwo
    exact ⟨t, by omega, hv⟩
  unfold IsMaximalTwoBlock
  refine ⟨hlo, by omega, by omega, hchildTwo, hchildAtt, ?_, ?_⟩
  · by_cases hborder : j = left
    · exact Or.inl hborder
    · right
      intro hnext
      have hjpos : 0 < j := by omega
      have hchildExtended : ∀ t < k,
          iterAbsDiff a (i + 1) ((j - 1) + t) = 0 ∨
          iterAbsDiff a (i + 1) ((j - 1) + t) = D := by
        intro t ht
        by_cases ht0 : t = 0
        · simpa [ht0] using hnext
        · have hindex : (j - 1) + t = j + (t - 1) := by omega
          rw [hindex]
          exact hchildTwo (t - 1) (by omega)
      have hchildExtendedAtt : ∃ t, t < k ∧
          iterAbsDiff a (i + 1) ((j - 1) + t) = D := by
        obtain ⟨t, ht, hv⟩ := hchildAtt
        refine ⟨t + 1, by omega, ?_⟩
        have hindex : (j - 1) + (t + 1) = j + t := by omega
        simpa [hindex] using hv
      have hparentExtendedBound : ∀ t, t ≤ k →
          iterAbsDiff a i ((j - 1) + t) ≤ B := by
        intro t ht
        apply hambient ((j - 1) + t)
        · omega
        · omega
      have hparentExtendedAtt : ∃ t, t ≤ k ∧
          iterAbsDiff a i ((j - 1) + t) = D := by
        obtain ⟨t, ht, hv⟩ := hparentAtt
        refine ⟨t + 1, by omega, ?_⟩
        have hindex : (j - 1) + (t + 1) = j + t := by omega
        simpa [hindex] using hv
      have hparentExtended :=
        extended_child_forces_two_valued_parent
          a (i + 1) (j - 1) k D B
          (by omega) hD hB
          (by simpa using hparentExtendedBound)
          (by simpa using hchildExtended)
          (by simpa using hchildExtendedAtt)
          (by simpa using hparentExtendedAtt)
      have hparentNext :=
        hparentExtended 0 (by omega)
      have hparentLeft :
          iterAbsDiff a i (j - 1) = 0 ∨
          iterAbsDiff a i (j - 1) = D := by
        simpa using hparentNext
      rcases hmaxLeft with hborder' | hstop
      · contradiction
      · exact hstop hparentLeft
  · by_cases hborder : j + k = right
    · exact Or.inl (by omega)
    · right
      intro hnext
      have hchildExtended : ∀ t < k,
          iterAbsDiff a (i + 1) (j + t) = 0 ∨
          iterAbsDiff a (i + 1) (j + t) = D := by
        intro t ht
        by_cases hsmall : t < k - 1
        · exact hchildTwo t hsmall
        · have htlast : t = k - 1 := by omega
          simpa [htlast] using hnext
      have hparentExtendedBound : ∀ t, t ≤ k →
          iterAbsDiff a i (j + t) ≤ B := by
        intro t ht
        apply hambient (j + t)
        · omega
        · omega
      have hparentExtendedAtt : ∃ t, t ≤ k ∧
          iterAbsDiff a i (j + t) = D := by
        obtain ⟨t, ht, hv⟩ := hparentAtt
        exact ⟨t, by omega, hv⟩
      have hparentExtended :=
        extended_child_forces_two_valued_parent
          a (i + 1) j k D B
          (by omega) hD hB
          (by simpa using hparentExtendedBound)
          (by simpa using hchildExtended)
          (by
            obtain ⟨t, ht, hv⟩ := hchildAtt
            exact ⟨t, by omega, hv⟩)
          (by simpa using hparentExtendedAtt)
      have hparentRight :
          iterAbsDiff a i (j + k) = 0 ∨
          iterAbsDiff a i (j + k) = D :=
        hparentExtended k (by omega)
      rcases hmaxRight with hborder' | hstop
      · contradiction
      · exact hstop hparentRight

/-- CHT Lemma 5.5(iii): every descendant that still has length at
least L is a good block of the same nonzero value. -/
theorem maximal_two_block_descendant
    (a : ℕ → ℕ) (N L i left right j k D B : ℕ)
    (hzero : NoLongZeroBlock a N L)
    (hvalid : i + j + k ≤ N)
    (hLpos : 1 ≤ L) (hD : 0 < D) (hB : B < 2 * D)
    (hgood : IsMaximalTwoBlock a i left right j k D) :
    ∀ depth, depth < k → L ≤ k - depth →
      (∀ d, d ≤ depth → ∀ x, left ≤ x → x < right - d →
        iterAbsDiff a (i + d) x ≤ B) →
      IsMaximalTwoBlock a (i + depth) left (right - depth)
        j (k - depth) D := by
  intro depth
  induction depth with
  | zero =>
      intro _ _ _
      simpa using hgood
  | succ depth ih =>
      intro hdepth hlength hambient
      have hparent :
          IsMaximalTwoBlock a (i + depth) left (right - depth)
            j (k - depth) D := by
        apply ih
        · omega
        · omega
        · intro d hd x hxleft hxright
          exact hambient d (by omega) x hxleft hxright
      have hstep :=
        maximal_two_block_immediate_descendant
          a N L (i + depth) left (right - depth)
          j (k - depth) D B
          hzero (by omega) (by omega) (by omega)
          hD hB hparent
          (by
            intro x hxleft hxright
            exact hambient depth (by omega) x hxleft hxright)
      simpa [Nat.add_assoc, Nat.sub_sub] using hstep

/-- CHT Lemma 5.5(iv): every point of a bounded triangle lies near a
maximal block whose nonzero value is at least the bottom value. -/
theorem bounded_triangle_good_block_covering
    (a : ℕ → ℕ) (N B L top T j Dmin U d q : ℕ)
    (hinput : ∀ u < N, a u ≤ B)
    (hzero : NoLongZeroBlock a N L)
    (hL : 1 ≤ L)
    (hvalid : top + T + j < N)
    (hDmin : 1 ≤ Dmin)
    (hbottom : iterAbsDiff a (top + T) j = Dmin)
    (htriangle : ∀ depth, depth ≤ T →
      ∀ offset, offset ≤ T - depth →
        iterAbsDiff a (top + depth) (j + offset) ≤ U)
    (hd : d ≤ T) (hqleft : j ≤ q)
    (hqright : q ≤ j + (T - d)) :
    ∃ p blockStart blockLen D,
      IsMaximalTwoBlock a (top + d)
        j (j + (T - d) + 1) blockStart blockLen D ∧
      blockStart ≤ p ∧ p < blockStart + blockLen ∧
      Dmin ≤ iterAbsDiff a (top + d) p ∧
      Dmin ≤ D ∧ D ≤ U ∧
      2 * Nat.dist p q ≤ B * (2 * L + 1) := by
  have hDB : Dmin ≤ B := by
    rw [← hbottom]
    exact finite_triangle_bounded a N B (top + T) j
      hinput (by omega)
  obtain ⟨p, _, hpleft, hpright, hpvalue, hpnear⟩ :=
    coarse_monotonicity a N B L (top + T) j Dmin
      (top + d) q hinput hzero hL hvalid hDmin
      hDB hbottom (by omega) hqleft (by omega)
  let D := iterAbsDiff a (top + d) p
  have hpupper : D ≤ U := by
    have hindex : j + (p - j) = p := by omega
    simpa [D, hindex] using htriangle d hd (p - j) (by omega)
  obtain ⟨blockStart, blockLen, hgood, hstart, hend⟩ :=
    maximal_two_block_exists_through_point
      a (top + d) j (j + (T - d) + 1) p D
      hpleft (by omega) rfl
  exact ⟨p, blockStart, blockLen, D,
    hgood, hstart, hend, hpvalue, hpvalue, hpupper, hpnear⟩

end Gilbreath

-- END GilbreathGoodBlocks_20260925.lean


-- BEGIN GilbreathStrictMonotonicity_20260925.lean

namespace Gilbreath

private theorem good_to_bad_transition
    (P : ℕ → Prop) (H : ℕ) (hzero : P 0) (hlast : ¬ P H) :
    ∃ h, h < H ∧ P h ∧ ¬ P (h + 1) := by
  induction H with
  | zero => exact False.elim (hlast hzero)
  | succ H ih =>
      by_cases hprev : P H
      · exact ⟨H, by omega, hprev, hlast⟩
      · obtain ⟨h, hh, hgood, hbad⟩ := ih hprev
        exact ⟨h, by omega, hgood, hbad⟩

/-- If a value occurs in every long subblock, an occurrence can be found
within L positions of any specified point of the block. -/
private theorem value_near_point_of_long_subblocks
    (f : ℕ → ℕ) (j len p L D : ℕ)
    (hpoint : j ≤ p ∧ p < j + len)
    (hatt : ∃ t, t < len ∧ f (j + t) = D)
    (hsub : ∀ s, s + L + 1 ≤ len →
      ∃ t, t < L + 1 ∧ f (j + s + t) = D) :
    ∃ q, j ≤ q ∧ q < j + len ∧
      q ≤ p + L ∧ p ≤ q + L ∧ f q = D := by
  by_cases hshort : len ≤ L + 1
  · obtain ⟨t, ht, hv⟩ := hatt
    exact ⟨j + t, by omega, by omega, by omega, by omega, hv⟩
  · let start := min (p - j) (len - (L + 1))
    have hs : start + L + 1 ≤ len := by
      dsimp [start]
      omega
    have hstart : j + start ≤ p := by
      dsimp [start]
      omega
    have hend : p ≤ j + start + L := by
      dsimp [start]
      omega
    obtain ⟨t, ht, hv⟩ := hsub start hs
    exact ⟨j + start + t, by omega, by omega,
      by omega, by omega, hv⟩

/-- Along a good block's ancestor chain, the first parent that stops
being good produces a larger value in every long subblock. This is
the local transition engine in CHT Lemma 5.7. -/
theorem good_ancestor_chain_increases
    (a : ℕ → ℕ) (N L B i left right j k D H : ℕ)
    (hzero : NoLongZeroBlock a N L)
    (hD : 0 < D) (hB : B < 2 * D)
    (hvalid : i + j + k ≤ N) (hH : H ≤ i)
    (hgood : IsMaximalTwoBlock a i left right j k D)
    (hbad : ¬ IsMaximalTwoBlock a (i - H) left (right + H)
      j (k + H) D)
    (hbound : ∀ h, h ≤ H → ∀ t, t < k + h →
      iterAbsDiff a (i - h) (j + t) ≤ B) :
    ∃ h D', h < H ∧ D < D' ∧ D' ≤ B ∧
      (∃ t, t < k + h + 1 ∧
        iterAbsDiff a (i - (h + 1)) (j + t) = D') ∧
      (∃ t, t ≤ L ∧
        iterAbsDiff a (i - (h + 1)) (j + t) = D') ∧
      ∀ s, s + L + 1 ≤ k + h + 1 →
        ∃ t, t < L + 1 ∧
          iterAbsDiff a (i - (h + 1)) (j + s + t) = D' := by
  let Good (h : ℕ) : Prop :=
    IsMaximalTwoBlock a (i - h) left (right + h)
      j (k + h) D
  have hGoodZero : Good 0 := by simpa [Good] using hgood
  have hBadLast : ¬ Good H := by simpa [Good] using hbad
  obtain ⟨h, hh, hgoodh, hbadh⟩ :=
    good_to_bad_transition Good H hGoodZero hBadLast
  have hdepth : 0 < i - h := by omega
  have hparentBound : ∀ t, t ≤ k + h →
      iterAbsDiff a ((i - h) - 1) (j + t) ≤ B := by
    intro t ht
    have hs := hbound (h + 1) (by omega) t (by omega)
    simpa [Nat.sub_sub, Nat.add_assoc] using hs
  have hparentNotGood :
      ¬ IsMaximalTwoBlock a ((i - h) - 1)
        left ((right + h) + 1) j ((k + h) + 1) D := by
    simpa [Good, Nat.sub_sub, Nat.add_assoc] using hbadh
  obtain ⟨D', hlarge, hupper, hatt, hsub⟩ :=
    good_block_non_good_parent_has_larger_value
      a N L (i - h) left (right + h) j (k + h) D B
      hdepth hD hB hzero (by omega)
      hgoodh hparentBound hparentNotGood
  have hnear : ∃ t, t ≤ L ∧
      iterAbsDiff a ((i - h) - 1) (j + t) = D' := by
    by_cases hlong : L + 1 ≤ (k + h) + 1
    · obtain ⟨t, ht, hv⟩ := hsub 0 (by omega)
      exact ⟨t, by omega, by simpa using hv⟩
    · obtain ⟨t, ht, hv⟩ := hatt
      exact ⟨t, by omega, hv⟩
  refine ⟨h, D', hh, hlarge, hupper, ?_, ?_, ?_⟩
  · simpa [Nat.sub_sub] using hatt
  · simpa [Nat.sub_sub] using hnear
  · intro s hs
    have hss : s + L + 1 ≤ (k + h) + 1 := by omega
    have hout := hsub s hss
    simpa [Nat.sub_sub, Nat.add_assoc] using hout

/-- A long overlap with a different good block forces the top
ancestor in a chain to stop being good, and hence forces a rise in
the nonzero value lower in that chain. -/
theorem crossing_good_blocks_force_increase
    (a : ℕ → ℕ)
    (N L B i left right j k D H
      otherStart otherLen E overlapStart : ℕ)
    (hzero : NoLongZeroBlock a N L)
    (hL : 1 ≤ L) (hD : 0 < D)
    (hB : B < 2 * D)
    (hvalid : i + j + k ≤ N) (hH : H ≤ i)
    (hgood : IsMaximalTwoBlock a i left right j k D)
    (hother : IsMaximalTwoBlock a (i - H)
      left (right + H) otherStart otherLen E)
    (hdifferent : j ≠ otherStart ∨ k + H ≠ otherLen)
    (hoverlapValid : (i - H) + overlapStart + L ≤ N)
    (hleft : j ≤ overlapStart)
    (hleftEnd : overlapStart + L ≤ j + (k + H))
    (hright : otherStart ≤ overlapStart)
    (hrightEnd : overlapStart + L ≤ otherStart + otherLen)
    (hbound : ∀ h, h ≤ H → ∀ t, t < k + h →
      iterAbsDiff a (i - h) (j + t) ≤ B) :
    ∃ h D', h < H ∧ D < D' ∧ D' ≤ B ∧
      (∃ t, t < k + h + 1 ∧
        iterAbsDiff a (i - (h + 1)) (j + t) = D') ∧
      (∃ t, t ≤ L ∧
        iterAbsDiff a (i - (h + 1)) (j + t) = D') ∧
      ∀ s, s + L + 1 ≤ k + h + 1 →
        ∃ t, t < L + 1 ∧
          iterAbsDiff a (i - (h + 1)) (j + s + t) = D' := by
  have hbad :
      ¬ IsMaximalTwoBlock a (i - H) left (right + H)
        j (k + H) D := by
    intro hancestor
    obtain ⟨hj, hk, _⟩ :=
      maximal_two_blocks_equal_of_long_overlap
        a N L (i - H) left (right + H)
        j (k + H) otherStart otherLen overlapStart D E
        hzero hL hD hancestor hother
        hoverlapValid hleft hleftEnd hright hrightEnd
    rcases hdifferent with hd | hd
    · exact hd hj
    · exact hd hk
  exact good_ancestor_chain_increases
    a N L B i left right j k D H
    hzero hD hB hvalid hH hgood hbad hbound

/-- The left-gap geometry in CHT Lemma 5.7: after g+L ancestor
steps, the point's block overlaps the other block's triangle in
at least L positions. -/
theorem left_gap_ancestor_overlap_geometry
    (iI ip jI jp jJ kJ kI L : ℕ)
    (hL : 1 ≤ L)
    (hgap : jp < jI)
    (hJleft : jJ ≤ jp) (hJright : jp < jJ + kJ)
    (hlower : iI + (jI - jp) + L ≤ ip)
    (hupper : ip ≤ iI + kI - L) :
    let H := (jI - jp) + L
    let depth := ip - H - iI
    H ≤ ip ∧ depth < kI ∧ L ≤ kI - depth ∧
      jJ < jI ∧ jI + L ≤ jJ + kJ + H := by
  dsimp
  omega

/-- The left-gap strict increase mechanism of CHT Lemma 5.7,
located relative to the good block containing the outer point. -/
theorem strict_coarse_upward_left_from_good_blocks
    (a : ℕ → ℕ)
    (N L B iI ip left rightP
      jI kI E jJ kJ D jp : ℕ)
    (hzero : NoLongZeroBlock a N L)
    (hL : 1 ≤ L)
    (hE : 0 < E) (hBE : B < 2 * E)
    (hD : 0 < D) (hBD : B < 2 * D)
    (hiOrder : iI ≤ ip)
    (hIvalid : iI + jI + kI ≤ N)
    (hJvalid : ip + jJ + kJ ≤ N)
    (hIgood : IsMaximalTwoBlock a iI left
      (rightP + (ip - iI)) jI kI E)
    (hJgood : IsMaximalTwoBlock a ip left rightP jJ kJ D)
    (hJcontainsLeft : jJ ≤ jp)
    (hJcontainsRight : jp < jJ + kJ)
    (hgap : jp < jI)
    (hlower : iI + (jI - jp) + L ≤ ip)
    (hupper : ip ≤ iI + kI - L)
    (hambientI :
      ∀ d, d ≤ ip - ((jI - jp) + L) - iI →
        ∀ x, left ≤ x →
          x < rightP + (ip - iI) - d →
            iterAbsDiff a (iI + d) x ≤ B)
    (hboundJ :
      ∀ h, h ≤ (jI - jp) + L →
        ∀ t, t < kJ + h →
          iterAbsDiff a (ip - h) (jJ + t) ≤ B) :
    ∃ h q D', h < (jI - jp) + L ∧
      q ≤ jp + L ∧ jp ≤ q + L ∧
      D < D' ∧ D' ≤ B ∧
      iterAbsDiff a (ip - (h + 1)) q = D' := by
  let H := (jI - jp) + L
  let delta := ip - H - iI
  have hgeom :
      H ≤ ip ∧ delta < kI ∧ L ≤ kI - delta ∧
        jJ < jI ∧ jI + L ≤ jJ + kJ + H := by
    simpa [H, delta] using
      left_gap_ancestor_overlap_geometry
        iI ip jI jp jJ kJ kI L
        hL hgap hJcontainsLeft hJcontainsRight hlower hupper
  obtain ⟨hHip, hdeltaK, hLdelta, hjJlt, hcover⟩ := hgeom
  have hdeltaDepth : iI + delta = ip - H := by
    dsimp [delta]
    omega
  have hdeltaRight :
      rightP + (ip - iI) - delta = rightP + H := by
    dsimp [delta]
    omega
  have hotherBase :=
    maximal_two_block_descendant
      a N L iI left (rightP + (ip - iI)) jI kI E B
      hzero hIvalid hL hE hBE hIgood
      delta hdeltaK hLdelta
      (by
        intro d hd x hxleft hxright
        exact hambientI d hd x hxleft hxright)
  have hother :
      IsMaximalTwoBlock a (ip - H) left (rightP + H)
        jI (kI - delta) E := by
    simpa [hdeltaDepth, hdeltaRight] using hotherBase
  have hoverlapValid : (ip - H) + jI + L ≤ N := by
    omega
  obtain ⟨h, D', hh, hlarge, hupperD, hatt, _, hsub⟩ :=
    crossing_good_blocks_force_increase
      a N L B ip left rightP jJ kJ D H
      jI (kI - delta) E jI
      hzero hL hD hBD hJvalid hHip
      hJgood hother (Or.inl (by omega))
      hoverlapValid
      (by omega) (by omega) (by omega) (by omega)
      (by
        intro h hh t ht
        exact hboundJ h (by simpa [H] using hh) t ht)
  have hpoint : jJ ≤ jp ∧ jp < jJ + (kJ + h + 1) := by
    omega
  obtain ⟨q, _, _, hrightNear, hleftNear, hv⟩ :=
    value_near_point_of_long_subblocks
      (iterAbsDiff a (ip - (h + 1)))
      jJ (kJ + h + 1) jp L D'
      hpoint hatt hsub
  exact ⟨h, q, D', by simpa [H] using hh,
    hrightNear, hleftNear, hlarge, hupperD, hv⟩

/-- The right-gap geometry is measured in the right coordinate j+i.
At the chosen ancestor depth, the rightmost L entries of the
descendant of I overlap the ancestor of J. -/
theorem right_gap_ancestor_overlap_geometry
    (iI ip jI kI jJ kJ L jp : ℕ)
    (hL : 1 ≤ L)
    (horder : iI ≤ ip)
    (hJleft : jJ ≤ jp) (hJright : jp < jJ + kJ)
    (hgap : jI + kI ≤ jp + (ip - iI))
    (hlower : iI +
      (jp + (ip - iI) + 1 - (jI + kI)) + L ≤ ip)
    (hupper : ip ≤ iI + kI - L) :
    let H := (jp + (ip - iI) + 1 - (jI + kI)) + L
    let delta := ip - H - iI
    H ≤ ip ∧ delta < kI ∧ L ≤ kI - delta ∧
      jI + kI - delta = jp + 1 + L ∧
      jI ≤ jp + 1 ∧ jJ ≤ jp + 1 ∧
      jp + 1 + L ≤ jJ + kJ + H ∧
      jI + kI - delta < jJ + kJ + H := by
  dsimp
  omega

/-- Right-gap strict increase, with a new point within L positions
of the specified point. -/
theorem strict_coarse_upward_right_from_good_blocks
    (a : ℕ → ℕ)
    (N L B iI ip left rightP
      jI kI E jJ kJ D jp : ℕ)
    (hzero : NoLongZeroBlock a N L)
    (hL : 1 ≤ L)
    (hE : 0 < E) (hBE : B < 2 * E)
    (hD : 0 < D) (hBD : B < 2 * D)
    (hiOrder : iI ≤ ip)
    (hIvalid : iI + jI + kI ≤ N)
    (hJvalid : ip + jJ + kJ ≤ N)
    (hIgood : IsMaximalTwoBlock a iI left
      (rightP + (ip - iI)) jI kI E)
    (hJgood : IsMaximalTwoBlock a ip left rightP jJ kJ D)
    (hJcontainsLeft : jJ ≤ jp)
    (hJcontainsRight : jp < jJ + kJ)
    (hgap : jI + kI ≤ jp + (ip - iI))
    (hlower : iI +
      (jp + (ip - iI) + 1 - (jI + kI)) + L ≤ ip)
    (hupper : ip ≤ iI + kI - L)
    (hambientI :
      ∀ d, d ≤ ip -
          ((jp + (ip - iI) + 1 - (jI + kI)) + L) - iI →
        ∀ x, left ≤ x →
          x < rightP + (ip - iI) - d →
            iterAbsDiff a (iI + d) x ≤ B)
    (hboundJ :
      ∀ h, h ≤
        (jp + (ip - iI) + 1 - (jI + kI)) + L →
        ∀ t, t < kJ + h →
          iterAbsDiff a (ip - h) (jJ + t) ≤ B) :
    ∃ h q D',
      h < (jp + (ip - iI) + 1 - (jI + kI)) + L ∧
      q ≤ jp + (h + 1) + L ∧
      jp + (h + 1) ≤ q + L ∧
      D < D' ∧ D' ≤ B ∧
      iterAbsDiff a (ip - (h + 1)) q = D' := by
  let H := (jp + (ip - iI) + 1 - (jI + kI)) + L
  let delta := ip - H - iI
  have hgeom :
      H ≤ ip ∧ delta < kI ∧ L ≤ kI - delta ∧
        jI + kI - delta = jp + 1 + L ∧
        jI ≤ jp + 1 ∧ jJ ≤ jp + 1 ∧
        jp + 1 + L ≤ jJ + kJ + H ∧
        jI + kI - delta < jJ + kJ + H := by
    simpa [H, delta] using
      right_gap_ancestor_overlap_geometry
        iI ip jI kI jJ kJ L jp
        hL hiOrder hJcontainsLeft hJcontainsRight
        hgap hlower hupper
  obtain ⟨hHip, hdeltaK, hLdelta, hIend,
    hIleft, hJleft, hJend, hstrictEnd⟩ := hgeom
  have hdeltaDepth : iI + delta = ip - H := by
    dsimp [delta]
    omega
  have hdeltaRight :
      rightP + (ip - iI) - delta = rightP + H := by
    dsimp [delta]
    omega
  have hotherBase :=
    maximal_two_block_descendant
      a N L iI left (rightP + (ip - iI)) jI kI E B
      hzero hIvalid hL hE hBE hIgood
      delta hdeltaK hLdelta
      (by
        intro d hd x hxleft hxright
        exact hambientI d hd x hxleft hxright)
  have hother :
      IsMaximalTwoBlock a (ip - H) left (rightP + H)
        jI (kI - delta) E := by
    simpa [hdeltaDepth, hdeltaRight] using hotherBase
  have hoverlapValid : (ip - H) + (jp + 1) + L ≤ N := by
    omega
  have hdifferent : jJ ≠ jI ∨ kJ + H ≠ kI - delta := by
    by_cases hj : jJ = jI
    · right
      omega
    · exact Or.inl hj
  obtain ⟨h, D', hh, hlarge, hupperD, hatt, _, hsub⟩ :=
    crossing_good_blocks_force_increase
      a N L B ip left rightP jJ kJ D H
      jI (kI - delta) E (jp + 1)
      hzero hL hD hBD hJvalid hHip
      hJgood hother hdifferent
      hoverlapValid
      (by omega) (by omega) (by omega) (by omega)
      (by
        intro h hh t ht
        exact hboundJ h (by simpa [H] using hh) t ht)
  have hpoint :
      jJ ≤ jp + (h + 1) ∧
        jp + (h + 1) < jJ + (kJ + h + 1) := by
    omega
  obtain ⟨q, _, _, hrightNear, hleftNear, hv⟩ :=
    value_near_point_of_long_subblocks
      (iterAbsDiff a (ip - (h + 1)))
      jJ (kJ + h + 1) (jp + (h + 1)) L D'
      hpoint hatt hsub
  exact ⟨h, q, D', by simpa [H] using hh,
    hrightNear, hleftNear, hlarge, hupperD, hv⟩

end Gilbreath

-- END GilbreathStrictMonotonicity_20260925.lean


-- BEGIN GilbreathAscentBudget_20260925.lean

namespace Gilbreath

/-- A numerical budget for the strict-increase iteration used in the
"small or huge" block argument. The step relation may come from
either side of a good block. -/
theorem bounded_strict_ascent_impossible
    (F : ℕ → ℕ → ℕ) (B L G Dmin base lo hi i₀ q₀ : ℕ)
    (hstartDepth : base + (B + 1) * G ≤ i₀)
    (hstartLeft : lo + (B + 1) * L ≤ q₀)
    (hstartRight : q₀ + (B + 1) * L ≤ hi)
    (hstartValue : Dmin ≤ F i₀ q₀)
    (hbounded : ∀ i q, base ≤ i → i ≤ i₀ →
      lo ≤ q → q ≤ hi → F i q ≤ B)
    (hstep : ∀ i q,
      base + G ≤ i → i ≤ i₀ →
      lo + L ≤ q → q + L ≤ hi →
      Dmin ≤ F i q →
      ∃ i' q',
        i' < i ∧ i ≤ i' + G ∧
        q' ≤ q + L ∧ q ≤ q' + L ∧
        F i q < F i' q') :
    False := by
  have iterate :
      ∀ r i q,
        base + r * G ≤ i →
        i ≤ i₀ →
        lo + r * L ≤ q →
        q + r * L ≤ hi →
        Dmin ≤ F i q →
        ∃ i' q',
          base ≤ i' ∧ i' ≤ i₀ ∧
          lo ≤ q' ∧ q' ≤ hi ∧
          F i q + r ≤ F i' q' := by
    intro r
    induction r with
    | zero =>
        intro i q hdepth htop hleft hright _
        exact ⟨i, q, by simpa using hdepth, htop,
          by simpa using hleft,
          by simpa using hright, by simp⟩
    | succ r ih =>
        intro i q hdepth htop hleft hright hlarge
        have hrG : (r + 1) * G = r * G + G := by
          simp [Nat.add_mul]
        have hrL : (r + 1) * L = r * L + L := by
          simp [Nat.add_mul]
        rw [hrG] at hdepth
        rw [hrL] at hleft hright
        clear hrG hrL
        have hdepthStep : base + G ≤ i := by omega
        have hleftStep : lo + L ≤ q := by omega
        have hrightStep : q + L ≤ hi := by omega
        obtain ⟨i', q', hsmaller, hdepthLoss,
          hmoveRight, hmoveLeft, hrise⟩ :=
          hstep i q hdepthStep htop
            hleftStep hrightStep hlarge
        have hnextDepth : base + r * G ≤ i' := by omega
        have hnextLeft : lo + r * L ≤ q' := by omega
        have hnextRight : q' + r * L ≤ hi := by omega
        obtain ⟨i'', q'', hdepthLower, hdepthUpper,
          hqLeft, hqRight, hgain⟩ :=
          ih i' q' hnextDepth (by omega)
            hnextLeft hnextRight (by omega)
        exact ⟨i'', q'', hdepthLower, hdepthUpper,
          hqLeft, hqRight, by omega⟩
  obtain ⟨i', q', hdepthLower, hdepthUpper,
    hqLeft, hqRight, hgain⟩ :=
    iterate (B + 1) i₀ q₀
      hstartDepth (by omega) hstartLeft hstartRight
      hstartValue
  have hmax := hbounded i' q'
    hdepthLower hdepthUpper hqLeft hqRight
  omega

end Gilbreath

-- END GilbreathAscentBudget_20260925.lean


-- BEGIN GilbreathStrictPoint_20260925.lean

namespace Gilbreath

/-- A point-form left strict rise inside one bounded finite triangle.
The maximal block containing the point is constructed here, so the
caller need not already know its horizontal extent. -/
theorem strict_coarse_upward_left_at_point
    (a : ℕ → ℕ)
    (N L B T iI left right0 jI kI E ip jp D : ℕ)
    (hzero : NoLongZeroBlock a N L)
    (hL : 1 ≤ L)
    (hvalid : iI + right0 ≤ N)
    (hE : 0 < E) (hBE : B < 2 * E)
    (hD : 0 < D) (hBD : B < 2 * D)
    (hIgood : IsMaximalTwoBlock a iI left right0 jI kI E)
    (htriangle :
      ∀ d, d ≤ T → ∀ x, left ≤ x →
        x < right0 - d →
          iterAbsDiff a (iI + d) x ≤ B)
    (hiOrder : iI ≤ ip) (hipT : ip ≤ iI + T)
    (hpointLeft : left ≤ jp)
    (hpointRight : jp < right0 - (ip - iI))
    (hpointValue : iterAbsDiff a ip jp = D)
    (hgap : jp < jI)
    (hlower : iI + (jI - jp) + L ≤ ip)
    (hupper : ip ≤ iI + kI - L) :
    ∃ i' q D', ip - ((jI - jp) + L) ≤ i' ∧
      i' < ip ∧
      q ≤ jp + L ∧ jp ≤ q + L ∧
      D < D' ∧ D' ≤ B ∧
      iterAbsDiff a i' q = D' := by
  let span := ip - iI
  let rightP := right0 - span
  have hspan : span ≤ T := by dsimp [span]; omega
  have hrightEq : rightP + span = right0 := by
    dsimp [rightP, span]
    omega
  have hrowValid : ip + rightP ≤ N := by
    dsimp [rightP, span] at *
    omega
  obtain ⟨jJ, kJ, hJgood, hJleft, hJright⟩ :=
    maximal_two_block_exists_through_point
      a ip left rightP jp D
      hpointLeft hpointRight hpointValue
  have hIvalid : iI + jI + kI ≤ N := by
    have hiEnd := hIgood.2.1
    omega
  have hJvalid : ip + jJ + kJ ≤ N := by
    have hjEnd := hJgood.2.1
    omega
  have hIgood' : IsMaximalTwoBlock a iI left
      (rightP + (ip - iI)) jI kI E := by
    simpa [span, hrightEq] using hIgood
  have hambientI :
      ∀ d, d ≤ ip - ((jI - jp) + L) - iI →
        ∀ x, left ≤ x →
          x < rightP + (ip - iI) - d →
            iterAbsDiff a (iI + d) x ≤ B := by
    intro d hd x hxleft hxright
    have hdT : d ≤ T := by omega
    have hxright' : x < right0 - d := by
      simpa [span, hrightEq] using hxright
    exact htriangle d hdT x hxleft hxright'
  have hboundJ :
      ∀ h, h ≤ (jI - jp) + L →
        ∀ t, t < kJ + h →
          iterAbsDiff a (ip - h) (jJ + t) ≤ B := by
    intro h hh t ht
    let d := ip - h - iI
    have hspanH : (jI - jp) + L ≤ span := by
      dsimp [span]
      omega
    have hdT : d ≤ T := by
      dsimp [d, span] at *
      omega
    have hdepth : iI + d = ip - h := by
      dsimp [d]
      omega
    have hright : right0 - d = rightP + h := by
      dsimp [d, rightP, span] at *
      omega
    have hjleft : left ≤ jJ + t := by
      have hj := hJgood.1
      omega
    have hjright : jJ + t < right0 - d := by
      have hj := hJgood.2.1
      omega
    rw [← hdepth]
    exact htriangle d hdT (jJ + t) hjleft hjright
  obtain ⟨h, q, D', hh, hqRight, hqLeft,
    hlarge, hupperD, hv⟩ :=
    strict_coarse_upward_left_from_good_blocks
      a N L B iI ip left rightP
      jI kI E jJ kJ D jp
      hzero hL hE hBE hD hBD
      hiOrder hIvalid hJvalid
      hIgood' hJgood hJleft hJright
      hgap hlower hupper hambientI hboundJ
  refine ⟨ip - (h + 1), q, D', ?_, ?_,
    hqRight, hqLeft, hlarge, hupperD, hv⟩
  · omega
  · omega

/-- Point-form right strict rise, measured in the right coordinate
j+i rather than the row's left index j. -/
theorem strict_coarse_upward_right_at_point
    (a : ℕ → ℕ)
    (N L B T iI left right0 jI kI E ip jp D : ℕ)
    (hzero : NoLongZeroBlock a N L)
    (hL : 1 ≤ L)
    (hvalid : iI + right0 ≤ N)
    (hE : 0 < E) (hBE : B < 2 * E)
    (hD : 0 < D) (hBD : B < 2 * D)
    (hIgood : IsMaximalTwoBlock a iI left right0 jI kI E)
    (htriangle :
      ∀ d, d ≤ T → ∀ x, left ≤ x →
        x < right0 - d →
          iterAbsDiff a (iI + d) x ≤ B)
    (hiOrder : iI ≤ ip) (hipT : ip ≤ iI + T)
    (hpointLeft : left ≤ jp)
    (hpointRight : jp < right0 - (ip - iI))
    (hpointValue : iterAbsDiff a ip jp = D)
    (hgap : jI + kI ≤ jp + (ip - iI))
    (hlower : iI +
      (jp + (ip - iI) + 1 - (jI + kI)) + L ≤ ip)
    (hupper : ip ≤ iI + kI - L) :
    ∃ i' q D',
      ip - ((jp + (ip - iI) + 1 - (jI + kI)) + L) ≤ i' ∧
      i' < ip ∧
      q + i' ≤ jp + ip + L ∧
      jp + ip ≤ q + i' + L ∧
      D < D' ∧ D' ≤ B ∧
      iterAbsDiff a i' q = D' := by
  let span := ip - iI
  let rightP := right0 - span
  have hspan : span ≤ T := by dsimp [span]; omega
  have hrightEq : rightP + span = right0 := by
    dsimp [rightP, span]
    omega
  have hrowValid : ip + rightP ≤ N := by
    dsimp [rightP, span] at *
    omega
  obtain ⟨jJ, kJ, hJgood, hJleft, hJright⟩ :=
    maximal_two_block_exists_through_point
      a ip left rightP jp D
      hpointLeft hpointRight hpointValue
  have hIvalid : iI + jI + kI ≤ N := by
    have hiEnd := hIgood.2.1
    omega
  have hJvalid : ip + jJ + kJ ≤ N := by
    have hjEnd := hJgood.2.1
    omega
  have hIgood' : IsMaximalTwoBlock a iI left
      (rightP + (ip - iI)) jI kI E := by
    simpa [span, hrightEq] using hIgood
  have hambientI :
      ∀ d, d ≤ ip -
        ((jp + (ip - iI) + 1 - (jI + kI)) + L) - iI →
        ∀ x, left ≤ x →
          x < rightP + (ip - iI) - d →
            iterAbsDiff a (iI + d) x ≤ B := by
    intro d hd x hxleft hxright
    have hdT : d ≤ T := by omega
    have hxright' : x < right0 - d := by
      simpa [span, hrightEq] using hxright
    exact htriangle d hdT x hxleft hxright'
  have hboundJ :
      ∀ h, h ≤
        (jp + (ip - iI) + 1 - (jI + kI)) + L →
        ∀ t, t < kJ + h →
          iterAbsDiff a (ip - h) (jJ + t) ≤ B := by
    intro h hh t ht
    let d := ip - h - iI
    have hspanH :
        (jp + (ip - iI) + 1 - (jI + kI)) + L ≤ span := by
      dsimp [span]
      omega
    have hdT : d ≤ T := by
      dsimp [d, span] at *
      omega
    have hdepth : iI + d = ip - h := by
      dsimp [d]
      omega
    have hright : right0 - d = rightP + h := by
      dsimp [d, rightP, span] at *
      omega
    have hjleft : left ≤ jJ + t := by
      have hj := hJgood.1
      omega
    have hjright : jJ + t < right0 - d := by
      have hj := hJgood.2.1
      omega
    rw [← hdepth]
    exact htriangle d hdT (jJ + t) hjleft hjright
  obtain ⟨h, q, D', hh, hqRight, hqLeft,
    hlarge, hupperD, hv⟩ :=
    strict_coarse_upward_right_from_good_blocks
      a N L B iI ip left rightP
      jI kI E jJ kJ D jp
      hzero hL hE hBE hD hBD
      hiOrder hIvalid hJvalid
      hIgood' hJgood hJleft hJright
      hgap hlower hupper hambientI hboundJ
  refine ⟨ip - (h + 1), q, D', ?_, ?_, ?_, ?_,
    hlarge, hupperD, hv⟩
  all_goals omega

end Gilbreath

-- END GilbreathStrictPoint_20260925.lean


-- BEGIN GilbreathLargeBlockLeft_20260925.lean

namespace Gilbreath

/-- A source-faithful left-side exclusion underlying CHT Lemma 5.8:
a high-value point cannot have enough room for B+1 strict rises
while staying to the left of a fixed good block. -/
theorem left_good_block_ascent_budget_contradiction
    (a : ℕ → ℕ)
    (N L B T Dmin iI left right0 jI kI E
      i₀ q₀ lo hi : ℕ)
    (hzero : NoLongZeroBlock a N L)
    (hL : 1 ≤ L)
    (hvalid : iI + right0 ≤ N)
    (hDmin : 0 < Dmin) (hBmin : B < 2 * Dmin)
    (hE : Dmin ≤ E)
    (hIgood : IsMaximalTwoBlock a iI left right0 jI kI E)
    (htriangle :
      ∀ d, d ≤ T → ∀ x, left ≤ x →
        x < right0 - d →
          iterAbsDiff a (iI + d) x ≤ B)
    (hpointValue : Dmin ≤ iterAbsDiff a i₀ q₀)
    (hstartDepth :
      iI + (B + 1) * (jI - lo + L) ≤ i₀)
    (hstartLeft : lo + (B + 1) * L ≤ q₀)
    (hstartRight : q₀ + (B + 1) * L ≤ hi)
    (hloLeft : left ≤ lo)
    (hhiGap : hi < jI)
    (hrow0 : i₀ ≤ iI + T)
    (hhiRow : hi < right0 - (i₀ - iI))
    (hupper : i₀ ≤ iI + kI - L) :
    False := by
  have hEpos : 0 < E := by omega
  have hBE : B < 2 * E := by omega
  apply bounded_strict_ascent_impossible
    (iterAbsDiff a) B L (jI - lo + L)
    Dmin iI lo hi i₀ q₀
    hstartDepth hstartLeft hstartRight hpointValue
  · intro i q hbase htop hloq hqhi
    have hdT : i - iI ≤ T := by omega
    have hqleft : left ≤ q := by omega
    have hqright : q < right0 - (i - iI) := by omega
    have hdepth : iI + (i - iI) = i := by omega
    rw [← hdepth]
    exact htriangle (i - iI) hdT q hqleft hqright
  · intro i q hdepth htop hloq hqhi hlarge
    let D := iterAbsDiff a i q
    have hDpos : 0 < D := by dsimp [D]; omega
    have hBD : B < 2 * D := by dsimp [D]; omega
    have hbase : iI ≤ i := by omega
    have hipT : i ≤ iI + T := by omega
    have hqleft : left ≤ q := by omega
    have hqright : q < right0 - (i - iI) := by omega
    have hgap : q < jI := by omega
    have hlower : iI + (jI - q) + L ≤ i := by omega
    have hupper' : i ≤ iI + kI - L := by omega
    obtain ⟨i', q', D', hnearDepth, hdepthRise,
      hmoveRight, hmoveLeft, hvalueRise, _, hv⟩ :=
      strict_coarse_upward_left_at_point
        a N L B T iI left right0 jI kI E i q D
        hzero hL hvalid hEpos hBE hDpos hBD
        hIgood htriangle hbase hipT
        hqleft hqright rfl hgap hlower hupper'
    refine ⟨i', q', hdepthRise, ?_,
      hmoveRight, hmoveLeft, ?_⟩
    · omega
    · change D < iterAbsDiff a i' q'
      rw [hv]
      exact hvalueRise

end Gilbreath

-- END GilbreathLargeBlockLeft_20260925.lean


-- BEGIN GilbreathLargeBlockNumbers_20260925.lean

namespace Gilbreath

/-- Quantitative room for B+1 strict ascents on the left.
S = B(L+1); the coarse point is within S of jI-4S. -/
theorem left_ascent_room_from_coarse_window
    (B L left jI kI iI p : ℕ)
    (hB : 1 ≤ B) (hL : 1 ≤ L)
    (hleft : left + 8 * (B * (L + 1)) ≤ jI)
    (hlength : 100 * L * B * B ≤ kI)
    (hnear :
      Nat.dist p (jI - 4 * (B * (L + 1))) ≤
        B * (L + 1)) :
    let S := B * (L + 1)
    let lo := jI - 8 * S
    let hi := jI - S
    let i₀ := iI + kI - L
    left ≤ lo ∧ hi < jI ∧
      lo + (B + 1) * L ≤ p ∧
      p + (B + 1) * L ≤ hi ∧
      iI + (B + 1) * (jI - lo + L) ≤ i₀ := by
  dsimp
  let S := B * (L + 1)
  have hS : 0 < S := by
    dsimp [S]
    nlinarith
  have hmove : (B + 1) * L ≤ 2 * S := by
    dsimp [S]
    nlinarith
  have hnear' :
      p ≤ (jI - 4 * S) + S ∧
      jI - 4 * S ≤ p + S := by
    simpa only [S] using
      (show p ≤ (jI - 4 * S) + S ∧
        jI - 4 * S ≤ p + S by
          dsimp [S] at hnear ⊢
          unfold Nat.dist at hnear
          omega)
  have hB2 : B + 1 ≤ 2 * B := by omega
  have hL2 : L + 1 ≤ 2 * L := by omega
  have hSbound : S ≤ 2 * B * L := by
    dsimp [S]
    nlinarith
  have hBL : L ≤ B * L := by nlinarith
  have hGbound : 8 * S + L ≤ 17 * B * L := by
    nlinarith
  have hBB : 1 ≤ B * B := by nlinarith
  have hLBB : L ≤ B * B * L := by
    have hm := Nat.mul_le_mul_right L hBB
    nlinarith
  have hmul :
      (B + 1) * (8 * S + L) ≤
        (2 * B) * (17 * B * L) :=
    Nat.mul_le_mul hB2 hGbound
  have hbudget :
      (B + 1) * (8 * S + L) + L ≤
        100 * L * B * B := by
    nlinarith
  have hlen : L ≤ kI := by nlinarith
  have hdiff : jI - (jI - 8 * S) = 8 * S := by omega
  have hdepth :
      iI + (B + 1) * (jI - (jI - 8 * S) + L) ≤
        iI + kI - L := by
    rw [hdiff]
    omega
  refine ⟨by omega, by omega, by omega, by omega, ?_⟩
  simpa only [S] using hdepth

/-- Symmetric numerical window measured in right coordinates.
The target row point is near jI+L+4S, with S=C(L+1). -/
theorem right_ascent_room_from_coarse_window
    (C L iI left right0 jI kI p : ℕ)
    (hC : 1 ≤ C) (hL : 1 ≤ L)
    (hIleft : left ≤ jI)
    (hright :
      jI + kI + 8 * (C * (L + 1)) < right0)
    (hlength : 100 * L * C * C ≤ kI)
    (hnear :
      Nat.dist p (jI + L + 4 * (C * (L + 1))) ≤
        C * (L + 1)) :
    let S := C * (L + 1)
    let R := iI + jI + kI
    let i₀ := iI + kI - L
    let r₀ := i₀ + p
    let lo := R + S
    let hi := R + 8 * S
    i₀ + left ≤ lo ∧
      R ≤ lo ∧ hi < iI + right0 ∧
      lo + (C + 1) * L ≤ r₀ ∧
      r₀ + (C + 1) * L ≤ hi ∧
      iI + (C + 1) * (hi - R + L + 1) ≤ i₀ := by
  dsimp
  let S := C * (L + 1)
  let R := iI + jI + kI
  let i₀ := iI + kI - L
  have hC2 : 1 ≤ C * C := by nlinarith
  have hLC2 : L ≤ C * C * L := by
    have hm := Nat.mul_le_mul_right L hC2
    nlinarith
  have hLk : L ≤ kI := by nlinarith
  have hidentity : i₀ + (jI + L) = R := by
    dsimp [i₀, R]
    omega
  have hmove : (C + 1) * L ≤ 2 * S := by
    dsimp [S]
    nlinarith
  have hnear' :
      p ≤ jI + L + 4 * S + S ∧
      jI + L + 4 * S ≤ p + S := by
    dsimp [S] at hnear ⊢
    unfold Nat.dist at hnear
    omega
  have hCdouble : C + 1 ≤ 2 * C := by omega
  have hSbound : S ≤ 2 * C * L := by
    dsimp [S]
    nlinarith
  have hCL : L ≤ C * L := by nlinarith
  have hOne : 1 ≤ C * L := by nlinarith
  have hGbound : 8 * S + L + 1 ≤ 18 * C * L := by
    nlinarith
  have hmul :
      (C + 1) * (8 * S + L + 1) ≤
        (2 * C) * (18 * C * L) :=
    Nat.mul_le_mul hCdouble hGbound
  have hbudget :
      (C + 1) * (8 * S + L + 1) + L ≤
        100 * L * C * C := by
    nlinarith
  have hdiff : (R + 8 * S) - R = 8 * S := by omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [S, R, i₀] at *
    omega
  · omega
  · dsimp [S, R] at *
    omega
  · omega
  · omega
  · rw [hdiff]
    omega

end Gilbreath

-- END GilbreathLargeBlockNumbers_20260925.lean


-- BEGIN GilbreathLargeBlockExclusion_20260925.lean

namespace Gilbreath

/-- A long good block far from the left boundary excludes a high
point in the coarse-monotonicity window. This is the left half of
the quantitative "small or huge" argument. -/
theorem long_good_block_excludes_left_high_point
    (a : ℕ → ℕ)
    (N C B L T Dmin iI left right0 jI kI E : ℕ)
    (hzero : NoLongZeroBlock a N L)
    (hL : 1 ≤ L) (hC : 1 ≤ C) (hBC : B ≤ C)
    (hvalid : iI + right0 ≤ N)
    (hDmin : 0 < Dmin) (hBmin : B < 2 * Dmin)
    (hE : Dmin ≤ E)
    (hIgood : IsMaximalTwoBlock a iI left right0 jI kI E)
    (htriangle :
      ∀ d, d ≤ T → ∀ x, left ≤ x →
        x < right0 - d →
          iterAbsDiff a (iI + d) x ≤ B)
    (hrow0 : iI + kI - L ≤ iI + T)
    (hlength : 100 * L * C * C ≤ kI)
    (hpoint :
      ∃ p, Dmin ≤ iterAbsDiff a (iI + kI - L) p ∧
        Nat.dist p (jI - 4 * (C * (L + 1))) ≤
          C * (L + 1)) :
    jI < left + 8 * (C * (L + 1)) := by
  by_contra hfar
  have hfar' : left + 8 * (C * (L + 1)) ≤ jI := by
    omega
  obtain ⟨p, hpValue, hpNear⟩ := hpoint
  let S := C * (L + 1)
  let lo := jI - 8 * S
  let hi := jI - S
  let i₀ := iI + kI - L
  obtain ⟨hloLeft, hhiGap, hpLeftC, hpRightC,
    hdepthC⟩ :=
    left_ascent_room_from_coarse_window
      C L left jI kI iI p
      hC hL hfar' hlength hpNear
  have hmove : (B + 1) * L ≤ (C + 1) * L := by
    exact Nat.mul_le_mul_right L (by omega)
  have hG : 0 ≤ jI - lo + L := Nat.zero_le _
  have hdepthMove :
      (B + 1) * (jI - lo + L) ≤
        (C + 1) * (jI - lo + L) := by
    exact Nat.mul_le_mul_right (jI - lo + L) (by omega)
  have hstartDepth :
      iI + (B + 1) * (jI - lo + L) ≤ i₀ := by
    dsimp [S, lo, i₀] at *
    omega
  have hstartLeft : lo + (B + 1) * L ≤ p := by
    dsimp [S, lo] at *
    omega
  have hstartRight : p + (B + 1) * L ≤ hi := by
    dsimp [S, hi] at *
    omega
  have hhiRow : hi < right0 - (i₀ - iI) := by
    have hIend := hIgood.2.1
    dsimp [hi, i₀, S] at *
    omega
  exact left_good_block_ascent_budget_contradiction
    a N L B T Dmin iI left right0 jI kI E
    i₀ p lo hi
    hzero hL hvalid hDmin hBmin hE hIgood htriangle
    hpValue hstartDepth hstartLeft hstartRight
    hloLeft hhiGap hrow0 hhiRow (by rfl)

end Gilbreath

-- END GilbreathLargeBlockExclusion_20260925.lean


-- BEGIN GilbreathLargeBlockLeftBoundary_20260925.lean

namespace Gilbreath

/-- The left boundary assertion of the "small or huge" argument,
with a safe 8 C (L+1) margin. The high point is supplied by coarse
monotonicity from the bottom vertex of the bounded triangle. -/
theorem long_good_block_near_left_boundary
    (a : ℕ → ℕ)
    (N C B L T Dmin top left dI jI kI E : ℕ)
    (hinput : ∀ u < N, a u ≤ C)
    (hzero : NoLongZeroBlock a N L)
    (hL : 1 ≤ L) (hC : 1 ≤ C)
    (hBC : B ≤ C)
    (hvalid : top + T + left < N)
    (hDmin : 1 ≤ Dmin) (hBmin : B < 2 * Dmin)
    (hbottom : iterAbsDiff a (top + T) left = Dmin)
    (htriangle :
      ∀ d, d ≤ T → ∀ x, left ≤ x →
        x < left + (T - d) + 1 →
          iterAbsDiff a (top + d) x ≤ B)
    (hdI : dI ≤ T)
    (hE : Dmin ≤ E)
    (hIgood : IsMaximalTwoBlock a (top + dI)
      left (left + (T - dI) + 1) jI kI E)
    (hlength : 100 * L * C * C ≤ kI) :
    jI < left + 8 * (C * (L + 1)) := by
  by_contra hfar
  have hfar' :
      left + 8 * (C * (L + 1)) ≤ jI := by omega
  have hC2 : 1 ≤ C * C := by nlinarith
  have hLk : L ≤ kI := by
    have hm := Nat.mul_le_mul_left L hC2
    nlinarith
  let d₀ := dI + (kI - L)
  let iI := top + dI
  let right0 := left + (T - dI) + 1
  let i₀ := top + d₀
  let q := jI - 4 * (C * (L + 1))
  have hIend : jI + kI ≤ right0 := hIgood.2.1
  have hdepth : d₀ ≤ T := by
    dsimp [d₀, right0] at *
    omega
  have hqleft : left ≤ q := by
    dsimp [q]
    omega
  have hqright : q ≤ left + (T - d₀) := by
    dsimp [q, d₀, right0] at *
    omega
  have htriangleOffset :
      ∀ d, d ≤ T → ∀ offset, offset ≤ T - d →
        iterAbsDiff a (top + d) (left + offset) ≤ B := by
    intro d hd offset hoff
    exact htriangle d hd (left + offset)
      (by omega) (by omega)
  obtain ⟨p, _, _, _, _, _, _, hpValue, _, _, hpNear⟩ :=
    bounded_triangle_good_block_covering
      a N C L top T left Dmin B d₀ q
      hinput hzero hL hvalid hDmin hbottom
      htriangleOffset hdepth hqleft hqright
  have hpDist :
      Nat.dist p q ≤ C * (L + 1) := by
    nlinarith
  have hpoint :
      ∃ p, Dmin ≤
        iterAbsDiff a (iI + kI - L) p ∧
        Nat.dist p (jI - 4 * (C * (L + 1))) ≤
          C * (L + 1) := by
    refine ⟨p, ?_, ?_⟩
    · have heq : iI + kI - L = top + d₀ := by
        dsimp [iI, d₀]
        omega
      simpa [heq] using hpValue
    · simpa [q] using hpDist
  have hvalidBlock : iI + right0 ≤ N := by
    dsimp [iI, right0]
    omega
  have htriangleBlock :
      ∀ d, d ≤ T - dI → ∀ x, left ≤ x →
        x < right0 - d →
          iterAbsDiff a (iI + d) x ≤ B := by
    intro d hd x hx hxright
    have hdt : dI + d ≤ T := by omega
    have hrightEq :
        right0 - d = left + (T - (dI + d)) + 1 := by
      dsimp [right0]
      omega
    have hdepthEq : iI + d = top + (dI + d) := by
      dsimp [iI]
      omega
    rw [hdepthEq]
    exact htriangle (dI + d) hdt x hx
      (by simpa [hrightEq] using hxright)
  have hrowBlock :
      iI + kI - L ≤ iI + (T - dI) := by
    dsimp [iI, right0] at *
    omega
  have hleftNear :=
    long_good_block_excludes_left_high_point
      a N C B L (T - dI) Dmin iI left right0 jI kI E
      hzero hL hC hBC hvalidBlock
      (by omega) hBmin hE hIgood
      htriangleBlock hrowBlock hlength hpoint
  exact hfar hleftNear

end Gilbreath

-- END GilbreathLargeBlockLeftBoundary_20260925.lean


-- BEGIN GilbreathLargeBlockRight_20260925.lean

namespace Gilbreath

/-- The right-coordinate counterpart of the finite strict-ascent
budget. This is the right-side exclusion used toward CHT Lemma 5.8. -/
theorem right_good_block_ascent_budget_contradiction
    (a : ℕ → ℕ)
    (N L B T Dmin iI left right0 jI kI E
      i₀ r₀ lo hi : ℕ)
    (hzero : NoLongZeroBlock a N L)
    (hL : 1 ≤ L)
    (hvalid : iI + right0 ≤ N)
    (hBmin : B < 2 * Dmin)
    (hE : Dmin ≤ E)
    (hIgood : IsMaximalTwoBlock a iI left right0 jI kI E)
    (htriangle :
      ∀ d, d ≤ T → ∀ x, left ≤ x →
        x < right0 - d →
          iterAbsDiff a (iI + d) x ≤ B)
    (hpointValue : Dmin ≤ iterAbsDiff a i₀ (r₀ - i₀))
    (hstartDepth :
      iI + (B + 1) *
        (hi - (iI + jI + kI) + L + 1) ≤ i₀)
    (hstartLeft : lo + (B + 1) * L ≤ r₀)
    (hstartRight : r₀ + (B + 1) * L ≤ hi)
    (hloRow : i₀ + left ≤ lo)
    (hloGap : iI + jI + kI ≤ lo)
    (hhiRow : hi < iI + right0)
    (hrow0 : i₀ ≤ iI + T)
    (hupper : i₀ ≤ iI + kI - L) :
    False := by
  have hDmin : 0 < Dmin := by omega
  have hEpos : 0 < E := by omega
  have hBE : B < 2 * E := by omega
  apply bounded_strict_ascent_impossible
    (fun i r => iterAbsDiff a i (r - i))
    B L (hi - (iI + jI + kI) + L + 1)
    Dmin iI lo hi i₀ r₀
    hstartDepth hstartLeft hstartRight hpointValue
  · intro i r hbase htop hlo hhi
    have hdT : i - iI ≤ T := by omega
    have hxleft : left ≤ r - i := by omega
    have hxright :
        r - i < right0 - (i - iI) := by omega
    have hdepth : iI + (i - iI) = i := by omega
    simpa only [hdepth] using
      htriangle (i - iI) hdT (r - i) hxleft hxright
  · intro i r hdepth htop hlo hhi hlarge
    let jp := r - i
    let D := iterAbsDiff a i jp
    have hDpos : 0 < D := by dsimp [D, jp]; omega
    have hBD : B < 2 * D := by dsimp [D, jp]; omega
    have hbase : iI ≤ i := by omega
    have hipT : i ≤ iI + T := by omega
    have hqleft : left ≤ jp := by dsimp [jp]; omega
    have hqright : jp < right0 - (i - iI) := by
      dsimp [jp]
      omega
    have hgap : jI + kI ≤ jp + (i - iI) := by
      dsimp [jp]
      omega
    have hlower : iI +
        (jp + (i - iI) + 1 - (jI + kI)) + L ≤ i := by
      dsimp [jp]
      omega
    have hupper' : i ≤ iI + kI - L := by omega
    obtain ⟨i', q', D', hnearDepth, hdepthRise,
      hmoveRight, hmoveLeft, hvalueRise, _, hv⟩ :=
      strict_coarse_upward_right_at_point
        a N L B T iI left right0 jI kI E i jp D
        hzero hL hvalid hEpos hBE hDpos hBD
        hIgood htriangle hbase hipT
        hqleft hqright rfl hgap hlower hupper'
    refine ⟨i', q' + i', hdepthRise, ?_, ?_, ?_, ?_⟩
    · dsimp [jp] at *
      omega
    · dsimp [jp] at *
      omega
    · dsimp [jp] at *
      omega
    · change D < iterAbsDiff a i' ((q' + i') - i')
      have heq : (q' + i') - i' = q' := by omega
      rw [heq, hv]
      exact hvalueRise

end Gilbreath

-- END GilbreathLargeBlockRight_20260925.lean


-- BEGIN GilbreathLargeBlockRightExclusion_20260925.lean

namespace Gilbreath

/-- A long good block far from the right boundary excludes a high
point in the corresponding coarse-monotonicity window. -/
theorem long_good_block_excludes_right_high_point
    (a : ℕ → ℕ)
    (N C B L T Dmin iI left right0 jI kI E : ℕ)
    (hzero : NoLongZeroBlock a N L)
    (hL : 1 ≤ L) (hC : 1 ≤ C) (hBC : B ≤ C)
    (hvalid : iI + right0 ≤ N)
    (hBmin : B < 2 * Dmin)
    (hE : Dmin ≤ E)
    (hIgood : IsMaximalTwoBlock a iI left right0 jI kI E)
    (htriangle :
      ∀ d, d ≤ T → ∀ x, left ≤ x →
        x < right0 - d →
          iterAbsDiff a (iI + d) x ≤ B)
    (hrow0 : iI + kI - L ≤ iI + T)
    (hlength : 100 * L * C * C ≤ kI)
    (hpoint :
      ∃ p, Dmin ≤ iterAbsDiff a (iI + kI - L) p ∧
        Nat.dist p (jI + L + 4 * (C * (L + 1))) ≤
          C * (L + 1)) :
    right0 ≤ jI + kI + 8 * (C * (L + 1)) := by
  by_contra hfar
  have hfar' :
      jI + kI + 8 * (C * (L + 1)) < right0 := by
    omega
  obtain ⟨p, hpValue, hpNear⟩ := hpoint
  let S := C * (L + 1)
  let R := iI + jI + kI
  let i₀ := iI + kI - L
  let r₀ := i₀ + p
  let lo := R + S
  let hi := R + 8 * S
  obtain ⟨hloRow, hloGap, hhiRow, hpLeftC, hpRightC,
    hdepthC⟩ :=
    right_ascent_room_from_coarse_window
      C L iI left right0 jI kI p
      hC hL hIgood.1 hfar' hlength hpNear
  have hmove : (B + 1) * L ≤ (C + 1) * L :=
    Nat.mul_le_mul_right L (by omega)
  have hdepthMove :
      (B + 1) * (hi - R + L + 1) ≤
        (C + 1) * (hi - R + L + 1) :=
    Nat.mul_le_mul_right (hi - R + L + 1) (by omega)
  have hstartDepth :
      iI + (B + 1) *
        (hi - (iI + jI + kI) + L + 1) ≤ i₀ := by
    exact (Nat.add_le_add_left hdepthMove iI).trans hdepthC
  have hstartLeft : lo + (B + 1) * L ≤ r₀ := by
    omega
  have hstartRight : r₀ + (B + 1) * L ≤ hi := by
    omega
  have hstartValue :
      Dmin ≤ iterAbsDiff a i₀ (r₀ - i₀) := by
    have heq : r₀ - i₀ = p := by
      dsimp [r₀]
      omega
    simpa [heq] using hpValue
  exact right_good_block_ascent_budget_contradiction
    a N L B T Dmin iI left right0 jI kI E
    i₀ r₀ lo hi
    hzero hL hvalid hBmin hE hIgood htriangle
    hstartValue hstartDepth hstartLeft hstartRight
    hloRow hloGap hhiRow hrow0 (by rfl)

end Gilbreath

-- END GilbreathLargeBlockRightExclusion_20260925.lean


-- BEGIN GilbreathLargeBlockRightBoundary_20260925.lean

namespace Gilbreath

/-- The right boundary assertion of the "small or huge" argument,
with a safe 8 C (L+1) margin. -/
theorem long_good_block_near_right_boundary
    (a : ℕ → ℕ)
    (N C B L T Dmin top left dI jI kI E : ℕ)
    (hinput : ∀ u < N, a u ≤ C)
    (hzero : NoLongZeroBlock a N L)
    (hL : 1 ≤ L) (hC : 1 ≤ C)
    (hBC : B ≤ C)
    (hvalid : top + T + left < N)
    (hDmin : 1 ≤ Dmin) (hBmin : B < 2 * Dmin)
    (hbottom : iterAbsDiff a (top + T) left = Dmin)
    (htriangle :
      ∀ d, d ≤ T → ∀ x, left ≤ x →
        x < left + (T - d) + 1 →
          iterAbsDiff a (top + d) x ≤ B)
    (hdI : dI ≤ T)
    (hE : Dmin ≤ E)
    (hIgood : IsMaximalTwoBlock a (top + dI)
      left (left + (T - dI) + 1) jI kI E)
    (hlength : 100 * L * C * C ≤ kI) :
    left + (T - dI) + 1 ≤
      jI + kI + 8 * (C * (L + 1)) := by
  by_contra hfar
  have hfar' :
      jI + kI + 8 * (C * (L + 1)) <
        left + (T - dI) + 1 := by omega
  have hC2 : 1 ≤ C * C := by nlinarith
  have hLk : L ≤ kI := by
    have hm := Nat.mul_le_mul_left L hC2
    nlinarith
  let d₀ := dI + (kI - L)
  let iI := top + dI
  let right0 := left + (T - dI) + 1
  let q := jI + L + 4 * (C * (L + 1))
  have hIend : jI + kI ≤ right0 := hIgood.2.1
  have hIleft : left ≤ jI := hIgood.1
  have hdepth : d₀ ≤ T := by
    dsimp [d₀, right0] at *
    omega
  have hqleft : left ≤ q := by
    dsimp [q]
    omega
  have hqright : q ≤ left + (T - d₀) := by
    dsimp [q, d₀, right0] at *
    omega
  have htriangleOffset :
      ∀ d, d ≤ T → ∀ offset, offset ≤ T - d →
        iterAbsDiff a (top + d) (left + offset) ≤ B := by
    intro d hd offset hoff
    exact htriangle d hd (left + offset)
      (by omega) (by omega)
  obtain ⟨p, _, _, _, _, _, _, hpValue, _, _, hpNear⟩ :=
    bounded_triangle_good_block_covering
      a N C L top T left Dmin B d₀ q
      hinput hzero hL hvalid hDmin hbottom
      htriangleOffset hdepth hqleft hqright
  have hpDist :
      Nat.dist p q ≤ C * (L + 1) := by
    nlinarith
  have hpoint :
      ∃ p, Dmin ≤
        iterAbsDiff a (iI + kI - L) p ∧
        Nat.dist p (jI + L + 4 * (C * (L + 1))) ≤
          C * (L + 1) := by
    refine ⟨p, ?_, ?_⟩
    · have heq : iI + kI - L = top + d₀ := by
        dsimp [iI, d₀]
        omega
      simpa [heq] using hpValue
    · simpa [q] using hpDist
  have hvalidBlock : iI + right0 ≤ N := by
    dsimp [iI, right0]
    omega
  have htriangleBlock :
      ∀ d, d ≤ T - dI → ∀ x, left ≤ x →
        x < right0 - d →
          iterAbsDiff a (iI + d) x ≤ B := by
    intro d hd x hx hxright
    have hdt : dI + d ≤ T := by omega
    have hrightEq :
        right0 - d = left + (T - (dI + d)) + 1 := by
      dsimp [right0]
      omega
    have hdepthEq : iI + d = top + (dI + d) := by
      dsimp [iI]
      omega
    rw [hdepthEq]
    exact htriangle (dI + d) hdt x hx
      (by simpa [hrightEq] using hxright)
  have hrowBlock :
      iI + kI - L ≤ iI + (T - dI) := by
    dsimp [iI, right0] at *
    omega
  have hrightNear :=
    long_good_block_excludes_right_high_point
      a N C B L (T - dI) Dmin iI left right0 jI kI E
      hzero hL hC hBC hvalidBlock
      hBmin hE hIgood
      htriangleBlock hrowBlock hlength hpoint
  exact (Nat.not_le.mpr (by simpa [right0] using hfar')) hrightNear

end Gilbreath

-- END GilbreathLargeBlockRightBoundary_20260925.lean


-- BEGIN GilbreathLargeBlockCover_20260925.lean

namespace Gilbreath

/-- CHT Lemma 5.8, huge-block branch, with explicit safe margins.
A block of length at least 100 L C^2 covers its ambient row except
for at most 8 C (L+1) entries at either end. -/
theorem large_good_block_covers_row
    (a : ℕ → ℕ)
    (N C B L T Dmin top left dI jI kI E : ℕ)
    (hinput : ∀ u < N, a u ≤ C)
    (hzero : NoLongZeroBlock a N L)
    (hL : 1 ≤ L) (hC : 1 ≤ C)
    (hBC : B ≤ C)
    (hvalid : top + T + left < N)
    (hDmin : 1 ≤ Dmin) (hBmin : B < 2 * Dmin)
    (hbottom : iterAbsDiff a (top + T) left = Dmin)
    (htriangle :
      ∀ d, d ≤ T → ∀ x, left ≤ x →
        x < left + (T - d) + 1 →
          iterAbsDiff a (top + d) x ≤ B)
    (hdI : dI ≤ T)
    (hE : Dmin ≤ E)
    (hIgood : IsMaximalTwoBlock a (top + dI)
      left (left + (T - dI) + 1) jI kI E)
    (hlength : 100 * L * C * C ≤ kI) :
    jI < left + 8 * (C * (L + 1)) ∧
    left + (T - dI) + 1 ≤
      jI + kI + 8 * (C * (L + 1)) ∧
    left + (T - dI) + 1 ≤
      left + kI + 16 * (C * (L + 1)) := by
  have hl :=
    long_good_block_near_left_boundary
      a N C B L T Dmin top left dI jI kI E
      hinput hzero hL hC hBC hvalid
      hDmin hBmin hbottom htriangle
      hdI hE hIgood hlength
  have hr :=
    long_good_block_near_right_boundary
      a N C B L T Dmin top left dI jI kI E
      hinput hzero hL hC hBC hvalid
      hDmin hBmin hbottom htriangle
      hdI hE hIgood hlength
  exact ⟨hl, hr, by omega⟩

end Gilbreath

-- END GilbreathLargeBlockCover_20260925.lean


-- BEGIN GilbreathTowerGrowth_20260925.lean

namespace Gilbreath

/-- Starting at a nonzero point, growing its ancestor block by h rows
either preserves its two-valued form or finds a larger point in one
of the intervening parents. This is the local engine of CHT Lemma 3.13. -/
theorem ancestor_two_block_or_larger
    (a : ℕ → ℕ) (i j d : ℕ)
    (hd : 0 < d)
    (hpoint : iterAbsDiff a i j = d) :
    ∀ h, h ≤ i →
      ((∀ t, t ≤ h →
          iterAbsDiff a (i - h) (j + t) = 0 ∨
          iterAbsDiff a (i - h) (j + t) = d) ∧
        (∃ t, t ≤ h ∧
          iterAbsDiff a (i - h) (j + t) = d)) ∨
      (∃ s t, s < h ∧ t ≤ s + 1 ∧
        d < iterAbsDiff a (i - (s + 1)) (j + t)) := by
  intro h
  induction h with
  | zero =>
      intro _
      left
      constructor
      · intro t ht
        have ht0 : t = 0 := by omega
        simpa [ht0, hpoint]
      · exact ⟨0, by omega, by simpa using hpoint⟩
  | succ h ih =>
      intro hh
      have hprev : h ≤ i := by omega
      rcases ih hprev with hstable | hrise
      · obtain ⟨htwo, hatt⟩ := hstable
        have hchild : ∀ t < h + 1,
            iterAbsDiff a (i - h) (j + t) = 0 ∨
            iterAbsDiff a (i - h) (j + t) = d := by
          intro t ht
          exact htwo t (by omega)
        have hchildAtt : ∃ t, t < h + 1 ∧
            iterAbsDiff a (i - h) (j + t) = d := by
          obtain ⟨t, ht, hv⟩ := hatt
          exact ⟨t, by omega, hv⟩
        rcases parent_block_dichotomy
            a (i - h) j (h + 1) d
            (by omega) hd hchild hchildAtt with
          hsame | hbig
        · left
          constructor
          · intro t ht
            have hv := hsame.1 t (by omega)
            simpa [Nat.sub_sub, Nat.add_assoc] using hv
          · obtain ⟨t, ht, hv⟩ := hsame.2
            exact ⟨t, by omega,
              by simpa [Nat.sub_sub, Nat.add_assoc] using hv⟩
        · right
          obtain ⟨t, ht, hv⟩ := hbig
          exact ⟨h, t, by omega, by omega,
            by simpa [Nat.sub_sub, Nat.add_assoc] using hv⟩
      · right
        obtain ⟨s, t, hs, ht, hv⟩ := hrise
        exact ⟨s, t, by omega, ht, hv⟩

end Gilbreath

-- END GilbreathTowerGrowth_20260925.lean


-- BEGIN GilbreathLongTwoBlock_20260925.lean

namespace Gilbreath

/-- A bounded backward cone of sufficient depth contains a long
two-valued block. This is the pigeonhole consequence of the attained
tower argument, proved directly by induction on the remaining value
budget B-d. -/
theorem long_two_block_from_bounded_cone
    (a : ℕ → ℕ) (top i j B K d : ℕ)
    (hK : 1 ≤ K)
    (horder : top ≤ i)
    (hd : 0 < d) (hdB : d ≤ B)
    (hpoint : iterAbsDiff a i j = d)
    (hbound : ∀ row x,
      top ≤ row → row ≤ i →
      j ≤ x → row + x ≤ i + j →
        iterAbsDiff a row x ≤ B)
    (hdepth : K * (B - d + 1) ≤ i - top + 1) :
    ∃ row x d',
      top ≤ row ∧ row ≤ i ∧ j ≤ x ∧
      row + x + K ≤ i + j + 1 ∧
      d ≤ d' ∧ d' ≤ B ∧
      ∀ t < K,
        iterAbsDiff a row (x + t) = 0 ∨
        iterAbsDiff a row (x + t) = d' := by
  have solve :
      ∀ rem i j d,
        B - d = rem →
        top ≤ i → 0 < d → d ≤ B →
        iterAbsDiff a i j = d →
        (∀ row x,
          top ≤ row → row ≤ i →
          j ≤ x → row + x ≤ i + j →
            iterAbsDiff a row x ≤ B) →
        K * (B - d + 1) ≤ i - top + 1 →
        ∃ row x d',
          top ≤ row ∧ row ≤ i ∧ j ≤ x ∧
          row + x + K ≤ i + j + 1 ∧
          d ≤ d' ∧ d' ≤ B ∧
          ∀ t < K,
            iterAbsDiff a row (x + t) = 0 ∨
            iterAbsDiff a row (x + t) = d' := by
    intro rem
    induction rem using Nat.strong_induction_on with
    | h rem ih =>
        intro i j d hrem horder hd hdB hpoint hbound hdepth
        have hfactor : 1 ≤ B - d + 1 := by omega
        have hKmul : K ≤ K * (B - d + 1) := by
          nlinarith
        have hheight : K - 1 ≤ i - top := by omega
        have hanc : K - 1 ≤ i := by omega
        rcases ancestor_two_block_or_larger
            a i j d hd hpoint (K - 1) hanc with
          hstable | hrise
        · obtain ⟨htwo, hatt⟩ := hstable
          refine ⟨i - (K - 1), j, d,
            by omega, by omega, le_refl j, ?_,
            le_refl d, hdB, ?_⟩
          · omega
          · intro t ht
            exact htwo t (by omega)
        · obtain ⟨s, t, hs, ht, hlarge⟩ := hrise
          let i' := i - (s + 1)
          let j' := j + t
          let d' := iterAbsDiff a i' j'
          have hnewDepth : top ≤ i' := by
            dsimp [i']
            omega
          have hnewRow : i' < i := by
            dsimp [i']
            omega
          have hnewCone : i' + j' ≤ i + j := by
            dsimp [i', j']
            omega
          have hnewD : d < d' := by
            simpa [i', j', d'] using hlarge
          have hnewPositive : 0 < d' := by omega
          have hnewBound : d' ≤ B := by
            apply hbound i' j' hnewDepth (by omega)
            · dsimp [j']
              omega
            · exact hnewCone
          have hremDecrease : B - d' < rem := by
            rw [← hrem]
            omega
          have hmul :
              K * (B - d' + 1) ≤ K * (B - d) := by
            apply Nat.mul_le_mul_left
            omega
          have hsplit :
              K * (B - d + 1) = K * (B - d) + K := by
            ring
          have hnewBudget :
              K * (B - d' + 1) ≤ i' - top + 1 := by
            dsimp [i']
            omega
          have hbound' :
              ∀ row x, top ≤ row → row ≤ i' →
                j' ≤ x → row + x ≤ i' + j' →
                  iterAbsDiff a row x ≤ B := by
            intro row x htop hrow hx hsum
            apply hbound row x htop
            · omega
            · dsimp [j'] at hx ⊢
              omega
            · omega
          obtain ⟨row, x, D, htop, hrow, hx,
            hinside, hD, hDB, htwo⟩ :=
            ih (B - d') hremDecrease
              i' j' d' rfl hnewDepth hnewPositive
              hnewBound rfl hbound' hnewBudget
          exact ⟨row, x, D, htop, by omega,
            by dsimp [j'] at hx ⊢; omega,
            by omega, by omega, hDB, htwo⟩
  exact solve (B - d) i j d rfl horder hd hdB
    hpoint hbound hdepth

end Gilbreath

-- END GilbreathLongTwoBlock_20260925.lean


-- BEGIN GilbreathTriangleLongBlock_20260925.lean

namespace Gilbreath

/-- From a bounded triangle with a high bottom vertex, find a long
two-valued block in one of its first H rows. This combines coarse
monotonicity with the direct tower/pigeonhole lemma. -/
theorem bounded_triangle_has_long_two_block
    (a : ℕ → ℕ)
    (N C B L top T left Dmin H K : ℕ)
    (hinput : ∀ u < N, a u ≤ C)
    (hzero : NoLongZeroBlock a N L)
    (hL : 1 ≤ L) (hK : 1 ≤ K)
    (hBC : B ≤ C)
    (hvalid : top + T + left < N)
    (hDmin : 1 ≤ Dmin)
    (hbottom : iterAbsDiff a (top + T) left = Dmin)
    (htriangle :
      ∀ d, d ≤ T → ∀ x, left ≤ x →
        x < left + (T - d) + 1 →
          iterAbsDiff a (top + d) x ≤ B)
    (hH : H ≤ T)
    (hroom : K * C ≤ H) :
    ∃ dI x D,
      dI ≤ H ∧
      left ≤ x ∧
      x + K ≤ left + (T - dI) + 1 ∧
      Dmin ≤ D ∧ D ≤ B ∧
      ∀ t < K,
        iterAbsDiff a (top + dI) (x + t) = 0 ∨
        iterAbsDiff a (top + dI) (x + t) = D := by
  have hDB : Dmin ≤ B := by
    have hb := htriangle T (by omega) left
      (by omega) (by omega)
    simpa [hbottom] using hb
  have hDC : Dmin ≤ C := by omega
  obtain ⟨p, _, hpLeft, hpRight, hpValue, _⟩ :=
    coarse_monotonicity
      a N C L (top + T) left Dmin (top + H) left
      hinput hzero hL hvalid hDmin hDC hbottom
      (by omega) (by omega) (by omega)
  let D := iterAbsDiff a (top + H) p
  have hDpos : 0 < D := by dsimp [D]; omega
  have hDle : D ≤ B := by
    exact htriangle H hH p hpLeft (by omega)
  have hconeBound :
      ∀ row x,
        top ≤ row → row ≤ top + H →
        p ≤ x → row + x ≤ top + H + p →
          iterAbsDiff a row x ≤ B := by
    intro row x hrowLow hrowHigh hx hsum
    have drow : row - top ≤ T := by omega
    have hdepthEq : top + (row - top) = row := by omega
    have hxleft : left ≤ x := by omega
    have hxright :
        x < left + (T - (row - top)) + 1 := by
      omega
    simpa only [hdepthEq] using
      htriangle (row - top) drow x hxleft hxright
  have hfactor : B - D + 1 ≤ C := by omega
  have hbudget :
      K * (B - D + 1) ≤ (top + H) - top + 1 := by
    have hm := Nat.mul_le_mul_left K hfactor
    omega
  obtain ⟨row, x, D', hrowLow, hrowHigh,
    hxLeft, hinside, hvalueLow, hvalueHigh, htwo⟩ :=
    long_two_block_from_bounded_cone
      a top (top + H) p B K D
      hK (by omega) hDpos hDle rfl
      hconeBound hbudget
  let dI := row - top
  have hrowEq : top + dI = row := by
    dsimp [dI]
    omega
  have hdI : dI ≤ H := by dsimp [dI]; omega
  have hrowRight :
      x + K ≤ left + (T - dI) + 1 := by
    dsimp [dI] at *
    omega
  refine ⟨dI, x, D', hdI, by omega,
    hrowRight, by omega, hvalueHigh, ?_⟩
  intro t ht
  simpa only [hrowEq] using htwo t ht

end Gilbreath

-- END GilbreathTriangleLongBlock_20260925.lean


-- BEGIN GilbreathMaximalExtension_20260925.lean

namespace Gilbreath

/-- A maximal {0,D}-block through a D-valued point of another
{0,D}-block contains the entire latter block. -/
theorem maximal_two_block_contains_two_block
    (a : ℕ → ℕ) (i left right x K D p j k : ℕ)
    (hxleft : left ≤ x) (hxright : x + K ≤ right)
    (hblock : ∀ t < K,
      iterAbsDiff a i (x + t) = 0 ∨
      iterAbsDiff a i (x + t) = D)
    (hpointLeft : x ≤ p) (hpointRight : p < x + K)
    (hgood : IsMaximalTwoBlock a i left right j k D)
    (hgoodLeft : j ≤ p) (hgoodRight : p < j + k) :
    j ≤ x ∧ x + K ≤ j + k ∧ K ≤ k := by
  rcases hgood with
    ⟨hlo, hhi, hk, _, _, hmaxLeft, hmaxRight⟩
  have hjx : j ≤ x := by
    by_contra hnot
    have hlt : x < j := by omega
    rcases hmaxLeft with hborder | hstop
    · omega
    · have hindex : x + (j - 1 - x) = j - 1 := by omega
      have hv := hblock (j - 1 - x) (by omega)
      rw [hindex] at hv
      exact hstop hv
  have hxend : x + K ≤ j + k := by
    by_contra hnot
    have hlt : j + k < x + K := by omega
    rcases hmaxRight with hborder | hstop
    · omega
    · have hindex : x + (j + k - x) = j + k := by omega
      have hv := hblock (j + k - x) (by omega)
      rw [hindex] at hv
      exact hstop hv
  exact ⟨hjx, hxend, by omega⟩

/-- Extend a long two-valued block to a good block without losing
its length. -/
theorem long_two_block_extends_to_good
    (a : ℕ → ℕ) (N L i left right x K D : ℕ)
    (hzero : NoLongZeroBlock a N L)
    (hxleft : left ≤ x) (hxright : x + K ≤ right)
    (hvalid : i + x + K ≤ N)
    (hLK : L ≤ K)
    (hblock : ∀ t < K,
      iterAbsDiff a i (x + t) = 0 ∨
      iterAbsDiff a i (x + t) = D) :
    ∃ j k,
      IsMaximalTwoBlock a i left right j k D ∧
      j ≤ x ∧ x + K ≤ j + k ∧ K ≤ k := by
  obtain ⟨t, ht, hv⟩ :=
    long_two_block_attains
      a N L i x K D hzero (by omega) hLK hblock
  let p := x + t
  obtain ⟨j, k, hgood, hgoodLeft, hgoodRight⟩ :=
    maximal_two_block_exists_through_point
      a i left right p D
      (by dsimp [p]; omega)
      (by dsimp [p]; omega)
      (by simpa [p] using hv)
  obtain ⟨hjx, hxend, hkK⟩ :=
    maximal_two_block_contains_two_block
      a i left right x K D p j k
      hxleft hxright hblock
      (by dsimp [p]; omega)
      (by dsimp [p]; omega)
      hgood hgoodLeft hgoodRight
  exact ⟨j, k, hgood, hjx, hxend, hkK⟩

end Gilbreath

-- END GilbreathMaximalExtension_20260925.lean


-- BEGIN GilbreathTriangleLargeGood_20260925.lean

namespace Gilbreath

/-- A bounded triangle with a high bottom vertex contains a large
good block in one of its first H rows, provided H pays for the
tower budget. This block covers its ambient row coarsely. -/
theorem bounded_triangle_has_large_good_block
    (a : ℕ → ℕ)
    (N C B L top T left Dmin H : ℕ)
    (hinput : ∀ u < N, a u ≤ C)
    (hzero : NoLongZeroBlock a N L)
    (hL : 1 ≤ L) (hC : 1 ≤ C)
    (hBC : B ≤ C) (hBmin : B < 2 * Dmin)
    (hvalid : top + T + left < N)
    (hDmin : 1 ≤ Dmin)
    (hbottom : iterAbsDiff a (top + T) left = Dmin)
    (htriangle :
      ∀ d, d ≤ T → ∀ x, left ≤ x →
        x < left + (T - d) + 1 →
          iterAbsDiff a (top + d) x ≤ B)
    (hH : H ≤ T)
    (hroom :
      (100 * L * C * C) * C ≤ H) :
    ∃ dI jG kG D,
      dI ≤ H ∧
      Dmin ≤ D ∧ D ≤ B ∧
      IsMaximalTwoBlock a (top + dI)
        left (left + (T - dI) + 1) jG kG D ∧
      100 * L * C * C ≤ kG ∧
      jG < left + 8 * (C * (L + 1)) ∧
      left + (T - dI) + 1 ≤
        jG + kG + 8 * (C * (L + 1)) ∧
      left + (T - dI) + 1 ≤
        left + kG + 16 * (C * (L + 1)) := by
  let K := 100 * L * C * C
  have hC2 : 1 ≤ C * C := by nlinarith
  have hLC : L ≤ L * (C * C) := by
    simpa using Nat.mul_le_mul_left L hC2
  have hLK : L ≤ K := by
    dsimp [K]
    nlinarith
  have hK : 1 ≤ K := by omega
  obtain ⟨dI, x, D, hdI, hxleft, hxright,
    hDminD, hDB, htwo⟩ :=
    bounded_triangle_has_long_two_block
      a N C B L top T left Dmin H K
      hinput hzero hL hK hBC hvalid hDmin hbottom
      htriangle hH (by simpa [K] using hroom)
  let right0 := left + (T - dI) + 1
  have hvalidRow : top + dI + right0 ≤ N := by
    dsimp [right0]
    omega
  have hvalidBlock : (top + dI) + x + K ≤ N := by
    omega
  obtain ⟨jG, kG, hgood, _, _, hKk⟩ :=
    long_two_block_extends_to_good
      a N L (top + dI) left right0 x K D
      hzero hxleft hxright hvalidBlock hLK htwo
  obtain ⟨hleft, hright, hcover⟩ :=
    large_good_block_covers_row
      a N C B L T Dmin top left dI jG kG D
      hinput hzero hL hC hBC hvalid
      hDmin hBmin hbottom htriangle
      (le_trans hdI hH) hDminD
      (by simpa [right0] using hgood)
      (by simpa [K] using hKk)
  exact ⟨dI, jG, kG, D, hdI, hDminD, hDB,
    by simpa [right0] using hgood,
    by simpa [K] using hKk,
    hleft, hright, hcover⟩

end Gilbreath

-- END GilbreathTriangleLargeGood_20260925.lean


-- BEGIN GilbreathFiniteCriterionProof_20260925.lean

namespace Gilbreath

/-- The published finite deterministic criterion, assembled from
scale selection, coarse monotonicity, the direct tower argument,
and the large-good-block covering theorem. -/
theorem finite_deterministic_criterion_proved :
    FiniteDeterministicCriterion := by
  intro a N N' M L R hbounds hinput hzero hnoTwo
  by_contra hnot
  have hbottom : 1 < iterAbsDiff a (N - 1) 0 := by
    omega
  obtain ⟨m, j, hm, hmM, hj, hvalid,
    hhigh, htriangleRaw⟩ :=
    finite_criterion_locates_large_triangle
      a N N' M L R hbounds hinput hzero hbottom
  obtain ⟨hN', hNN, hM, hL, hRzero, hinc,
    hterminal, hscale, hlarge⟩ := hbounds
  let C := 2 ^ M
  let B := 2 ^ (M - m + 1)
  let H := R (m - 1)
  let T := R m - H
  let Dmin := iterAbsDiff a (R m) j
  have hC : 1 ≤ C := by dsimp [C]; exact Nat.one_le_pow _ _ (by omega)
  have hBC : B ≤ C := by
    dsimp [B, C]
    have hexp : M - m + 1 ≤ M := by omega
    gcongr <;> omega
  have hBtwice : B = 2 * 2 ^ (M - m) := by
    dsimp [B]
    simp [pow_succ, Nat.mul_comm]
  have hDmin : 1 ≤ Dmin := by
    dsimp [Dmin]
    have hpow : 1 ≤ (2 : ℕ) ^ (M - m) := by
      exact Nat.one_le_pow _ _ (by omega)
    omega
  have hBmin : B < 2 * Dmin := by
    dsimp [Dmin] at *
    omega
  have hHfour : 4 * H ≤ R m := by
    dsimp [H]
    exact hscale m hm hmM
  have hH : H ≤ T := by
    dsimp [T]
    omega
  have hTopBottom : H + T = R m := by
    dsimp [T]
    omega
  have hvalidTriangle : H + T + j < N := by omega
  have htriangle :
      ∀ d, d ≤ T → ∀ x, j ≤ x →
        x < j + (T - d) + 1 →
          iterAbsDiff a (H + d) x ≤ B := by
    intro d hd x hx hxright
    have hdo : d + (x - j) ≤ T := by omega
    have hindex : j + (x - j) = x := by omega
    have hv := htriangleRaw d (x - j) hdo
    simpa only [H, T, B, hindex] using hv
  have hR0 : ∀ n, n ≤ M → R 0 ≤ R n := by
    intro n hn
    induction n with
    | zero => exact le_refl _
    | succ n ih =>
        exact le_trans (ih (by omega))
          (le_of_lt (hinc n (by omega)))
  have hpowCube : C * C * C = 8 ^ M := by
    dsimp [C]
    calc
      2 ^ M * 2 ^ M * 2 ^ M = (2 * 2 * 2) ^ M := by
        simp only [mul_pow]
      _ = 8 ^ M := by norm_num
  have hroom : (100 * L * C * C) * C ≤ H := by
    have hpowEq :
        (100 * L * C * C) * C =
          100 * L * 8 ^ M := by
      calc
        _ = 100 * L * (C * C * C) := by ring
        _ = 100 * L * 8 ^ M := by rw [hpowCube]
    rw [hpowEq]
    exact le_trans hlarge (hR0 (m - 1) (by omega))
  have hC2 : 1 ≤ C * C := by nlinarith
  have hC3 : C ≤ C * C * C := by
    have hm := Nat.mul_le_mul_left C hC2
    nlinarith
  have hMargin : 16 * (C * (L + 1)) ≤ H := by
    have hL2 : L + 1 ≤ 2 * L := by omega
    have ha := Nat.mul_le_mul_left C hL2
    have hb := Nat.mul_le_mul_right (2 * L) hC3
    have hc :
        16 * (C * (L + 1)) ≤
          100 * L * C * C * C := by
      nlinarith
    omega
  obtain ⟨dI, jG, kG, D, hdI, hDminD, hDB,
    hgood, hK, hleft, hright, hcover⟩ :=
    bounded_triangle_has_large_good_block
      a N C B L H T j Dmin H
      hinput hzero hL hC hBC hBmin
      hvalidTriangle hDmin
      (by simpa only [hTopBottom, Dmin] using rfl)
      htriangle hH hroom
  have hgoodLeft : j ≤ jG := hgood.1
  have hgoodRight :
      jG + kG ≤ j + (T - dI) + 1 := hgood.2.1
  have hdepthShallow : H + dI ≤ 2 * H := by omega
  have hlengthStrong : R m + 1 ≤ kG + 3 * H := by
    omega
  have hkpos : 1 ≤ kG := by omega
  have hlengthFinal : R m ≤ (kG - 1) + 3 * H := by
    omega
  have hlocation : N' ≤ jG + 1 := by omega
  have hvalidBlock :
      jG + (H + dI) + (kG - 1) + 1 ≤ N := by
    omega
  apply hnoTwo
  refine ⟨m, D, H + dI, kG - 1, jG,
    hm, hmM, ?_, ?_, hdepthShallow,
    ?_, hlocation, hvalidBlock, ?_⟩
  · dsimp [Dmin] at hDminD
    exact lt_of_lt_of_le hhigh hDminD
  · simpa only [B] using hDB
  · simpa only [H] using hlengthFinal
  · intro t ht
    exact hgood.2.2.2.1 t (by omega)

end Gilbreath

-- END GilbreathFiniteCriterionProof_20260925.lean


open Gilbreath

theorem solution
    (a : ℕ → ℕ) (N N' M L : ℕ) (R : ℕ → ℕ)
    (hbounds :
      1 ≤ N' ∧ N' ≤ N ∧ 1 ≤ M ∧ 1 ≤ L ∧
      1 < R 0 ∧
      (∀ m, m < M → R m < R (m + 1)) ∧
      2 * R M + N' < N ∧
      (∀ m, 1 ≤ m → m ≤ M → 4 * R (m - 1) ≤ R m) ∧
      100 * L * 8 ^ M ≤ R 0)
    (hinput : ∀ j < N, a j ≤ 2 ^ M)
    (hzero : ¬ ∃ i j : ℕ,
      i + L ≤ N ∧ j + i + L ≤ N ∧
      ∀ t < L, iterAbsDiff a i (j + t) = 0)
    (htwo : ¬ ∃ m d i k j : ℕ,
      1 ≤ m ∧ m ≤ M ∧
      2 ^ (M - m) < d ∧ d ≤ 2 ^ (M - m + 1) ∧
      i ≤ 2 * R (m - 1) ∧
      R m ≤ k + 3 * R (m - 1) ∧
      N' ≤ j + 1 ∧ j + i + k + 1 ≤ N ∧
      ∀ t < k, iterAbsDiff a i (j + t) = 0 ∨
        iterAbsDiff a i (j + t) = d) :
    iterAbsDiff a (N - 1) 0 = 0 ∨
      iterAbsDiff a (N - 1) 0 = 1 := by
  exact Gilbreath.finite_deterministic_criterion_proved a N N' M L R hbounds hinput hzero htwo


