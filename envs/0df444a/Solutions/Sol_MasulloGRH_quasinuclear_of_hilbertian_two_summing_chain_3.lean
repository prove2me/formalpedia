-- Prove2me | solution 3 for MasulloGRH.quasinuclear_of_hilbertian_two_summing_chain
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-20T23:35:45.275983+00:00
-- url     : https://prove2.me/submissions/211315e5-126b-422d-ab56-28e9f522ff5c

import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false

open MasulloGRH Set Filter Topology Finset

universe u

namespace HilbertChain

/-! ### Part I: lemmas in a (semi-definite) inner product space -/

section IPS

variable {F : Type*} [SeminormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- Pythagoras for a finite orthogonal family. -/
theorem norm_sq_sum_orth (u : ℕ → F) (horth : ∀ i j, i ≠ j → inner ℂ (u i) (u j) = 0)
    (c : ℕ → ℂ) (N : ℕ) :
    ‖∑ i ∈ range N, c i • u i‖ ^ 2 = ∑ i ∈ range N, ‖c i‖ ^ 2 * ‖u i‖ ^ 2 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ, sum_range_succ, ← ih]
    have h0 : inner ℂ (∑ i ∈ range N, c i • u i) (c N • u N) = 0 := by
      rw [sum_inner]
      refine sum_eq_zero fun i hi => ?_
      rw [inner_smul_left, inner_smul_right, horth i N (mem_range.1 hi).ne]
      simp
    rw [@norm_add_sq ℂ, h0]
    simp [norm_smul, mul_pow]

/-- **Bessel's inequality for a bounded functional**: if `|g| ≤ C ‖·‖` and `u` is an orthogonal
family of vectors of norm at most one, then `∑ |g (u i)|² ≤ C²`. -/
theorem bessel_functional (g : F →ₗ[ℂ] ℂ) (C : ℝ) (hg : ∀ y, ‖g y‖ ≤ C * ‖y‖)
    (u : ℕ → F) (horth : ∀ i j, i ≠ j → inner ℂ (u i) (u j) = 0) (hn : ∀ i, ‖u i‖ ≤ 1)
    (N : ℕ) : ∑ i ∈ range N, ‖g (u i)‖ ^ 2 ≤ C ^ 2 := by
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = ∑ i ∈ range N, ‖g (u i)‖ ^ 2 := ⟨_, rfl⟩
  rw [← hA]
  have hA0 : 0 ≤ A := by rw [hA]; exact sum_nonneg fun i _ => by positivity
  obtain ⟨y, hy⟩ : ∃ y : F, y = ∑ i ∈ range N, (starRingEnd ℂ) (g (u i)) • u i := ⟨_, rfl⟩
  have hgy : g y = (A : ℂ) := by
    rw [hy, map_sum, hA]
    push_cast
    refine sum_congr rfl fun i _ => ?_
    rw [map_smul, smul_eq_mul, Complex.conj_mul']
  have hny : ‖y‖ ^ 2 ≤ A := by
    rw [hy, norm_sq_sum_orth u horth, hA]
    refine sum_le_sum fun i _ => ?_
    rw [RCLike.norm_conj]
    calc ‖g (u i)‖ ^ 2 * ‖u i‖ ^ 2 ≤ ‖g (u i)‖ ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left (pow_le_one₀ (norm_nonneg _) (hn i)) (by positivity)
      _ = ‖g (u i)‖ ^ 2 := mul_one _
  have h1 : A ≤ C * ‖y‖ := by
    have := hg y
    rwa [hgy, Complex.norm_real, Real.norm_of_nonneg hA0] at this
  have h2 : A * A ≤ C ^ 2 * A := by
    calc A * A = A ^ 2 := (sq A).symm
      _ ≤ (C * ‖y‖) ^ 2 := pow_le_pow_left₀ hA0 h1 2
      _ = C ^ 2 * ‖y‖ ^ 2 := by ring
      _ ≤ C ^ 2 * A := mul_le_mul_of_nonneg_left hny (by positivity)
  by_cases hA' : A = 0
  · rw [hA']; positivity
  · exact le_of_mul_le_mul_right h2 (lt_of_le_of_ne hA0 (Ne.symm hA'))

/-- Bessel's inequality. -/
theorem bessel (u : ℕ → F) (horth : ∀ i j, i ≠ j → inner ℂ (u i) (u j) = 0)
    (hn : ∀ i, ‖u i‖ ≤ 1) (x : F) (N : ℕ) :
    ∑ i ∈ range N, ‖inner ℂ (u i) x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
  let g : F →ₗ[ℂ] ℂ :=
    { toFun := fun y => inner ℂ x y
      map_add' := fun a b => inner_add_right x a b
      map_smul' := fun c a => by simp [inner_smul_right] }
  have h := bessel_functional g ‖x‖ (fun y => norm_inner_le_norm x y) u horth hn N
  have e : ∀ i, ‖inner ℂ (u i) x‖ = ‖g (u i)‖ := fun i => norm_inner_symm _ _
  simp only [e]
  exact h

/-- The remainder of the orthogonal expansion is orthogonal to the first `N` vectors. -/
theorem inner_tail (u : ℕ → F) (horth : ∀ i j, i ≠ j → inner ℂ (u i) (u j) = 0)
    (hunit : ∀ k, u k = 0 ∨ ‖u k‖ = 1) (x : F) (N i : ℕ) (hi : i < N) :
    inner ℂ (u i) (x - ∑ k ∈ range N, inner ℂ (u k) x • u k) = 0 := by
  rw [inner_sub_right, inner_sum]
  have h1 : ∑ k ∈ range N, inner ℂ (u i) (inner ℂ (u k) x • u k) =
      inner ℂ (u i) x * inner ℂ (u i) (u i) := by
    rw [sum_eq_single i]
    · rw [inner_smul_right]
    · intro k _ hk
      rw [inner_smul_right, horth i k (Ne.symm hk), mul_zero]
    · intro h
      exact absurd (mem_range.2 hi) h
  rw [h1]
  rcases hunit i with h0 | h1'
  · simp [h0]
  · rw [inner_self_eq_norm_sq_to_K, h1']
    simp

/-- The remainder of the orthogonal expansion has norm at most `‖x‖`. -/
theorem norm_tail_le (u : ℕ → F) (horth : ∀ i j, i ≠ j → inner ℂ (u i) (u j) = 0)
    (hunit : ∀ k, u k = 0 ∨ ‖u k‖ = 1) (x : F) (N : ℕ) :
    ‖x - ∑ k ∈ range N, inner ℂ (u k) x • u k‖ ≤ ‖x‖ := by
  obtain ⟨P, hP⟩ : ∃ P : F, P = ∑ k ∈ range N, inner ℂ (u k) x • u k := ⟨_, rfl⟩
  rw [← hP]
  have h0' : inner ℂ (x - P) (∑ k ∈ range N, inner ℂ (u k) x • u k) = 0 := by
    rw [inner_sum]
    refine sum_eq_zero fun k hk => ?_
    have := inner_tail u horth hunit x N k (mem_range.1 hk)
    rw [← hP] at this
    rw [inner_smul_right, inner_eq_zero_symm.1 this, mul_zero]
  have h0 : inner ℂ (x - P) P = 0 := by rw [← hP] at h0'; exact h0'
  have h1 : ‖x‖ ^ 2 = ‖x - P‖ ^ 2 + ‖P‖ ^ 2 := by
    have h2 := @norm_add_sq ℂ F _ _ _ (x - P) P
    rw [sub_add_cancel, h0] at h2
    simpa using h2
  have h3 : ‖x - P‖ ^ 2 ≤ ‖x‖ ^ 2 := by nlinarith [sq_nonneg ‖P‖]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h3

/-- **Greedy orthonormal sequence.**  Let `h` be a seminorm dominated by the norm which is
Hilbert–Schmidt in the sense that `∑ h (e i)² ≤ 1` on finite orthogonal families of vectors of norm
at most one.  Then there is an orthogonal sequence `u` of unit-or-zero vectors such that the
remainders of the orthogonal expansion of every vector tend to `0` for `h`. -/
theorem greedy (h : Seminorm ℂ F) (hle : ∀ x, h x ≤ ‖x‖)
    (HS : ∀ (e : ℕ → F) (N : ℕ), (∀ i j, i ≠ j → inner ℂ (e i) (e j) = 0) → (∀ i, ‖e i‖ ≤ 1) →
      ∑ i ∈ range N, h (e i) ^ 2 ≤ 1) :
    ∃ u : ℕ → F, (∀ k, u k = 0 ∨ ‖u k‖ = 1) ∧ (∀ i j, i ≠ j → inner ℂ (u i) (u j) = 0) ∧
      ∀ x, Tendsto (fun N => h (x - ∑ k ∈ range N, inner ℂ (u k) x • u k)) atTop (𝓝 0) := by
  -- one greedy step: a near-maximiser of `h` among unit vectors orthogonal to a finite list
  have step : ∀ L : List F, ∃ w : F, (w = 0 ∨ ‖w‖ = 1) ∧ (∀ v ∈ L, inner ℂ v w = 0) ∧
      ∀ z : F, ‖z‖ = 1 → (∀ v ∈ L, inner ℂ v z = 0) → h z ^ 2 ≤ 2 * h w ^ 2 := by
    intro L
    by_cases hex : ∃ z : F, ‖z‖ = 1 ∧ (∀ v ∈ L, inner ℂ v z = 0) ∧ 0 < h z
    · obtain ⟨z0, hz0n, hz0o, hz0p⟩ := hex
      let S : Set ℝ := {t | ∃ z : F, ‖z‖ = 1 ∧ (∀ v ∈ L, inner ℂ v z = 0) ∧ t = h z ^ 2}
      have hbdd : BddAbove S := ⟨1, by
        rintro _ ⟨z, hz, -, rfl⟩
        have := hle z
        rw [hz] at this
        exact pow_le_one₀ (apply_nonneg h z) this⟩
      have hmem0 : h z0 ^ 2 ∈ S := ⟨z0, hz0n, hz0o, rfl⟩
      have hm : 0 < sSup S := lt_of_lt_of_le (by positivity) (le_csSup hbdd hmem0)
      obtain ⟨t, ⟨w, hwn, hwo, rfl⟩, ht⟩ := exists_lt_of_lt_csSup ⟨_, hmem0⟩ (half_lt_self hm)
      refine ⟨w, Or.inr hwn, hwo, fun z hz hzo => ?_⟩
      have := le_csSup hbdd (⟨z, hz, hzo, rfl⟩ : h z ^ 2 ∈ S)
      linarith
    · refine ⟨0, Or.inl rfl, fun v _ => inner_zero_right v, fun z hz hzo => ?_⟩
      have hz0 : h z ≤ 0 := by
        by_contra hc
        exact hex ⟨z, hz, hzo, not_le.1 hc⟩
      have hz1 : h z = 0 := le_antisymm hz0 (apply_nonneg h z)
      simp [hz1]
  choose step hstep using step
  obtain ⟨L, hL0, hLs⟩ : ∃ L : ℕ → List F, L 0 = [] ∧ ∀ n, L (n + 1) = step (L n) :: L n :=
    ⟨fun n => Nat.rec [] (fun _ l => step l :: l) n, rfl, fun _ => rfl⟩
  obtain ⟨u, hu⟩ : ∃ u : ℕ → F, ∀ n, u n = step (L n) := ⟨_, fun _ => rfl⟩
  have hmemL : ∀ n v, v ∈ L n ↔ ∃ k < n, v = u k := by
    intro n
    induction n with
    | zero => intro v; simp [hL0]
    | succ n ih =>
      intro v
      rw [hLs, List.mem_cons, ih, ← hu]
      constructor
      · rintro (rfl | ⟨k, hk, rfl⟩)
        · exact ⟨n, Nat.lt_succ_self n, rfl⟩
        · exact ⟨k, Nat.lt_succ_of_lt hk, rfl⟩
      · rintro ⟨k, hk, rfl⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hk with h' | rfl
        · exact Or.inr ⟨k, h', rfl⟩
        · exact Or.inl rfl
  have hunit : ∀ k, u k = 0 ∨ ‖u k‖ = 1 := fun k => by rw [hu]; exact (hstep _).1
  have hlt : ∀ i j, i < j → inner ℂ (u i) (u j) = 0 := fun i j hij => by
    have := (hstep (L j)).2.1 (u i) ((hmemL j _).2 ⟨i, hij, rfl⟩)
    rwa [← hu] at this
  have horth : ∀ i j, i ≠ j → inner ℂ (u i) (u j) = 0 := by
    intro i j hij
    rcases lt_or_gt_of_ne hij with h' | h'
    · exact hlt i j h'
    · exact inner_eq_zero_symm.1 (hlt j i h')
  have hgreedy : ∀ N z, ‖z‖ = 1 → (∀ k < N, inner ℂ (u k) z = 0) →
      h z ^ 2 ≤ 2 * h (u N) ^ 2 := by
    intro N z hz ho
    rw [hu N]
    refine (hstep (L N)).2.2 z hz fun v hv => ?_
    obtain ⟨k, hk, rfl⟩ := (hmemL N v).1 hv
    exact ho k hk
  have hnorm : ∀ k, ‖u k‖ ≤ 1 := fun k => by rcases hunit k with h' | h' <;> simp [h']
  have hsum : Summable fun k => h (u k) ^ 2 :=
    summable_of_sum_range_le (fun k => by positivity) (fun N => HS u N horth hnorm)
  have hlim : Tendsto (fun k => h (u k)) atTop (𝓝 0) := by
    have h2 := (Real.continuous_sqrt.tendsto 0).comp hsum.tendsto_atTop_zero
    simpa [Function.comp_def, Real.sqrt_sq (apply_nonneg h _)] using h2
  refine ⟨u, hunit, horth, fun x => ?_⟩
  have hbound : ∀ N, h (x - ∑ k ∈ range N, inner ℂ (u k) x • u k) ≤ 2 * h (u N) * ‖x‖ := by
    intro N
    obtain ⟨r, hr⟩ : ∃ r : F, r = x - ∑ k ∈ range N, inner ℂ (u k) x • u k := ⟨_, rfl⟩
    rw [← hr]
    have hrn : ‖r‖ ≤ ‖x‖ := by rw [hr]; exact norm_tail_le u horth hunit x N
    have hro : ∀ k < N, inner ℂ (u k) r = 0 := fun k hk => by
      rw [hr]; exact inner_tail u horth hunit x N k hk
    by_cases h0 : ‖r‖ = 0
    · have h1 : h r ≤ 0 := h0 ▸ hle r
      exact h1.trans (by positivity)
    · have hpos : 0 < ‖r‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
      obtain ⟨z, hzdef⟩ : ∃ z : F, z = ((‖r‖⁻¹ : ℝ) : ℂ) • r := ⟨_, rfl⟩
      have hz : ‖z‖ = 1 := by
        rw [hzdef, norm_smul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.2 hpos.le),
          inv_mul_cancel₀ h0]
      have hzo : ∀ k < N, inner ℂ (u k) z = 0 := fun k hk => by
        rw [hzdef, inner_smul_right, hro k hk, mul_zero]
      have hg := hgreedy N z hz hzo
      have hhz : h z = ‖r‖⁻¹ * h r := by
        rw [hzdef, map_smul_eq_mul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.2 hpos.le)]
      have hr' : h r = ‖r‖ * h z := by rw [hhz, ← mul_assoc, mul_inv_cancel₀ h0, one_mul]
      have hz2 : h z ≤ 2 * h (u N) := by
        have h3 : h z ^ 2 ≤ (2 * h (u N)) ^ 2 := by nlinarith [sq_nonneg (h (u N))]
        exact (pow_le_pow_iff_left₀ (apply_nonneg h z) (by positivity) two_ne_zero).1 h3
      rw [hr']
      calc ‖r‖ * h z ≤ ‖x‖ * (2 * h (u N)) :=
            mul_le_mul hrn hz2 (apply_nonneg h z) (norm_nonneg x)
        _ = 2 * h (u N) * ‖x‖ := by ring
  refine squeeze_zero (fun N => apply_nonneg h _) hbound ?_
  have h4 := (hlim.const_mul 2).mul_const ‖x‖
  simpa using h4

end IPS

/-! ### Part II: seminorms satisfying the parallelogram law -/

section Forms

variable {E : Type u} [AddCommGroup E] [Module ℂ E]

/-- **Jordan–von Neumann** for seminorms: a seminorm satisfying the parallelogram law comes from a
positive semi-definite Hermitian form. -/
theorem core_of_parallelogram (H : Seminorm ℂ E)
    (hpar : ∀ x y, H (x + y) ^ 2 + H (x - y) ^ 2 = 2 * H x ^ 2 + 2 * H y ^ 2) :
    ∃ c : PreInnerProductSpace.Core ℂ E, ∀ x, (c.inner x x).re = H x ^ 2 := by
  let _ : SeminormedAddCommGroup E := H.toAddGroupSeminorm.toSeminormedAddCommGroup
  have hnorm : ∀ x : E, ‖x‖ = H x := fun _ => rfl
  let _ : NormedSpace ℂ E :=
    { ‹Module ℂ E› with norm_smul_le := fun c x => le_of_eq (map_smul_eq_mul H c x) }
  have hparQ : ∀ X Y : SeparationQuotient E,
      ‖X + Y‖ * ‖X + Y‖ + ‖X - Y‖ * ‖X - Y‖ = 2 * (‖X‖ * ‖X‖ + ‖Y‖ * ‖Y‖) := by
    intro X Y
    obtain ⟨x, rfl⟩ := SeparationQuotient.surjective_mk X
    obtain ⟨y, rfl⟩ := SeparationQuotient.surjective_mk Y
    rw [← SeparationQuotient.mk_add, ← SeparationQuotient.mk_sub]
    simp only [SeparationQuotient.norm_mk, hnorm]
    have := hpar x y
    nlinarith [this]
  let _ : InnerProductSpace ℂ (SeparationQuotient E) := InnerProductSpace.ofNorm ℂ hparQ
  refine ⟨{ inner := fun x y => inner ℂ (SeparationQuotient.mk x) (SeparationQuotient.mk y)
            conj_inner_symm := fun x y => inner_conj_symm _ _
            re_inner_nonneg := fun x => inner_self_nonneg
            add_left := fun x y z => by
              rw [SeparationQuotient.mk_add, inner_add_left]
            smul_left := fun x y r => by
              rw [SeparationQuotient.mk_smul, inner_smul_left] }, fun x => ?_⟩
  change (inner ℂ (SeparationQuotient.mk x) (SeparationQuotient.mk x)).re = H x ^ 2
  have h1 := @inner_self_eq_norm_sq ℂ (SeparationQuotient E) _ _ _ (SeparationQuotient.mk x)
  rw [SeparationQuotient.norm_mk, hnorm] at h1
  exact h1

/-- **One level of the chain.**  `H` is a Hilbertian seminorm, `h ≤ H` is a seminorm which is
`2`-summing with respect to the functionals dominated by `H`.  Then there are vectors `u k` and
functionals `g k` (the coordinates of an orthogonal expansion for `H`) with: `|g k| ≤ H`, the
remainders of the expansion tend to `0` for `h`, `∑ h (u k)² ≤ 1`, and Bessel's inequality. -/
theorem level (h H : Seminorm ℂ E)
    (hpar : ∀ x y, H (x + y) ^ 2 + H (x - y) ^ 2 = 2 * H x ^ 2 + 2 * H y ^ 2)
    (hle : ∀ x, h x ≤ H x)
    (hHS : ∀ (e : ℕ → E) (N : ℕ),
      (∀ g : E →ₗ[ℂ] ℂ, (∀ y, ‖g y‖ ≤ H y) → ∑ i ∈ range N, ‖g (e i)‖ ^ 2 ≤ 1) →
      ∑ i ∈ range N, h (e i) ^ 2 ≤ 1) :
    ∃ (u : ℕ → E) (g : ℕ → E →ₗ[ℂ] ℂ),
      (∀ k x, ‖g k x‖ ≤ H x) ∧
      (∀ x, Tendsto (fun N => h (x - ∑ k ∈ range N, g k x • u k)) atTop (𝓝 0)) ∧
      (∀ N, ∑ k ∈ range N, h (u k) ^ 2 ≤ 1) ∧
      (∀ y N, ∑ k ∈ range N, ‖g k y‖ ^ 2 ≤ H y ^ 2) := by
  obtain ⟨c, hc⟩ := core_of_parallelogram H hpar
  let _ : SeminormedAddCommGroup E := InnerProductSpace.Core.toSeminormedAddCommGroup (c := c)
  let _ : InnerProductSpace ℂ E := InnerProductSpace.ofCore c
  have hnorm : ∀ x : E, ‖x‖ = H x := by
    intro x
    have h1 : ‖x‖ ^ 2 = H x ^ 2 := by
      rw [← hc x]
      exact norm_sq_eq_re_inner (𝕜 := ℂ) x
    exact (pow_left_inj₀ (norm_nonneg x) (apply_nonneg H x) two_ne_zero).1 h1
  have hle' : ∀ x, h x ≤ ‖x‖ := fun x => by rw [hnorm]; exact hle x
  have HS : ∀ (e : ℕ → E) (N : ℕ), (∀ i j, i ≠ j → inner ℂ (e i) (e j) = 0) →
      (∀ i, ‖e i‖ ≤ 1) → ∑ i ∈ range N, h (e i) ^ 2 ≤ 1 := by
    intro e N horth hn
    refine hHS e N fun g hg => ?_
    have := bessel_functional g 1 (fun y => by rw [one_mul, hnorm]; exact hg y) e horth hn N
    simpa using this
  obtain ⟨u, hunit, horth, htail⟩ := greedy h hle' HS
  have hn : ∀ k, ‖u k‖ ≤ 1 := fun k => by rcases hunit k with h' | h' <;> simp [h']
  let g : ℕ → E →ₗ[ℂ] ℂ := fun k =>
    { toFun := fun y => inner ℂ (u k) y
      map_add' := fun a b => inner_add_right (u k) a b
      map_smul' := fun r a => by simp [inner_smul_right] }
  have hg : ∀ k y, g k y = inner ℂ (u k) y := fun _ _ => rfl
  refine ⟨u, g, fun k x => ?_, fun x => ?_, fun N => HS u N horth hn, fun y N => ?_⟩
  · rw [hg, ← hnorm]
    calc ‖inner ℂ (u k) x‖ ≤ ‖u k‖ * ‖x‖ := norm_inner_le_norm _ _
      _ ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right (hn k) (norm_nonneg x)
      _ = ‖x‖ := one_mul _
  · exact htail x
  · rw [← hnorm]
    exact bessel u horth hn y N

/-! ### Part III: composing two levels -/

theorem seminorm_sum_le (h : Seminorm ℂ E) (f : ℕ → E) (N : ℕ) :
    h (∑ k ∈ range N, f k) ≤ ∑ k ∈ range N, h (f k) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ, sum_range_succ]
    exact (map_add_le_add h _ _).trans (add_le_add ih le_rfl)

/-- **Two Hilbert–Schmidt steps give an `ℓ¹` domination.** -/
theorem chain (h₁ h₂ h₃ : Seminorm ℂ E)
    (u : ℕ → E) (g : ℕ → E →ₗ[ℂ] ℂ)
    (ha : ∀ k x, ‖g k x‖ ≤ h₂ x)
    (hb : ∀ x, Tendsto (fun N => h₁ (x - ∑ k ∈ range N, g k x • u k)) atTop (𝓝 0))
    (hc : ∀ N, ∑ k ∈ range N, h₁ (u k) ^ 2 ≤ 1)
    (hd : ∀ y N, ∑ k ∈ range N, ‖g k y‖ ^ 2 ≤ h₂ y ^ 2)
    (v : ℕ → E) (γ : ℕ → E →ₗ[ℂ] ℂ)
    (hb' : ∀ x, Tendsto (fun N => h₂ (x - ∑ j ∈ range N, γ j x • v j)) atTop (𝓝 0))
    (hc' : ∀ N, ∑ j ∈ range N, h₂ (v j) ^ 2 ≤ 1)
    (hd' : ∀ y N, ∑ j ∈ range N, ‖γ j y‖ ^ 2 ≤ h₃ y ^ 2) :
    ∃ (f : ℕ → E →ₗ[ℂ] ℂ) (c : ℕ → ℝ),
      (∀ n, 0 ≤ c n) ∧ Summable c ∧ (∀ n x, ‖f n x‖ ≤ h₃ x) ∧
      ∀ x, h₁ x ≤ ∑' n, c n * ‖f n x‖ := by
  -- the matrix coefficients `|g k (v j)|²`
  have hsv : Summable fun j => h₂ (v j) ^ 2 :=
    summable_of_sum_range_le (fun j => by positivity) hc'
  have hsv1 : ∑' j, h₂ (v j) ^ 2 ≤ 1 :=
    Real.tsum_le_of_sum_range_le (fun j => by positivity) hc'
  have hak : ∀ k j, ‖g k (v j)‖ ^ 2 ≤ h₂ (v j) ^ 2 := fun k j =>
    pow_le_pow_left₀ (norm_nonneg _) (ha k (v j)) 2
  have hsa : ∀ k, Summable fun j => ‖g k (v j)‖ ^ 2 := fun k =>
    Summable.of_nonneg_of_le (fun j => by positivity) (hak k) hsv
  obtain ⟨D, hD⟩ : ∃ D : ℕ → ℝ, ∀ k, D k = Real.sqrt (∑' j, ‖g k (v j)‖ ^ 2) := ⟨_, fun _ => rfl⟩
  have hD0 : ∀ k, 0 ≤ D k := fun k => by rw [hD]; exact Real.sqrt_nonneg _
  have hDsq : ∀ k, D k ^ 2 = ∑' j, ‖g k (v j)‖ ^ 2 := fun k => by
    rw [hD, Real.sq_sqrt (tsum_nonneg fun j => by positivity)]
  -- (S2) the functional `g k` has norm at most `D k` with respect to `h₃`
  have hS2 : ∀ k x, ‖g k x‖ ≤ h₃ x * D k := by
    intro k x
    have hN : ∀ N, ‖g k x‖ ≤ h₃ x * D k + h₂ (x - ∑ j ∈ range N, γ j x • v j) := by
      intro N
      have hx : g k x = ∑ j ∈ range N, γ j x * g k (v j) +
          g k (x - ∑ j ∈ range N, γ j x • v j) := by
        rw [map_sub, map_sum]
        simp only [map_smul, smul_eq_mul]
        ring
      have h1 : ‖∑ j ∈ range N, γ j x * g k (v j)‖ ≤
          ∑ j ∈ range N, ‖γ j x‖ * ‖g k (v j)‖ :=
        (norm_sum_le _ _).trans (le_of_eq (sum_congr rfl fun j _ => norm_mul _ _))
      have h2 : (∑ j ∈ range N, ‖γ j x‖ * ‖g k (v j)‖) ^ 2 ≤ (h₃ x * D k) ^ 2 := by
        calc (∑ j ∈ range N, ‖γ j x‖ * ‖g k (v j)‖) ^ 2
            ≤ (∑ j ∈ range N, ‖γ j x‖ ^ 2) * ∑ j ∈ range N, ‖g k (v j)‖ ^ 2 :=
              sum_mul_sq_le_sq_mul_sq _ _ _
          _ ≤ h₃ x ^ 2 * D k ^ 2 := by
              refine mul_le_mul (hd' x N) ?_ (sum_nonneg fun j _ => by positivity) (by positivity)
              rw [hDsq]
              exact (hsa k).sum_le_tsum _ fun j _ => by positivity
          _ = (h₃ x * D k) ^ 2 := by ring
      have h3 : ∑ j ∈ range N, ‖γ j x‖ * ‖g k (v j)‖ ≤ h₃ x * D k :=
        (pow_le_pow_iff_left₀ (sum_nonneg fun j _ => by positivity)
          (mul_nonneg (apply_nonneg h₃ x) (hD0 k)) two_ne_zero).1 h2
      calc ‖g k x‖ = ‖∑ j ∈ range N, γ j x * g k (v j) +
              g k (x - ∑ j ∈ range N, γ j x • v j)‖ := by rw [← hx]
        _ ≤ ‖∑ j ∈ range N, γ j x * g k (v j)‖ +
              ‖g k (x - ∑ j ∈ range N, γ j x • v j)‖ := norm_add_le _ _
        _ ≤ h₃ x * D k + h₂ (x - ∑ j ∈ range N, γ j x • v j) :=
              add_le_add (h1.trans h3) (ha k _)
    have hlim : Tendsto (fun N => h₃ x * D k + h₂ (x - ∑ j ∈ range N, γ j x • v j)) atTop
        (𝓝 (h₃ x * D k + 0)) := tendsto_const_nhds.add (hb' x)
    rw [add_zero] at hlim
    exact ge_of_tendsto' hlim hN
  -- (S3) `∑ D k² ≤ 1`
  have hS3 : ∀ M, ∑ k ∈ range M, D k ^ 2 ≤ 1 := by
    intro M
    simp only [hDsq]
    rw [← Summable.tsum_finsetSum fun k _ => hsa k]
    refine le_trans ?_ hsv1
    refine Summable.tsum_le_tsum (fun j => hd (v j) M) ?_ hsv
    exact summable_sum fun k _ => hsa k
  have hsD : Summable fun k => D k ^ 2 :=
    summable_of_sum_range_le (fun k => by positivity) hS3
  have hsu : Summable fun k => h₁ (u k) ^ 2 :=
    summable_of_sum_range_le (fun k => by positivity) hc
  -- the coefficients and the normalised functionals
  refine ⟨fun k => (((D k)⁻¹ : ℝ) : ℂ) • g k, fun k => h₁ (u k) * D k,
    fun k => mul_nonneg (apply_nonneg h₁ _) (hD0 k), ?_, fun k x => ?_, fun x => ?_⟩
  · refine Summable.of_nonneg_of_le (fun k => mul_nonneg (apply_nonneg h₁ _) (hD0 k))
      (fun k => ?_) ((hsu.add hsD).mul_left (1 / 2))
    nlinarith [sq_nonneg (h₁ (u k) - D k)]
  · have h1 : ‖((((D k)⁻¹ : ℝ) : ℂ) • g k) x‖ = (D k)⁻¹ * ‖g k x‖ := by
      rw [LinearMap.smul_apply, norm_smul, Complex.norm_real,
        Real.norm_of_nonneg (inv_nonneg.2 (hD0 k))]
    rw [h1]
    by_cases hDk : D k = 0
    · rw [hDk, inv_zero, zero_mul]; exact apply_nonneg h₃ x
    · have hpos : 0 < D k := lt_of_le_of_ne (hD0 k) (Ne.symm hDk)
      rw [inv_mul_le_iff₀ hpos, mul_comm]
      exact hS2 k x
  · have hterm : ∀ k, h₁ (u k) * D k * ‖((((D k)⁻¹ : ℝ) : ℂ) • g k) x‖ =
        ‖g k x‖ * h₁ (u k) := by
      intro k
      have h1 : ‖((((D k)⁻¹ : ℝ) : ℂ) • g k) x‖ = (D k)⁻¹ * ‖g k x‖ := by
        rw [LinearMap.smul_apply, norm_smul, Complex.norm_real,
          Real.norm_of_nonneg (inv_nonneg.2 (hD0 k))]
      rw [h1]
      by_cases hDk : D k = 0
      · have h2 : ‖g k x‖ = 0 := by
          have := hS2 k x
          rw [hDk, mul_zero] at this
          exact le_antisymm this (norm_nonneg _)
        rw [hDk, h2]; ring
      · field_simp
    simp only [hterm]
    have hsx : Summable fun k => ‖g k x‖ * h₁ (u k) := by
      refine Summable.of_nonneg_of_le (fun k => mul_nonneg (norm_nonneg _) (apply_nonneg h₁ _))
        (fun k => ?_) ((hsu.add hsD).mul_left (h₃ x))
      have h2 := hS2 k x
      have h3 : ‖g k x‖ * h₁ (u k) ≤ h₃ x * D k * h₁ (u k) :=
        mul_le_mul_of_nonneg_right h2 (apply_nonneg h₁ _)
      have h4 : D k * h₁ (u k) ≤ h₁ (u k) ^ 2 + D k ^ 2 := by
        nlinarith [sq_nonneg (h₁ (u k) - D k), sq_nonneg (h₁ (u k) + D k)]
      calc ‖g k x‖ * h₁ (u k) ≤ h₃ x * (D k * h₁ (u k)) := by rw [← mul_assoc]; exact h3
        _ ≤ h₃ x * (h₁ (u k) ^ 2 + D k ^ 2) :=
            mul_le_mul_of_nonneg_left h4 (apply_nonneg h₃ x)
    have hN : ∀ N, h₁ x ≤ ∑' k, ‖g k x‖ * h₁ (u k) +
        h₁ (x - ∑ k ∈ range N, g k x • u k) := by
      intro N
      have h1 : h₁ (∑ k ∈ range N, g k x • u k) ≤ ∑ k ∈ range N, ‖g k x‖ * h₁ (u k) := by
        refine (seminorm_sum_le h₁ _ N).trans (le_of_eq (sum_congr rfl fun k _ => ?_))
        rw [map_smul_eq_mul]
      have h2 : ∑ k ∈ range N, ‖g k x‖ * h₁ (u k) ≤ ∑' k, ‖g k x‖ * h₁ (u k) :=
        hsx.sum_le_tsum _ fun k _ => mul_nonneg (norm_nonneg _) (apply_nonneg h₁ _)
      calc h₁ x = h₁ (∑ k ∈ range N, g k x • u k + (x - ∑ k ∈ range N, g k x • u k)) := by
            rw [add_sub_cancel]
        _ ≤ h₁ (∑ k ∈ range N, g k x • u k) + h₁ (x - ∑ k ∈ range N, g k x • u k) :=
            map_add_le_add h₁ _ _
        _ ≤ ∑' k, ‖g k x‖ * h₁ (u k) + h₁ (x - ∑ k ∈ range N, g k x • u k) :=
            add_le_add (h1.trans h2) le_rfl
    have hlim : Tendsto (fun N => ∑' k, ‖g k x‖ * h₁ (u k) +
        h₁ (x - ∑ k ∈ range N, g k x • u k)) atTop (𝓝 (∑' k, ‖g k x‖ * h₁ (u k) + 0)) :=
      tendsto_const_nhds.add (hb x)
    rw [add_zero] at hlim
    exact ge_of_tendsto' hlim hN

end Forms

end HilbertChain

open HilbertChain

theorem solution (E : Type u)
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] (hE : IsHLCS E)
    (h₁ h₂ h₃ : Seminorm ℂ E) (hc₃ : Continuous h₃)
    (hpar₁ : ∀ x y, h₁ (x + y) ^ 2 + h₁ (x - y) ^ 2 = 2 * h₁ x ^ 2 + 2 * h₁ y ^ 2)
    (hpar₂ : ∀ x y, h₂ (x + y) ^ 2 + h₂ (x - y) ^ 2 = 2 * h₂ x ^ 2 + 2 * h₂ y ^ 2)
    (hpar₃ : ∀ x y, h₃ (x + y) ^ 2 + h₃ (x - y) ^ 2 = 2 * h₃ x ^ 2 + 2 * h₃ y ^ 2)
    (h₁₂ : ∀ (n : ℕ) (x : Fin n → E) (c : ℝ),
      (∀ f : StrongDual ℂ E, (∀ y, ‖f y‖ ≤ h₂ y) → ∑ i, ‖f (x i)‖ ^ 2 ≤ c) →
      ∑ i, h₁ (x i) ^ 2 ≤ c)
    (h₂₃ : ∀ (n : ℕ) (x : Fin n → E) (c : ℝ),
      (∀ f : StrongDual ℂ E, (∀ y, ‖f y‖ ≤ h₃ y) → ∑ i, ‖f (x i)‖ ^ 2 ≤ c) →
      ∑ i, h₂ (x i) ^ 2 ≤ c) :
    ∃ (f : ℕ → StrongDual ℂ E) (c : ℕ → ℝ),
      (∀ n, 0 ≤ c n) ∧ Summable c ∧ (∀ n x, ‖f n x‖ ≤ h₃ x) ∧
      ∀ x, h₁ x ≤ ∑' n, c n * ‖f n x‖ := by
  obtain ⟨⟨ι, _, P, hP⟩, _⟩ := hE
  have hadd : IsTopologicalAddGroup E := hP.topologicalAddGroup
  -- a linear functional dominated by a continuous seminorm is continuous
  have hcont : ∀ (H : Seminorm ℂ E), Continuous H → ∀ g : E →ₗ[ℂ] ℂ, (∀ y, ‖g y‖ ≤ H y) →
      Continuous g := by
    intro H hH g hg
    refine continuous_of_continuousAt_zero g ?_
    rw [ContinuousAt, map_zero]
    refine Metric.tendsto_nhds.2 fun ε hε => ?_
    have hmem : {x : E | H x < ε} ∈ 𝓝 (0 : E) :=
      (isOpen_lt hH continuous_const).mem_nhds (by simpa using hε)
    filter_upwards [hmem] with x hx
    rw [dist_zero_right]
    exact (hg x).trans_lt hx
  -- consequences of the `2`-summing hypotheses
  have hle₁₂ : ∀ x, h₁ x ≤ h₂ x := by
    intro x
    have h := h₁₂ 1 (fun _ => x) (h₂ x ^ 2) (fun f hf => by
      simpa using pow_le_pow_left₀ (norm_nonneg _) (hf x) 2)
    have h' : h₁ x ^ 2 ≤ h₂ x ^ 2 := by simpa using h
    exact (pow_le_pow_iff_left₀ (apply_nonneg h₁ x) (apply_nonneg h₂ x) two_ne_zero).1 h'
  have hle₂₃ : ∀ x, h₂ x ≤ h₃ x := by
    intro x
    have h := h₂₃ 1 (fun _ => x) (h₃ x ^ 2) (fun f hf => by
      simpa using pow_le_pow_left₀ (norm_nonneg _) (hf x) 2)
    have h' : h₂ x ^ 2 ≤ h₃ x ^ 2 := by simpa using h
    exact (pow_le_pow_iff_left₀ (apply_nonneg h₂ x) (apply_nonneg h₃ x) two_ne_zero).1 h'
  have hHS₁₂ : ∀ (e : ℕ → E) (N : ℕ),
      (∀ g : E →ₗ[ℂ] ℂ, (∀ y, ‖g y‖ ≤ h₂ y) → ∑ i ∈ range N, ‖g (e i)‖ ^ 2 ≤ 1) →
      ∑ i ∈ range N, h₁ (e i) ^ 2 ≤ 1 := by
    intro e N hg
    have h := h₁₂ N (fun i => e i) 1 (fun f hf => by
      have h' : ∑ i ∈ range N, ‖f (e i)‖ ^ 2 ≤ 1 := hg f.toLinearMap hf
      rw [← Fin.sum_univ_eq_sum_range (fun i => ‖f (e i)‖ ^ 2) N] at h'
      exact h')
    rw [← Fin.sum_univ_eq_sum_range (fun i => h₁ (e i) ^ 2) N]
    exact h
  have hHS₂₃ : ∀ (e : ℕ → E) (N : ℕ),
      (∀ g : E →ₗ[ℂ] ℂ, (∀ y, ‖g y‖ ≤ h₃ y) → ∑ i ∈ range N, ‖g (e i)‖ ^ 2 ≤ 1) →
      ∑ i ∈ range N, h₂ (e i) ^ 2 ≤ 1 := by
    intro e N hg
    have h := h₂₃ N (fun i => e i) 1 (fun f hf => by
      have h' : ∑ i ∈ range N, ‖f (e i)‖ ^ 2 ≤ 1 := hg f.toLinearMap hf
      rw [← Fin.sum_univ_eq_sum_range (fun i => ‖f (e i)‖ ^ 2) N] at h'
      exact h')
    rw [← Fin.sum_univ_eq_sum_range (fun i => h₂ (e i) ^ 2) N]
    exact h
  obtain ⟨u, g, ha, hb, hc, hd⟩ := level h₁ h₂ hpar₂ hle₁₂ hHS₁₂
  obtain ⟨v, γ, -, hb', hc', hd'⟩ := level h₂ h₃ hpar₃ hle₂₃ hHS₂₃
  obtain ⟨f, c, hc0, hcs, hf, hdom⟩ := chain h₁ h₂ h₃ u g ha hb hc hd v γ hb' hc' hd'
  exact ⟨fun n => ⟨f n, hcont h₃ hc₃ (f n) (hf n)⟩, c, hc0, hcs, fun n x => hf n x,
    fun x => hdom x⟩
