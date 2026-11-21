-- Prove2me | solution 3 for MasulloGRH.nuclearFrechet_bounded_nuclear_domination
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-21T00:08:28.231157+00:00
-- url     : https://prove2.me/submissions/e8e96eb9-9b76-45af-b8c1-8600809ac6ae

import Theorems.Thm_MasulloGRH_abs_summing_of_l1_tensor_topologies_eq
import Theorems.Thm_MasulloGRH_isHLCS_ulift_lp_one
import Theorems.Thm_MasulloGRH_pietsch_hilbertian_two_summing

set_option autoImplicit false

universe u

section ChainPart

open MasulloGRH Set Filter Topology Finset

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

/-- **Dual form of the chain.**  With the data of two levels, every linear functional `φ` which is
bounded with respect to `h₁` is dominated on the unit ball of `h₃` by an `ℓ¹`-combination of its
values at the vectors `u k`. -/
theorem chain_dual (h₁ h₂ h₃ : Seminorm ℂ E)
    (u : ℕ → E) (g : ℕ → E →ₗ[ℂ] ℂ)
    (ha : ∀ k x, ‖g k x‖ ≤ h₂ x)
    (hb : ∀ x, Tendsto (fun N => h₁ (x - ∑ k ∈ range N, g k x • u k)) atTop (𝓝 0))
    (hc : ∀ N, ∑ k ∈ range N, h₁ (u k) ^ 2 ≤ 1)
    (hd : ∀ y N, ∑ k ∈ range N, ‖g k y‖ ^ 2 ≤ h₂ y ^ 2)
    (v : ℕ → E) (γ : ℕ → E →ₗ[ℂ] ℂ)
    (hb' : ∀ x, Tendsto (fun N => h₂ (x - ∑ j ∈ range N, γ j x • v j)) atTop (𝓝 0))
    (hc' : ∀ N, ∑ j ∈ range N, h₂ (v j) ^ 2 ≤ 1)
    (hd' : ∀ y N, ∑ j ∈ range N, ‖γ j y‖ ^ 2 ≤ h₃ y ^ 2) :
    ∃ D : ℕ → ℝ, (∀ k, 0 ≤ D k) ∧ (Summable fun k => D k * h₁ (u k)) ∧
      ∀ (φ : E →ₗ[ℂ] ℂ) (C : ℝ), (∀ x, ‖φ x‖ ≤ C * h₁ x) →
        ∀ x, ‖φ x‖ ≤ h₃ x * ∑' k, D k * ‖φ (u k)‖ := by
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
  have hsDu : Summable fun k => D k * h₁ (u k) := by
    refine Summable.of_nonneg_of_le (fun k => mul_nonneg (hD0 k) (apply_nonneg h₁ _))
      (fun k => ?_) ((hsu.add hsD).mul_left (1 / 2))
    nlinarith [sq_nonneg (h₁ (u k) - D k)]
  refine ⟨D, hD0, hsDu, fun φ C hφ x => ?_⟩
  have hφu : ∀ k, ‖φ (u k)‖ ≤ |C| * h₁ (u k) := fun k =>
    (hφ (u k)).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (apply_nonneg h₁ _))
  have hsφ : Summable fun k => D k * ‖φ (u k)‖ := by
    refine Summable.of_nonneg_of_le (fun k => mul_nonneg (hD0 k) (norm_nonneg _))
      (fun k => ?_) (hsDu.mul_left |C|)
    calc D k * ‖φ (u k)‖ ≤ D k * (|C| * h₁ (u k)) :=
          mul_le_mul_of_nonneg_left (hφu k) (hD0 k)
      _ = |C| * (D k * h₁ (u k)) := by ring
  have hN : ∀ N, ‖φ x‖ ≤ h₃ x * ∑' k, D k * ‖φ (u k)‖ +
      |C| * h₁ (x - ∑ k ∈ range N, g k x • u k) := by
    intro N
    have hx : φ x = ∑ k ∈ range N, g k x * φ (u k) +
        φ (x - ∑ k ∈ range N, g k x • u k) := by
      rw [map_sub, map_sum]
      simp only [map_smul, smul_eq_mul]
      ring
    have h1 : ‖∑ k ∈ range N, g k x * φ (u k)‖ ≤ ∑ k ∈ range N, h₃ x * (D k * ‖φ (u k)‖) := by
      refine (norm_sum_le _ _).trans (sum_le_sum fun k _ => ?_)
      rw [norm_mul]
      calc ‖g k x‖ * ‖φ (u k)‖ ≤ h₃ x * D k * ‖φ (u k)‖ :=
            mul_le_mul_of_nonneg_right (hS2 k x) (norm_nonneg _)
        _ = h₃ x * (D k * ‖φ (u k)‖) := by ring
    have h2 : ∑ k ∈ range N, h₃ x * (D k * ‖φ (u k)‖) ≤ h₃ x * ∑' k, D k * ‖φ (u k)‖ := by
      rw [← mul_sum]
      exact mul_le_mul_of_nonneg_left
        (hsφ.sum_le_tsum _ fun k _ => mul_nonneg (hD0 k) (norm_nonneg _)) (apply_nonneg h₃ x)
    have h3 : ‖φ (x - ∑ k ∈ range N, g k x • u k)‖ ≤
        |C| * h₁ (x - ∑ k ∈ range N, g k x • u k) :=
      (hφ _).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (apply_nonneg h₁ _))
    calc ‖φ x‖ = ‖∑ k ∈ range N, g k x * φ (u k) +
            φ (x - ∑ k ∈ range N, g k x • u k)‖ := by rw [← hx]
      _ ≤ ‖∑ k ∈ range N, g k x * φ (u k)‖ + ‖φ (x - ∑ k ∈ range N, g k x • u k)‖ :=
          norm_add_le _ _
      _ ≤ _ := add_le_add (h1.trans h2) h3
  have hlim : Tendsto (fun N => h₃ x * ∑' k, D k * ‖φ (u k)‖ +
      |C| * h₁ (x - ∑ k ∈ range N, g k x • u k)) atTop
      (𝓝 (h₃ x * ∑' k, D k * ‖φ (u k)‖ + |C| * 0)) :=
    tendsto_const_nhds.add ((hb x).const_mul |C|)
  rw [mul_zero, add_zero] at hlim
  exact ge_of_tendsto' hlim hN

end Forms

end HilbertChain

end ChainPart

section S1Part

open MasulloGRH

namespace NFBD

open Topology in
/-- Scaling argument: if `p' ≤ 1` on the open `p`-ball of radius `r`, then `p' ≤ (2 / r) * p`. -/
theorem seminorm_le_of_ball {E : Type u} [AddCommGroup E] [Module ℂ E]
    (p p' : Seminorm ℂ E) (r : ℝ) (hr : 0 < r) (h : ∀ x, p x < r → p' x ≤ 1) :
    ∀ x, p' x ≤ 2 / r * p x := by
  intro y
  have key : ∀ t : ℝ, 0 < t → t * p y < r → t * p' y ≤ 1 := by
    intro t ht htq
    have h1 := h ((t : ℂ) • y) (by
      rw [map_smul_eq_mul, Complex.norm_real, Real.norm_of_nonneg ht.le]; exact htq)
    rwa [map_smul_eq_mul, Complex.norm_real, Real.norm_of_nonneg ht.le] at h1
  by_cases hq0 : p y = 0
  · have hPy : p' y ≤ 0 := by
      by_contra h
      push Not at h
      have h3 := key (2 / p' y) (by positivity) (by rw [hq0, mul_zero]; exact hr)
      rw [div_mul_cancel₀ _ h.ne'] at h3
      linarith
    rw [hq0, mul_zero]
    exact hPy
  · have hqpos : 0 < p y := lt_of_le_of_ne (apply_nonneg _ _) (Ne.symm hq0)
    have h3 := key (r / (2 * p y)) (by positivity) (by
      have : r / (2 * p y) * p y = r / 2 := by field_simp
      rw [this]; linarith)
    rw [div_mul_eq_mul_div, div_le_one (by positivity)] at h3
    rw [div_mul_eq_mul_div, le_div_iff₀ hr]
    linarith

theorem exists_hilbert_seminorm_seq (E : Type u) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (hE : IsFrechet E) (hN : IsNuclear E) :
    ∃ h : ℕ → Seminorm ℂ E,
      (∀ n, Continuous (h n)) ∧
      (∀ n x, h n x ≤ h (n + 1) x) ∧
      (∀ n x y, h n (x + y) ^ 2 + h n (x - y) ^ 2 = 2 * h n x ^ 2 + 2 * h n y ^ 2) ∧
      (∀ p : Seminorm ℂ E, Continuous p → ∃ (n : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ x, p x ≤ C * h n x) ∧
      (∀ (n m : ℕ) (x : Fin m → E) (c : ℝ),
        (∀ f : StrongDual ℂ E, (∀ y, ‖f y‖ ≤ h (n + 1) y) → ∑ i, ‖f (x i)‖ ^ 2 ≤ c) →
        ∑ i, h n (x i) ^ 2 ≤ c) := by
  obtain ⟨hLC, -, hmet⟩ := hE
  have hH : IsHLCS E := hN.1
  obtain ⟨ι, hι, P, hP⟩ := hLC
  have hadd : IsTopologicalAddGroup E := hP.topologicalAddGroup
  have hsmul : ContinuousSMul ℂ E := hP.continuousSMul
  have : TopologicalSpace.MetrizableSpace E := hmet
  -- absolute summability from nuclearity
  have hAS := abs_summing_of_l1_tensor_topologies_eq E hH
    (hN.2 (ULift.{u} (lp (fun _ : ℕ => ℂ) 1)) isHLCS_ulift_lp_one)
  -- one step of the construction: `s ↦ (q, h)` with `s ≤ h ≤ q`
  have hstep : ∀ s : {s : Seminorm ℂ E // Continuous s},
      ∃ qh : {q : Seminorm ℂ E // Continuous q} × Seminorm ℂ E,
        Continuous qh.2 ∧ (∀ x, s.1 x ≤ qh.2 x) ∧ (∀ x, qh.2 x ≤ qh.1.1 x) ∧
        (∀ x y, qh.2 (x + y) ^ 2 + qh.2 (x - y) ^ 2 = 2 * qh.2 x ^ 2 + 2 * qh.2 y ^ 2) ∧
        ∀ (n : ℕ) (x : Fin n → E) (c : ℝ),
          (∀ f : StrongDual ℂ E, (∀ y, ‖f y‖ ≤ qh.1.1 y) → ∑ i, ‖f (x i)‖ ^ 2 ≤ c) →
          ∑ i, qh.2 (x i) ^ 2 ≤ c := by
    rintro ⟨s, hs⟩
    obtain ⟨q, hq, hqAS⟩ := hAS s hs
    obtain ⟨h, hh, h1, h2, h3, h4⟩ := pietsch_hilbertian_two_summing E hH s q hs hq hqAS
    exact ⟨(⟨q, hq⟩, h), hh, h1, h2, h3, h4⟩
  choose QH hQHc hQH1 hQH2 hQH3 hQH4 using hstep
  -- a countable cofinal family of continuous seminorms
  obtain ⟨V, hV⟩ := (nhds (0 : E)).exists_antitone_basis
  have hpn : ∀ n : ℕ, ∃ (p : Seminorm ℂ E) (r : ℝ), Continuous p ∧ 0 < r ∧ p.ball 0 r ⊆ V n := by
    intro n
    obtain ⟨⟨s, r⟩, hr, hsub⟩ :=
      hP.hasBasis_zero_ball.mem_iff.1 (hV.toHasBasis.mem_of_mem (i := n) trivial)
    exact ⟨s.sup P, r,
      Seminorm.continuous (r := r) (hP.hasBasis_zero_ball.mem_of_mem (i := (s, r)) hr), hr, hsub⟩
  choose p r hpc hr hpV using hpn
  have hsupc : ∀ a b : Seminorm ℂ E, Continuous a → Continuous b →
      Continuous (⇑(a ⊔ b : Seminorm ℂ E)) := by
    intro a b ha hb
    have : ⇑(a ⊔ b) = fun x => max (a x) (b x) := by
      ext x
      exact Seminorm.sup_apply a b x
    rw [this]
    exact ha.max hb
  -- the recursion
  obtain ⟨S, hS0, hSs⟩ : ∃ S : ℕ → {s : Seminorm ℂ E // Continuous s},
      S 0 = ⟨p 0, hpc 0⟩ ∧
      ∀ n, S (n + 1) =
        ⟨(QH (S n)).1.1 ⊔ p (n + 1), hsupc _ _ (QH (S n)).1.2 (hpc (n + 1))⟩ :=
    ⟨fun n => Nat.rec ⟨p 0, hpc 0⟩
      (fun n a => ⟨(QH a).1.1 ⊔ p (n + 1), hsupc _ _ (QH a).1.2 (hpc (n + 1))⟩) n,
      rfl, fun _ => rfl⟩
  have hpS : ∀ n x, p n x ≤ (S n).1 x := by
    intro n x
    cases n with
    | zero => rw [hS0]
    | succ n =>
      rw [hSs]
      change p (n + 1) x ≤ ((QH (S n)).1.1 ⊔ p (n + 1)) x
      rw [Seminorm.sup_apply]
      exact le_max_right _ _
  have hqS : ∀ n x, (QH (S n)).1.1 x ≤ (S (n + 1)).1 x := by
    intro n x
    rw [hSs]
    change (QH (S n)).1.1 x ≤ ((QH (S n)).1.1 ⊔ p (n + 1)) x
    rw [Seminorm.sup_apply]
    exact le_max_left _ _
  refine ⟨fun n => (QH (S n)).2, fun n => hQHc _, fun n x => ?_, fun n => hQH3 _, ?_, ?_⟩
  · exact (hQH2 _ x).trans ((hqS n x).trans (hQH1 _ x))
  · intro p' hp'
    have h1 : {x : E | p' x < 1} ∈ nhds (0 : E) :=
      (isOpen_lt hp' continuous_const).mem_nhds (by simp)
    obtain ⟨n, -, hn⟩ := hV.toHasBasis.mem_iff.1 h1
    have hC : (0 : ℝ) ≤ 2 / r n := by
      have := hr n
      positivity
    refine ⟨n, 2 / r n, hC, fun x => ?_⟩
    have h2 := seminorm_le_of_ball (p n) p' (r n) (hr n)
      (fun z hz => le_of_lt (hn (hpV n (by rw [Seminorm.mem_ball_zero]; exact hz)))) x
    exact h2.trans (mul_le_mul_of_nonneg_left ((hpS n x).trans (hQH1 _ x)) hC)
  · intro n m x c hf
    exact hQH4 (S n) m x c
      (fun f hfq => hf f (fun y => (hfq y).trans ((hqS n y).trans (hQH1 _ y))))

end NFBD

end S1Part

section S2Part

namespace NFBD

/-- Weighted Minkowski inequality in `ℓ²` for nonnegative sequences. -/
theorem weighted_minkowski (w a b : ℕ → ℝ) (hw : ∀ n, 0 ≤ w n) (ha : ∀ n, 0 ≤ a n)
    (hb : ∀ n, 0 ≤ b n) (hsa : Summable fun n => w n * a n ^ 2)
    (hsb : Summable fun n => w n * b n ^ 2) :
    (Summable fun n => w n * (a n + b n) ^ 2) ∧
      Real.sqrt (∑' n, w n * (a n + b n) ^ 2) ≤
        Real.sqrt (∑' n, w n * a n ^ 2) + Real.sqrt (∑' n, w n * b n ^ 2) := by
  have e : ∀ c : ℕ → ℝ,
      (fun n => (Real.sqrt (w n) * c n) ^ (2 : ℝ)) = fun n => w n * c n ^ 2 := by
    intro c
    funext n
    rw [Real.rpow_two, mul_pow, Real.sq_sqrt (hw n)]
  have key := Real.Lp_add_le_tsum_of_nonneg (p := 2)
    (f := fun n => Real.sqrt (w n) * a n) (g := fun n => Real.sqrt (w n) * b n) (by norm_num)
    (fun n => mul_nonneg (Real.sqrt_nonneg _) (ha n))
    (fun n => mul_nonneg (Real.sqrt_nonneg _) (hb n))
    (by rw [e a]; exact hsa) (by rw [e b]; exact hsb)
  have e' : (fun n => (Real.sqrt (w n) * a n + Real.sqrt (w n) * b n) ^ (2 : ℝ)) =
      fun n => w n * (a n + b n) ^ 2 := by
    rw [← e fun n => a n + b n]
    funext n
    rw [mul_add]
  rw [e a, e b, e'] at key
  refine ⟨key.1, ?_⟩
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  exact key.2

/-- The set of `x` with `∑ w n * h n x ^ 2 < ∞` is a subspace. -/
theorem exists_summable_submodule {E : Type*} [AddCommGroup E] [Module ℂ E]
    (h : ℕ → Seminorm ℂ E) (w : ℕ → ℝ) (hw : ∀ n, 0 ≤ w n) :
    ∃ W : Submodule ℂ E, ∀ x : E, x ∈ W ↔ Summable fun n => w n * h n x ^ 2 := by
  refine ⟨{ carrier := {x | Summable fun n => w n * h n x ^ 2}
            add_mem' := ?_
            zero_mem' := ?_
            smul_mem' := ?_ }, fun x => Iff.rfl⟩
  · intro x y hx hy
    have hx' : Summable fun n => w n * h n x ^ 2 := hx
    have hy' : Summable fun n => w n * h n y ^ 2 := hy
    have hsum : Summable fun n => 2 * (w n * h n x ^ 2) + 2 * (w n * h n y ^ 2) :=
      (hx'.mul_left 2).add (hy'.mul_left 2)
    refine Summable.of_nonneg_of_le (fun n => mul_nonneg (hw n) (sq_nonneg _)) (fun n => ?_) hsum
    have h1 : h n (x + y) ≤ h n x + h n y := map_add_le_add (h n) x y
    have h0 : 0 ≤ h n (x + y) := apply_nonneg (h n) _
    have h2 : h n (x + y) ^ 2 ≤ 2 * h n x ^ 2 + 2 * h n y ^ 2 := by
      nlinarith [sq_nonneg (h n x - h n y)]
    nlinarith [hw n]
  · show Summable fun n => w n * h n 0 ^ 2
    simp
  · intro c x hx
    have hx' : Summable fun n => w n * h n x ^ 2 := hx
    show Summable fun n => w n * h n (c • x) ^ 2
    have e : (fun n => w n * h n (c • x) ^ 2) = fun n => ‖c‖ ^ 2 * (w n * h n x ^ 2) := by
      funext n
      rw [map_smul_eq_mul]
      ring
    rw [e]
    exact hx'.mul_left _

/-- On a subspace where the weighted series converges, `x ↦ sqrt (∑' w n * h n x ^ 2)` is a
seminorm satisfying the parallelogram law. -/
theorem exists_weighted_hilbert_seminorm {E : Type*} [AddCommGroup E] [Module ℂ E]
    (h : ℕ → Seminorm ℂ E)
    (hpar : ∀ n x y, h n (x + y) ^ 2 + h n (x - y) ^ 2 = 2 * h n x ^ 2 + 2 * h n y ^ 2)
    (w : ℕ → ℝ) (hw : ∀ n, 0 ≤ w n) (W : Submodule ℂ E)
    (hW : ∀ x ∈ W, Summable fun n => w n * h n x ^ 2) :
    ∃ N : Seminorm ℂ W,
      (∀ x y, N (x + y) ^ 2 + N (x - y) ^ 2 = 2 * N x ^ 2 + 2 * N y ^ 2) ∧
      ∀ x : W, N x ^ 2 = ∑' n, w n * h n (x : E) ^ 2 := by
  have hadd : ∀ x y : W, Real.sqrt (∑' n, w n * h n ((x + y : W) : E) ^ 2) ≤
      Real.sqrt (∑' n, w n * h n (x : E) ^ 2) + Real.sqrt (∑' n, w n * h n (y : E) ^ 2) := by
    intro x y
    obtain ⟨hs, hle⟩ := weighted_minkowski w (fun n => h n (x : E)) (fun n => h n (y : E)) hw
      (fun n => apply_nonneg (h n) _) (fun n => apply_nonneg (h n) _) (hW _ x.2) (hW _ y.2)
    refine le_trans (Real.sqrt_le_sqrt ?_) hle
    refine Summable.tsum_le_tsum (fun n => ?_) (hW _ (x + y).2) hs
    have h1 : h n ((x : E) + (y : E)) ≤ h n (x : E) + h n (y : E) := map_add_le_add (h n) _ _
    have h0 : 0 ≤ h n ((x : E) + (y : E)) := apply_nonneg (h n) _
    rw [Submodule.coe_add]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 h1 2) (hw n)
  have hsmul : ∀ (c : ℂ) (x : W), Real.sqrt (∑' n, w n * h n ((c • x : W) : E) ^ 2) =
      ‖c‖ * Real.sqrt (∑' n, w n * h n (x : E) ^ 2) := by
    intro c x
    have e : (fun n => w n * h n ((c • x : W) : E) ^ 2) =
        fun n => ‖c‖ ^ 2 * (w n * h n (x : E) ^ 2) := by
      funext n
      rw [Submodule.coe_smul, map_smul_eq_mul]
      ring
    rw [e, tsum_mul_left, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg c)]
  let N : Seminorm ℂ W :=
    Seminorm.of (fun x : W => Real.sqrt (∑' n, w n * h n (x : E) ^ 2)) hadd hsmul
  have hN : ∀ x : W, N x ^ 2 = ∑' n, w n * h n (x : E) ^ 2 := by
    intro x
    show Real.sqrt (∑' n, w n * h n (x : E) ^ 2) ^ 2 = _
    exact Real.sq_sqrt (tsum_nonneg fun n => mul_nonneg (hw n) (sq_nonneg _))
  refine ⟨N, ?_, hN⟩
  intro x y
  rw [hN, hN, hN, hN, ← (hW _ (x + y).2).tsum_add (hW _ (x - y).2), ← tsum_mul_left,
    ← tsum_mul_left, ← ((hW _ x.2).mul_left 2).tsum_add ((hW _ y.2).mul_left 2)]
  refine tsum_congr fun n => ?_
  rw [Submodule.coe_add, Submodule.coe_sub]
  have := hpar n (x : E) (y : E)
  linear_combination w n * this

end NFBD

end S2Part

section MainPart

open MasulloGRH Set Filter Topology Finset HilbertChain

namespace NFBD

/-- A continuous seminorm is bounded on a von Neumann bounded set. -/
theorem seminorm_bounded_on {G : Type*} [AddCommGroup G] [Module ℂ G] [TopologicalSpace G]
    (q : Seminorm ℂ G) (hq : Continuous q) {B : Set G}
    (hB : Bornology.IsVonNBounded ℂ B) : ∃ M : ℝ, 0 < M ∧ ∀ x ∈ B, q x ≤ M := by
  have hq1 : {x : G | q x < 1} ∈ 𝓝 (0 : G) :=
    (isOpen_lt hq continuous_const).mem_nhds (by simp)
  obtain ⟨ρ, hρ⟩ := absorbs_iff_norm.1 (hB hq1)
  refine ⟨max ρ 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun x hx => ?_⟩
  have hnorm : ‖((max ρ 1 : ℝ) : ℂ)‖ = max ρ 1 := by
    rw [Complex.norm_real, Real.norm_of_nonneg (le_trans zero_le_one (le_max_right _ _))]
  obtain ⟨y, hy, rfl⟩ := hρ ((max ρ 1 : ℝ) : ℂ) (by rw [hnorm]; exact le_max_left _ _) hx
  have hy' : q y < 1 := hy
  change q (((max ρ 1 : ℝ) : ℂ) • y) ≤ max ρ 1
  rw [map_smul_eq_mul, hnorm]
  nlinarith [le_max_right ρ 1, apply_nonneg q y]

/-- **Hilbert–Schmidt link between two weighted norms.**  If `w n ≤ (1/2)^(n+1) * w' (n+1)` and
`h n` is 2-summing relative to the polar of `h (n+1)`, then the weighted norm `N` (weights `w`) is
2-summing relative to the functionals dominated by the weighted norm `N'` (weights `w'`). -/
theorem weighted_HS {E : Type u} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    (h : ℕ → Seminorm ℂ E)
    (h2s : ∀ (n m : ℕ) (x : Fin m → E) (c : ℝ),
      (∀ f : StrongDual ℂ E, (∀ y, ‖f y‖ ≤ h (n + 1) y) → ∑ i, ‖f (x i)‖ ^ 2 ≤ c) →
      ∑ i, h n (x i) ^ 2 ≤ c)
    (W : Submodule ℂ E) (w w' : ℕ → ℝ) (hw : ∀ n, 0 ≤ w n) (hw' : ∀ n, 0 < w' n)
    (hww : ∀ n, w n ≤ (1 / 2 : ℝ) ^ (n + 1) * w' (n + 1))
    (N N' : Seminorm ℂ W)
    (hN : ∀ x : W, N x ^ 2 = ∑' n, w n * h n (x : E) ^ 2)
    (hNs : ∀ x : W, Summable fun n => w n * h n (x : E) ^ 2)
    (hN' : ∀ x : W, N' x ^ 2 = ∑' n, w' n * h n (x : E) ^ 2)
    (hN's : ∀ x : W, Summable fun n => w' n * h n (x : E) ^ 2)
    (e : ℕ → W) (J : ℕ)
    (hg : ∀ g : W →ₗ[ℂ] ℂ, (∀ y, ‖g y‖ ≤ N' y) → ∑ i ∈ range J, ‖g (e i)‖ ^ 2 ≤ 1) :
    ∑ i ∈ range J, N (e i) ^ 2 ≤ 1 := by
  -- each level: `∑ h n (e i)² ≤ 1 / w' (n+1)`
  have hlevel : ∀ n, ∑ i ∈ range J, h n (e i : E) ^ 2 ≤ 1 / w' (n + 1) := by
    intro n
    have h1 := h2s n J (fun i => (e i : E)) (1 / w' (n + 1)) (fun f hf => by
      let g : W →ₗ[ℂ] ℂ := ((Real.sqrt (w' (n + 1)) : ℝ) : ℂ) • (f.toLinearMap ∘ₗ W.subtype)
      have hgapp : ∀ y : W, ‖g y‖ = Real.sqrt (w' (n + 1)) * ‖f (y : E)‖ := fun y => by
        simp only [g, LinearMap.smul_apply, LinearMap.comp_apply, Submodule.subtype_apply,
          ContinuousLinearMap.coe_coe, smul_eq_mul, norm_mul, Complex.norm_real,
          Real.norm_of_nonneg (Real.sqrt_nonneg _)]
      have hgN : ∀ y : W, ‖g y‖ ≤ N' y := by
        intro y
        rw [hgapp]
        have h2 : (Real.sqrt (w' (n + 1)) * ‖f (y : E)‖) ^ 2 ≤ N' y ^ 2 := by
          rw [mul_pow, Real.sq_sqrt (hw' (n + 1)).le, hN']
          calc w' (n + 1) * ‖f (y : E)‖ ^ 2 ≤ w' (n + 1) * h (n + 1) (y : E) ^ 2 :=
                mul_le_mul_of_nonneg_left
                  (pow_le_pow_left₀ (norm_nonneg _) (hf _) 2) (hw' (n + 1)).le
            _ ≤ ∑' m, w' m * h m (y : E) ^ 2 :=
                (hN's y).le_tsum (n + 1) fun m _ =>
                  mul_nonneg (hw' m).le (by positivity)
        exact (pow_le_pow_iff_left₀ (by positivity) (apply_nonneg N' y) two_ne_zero).1 h2
      have h3 := hg g hgN
      simp only [hgapp, mul_pow, Real.sq_sqrt (hw' (n + 1)).le] at h3
      rw [← mul_sum] at h3
      rw [Fin.sum_univ_eq_sum_range (fun i => ‖f (e i : E)‖ ^ 2) J,
        le_div_iff₀ (hw' (n + 1)), mul_comm]
      exact h3)
    rw [← Fin.sum_univ_eq_sum_range (fun i => h n (e i : E) ^ 2) J]
    exact h1
  -- sum over the levels
  have hsumn : Summable fun n => ∑ i ∈ range J, w n * h n (e i : E) ^ 2 :=
    summable_sum fun i _ => hNs (e i)
  have h1 : ∑ i ∈ range J, N (e i) ^ 2 = ∑' n, ∑ i ∈ range J, w n * h n (e i : E) ^ 2 := by
    simp only [hN]
    rw [Summable.tsum_finsetSum fun i _ => hNs (e i)]
  rw [h1]
  have hgeo : Summable fun n : ℕ => (1 / 2 : ℝ) ^ (n + 1) := by
    have := (summable_geometric_two).mul_left (1 / 2 : ℝ)
    simpa [pow_succ, mul_comm] using this
  have hgeo1 : ∑' n : ℕ, (1 / 2 : ℝ) ^ (n + 1) = 1 := by
    have h2 : ∑' n : ℕ, (1 / 2 : ℝ) ^ (n + 1) = (1 / 2) * ∑' n : ℕ, (1 / 2 : ℝ) ^ n := by
      rw [← tsum_mul_left]
      exact tsum_congr fun n => by rw [pow_succ]; ring
    rw [h2, tsum_geometric_two]
    norm_num
  rw [← hgeo1]
  refine hsumn.tsum_le_tsum (fun n => ?_) hgeo
  rw [← mul_sum]
  calc w n * ∑ i ∈ range J, h n (e i : E) ^ 2 ≤ w n * (1 / w' (n + 1)) :=
        mul_le_mul_of_nonneg_left (hlevel n) (hw n)
    _ ≤ (1 / 2 : ℝ) ^ (n + 1) * w' (n + 1) * (1 / w' (n + 1)) :=
        mul_le_mul_of_nonneg_right (hww n) (by have := hw' (n + 1); positivity)
    _ = (1 / 2 : ℝ) ^ (n + 1) := by
        have := (hw' (n + 1)).ne'
        field_simp


theorem geo_summable : Summable fun n : ℕ => (1 / 2 : ℝ) ^ (n + 1) := by
  have := (summable_geometric_two).mul_left (1 / 2 : ℝ)
  simpa [pow_succ, mul_comm] using this

theorem geo_tsum : ∑' n : ℕ, (1 / 2 : ℝ) ^ (n + 1) = 1 := by
  have h2 : ∑' n : ℕ, (1 / 2 : ℝ) ^ (n + 1) = (1 / 2) * ∑' n : ℕ, (1 / 2 : ℝ) ^ n := by
    rw [← tsum_mul_left]
    exact tsum_congr fun n => by rw [pow_succ]; ring
  rw [h2, tsum_geometric_two]
  norm_num

end NFBD

end MainPart

open MasulloGRH Set Filter Topology HilbertChain NFBD in
theorem solution (E : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (hE : IsFrechet E) (hN : IsNuclear E)
    (B : Set E) (hB : Bornology.IsVonNBounded ℂ B) :
    ∃ (y : ℕ → E) (c : ℕ → ℝ), Bornology.IsVonNBounded ℂ (Set.range y) ∧ (∀ n, 0 ≤ c n) ∧
      Summable c ∧ ∀ (f : StrongDual ℂ E), ∀ x ∈ B, ‖f x‖ ≤ ∑' n, c n * ‖f (y n)‖ := by
  have hE' := hE
  obtain ⟨⟨ι, _, P, hP⟩, -, -⟩ := hE
  have hadd : IsTopologicalAddGroup E := hP.topologicalAddGroup
  have hsmul : ContinuousSMul ℂ E := hP.continuousSMul
  -- Hilbertian seminorms with 2-summing links
  obtain ⟨h, hcont, hmono, hpar, hcof, h2s⟩ := exists_hilbert_seminorm_seq E hE' hN
  have hbd : ∀ n, ∃ M : ℝ, 0 < M ∧ ∀ x ∈ B, h n x ≤ M := fun n =>
    seminorm_bounded_on (h n) (hcont n) hB
  choose M hMpos hM using hbd
  -- three weight sequences
  have hhalf : ∀ n : ℕ, (0 : ℝ) < (1 / 2 : ℝ) ^ (n + 1) := fun n => by positivity
  have hhalf1 : ∀ n : ℕ, (1 / 2 : ℝ) ^ (n + 1) ≤ 1 := fun n =>
    pow_le_one₀ (by norm_num) (by norm_num)
  obtain ⟨δ, hδ⟩ : ∃ δ : ℕ → ℝ, ∀ n, δ n = (1 / 2 : ℝ) ^ (n + 1) / (1 + M n ^ 2) :=
    ⟨_, fun _ => rfl⟩
  have hδpos : ∀ n, 0 < δ n := fun n => by rw [hδ]; positivity
  obtain ⟨ε, hε⟩ : ∃ ε : ℕ → ℝ, ∀ n, ε n = (1 / 2 : ℝ) ^ (n + 1) * min (δ n) (δ (n + 1)) :=
    ⟨_, fun _ => rfl⟩
  have hεpos : ∀ n, 0 < ε n := fun n => by
    rw [hε]; exact mul_pos (hhalf n) (lt_min (hδpos n) (hδpos (n + 1)))
  have hεδ : ∀ n, ε n ≤ δ n := fun n => by
    rw [hε]
    calc (1 / 2 : ℝ) ^ (n + 1) * min (δ n) (δ (n + 1)) ≤ 1 * δ n :=
          mul_le_mul (hhalf1 n) (min_le_left _ _) (le_min (hδpos n).le (hδpos _).le) zero_le_one
      _ = δ n := one_mul _
  have hεδ' : ∀ n, ε n ≤ (1 / 2 : ℝ) ^ (n + 1) * δ (n + 1) := fun n => by
    rw [hε]; exact mul_le_mul_of_nonneg_left (min_le_right _ _) (hhalf n).le
  obtain ⟨η, hη⟩ : ∃ η : ℕ → ℝ, ∀ n, η n = (1 / 2 : ℝ) ^ (n + 1) * min (ε n) (ε (n + 1)) :=
    ⟨_, fun _ => rfl⟩
  have hηpos : ∀ n, 0 < η n := fun n => by
    rw [hη]; exact mul_pos (hhalf n) (lt_min (hεpos n) (hεpos (n + 1)))
  have hηε : ∀ n, η n ≤ ε n := fun n => by
    rw [hη]
    calc (1 / 2 : ℝ) ^ (n + 1) * min (ε n) (ε (n + 1)) ≤ 1 * ε n :=
          mul_le_mul (hhalf1 n) (min_le_left _ _) (le_min (hεpos n).le (hεpos _).le) zero_le_one
      _ = ε n := one_mul _
  have hηε' : ∀ n, η n ≤ (1 / 2 : ℝ) ^ (n + 1) * ε (n + 1) := fun n => by
    rw [hη]; exact mul_le_mul_of_nonneg_left (min_le_right _ _) (hhalf n).le
  -- the subspace where the strongest weighted norm is finite, and the three norms on it
  obtain ⟨W, hW⟩ := exists_summable_submodule h δ fun n => (hδpos n).le
  have hWδ : ∀ x ∈ W, Summable fun n => δ n * h n x ^ 2 := fun x hx => (hW x).1 hx
  have hWε : ∀ x ∈ W, Summable fun n => ε n * h n x ^ 2 := fun x hx =>
    Summable.of_nonneg_of_le (fun n => mul_nonneg (hεpos n).le (by positivity))
      (fun n => mul_le_mul_of_nonneg_right (hεδ n) (by positivity)) (hWδ x hx)
  have hWη : ∀ x ∈ W, Summable fun n => η n * h n x ^ 2 := fun x hx =>
    Summable.of_nonneg_of_le (fun n => mul_nonneg (hηpos n).le (by positivity))
      (fun n => mul_le_mul_of_nonneg_right (hηε n) (by positivity)) (hWε x hx)
  obtain ⟨N₃, hpar₃, hN₃⟩ :=
    exists_weighted_hilbert_seminorm h hpar δ (fun n => (hδpos n).le) W hWδ
  obtain ⟨N₂, hpar₂, hN₂⟩ :=
    exists_weighted_hilbert_seminorm h hpar ε (fun n => (hεpos n).le) W hWε
  obtain ⟨N₁, hpar₁, hN₁⟩ :=
    exists_weighted_hilbert_seminorm h hpar η (fun n => (hηpos n).le) W hWη
  have hle₂₃ : ∀ x, N₂ x ≤ N₃ x := by
    intro x
    have h1 : N₂ x ^ 2 ≤ N₃ x ^ 2 := by
      rw [hN₂, hN₃]
      exact (hWε x x.2).tsum_le_tsum
        (fun n => mul_le_mul_of_nonneg_right (hεδ n) (by positivity)) (hWδ x x.2)
    exact (pow_le_pow_iff_left₀ (apply_nonneg _ _) (apply_nonneg _ _) two_ne_zero).1 h1
  have hle₁₂ : ∀ x, N₁ x ≤ N₂ x := by
    intro x
    have h1 : N₁ x ^ 2 ≤ N₂ x ^ 2 := by
      rw [hN₁, hN₂]
      exact (hWη x x.2).tsum_le_tsum
        (fun n => mul_le_mul_of_nonneg_right (hηε n) (by positivity)) (hWε x x.2)
    exact (pow_le_pow_iff_left₀ (apply_nonneg _ _) (apply_nonneg _ _) two_ne_zero).1 h1
  -- Hilbert–Schmidt links between the weighted norms
  have HS₂₃ : ∀ (e : ℕ → W) (J : ℕ),
      (∀ g : W →ₗ[ℂ] ℂ, (∀ y, ‖g y‖ ≤ N₃ y) → ∑ i ∈ Finset.range J, ‖g (e i)‖ ^ 2 ≤ 1) →
      ∑ i ∈ Finset.range J, N₂ (e i) ^ 2 ≤ 1 := fun e J hg =>
    weighted_HS h h2s W ε δ (fun n => (hεpos n).le) hδpos hεδ' N₂ N₃ hN₂
      (fun x => hWε x x.2) hN₃ (fun x => hWδ x x.2) e J hg
  have HS₁₂ : ∀ (e : ℕ → W) (J : ℕ),
      (∀ g : W →ₗ[ℂ] ℂ, (∀ y, ‖g y‖ ≤ N₂ y) → ∑ i ∈ Finset.range J, ‖g (e i)‖ ^ 2 ≤ 1) →
      ∑ i ∈ Finset.range J, N₁ (e i) ^ 2 ≤ 1 := fun e J hg =>
    weighted_HS h h2s W η ε (fun n => (hηpos n).le) hεpos hηε' N₁ N₂ hN₁
      (fun x => hWη x x.2) hN₂ (fun x => hWε x x.2) e J hg
  -- the two levels and the dual chain estimate
  obtain ⟨u, g, ha, hb, hc, hd⟩ := level N₁ N₂ hpar₂ hle₁₂ HS₁₂
  obtain ⟨v, γ, -, hb', hc', hd'⟩ := level N₂ N₃ hpar₃ hle₂₃ HS₂₃
  obtain ⟨D, hD0, hsDu, hdual⟩ := chain_dual N₁ N₂ N₃ u g ha hb hc hd v γ hb' hc' hd'
  -- the seminorms `h n` are controlled by `N₁` on `W`
  have hηh : ∀ (n : ℕ) (z : W), Real.sqrt (η n) * h n (z : E) ≤ N₁ z := by
    intro n z
    have h1 : (Real.sqrt (η n) * h n (z : E)) ^ 2 ≤ N₁ z ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (hηpos n).le, hN₁]
      exact (hWη z z.2).le_tsum n fun m _ => mul_nonneg (hηpos m).le (by positivity)
    exact (pow_le_pow_iff_left₀ (by positivity) (apply_nonneg _ _) two_ne_zero).1 h1
  -- the points and the coefficients
  refine ⟨fun k => (((N₁ (u k))⁻¹ : ℝ) : ℂ) • ((u k : W) : E), fun k => D k * N₁ (u k),
    ?_, fun k => mul_nonneg (hD0 k) (apply_nonneg _ _), hsDu, fun f x hx => ?_⟩
  · -- the points form a bounded set
    apply hP.isVonNBounded_iff_seminorm_bounded.mpr
    intro i
    obtain ⟨n, C, hC, hPn⟩ := hcof (P i) (hP.continuous_seminorm i)
    have hsq : 0 < Real.sqrt (η n) := Real.sqrt_pos.2 (hηpos n)
    refine ⟨C * (1 / Real.sqrt (η n)) + 1, by positivity, ?_⟩
    rintro _ ⟨k, rfl⟩
    have hy : (((N₁ (u k))⁻¹ : ℝ) : ℂ) • ((u k : W) : E) =
        (((((N₁ (u k))⁻¹ : ℝ) : ℂ) • u k : W) : E) := by
      rw [Submodule.coe_smul]
    have hN1 : N₁ ((((N₁ (u k))⁻¹ : ℝ) : ℂ) • u k) ≤ 1 := by
      rw [map_smul_eq_mul, Complex.norm_real,
        Real.norm_of_nonneg (inv_nonneg.2 (apply_nonneg _ _))]
      by_cases h0 : N₁ (u k) = 0
      · rw [h0]; simp
      · rw [inv_mul_cancel₀ h0]
    have h1 := hηh n ((((N₁ (u k))⁻¹ : ℝ) : ℂ) • u k)
    have h2 : h n ((((N₁ (u k))⁻¹ : ℝ) : ℂ) • ((u k : W) : E)) ≤ 1 / Real.sqrt (η n) := by
      rw [hy, le_div_iff₀ hsq, mul_comm]
      exact h1.trans hN1
    have h3 := hPn ((((N₁ (u k))⁻¹ : ℝ) : ℂ) • ((u k : W) : E))
    have h4 : C * h n ((((N₁ (u k))⁻¹ : ℝ) : ℂ) • ((u k : W) : E)) ≤
        C * (1 / Real.sqrt (η n)) := mul_le_mul_of_nonneg_left h2 hC
    change (P i) ((((N₁ (u k))⁻¹ : ℝ) : ℂ) • ((u k : W) : E)) < _
    linarith
  · -- the domination
    have hxW : x ∈ W := by
      refine (hW x).2 (Summable.of_nonneg_of_le
        (fun n => mul_nonneg (hδpos n).le (by positivity)) (fun n => ?_) geo_summable)
      rw [hδ, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      have h1 : h n x ^ 2 ≤ M n ^ 2 := pow_le_pow_left₀ (apply_nonneg _ _) (hM n x hx) 2
      nlinarith [hhalf n, sq_nonneg (M n)]
    have hx3 : N₃ ⟨x, hxW⟩ ≤ 1 := by
      have h1 : N₃ ⟨x, hxW⟩ ^ 2 ≤ 1 := by
        rw [hN₃, ← geo_tsum]
        refine (hWδ x hxW).tsum_le_tsum (fun n => ?_) geo_summable
        change δ n * h n x ^ 2 ≤ _
        rw [hδ, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        have h2 : h n x ^ 2 ≤ M n ^ 2 := pow_le_pow_left₀ (apply_nonneg _ _) (hM n x hx) 2
        nlinarith [hhalf n, sq_nonneg (M n)]
      exact (pow_le_one_iff_of_nonneg (apply_nonneg _ _) two_ne_zero).1 h1
    -- `f` restricted to `W` is bounded with respect to `N₁`
    let φ : W →ₗ[ℂ] ℂ := f.toLinearMap ∘ₗ W.subtype
    have hφapp : ∀ z : W, φ z = f (z : E) := fun _ => rfl
    let pf : Seminorm ℂ E := (normSeminorm ℂ ℂ).comp f.toLinearMap
    have hpfc : Continuous pf := continuous_norm.comp f.continuous
    obtain ⟨n, C, hC, hfn⟩ := hcof pf hpfc
    have hsq : 0 < Real.sqrt (η n) := Real.sqrt_pos.2 (hηpos n)
    have hφ : ∀ z : W, ‖φ z‖ ≤ C / Real.sqrt (η n) * N₁ z := by
      intro z
      have h1 : ‖f (z : E)‖ ≤ C * h n (z : E) := hfn (z : E)
      have h2 : h n (z : E) ≤ N₁ z / Real.sqrt (η n) := by
        rw [le_div_iff₀ hsq, mul_comm]; exact hηh n z
      rw [hφapp]
      calc ‖f (z : E)‖ ≤ C * h n (z : E) := h1
        _ ≤ C * (N₁ z / Real.sqrt (η n)) := mul_le_mul_of_nonneg_left h2 hC
        _ = C / Real.sqrt (η n) * N₁ z := by ring
    have hmain := hdual φ _ hφ ⟨x, hxW⟩
    have hsum0 : 0 ≤ ∑' k, D k * ‖φ (u k)‖ :=
      tsum_nonneg fun k => mul_nonneg (hD0 k) (norm_nonneg _)
    have hterm : ∀ k, D k * ‖φ (u k)‖ =
        D k * N₁ (u k) * ‖f ((((N₁ (u k))⁻¹ : ℝ) : ℂ) • ((u k : W) : E))‖ := by
      intro k
      rw [map_smul, norm_smul, Complex.norm_real,
        Real.norm_of_nonneg (inv_nonneg.2 (apply_nonneg _ _)), hφapp]
      by_cases h0 : N₁ (u k) = 0
      · have h1 : ‖f ((u k : W) : E)‖ = 0 := by
          have := hφ (u k)
          rw [h0, mul_zero, hφapp] at this
          exact le_antisymm this (norm_nonneg _)
        rw [h0, h1]; ring
      · field_simp
    calc ‖f x‖ = ‖φ ⟨x, hxW⟩‖ := rfl
      _ ≤ N₃ ⟨x, hxW⟩ * ∑' k, D k * ‖φ (u k)‖ := hmain
      _ ≤ 1 * ∑' k, D k * ‖φ (u k)‖ := mul_le_mul_of_nonneg_right hx3 hsum0
      _ = ∑' k, D k * ‖φ (u k)‖ := one_mul _
      _ = _ := tsum_congr hterm
