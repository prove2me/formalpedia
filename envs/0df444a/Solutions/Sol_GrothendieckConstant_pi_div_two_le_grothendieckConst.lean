-- Prove2me | solution 1 for GrothendieckConstant.pi_div_two_le_grothendieckConst
-- status  : ACCEPTED   (prove)
-- author  : @BrunoDCDO
-- created : 2026-09-30T22:59:48.289161+00:00
-- url     : https://prove2.me/submissions/ffaa9038-c1b0-4f89-a992-ec0ecc1ccaff

import Mathlib
import Definitions.Def_GrothendieckConstantDefs

set_option autoImplicit false

/- The finite upper-bound proof below is reproduced from Nickrobbins95,
Prove2Me submission f260128e-39ad-469d-96d6-7bf32941862c, accepted September 24, 2026.
Its theorem is renamed to GrothendieckConstant.exists_grothendieck_bound.
The remaining argument proves the classical lower bound from the explicit definitions. -/

/- Existing finite universal bound. -/
section
/-! 35d00984 GrothendieckConstant.exists_grothendieck_bound (Grothendieck's inequality, K = 98).
Route (Rademacher projection + truncation + self-bounding, no Gaussians):
* `OPT(A)` dominates the bilinear form on `[-1,1]`-valued vectors (two sign-rounding steps).
* `SDP(A)` dominates the form on vectors of norm `≤ 1` in any finite coordinate space
  (pad each vector with a private orthogonal coordinate to make it a unit vector).
* For unit `u ∈ ℝ^d`, `X_u(ε) = Σ_k ε_k u_k` on the cube `{±1}^d` satisfies
  `E[X_u X_v] = ⟪u,v⟫` and `E[X_u^4] ≤ 3` (induction on `d`).
* Split `X = T X + (X - T X)` with `T` = truncation at `7`: the bounded part gives
  `≤ 49 OPT`, each tail part has `L²` norm `≤ 1/4` and gives `≤ SDP/4`.
  Hence `SDP ≤ 49 OPT + SDP/2`, i.e. `SDP ≤ 98 OPT`. -/

set_option autoImplicit false

namespace GrothendieckAux
open GrothendieckConstant

theorem sgn_bound (a r : ℝ) (ha : |a| ≤ 1) : a * r ≤ (if 0 ≤ r then (1:ℝ) else -1) * r := by
  rw [abs_le] at ha
  split_ifs with h
  · nlinarith
  · nlinarith

theorem sgn_pm (r : ℝ) : (if 0 ≤ r then (1:ℝ) else -1) = 1 ∨ (if 0 ≤ r then (1:ℝ) else -1) = -1 := by
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem optSet_bdd {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : BddAbove (optSet A) := by
  refine ⟨∑ i, ∑ j, |A i j|, ?_⟩
  rintro s ⟨x, y, hx, hy, rfl⟩
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  have h1 := le_abs_self (A i j)
  have h2 := neg_abs_le (A i j)
  rcases hx i with h | h <;> rcases hy j with h' | h' <;> rw [h, h'] <;> linarith

theorem bil_le_opt {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (a : Fin m → ℝ) (b : Fin n → ℝ)
    (ha : ∀ i, |a i| ≤ 1) (hb : ∀ j, |b j| ≤ 1) :
    ∑ i, ∑ j, A i j * a i * b j ≤ optValue A := by
  set x : Fin m → ℝ := fun i => if 0 ≤ ∑ j, A i j * b j then 1 else -1 with hxdef
  set y : Fin n → ℝ := fun j => if 0 ≤ ∑ i, A i j * x i then 1 else -1 with hydef
  have h1 : ∑ i, ∑ j, A i j * a i * b j ≤ ∑ i, ∑ j, A i j * x i * b j := by
    apply Finset.sum_le_sum
    intro i _
    have e1 : ∑ j, A i j * a i * b j = a i * ∑ j, A i j * b j := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring
    have e2 : ∑ j, A i j * x i * b j = x i * ∑ j, A i j * b j := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring
    rw [e1, e2]
    exact sgn_bound _ _ (ha i)
  have h2 : ∑ i, ∑ j, A i j * x i * b j ≤ ∑ i, ∑ j, A i j * x i * y j := by
    rw [Finset.sum_comm, Finset.sum_comm (f := fun i j => A i j * x i * y j)]
    apply Finset.sum_le_sum
    intro j _
    have e1 : ∑ i, A i j * x i * b j = b j * ∑ i, A i j * x i := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
    have e2 : ∑ i, A i j * x i * y j = y j * ∑ i, A i j * x i := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
    rw [e1, e2]
    exact sgn_bound _ _ (hb j)
  have h3 : ∑ i, ∑ j, A i j * x i * y j ≤ optValue A :=
    le_csSup (optSet_bdd A) ⟨x, y, fun i => sgn_pm _, fun j => sgn_pm _, rfl⟩
  linarith

theorem sdpSet_bdd {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : BddAbove (sdpSet A) := by
  refine ⟨∑ i, ∑ j, |A i j|, ?_⟩
  rintro s ⟨d, u, v, hu, hv, rfl⟩
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  have h1 : |inner ℝ (u i) (v j)| ≤ 1 := by
    have := abs_real_inner_le_norm (u i) (v j)
    rw [hu i, hv j] at this
    simpa using this
  calc A i j * inner ℝ (u i) (v j) ≤ |A i j * inner ℝ (u i) (v j)| := le_abs_self _
    _ = |A i j| * |inner ℝ (u i) (v j)| := abs_mul _ _
    _ ≤ |A i j| * 1 := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
    _ = |A i j| := mul_one _

theorem pad_mem {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) {ι : Type} [Fintype ι]
    (f : Fin m → ι → ℝ) (g : Fin n → ι → ℝ)
    (hf : ∀ i, ∑ k, f i k ^ 2 ≤ 1) (hg : ∀ j, ∑ k, g j k ^ 2 ≤ 1) :
    ∑ i, ∑ j, A i j * ∑ k, f i k * g j k ∈ sdpSet A := by
  classical
  let F : Fin m → ι ⊕ (Fin m ⊕ Fin n) → ℝ := fun i =>
    Sum.elim (f i) (Sum.elim (fun i' => if i' = i then √(1 - ∑ k, f i k ^ 2) else 0) (fun _ => 0))
  let G : Fin n → ι ⊕ (Fin m ⊕ Fin n) → ℝ := fun j =>
    Sum.elim (g j) (Sum.elim (fun _ => 0) (fun j' => if j' = j then √(1 - ∑ k, g j k ^ 2) else 0))
  have hF : ∀ i, ∑ t, F i t ^ 2 = 1 := by
    intro i
    have h0 : 0 ≤ 1 - ∑ k, f i k ^ 2 := by linarith [hf i]
    simp only [F, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
    rw [Finset.sum_eq_single i (fun b _ hb => by simp [hb]) (by simp)]
    simp [Real.sq_sqrt h0]
  have hG : ∀ j, ∑ t, G j t ^ 2 = 1 := by
    intro j
    have h0 : 0 ≤ 1 - ∑ k, g j k ^ 2 := by linarith [hg j]
    simp only [G, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
    rw [Finset.sum_eq_single j (fun b _ hb => by simp [hb]) (by simp)]
    simp [Real.sq_sqrt h0]
  have hFG : ∀ i j, ∑ t, F i t * G j t = ∑ k, f i k * g j k := by
    intro i j
    simp [F, G, Fintype.sum_sum_type]
  let e := Fintype.equivFin (ι ⊕ (Fin m ⊕ Fin n))
  refine ⟨Fintype.card (ι ⊕ (Fin m ⊕ Fin n)),
    fun i => WithLp.toLp 2 (fun k => F i (e.symm k)),
    fun j => WithLp.toLp 2 (fun k => G j (e.symm k)), ?_, ?_, ?_⟩
  · intro i
    rw [EuclideanSpace.norm_eq]
    simp only [Real.norm_eq_abs, sq_abs]
    rw [e.symm.sum_comp (fun t => F i t ^ 2), hF i, Real.sqrt_one]
  · intro j
    rw [EuclideanSpace.norm_eq]
    simp only [Real.norm_eq_abs, sq_abs]
    rw [e.symm.sum_comp (fun t => G j t ^ 2), hG j, Real.sqrt_one]
  · apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [EuclideanSpace.inner_toLp_toLp, ← hFG i j]
    simp only [dotProduct, star_trivial]
    rw [← e.symm.sum_comp (fun t => F i t * G j t)]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    ring

theorem sdpSet_nonempty {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : (sdpSet A).Nonempty :=
  ⟨_, pad_mem A (ι := Fin 0) (fun _ _ => 0) (fun _ _ => 0) (by simp) (by simp)⟩

theorem sdp_scaled {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) {Ω : Type} [Fintype Ω]
    (w a b : ℝ) (hw : 0 < w) (ha : 0 < a) (hb : 0 < b)
    (f : Fin m → Ω → ℝ) (g : Fin n → Ω → ℝ)
    (hf : ∀ i, w * ∑ ω, f i ω ^ 2 ≤ a ^ 2) (hg : ∀ j, w * ∑ ω, g j ω ^ 2 ≤ b ^ 2) :
    ∑ i, ∑ j, A i j * (w * ∑ ω, f i ω * g j ω) ≤ a * b * sdpValue A := by
  set c := √w with hcdef
  have hc : c ^ 2 = w := Real.sq_sqrt hw.le
  have hmem := pad_mem A (fun i ω => c / a * f i ω) (fun j ω => c / b * g j ω)
    (by
      intro i
      have h := hf i
      have e : ∑ ω, (c / a * f i ω) ^ 2 = (w * ∑ ω, f i ω ^ 2) / a ^ 2 := by
        rw [Finset.mul_sum, Finset.sum_div]
        apply Finset.sum_congr rfl
        intro ω _
        rw [← hc]
        field_simp
      rw [e, div_le_one (by positivity)]
      exact h)
    (by
      intro j
      have h := hg j
      have e : ∑ ω, (c / b * g j ω) ^ 2 = (w * ∑ ω, g j ω ^ 2) / b ^ 2 := by
        rw [Finset.mul_sum, Finset.sum_div]
        apply Finset.sum_congr rfl
        intro ω _
        rw [← hc]
        field_simp
      rw [e, div_le_one (by positivity)]
      exact h)
  have hle := le_csSup (sdpSet_bdd A) hmem
  have e : ∑ i, ∑ j, A i j * ∑ ω, (c / a * f i ω) * (c / b * g j ω)
      = (∑ i, ∑ j, A i j * (w * ∑ ω, f i ω * g j ω)) / (a * b) := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro ω _
    rw [← hc]
    field_simp
  rw [e, div_le_iff₀ (mul_pos ha hb)] at hle
  calc _ ≤ sSup (sdpSet A) * (a * b) := hle
    _ = a * b * sdpValue A := mul_comm _ _

theorem opt_avg {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) {Ω : Type} [Fintype Ω]
    (w : ℝ) (hw : 0 ≤ w) (a : Fin m → Ω → ℝ) (b : Fin n → Ω → ℝ)
    (ha : ∀ i ω, |a i ω| ≤ 7) (hb : ∀ j ω, |b j ω| ≤ 7) :
    ∑ i, ∑ j, A i j * (w * ∑ ω, a i ω * b j ω)
      ≤ w * (Fintype.card Ω : ℝ) * (49 * optValue A) := by
  have h1 : ∀ ω, ∑ i, ∑ j, A i j * a i ω * b j ω ≤ 49 * optValue A := by
    intro ω
    have h := bil_le_opt A (fun i => a i ω / 7) (fun j => b j ω / 7)
      (by intro i; rw [abs_div, div_le_one (by norm_num)]; simpa using ha i ω)
      (by intro j; rw [abs_div, div_le_one (by norm_num)]; simpa using hb j ω)
    have e : ∑ i, ∑ j, A i j * (a i ω / 7) * (b j ω / 7)
        = (∑ i, ∑ j, A i j * a i ω * b j ω) / 49 := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [e] at h
    linarith
  have e : ∑ i, ∑ j, A i j * (w * ∑ ω, a i ω * b j ω)
      = w * ∑ ω, ∑ i, ∑ j, A i j * a i ω * b j ω := by
    calc ∑ i, ∑ j, A i j * (w * ∑ ω, a i ω * b j ω)
        = ∑ i, ∑ j, ∑ ω, w * (A i j * a i ω * b j ω) := by
          apply Finset.sum_congr rfl; intro i _
          apply Finset.sum_congr rfl; intro j _
          rw [Finset.mul_sum, Finset.mul_sum]
          apply Finset.sum_congr rfl; intro ω _
          ring
      _ = ∑ i, ∑ ω, ∑ j, w * (A i j * a i ω * b j ω) := by
          apply Finset.sum_congr rfl; intro i _
          exact Finset.sum_comm
      _ = ∑ ω, ∑ i, ∑ j, w * (A i j * a i ω * b j ω) := Finset.sum_comm
      _ = w * ∑ ω, ∑ i, ∑ j, A i j * a i ω * b j ω := by
          simp_rw [Finset.mul_sum]
  rw [e]
  have h2 : ∑ ω, ∑ i, ∑ j, A i j * a i ω * b j ω ≤ ∑ _ω : Ω, 49 * optValue A :=
    Finset.sum_le_sum (fun ω _ => h1 ω)
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h2
  calc w * ∑ ω, ∑ i, ∑ j, A i j * a i ω * b j ω ≤ w * ((Fintype.card Ω : ℝ) * (49 * optValue A)) :=
        mul_le_mul_of_nonneg_left h2 hw
    _ = w * (Fintype.card Ω : ℝ) * (49 * optValue A) := by ring

/-! Rademacher sums on the cube. -/

def rs (b : Bool) : ℝ := if b then 1 else -1

def rX {d : ℕ} (u : Fin d → ℝ) (ε : Fin d → Bool) : ℝ := ∑ k, rs (ε k) * u k

theorem sum_cube_succ {d : ℕ} (F : (Fin (d + 1) → Bool) → ℝ) :
    ∑ ε, F ε = ∑ ε : Fin d → Bool, (F (Fin.cons true ε) + F (Fin.cons false ε)) := by
  rw [← (Fin.consEquiv (fun _ : Fin (d + 1) => Bool)).sum_comp, Fintype.sum_prod_type,
    Fintype.sum_bool, ← Finset.sum_add_distrib]
  rfl

theorem rX_cons {d : ℕ} (u : Fin (d + 1) → ℝ) (b : Bool) (ε : Fin d → Bool) :
    rX u (Fin.cons b ε) = rs b * u 0 + rX (fun k => u k.succ) ε := by
  simp [rX, Fin.sum_univ_succ]

theorem rad2 : ∀ (d : ℕ) (u v : Fin d → ℝ),
    ∑ ε, rX u ε * rX v ε = 2 ^ d * ∑ k, u k * v k := by
  intro d
  induction d with
  | zero => intro u v; simp [rX]
  | succ d ih =>
    intro u v
    rw [sum_cube_succ]
    simp only [rX_cons, rs, if_true, Bool.false_eq_true, if_false]
    have h : ∀ ε : Fin d → Bool,
        (1 * u 0 + rX (fun k => u k.succ) ε) * (1 * v 0 + rX (fun k => v k.succ) ε)
          + (-1 * u 0 + rX (fun k => u k.succ) ε) * (-1 * v 0 + rX (fun k => v k.succ) ε)
          = 2 * (u 0 * v 0) + 2 * (rX (fun k => u k.succ) ε * rX (fun k => v k.succ) ε) := by
      intro ε; ring
    simp_rw [h]
    rw [Finset.sum_add_distrib, Finset.sum_const, ← Finset.mul_sum, ih, Fin.sum_univ_succ,
      Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    ring

theorem rad4 : ∀ (d : ℕ) (u : Fin d → ℝ),
    ∑ ε, rX u ε ^ 4 ≤ 3 * 2 ^ d * (∑ k, u k ^ 2) ^ 2 := by
  intro d
  induction d with
  | zero => intro u; simp [rX]
  | succ d ih =>
    intro u
    rw [sum_cube_succ]
    simp only [rX_cons, rs, if_true, Bool.false_eq_true, if_false]
    have h : ∀ ε : Fin d → Bool,
        (1 * u 0 + rX (fun k => u k.succ) ε) ^ 4 + (-1 * u 0 + rX (fun k => u k.succ) ε) ^ 4
          = 2 * u 0 ^ 4 + 12 * u 0 ^ 2 * (rX (fun k => u k.succ) ε * rX (fun k => u k.succ) ε)
            + 2 * rX (fun k => u k.succ) ε ^ 4 := by
      intro ε; ring
    simp_rw [h]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, ← Finset.mul_sum,
      ← Finset.mul_sum, rad2, Finset.card_univ, Fintype.card_fun,
      Fintype.card_bool, Fintype.card_fin, nsmul_eq_mul, Fin.sum_univ_succ]
    have hi := ih (fun k => u k.succ)
    have hs : ∑ k : Fin d, u k.succ * u k.succ = ∑ k : Fin d, u k.succ ^ 2 := by
      apply Finset.sum_congr rfl; intro k _; ring
    rw [hs]
    have hp : (0 : ℝ) < 2 ^ d := by positivity
    have hq : 0 ≤ ∑ k : Fin d, u k.succ ^ 2 := Finset.sum_nonneg (fun k _ => sq_nonneg _)
    have h2 : (2 : ℝ) ^ (d + 1) = 2 * 2 ^ d := by ring
    rw [h2]
    push_cast
    nlinarith [sq_nonneg (u 0), pow_nonneg (sq_nonneg (u 0)) 2, mul_nonneg hp.le (pow_nonneg (sq_nonneg (u 0)) 2),
      mul_nonneg (mul_nonneg hp.le (sq_nonneg (u 0))) hq]

/-! The main self-bounding estimate. -/

theorem main_bound {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (s : ℝ) (hs : s ∈ sdpSet A) :
    s ≤ 49 * optValue A + (1 / 2) * sdpValue A := by
  obtain ⟨d, u, v, hu, hv, rfl⟩ := hs
  set U : Fin m → Fin d → ℝ := fun i k => u i k with hUdef
  set V : Fin n → Fin d → ℝ := fun j k => v j k with hVdef
  have hU : ∀ i, ∑ k, U i k ^ 2 = 1 := by
    intro i
    have h := EuclideanSpace.real_norm_sq_eq (u i)
    rw [hu i] at h
    simpa [U] using h.symm
  have hV : ∀ j, ∑ k, V j k ^ 2 = 1 := by
    intro j
    have h := EuclideanSpace.real_norm_sq_eq (v j)
    rw [hv j] at h
    simpa [V] using h.symm
  have hinner : ∀ i j, inner ℝ (u i) (v j) = ∑ k, U i k * V j k := by
    intro i j
    simp [U, V, PiLp.inner_apply, mul_comm]
  have hN : (0 : ℝ) < 2 ^ d := by positivity
  set w : ℝ := 1 / 2 ^ d with hwdef
  have hw : 0 < w := by positivity
  have hwN : w * 2 ^ d = 1 := by rw [hwdef]; field_simp
  have hcard : (Fintype.card (Fin d → Bool) : ℝ) = 2 ^ d := by simp
  let X : Fin m → (Fin d → Bool) → ℝ := fun i ε => rX (U i) ε
  let Y : Fin n → (Fin d → Bool) → ℝ := fun j ε => rX (V j) ε
  let T : ℝ → ℝ := fun x => if |x| ≤ 7 then x else 0
  have hT : ∀ x, |T x| ≤ 7 := by
    intro x
    simp only [T]
    split_ifs with h
    · exact h
    · simp
  have hT2 : ∀ x, T x ^ 2 ≤ x ^ 2 := by
    intro x
    simp only [T]
    split_ifs
    · exact le_rfl
    · simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]; exact sq_nonneg x
  have ht2 : ∀ x, (x - T x) ^ 2 ≤ x ^ 4 / 49 := by
    intro x
    simp only [T]
    split_ifs with h
    · simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
      positivity
    · have h' : 7 < |x| := not_le.mp h
      have h7 : (49 : ℝ) ≤ x ^ 2 := by
        have := sq_abs x
        nlinarith [abs_nonneg x, h']
      rw [le_div_iff₀ (by norm_num)]
      simp only [sub_zero]
      nlinarith [sq_nonneg x]
  have hsq : ∀ (d' : ℕ) (z : Fin d' → ℝ), ∑ k, z k * z k = ∑ k, z k ^ 2 := by
    intro d' z; apply Finset.sum_congr rfl; intro k _; ring
  have hXY : ∀ i j, inner ℝ (u i) (v j) = w * ∑ ε, X i ε * Y j ε := by
    intro i j
    rw [hinner]
    simp only [X, Y]
    rw [rad2, ← mul_assoc, hwN, one_mul]
  have hX2 : ∀ i, w * ∑ ε, X i ε ^ 2 ≤ 1 ^ 2 := by
    intro i
    have h := rad2 d (U i) (U i)
    rw [hsq, hU i] at h
    have e : ∑ ε, X i ε ^ 2 = ∑ ε, rX (U i) ε * rX (U i) ε := by
      apply Finset.sum_congr rfl; intro ε _; simp only [X]; ring
    rw [e, h, mul_one, hwN]; norm_num
  have hY2 : ∀ j, w * ∑ ε, Y j ε ^ 2 ≤ 1 ^ 2 := by
    intro j
    have h := rad2 d (V j) (V j)
    rw [hsq, hV j] at h
    have e : ∑ ε, Y j ε ^ 2 = ∑ ε, rX (V j) ε * rX (V j) ε := by
      apply Finset.sum_congr rfl; intro ε _; simp only [Y]; ring
    rw [e, h, mul_one, hwN]; norm_num
  have htail : ∀ (z : Fin d → ℝ), ∑ k, z k ^ 2 = 1 →
      w * ∑ ε, (rX z ε - T (rX z ε)) ^ 2 ≤ (1 / 4) ^ 2 := by
    intro z hz
    have h4 := rad4 d z
    rw [hz] at h4
    have h1 : ∑ ε, (rX z ε - T (rX z ε)) ^ 2 ≤ ∑ ε, rX z ε ^ 4 / 49 :=
      Finset.sum_le_sum (fun ε _ => ht2 _)
    rw [← Finset.sum_div] at h1
    have h2 : w * ∑ ε, (rX z ε - T (rX z ε)) ^ 2 ≤ w * (3 * 2 ^ d / 49) := by
      apply mul_le_mul_of_nonneg_left _ hw.le
      calc ∑ ε, (rX z ε - T (rX z ε)) ^ 2 ≤ (∑ ε, rX z ε ^ 4) / 49 := h1
        _ ≤ (3 * 2 ^ d * 1 ^ 2) / 49 := by gcongr
        _ = 3 * 2 ^ d / 49 := by ring
    have h3 : w * (3 * 2 ^ d / 49) = 3 / 49 := by
      rw [mul_div_assoc', mul_comm 3, ← mul_assoc, hwN]; ring
    rw [h3] at h2
    linarith
  have split : ∀ i j, A i j * inner ℝ (u i) (v j)
      = A i j * (w * ∑ ε, T (X i ε) * T (Y j ε))
        + A i j * (w * ∑ ε, T (X i ε) * (Y j ε - T (Y j ε)))
        + A i j * (w * ∑ ε, (X i ε - T (X i ε)) * Y j ε) := by
    intro i j
    rw [hXY, ← mul_add, ← mul_add, ← mul_add, ← mul_add, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    congr 2
    apply Finset.sum_congr rfl
    intro ε _
    ring
  simp_rw [split, Finset.sum_add_distrib]
  have t1 := opt_avg A w hw.le (fun i ε => T (X i ε)) (fun j ε => T (Y j ε))
    (fun i ε => hT _) (fun j ε => hT _)
  rw [hcard, hwN, one_mul] at t1
  have t2 := sdp_scaled A w 1 (1 / 4) hw one_pos (by norm_num)
    (fun i ε => T (X i ε)) (fun j ε => Y j ε - T (Y j ε))
    (fun i => le_trans (mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum (fun ε _ => hT2 (X i ε))) hw.le) (hX2 i))
    (fun j => htail (V j) (hV j))
  have t3 := sdp_scaled A w (1 / 4) 1 hw (by norm_num) one_pos
    (fun i ε => X i ε - T (X i ε)) (fun j ε => Y j ε)
    (fun i => htail (U i) (hU i)) hY2
  linarith

end GrothendieckAux

open GrothendieckConstant in
theorem GrothendieckConstant.exists_grothendieck_bound : ∃ K : ℝ, IsGrothendieckBound K := by
  refine ⟨98, fun m n A => ?_⟩
  have h : sdpValue A ≤ 49 * optValue A + (1 / 2) * sdpValue A :=
    csSup_le (GrothendieckAux.sdpSet_nonempty A) (fun s hs => GrothendieckAux.main_bound A s hs)
  linarith
end

/- Finite weighted Gram matrices. -/
section
set_option autoImplicit false

namespace GrothendieckGeometry
open GrothendieckConstant

/- The two boundedness proofs below are reproduced from Nickrobbins95's accepted
Prove2Me submission f260128e-39ad-469d-96d6-7bf32941862c. -/
theorem optSet_bdd {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : BddAbove (optSet A) := by
  refine ⟨∑ i, ∑ j, |A i j|, ?_⟩
  rintro s ⟨x, y, hx, hy, rfl⟩
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  have h1 := le_abs_self (A i j)
  have h2 := neg_abs_le (A i j)
  rcases hx i with h | h <;> rcases hy j with h' | h' <;> rw [h, h'] <;> linarith

theorem sdpSet_bdd {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : BddAbove (sdpSet A) := by
  refine ⟨∑ i, ∑ j, |A i j|, ?_⟩
  rintro s ⟨d, u, v, hu, hv, rfl⟩
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  have h1 : |inner ℝ (u i) (v j)| ≤ 1 := by
    have := abs_real_inner_le_norm (u i) (v j)
    rw [hu i, hv j] at this
    simpa using this
  calc A i j * inner ℝ (u i) (v j) ≤ |A i j * inner ℝ (u i) (v j)| := le_abs_self _
    _ = |A i j| * |inner ℝ (u i) (v j)| := abs_mul _ _
    _ ≤ |A i j| * 1 := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
    _ = |A i j| := mul_one _

/-- The Gram matrix turns the bilinear sign problem into a signed-vector problem. -/
noncomputable def gramMatrix {m d : ℕ} (u : Fin m → EuclideanSpace ℝ (Fin d)) :
    Matrix (Fin m) (Fin m) ℝ := fun i j => inner ℝ (u i) (u j)

def signVector {m : ℕ} (ε : Fin m → Bool) (i : Fin m) : ℝ :=
  if ε i then 1 else -1

theorem signVector_pm {m : ℕ} (ε : Fin m → Bool) (i : Fin m) :
    signVector ε i = 1 ∨ signVector ε i = -1 := by
  simp only [signVector]; split <;> simp

def signedSum {m d : ℕ} (u : Fin m → EuclideanSpace ℝ (Fin d))
    (ε : Fin m → Bool) : EuclideanSpace ℝ (Fin d) := ∑ i, signVector ε i • u i

theorem signs_representation {m : ℕ} (x : Fin m → ℝ)
    (hx : ∀ i, x i = 1 ∨ x i = -1) : ∃ ε : Fin m → Bool, x = signVector ε := by
  classical
  refine ⟨fun i => decide (x i = 1), ?_⟩
  funext i
  rcases hx i with h | h <;> simp [signVector, h]

theorem gram_bilinear {m d : ℕ} (u : Fin m → EuclideanSpace ℝ (Fin d))
    (x y : Fin m → ℝ) :
    (∑ i, ∑ j, gramMatrix u i j * x i * y j) =
      inner ℝ (∑ i, x i • u i) (∑ j, y j • u j) := by
  rw [sum_inner]
  simp only [inner_sum, real_inner_smul_left, real_inner_smul_right]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  simp only [gramMatrix]
  ring

theorem signed_norm_sq_mem_opt {m d : ℕ} (u : Fin m → EuclideanSpace ℝ (Fin d))
    (ε : Fin m → Bool) : ‖signedSum u ε‖ ^ 2 ∈ optSet (gramMatrix u) := by
  refine ⟨signVector ε, signVector ε, signVector_pm ε, signVector_pm ε, ?_⟩
  rw [gram_bilinear, real_inner_self_eq_norm_sq]
  rfl

/-- The optimum of a Gram matrix is the largest squared norm of a signed sum. -/
theorem gram_opt_eq_max_signed_norm {m d : ℕ} (u : Fin m → EuclideanSpace ℝ (Fin d)) :
    optValue (gramMatrix u) = sSup (Set.range fun ε : Fin m → Bool => ‖signedSum u ε‖ ^ 2) := by
  classical
  let S := Set.range fun ε : Fin m → Bool => ‖signedSum u ε‖ ^ 2
  have hfin : S.Finite := Set.finite_range _
  have hne : S.Nonempty := Set.range_nonempty _
  have hmax := hne.csSup_mem hfin
  apply le_antisymm
  · apply csSup_le
    · exact ⟨_, signed_norm_sq_mem_opt u (fun _ => false)⟩
    · rintro s ⟨x, y, hx, hy, rfl⟩
      obtain ⟨ε, rfl⟩ := signs_representation x hx
      obtain ⟨δ, rfl⟩ := signs_representation y hy
      rw [gram_bilinear]
      have hε : ‖signedSum u ε‖ ^ 2 ≤ sSup S := le_csSup hfin.bddAbove ⟨ε, rfl⟩
      have hδ : ‖signedSum u δ‖ ^ 2 ≤ sSup S := le_csSup hfin.bddAbove ⟨δ, rfl⟩
      have hcs := real_inner_le_norm (signedSum u ε) (signedSum u δ)
      change inner ℝ (signedSum u ε) (signedSum u δ) ≤ sSup S
      nlinarith [sq_nonneg (‖signedSum u ε‖ - ‖signedSum u δ‖)]
  · obtain ⟨ε, hε⟩ := hmax
    rw [← hε]
    exact le_csSup (optSet_bdd _) (signed_norm_sq_mem_opt u ε)

/-- A Gram optimum is attained with the same signs in its two factors. -/
theorem gram_opt_attained {m d : ℕ} (u : Fin m → EuclideanSpace ℝ (Fin d)) :
    ∃ ε : Fin m → Bool, optValue (gramMatrix u) = ‖signedSum u ε‖ ^ 2 := by
  rw [gram_opt_eq_max_signed_norm]
  obtain ⟨ε, hε⟩ := (Set.range_nonempty (fun ε : Fin m → Bool => ‖signedSum u ε‖ ^ 2)).csSup_mem
    (Set.finite_range _)
  exact ⟨ε, hε.symm⟩

theorem signed_inner_le_support {m d : ℕ} (u : Fin m → EuclideanSpace ℝ (Fin d))
    (ε : Fin m → Bool) (z : EuclideanSpace ℝ (Fin d)) :
    inner ℝ (signedSum u ε) z ≤ ∑ i, |inner ℝ (u i) z| := by
  simp only [signedSum, sum_inner, real_inner_smul_left]
  apply Finset.sum_le_sum
  intro i hi
  rcases signVector_pm ε i with h | h
  · simp only [h, one_mul]; exact le_abs_self _
  · simp only [h, neg_one_mul]; exact neg_le_abs _

theorem support_attained_by_signs {m d : ℕ} (u : Fin m → EuclideanSpace ℝ (Fin d))
    (z : EuclideanSpace ℝ (Fin d)) :
    ∃ ε : Fin m → Bool, inner ℝ (signedSum u ε) z = ∑ i, |inner ℝ (u i) z| := by
  classical
  refine ⟨fun i => decide (0 ≤ inner ℝ (u i) z), ?_⟩
  simp only [signedSum, sum_inner, real_inner_smul_left]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases h : 0 ≤ inner ℝ (u i) z
  · simp [signVector, h, abs_of_nonneg h]
  · simp [signVector, h, abs_of_neg (lt_of_not_ge h)]

/-- Duality between signed sums and the support function of their zonotope. -/
theorem signed_norm_le_iff_support {m d : ℕ} (u : Fin m → EuclideanSpace ℝ (Fin d))
    {L : ℝ} (hL : 0 ≤ L) :
    (∀ ε : Fin m → Bool, ‖signedSum u ε‖ ≤ L) ↔
      ∀ z : EuclideanSpace ℝ (Fin d), ‖z‖ = 1 → ∑ i, |inner ℝ (u i) z| ≤ L := by
  constructor
  · intro h z hz
    obtain ⟨ε, hε⟩ := support_attained_by_signs u z
    rw [← hε]
    calc inner ℝ (signedSum u ε) z ≤ ‖signedSum u ε‖ * ‖z‖ := real_inner_le_norm _ _
      _ ≤ L := by simpa [hz] using h ε
  · intro h ε
    by_cases he : signedSum u ε = 0
    · simpa [he] using hL
    · let z : EuclideanSpace ℝ (Fin d) := ‖signedSum u ε‖⁻¹ • signedSum u ε
      have hz : ‖z‖ = 1 := norm_smul_inv_norm he
      have hzinner : inner ℝ (signedSum u ε) z = ‖signedSum u ε‖ := by
        simp only [z, real_inner_smul_right, real_inner_self_eq_norm_sq]
        have hn : ‖signedSum u ε‖ ≠ 0 := norm_ne_zero_iff.mpr he
        field_simp
      rw [← hzinner]
      exact (signed_inner_le_support u ε z).trans (h z hz)

/-- Exact geometric characterization of a quadratic upper bound on the discrete optimum. -/
theorem gram_opt_le_iff_support {m d : ℕ} (u : Fin m → EuclideanSpace ℝ (Fin d))
    {L : ℝ} (hL : 0 ≤ L) :
    optValue (gramMatrix u) ≤ L ^ 2 ↔
      ∀ z : EuclideanSpace ℝ (Fin d), ‖z‖ = 1 → ∑ i, |inner ℝ (u i) z| ≤ L := by
  rw [← signed_norm_le_iff_support u hL]
  constructor
  · intro h ε
    have hε := (le_csSup (optSet_bdd _) (signed_norm_sq_mem_opt u ε)).trans h
    nlinarith [norm_nonneg (signedSum u ε)]
  · intro h
    obtain ⟨ε, hε⟩ := gram_opt_attained u
    rw [hε]
    exact pow_le_pow_left₀ (norm_nonneg _) (h ε) 2

theorem gram_energy_le_sdp {m d : ℕ} (u : Fin m → EuclideanSpace ℝ (Fin d))
    (hu : ∀ i, ‖u i‖ = 1) :
    (∑ i, ∑ j, (inner ℝ (u i) (u j)) ^ 2) ≤ sdpValue (gramMatrix u) := by
  apply le_csSup (sdpSet_bdd _)
  refine ⟨d, u, u, hu, hu, ?_⟩
  simp [gramMatrix, pow_two]

/-- Expanding either Gram matrix gives the same squared Frobenius norm. -/
theorem gram_energy_eq_covariance {m d : ℕ} (u : Fin m → EuclideanSpace ℝ (Fin d)) :
    (∑ i, ∑ j, (inner ℝ (u i) (u j)) ^ 2) =
      ∑ k, ∑ l, (∑ i, u i k * u i l) ^ 2 := by
  have inner_coords (i j : Fin m) : inner ℝ (u i) (u j) = ∑ k, u i k * u j k := by
    simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Pi.star_apply,
      star_trivial, mul_comm]
  simp_rw [inner_coords, pow_two, Finset.sum_mul_sum]
  calc
    (∑ i, ∑ j, ∑ k, ∑ l, u i k * u j k * (u i l * u j l)) =
        ∑ k, ∑ i, ∑ j, ∑ l, u i k * u j k * (u i l * u j l) := by
      simp_rw [Finset.sum_comm (f := fun j k => ∑ l, u _ k * u j k * (u _ l * u j l))]
      rw [Finset.sum_comm]
    _ = ∑ k, ∑ l, ∑ i, ∑ j, u i k * u j k * (u i l * u j l) := by
      apply Finset.sum_congr rfl
      intro k hk
      simp_rw [Finset.sum_comm (f := fun j l => u _ k * u j k * (u _ l * u j l))]
      rw [Finset.sum_comm]
    _ = ∑ k, ∑ l, ∑ i, ∑ j, u i k * u i l * (u j k * u j l) := by
      apply Finset.sum_congr rfl; intro k hk
      apply Finset.sum_congr rfl; intro l hl
      apply Finset.sum_congr rfl; intro i hi
      apply Finset.sum_congr rfl; intro j hj
      ring

/-- Trace versus squared Frobenius norm, with no normalization assumption. -/
theorem sum_norm_sq_sq_le_dimension_mul_energy {m d : ℕ}
    (u : Fin m → EuclideanSpace ℝ (Fin d)) :
    (∑ i, ‖u i‖ ^ 2) ^ 2 ≤ (d : ℝ) * ∑ i, ∑ j, (inner ℝ (u i) (u j)) ^ 2 := by
  have htrace : (∑ k, ∑ i, u i k * u i k) = ∑ i, ‖u i‖ ^ 2 := by
    rw [Finset.sum_comm]
    simp_rw [← pow_two, ← EuclideanSpace.real_norm_sq_eq]
  have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.univ)
    (f := fun k : Fin d => ∑ i, u i k * u i k)
  simp only [Finset.card_univ, Fintype.card_fin, htrace] at hcs
  refine hcs.trans (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg d))
  rw [gram_energy_eq_covariance]
  apply Finset.sum_le_sum
  intro k hk
  exact Finset.single_le_sum (fun l hl => sq_nonneg (∑ i, u i k * u i l)) (Finset.mem_univ k)

/-- The trace bound for the Gram energy of any finite family of unit vectors. -/
theorem card_sq_le_dimension_mul_energy {m d : ℕ} (u : Fin m → EuclideanSpace ℝ (Fin d))
    (hu : ∀ i, ‖u i‖ = 1) :
    (m : ℝ) ^ 2 ≤ (d : ℝ) * ∑ i, ∑ j, (inner ℝ (u i) (u j)) ^ 2 := by
  simpa [hu] using sum_norm_sq_sq_le_dimension_mul_energy u

/-- A unit-vector cloud gives the rank-sensitive SDP lower bound used in spherical examples. -/
theorem card_sq_div_dimension_le_sdp {m d : ℕ} (u : Fin m → EuclideanSpace ℝ (Fin d))
    (hd : 0 < d) (hu : ∀ i, ‖u i‖ = 1) :
    (m : ℝ) ^ 2 / d ≤ sdpValue (gramMatrix u) := by
  have hd' : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  apply le_trans _ (gram_energy_le_sdp u hu)
  exact (div_le_iff₀ hd').mpr (by simpa [mul_comm] using card_sq_le_dimension_mul_energy u hu)

/-- Gram matrix weighted in both indices, preserving the sign-support interpretation. -/
noncomputable def weightedGramMatrix {m d : ℕ} (p : Fin m → ℝ)
    (u : Fin m → EuclideanSpace ℝ (Fin d)) : Matrix (Fin m) (Fin m) ℝ :=
  gramMatrix (fun i => p i • u i)

theorem weightedGramMatrix_apply {m d : ℕ} (p : Fin m → ℝ)
    (u : Fin m → EuclideanSpace ℝ (Fin d)) (i j : Fin m) :
    weightedGramMatrix p u i j = p i * p j * inner ℝ (u i) (u j) := by
  simp only [weightedGramMatrix, gramMatrix, real_inner_smul_left, real_inner_smul_right]
  ring

theorem weighted_opt_le_iff_support {m d : ℕ} (p : Fin m → ℝ)
    (u : Fin m → EuclideanSpace ℝ (Fin d)) (hp : ∀ i, 0 ≤ p i)
    {L : ℝ} (hL : 0 ≤ L) :
    optValue (weightedGramMatrix p u) ≤ L ^ 2 ↔
      ∀ z : EuclideanSpace ℝ (Fin d), ‖z‖ = 1 → ∑ i, p i * |inner ℝ (u i) z| ≤ L := by
  simpa only [real_inner_smul_left, abs_mul, abs_of_nonneg (hp _), weightedGramMatrix] using
    gram_opt_le_iff_support (fun i => p i • u i) hL

theorem weighted_energy_le_sdp {m d : ℕ} (p : Fin m → ℝ)
    (u : Fin m → EuclideanSpace ℝ (Fin d)) (hu : ∀ i, ‖u i‖ = 1) :
    (∑ i, ∑ j, p i * p j * (inner ℝ (u i) (u j)) ^ 2) ≤
      sdpValue (weightedGramMatrix p u) := by
  apply le_csSup (sdpSet_bdd _)
  refine ⟨d, u, u, hu, hu, ?_⟩
  simp_rw [weightedGramMatrix_apply, pow_two, mul_assoc]

/-- Positive weights are absorbed by square roots before applying the trace inequality. -/
theorem mass_sq_le_dimension_mul_weighted_energy {m d : ℕ} (p : Fin m → ℝ)
    (u : Fin m → EuclideanSpace ℝ (Fin d)) (hp : ∀ i, 0 ≤ p i)
    (hu : ∀ i, ‖u i‖ = 1) :
    (∑ i, p i) ^ 2 ≤ (d : ℝ) * ∑ i, ∑ j, p i * p j * (inner ℝ (u i) (u j)) ^ 2 := by
  have h := sum_norm_sq_sq_le_dimension_mul_energy (fun i => Real.sqrt (p i) • u i)
  have hn (i : Fin m) : ‖Real.sqrt (p i) • u i‖ ^ 2 = p i := by
    rw [norm_smul, Real.norm_of_nonneg (Real.sqrt_nonneg _), hu i, mul_one, Real.sq_sqrt (hp i)]
  have hi (i j : Fin m) : (inner ℝ (Real.sqrt (p i) • u i) (Real.sqrt (p j) • u j)) ^ 2 =
      p i * p j * (inner ℝ (u i) (u j)) ^ 2 := by
    rw [real_inner_smul_left, real_inner_smul_right]
    simp only [mul_pow, Real.sq_sqrt (hp _)]
    ring
  simpa only [hn, hi] using h

theorem mass_sq_div_dimension_le_sdp {m d : ℕ} (p : Fin m → ℝ)
    (u : Fin m → EuclideanSpace ℝ (Fin d)) (hd : 0 < d)
    (hp : ∀ i, 0 ≤ p i) (hu : ∀ i, ‖u i‖ = 1) :
    (∑ i, p i) ^ 2 / d ≤ sdpValue (weightedGramMatrix p u) := by
  have hd' : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  apply le_trans _ (weighted_energy_le_sdp p u hu)
  exact (div_le_iff₀ hd').mpr
    (by simpa [mul_comm] using mass_sq_le_dimension_mul_weighted_energy p u hp hu)

theorem one_le_of_isGrothendieckBound {K : ℝ} (hK : IsGrothendieckBound K) : 1 ≤ K := by
  let A : Matrix (Fin 1) (Fin 1) ℝ := fun _ _ => 1
  have hmem : (1 : ℝ) ∈ optSet A := by
    refine ⟨fun _ => 1, fun _ => 1, fun _ => Or.inl rfl, fun _ => Or.inl rfl, ?_⟩
    simp [A]
  have hopt : optValue A = 1 := by
    apply le_antisymm
    · apply csSup_le ⟨1, hmem⟩
      rintro s ⟨x, y, hx, hy, rfl⟩
      simp only [A, Fin.sum_univ_one, one_mul]
      rcases hx 0 with h | h <;> rcases hy 0 with h' | h' <;> rw [h, h'] <;> norm_num
    · exact le_csSup (optSet_bdd A) hmem
  let v : EuclideanSpace ℝ (Fin 1) := WithLp.toLp 2 (fun _ => 1)
  have hv : ‖v‖ = 1 := by simp [v, EuclideanSpace.norm_eq]
  have hsdp : 1 ≤ sdpValue A := by
    apply le_csSup (sdpSet_bdd A)
    refine ⟨1, fun _ => v, fun _ => v, fun _ => hv, fun _ => hv, ?_⟩
    simp [A, hv]
  have h := hK 1 1 A
  rw [hopt, mul_one] at h
  exact hsdp.trans h

/-- A finite weighted spherical cloud certifies a numerical lower bound for every
Grothendieck bound. The proof uses its actual matrix and the trace inequality. -/
theorem weighted_cloud_le_bound {m d : ℕ} (p : Fin m → ℝ)
    (u : Fin m → EuclideanSpace ℝ (Fin d)) (hd : 0 < d)
    (hp : ∀ i, 0 ≤ p i) (hu : ∀ i, ‖u i‖ = 1)
    {L : ℝ} (hL : 0 < L)
    (hsupport : ∀ z : EuclideanSpace ℝ (Fin d), ‖z‖ = 1 →
      ∑ i, p i * |inner ℝ (u i) z| ≤ L)
    {K : ℝ} (hK : IsGrothendieckBound K) :
    (∑ i, p i) ^ 2 / ((d : ℝ) * L ^ 2) ≤ K := by
  have hK0 : 0 ≤ K := le_trans zero_le_one (one_le_of_isGrothendieckBound hK)
  have ho := (weighted_opt_le_iff_support p u hp hL.le).mpr hsupport
  have hlo := mass_sq_div_dimension_le_sdp p u hd hp hu
  have hhi := (hK m m (weightedGramMatrix p u)).trans (mul_le_mul_of_nonneg_left ho hK0)
  have hd' : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  apply (div_le_iff₀ (mul_pos hd' (sq_pos_of_pos hL))).mpr
  have h := (div_le_iff₀ hd').mp (hlo.trans hhi)
  nlinarith

/-- The existing finite upper bound ensures that the infimum is taken over a nonempty set. -/
theorem weighted_cloud_le_constant {m d : ℕ} (p : Fin m → ℝ)
    (u : Fin m → EuclideanSpace ℝ (Fin d)) (hd : 0 < d)
    (hp : ∀ i, 0 ≤ p i) (hu : ∀ i, ‖u i‖ = 1)
    {L : ℝ} (hL : 0 < L)
    (hsupport : ∀ z : EuclideanSpace ℝ (Fin d), ‖z‖ = 1 →
      ∑ i, p i * |inner ℝ (u i) z| ≤ L) :
    (∑ i, p i) ^ 2 / ((d : ℝ) * L ^ 2) ≤ grothendieckConst := by
  apply le_csInf exists_grothendieck_bound
  intro K hK
  exact weighted_cloud_le_bound p u hd hp hu hL hsupport hK

end GrothendieckGeometry

open GrothendieckConstant in
/-- Probability weights yield the lower bound directly in the form needed for cubature. -/
theorem GrothendieckGeometry.probability_weighted_cloud_lower_bound {m d : ℕ} (p : Fin m → ℝ)
    (u : Fin m → EuclideanSpace ℝ (Fin d)) (hd : 0 < d)
    (hp : ∀ i, 0 ≤ p i) (hmass : ∑ i, p i = 1) (hu : ∀ i, ‖u i‖ = 1)
    {L : ℝ} (hL : 0 < L)
    (hsupport : ∀ z : EuclideanSpace ℝ (Fin d), ‖z‖ = 1 →
      ∑ i, p i * |inner ℝ (u i) z| ≤ L) :
    1 / ((d : ℝ) * L ^ 2) ≤ grothendieckConst := by
  simpa only [hmass, one_pow] using
    GrothendieckGeometry.weighted_cloud_le_constant p u hd hp hu hL hsupport
end

/- Uniform finite approximation on the sphere. -/
section
set_option autoImplicit false

open MeasureTheory

namespace GrothendieckDiscretization

abbrev Sphere (d : ℕ) := Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1

noncomputable def supportFunction {d : ℕ} (u : Sphere d) : C(Sphere d, ℝ) :=
  ⟨fun z => |inner ℝ (u : EuclideanSpace ℝ (Fin d)) (z : EuclideanSpace ℝ (Fin d))|,
    by fun_prop⟩

theorem supportFunction_continuous {d : ℕ} : Continuous (@supportFunction d) := by
  have hlip : LipschitzWith 1 (@supportFunction d) := by
    apply LipschitzWith.of_dist_le_mul
    intro u v
    simp only [NNReal.coe_one, one_mul, dist_eq_norm]
    change ‖supportFunction u - supportFunction v‖ ≤
      ‖(u : EuclideanSpace ℝ (Fin d)) - (v : EuclideanSpace ℝ (Fin d))‖
    apply (ContinuousMap.norm_le _ (norm_nonneg _)).2
    intro z
    change ‖|inner ℝ (u : EuclideanSpace ℝ (Fin d)) (z : EuclideanSpace ℝ (Fin d))| -
      |inner ℝ (v : EuclideanSpace ℝ (Fin d)) (z : EuclideanSpace ℝ (Fin d))|‖ ≤ _
    have hz : ‖(z : EuclideanSpace ℝ (Fin d))‖ = 1 := by simp
    calc
      _ ≤ |inner ℝ (u : EuclideanSpace ℝ (Fin d)) (z : EuclideanSpace ℝ (Fin d)) -
        inner ℝ (v : EuclideanSpace ℝ (Fin d)) (z : EuclideanSpace ℝ (Fin d))| :=
          abs_abs_sub_abs_le_abs_sub _ _
      _ = |inner ℝ ((u : EuclideanSpace ℝ (Fin d)) - v) (z : EuclideanSpace ℝ (Fin d))| := by
        rw [inner_sub_left]
      _ ≤ ‖(u : EuclideanSpace ℝ (Fin d)) - v‖ := by
        simpa [hz] using abs_real_inner_le_norm ((u : EuclideanSpace ℝ (Fin d)) - v)
          (z : EuclideanSpace ℝ (Fin d))
  exact hlip.continuous

/-- Approximation in the uniform norm preserves every directional support bound. -/
theorem sphere_discretization {d : ℕ} (μ : Measure (Sphere d)) [IsProbabilityMeasure μ]
    (a : ℝ)
    (ha : ∀ z : EuclideanSpace ℝ (Fin d), ‖z‖ = 1 →
      ∫ u : Sphere d, |inner ℝ (u : EuclideanSpace ℝ (Fin d)) z| ∂μ ≤ a)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (m : ℕ) (p : Fin m → ℝ) (u : Fin m → EuclideanSpace ℝ (Fin d)),
      (∀ i, 0 ≤ p i) ∧ (∑ i, p i = 1) ∧ (∀ i, ‖u i‖ = 1) ∧
      ∀ z : EuclideanSpace ℝ (Fin d), ‖z‖ = 1 →
        ∑ i, p i * |inner ℝ (u i) z| ≤ a + ε := by
  classical
  let F : Sphere d → C(Sphere d, ℝ) := supportFunction
  have hF : Continuous F := supportFunction_continuous
  have hFI : Integrable F μ :=
    hF.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace F)
  have hcl : (∫ u, F u ∂μ) ∈ closure (convexHull ℝ (Set.range F)) :=
    (convex_convexHull ℝ (Set.range F)).closure.integral_mem isClosed_closure
      (Filter.Eventually.of_forall fun u => subset_closure (subset_convexHull ℝ _ (Set.mem_range_self u)))
      hFI
  obtain ⟨f, hf, hdist⟩ := Metric.mem_closure_iff.mp hcl ε hε
  obtain ⟨ι, hι, p, v, hp, hsum, hv, heq⟩ := mem_convexHull_iff_exists_fintype.mp hf
  choose u hu using hv
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  refine ⟨Fintype.card ι, p ∘ e, fun i => u (e i), ?_, ?_, ?_, ?_⟩
  · intro i
    exact hp _
  · simpa only [Function.comp_apply] using (Equiv.sum_comp e p).trans hsum
  · intro i
    simp
  · intro z hz
    let z' : Sphere d := ⟨z, by simpa using hz⟩
    have heval : (∑ i, p i * |inner ℝ (u i : EuclideanSpace ℝ (Fin d)) z|) = f z' := by
      rw [← heq]
      simp only [ContinuousMap.sum_apply, ContinuousMap.smul_apply, smul_eq_mul]
      apply Finset.sum_congr rfl
      intro i hi
      rw [← hu i]
      rfl
    have hbound : f z' ≤ a + ε := by
      have hevaldist := ContinuousMap.dist_apply_le_dist
        (f := ∫ u, F u ∂μ) (g := f) z'
      have hnear : |(∫ u, F u ∂μ) z' - f z'| < ε := by
        exact lt_of_le_of_lt hevaldist hdist
      have hint : (∫ u, F u ∂μ) z' ≤ a := by
        rw [ContinuousMap.integral_apply hFI]
        exact ha z hz
      have := neg_le_abs ((∫ u, F u ∂μ) z' - f z')
      linarith
    change (∑ i, p (e i) * |inner ℝ (u (e i) : EuclideanSpace ℝ (Fin d)) z|) ≤ a + ε
    rw [Equiv.sum_comp e (fun i => p i * |inner ℝ (u i : EuclideanSpace ℝ (Fin d)) z|), heval]
    exact hbound

end GrothendieckDiscretization
end

/- Gaussian norm moments and lower bound. -/
section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace ImpactGrothGaussianNorm

lemma gaussian_integrable_pow (n : ℕ) :
    Integrable (fun x : ℝ ↦ x ^ n) (gaussianReal 0 1) := by
  simpa using integrable_pow_of_mem_interior_integrableExpSet
    (X := id) (μ := gaussianReal 0 1) (by simp) n

lemma gaussian_second : ∫ x : ℝ, x ^ 2 ∂gaussianReal 0 1 = 1 := by
  have h := variance_fun_id_gaussianReal (μ := (0 : ℝ)) (v := (1 : ℝ≥0))
  rw [variance_eq_integral (by fun_prop)] at h
  simpa using h

lemma gaussian_fourth : ∫ x : ℝ, x ^ 4 ∂gaussianReal 0 1 = 3 := by
  have h1 : deriv (fun t : ℝ ↦ Real.exp (t ^ 2 / 2)) =
      fun t ↦ t * Real.exp (t ^ 2 / 2) := by
    ext t
    convert ((((hasDerivAt_id t).pow 2).div_const 2).exp).deriv using 1 <;> first | rfl | (simp only [Pi.pow_apply, id_eq]; ring)
  have h2 : deriv (fun t : ℝ ↦ t * Real.exp (t ^ 2 / 2)) =
      fun t ↦ (1 + t ^ 2) * Real.exp (t ^ 2 / 2) := by
    ext t
    convert ((hasDerivAt_id t).mul ((((hasDerivAt_id t).pow 2).div_const 2).exp)).deriv using 1 <;> first | rfl | (simp only [Pi.pow_apply, id_eq]; ring)
  have h3 : deriv (fun t : ℝ ↦ (1 + t ^ 2) * Real.exp (t ^ 2 / 2)) =
      fun t ↦ (3 * t + t ^ 3) * Real.exp (t ^ 2 / 2) := by
    ext t
    convert (((hasDerivAt_const t 1).add ((hasDerivAt_id t).pow 2)).mul
      ((((hasDerivAt_id t).pow 2).div_const 2).exp)).deriv using 1 <;> first | rfl | (simp only [Pi.pow_apply, Pi.add_apply, id_eq]; ring)
  have h4 : deriv (fun t : ℝ ↦ (3 * t + t ^ 3) * Real.exp (t ^ 2 / 2)) =
      fun t ↦ (3 + 6 * t ^ 2 + t ^ 4) * Real.exp (t ^ 2 / 2) := by
    ext t
    convert ((((hasDerivAt_id t).const_mul 3).add ((hasDerivAt_id t).pow 3)).mul
      ((((hasDerivAt_id t).pow 2).div_const 2).exp)).deriv using 1 <;> first | rfl | (simp only [Pi.pow_apply, Pi.add_apply, id_eq]; ring)
  have hm := iteratedDeriv_mgf_zero (X := fun x : ℝ ↦ x)
    (μ := gaussianReal 0 1) (by simp) 4
  rw [mgf_fun_id_gaussianReal] at hm
  norm_num only [NNReal.coe_one, zero_mul, zero_add, one_mul] at hm
  rw [iteratedDeriv_succ', iteratedDeriv_succ', iteratedDeriv_succ',
    iteratedDeriv_succ', iteratedDeriv_zero, h1, h2, h3, h4] at hm
  simpa using hm.symm

lemma gaussian_square_variance : Var[fun x : ℝ ↦ x ^ 2; gaussianReal 0 1] = 2 := by
  rw [variance_eq_integral (by fun_prop), gaussian_second]
  calc
    _ = ∫ x : ℝ, (x ^ 4 - 2 * x ^ 2) + 1 ∂gaussianReal 0 1 := by
      congr 1
      funext x
      ring
    _ = 2 := by
      rw [integral_add (f := fun x : ℝ ↦ x ^ 4 - 2 * x ^ 2) (g := fun _ ↦ (1 : ℝ)) ((gaussian_integrable_pow 4).sub
        ((gaussian_integrable_pow 2).const_mul 2)) (integrable_const _),
        integral_sub (gaussian_integrable_pow 4) ((gaussian_integrable_pow 2).const_mul 2),
        integral_const_mul, gaussian_fourth, gaussian_second]
      norm_num

lemma gaussian_square_memLp : MemLp (fun x : ℝ ↦ x ^ 2) 2 (gaussianReal 0 1) := by
  apply (memLp_two_iff_integrable_sq (by fun_prop)).2
  simpa only [← pow_mul] using gaussian_integrable_pow 4

lemma norm_pow_integrable (d n : ℕ) :
    Integrable (fun x : EuclideanSpace ℝ (Fin d) ↦ ‖x‖ ^ n) (stdGaussian _) := by
  simpa only [id_eq] using (IsGaussian.memLp_id
    (stdGaussian (EuclideanSpace ℝ (Fin d))) n (by simp)).integrable_norm_pow'

lemma norm_integrable (d : ℕ) :
    Integrable (fun x : EuclideanSpace ℝ (Fin d) ↦ ‖x‖) (stdGaussian _) := by
  simpa using norm_pow_integrable d 1

lemma norm_second (d : ℕ) :
    (∫ x : EuclideanSpace ℝ (Fin d), ‖x‖ ^ 2 ∂stdGaussian _) = d := by
  rw [← map_pi_eq_stdGaussian, integral_map (by fun_prop) (by fun_prop)]
  simp only [EuclideanSpace.real_norm_sq_eq]
  rw [integral_finsetSum]
  · simp only [integral_comp_eval (μ := fun _ : Fin d ↦ gaussianReal 0 1) (by fun_prop : AEStronglyMeasurable
      (fun x : ℝ ↦ x ^ 2) (gaussianReal 0 1)), gaussian_second]
    simp
  · intro i hi
    exact integrable_comp_eval (μ := fun _ : Fin d ↦ gaussianReal 0 1) (i := i) (gaussian_integrable_pow 2)

lemma norm_square_variance (d : ℕ) :
    Var[fun x : EuclideanSpace ℝ (Fin d) ↦ ‖x‖ ^ 2; stdGaussian _] = 2 * d := by
  rw [← map_pi_eq_stdGaussian, variance_map (by fun_prop) (by fun_prop)]
  simp only [Function.comp_def, EuclideanSpace.real_norm_sq_eq]
  have h := variance_sum_pi (ι := Fin d) (μ := fun _ : Fin d ↦ gaussianReal 0 1)
    (fun _ ↦ gaussian_square_memLp)
  have he : (∑ i : Fin d, fun ω : Fin d → ℝ ↦ ω i ^ 2) =
      (fun ω : Fin d → ℝ ↦ ∑ i : Fin d, ω i ^ 2) := by
    funext ω
    simp
  rw [he] at h
  simpa [gaussian_square_variance, mul_comm] using h

lemma norm_fourth (d : ℕ) :
    (∫ x : EuclideanSpace ℝ (Fin d), ‖x‖ ^ 4 ∂stdGaussian _) =
      (d : ℝ) ^ 2 + 2 * d := by
  have hm : MemLp (fun x : EuclideanSpace ℝ (Fin d) ↦ ‖x‖ ^ 2) 2 (stdGaussian _) := by
    apply (memLp_two_iff_integrable_sq (by fun_prop)).2
    simpa only [← pow_mul] using norm_pow_integrable d 4
  have hv := norm_square_variance d
  rw [variance_eq_sub hm, norm_second] at hv
  simp only [Pi.pow_apply, ← pow_mul] at hv
  linarith

lemma polynomial_lower (a s : ℝ) (ha : 0 ≤ a) (hs : 0 ≤ s) :
    3 * s ^ 2 * a ^ 2 - a ^ 4 ≤ 2 * s ^ 3 * a := by
  have h := mul_nonneg (mul_nonneg ha (sq_nonneg (a - s))) (show 0 ≤ a + 2 * s by positivity)
  nlinarith

lemma gaussian_norm_lower (d : ℕ) (hd : 0 < d) :
    Real.sqrt d - 1 / Real.sqrt d ≤
      ∫ x : EuclideanSpace ℝ (Fin d), ‖x‖ ∂stdGaussian _ := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hs : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.2 hd'
  have hs2 : (Real.sqrt (d : ℝ)) ^ 2 = d := Real.sq_sqrt hd'.le
  have h := integral_mono
    (((norm_pow_integrable d 2).const_mul (3 * Real.sqrt (d : ℝ) ^ 2)).sub
      (norm_pow_integrable d 4))
    ((norm_integrable d).const_mul (2 * Real.sqrt (d : ℝ) ^ 3))
    (fun x ↦ polynomial_lower ‖x‖ (Real.sqrt d) (norm_nonneg x) hs.le)
  simp only [Pi.sub_apply] at h
  rw [integral_sub ((norm_pow_integrable d 2).const_mul _) (norm_pow_integrable d 4),
    integral_const_mul, integral_const_mul, norm_second, norm_fourth, hs2] at h
  have hs3 : Real.sqrt (d : ℝ) ^ 3 = d * Real.sqrt d := by
    rw [pow_succ, hs2]
  rw [hs3] at h
  have h' : (d : ℝ) - 1 ≤ Real.sqrt d *
      ∫ x : EuclideanSpace ℝ (Fin d), ‖x‖ ∂stdGaussian _ := by
    nlinarith
  apply (mul_le_mul_iff_left₀ hs).mp
  rw [sub_mul, div_mul_cancel₀ _ hs.ne']
  nlinarith

lemma gaussian_norm_pos (d : ℕ) (hd : 0 < d) :
    0 < ∫ x : EuclideanSpace ℝ (Fin d), ‖x‖ ∂stdGaussian _ := by
  have hn : 0 ≤ ∫ x : EuclideanSpace ℝ (Fin d), ‖x‖ ∂stdGaussian _ :=
    integral_nonneg (fun x ↦ norm_nonneg x)
  apply lt_of_le_of_ne hn
  intro h
  have hz := (integral_eq_zero_iff_of_nonneg (fun x : EuclideanSpace ℝ (Fin d) ↦ norm_nonneg x)
    (norm_integrable d)).1 h.symm
  have h2 : (∫ x : EuclideanSpace ℝ (Fin d), ‖x‖ ^ 2 ∂stdGaussian _) = 0 := by
    calc
      _ = ∫ x : EuclideanSpace ℝ (Fin d), (0 : ℝ) ∂stdGaussian _ := by
        apply integral_congr_ae
        filter_upwards [hz] with x hx
        simp only [Pi.zero_apply] at hx
        simp [hx]
      _ = 0 := integral_zero _ _
  rw [norm_second] at h2
  have : (0 : ℝ) < d := by exact_mod_cast hd
  linarith

lemma gaussian_norm_sq_lower (d : ℕ) (hd : 0 < d) :
    (d : ℝ) - 2 ≤ (∫ x : EuclideanSpace ℝ (Fin d), ‖x‖ ∂stdGaussian _) ^ 2 := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hs : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.2 hd'
  have h := mul_le_mul_of_nonneg_right (gaussian_norm_lower d hd) hs.le
  rw [sub_mul, div_mul_cancel₀ _ hs.ne'] at h
  have hs2 : (Real.sqrt (d : ℝ)) ^ 2 = d := Real.sq_sqrt hd'.le
  nlinarith [sq_nonneg ((∫ x : EuclideanSpace ℝ (Fin d), ‖x‖ ∂stdGaussian _) -
    Real.sqrt (d : ℝ))]

end ImpactGrothGaussianNorm
end

/- Radially weighted Gaussian directions. -/
section
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology NNReal ENNReal

namespace ImpactGrothGaussianSphere

lemma integral_mul_gaussian_Ioi :
    ∫ x : ℝ in Ioi 0, x * Real.exp (-(1 / 2 : ℝ) * x ^ 2) = 1 := by
  have h := integral_mul_cexp_neg_mul_sq (b := (1 / 2 : ℂ)) (by norm_num)
  have hi := (integrable_mul_cexp_neg_mul_sq (b := (1 / 2 : ℂ)) (by norm_num)).integrableOn (s := Ioi 0)
  have hr := congrArg (RCLike.re : ℂ → ℝ) h
  rw [← integral_re hi] at hr
  convert hr using 1 <;>
    norm_num [← Complex.ofReal_pow, Complex.exp_re, Complex.mul_re, Complex.mul_im]

lemma integral_abs_gaussianReal :
    ∫ x : ℝ, |x| ∂gaussianReal 0 1 = Real.sqrt (2 / Real.pi) := by
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0)]
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero, smul_eq_mul]
  have he : (fun x : ℝ => (Real.sqrt (2 * Real.pi))⁻¹ *
      Real.exp (-(x ^ 2) / 2) * |x|) =
      (fun x : ℝ => (Real.sqrt (2 * Real.pi))⁻¹ *
        (|x| * Real.exp (-(1 / 2 : ℝ) * |x| ^ 2))) := by
    ext x
    rw [sq_abs]
    rw [show -(x ^ 2) / 2 = -(1 / 2 : ℝ) * x ^ 2 by ring]
    ring
  rw [he, integral_const_mul,
    integral_comp_abs (f := fun x : ℝ => x * Real.exp (-(1 / 2 : ℝ) * x ^ 2)),
    integral_mul_gaussian_Ioi]
  have hp : 0 < Real.pi := Real.pi_pos
  have hs := Real.sq_sqrt (show 0 ≤ 2 * Real.pi by positivity)
  have ht := Real.sq_sqrt (show 0 ≤ 2 / Real.pi by positivity)
  have hsp : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  have htp : 0 < Real.sqrt (2 / Real.pi) := Real.sqrt_pos.2 (by positivity)
  have hprod : Real.sqrt (2 * Real.pi) * Real.sqrt (2 / Real.pi) = 2 := by
    rw [← Real.sqrt_mul (by positivity)]
    field_simp
    norm_num
  field_simp
  nlinarith

lemma integral_abs_inner_stdGaussian {d : ℕ}
    (z : EuclideanSpace ℝ (Fin d)) (hz : ‖z‖ = 1) :
    ∫ x, |inner ℝ x z| ∂stdGaussian (EuclideanSpace ℝ (Fin d)) =
      Real.sqrt (2 / Real.pi) := by
  let L : StrongDual ℝ (EuclideanSpace ℝ (Fin d)) := innerSL ℝ z
  have hL : ‖L‖ = 1 := by simp [L, hz]
  have hm : (stdGaussian (EuclideanSpace ℝ (Fin d))).map L = gaussianReal 0 1 := by
    rw [IsGaussian.map_eq_gaussianReal, integral_strongDual_stdGaussian,
      variance_dual_stdGaussian, hL]
    norm_num
  rw [← integral_abs_gaussianReal, ← hm, integral_map (by fun_prop) (by fun_prop)]
  congr 1
  ext x
  simp [L, real_inner_comm]

abbrev Sphere (d : ℕ) := Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1

noncomputable def direction {d : ℕ} (e : Sphere d)
    (x : EuclideanSpace ℝ (Fin d)) : Sphere d :=
  ⟨if x = 0 then (e : EuclideanSpace ℝ (Fin d)) else ‖x‖⁻¹ • x, by
    split_ifs with hx
    · exact e.property
    · simp [norm_smul, norm_ne_zero_iff.mpr hx]⟩

lemma measurable_direction {d : ℕ} (e : Sphere d) : Measurable (direction e) := by
  apply Measurable.subtype_mk
  exact Measurable.ite (measurableSet_singleton 0) measurable_const
    (measurable_norm.inv.smul measurable_id)

lemma weighted_direction_identity {d : ℕ} (e : Sphere d)
    (x z : EuclideanSpace ℝ (Fin d)) (r : ℝ) :
    (‖x‖ / r) * |inner ℝ (direction e x : EuclideanSpace ℝ (Fin d)) z| =
      |inner ℝ x z| / r := by
  by_cases hx : x = 0
  · simp [hx]
  · simp only [direction, hx, if_false, real_inner_smul_left, abs_mul,
      abs_inv, abs_norm]
    field_simp [norm_ne_zero_iff.mpr hx]

/-- Radial weighting transfers Gaussian first moments to a probability measure on the sphere. -/
lemma exists_sphere_measure {d : ℕ} (e : Sphere d)
    (hr : 0 < ∫ x : EuclideanSpace ℝ (Fin d), ‖x‖ ∂stdGaussian _) :
    ∃ μ : Measure (Sphere d), IsProbabilityMeasure μ ∧
      ∀ z : EuclideanSpace ℝ (Fin d), ‖z‖ = 1 →
        ∫ u : Sphere d, |inner ℝ (u : EuclideanSpace ℝ (Fin d)) z| ∂μ =
          Real.sqrt (2 / Real.pi) /
            (∫ x : EuclideanSpace ℝ (Fin d), ‖x‖ ∂stdGaussian _) := by
  let r := ∫ x : EuclideanSpace ℝ (Fin d), ‖x‖ ∂stdGaussian _
  let ν := (stdGaussian (EuclideanSpace ℝ (Fin d))).withDensity
    (fun x => ENNReal.ofReal (‖x‖ / r))
  have hnorm : Integrable (fun x : EuclideanSpace ℝ (Fin d) => ‖x‖) (stdGaussian _) :=
    IsGaussian.integrable_id.norm
  have hν : IsProbabilityMeasure ν := by
    constructor
    change ((stdGaussian _).withDensity (fun x => ENNReal.ofReal (‖x‖ / r))) univ = 1
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal (hnorm.div_const r)
        (Filter.Eventually.of_forall fun x => div_nonneg (norm_nonneg x) hr.le),
      integral_div]
    change ENNReal.ofReal (r / r) = 1
    rw [div_self hr.ne', ENNReal.ofReal_one]
  let μ := ν.map (direction e)
  have hμ : IsProbabilityMeasure μ := by
    let _ := hν
    exact Measure.isProbabilityMeasure_map (measurable_direction e).aemeasurable
  refine ⟨μ, hμ, ?_⟩
  intro z hz
  change ∫ u : Sphere d, |inner ℝ (u : EuclideanSpace ℝ (Fin d)) z|
    ∂ν.map (direction e) = _
  rw [integral_map (measurable_direction e).aemeasurable (by fun_prop)]
  change ∫ x, |inner ℝ (direction e x : EuclideanSpace ℝ (Fin d)) z|
    ∂(stdGaussian _).withDensity (fun x => ENNReal.ofReal (‖x‖ / r)) = _
  rw [integral_withDensity_eq_integral_toReal_smul (by fun_prop)
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  calc
    _ = ∫ x : EuclideanSpace ℝ (Fin d), |inner ℝ x z| / r ∂stdGaussian _ := by
      apply integral_congr_ae
      filter_upwards with x
      rw [ENNReal.toReal_ofReal (div_nonneg (norm_nonneg x) hr.le), smul_eq_mul]
      exact weighted_direction_identity e x z r
    _ = _ := by rw [integral_div, integral_abs_inner_stdGaussian z hz]


end ImpactGrothGaussianSphere
end

/- Passage to the classical constant. -/
section
set_option autoImplicit false

namespace GrothendieckGeometry
open GrothendieckConstant Filter Topology MeasureTheory

/-- Vanishing cubature error can be removed at a fixed positive support coefficient. -/
theorem lower_bound_of_approximate_clouds {d : ℕ} (hd : 0 < d) {a : ℝ} (ha : 0 < a)
    (hcloud : ∀ ε : ℝ, 0 < ε → ∃ m : ℕ, ∃ p : Fin m → ℝ,
      ∃ u : Fin m → EuclideanSpace ℝ (Fin d),
      (∀ i, 0 ≤ p i) ∧ (∑ i, p i) = 1 ∧ (∀ i, ‖u i‖ = 1) ∧
      (∀ z : EuclideanSpace ℝ (Fin d), ‖z‖ = 1 →
        ∑ i, p i * |inner ℝ (u i) z| ≤ a + ε)) :
    1 / ((d : ℝ) * a ^ 2) ≤ grothendieckConst := by
  have hd' : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have heps : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hlim : Tendsto (fun n : ℕ => 1 / ((d : ℝ) * (a + 1 / ((n : ℝ) + 1)) ^ 2))
      atTop (𝓝 (1 / ((d : ℝ) * a ^ 2))) := by
    simpa only [add_zero] using! (tendsto_const_nhds (x := (1 : ℝ))).div
      ((tendsto_const_nhds (x := (d : ℝ))).mul
        (((tendsto_const_nhds (x := a)).add heps).pow 2))
      (show (d : ℝ) * (a + 0) ^ 2 ≠ 0 by positivity)
  apply le_of_tendsto' hlim
  intro n
  have hε : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  obtain ⟨m, p, u, hp, hmass, hu, hs⟩ := hcloud _ hε
  simpa only [hmass, one_pow] using
    weighted_cloud_le_constant p u hd hp hu (add_pos ha hε) hs

theorem sqrt_dimension_gap_pos {d : ℕ} (hd : 2 ≤ d) :
    0 < Real.sqrt (d : ℝ) - 1 / Real.sqrt (d : ℝ) := by
  have hd' : (1 : ℝ) < d := by exact_mod_cast (by omega : 1 < d)
  have hs : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.2 (by linarith)
  apply sub_pos.mpr
  apply (div_lt_iff₀ hs).mpr
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ d by positivity)]

theorem gaussian_support_coefficient_pos {d : ℕ} (hd : 2 ≤ d) :
    0 < Real.sqrt (2 / Real.pi) / (Real.sqrt (d : ℝ) - 1 / Real.sqrt (d : ℝ)) := by
  exact div_pos (Real.sqrt_pos.2 (div_pos (by norm_num) Real.pi_pos)) (sqrt_dimension_gap_pos hd)

theorem gaussian_cloud_bound_identity {d : ℕ} (hd : 2 ≤ d) :
    1 / ((d : ℝ) *
      (Real.sqrt (2 / Real.pi) / (Real.sqrt (d : ℝ) - 1 / Real.sqrt (d : ℝ))) ^ 2) =
      (Real.pi / 2) * (1 - 1 / (d : ℝ)) ^ 2 := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hs : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.2 hd'
  have hs2 := Real.sq_sqrt hd'.le
  have hp := Real.pi_pos
  rw [div_pow, Real.sq_sqrt (div_nonneg (by norm_num) hp.le)]
  have hgap : Real.sqrt (d : ℝ) - 1 / Real.sqrt (d : ℝ) ≠ 0 :=
    ne_of_gt (sqrt_dimension_gap_pos hd)
  field_simp
  rw [hs2]

/-- The explicit dimension-dependent cloud bounds converge to the classical constant. -/
theorem pi_div_two_le_of_gaussian_clouds
    (hcloud : ∀ d : ℕ, 2 ≤ d → ∀ ε : ℝ, 0 < ε →
      ∃ m : ℕ, ∃ p : Fin m → ℝ, ∃ u : Fin m → EuclideanSpace ℝ (Fin d),
      (∀ i, 0 ≤ p i) ∧ (∑ i, p i) = 1 ∧ (∀ i, ‖u i‖ = 1) ∧
      (∀ z : EuclideanSpace ℝ (Fin d), ‖z‖ = 1 →
        ∑ i, p i * |inner ℝ (u i) z| ≤
          Real.sqrt (2 / Real.pi) / (Real.sqrt (d : ℝ) - 1 / Real.sqrt (d : ℝ)) + ε)) :
    Real.pi / 2 ≤ grothendieckConst := by
  have hdim (d : ℕ) (hd : 2 ≤ d) : (Real.pi / 2) * (1 - 1 / (d : ℝ)) ^ 2 ≤
      grothendieckConst := by
    rw [← gaussian_cloud_bound_identity hd]
    exact lower_bound_of_approximate_clouds (by omega) (gaussian_support_coefficient_pos hd)
      (hcloud d hd)
  have hinv : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 2)) atTop (𝓝 0) :=
    by simpa using ((tendsto_add_atTop_iff_nat 2).2
      (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)))
  have hlim : Tendsto (fun n : ℕ => (Real.pi / 2) * (1 - 1 / ((n : ℝ) + 2)) ^ 2)
      atTop (𝓝 (Real.pi / 2)) := by
    convert tendsto_const_nhds.mul ((tendsto_const_nhds.sub hinv).pow 2) using 1
    norm_num
  apply le_of_tendsto' hlim
  intro n
  simpa only [Nat.cast_add, Nat.cast_ofNat] using hdim (n + 2) (by omega)

/-- The finite matrix construction extends to probability measures on the sphere
through approximation in the uniform norm. -/
theorem lower_bound_of_spherical_measure {d : ℕ} (hd : 0 < d)
    (μ : Measure (GrothendieckDiscretization.Sphere d)) [IsProbabilityMeasure μ]
    {a : ℝ} (ha : 0 < a)
    (hsupport : ∀ z : EuclideanSpace ℝ (Fin d), ‖z‖ = 1 →
      ∫ u : GrothendieckDiscretization.Sphere d,
        |inner ℝ (u : EuclideanSpace ℝ (Fin d)) z| ∂μ ≤ a) :
    1 / ((d : ℝ) * a ^ 2) ≤ grothendieckConst := by
  apply lower_bound_of_approximate_clouds hd ha
  intro ε hε
  exact GrothendieckDiscretization.sphere_discretization μ a hsupport ε hε

/-- Probability measures with the explicit Gaussian directional bound suffice for
Grothendieck's classical lower bound. -/
theorem pi_div_two_le_of_spherical_measures
    (hmeasure : ∀ d : ℕ, 2 ≤ d →
      ∃ μ : Measure (GrothendieckDiscretization.Sphere d), IsProbabilityMeasure μ ∧
      ∀ z : EuclideanSpace ℝ (Fin d), ‖z‖ = 1 →
        ∫ u : GrothendieckDiscretization.Sphere d,
          |inner ℝ (u : EuclideanSpace ℝ (Fin d)) z| ∂μ ≤
            Real.sqrt (2 / Real.pi) / (Real.sqrt (d : ℝ) - 1 / Real.sqrt (d : ℝ))) :
    Real.pi / 2 ≤ grothendieckConst := by
  apply pi_div_two_le_of_gaussian_clouds
  intro d hd ε hε
  obtain ⟨μ, hμ, hs⟩ := hmeasure d hd
  let := hμ
  exact GrothendieckDiscretization.sphere_discretization μ _ hs ε hε

end GrothendieckGeometry
end

theorem solution : Real.pi / 2 ≤ GrothendieckConstant.grothendieckConst := by
  apply GrothendieckGeometry.pi_div_two_le_of_spherical_measures
  intro d hd
  have hd0 : 0 < d := by omega
  let e : ImpactGrothGaussianSphere.Sphere d :=
    ⟨EuclideanSpace.single ⟨0, hd0⟩ 1, by simp⟩
  obtain ⟨μ, hμ, hs⟩ := ImpactGrothGaussianSphere.exists_sphere_measure e
    (ImpactGrothGaussianNorm.gaussian_norm_pos d hd0)
  refine ⟨μ, hμ, ?_⟩
  intro z hz
  rw [hs z hz]
  exact div_le_div_of_nonneg_left (Real.sqrt_nonneg _)
    (GrothendieckGeometry.sqrt_dimension_gap_pos hd)
    (ImpactGrothGaussianNorm.gaussian_norm_lower d hd0)
