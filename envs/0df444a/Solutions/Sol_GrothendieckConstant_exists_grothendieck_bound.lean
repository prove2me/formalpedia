-- Prove2me | solution 1 for GrothendieckConstant.exists_grothendieck_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-24T20:40:42.004875+00:00
-- url     : https://prove2.me/submissions/f260128e-39ad-469d-96d6-7bf32941862c

import Mathlib
import Definitions.Def_GrothendieckConstantDefs

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
theorem solution : ∃ K : ℝ, IsGrothendieckBound K := by
  refine ⟨98, fun m n A => ?_⟩
  have h : sdpValue A ≤ 49 * optValue A + (1 / 2) * sdpValue A :=
    csSup_le (GrothendieckAux.sdpSet_nonempty A) (fun s hs => GrothendieckAux.main_bound A s hs)
  linarith
