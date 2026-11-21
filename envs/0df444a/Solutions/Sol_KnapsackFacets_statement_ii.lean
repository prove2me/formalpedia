-- Prove2me | solution 1 for KnapsackFacets.statement_ii
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-20T23:54:35.322911+00:00
-- url     : https://prove2.me/submissions/d1ea7922-4d32-40ee-82a3-7a37d153814a

import Definitions.Def_KnapsackFacets_KnapsackPolytope
import Definitions.Def_KnapsackFacets_Reduction

set_option autoImplicit false

namespace Aux_KFs2
open KnapsackFacets

theorem frec (k : ℕ) (hk : 2 ≤ k) :
    shiftedFib (k + 2) = shiftedFib k + shiftedFib (k + 1) := by
  obtain ⟨i, rfl⟩ : ∃ i, k = i + 2 := ⟨k - 2, by omega⟩
  show shiftedFib (i + 4) = shiftedFib (i + 2) + shiftedFib (i + 3)
  rfl

noncomputable def F (c : ℕ) : ℝ := (shiftedFib (c + 1) : ℝ)

noncomputable def T (N : ℕ) (g : ℕ → ℝ) : ℝ := ∑ c ∈ Finset.range N, F c * g c

noncomputable def ind (a c : ℕ) : ℝ := if c = a then 1 else 0

noncomputable def D : ℕ → ℕ → ℝ
  | 0, c => ind 0 c - ind 1 c
  | 1, c => ind 1 c - ind 2 c
  | k + 2, c => ind (k + 1) c + ind (k + 2) c - ind (k + 3) c

theorem T_add (N : ℕ) (g h : ℕ → ℝ) : T N (fun c => g c + h c) = T N g + T N h := by
  unfold T
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun c _ => by ring)

theorem T_sub (N : ℕ) (g h : ℕ → ℝ) : T N (fun c => g c - h c) = T N g - T N h := by
  unfold T
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun c _ => by ring)

theorem T_ind (N a : ℕ) (ha : a < N) : T N (ind a) = F a := by
  unfold T ind
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hb
    simp [hb]
  · intro h
    exact absurd (Finset.mem_range.mpr ha) h

theorem T_congr (N : ℕ) (g h : ℕ → ℝ) (hgh : ∀ c, g c = h c) : T N g = T N h := by
  unfold T
  exact Finset.sum_congr rfl (fun c _ => by rw [hgh c])

theorem T_D (N k : ℕ) (hk : k + 2 ≤ N) : T N (D k) = 0 := by
  rcases k with _ | _ | k
  · show T N (fun c => ind 0 c - ind 1 c) = 0
    rw [T_sub, T_ind N 0 (by omega), T_ind N 1 (by omega)]
    simp [F, shiftedFib]
  · show T N (fun c => ind 1 c - ind 2 c) = 0
    rw [T_sub, T_ind N 1 (by omega), T_ind N 2 (by omega)]
    simp [F, shiftedFib]
  · show T N (fun c => ind (k + 1) c + ind (k + 2) c - ind (k + 3) c) = 0
    rw [T_sub, T_add, T_ind N (k + 1) (by omega), T_ind N (k + 2) (by omega),
      T_ind N (k + 3) (by omega)]
    have h' : F (k + 1) + F (k + 2) = F (k + 3) := by
      unfold F
      exact_mod_cast (frec (k + 2) (by omega)).symm
    linarith

theorem D_ge (k : ℕ) (hk : 2 ≤ k) (c : ℕ) :
    D k c = ind (k - 1) c + ind k c - ind (k + 1) c := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  rw [show j + 2 - 1 = j + 1 by omega]
  rfl

theorem D_zero (k c : ℕ) (h : k + 1 < c) : D k c = 0 := by
  rcases k with _ | _ | k
  · show ind 0 c - ind 1 c = 0
    unfold ind
    rw [if_neg (by omega), if_neg (by omega)]
    ring
  · show ind 1 c - ind 2 c = 0
    unfold ind
    rw [if_neg (by omega), if_neg (by omega)]
    ring
  · show ind (k + 1) c + ind (k + 2) c - ind (k + 3) c = 0
    unfold ind
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    ring

theorem D_piv (k : ℕ) : D k (k + 1) = -1 := by
  rcases k with _ | _ | k
  · show ind 0 1 - ind 1 1 = -1
    unfold ind
    rw [if_neg (by omega), if_pos rfl]
    ring
  · show ind 1 2 - ind 2 2 = -1
    unfold ind
    rw [if_neg (by omega), if_pos rfl]
    ring
  · show ind (k + 1) (k + 3) + ind (k + 2) (k + 3) - ind (k + 3) (k + 3) = -1
    unfold ind
    rw [if_neg (by omega), if_neg (by omega), if_pos rfl]
    ring

/-- the points `X_m`, `V_s` (fibonacci index `c+1`) -/
noncomputable def gX (m c : ℕ) : ℝ :=
  if c + 1 ≤ 2 * m ∨ ((c + 1) % 2 = 1 ∧ 2 * m + 3 ≤ c + 1) then 1 else 0

noncomputable def gV (s c : ℕ) : ℝ :=
  if c + 1 = 2 * s ∨ ((c + 1) % 2 = 1 ∧ 2 * s + 1 ≤ c + 1) then 1 else 0

theorem gX_01 (m c : ℕ) : gX m c = 0 ∨ gX m c = 1 := by
  unfold gX
  split_ifs <;> simp

theorem gV_01 (s c : ℕ) : gV s c = 0 ∨ gV s c = 1 := by
  unfold gV
  split_ifs <;> simp

theorem relX (m : ℕ) (hm : 1 ≤ m) (c : ℕ) : gX (m + 1) c = gX m c + D (2 * m + 1) c := by
  rw [D_ge (2 * m + 1) (by omega)]
  unfold gX ind
  split_ifs <;> first | (exfalso; omega) | (norm_num; done) | (exfalso; simp only [false_or, or_false] at *; omega) | simp_all

theorem relX1 (c : ℕ) : gX 1 c = gV 0 c + D 1 c := by
  show gX 1 c = gV 0 c + (ind 1 c - ind 2 c)
  unfold gX gV ind
  split_ifs <;> first | (exfalso; omega) | (norm_num; done) | (exfalso; simp only [false_or, or_false] at *; omega) | simp_all

theorem relV0 (c : ℕ) : gV 0 c = gV 1 c + D 0 c := by
  show gV 0 c = gV 1 c + (ind 0 c - ind 1 c)
  unfold gV ind
  split_ifs <;> first | (exfalso; omega) | (norm_num; done) | (exfalso; simp only [false_or, or_false] at *; omega) | simp_all

theorem relV (s : ℕ) (hs : 1 ≤ s) (c : ℕ) : gV s c = gV (s + 1) c + D (2 * s) c := by
  rw [D_ge (2 * s) (by omega)]
  unfold gV ind
  split_ifs <;> first | (exfalso; omega) | (norm_num; done) | (exfalso; simp only [false_or, or_false] at *; omega) | simp_all

theorem T_rel (N k : ℕ) (hk : k + 2 ≤ N) (P Q : ℕ → ℝ) (h : ∀ c, P c = Q c + D k c) :
    T N P = T N Q := by
  rw [T_congr N P (fun c => Q c + D k c) h, T_add, T_D N k hk, add_zero]

theorem T_Xr (r : ℕ) :
    T (2 * r + 1) (gX r) = ((∑ i ∈ Finset.Icc 1 (2 * r), shiftedFib i : ℕ) : ℝ) := by
  unfold T
  rw [Finset.sum_range_succ]
  have h1 : gX r (2 * r) = 0 := by
    unfold gX
    rw [if_neg (by omega)]
  have h2 : ∑ c ∈ Finset.range (2 * r), F c * gX r c = ∑ c ∈ Finset.range (2 * r), F c := by
    apply Finset.sum_congr rfl
    intro c hc
    rw [Finset.mem_range] at hc
    unfold gX
    rw [if_pos (Or.inl (by omega)), mul_one]
  rw [h1, mul_zero, add_zero, h2]
  have hI : Finset.Icc 1 (2 * r) = Finset.Ico 1 (2 * r + 1) := by
    ext a
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    constructor <;> intro h <;> omega
  rw [hI, Finset.sum_Ico_eq_sum_range]
  push_cast
  try rw [show 2 * r + 1 - 1 = 2 * r by omega]
  exact Finset.sum_congr rfl (fun j _ => by unfold F; rw [add_comm])

theorem T_X (r : ℕ) (m : ℕ) (hm1 : 1 ≤ m) (hmr : m ≤ r) :
    T (2 * r + 1) (gX m) = ((∑ i ∈ Finset.Icc 1 (2 * r), shiftedFib i : ℕ) : ℝ) := by
  obtain ⟨d, hd⟩ : ∃ d, r = m + d := ⟨r - m, by omega⟩
  induction d generalizing m with
  | zero =>
    rw [add_zero] at hd
    subst hd
    exact T_Xr _
  | succ d ih =>
    rw [← ih (m + 1) (by omega) (by omega) (by omega)]
    exact (T_rel (2 * r + 1) (2 * m + 1) (by omega) _ _ (relX m hm1)).symm

theorem T_V (r : ℕ) (hr : 1 ≤ r) (s : ℕ) (hsr : s ≤ r) :
    T (2 * r + 1) (gV s) = ((∑ i ∈ Finset.Icc 1 (2 * r), shiftedFib i : ℕ) : ℝ) := by
  have h0 : T (2 * r + 1) (gV 0) = ((∑ i ∈ Finset.Icc 1 (2 * r), shiftedFib i : ℕ) : ℝ) := by
    rw [← T_X r 1 le_rfl hr]
    exact (T_rel (2 * r + 1) 1 (by omega) _ _ relX1).symm
  have h1 : T (2 * r + 1) (gV 1) = ((∑ i ∈ Finset.Icc 1 (2 * r), shiftedFib i : ℕ) : ℝ) := by
    rw [← h0]
    exact (T_rel (2 * r + 1) 0 (by omega) _ _ relV0).symm
  induction s with
  | zero => exact h0
  | succ s ih =>
    rcases Nat.eq_zero_or_pos s with hs | hs
    · subst hs
      exact h1
    · rw [← ih (by omega)]
      exact (T_rel (2 * r + 1) (2 * s) (by omega) _ _ (relV s hs)).symm

theorem tri_li (K : ℕ) (u : Fin K → Fin (K + 1) → ℝ)
    (hz : ∀ k : Fin K, ∀ c : Fin (K + 1), k.val + 1 < c.val → u k c = 0)
    (hp : ∀ k : Fin K, u k ⟨k.val + 1, Nat.succ_lt_succ k.isLt⟩ ≠ 0) : LinearIndependent ℝ u := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have key : ∀ d : ℕ, ∀ k : Fin K, K - 1 - k.val = d → g k = 0 := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro k hk
      have hc := congrFun hg ⟨k.val + 1, Nat.succ_lt_succ k.isLt⟩
      rw [Finset.sum_apply] at hc
      simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hc
      rw [Finset.sum_eq_single k] at hc
      · exact (mul_eq_zero.mp hc).resolve_right (hp k)
      · intro j _ hjk
        rcases lt_or_gt_of_ne hjk with hlt | hgt
        · have hlt' := Fin.lt_iff_val_lt_val.mp hlt
          rw [hz j ⟨k.val + 1, Nat.succ_lt_succ k.isLt⟩ (by show j.val + 1 < k.val + 1; omega)]
          ring
        · have hgt' := Fin.lt_iff_val_lt_val.mp hgt
          have hjK := j.isLt
          rw [ih (K - 1 - j.val) (by omega) j rfl]
          ring
      · intro h
        exact absurd (Finset.mem_univ k) h
  intro k
  exact key _ k rfl

theorem fib_le (r : ℕ) (hr : 1 ≤ r) (i : ℕ) (hi : i < 2 * r + 1) :
    shiftedFib (i + 1) ≤ ∑ j ∈ Finset.Icc 1 (2 * r), shiftedFib j := by
  by_cases h : i + 1 ≤ 2 * r
  · exact Finset.single_le_sum (f := shiftedFib) (fun _ _ => Nat.zero_le _)
      (Finset.mem_Icc.mpr ⟨by omega, h⟩)
  · have hi' : i + 1 = 2 * r + 1 := by omega
    rw [hi']
    have h1 : shiftedFib (2 * r + 1) ≤ shiftedFib (2 * r - 1) + shiftedFib (2 * r) := by
      rcases Nat.lt_or_ge r 2 with hr2 | hr2
      · have : r = 1 := by omega
        subst this
        decide
      · have := frec (2 * r - 1) (by omega)
        rw [show 2 * r - 1 + 2 = 2 * r + 1 by omega, show 2 * r - 1 + 1 = 2 * r by omega] at this
        omega
    have h2 : shiftedFib (2 * r - 1) + shiftedFib (2 * r) =
        ∑ j ∈ ({2 * r - 1, 2 * r} : Finset ℕ), shiftedFib j := by
      rw [Finset.sum_pair (by omega)]
    have h3 : ∑ j ∈ ({2 * r - 1, 2 * r} : Finset ℕ), shiftedFib j ≤
        ∑ j ∈ Finset.Icc 1 (2 * r), shiftedFib j := by
      apply Finset.sum_le_sum_of_subset
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rw [Finset.mem_Icc]
      omega
    omega

section coef
variable {n : ℕ} (w : Fin n → ℕ) (t : ℕ)

theorem cA1 (j : ℕ) (hj : j < 2 * redR w + 1) :
    aCoef w t (j + 1) = t * shiftedFib (j + 1) := by
  unfold aCoef
  rw [if_pos ⟨by omega, by omega⟩]

theorem cA2 : aCoef w t (2 * redR w + 1 + 1) = t * (2 * redL w + 1) + 1 := by
  unfold aCoef
  rw [if_neg (fun h => by omega), if_pos (by omega)]

theorem cA3 (k : ℕ) (hk : k < n) :
    aCoef w t (2 * redR w + 2 + k + 1) = (t + 1) * wAt w k := by
  unfold aCoef
  rw [if_neg (fun h => by omega), if_neg (by omega), if_pos ⟨by omega, by omega⟩,
    show 2 * redR w + 2 + k + 1 - (2 * redR w + 3) = k by omega]

theorem cA4 : aCoef w t (2 * redR w + n + 2 + 1) =
    t * shiftedFib (2 * redR w + 1) + t ^ 2 + t * (2 * redL w + 2) + 1 := by
  unfold aCoef
  rw [if_neg (fun h => by omega), if_neg (by omega), if_neg (fun h => by omega),
    if_pos (by omega)]

theorem cA5 : aCoef w t (2 * redR w + n + 3 + 1) = t + 1 := by
  unfold aCoef
  rw [if_neg (fun h => by omega), if_neg (by omega), if_neg (fun h => by omega),
    if_neg (by omega), if_pos (by omega)]

theorem cB1 (j : ℕ) (hj : j < 2 * redR w + 1) :
    alphaCoef w t (j + 1) = shiftedFib (j + 1) := by
  unfold alphaCoef
  rw [if_pos ⟨by omega, by omega⟩]

theorem cB2 : alphaCoef w t (2 * redR w + 1 + 1) = 2 * redL w + 2 := by
  unfold alphaCoef
  rw [if_neg (fun h => by omega), if_pos (by omega)]

theorem cB3 (k : ℕ) (hk : k < n) :
    alphaCoef w t (2 * redR w + 2 + k + 1) = wAt w k := by
  unfold alphaCoef
  rw [if_neg (fun h => by omega), if_neg (by omega), if_pos ⟨by omega, by omega⟩,
    show 2 * redR w + 2 + k + 1 - (2 * redR w + 3) = k by omega]

theorem cB4 : alphaCoef w t (2 * redR w + n + 2 + 1) =
    shiftedFib (2 * redR w + 1) + t + 2 * redL w + 1 := by
  unfold alphaCoef
  rw [if_neg (fun h => by omega), if_neg (by omega), if_neg (fun h => by omega),
    if_pos (by omega)]

theorem cB5 : alphaCoef w t (2 * redR w + n + 3 + 1) = 0 := by
  unfold alphaCoef
  rw [if_neg (fun h => by omega), if_neg (by omega), if_neg (fun h => by omega),
    if_neg (by omega)]

end coef

def pt {N : ℕ} (g : ℕ → ℝ) : Fin N → ℝ := fun i => g i.val

noncomputable def ext {N : ℕ} (x : Fin N → ℝ) (c : ℕ) : ℝ := if h : c < N then x ⟨c, h⟩ else 0

theorem ext_pt {N : ℕ} (x : Fin N → ℝ) : (pt (ext x) : Fin N → ℝ) = x := by
  funext i
  simp [pt, ext, i.isLt]

theorem ext_01 {N : ℕ} {x : Fin N → ℝ} (h01 : ∀ i, x i = 0 ∨ x i = 1) (c : ℕ) :
    ext x c = 0 ∨ ext x c = 1 := by
  unfold ext
  split_ifs with h
  · exact h01 _
  · left; rfl

noncomputable def trunc (N : ℕ) (g : ℕ → ℝ) (c : ℕ) : ℝ := if c < N then g c else 0

theorem trunc_01 (N : ℕ) (g : ℕ → ℝ) (h01 : ∀ c, g c = 0 ∨ g c = 1) (c : ℕ) :
    trunc N g c = 0 ∨ trunc N g c = 1 := by
  unfold trunc
  split_ifs
  · exact h01 c
  · left; rfl

theorem trunc_ge (N : ℕ) (g : ℕ → ℝ) (c : ℕ) (hc : N ≤ c) : trunc N g c = 0 := by
  unfold trunc
  rw [if_neg (by omega)]

theorem T_trunc (N : ℕ) (g : ℕ → ℝ) : T N (trunc N g) = T N g := by
  unfold T
  apply Finset.sum_congr rfl
  intro c hc
  rw [Finset.mem_range] at hc
  unfold trunc
  rw [if_pos hc]

theorem trel (N k : ℕ) (hk : k + 2 ≤ N) (P Q : ℕ → ℝ) (h : ∀ c, P c = Q c + D k c) :
    ∀ c, trunc N P c = trunc N Q c + D k c := by
  intro c
  by_cases hc : c < N
  · unfold trunc
    rw [if_pos hc, if_pos hc, h c]
  · rw [D_zero k c (by omega), trunc_ge N P c (by omega), trunc_ge N Q c (by omega)]
    ring

noncomputable def gS (A E : Finset ℕ) (c : ℕ) : ℝ := if c ∈ A ∨ c ∈ E then 1 else 0

theorem gS_01 (A E : Finset ℕ) (c : ℕ) : gS A E c = 0 ∨ gS A E c = 1 := by
  unfold gS
  split_ifs <;> simp

theorem gS_E (A E : Finset ℕ) (c : ℕ) (hc : c ∈ E) : gS A E c = 1 := by
  unfold gS
  rw [if_pos (Or.inr hc)]

theorem gS_out (A E : Finset ℕ) (c : ℕ) (hA : c ∉ A) (hE : c ∉ E) : gS A E c = 0 := by
  unfold gS
  rw [if_neg (by tauto)]

theorem T_gS (N : ℕ) (A E : Finset ℕ) (hA : A ⊆ Finset.range N) (hE : ∀ e ∈ E, N ≤ e) :
    T N (gS A E) = ((∑ c ∈ A, shiftedFib (c + 1) : ℕ) : ℝ) := by
  unfold T
  have hz : ∀ c ∈ Finset.range N, c ∉ A → F c * gS A E c = 0 := by
    intro c hc hcA
    have hcE : c ∉ E := fun h => by
      have := hE c h
      rw [Finset.mem_range] at hc
      omega
    rw [gS_out A E c hcA hcE, mul_zero]
  rw [← Finset.sum_subset hA hz]
  push_cast
  apply Finset.sum_congr rfl
  intro c hc
  unfold gS F
  rw [if_pos (Or.inl hc), mul_one]

theorem T_nat (N : ℕ) (g : ℕ → ℝ) (h01 : ∀ c, g c = 0 ∨ g c = 1) : ∃ m : ℕ, T N g = m := by
  induction N with
  | zero => exact ⟨0, by simp [T]⟩
  | succ N ih =>
    obtain ⟨m, hm⟩ := ih
    unfold T at hm ⊢
    rw [Finset.sum_range_succ, hm]
    rcases h01 N with h | h
    · exact ⟨m, by rw [h]; ring⟩
    · exact ⟨m + shiftedFib (N + 1), by rw [h]; unfold F; push_cast; ring⟩

theorem fmono (k : ℕ) : shiftedFib (k + 1) ≤ shiftedFib (k + 2) := by
  rcases Nat.lt_or_ge k 2 with h | h
  · interval_cases k <;> decide
  · have := frec k h
    omega

theorem fgrow (k : ℕ) : 2 ^ k ≤ shiftedFib (2 * k + 2) := by
  induction k with
  | zero => decide
  | succ k ih =>
    have h1 : shiftedFib (2 * k + 4) = shiftedFib (2 * k + 2) + shiftedFib (2 * k + 3) :=
      frec (2 * k + 2) (by omega)
    have h2 : shiftedFib (2 * k + 2) ≤ shiftedFib (2 * k + 3) := fmono (2 * k + 1)
    rw [show 2 * (k + 1) + 2 = 2 * k + 4 by ring, pow_succ]
    omega

theorem S_eq (K : ℕ) (hK : 1 ≤ K) :
    ∑ c ∈ Finset.range K, shiftedFib (c + 1) = shiftedFib (K + 2) := by
  induction K with
  | zero => omega
  | succ K ih =>
    rcases Nat.eq_zero_or_pos K with h | h
    · subst h
      simp [shiftedFib]
    · rw [Finset.sum_range_succ, ih h]
      have h3 : shiftedFib (K + 3) = shiftedFib (K + 1) + shiftedFib (K + 2) :=
        frec (K + 1) (by omega)
      rw [show K + 1 + 2 = K + 3 from rfl, h3]
      ring

theorem Icc_sum (M : ℕ) :
    ∑ i ∈ Finset.Icc 1 M, shiftedFib i = ∑ c ∈ Finset.range M, shiftedFib (c + 1) := by
  have hI : Finset.Icc 1 M = Finset.Ico 1 (M + 1) := by
    ext a
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    constructor <;> intro h <;> omega
  rw [hI, Finset.sum_Ico_eq_sum_range]
  try rw [show M + 1 - 1 = M by omega]
  exact Finset.sum_congr rfl (fun j _ => by rw [add_comm])

theorem rep (K x : ℕ) (hx : x ≤ ∑ c ∈ Finset.range K, shiftedFib (c + 1)) :
    ∃ A : Finset ℕ, A ⊆ Finset.range K ∧ ∑ c ∈ A, shiftedFib (c + 1) = x := by
  induction K generalizing x with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, Nat.le_zero] at hx
    exact ⟨∅, by simp, by simp [hx]⟩
  | succ K ih =>
    rw [Finset.sum_range_succ] at hx
    by_cases hle : x ≤ ∑ c ∈ Finset.range K, shiftedFib (c + 1)
    · obtain ⟨A, hA, hs⟩ := ih x hle
      exact ⟨A, hA.trans (Finset.range_subset_range.mpr (by omega)), hs⟩
    · have hf : shiftedFib (K + 1) ≤ ∑ c ∈ Finset.range K, shiftedFib (c + 1) + 1 := by
        rcases Nat.eq_zero_or_pos K with h0 | h0
        · subst h0
          simp [shiftedFib]
        · rw [S_eq K h0]
          exact le_trans (fmono K) (Nat.le_succ _)
      obtain ⟨A, hA, hs⟩ := ih (x - shiftedFib (K + 1)) (by omega)
      have hK : K ∉ A := fun h => by
        have := hA h
        simp at this
      refine ⟨insert K A, ?_, ?_⟩
      · intro c hc
        rw [Finset.mem_insert] at hc
        rcases hc with rfl | hc
        · simp
        · exact Finset.range_subset_range.mpr (by omega) (hA hc)
      · rw [Finset.sum_insert hK, hs]
        omega

theorem R_bound {n : ℕ} (w : Fin n → ℕ) : 1 ≤ redR w ∧ 15 * redL w + 10 ≤ 2 ^ redR w := by
  have h1 : 30 * redL w + 20 ≤ 2 ^ Nat.clog 2 (30 * redL w + 20) := Nat.le_pow_clog (by norm_num) _
  have h2 : 0 < Nat.clog 2 (30 * redL w + 20) := Nat.clog_pos (by norm_num) (by omega)
  have h3 : redR w + 1 = Nat.clog 2 (30 * redL w + 20) := by
    unfold redR rOf
    omega
  rw [← h3, pow_succ] at h1
  constructor
  · by_contra h
    have h0 : redR w = 0 := by omega
    have h4 : 2 ^ redR w = 1 := by rw [h0, pow_zero]
    omega
  · omega

theorem beta_bound {n : ℕ} (w : Fin n → ℕ) :
    15 * redL w + 10 ≤ ∑ i ∈ Finset.Icc 1 (2 * redR w), shiftedFib i := by
  obtain ⟨hR1, hRL⟩ := R_bound w
  rw [Icc_sum, S_eq _ (by omega)]
  have := fgrow (redR w)
  omega

noncomputable def phiA {N : ℕ} (α : Fin N → ℤ) : (Fin N → ℝ) →ₗ[ℝ] ℝ where
  toFun x := ∑ i, (α i : ℝ) * x i
  map_add' x y := by
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by ring)

theorem phiA_apply {N : ℕ} (α : Fin N → ℤ) (x : Fin N → ℝ) :
    phiA α x = ∑ i, (α i : ℝ) * x i := rfl

theorem facetCrit {N K : ℕ} (hNK : N = K + 1) (a : Fin N → ℕ) (b : ℕ) (α : Fin N → ℤ) (β : ℤ)
    (hV : ∀ x ∈ knapsackSet a b, ∑ i, (α i : ℝ) * x i ≤ β)
    (hU : ∀ i, a i ≤ b) (i0 : Fin N) (hα0 : α i0 ≠ 0)
    (hne : (face a b α β).Nonempty)
    (u : Fin K → Fin N → ℝ) (hu : ∀ k, u k ∈ vectorSpan ℝ (face a b α β))
    (hz : ∀ k : Fin K, ∀ c : Fin N, k.val + 1 < c.val → u k c = 0)
    (hp : ∀ k : Fin K, ∀ c : Fin N, c.val = k.val + 1 → u k c ≠ 0) :
    IsFacetDefining a b α β := by
  subst hNK
  have hval : IsValid a b α β := by
    intro x hx
    have hconv : Convex ℝ {x : Fin (K + 1) → ℝ | phiA α x ≤ (β : ℝ)} :=
      convex_halfSpace_le (phiA α).isLinear _
    exact convexHull_min (fun y hy => hV y hy) hconv hx
  have hup : vectorSpan ℝ (face a b α β) ≤ LinearMap.ker (phiA α) := by
    rw [vectorSpan_def, Submodule.span_le]
    rintro z ⟨p, hp', q, hq', rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker]
    show phiA α (p -ᵥ q) = 0
    have hp2 : phiA α p = β := hp'.2
    have hq2 : phiA α q = β := hq'.2
    rw [vsub_eq_sub, map_sub, hp2, hq2, sub_self]
  have hker : Module.finrank ℝ (LinearMap.ker (phiA α)) = K := by
    have h := LinearMap.finrank_range_add_finrank_ker (phiA α)
    have hα0' : (α i0 : ℝ) ≠ 0 := by exact_mod_cast hα0
    have hr : LinearMap.range (phiA α) = ⊤ := by
      rw [LinearMap.range_eq_top]
      intro y
      refine ⟨Pi.single i0 (y / (α i0 : ℝ)), ?_⟩
      rw [phiA_apply, Finset.sum_eq_single i0]
      · rw [Pi.single_eq_same]
        field_simp
      · intro j _ hj
        rw [Pi.single_eq_of_ne hj, mul_zero]
      · intro h
        exact absurd (Finset.mem_univ _) h
    rw [hr, finrank_top, Module.finrank_self, Module.finrank_fin_fun] at h
    omega
  have hli := tri_li K u hz (fun k => hp k ⟨k.val + 1, Nat.succ_lt_succ k.isLt⟩ rfl)
  have hlow : K ≤ Module.finrank ℝ (vectorSpan ℝ (face a b α β)) := by
    have h1 : Submodule.span ℝ (Set.range u) ≤ vectorSpan ℝ (face a b α β) := by
      rw [Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      exact hu k
    have h2 := Submodule.finrank_mono h1
    rw [finrank_span_eq_card hli, Fintype.card_fin] at h2
    exact h2
  have hhigh : Module.finrank ℝ (vectorSpan ℝ (face a b α β)) ≤ K := by
    have h2 := Submodule.finrank_mono hup
    rw [hker] at h2
    exact h2
  have hfull : vectorSpan ℝ (KP a b) = ⊤ := by
    rw [eq_top_iff, ← (Pi.basisFun ℝ (Fin (K + 1))).span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    rw [Pi.basisFun_apply]
    have h0 : (0 : Fin (K + 1) → ℝ) ∈ KP a b := by
      refine subset_convexHull ℝ _ ⟨fun j => Or.inl rfl, ?_⟩
      simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero]
      positivity
    have hi : (Pi.single i 1 : Fin (K + 1) → ℝ) ∈ KP a b := by
      refine subset_convexHull ℝ _ ⟨fun j => ?_, ?_⟩
      · by_cases hj : j = i
        · right
          rw [hj, Pi.single_eq_same]
        · left
          rw [Pi.single_eq_of_ne hj]
      · have hs : ∑ j, ((a j : ℕ) : ℝ) * (Pi.single i 1 : Fin (K + 1) → ℝ) j = ((a i : ℕ) : ℝ) := by
          rw [Finset.sum_eq_single i]
          · rw [Pi.single_eq_same, mul_one]
          · intro j _ hj
            rw [Pi.single_eq_of_ne hj, mul_zero]
          · intro h
            exact absurd (Finset.mem_univ i) h
        rw [hs]
        exact_mod_cast hU i
    have h := vsub_mem_vectorSpan ℝ hi h0
    rwa [vsub_eq_sub, sub_zero] at h
  refine ⟨hval, hne, ?_⟩
  rw [hfull, finrank_top, Module.finrank_fin_fun]
  omega

theorem diff_mem {N : ℕ} (s : Set (Fin N → ℝ)) (P Q d : ℕ → ℝ) (h : ∀ c, P c = Q c + d c)
    (hP : (pt P : Fin N → ℝ) ∈ s) (hQ : (pt Q : Fin N → ℝ) ∈ s) :
    (pt d : Fin N → ℝ) ∈ vectorSpan ℝ s := by
  have h' := vsub_mem_vectorSpan ℝ hP hQ
  rw [vsub_eq_sub] at h'
  convert h' using 1
  funext i
  simp only [pt, Pi.sub_apply, h]
  ring

attribute [local irreducible] KnapsackFacets.redR

theorem W_nat (n p : ℕ) (cf : ℕ → ℕ) (g : ℕ → ℝ) (h01 : ∀ c, g c = 0 ∨ g c = 1) :
    ∃ m : ℕ, ∑ k ∈ Finset.range n, (cf k : ℝ) * g (p + k) = m := by
  induction n with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨m, hm⟩ := ih
    rw [Finset.sum_range_succ, hm]
    rcases h01 (p + n) with h | h
    · exact ⟨m, by rw [h]; ring⟩
    · exact ⟨m + cf n, by rw [h]; push_cast; ring⟩

theorem W_zero (n p : ℕ) (cf : ℕ → ℕ) (g : ℕ → ℝ) (h0 : ∀ k, k < n → g (p + k) = 0) :
    ∑ k ∈ Finset.range n, (cf k : ℝ) * g (p + k) = 0 := by
  apply Finset.sum_eq_zero
  intro k hk
  rw [h0 k (Finset.mem_range.mp hk), mul_zero]

theorem W_single (n p : ℕ) (cf : ℕ → ℕ) (g : ℕ → ℝ) (j : ℕ) (hj : j < n)
    (h1 : g (p + j) = 1) (h0 : ∀ k, k < n → k ≠ j → g (p + k) = 0) :
    ∑ k ∈ Finset.range n, (cf k : ℝ) * g (p + k) = cf j := by
  rw [Finset.sum_eq_single j]
  · rw [h1, mul_one]
  · intro k hk hkj
    rw [h0 k (Finset.mem_range.mp hk) hkj, mul_zero]
  · intro h
    exact absurd (Finset.mem_range.mpr hj) h

theorem wAt_le {n : ℕ} (w : Fin n → ℕ) (k : ℕ) : wAt w k ≤ redL w := by
  unfold wAt redL
  split_ifs with h
  · exact Finset.single_le_sum (f := w) (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)
  · exact Nat.zero_le _

theorem wAt_fin' {n : ℕ} (w : Fin n → ℕ) (i : Fin n) : wAt w i.val = w i := by
  unfold wAt
  rw [dif_pos i.isLt]

theorem WS {n : ℕ} (w : Fin n → ℕ) (p : ℕ) (Y : ℕ → ℝ) (hY : ∀ c, Y c = 0 ∨ Y c = 1) :
    ∑ k ∈ Finset.range n, (wAt w k : ℝ) * Y (p + k) =
      ((∑ i ∈ Finset.univ.filter (fun i : Fin n => Y (p + i.val) = 1), w i : ℕ) : ℝ) := by
  push_cast
  rw [Finset.sum_filter, ← Fin.sum_univ_eq_sum_range (fun k => (wAt w k : ℝ) * Y (p + k))]
  apply Finset.sum_congr rfl
  intro i _
  rw [wAt_fin']
  rcases hY (p + i.val) with h | h
  · rw [h, if_neg (by norm_num), mul_zero]
  · rw [h, if_pos rfl, mul_one]

theorem W_le {n : ℕ} (w : Fin n → ℕ) (p : ℕ) (Y : ℕ → ℝ) (hY : ∀ c, Y c = 0 ∨ Y c = 1) :
    ∑ k ∈ Finset.range n, (wAt w k : ℝ) * Y (p + k) ≤ (redL w : ℝ) := by
  rw [WS w p Y hY]
  have h : ∑ i ∈ Finset.univ.filter (fun i : Fin n => Y (p + i.val) = 1), w i ≤ redL w := by
    unfold redL
    exact Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
  exact_mod_cast h

theorem T_le (N : ℕ) (g : ℕ → ℝ) (h01 : ∀ c, g c = 0 ∨ g c = 1) :
    T N g ≤ ∑ c ∈ Finset.range N, F c := by
  unfold T
  apply Finset.sum_le_sum
  intro c _
  have hF : 0 ≤ F c := by unfold F; positivity
  rcases h01 c with h | h <;> rw [h] <;> linarith

theorem T_ind_out (N a : ℕ) (ha : N ≤ a) : T N (ind a) = 0 := by
  unfold T
  apply Finset.sum_eq_zero
  intro c hc
  rw [Finset.mem_range] at hc
  unfold ind
  rw [if_neg (by omega), mul_zero]

theorem Phi_split (R : ℕ) :
    ∑ i ∈ Finset.Icc 1 (2 * R + 1), shiftedFib i =
      ∑ i ∈ Finset.Icc 1 (2 * R), shiftedFib i + shiftedFib (2 * R + 1) := by
  rw [Icc_sum, Icc_sum, Finset.sum_range_succ]

theorem sumA2 {n : ℕ} (w : Fin n → ℕ) (t : ℕ) (g : ℕ → ℝ) :
    ∑ i : Fin (redN w), ((redA w t i : ℕ) : ℝ) * (pt g : Fin (redN w) → ℝ) i =
      (t : ℝ) * T (2 * redR w + 1) g +
        ((t : ℝ) * (2 * (redL w : ℝ) + 1) + 1) * g (2 * redR w + 1) +
        ((t : ℝ) + 1) * ∑ k ∈ Finset.range n, (wAt w k : ℝ) * g (2 * redR w + 2 + k) +
        ((t : ℝ) * (shiftedFib (2 * redR w + 1) : ℝ) + (t : ℝ) ^ 2 +
          (t : ℝ) * (2 * (redL w : ℝ) + 2) + 1) * g (2 * redR w + n + 2) +
        ((t : ℝ) + 1) * g (2 * redR w + n + 3) := by
  show ∑ i : Fin (redN w), ((aCoef w t (i.val + 1) : ℕ) : ℝ) * g i.val = _
  rw [Fin.sum_univ_eq_sum_range (fun c => ((aCoef w t (c + 1) : ℕ) : ℝ) * g c) (redN w)]
  have e0 : ∑ c ∈ Finset.range (redN w), ((aCoef w t (c + 1) : ℕ) : ℝ) * g c =
      ∑ c ∈ Finset.range (2 * redR w + n + 3), ((aCoef w t (c + 1) : ℕ) : ℝ) * g c +
      ((aCoef w t (2 * redR w + n + 3 + 1) : ℕ) : ℝ) * g (2 * redR w + n + 3) :=
    Finset.sum_range_succ _ _
  have e0' : ∑ c ∈ Finset.range (2 * redR w + n + 3), ((aCoef w t (c + 1) : ℕ) : ℝ) * g c =
      ∑ c ∈ Finset.range (2 * redR w + n + 2), ((aCoef w t (c + 1) : ℕ) : ℝ) * g c +
      ((aCoef w t (2 * redR w + n + 2 + 1) : ℕ) : ℝ) * g (2 * redR w + n + 2) :=
    Finset.sum_range_succ _ _
  have e1 : ∑ c ∈ Finset.range (2 * redR w + n + 2), ((aCoef w t (c + 1) : ℕ) : ℝ) * g c =
      ∑ c ∈ Finset.range (2 * redR w + 2), ((aCoef w t (c + 1) : ℕ) : ℝ) * g c +
      ∑ k ∈ Finset.range n, ((aCoef w t (2 * redR w + 2 + k + 1) : ℕ) : ℝ) *
        g (2 * redR w + 2 + k) := by
    rw [show 2 * redR w + n + 2 = 2 * redR w + 2 + n by omega]
    exact Finset.sum_range_add _ _ _
  have e2 : ∑ c ∈ Finset.range (2 * redR w + 2), ((aCoef w t (c + 1) : ℕ) : ℝ) * g c =
      ∑ c ∈ Finset.range (2 * redR w + 1), ((aCoef w t (c + 1) : ℕ) : ℝ) * g c +
      ((aCoef w t (2 * redR w + 1 + 1) : ℕ) : ℝ) * g (2 * redR w + 1) :=
    Finset.sum_range_succ _ _
  have h1 : ∑ c ∈ Finset.range (2 * redR w + 1), ((aCoef w t (c + 1) : ℕ) : ℝ) * g c =
      (t : ℝ) * ∑ c ∈ Finset.range (2 * redR w + 1), F c * g c := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro c hc
    rw [Finset.mem_range] at hc
    rw [cA1 w t c hc]
    unfold F
    push_cast
    ring
  have h3 : ∑ k ∈ Finset.range n, ((aCoef w t (2 * redR w + 2 + k + 1) : ℕ) : ℝ) *
        g (2 * redR w + 2 + k) =
      ((t : ℝ) + 1) * ∑ k ∈ Finset.range n, (wAt w k : ℝ) * g (2 * redR w + 2 + k) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_range] at hk
    rw [cA3 w t k hk]
    push_cast
    ring
  rw [e0, e0', e1, e2, h1, h3, cA2, cA4, cA5]
  unfold T
  push_cast
  try ring

theorem sumB2 {n : ℕ} (w : Fin n → ℕ) (t : ℕ) (g : ℕ → ℝ) :
    ∑ i : Fin (redN w), ((redAlpha w t i : ℤ) : ℝ) * (pt g : Fin (redN w) → ℝ) i =
      T (2 * redR w + 1) g + (2 * (redL w : ℝ) + 2) * g (2 * redR w + 1) +
        ∑ k ∈ Finset.range n, (wAt w k : ℝ) * g (2 * redR w + 2 + k) +
        ((shiftedFib (2 * redR w + 1) : ℝ) + (t : ℝ) + 2 * (redL w : ℝ) + 1) *
          g (2 * redR w + n + 2) := by
  show ∑ i : Fin (redN w), (((alphaCoef w t (i.val + 1) : ℕ) : ℤ) : ℝ) * g i.val = _
  simp only [Int.cast_natCast]
  rw [Fin.sum_univ_eq_sum_range (fun c => ((alphaCoef w t (c + 1) : ℕ) : ℝ) * g c) (redN w)]
  have e0 : ∑ c ∈ Finset.range (redN w), ((alphaCoef w t (c + 1) : ℕ) : ℝ) * g c =
      ∑ c ∈ Finset.range (2 * redR w + n + 3), ((alphaCoef w t (c + 1) : ℕ) : ℝ) * g c +
      ((alphaCoef w t (2 * redR w + n + 3 + 1) : ℕ) : ℝ) * g (2 * redR w + n + 3) :=
    Finset.sum_range_succ _ _
  have e0' : ∑ c ∈ Finset.range (2 * redR w + n + 3), ((alphaCoef w t (c + 1) : ℕ) : ℝ) * g c =
      ∑ c ∈ Finset.range (2 * redR w + n + 2), ((alphaCoef w t (c + 1) : ℕ) : ℝ) * g c +
      ((alphaCoef w t (2 * redR w + n + 2 + 1) : ℕ) : ℝ) * g (2 * redR w + n + 2) :=
    Finset.sum_range_succ _ _
  have e1 : ∑ c ∈ Finset.range (2 * redR w + n + 2), ((alphaCoef w t (c + 1) : ℕ) : ℝ) * g c =
      ∑ c ∈ Finset.range (2 * redR w + 2), ((alphaCoef w t (c + 1) : ℕ) : ℝ) * g c +
      ∑ k ∈ Finset.range n, ((alphaCoef w t (2 * redR w + 2 + k + 1) : ℕ) : ℝ) *
        g (2 * redR w + 2 + k) := by
    rw [show 2 * redR w + n + 2 = 2 * redR w + 2 + n by omega]
    exact Finset.sum_range_add _ _ _
  have e2 : ∑ c ∈ Finset.range (2 * redR w + 2), ((alphaCoef w t (c + 1) : ℕ) : ℝ) * g c =
      ∑ c ∈ Finset.range (2 * redR w + 1), ((alphaCoef w t (c + 1) : ℕ) : ℝ) * g c +
      ((alphaCoef w t (2 * redR w + 1 + 1) : ℕ) : ℝ) * g (2 * redR w + 1) :=
    Finset.sum_range_succ _ _
  have h1 : ∑ c ∈ Finset.range (2 * redR w + 1), ((alphaCoef w t (c + 1) : ℕ) : ℝ) * g c =
      ∑ c ∈ Finset.range (2 * redR w + 1), F c * g c := by
    apply Finset.sum_congr rfl
    intro c hc
    rw [Finset.mem_range] at hc
    simp only [cB1 w t c hc, F]
  have h3 : ∑ k ∈ Finset.range n, ((alphaCoef w t (2 * redR w + 2 + k + 1) : ℕ) : ℝ) *
        g (2 * redR w + 2 + k) =
      ∑ k ∈ Finset.range n, (wAt w k : ℝ) * g (2 * redR w + 2 + k) := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_range] at hk
    rw [cB3 w t k hk]
  rw [e0, e0', e1, e2, h1, h3, cB2, cB4, cB5]
  unfold T
  push_cast
  try ring

theorem redB_eq {n : ℕ} (w : Fin n → ℕ) (t : ℕ) :
    ((redB w t : ℕ) : ℝ) = (t : ℝ) * ((∑ i ∈ Finset.Icc 1 (2 * redR w + 1), shiftedFib i : ℕ) : ℝ)
      + (t : ℝ) ^ 2 + (t : ℝ) * (2 * (redL w : ℝ) + 2) + 1 := by
  unfold redB
  push_cast
  ring

theorem redBeta_eq {n : ℕ} (w : Fin n → ℕ) (t : ℕ) :
    ((redBeta w t : ℕ) : ℝ) = ((∑ i ∈ Finset.Icc 1 (2 * redR w + 1), shiftedFib i : ℕ) : ℝ)
      + (t : ℝ) + 2 * (redL w : ℝ) + 1 := by
  unfold redBeta
  push_cast
  ring

/-- A tight feasible 0/1 point whose last coordinate is 1 yields a subset of sum `t - 1`. -/
theorem vlemma {n : ℕ} (w : Fin n → ℕ) (t : ℕ) (ht : 2 ≤ t) (g : ℕ → ℝ)
    (h01 : ∀ c, g c = 0 ∨ g c = 1)
    (hcap : ∑ i : Fin (redN w), ((redA w t i : ℕ) : ℝ) * (pt g : Fin (redN w) → ℝ) i ≤
      ((redB w t : ℕ) : ℝ))
    (htight : ∑ i : Fin (redN w), ((redAlpha w t i : ℤ) : ℝ) * (pt g : Fin (redN w) → ℝ) i =
      ((redBeta w t : ℕ) : ℝ))
    (hv : g (2 * redR w + n + 3) = 1) :
    ∃ S : Finset (Fin n), ∑ i ∈ S, w i + 1 = t := by
  rw [sumA2, redB_eq] at hcap
  rw [sumB2, redBeta_eq] at htight
  generalize redR w = R at hcap htight hv
  have hTle := T_le (2 * R + 1) g h01
  have hWle := W_le w (2 * R + 2) g h01
  have hPhi : ∑ c ∈ Finset.range (2 * R + 1), F c =
      ((∑ i ∈ Finset.Icc 1 (2 * R + 1), shiftedFib i : ℕ) : ℝ) := by
    rw [Icc_sum]
    push_cast
    rfl
  rw [hPhi] at hTle
  obtain ⟨m', hm'⟩ := W_nat n (2 * R + 2) (wAt w) g h01
  have hWS := WS w (2 * R + 2) g h01
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : ℝ, Φ = ((∑ i ∈ Finset.Icc 1 (2 * R + 1), shiftedFib i : ℕ) : ℝ) :=
    ⟨_, rfl⟩
  rw [← hΦ] at hcap htight hTle
  rw [hm'] at hcap htight hWle
  rw [hv] at hcap
  have htR : (2 : ℝ) ≤ t := by exact_mod_cast ht
  have hf0 : (0 : ℝ) ≤ (shiftedFib (2 * R + 1) : ℝ) := by positivity
  have hm0 : (0 : ℝ) ≤ m' := by positivity
  have hT0 : 0 ≤ T (2 * R + 1) g := by
    obtain ⟨m, hm⟩ := T_nat (2 * R + 1) g h01
    rw [hm]
    positivity
  have hL0 : (0 : ℝ) ≤ redL w := by positivity
  have key : (m' : ℝ) = t - 1 := by
    rcases h01 (2 * R + 1) with hy | hy <;> rcases h01 (2 * R + n + 2) with hu | hu <;>
      rw [hy, hu] at hcap htight
    · linarith
    · have hΦ' : Φ = T (2 * R + 1) g + m' + shiftedFib (2 * R + 1) := by linarith
      rw [hΦ'] at hcap
      linarith
    · have hΦ' : Φ = T (2 * R + 1) g + m' - t + 1 := by linarith
      rw [hΦ'] at hcap hTle
      linarith
    · have hΦ' : Φ = T (2 * R + 1) g + m' + shiftedFib (2 * R + 1) +
          2 * redL w + 2 := by linarith
      rw [hΦ'] at hcap
      linarith
  refine ⟨Finset.univ.filter (fun i : Fin n => g (2 * R + 2 + i.val) = 1), ?_⟩
  rw [hm'] at hWS
  have h : ((∑ i ∈ Finset.univ.filter (fun i : Fin n => g (2 * R + 2 + i.val) = 1), w i :
      ℕ) : ℝ) + 1 = t := by
    rw [← hWS, key]
    ring
  exact_mod_cast h

noncomputable def addU (U : ℕ) (g : ℕ → ℝ) (c : ℕ) : ℝ := g c + ind U c

/-- the ordered list of the `2R+n+4` points -/
noncomputable def Pt (R n : ℕ) (XB VB : ℕ → ℕ → ℝ) (PY : ℕ → ℝ) (Z : ℕ → ℕ → ℝ)
    (PA Pv : ℕ → ℝ) (j : ℕ) : ℕ → ℝ :=
  if j < R then XB (j + 1) else if j < 2 * R + 1 then VB (j - R) else
  if j = 2 * R + 1 then PY else if j < 2 * R + 2 + n then Z (j - (2 * R + 2)) else
  if j = 2 * R + n + 2 then PA else Pv

theorem Pt_X (R n : ℕ) (XB VB : ℕ → ℕ → ℝ) (PY : ℕ → ℝ) (Z : ℕ → ℕ → ℝ) (PA Pv : ℕ → ℝ)
    (m : ℕ) (h1 : 1 ≤ m) (h2 : m ≤ R) : Pt R n XB VB PY Z PA Pv (m - 1) = XB m := by
  unfold Pt
  rw [if_pos (by omega), show m - 1 + 1 = m by omega]

theorem Pt_V (R n : ℕ) (XB VB : ℕ → ℕ → ℝ) (PY : ℕ → ℝ) (Z : ℕ → ℕ → ℝ) (PA Pv : ℕ → ℝ)
    (s : ℕ) (h : s ≤ R) : Pt R n XB VB PY Z PA Pv (R + s) = VB s := by
  unfold Pt
  rw [if_neg (by omega), if_pos (by omega), show R + s - R = s by omega]

theorem Pt_Y (R n : ℕ) (XB VB : ℕ → ℕ → ℝ) (PY : ℕ → ℝ) (Z : ℕ → ℕ → ℝ) (PA Pv : ℕ → ℝ) :
    Pt R n XB VB PY Z PA Pv (2 * R + 1) = PY := by
  unfold Pt
  rw [if_neg (by omega), if_neg (by omega), if_pos rfl]

theorem Pt_Z (R n : ℕ) (XB VB : ℕ → ℕ → ℝ) (PY : ℕ → ℝ) (Z : ℕ → ℕ → ℝ) (PA Pv : ℕ → ℝ)
    (j : ℕ) (hj : j < n) : Pt R n XB VB PY Z PA Pv (2 * R + 2 + j) = Z j := by
  unfold Pt
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega),
    show 2 * R + 2 + j - (2 * R + 2) = j by omega]

theorem Pt_A (R n : ℕ) (XB VB : ℕ → ℕ → ℝ) (PY : ℕ → ℝ) (Z : ℕ → ℕ → ℝ) (PA Pv : ℕ → ℝ) :
    Pt R n XB VB PY Z PA Pv (2 * R + n + 2) = PA := by
  unfold Pt
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos rfl]

theorem Pt_v (R n : ℕ) (XB VB : ℕ → ℕ → ℝ) (PY : ℕ → ℝ) (Z : ℕ → ℕ → ℝ) (PA Pv : ℕ → ℝ) :
    Pt R n XB VB PY Z PA Pv (2 * R + n + 3) = Pv := by
  unfold Pt
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega)]

theorem Pt_cases (R n : ℕ) (XB VB : ℕ → ℕ → ℝ) (PY : ℕ → ℝ) (Z : ℕ → ℕ → ℝ) (PA Pv : ℕ → ℝ)
    (P : (ℕ → ℝ) → Prop) (hX : ∀ m, 1 ≤ m → m ≤ R → P (XB m)) (hV : ∀ s, s ≤ R → P (VB s))
    (hY : P PY) (hZ : ∀ j, j < n → P (Z j)) (hA : P PA) (hv : P Pv) (j : ℕ) (hj : j < 2 * R + n + 4) :
    P (Pt R n XB VB PY Z PA Pv j) := by
  unfold Pt
  split_ifs with h1 h2 h3 h4 h5
  · exact hX _ (by omega) (by omega)
  · exact hV _ (by omega)
  · exact hY
  · exact hZ _ (by omega)
  · exact hA
  · exact hv

/-- the differences, indexed by pivot -/
noncomputable def dd4 (R n : ℕ) (XR PY : ℕ → ℝ) (Z : ℕ → ℕ → ℝ) (PA Pv : ℕ → ℝ) (j c : ℕ) : ℝ :=
  if j < 2 * R then D j c else if j = 2 * R then PY c - XR c else
  if j < 2 * R + n + 1 then Z (j - (2 * R + 1)) c - PY c else
  if j = 2 * R + n + 1 then PA c - PY c else Pv c - PA c

noncomputable def u4 {N : ℕ} (R n : ℕ) (XR PY : ℕ → ℝ) (Z : ℕ → ℕ → ℝ) (PA Pv : ℕ → ℝ)
    (k : Fin (2 * R + n + 3)) (c : Fin N) : ℝ :=
  dd4 R n XR PY Z PA Pv k.val c.val

theorem u4_apply {N : ℕ} (R n : ℕ) (XR PY : ℕ → ℝ) (Z : ℕ → ℕ → ℝ) (PA Pv : ℕ → ℝ)
    (k : Fin (2 * R + n + 3)) (c : Fin N) :
    u4 R n XR PY Z PA Pv k c = dd4 R n XR PY Z PA Pv k.val c.val := rfl

theorem u4_eq {N : ℕ} (R n : ℕ) (XR PY : ℕ → ℝ) (Z : ℕ → ℕ → ℝ) (PA Pv : ℕ → ℝ)
    (k : Fin (2 * R + n + 3)) :
    (u4 R n XR PY Z PA Pv k : Fin N → ℝ) = pt (dd4 R n XR PY Z PA Pv k.val) := rfl

theorem finrank_ge_tri {N K : ℕ} (hNK : N = K + 1) (u : Fin K → Fin N → ℝ)
    (P : Submodule ℝ (Fin N → ℝ)) (hu : ∀ k, u k ∈ P)
    (hz : ∀ k : Fin K, ∀ c : Fin N, k.val + 1 < c.val → u k c = 0)
    (hp : ∀ k : Fin K, ∀ c : Fin N, c.val = k.val + 1 → u k c ≠ 0) :
    K ≤ Module.finrank ℝ P := by
  subst hNK
  have hli := tri_li K u hz (fun k => hp k ⟨k.val + 1, Nat.succ_lt_succ k.isLt⟩ rfl)
  have h1 : Submodule.span ℝ (Set.range u) ≤ P := by
    rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    exact hu k
  have h2 := Submodule.finrank_mono h1
  rw [finrank_span_eq_card hli, Fintype.card_fin] at h2
  exact h2

theorem memS' {n : ℕ} (R : ℕ) (S : Finset (Fin n)) (k : ℕ) (hk : k < n) :
    2 * R + 2 + k ∈ S.image (fun i : Fin n => 2 * R + 2 + i.val) ↔ (⟨k, hk⟩ : Fin n) ∈ S := by
  rw [Finset.mem_image]
  constructor
  · rintro ⟨i, hi, he⟩
    have : i = ⟨k, hk⟩ := Fin.ext (by show i.val = k; omega)
    rw [← this]
    exact hi
  · intro h
    exact ⟨_, h, rfl⟩

theorem memS'_ge {n : ℕ} (R : ℕ) (S : Finset (Fin n)) (c : ℕ)
    (hc : c ∈ S.image (fun i : Fin n => 2 * R + 2 + i.val)) : 2 * R + 2 ≤ c ∧ c < 2 * R + 2 + n := by
  rw [Finset.mem_image] at hc
  obtain ⟨i, _, rfl⟩ := hc
  have := i.isLt
  omega

noncomputable def PsiM {N : ℕ} (α : Fin N → ℤ) (iV : Fin N) : (Fin N → ℝ) →ₗ[ℝ] ℝ × ℝ :=
  (phiA α).prod (LinearMap.proj (R := ℝ) (φ := fun _ : Fin N => ℝ) iV)

theorem PsiM_apply {N : ℕ} (α : Fin N → ℤ) (iV : Fin N) (x : Fin N → ℝ) :
    PsiM α iV x = (phiA α x, x iV) := rfl

theorem finrank_ker_Psi {N : ℕ} (α : Fin N → ℤ) (i0 iV : Fin N) (hne : i0 ≠ iV)
    (hα0 : α i0 = 1) (hαV : α iV = 0) :
    Module.finrank ℝ (LinearMap.ker (PsiM α iV)) = N - 2 := by
  have h := LinearMap.finrank_range_add_finrank_ker (PsiM α iV)
  have hr : LinearMap.range (PsiM α iV) = ⊤ := by
    rw [LinearMap.range_eq_top]
    rintro ⟨a, b⟩
    refine ⟨Pi.single i0 a + Pi.single iV b, ?_⟩
    rw [PsiM_apply]
    have h1 : phiA α (Pi.single i0 a) = a := by
      rw [phiA_apply, Finset.sum_eq_single i0]
      · rw [Pi.single_eq_same, hα0]
        simp
      · intro j _ hj
        rw [Pi.single_eq_of_ne hj, mul_zero]
      · intro h
        exact absurd (Finset.mem_univ _) h
    have h2 : phiA α (Pi.single iV b) = 0 := by
      rw [phiA_apply, Finset.sum_eq_single iV]
      · rw [Pi.single_eq_same, hαV]
        simp
      · intro j _ hj
        rw [Pi.single_eq_of_ne hj, mul_zero]
      · intro h
        exact absurd (Finset.mem_univ _) h
    rw [map_add, h1, h2, add_zero, Pi.add_apply, Pi.single_eq_of_ne hne.symm, Pi.single_eq_same,
      zero_add]
  rw [hr, finrank_top, Module.finrank_prod, Module.finrank_self, Module.finrank_fin_fun] at h
  omega

noncomputable def XBf (R n m : ℕ) : ℕ → ℝ := addU (2 * R + n + 2) (trunc (2 * R + 1) (gX m))
noncomputable def VBf (R n s : ℕ) : ℕ → ℝ := addU (2 * R + n + 2) (trunc (2 * R + 1) (gV s))
noncomputable def PYf (R n : ℕ) (A : Finset ℕ) : ℕ → ℝ := gS A {2 * R + 1, 2 * R + n + 2}
noncomputable def Zf (R n : ℕ) (Af : ℕ → Finset ℕ) (j : ℕ) : ℕ → ℝ :=
  gS (Af j) {2 * R + 1, 2 * R + 2 + j, 2 * R + n + 2}
noncomputable def PAf (R : ℕ) (S' : Finset ℕ) : ℕ → ℝ :=
  gS (Finset.range (2 * R + 1)) (insert (2 * R + 1) S')
noncomputable def Pvf (R n : ℕ) (S' : Finset ℕ) : ℕ → ℝ :=
  gS (Finset.range (2 * R + 1)) (insert (2 * R + 1) (insert (2 * R + n + 3) S'))

theorem addU_01 (U N : ℕ) (g : ℕ → ℝ) (h01 : ∀ c, g c = 0 ∨ g c = 1) (hU : N ≤ U) (c : ℕ) :
    addU U (trunc N g) c = 0 ∨ addU U (trunc N g) c = 1 := by
  unfold addU ind
  by_cases hc : c = U
  · rw [if_pos hc, trunc_ge N g c (by omega)]
    right
    ring
  · rw [if_neg hc, add_zero]
    exact trunc_01 N g h01 c

theorem addU_rel (U N k : ℕ) (hk : k + 2 ≤ N) (P Q : ℕ → ℝ) (h : ∀ c, P c = Q c + D k c) :
    ∀ c, addU U (trunc N P) c = addU U (trunc N Q) c + D k c := by
  intro c
  unfold addU
  rw [trel N k hk P Q h c]
  ring

theorem T_addU (U N : ℕ) (hU : N ≤ U) (g : ℕ → ℝ) : T N (addU U g) = T N g := by
  unfold addU
  rw [T_add, T_ind_out N U hU, add_zero]

theorem addU_at (U N : ℕ) (hU : N ≤ U) (g : ℕ → ℝ) (c : ℕ) (hc : N ≤ c) :
    addU U (trunc N g) c = if c = U then 1 else 0 := by
  unfold addU ind
  rw [trunc_ge N g c hc, zero_add]

end Aux_KFs2

attribute [local irreducible] KnapsackFacets.redR

open KnapsackFacets Aux_KFs2 in
theorem solution {n : ℕ} (w : Fin n → ℕ) (t : ℕ) (ht : 2 ≤ t) (hw : ∀ i, w i + 1 ≤ t) :
    (∃ v : Fin (redN w) → (Fin (redN w) → ℝ), AffineIndependent ℝ v ∧
        ∀ k, v k ∈ knapsackSet (redA w t) (redB w t) ∧
          ∑ i, ((redAlpha w t i : ℤ) : ℝ) * v k i = ((redBeta w t : ℕ) : ℝ)) ↔
      ∃ S : Finset (Fin n), ∑ i ∈ S, w i + 1 = t := by
  obtain ⟨hR1, _⟩ := R_bound w
  have hβ := beta_bound w
  have hN : redN w = 2 * redR w + n + 4 := rfl
  have htR : (2 : ℝ) ≤ t := by exact_mod_cast ht
  constructor
  · -- (⇒)
    rintro ⟨v, hai, hv⟩
    by_contra hno
    have hV : 2 * redR w + n + 3 < redN w := by omega
    have hv0 : ∀ k, v k ⟨2 * redR w + n + 3, hV⟩ = 0 := by
      intro k
      have h01 := (hv k).1.1
      rcases h01 ⟨2 * redR w + n + 3, hV⟩ with h | h
      · exact h
      · exfalso
        apply hno
        have e := ext_pt (v k)
        have hk1 := (hv k).1.2
        have hk2 := (hv k).2
        rw [← e] at hk1 hk2
        refine vlemma w t ht (ext (v k)) (ext_01 h01) hk1 hk2 ?_
        unfold ext
        rw [dif_pos hV]
        exact h
    have hα0 : redAlpha w t ⟨0, by omega⟩ = 1 := by
      show ((alphaCoef w t (0 + 1) : ℕ) : ℤ) = 1
      rw [cB1 w t 0 (by omega)]
      simp [shiftedFib]
    have hαV : redAlpha w t ⟨2 * redR w + n + 3, hV⟩ = 0 := by
      show ((alphaCoef w t (2 * redR w + n + 3 + 1) : ℕ) : ℤ) = 0
      rw [cB5]
      simp
    have hne : (⟨0, by omega⟩ : Fin (redN w)) ≠ ⟨2 * redR w + n + 3, hV⟩ := by
      intro h
      have h' : (0 : ℕ) = 2 * redR w + n + 3 := congrArg Fin.val h
      omega
    have hker := finrank_ker_Psi (redAlpha w t) _ _ hne hα0 hαV
    have hsub : vectorSpan ℝ (Set.range v) ≤
        LinearMap.ker (PsiM (redAlpha w t) ⟨2 * redR w + n + 3, hV⟩) := by
      rw [vectorSpan_def, Submodule.span_le]
      rintro z ⟨p, ⟨i, rfl⟩, q, ⟨j, rfl⟩, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker, PsiM_apply, Prod.mk_eq_zero]
      beta_reduce
      constructor
      · rw [vsub_eq_sub, map_sub, phiA_apply, phiA_apply, (hv i).2, (hv j).2, sub_self]
      · rw [vsub_eq_sub, Pi.sub_apply, hv0 i, hv0 j, sub_self]
    have h1 := Submodule.finrank_mono hsub
    have h2 := hai.finrank_vectorSpan (n := redN w - 1) (by rw [Fintype.card_fin]; omega)
    rw [h2, hker] at h1
    omega
  · -- (⇐)
    rintro ⟨S, hS⟩
    have hsumB := Icc_sum (2 * redR w)
    have hsplit := Phi_split (redR w)
    have hTX : ∀ m, 1 ≤ m → m ≤ redR w →
        T (2 * redR w + 1) (trunc (2 * redR w + 1) (gX m)) =
          ((∑ i ∈ Finset.Icc 1 (2 * redR w), shiftedFib i : ℕ) : ℝ) := fun m h1 h2 => by
      rw [T_trunc]
      exact T_X _ m h1 h2
    have hTV : ∀ s, s ≤ redR w →
        T (2 * redR w + 1) (trunc (2 * redR w + 1) (gV s)) =
          ((∑ i ∈ Finset.Icc 1 (2 * redR w), shiftedFib i : ℕ) : ℝ) := fun s h => by
      rw [T_trunc]
      exact T_V _ hR1 s h
    have hPhiR : ((∑ i ∈ Finset.Icc 1 (2 * redR w + 1), shiftedFib i : ℕ) : ℝ) =
        ∑ c ∈ Finset.range (2 * redR w + 1), F c := by
      rw [Icc_sum]
      push_cast
      rfl
    obtain ⟨B, hB⟩ : ∃ B, B = ∑ i ∈ Finset.Icc 1 (2 * redR w), shiftedFib i := ⟨_, rfl⟩
    rw [← hB] at hβ hTX hTV hsumB hsplit
    obtain ⟨Φ, hΦ⟩ : ∃ Φ : ℝ, Φ = ((∑ i ∈ Finset.Icc 1 (2 * redR w + 1), shiftedFib i : ℕ) : ℝ) :=
      ⟨_, rfl⟩
    have hΦB : Φ = (B : ℝ) + (shiftedFib (2 * redR w + 1) : ℝ) := by
      rw [hΦ, hsplit]
      push_cast
      try ring
    rw [← hΦ] at hPhiR
    have hSR : ((∑ i ∈ S, w i : ℕ) : ℝ) = (t : ℝ) - 1 := by
      have : ((∑ i ∈ S, w i : ℕ) : ℝ) + 1 = t := by exact_mod_cast hS
      linarith
    have hwt : ∀ k, k < n → wAt w k + 1 ≤ t := by
      intro k hk
      have := hw ⟨k, hk⟩
      unfold wAt
      rw [dif_pos hk]
      exact this
    -- generic membership criterion
    have hpt : ∀ g : ℕ → ℝ, (∀ c, g c = 0 ∨ g c = 1) →
        (t : ℝ) * T (2 * redR w + 1) g +
          ((t : ℝ) * (2 * (redL w : ℝ) + 1) + 1) * g (2 * redR w + 1) +
          ((t : ℝ) + 1) * ∑ k ∈ Finset.range n, (wAt w k : ℝ) * g (2 * redR w + 2 + k) +
          ((t : ℝ) * (shiftedFib (2 * redR w + 1) : ℝ) + (t : ℝ) ^ 2 +
            (t : ℝ) * (2 * (redL w : ℝ) + 2) + 1) * g (2 * redR w + n + 2) +
          ((t : ℝ) + 1) * g (2 * redR w + n + 3) ≤
          (t : ℝ) * Φ + (t : ℝ) ^ 2 + (t : ℝ) * (2 * (redL w : ℝ) + 2) + 1 →
        T (2 * redR w + 1) g + (2 * (redL w : ℝ) + 2) * g (2 * redR w + 1) +
          ∑ k ∈ Finset.range n, (wAt w k : ℝ) * g (2 * redR w + 2 + k) +
          ((shiftedFib (2 * redR w + 1) : ℝ) + (t : ℝ) + 2 * (redL w : ℝ) + 1) *
            g (2 * redR w + n + 2) = Φ + (t : ℝ) + 2 * (redL w : ℝ) + 1 →
        (pt g : Fin (redN w) → ℝ) ∈ knapsackSet (redA w t) (redB w t) ∧
          ∑ i, ((redAlpha w t i : ℤ) : ℝ) * (pt g : Fin (redN w) → ℝ) i =
            ((redBeta w t : ℕ) : ℝ) := by
      intro g h01 hcap htight
      refine ⟨⟨fun i => h01 i.val, ?_⟩, ?_⟩
      · show ∑ i : Fin (redN w), ((redA w t i : ℕ) : ℝ) * (pt g : Fin (redN w) → ℝ) i ≤
          ((redB w t : ℕ) : ℝ)
        rw [sumA2, redB_eq, ← hΦ]
        linarith
      · rw [sumB2, redBeta_eq, ← hΦ]
        linarith
    -- auxiliary representations
    obtain ⟨A, hA, hAs⟩ := rep (2 * redR w) (B - (2 * redL w + 2)) (by rw [← hsumB]; omega)
    have hrepZ : ∀ j, ∃ A' : Finset ℕ, A' ⊆ Finset.range (2 * redR w) ∧
        ∑ c ∈ A', shiftedFib (c + 1) = B - (2 * redL w + 2) - wAt w j := fun j =>
      rep (2 * redR w) _ (by rw [← hsumB]; omega)
    choose Af hAf hAfs using hrepZ
    obtain ⟨S', hS'⟩ : ∃ S' : Finset ℕ, S' = S.image (fun i : Fin n => 2 * redR w + 2 + i.val) :=
      ⟨_, rfl⟩
    have hS'ge : ∀ c ∈ S', 2 * redR w + 2 ≤ c ∧ c < 2 * redR w + 2 + n := by
      intro c hc
      rw [hS'] at hc
      exact memS'_ge _ S c hc
    have hS'mem : ∀ k (hk : k < n), 2 * redR w + 2 + k ∈ S' ↔ (⟨k, hk⟩ : Fin n) ∈ S := by
      intro k hk
      rw [hS']
      exact memS' _ S k hk
    have hcB : ((B - (2 * redL w + 2) : ℕ) : ℝ) = (B : ℝ) - (2 * (redL w : ℝ) + 2) := by
      rw [Nat.cast_sub (show 2 * redL w + 2 ≤ B by omega)]
      push_cast
      try ring
    -- the points and their membership
    have hXB : ∀ m, 1 ≤ m → m ≤ redR w →
        (pt (XBf (redR w) n m) : Fin (redN w) → ℝ) ∈ knapsackSet (redA w t) (redB w t) ∧
          ∑ i, ((redAlpha w t i : ℤ) : ℝ) * (pt (XBf (redR w) n m) : Fin (redN w) → ℝ) i =
            ((redBeta w t : ℕ) : ℝ) := by
      intro m h1 h2
      have hT : T (2 * redR w + 1) (XBf (redR w) n m) = B := by
        unfold XBf
        rw [T_addU (2 * redR w + n + 2) (2 * redR w + 1) (by omega), hTX m h1 h2]
      have hy : XBf (redR w) n m (2 * redR w + 1) = 0 := by
        unfold XBf
        rw [addU_at (2 * redR w + n + 2) (2 * redR w + 1) (by omega) _ (2 * redR w + 1) le_rfl,
          if_neg (by omega)]
      have hu : XBf (redR w) n m (2 * redR w + n + 2) = 1 := by
        unfold XBf
        rw [addU_at (2 * redR w + n + 2) (2 * redR w + 1) (by omega) _ (2 * redR w + n + 2)
          (by omega), if_pos rfl]
      have hv : XBf (redR w) n m (2 * redR w + n + 3) = 0 := by
        unfold XBf
        rw [addU_at (2 * redR w + n + 2) (2 * redR w + 1) (by omega) _ (2 * redR w + n + 3)
          (by omega), if_neg (by omega)]
      have hW : ∑ k ∈ Finset.range n, (wAt w k : ℝ) * XBf (redR w) n m (2 * redR w + 2 + k) = 0 :=
        W_zero _ _ _ _ (fun k hk => by
          unfold XBf
          rw [addU_at (2 * redR w + n + 2) (2 * redR w + 1) (by omega) _ (2 * redR w + 2 + k)
            (by omega), if_neg (by omega)])
      apply hpt (XBf (redR w) n m) (fun c => addU_01 _ _ _ (gX_01 m) (by omega) c)
      · rw [hT, hy, hu, hv, hW, hΦB]
        linarith
      · rw [hT, hy, hu, hW, hΦB]
        ring
    have hVB : ∀ s, s ≤ redR w →
        (pt (VBf (redR w) n s) : Fin (redN w) → ℝ) ∈ knapsackSet (redA w t) (redB w t) ∧
          ∑ i, ((redAlpha w t i : ℤ) : ℝ) * (pt (VBf (redR w) n s) : Fin (redN w) → ℝ) i =
            ((redBeta w t : ℕ) : ℝ) := by
      intro s h
      have hT : T (2 * redR w + 1) (VBf (redR w) n s) = B := by
        unfold VBf
        rw [T_addU (2 * redR w + n + 2) (2 * redR w + 1) (by omega), hTV s h]
      have hy : VBf (redR w) n s (2 * redR w + 1) = 0 := by
        unfold VBf
        rw [addU_at (2 * redR w + n + 2) (2 * redR w + 1) (by omega) _ (2 * redR w + 1) le_rfl,
          if_neg (by omega)]
      have hu : VBf (redR w) n s (2 * redR w + n + 2) = 1 := by
        unfold VBf
        rw [addU_at (2 * redR w + n + 2) (2 * redR w + 1) (by omega) _ (2 * redR w + n + 2)
          (by omega), if_pos rfl]
      have hv : VBf (redR w) n s (2 * redR w + n + 3) = 0 := by
        unfold VBf
        rw [addU_at (2 * redR w + n + 2) (2 * redR w + 1) (by omega) _ (2 * redR w + n + 3)
          (by omega), if_neg (by omega)]
      have hW : ∑ k ∈ Finset.range n, (wAt w k : ℝ) * VBf (redR w) n s (2 * redR w + 2 + k) = 0 :=
        W_zero _ _ _ _ (fun k hk => by
          unfold VBf
          rw [addU_at (2 * redR w + n + 2) (2 * redR w + 1) (by omega) _ (2 * redR w + 2 + k)
            (by omega), if_neg (by omega)])
      apply hpt (VBf (redR w) n s) (fun c => addU_01 _ _ _ (gV_01 s) (by omega) c)
      · rw [hT, hy, hu, hv, hW, hΦB]
        linarith
      · rw [hT, hy, hu, hW, hΦB]
        ring
    have hPYz : ∀ c, 2 * redR w + 2 ≤ c → c ≠ 2 * redR w + n + 2 → PYf (redR w) n A c = 0 := by
      intro c hc hcU
      apply gS_out
      · intro h
        have := hA h
        rw [Finset.mem_range] at this
        omega
      · simp only [Finset.mem_insert, Finset.mem_singleton]
        omega
    have hPY1 : PYf (redR w) n A (2 * redR w + 1) = 1 := gS_E _ _ _ (by simp)
    have hPYU : PYf (redR w) n A (2 * redR w + n + 2) = 1 := gS_E _ _ _ (by simp)
    have hPY : (pt (PYf (redR w) n A) : Fin (redN w) → ℝ) ∈ knapsackSet (redA w t) (redB w t) ∧
        ∑ i, ((redAlpha w t i : ℤ) : ℝ) * (pt (PYf (redR w) n A) : Fin (redN w) → ℝ) i =
          ((redBeta w t : ℕ) : ℝ) := by
      have hT : T (2 * redR w + 1) (PYf (redR w) n A) = ((B - (2 * redL w + 2) : ℕ) : ℝ) := by
        unfold PYf
        rw [T_gS (2 * redR w + 1) A {2 * redR w + 1, 2 * redR w + n + 2} (hA.trans (Finset.range_subset_range.mpr (by omega)))
          (by intro e he; simp only [Finset.mem_insert, Finset.mem_singleton] at he; omega), hAs]
      have hv : PYf (redR w) n A (2 * redR w + n + 3) = 0 := hPYz _ (by omega) (by omega)
      have hW : ∑ k ∈ Finset.range n, (wAt w k : ℝ) * PYf (redR w) n A (2 * redR w + 2 + k) = 0 :=
        W_zero _ _ _ _ (fun k hk => hPYz _ (by omega) (by omega))
      apply hpt (PYf (redR w) n A) (gS_01 _ _)
      · rw [hT, hPY1, hPYU, hv, hW, hcB, hΦB]
        linarith
      · rw [hT, hPY1, hPYU, hW, hcB, hΦB]
        ring
    have hZz : ∀ j c, 2 * redR w + 2 ≤ c → c ≠ 2 * redR w + 2 + j → c ≠ 2 * redR w + n + 2 →
        Zf (redR w) n Af j c = 0 := by
      intro j c hc hcj hcU
      apply gS_out
      · intro h
        have := hAf j h
        rw [Finset.mem_range] at this
        omega
      · simp only [Finset.mem_insert, Finset.mem_singleton]
        omega
    have hZ1 : ∀ j, Zf (redR w) n Af j (2 * redR w + 1) = 1 := fun j => gS_E _ _ _ (by simp)
    have hZj : ∀ j, Zf (redR w) n Af j (2 * redR w + 2 + j) = 1 := fun j => gS_E _ _ _ (by simp)
    have hZU : ∀ j, Zf (redR w) n Af j (2 * redR w + n + 2) = 1 := fun j => gS_E _ _ _ (by simp)
    have hZ : ∀ j, j < n →
        (pt (Zf (redR w) n Af j) : Fin (redN w) → ℝ) ∈ knapsackSet (redA w t) (redB w t) ∧
          ∑ i, ((redAlpha w t i : ℤ) : ℝ) * (pt (Zf (redR w) n Af j) : Fin (redN w) → ℝ) i =
            ((redBeta w t : ℕ) : ℝ) := by
      intro j hj
      have hT : T (2 * redR w + 1) (Zf (redR w) n Af j) =
          ((B - (2 * redL w + 2) - wAt w j : ℕ) : ℝ) := by
        unfold Zf
        rw [T_gS (2 * redR w + 1) (Af j) {2 * redR w + 1, 2 * redR w + 2 + j, 2 * redR w + n + 2}
          ((hAf j).trans (Finset.range_subset_range.mpr (by omega)))
          (by intro e he; simp only [Finset.mem_insert, Finset.mem_singleton] at he; omega), hAfs j]
      have hv : Zf (redR w) n Af j (2 * redR w + n + 3) = 0 := hZz j _ (by omega) (by omega) (by omega)
      have hW : ∑ k ∈ Finset.range n, (wAt w k : ℝ) * Zf (redR w) n Af j (2 * redR w + 2 + k) =
          wAt w j :=
        W_single _ _ _ _ j hj (hZj j) (fun k hk hkj => hZz j _ (by omega) (by omega) (by omega))
      have hwj := wAt_le w j
      have hwj' := hwt j hj
      have hc : ((B - (2 * redL w + 2) - wAt w j : ℕ) : ℝ) =
          (B : ℝ) - (2 * (redL w : ℝ) + 2) - (wAt w j : ℝ) := by
        rw [Nat.cast_sub (show wAt w j ≤ B - (2 * redL w + 2) by omega),
          Nat.cast_sub (show 2 * redL w + 2 ≤ B by omega)]
        push_cast
        try ring
      have hwjR : (wAt w j : ℝ) + 1 ≤ t := by exact_mod_cast hwj'
      apply hpt (Zf (redR w) n Af j) (gS_01 _ _)
      · rw [hT, hZ1, hZU, hv, hW, hc, hΦB]
        linarith
      · rw [hT, hZ1, hZU, hW, hc, hΦB]
        ring
    have hTA : ∀ E : Finset ℕ, (∀ e ∈ E, 2 * redR w + 1 ≤ e) →
        T (2 * redR w + 1) (gS (Finset.range (2 * redR w + 1)) E) = Φ := by
      intro E hE
      rw [T_gS (2 * redR w + 1) _ E (subset_refl _) hE, hPhiR]
      unfold F
      push_cast
      try rfl
    have hWA : ∀ E : Finset ℕ, (∀ k (hk : k < n), 2 * redR w + 2 + k ∈ E ↔
        (⟨k, hk⟩ : Fin n) ∈ S) →
        ∑ k ∈ Finset.range n, (wAt w k : ℝ) *
          gS (Finset.range (2 * redR w + 1)) E (2 * redR w + 2 + k) = (t : ℝ) - 1 := by
      intro E hE
      have hfS : Finset.univ.filter (fun i : Fin n =>
          gS (Finset.range (2 * redR w + 1)) E (2 * redR w + 2 + i.val) = 1) = S := by
        ext i
        rw [Finset.mem_filter]
        simp only [Finset.mem_univ, true_and]
        constructor
        · intro h
          by_contra hi
          rw [gS_out _ _ _ (by rw [Finset.mem_range]; omega)
            (fun h' => hi ((hE i.val i.isLt).mp h'))] at h
          norm_num at h
        · intro hi
          exact gS_E _ _ _ ((hE i.val i.isLt).mpr hi)
      rw [WS w (2 * redR w + 2) _ (gS_01 _ _), hfS, hSR]
    have hPA : (pt (PAf (redR w) S') : Fin (redN w) → ℝ) ∈ knapsackSet (redA w t) (redB w t) ∧
        ∑ i, ((redAlpha w t i : ℤ) : ℝ) * (pt (PAf (redR w) S') : Fin (redN w) → ℝ) i =
          ((redBeta w t : ℕ) : ℝ) := by
      have hE : ∀ e ∈ insert (2 * redR w + 1) S', 2 * redR w + 1 ≤ e := by
        intro e he
        rw [Finset.mem_insert] at he
        rcases he with rfl | he
        · exact le_rfl
        · have := hS'ge e he
          omega
      have hT : T (2 * redR w + 1) (PAf (redR w) S') = Φ := hTA _ hE
      have hy : PAf (redR w) S' (2 * redR w + 1) = 1 := gS_E _ _ _ (Finset.mem_insert_self _ _)
      have hu : PAf (redR w) S' (2 * redR w + n + 2) = 0 := by
        apply gS_out
        · rw [Finset.mem_range]
          omega
        · rw [Finset.mem_insert]
          rintro (h | h)
          · omega
          · have := hS'ge _ h
            omega
      have hv : PAf (redR w) S' (2 * redR w + n + 3) = 0 := by
        apply gS_out
        · rw [Finset.mem_range]
          omega
        · rw [Finset.mem_insert]
          rintro (h | h)
          · omega
          · have := hS'ge _ h
            omega
      have hW : ∑ k ∈ Finset.range n, (wAt w k : ℝ) * PAf (redR w) S' (2 * redR w + 2 + k) =
          (t : ℝ) - 1 := hWA _ (fun k hk => by
        rw [Finset.mem_insert, hS'mem k hk]
        constructor
        · rintro (h | h)
          · omega
          · exact h
        · intro h
          exact Or.inr h)
      apply hpt (PAf (redR w) S') (gS_01 _ _)
      · rw [hT, hy, hu, hv, hW]
        linarith
      · rw [hT, hy, hu, hW]
        ring
    have hPv : (pt (Pvf (redR w) n S') : Fin (redN w) → ℝ) ∈ knapsackSet (redA w t) (redB w t) ∧
        ∑ i, ((redAlpha w t i : ℤ) : ℝ) * (pt (Pvf (redR w) n S') : Fin (redN w) → ℝ) i =
          ((redBeta w t : ℕ) : ℝ) := by
      have hE : ∀ e ∈ insert (2 * redR w + 1) (insert (2 * redR w + n + 3) S'),
          2 * redR w + 1 ≤ e := by
        intro e he
        rw [Finset.mem_insert, Finset.mem_insert] at he
        rcases he with rfl | rfl | he
        · exact le_rfl
        · omega
        · have := hS'ge e he
          omega
      have hT : T (2 * redR w + 1) (Pvf (redR w) n S') = Φ := hTA _ hE
      have hy : Pvf (redR w) n S' (2 * redR w + 1) = 1 := gS_E _ _ _ (Finset.mem_insert_self _ _)
      have hu : Pvf (redR w) n S' (2 * redR w + n + 2) = 0 := by
        apply gS_out
        · rw [Finset.mem_range]
          omega
        · rw [Finset.mem_insert, Finset.mem_insert]
          rintro (h | h | h)
          · omega
          · omega
          · have := hS'ge _ h
            omega
      have hv : Pvf (redR w) n S' (2 * redR w + n + 3) = 1 :=
        gS_E _ _ _ (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
      have hW : ∑ k ∈ Finset.range n, (wAt w k : ℝ) * Pvf (redR w) n S' (2 * redR w + 2 + k) =
          (t : ℝ) - 1 := hWA _ (fun k hk => by
        rw [Finset.mem_insert, Finset.mem_insert, hS'mem k hk]
        constructor
        · rintro (h | h | h)
          · omega
          · omega
          · exact h
        · intro h
          exact Or.inr (Or.inr h))
      apply hpt (Pvf (redR w) n S') (gS_01 _ _)
      · rw [hT, hy, hu, hv, hW]
        linarith
      · rw [hT, hy, hu, hW]
        ring
    -- the family
    refine ⟨fun i => (pt (Pt (redR w) n (XBf (redR w) n) (VBf (redR w) n) (PYf (redR w) n A)
      (Zf (redR w) n Af) (PAf (redR w) S') (Pvf (redR w) n S') i.val) : Fin (redN w) → ℝ),
      ?_, ?_⟩
    · obtain ⟨p, hp⟩ : ∃ p : Fin (redN w) → (Fin (redN w) → ℝ), p = fun i =>
          (pt (Pt (redR w) n (XBf (redR w) n) (VBf (redR w) n) (PYf (redR w) n A)
            (Zf (redR w) n Af) (PAf (redR w) S') (Pvf (redR w) n S') i.val) : Fin (redN w) → ℝ) :=
        ⟨_, rfl⟩
      rw [← hp]
      have hmem : ∀ j (hj : j < redN w), (pt (Pt (redR w) n (XBf (redR w) n) (VBf (redR w) n)
          (PYf (redR w) n A) (Zf (redR w) n Af) (PAf (redR w) S') (Pvf (redR w) n S') j) :
            Fin (redN w) → ℝ) ∈ Set.range p := by
        intro j hj
        rw [hp]
        exact ⟨⟨j, hj⟩, rfl⟩
      have mX : ∀ m, 1 ≤ m → m ≤ redR w →
          (pt (XBf (redR w) n m) : Fin (redN w) → ℝ) ∈ Set.range p := by
        intro m h1 h2
        rw [← Pt_X (redR w) n (XBf (redR w) n) (VBf (redR w) n) (PYf (redR w) n A)
          (Zf (redR w) n Af) (PAf (redR w) S') (Pvf (redR w) n S') m h1 h2]
        exact hmem _ (by omega)
      have mV : ∀ s, s ≤ redR w → (pt (VBf (redR w) n s) : Fin (redN w) → ℝ) ∈ Set.range p := by
        intro s h
        rw [← Pt_V (redR w) n (XBf (redR w) n) (VBf (redR w) n) (PYf (redR w) n A)
          (Zf (redR w) n Af) (PAf (redR w) S') (Pvf (redR w) n S') s h]
        exact hmem _ (by omega)
      have mY : (pt (PYf (redR w) n A) : Fin (redN w) → ℝ) ∈ Set.range p := by
        rw [← Pt_Y (redR w) n (XBf (redR w) n) (VBf (redR w) n) (PYf (redR w) n A)
          (Zf (redR w) n Af) (PAf (redR w) S') (Pvf (redR w) n S')]
        exact hmem _ (by omega)
      have mZ : ∀ j, j < n → (pt (Zf (redR w) n Af j) : Fin (redN w) → ℝ) ∈ Set.range p := by
        intro j hj
        rw [← Pt_Z (redR w) n (XBf (redR w) n) (VBf (redR w) n) (PYf (redR w) n A)
          (Zf (redR w) n Af) (PAf (redR w) S') (Pvf (redR w) n S') j hj]
        exact hmem _ (by omega)
      have mA : (pt (PAf (redR w) S') : Fin (redN w) → ℝ) ∈ Set.range p := by
        rw [← Pt_A (redR w) n (XBf (redR w) n) (VBf (redR w) n) (PYf (redR w) n A)
          (Zf (redR w) n Af) (PAf (redR w) S') (Pvf (redR w) n S')]
        exact hmem _ (by omega)
      have mv : (pt (Pvf (redR w) n S') : Fin (redN w) → ℝ) ∈ Set.range p := by
        rw [← Pt_v (redR w) n (XBf (redR w) n) (VBf (redR w) n) (PYf (redR w) n A)
          (Zf (redR w) n Af) (PAf (redR w) S') (Pvf (redR w) n S')]
        exact hmem _ (by omega)
      have hD : ∀ k, k < 2 * redR w → (pt (D k) : Fin (redN w) → ℝ) ∈
          vectorSpan ℝ (Set.range p) := by
        intro k hk
        rcases Nat.lt_or_ge k 2 with hk2 | hk2
        · rcases Nat.lt_or_ge k 1 with hk1 | hk1
          · obtain rfl : k = 0 := by omega
            exact diff_mem _ _ _ _
              (addU_rel _ (2 * redR w + 1) 0 (by omega) _ _ relV0) (mV 0 (by omega)) (mV 1 hR1)
          · obtain rfl : k = 1 := by omega
            exact diff_mem _ _ _ _
              (addU_rel _ (2 * redR w + 1) 1 (by omega) _ _ relX1) (mX 1 le_rfl hR1)
              (mV 0 (by omega))
        · rcases Nat.even_or_odd k with ⟨s, hs⟩ | ⟨m, hm⟩
          · obtain rfl : k = 2 * s := by omega
            exact diff_mem _ _ _ _
              (addU_rel _ (2 * redR w + 1) (2 * s) (by omega) _ _ (relV s (by omega)))
              (mV s (by omega)) (mV (s + 1) (by omega))
          · subst hm
            exact diff_mem _ _ _ _
              (addU_rel _ (2 * redR w + 1) (2 * m + 1) (by omega) _ _ (relX m (by omega)))
              (mX (m + 1) (by omega) (by omega)) (mX m (by omega) (by omega))
      have hXRat : ∀ c, 2 * redR w + 1 ≤ c →
          XBf (redR w) n (redR w) c = if c = 2 * redR w + n + 2 then 1 else 0 := by
        intro c hc
        unfold XBf
        exact addU_at _ _ (by omega) _ _ hc
      have hPAz : ∀ c, 2 * redR w + n + 2 ≤ c → PAf (redR w) S' c = 0 := by
        intro c hc
        apply gS_out
        · rw [Finset.mem_range]
          omega
        · rw [Finset.mem_insert]
          rintro (h | h)
          · omega
          · have := hS'ge _ h
            omega
      have hPvV : Pvf (redR w) n S' (2 * redR w + n + 3) = 1 :=
        gS_E _ _ _ (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
      have hge := finrank_ge_tri (N := redN w) (K := 2 * redR w + n + 3) (by omega)
        (u4 (redR w) n (XBf (redR w) n (redR w)) (PYf (redR w) n A) (Zf (redR w) n Af)
          (PAf (redR w) S') (Pvf (redR w) n S'))
        (vectorSpan ℝ (Set.range p))
        (by
          intro k
          rw [u4_eq]
          by_cases hk : k.val < 2 * redR w
          · have e : dd4 (redR w) n (XBf (redR w) n (redR w)) (PYf (redR w) n A)
                (Zf (redR w) n Af) (PAf (redR w) S') (Pvf (redR w) n S') k.val = D k.val := by
              funext c
              unfold dd4
              rw [if_pos hk]
            rw [e]
            exact hD k.val hk
          · by_cases hk2 : k.val = 2 * redR w
            · refine diff_mem _ _ _ _ (fun c => ?_) mY (mX (redR w) hR1 le_rfl)
              unfold dd4
              rw [if_neg hk, if_pos hk2]
              ring
            · by_cases hk3 : k.val < 2 * redR w + n + 1
              · refine diff_mem _ _ _ _ (fun c => ?_) (mZ (k.val - (2 * redR w + 1)) (by omega)) mY
                unfold dd4
                rw [if_neg hk, if_neg hk2, if_pos hk3]
                ring
              · by_cases hk4 : k.val = 2 * redR w + n + 1
                · refine diff_mem _ _ _ _ (fun c => ?_) mA mY
                  unfold dd4
                  rw [if_neg hk, if_neg hk2, if_neg hk3, if_pos hk4]
                  ring
                · refine diff_mem _ _ _ _ (fun c => ?_) mv mA
                  unfold dd4
                  rw [if_neg hk, if_neg hk2, if_neg hk3, if_neg hk4]
                  ring)
        (by
          intro k c hkc
          have hcN : c.val < 2 * redR w + n + 4 := c.isLt
          have hkK := k.isLt
          rw [u4_apply]
          unfold dd4
          split_ifs with hk hk2 hk3 hk4
          · exact D_zero k.val c.val hkc
          · rw [hXRat c.val (by omega)]
            by_cases hcU : c.val = 2 * redR w + n + 2
            · rw [hcU, if_pos rfl, hPYU]
              ring
            · rw [if_neg hcU, hPYz c.val (by omega) hcU]
              ring
          · by_cases hcU : c.val = 2 * redR w + n + 2
            · rw [hcU, hZU, hPYU]
              ring
            · rw [hZz (k.val - (2 * redR w + 1)) c.val (by omega) (by omega) hcU,
                hPYz c.val (by omega) hcU]
              ring
          · rw [hPAz c.val (by omega), hPYz c.val (by omega) (by omega)]
            ring
          · exfalso
            omega)
        (by
          intro k c hc
          have hkK := k.isLt
          rw [u4_apply, hc]
          unfold dd4
          split_ifs with hk hk2 hk3 hk4
          · rw [D_piv]
            norm_num
          · rw [hXRat (k.val + 1) (by omega),
              if_neg (show ¬(k.val + 1 = 2 * redR w + n + 2) by omega),
              show k.val + 1 = 2 * redR w + 1 by omega, hPY1]
            norm_num
          · rw [show k.val + 1 = 2 * redR w + 2 + (k.val - (2 * redR w + 1)) by omega, hZj,
              hPYz (2 * redR w + 2 + (k.val - (2 * redR w + 1))) (by omega) (by omega)]
            norm_num
          · rw [show k.val + 1 = 2 * redR w + n + 2 by omega, hPAz _ le_rfl, hPYU]
            norm_num
          · rw [show k.val + 1 = 2 * redR w + n + 3 by omega, hPvV,
              hPAz (2 * redR w + n + 3) (by omega)]
            norm_num)
      have hc : Fintype.card (Fin (redN w)) = (redN w - 1) + 1 := by
        rw [Fintype.card_fin]
        omega
      rw [affineIndependent_iff_finrank_vectorSpan_eq ℝ p hc]
      apply le_antisymm (finrank_vectorSpan_range_le ℝ p hc)
      omega
    · intro k
      exact Pt_cases (redR w) n (XBf (redR w) n) (VBf (redR w) n) (PYf (redR w) n A)
        (Zf (redR w) n Af) (PAf (redR w) S') (Pvf (redR w) n S')
        (fun g => (pt g : Fin (redN w) → ℝ) ∈ knapsackSet (redA w t) (redB w t) ∧
          ∑ i, ((redAlpha w t i : ℤ) : ℝ) * (pt g : Fin (redN w) → ℝ) i = ((redBeta w t : ℕ) : ℝ))
        hXB hVB hPY hZ hPA hPv k.val (by have := k.isLt; omega)
