-- Prove2me | solution 1 for KnapsackFacets.claim_c
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-20T23:22:04.94705+00:00
-- url     : https://prove2.me/submissions/253948f5-141b-4b08-ab8e-5138ffdb43a8

import Definitions.Def_KnapsackFacets_KnapsackPolytope
import Definitions.Def_KnapsackFacets_Reduction

set_option autoImplicit false

namespace Aux_KFcc
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

theorem sumAc {n : ℕ} (w : Fin n → ℕ) (t : ℕ) (g : ℕ → ℝ) :
    ∑ i : Fin (2 * redR w + 2), ((aCoef w t (i.val + 1) : ℕ) : ℝ) *
        (pt g : Fin (2 * redR w + 2) → ℝ) i =
      (t : ℝ) * T (2 * redR w + 1) g +
        ((t : ℝ) * (2 * (redL w : ℝ) + 1) + 1) * g (2 * redR w + 1) := by
  show ∑ i : Fin (2 * redR w + 2), ((aCoef w t (i.val + 1) : ℕ) : ℝ) * g i.val = _
  rw [Fin.sum_univ_eq_sum_range (fun c => ((aCoef w t (c + 1) : ℕ) : ℝ) * g c) (2 * redR w + 2)]
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
  rw [e2, h1, cA2]
  unfold T
  push_cast
  try ring

theorem sumBc {n : ℕ} (w : Fin n → ℕ) (t : ℕ) (g : ℕ → ℝ) :
    ∑ i : Fin (2 * redR w + 2), (((alphaCoef w t (i.val + 1) : ℕ) : ℤ) : ℝ) *
        (pt g : Fin (2 * redR w + 2) → ℝ) i =
      T (2 * redR w + 1) g + (2 * (redL w : ℝ) + 2) * g (2 * redR w + 1) := by
  show ∑ i : Fin (2 * redR w + 2), (((alphaCoef w t (i.val + 1) : ℕ) : ℤ) : ℝ) * g i.val = _
  simp only [Int.cast_natCast]
  rw [Fin.sum_univ_eq_sum_range (fun c => ((alphaCoef w t (c + 1) : ℕ) : ℝ) * g c)
    (2 * redR w + 2)]
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
  rw [e2, h1, cB2]
  unfold T
  push_cast
  try ring

noncomputable def ddc (R : ℕ) (Y X : ℕ → ℝ) (j c : ℕ) : ℝ :=
  if j < 2 * R then D j c else Y c - X c

noncomputable def uC {N : ℕ} (R : ℕ) (Y X : ℕ → ℝ) (k : Fin (2 * R + 1)) (c : Fin N) : ℝ :=
  ddc R Y X k.val c.val

theorem uC_apply {N : ℕ} (R : ℕ) (Y X : ℕ → ℝ) (k : Fin (2 * R + 1)) (c : Fin N) :
    uC R Y X k c = ddc R Y X k.val c.val := rfl

theorem uC_eq {N : ℕ} (R : ℕ) (Y X : ℕ → ℝ) (k : Fin (2 * R + 1)) :
    (uC R Y X k : Fin N → ℝ) = pt (ddc R Y X k.val) := rfl

end Aux_KFcc

open KnapsackFacets Aux_KFcc in
theorem solution {n : ℕ} (w : Fin n → ℕ) (t : ℕ) (ht : 2 ≤ t) (hw : ∀ i, w i + 1 ≤ t) :
    IsFacetDefining (fun i : Fin (2 * redR w + 2) => aCoef w t (i.val + 1))
      (t * ∑ i ∈ Finset.Icc 1 (2 * redR w), shiftedFib i)
      (fun i : Fin (2 * redR w + 2) => (alphaCoef w t (i.val + 1) : ℤ))
      ((∑ i ∈ Finset.Icc 1 (2 * redR w), shiftedFib i : ℕ) : ℤ) := by
  obtain ⟨hR1, _⟩ := R_bound w
  have hβ := beta_bound w
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
  have hsumB := Icc_sum (2 * redR w)
  obtain ⟨B, hB⟩ : ∃ B, B = ∑ i ∈ Finset.Icc 1 (2 * redR w), shiftedFib i := ⟨_, rfl⟩
  rw [← hB] at hβ hTX hTV hsumB ⊢
  have htR : (1 : ℝ) ≤ t := by exact_mod_cast (show 1 ≤ t by omega)
  have hface : ∀ g : ℕ → ℝ, (∀ c, g c = 0 ∨ g c = 1) →
      (t : ℝ) * T (2 * redR w + 1) g +
          ((t : ℝ) * (2 * (redL w : ℝ) + 1) + 1) * g (2 * redR w + 1) ≤ (t : ℝ) * B →
      T (2 * redR w + 1) g + (2 * (redL w : ℝ) + 2) * g (2 * redR w + 1) = B →
      (pt g : Fin (2 * redR w + 2) → ℝ) ∈
        face (fun i : Fin (2 * redR w + 2) => aCoef w t (i.val + 1)) (t * B)
          (fun i : Fin (2 * redR w + 2) => (alphaCoef w t (i.val + 1) : ℤ)) ((B : ℕ) : ℤ) := by
    intro g h01 hcap htight
    refine ⟨subset_convexHull ℝ _ ⟨fun i => h01 i.val, ?_⟩, ?_⟩
    · show ∑ i : Fin (2 * redR w + 2), ((aCoef w t (i.val + 1) : ℕ) : ℝ) *
          (pt g : Fin (2 * redR w + 2) → ℝ) i ≤ ((t * B : ℕ) : ℝ)
      rw [sumAc]
      push_cast
      linarith
    · show ∑ i : Fin (2 * redR w + 2), (((alphaCoef w t (i.val + 1) : ℕ) : ℤ) : ℝ) *
          (pt g : Fin (2 * redR w + 2) → ℝ) i = (((B : ℕ) : ℤ) : ℝ)
      rw [sumBc]
      push_cast
      linarith
  have hV : ∀ x ∈ knapsackSet (fun i : Fin (2 * redR w + 2) => aCoef w t (i.val + 1)) (t * B),
      ∑ i, (((fun i : Fin (2 * redR w + 2) => (alphaCoef w t (i.val + 1) : ℤ)) i : ℤ) : ℝ) * x i ≤
        (((B : ℕ) : ℤ) : ℝ) := by
    intro x hx
    obtain ⟨h01, hcap⟩ := hx
    have hg01 := ext_01 h01
    rw [← ext_pt x] at hcap ⊢
    have hcap' : ∑ i : Fin (2 * redR w + 2), ((aCoef w t (i.val + 1) : ℕ) : ℝ) *
        (pt (ext x) : Fin (2 * redR w + 2) → ℝ) i ≤ ((t * B : ℕ) : ℝ) := hcap
    rw [sumAc] at hcap'
    show ∑ i : Fin (2 * redR w + 2), (((alphaCoef w t (i.val + 1) : ℕ) : ℤ) : ℝ) *
        (pt (ext x) : Fin (2 * redR w + 2) → ℝ) i ≤ (((B : ℕ) : ℤ) : ℝ)
    rw [sumBc]
    push_cast at hcap' ⊢
    obtain ⟨m, hm⟩ := T_nat (2 * redR w + 1) (ext x) hg01
    rw [hm] at hcap' ⊢
    rcases hg01 (2 * redR w + 1) with hy | hy <;> rw [hy] at hcap' ⊢
    · have h0 : (t : ℝ) * m ≤ t * B := by linarith
      have h1 : (m : ℝ) ≤ B := le_of_mul_le_mul_left h0 (by linarith)
      linarith
    · rcases Nat.lt_or_ge B (m + 2 * redL w + 2) with hlt | hge
      · have h1 : (B : ℝ) ≤ m + 2 * redL w + 1 := by
          exact_mod_cast (show B ≤ m + 2 * redL w + 1 by omega)
        have h2 : (t : ℝ) * B ≤ t * (m + 2 * redL w + 1) :=
          mul_le_mul_of_nonneg_left h1 (by linarith)
        linarith
      · have h1 : (m : ℝ) + 2 * redL w + 2 ≤ B := by exact_mod_cast hge
        linarith
  have hU : ∀ i : Fin (2 * redR w + 2),
      (fun i : Fin (2 * redR w + 2) => aCoef w t (i.val + 1)) i ≤ t * B := by
    intro i
    show aCoef w t (i.val + 1) ≤ t * B
    rcases Nat.lt_or_ge i.val (2 * redR w + 1) with hi | hi
    · rw [cA1 w t i.val hi, hB]
      exact Nat.mul_le_mul_left t (fib_le _ hR1 i.val hi)
    · have hi' : i.val = 2 * redR w + 1 := by have := i.isLt; omega
      rw [hi', cA2]
      linarith [Nat.mul_le_mul_left t (show 2 * redL w + 2 ≤ B by omega)]
  have hα0 : (fun i : Fin (2 * redR w + 2) => (alphaCoef w t (i.val + 1) : ℤ))
      ⟨0, by omega⟩ ≠ 0 := by
    show ((alphaCoef w t (0 + 1) : ℕ) : ℤ) ≠ 0
    rw [cB1 w t 0 (by omega)]
    simp [shiftedFib]
  -- the extra point with y = 1
  obtain ⟨A, hA, hAs⟩ := rep (2 * redR w) (B - (2 * redL w + 2)) (by rw [← hsumB]; omega)
  have hTY : T (2 * redR w + 1) (gS A {2 * redR w + 1}) =
      ((B - (2 * redL w + 2) : ℕ) : ℝ) := by
    rw [T_gS (2 * redR w + 1) A {2 * redR w + 1} (hA.trans (Finset.range_subset_range.mpr (by omega))) (by simp), hAs]
  have hY1 : gS A {2 * redR w + 1} (2 * redR w + 1) = 1 := gS_E _ _ _ (by simp)
  have hcastB : ((B - (2 * redL w + 2) : ℕ) : ℝ) = (B : ℝ) - (2 * (redL w : ℝ) + 2) := by
    rw [Nat.cast_sub (show 2 * redL w + 2 ≤ B by omega)]
    push_cast
    try ring
  have hYmem := hface (gS A {2 * redR w + 1}) (gS_01 _ _)
    (by rw [hTY, hY1, hcastB]; linarith) (by rw [hTY, hY1, hcastB]; ring)
  have hXm : ∀ m, 1 ≤ m → m ≤ redR w →
      (pt (trunc (2 * redR w + 1) (gX m)) : Fin (2 * redR w + 2) → ℝ) ∈
        face (fun i : Fin (2 * redR w + 2) => aCoef w t (i.val + 1)) (t * B)
          (fun i : Fin (2 * redR w + 2) => (alphaCoef w t (i.val + 1) : ℤ)) ((B : ℕ) : ℤ) := by
    intro m h1 h2
    apply hface _ (trunc_01 _ _ (gX_01 m))
    · rw [hTX m h1 h2, trunc_ge _ _ _ le_rfl]
      linarith
    · rw [hTX m h1 h2, trunc_ge _ _ _ le_rfl]
      ring
  have hVs : ∀ s, s ≤ redR w →
      (pt (trunc (2 * redR w + 1) (gV s)) : Fin (2 * redR w + 2) → ℝ) ∈
        face (fun i : Fin (2 * redR w + 2) => aCoef w t (i.val + 1)) (t * B)
          (fun i : Fin (2 * redR w + 2) => (alphaCoef w t (i.val + 1) : ℤ)) ((B : ℕ) : ℤ) := by
    intro s h
    apply hface _ (trunc_01 _ _ (gV_01 s))
    · rw [hTV s h, trunc_ge _ _ _ le_rfl]
      linarith
    · rw [hTV s h, trunc_ge _ _ _ le_rfl]
      ring
  have hD : ∀ k, k < 2 * redR w → (pt (D k) : Fin (2 * redR w + 2) → ℝ) ∈
      vectorSpan ℝ (face (fun i : Fin (2 * redR w + 2) => aCoef w t (i.val + 1)) (t * B)
        (fun i : Fin (2 * redR w + 2) => (alphaCoef w t (i.val + 1) : ℤ)) ((B : ℕ) : ℤ)) := by
    intro k hk
    rcases Nat.lt_or_ge k 2 with hk2 | hk2
    · rcases Nat.lt_or_ge k 1 with hk1 | hk1
      · obtain rfl : k = 0 := by omega
        exact diff_mem _ _ _ _ (trel (2 * redR w + 1) 0 (by omega) _ _ relV0) (hVs 0 (by omega)) (hVs 1 hR1)
      · obtain rfl : k = 1 := by omega
        exact diff_mem _ _ _ _ (trel (2 * redR w + 1) 1 (by omega) _ _ relX1) (hXm 1 le_rfl hR1)
          (hVs 0 (by omega))
    · rcases Nat.even_or_odd k with ⟨s, hs⟩ | ⟨m, hm⟩
      · obtain rfl : k = 2 * s := by omega
        exact diff_mem _ _ _ _ (trel (2 * redR w + 1) (2 * s) (by omega) _ _ (relV s (by omega)))
          (hVs s (by omega)) (hVs (s + 1) (by omega))
      · subst hm
        exact diff_mem _ _ _ _ (trel (2 * redR w + 1) (2 * m + 1) (by omega) _ _ (relX m (by omega)))
          (hXm (m + 1) (by omega) (by omega)) (hXm m (by omega) (by omega))
  refine facetCrit (N := 2 * redR w + 2) (K := 2 * redR w + 1) (by omega) _ _ _ _ hV hU
    ⟨0, by omega⟩ hα0 ⟨_, hYmem⟩
    (uC (redR w) (gS A {2 * redR w + 1}) (trunc (2 * redR w + 1) (gX (redR w)))) ?_ ?_ ?_
  · intro k
    rw [uC_eq]
    by_cases hk : k.val < 2 * redR w
    · have e : ddc (redR w) (gS A {2 * redR w + 1}) (trunc (2 * redR w + 1) (gX (redR w))) k.val =
          D k.val := by
        funext c
        unfold ddc
        rw [if_pos hk]
      rw [e]
      exact hD k.val hk
    · have e : ∀ c, gS A {2 * redR w + 1} c = trunc (2 * redR w + 1) (gX (redR w)) c +
          ddc (redR w) (gS A {2 * redR w + 1}) (trunc (2 * redR w + 1) (gX (redR w))) k.val c := by
        intro c
        unfold ddc
        rw [if_neg hk]
        ring
      exact diff_mem _ _ _ _ e hYmem (hXm (redR w) hR1 le_rfl)
  · intro k c hkc
    rw [uC_apply]
    unfold ddc
    split_ifs with hk
    · exact D_zero k.val c.val hkc
    · have := c.isLt
      have := k.isLt
      omega
  · intro k c hc
    rw [uC_apply, hc]
    unfold ddc
    split_ifs with hk
    · rw [D_piv]
      norm_num
    · have hk' : k.val + 1 = 2 * redR w + 1 := by have := k.isLt; omega
      rw [hk', hY1, trunc_ge _ _ _ le_rfl]
      norm_num
