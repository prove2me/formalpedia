-- Prove2me | solution 1 for KnapsackFacets.claim_b
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-20T22:54:31.24045+00:00
-- url     : https://prove2.me/submissions/9f2dd79b-ac42-40ed-a691-4974ab35130c

import Definitions.Def_KnapsackFacets_KnapsackPolytope
import Definitions.Def_KnapsackFacets_ShiftedFib

set_option autoImplicit false

namespace Aux_KFcb
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

def pt {N : ℕ} (g : ℕ → ℝ) : Fin N → ℝ := fun i => g i.val

def aC (r t : ℕ) : Fin (2 * r + 1) → ℕ := fun i => t * shiftedFib (i.val + 1)
def bC (r t : ℕ) : ℕ := t * ∑ i ∈ Finset.Icc 1 (2 * r), shiftedFib i
def αC (r : ℕ) : Fin (2 * r + 1) → ℤ := fun i => (shiftedFib (i.val + 1) : ℤ)
def βC (r : ℕ) : ℤ := ((∑ i ∈ Finset.Icc 1 (2 * r), shiftedFib i : ℕ) : ℤ)

noncomputable def phi (N : ℕ) : (Fin N → ℝ) →ₗ[ℝ] ℝ where
  toFun x := ∑ i, F i.val * x i
  map_add' x y := by
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by ring)

theorem phi_apply (N : ℕ) (x : Fin N → ℝ) : phi N x = ∑ i, F i.val * x i := rfl

theorem alpha_sum (r : ℕ) (x : Fin (2 * r + 1) → ℝ) :
    ∑ i, ((αC r i : ℤ) : ℝ) * x i = phi (2 * r + 1) x := by
  rw [phi_apply]
  apply Finset.sum_congr rfl
  intro i _
  simp only [αC, Int.cast_natCast, F]

theorem beta_eq (r : ℕ) :
    ((βC r : ℤ) : ℝ) = ((∑ i ∈ Finset.Icc 1 (2 * r), shiftedFib i : ℕ) : ℝ) := by
  simp only [βC, Int.cast_natCast]

theorem a_sum (r t : ℕ) (x : Fin (2 * r + 1) → ℝ) :
    ∑ i, ((aC r t i : ℕ) : ℝ) * x i = (t : ℝ) * phi (2 * r + 1) x := by
  rw [phi_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [aC, Nat.cast_mul, F]
  ring

theorem b_eq (r t : ℕ) :
    ((bC r t : ℕ) : ℝ) = (t : ℝ) * ((∑ i ∈ Finset.Icc 1 (2 * r), shiftedFib i : ℕ) : ℝ) := by
  simp only [bC, Nat.cast_mul]

theorem phi_pt (r : ℕ) (g : ℕ → ℝ) : phi (2 * r + 1) (pt g) = T (2 * r + 1) g := by
  rw [phi_apply]
  exact Fin.sum_univ_eq_sum_range (fun c => F c * g c) (2 * r + 1)

theorem face_mem (r t : ℕ) (g : ℕ → ℝ) (h01 : ∀ c, g c = 0 ∨ g c = 1)
    (hT : T (2 * r + 1) g = ((∑ i ∈ Finset.Icc 1 (2 * r), shiftedFib i : ℕ) : ℝ)) :
    (pt g : Fin (2 * r + 1) → ℝ) ∈ face (aC r t) (bC r t) (αC r) (βC r) := by
  refine ⟨subset_convexHull ℝ _ ⟨fun i => h01 i.val, ?_⟩, ?_⟩
  · exact le_of_eq (by rw [a_sum, b_eq, phi_pt, hT])
  · show ∑ i, ((αC r i : ℤ) : ℝ) * pt g i = ((βC r : ℤ) : ℝ)
    rw [alpha_sum, beta_eq, phi_pt, hT]

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

theorem finrank_ker (N : ℕ) (hN : 1 ≤ N) :
    Module.finrank ℝ (LinearMap.ker (phi N)) = N - 1 := by
  have h := LinearMap.finrank_range_add_finrank_ker (phi N)
  have hr : LinearMap.range (phi N) = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro y
    refine ⟨fun i => if i.val = 0 then y else 0, ?_⟩
    rw [phi_apply]
    rw [Finset.sum_eq_single ⟨0, hN⟩]
    · simp [F, shiftedFib]
    · intro b _ hb
      have : b.val ≠ 0 := fun h => hb (Fin.ext h)
      simp [this]
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [hr, finrank_top, Module.finrank_self, Module.finrank_fin_fun] at h
  omega

end Aux_KFcb

open KnapsackFacets Aux_KFcb in
theorem solution (r : ℕ) (hr : 1 ≤ r) (t : ℕ) (ht : 1 ≤ t) :
    IsFacetDefining (fun i : Fin (2 * r + 1) => t * shiftedFib (i.val + 1))
      (t * ∑ i ∈ Finset.Icc 1 (2 * r), shiftedFib i)
      (fun i : Fin (2 * r + 1) => (shiftedFib (i.val + 1) : ℤ))
      ((∑ i ∈ Finset.Icc 1 (2 * r), shiftedFib i : ℕ) : ℤ) := by
  show IsFacetDefining (aC r t) (bC r t) (αC r) (βC r)
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  -- validity
  have hval : IsValid (aC r t) (bC r t) (αC r) (βC r) := by
    intro x hx
    have hconv : Convex ℝ {x : Fin (2 * r + 1) → ℝ |
        phi (2 * r + 1) x ≤ ((∑ i ∈ Finset.Icc 1 (2 * r), shiftedFib i : ℕ) : ℝ)} :=
      convex_halfSpace_le (phi (2 * r + 1)).isLinear _
    have hsub : knapsackSet (aC r t) (bC r t) ⊆ {x : Fin (2 * r + 1) → ℝ |
        phi (2 * r + 1) x ≤ ((∑ i ∈ Finset.Icc 1 (2 * r), shiftedFib i : ℕ) : ℝ)} := by
      rintro y ⟨_, hcap⟩
      rw [a_sum, b_eq] at hcap
      exact le_of_mul_le_mul_left hcap htR
    have h := convexHull_min hsub hconv hx
    show ∑ i, ((αC r i : ℤ) : ℝ) * x i ≤ ((βC r : ℤ) : ℝ)
    rw [alpha_sum, beta_eq]
    exact h
  -- nonempty
  have hXr : (pt (gX r) : Fin (2 * r + 1) → ℝ) ∈ face (aC r t) (bC r t) (αC r) (βC r) :=
    face_mem r t (gX r) (gX_01 r) (T_Xr r)
  -- the face lies in the kernel hyperplane
  have hup : vectorSpan ℝ (face (aC r t) (bC r t) (αC r) (βC r)) ≤
      LinearMap.ker (phi (2 * r + 1)) := by
    rw [vectorSpan_def, Submodule.span_le]
    rintro z ⟨p, hp, q, hq, rfl⟩
    have hp2 := hp.2
    have hq2 := hq.2
    simp only [Set.mem_setOf_eq] at hp2 hq2
    rw [alpha_sum] at hp2 hq2
    rw [SetLike.mem_coe, LinearMap.mem_ker]
    show phi (2 * r + 1) (p -ᵥ q) = 0
    rw [vsub_eq_sub, map_sub, hp2, hq2, sub_self]
  -- the differences D k lie in the vector span
  have hmemD : ∀ k : Fin (2 * r), (pt (D k.val) : Fin (2 * r + 1) → ℝ) ∈
      vectorSpan ℝ (face (aC r t) (bC r t) (αC r) (βC r)) := by
    intro k
    have hk := k.isLt
    have hgen : ∀ (P Q : ℕ → ℝ), (∀ c, P c = Q c + D k.val c) →
        (pt P : Fin (2 * r + 1) → ℝ) ∈ face (aC r t) (bC r t) (αC r) (βC r) →
        (pt Q : Fin (2 * r + 1) → ℝ) ∈ face (aC r t) (bC r t) (αC r) (βC r) →
        (pt (D k.val) : Fin (2 * r + 1) → ℝ) ∈
          vectorSpan ℝ (face (aC r t) (bC r t) (αC r) (βC r)) := by
      intro P Q hPQ hP hQ
      have h := vsub_mem_vectorSpan ℝ hP hQ
      rw [vsub_eq_sub] at h
      convert h using 1
      funext i
      simp only [pt, Pi.sub_apply, hPQ]
      ring
    have hXm : ∀ m, 1 ≤ m → m ≤ r →
        (pt (gX m) : Fin (2 * r + 1) → ℝ) ∈ face (aC r t) (bC r t) (αC r) (βC r) :=
      fun m h1 h2 => face_mem r t (gX m) (gX_01 m) (T_X r m h1 h2)
    have hVs : ∀ s, s ≤ r →
        (pt (gV s) : Fin (2 * r + 1) → ℝ) ∈ face (aC r t) (bC r t) (αC r) (βC r) :=
      fun s h => face_mem r t (gV s) (gV_01 s) (T_V r hr s h)
    rcases Nat.lt_or_ge k.val 2 with hk2 | hk2
    · rcases Nat.lt_or_ge k.val 1 with hk1 | hk1
      · have hk0 : k.val = 0 := by omega
        rw [hk0] at hgen ⊢
        exact hgen (gV 0) (gV 1) relV0 (hVs 0 (by omega)) (hVs 1 hr)
      · have hk1' : k.val = 1 := by omega
        rw [hk1'] at hgen ⊢
        exact hgen (gX 1) (gV 0) relX1 (hXm 1 le_rfl hr) (hVs 0 (by omega))
    · rcases Nat.even_or_odd k.val with ⟨s, hs⟩ | ⟨m, hm⟩
      · have hs' : k.val = 2 * s := by omega
        rw [hs'] at hgen ⊢
        exact hgen (gV s) (gV (s + 1)) (relV s (by omega)) (hVs s (by omega))
          (hVs (s + 1) (by omega))
      · rw [hm] at hgen ⊢
        exact hgen (gX (m + 1)) (gX m) (relX m (by omega)) (hXm (m + 1) (by omega) (by omega))
          (hXm m (by omega) (by omega))
  have hli := tri_li (2 * r) (fun k => (pt (D k.val) : Fin (2 * r + 1) → ℝ))
    (fun k c hkc => D_zero k.val c.val hkc)
    (fun k => by
      show D k.val (k.val + 1) ≠ 0
      rw [D_piv]
      norm_num)
  have hlow : 2 * r ≤ Module.finrank ℝ (vectorSpan ℝ (face (aC r t) (bC r t) (αC r) (βC r))) := by
    have h1 : Submodule.span ℝ (Set.range (fun k : Fin (2 * r) =>
        (pt (D k.val) : Fin (2 * r + 1) → ℝ))) ≤
        vectorSpan ℝ (face (aC r t) (bC r t) (αC r) (βC r)) := by
      rw [Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      exact hmemD k
    have h2 := Submodule.finrank_mono h1
    rw [finrank_span_eq_card hli, Fintype.card_fin] at h2
    exact h2
  have hhigh : Module.finrank ℝ (vectorSpan ℝ (face (aC r t) (bC r t) (αC r) (βC r))) ≤ 2 * r := by
    have h2 := Submodule.finrank_mono hup
    rw [finrank_ker (2 * r + 1) (by omega)] at h2
    omega
  -- the knapsack polytope is full dimensional
  have hfull : vectorSpan ℝ (KP (aC r t) (bC r t)) = ⊤ := by
    rw [eq_top_iff, ← (Pi.basisFun ℝ (Fin (2 * r + 1))).span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    rw [Pi.basisFun_apply]
    have h0 : (0 : Fin (2 * r + 1) → ℝ) ∈ KP (aC r t) (bC r t) := by
      refine subset_convexHull ℝ _ ⟨fun j => Or.inl rfl, ?_⟩
      simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero]
      positivity
    have hi : (Pi.single i 1 : Fin (2 * r + 1) → ℝ) ∈ KP (aC r t) (bC r t) := by
      refine subset_convexHull ℝ _ ⟨fun j => ?_, ?_⟩
      · by_cases hj : j = i
        · right
          rw [hj, Pi.single_eq_same]
        · left
          rw [Pi.single_eq_of_ne hj]
      · have hs : ∑ j, ((aC r t j : ℕ) : ℝ) * (Pi.single i 1 : Fin (2 * r + 1) → ℝ) j =
            ((aC r t i : ℕ) : ℝ) := by
          rw [Finset.sum_eq_single i]
          · rw [Pi.single_eq_same, mul_one]
          · intro j _ hj
            rw [Pi.single_eq_of_ne hj, mul_zero]
          · intro h
            exact absurd (Finset.mem_univ i) h
        rw [hs]
        have hle : aC r t i ≤ bC r t := by
          unfold aC bC
          exact Nat.mul_le_mul_left t (fib_le r hr i.val i.isLt)
        exact_mod_cast hle
    have h := vsub_mem_vectorSpan ℝ hi h0
    rwa [vsub_eq_sub, sub_zero] at h
  refine ⟨hval, ⟨_, hXr⟩, ?_⟩
  rw [hfull, finrank_top, Module.finrank_fin_fun]
  omega
